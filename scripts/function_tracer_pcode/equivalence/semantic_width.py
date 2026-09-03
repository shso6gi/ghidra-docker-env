# -*- coding: utf-8 -*-
"""Semantic-width aware expression normalization."""

from __future__ import annotations

from dataclasses import replace
from typing import Any, Dict, Iterable, Optional, Tuple

from ..analysis.condition.simplifier import ConditionSimplifier
from ..model import (
    ComparisonSurface,
    Condition,
    Expression,
    ExpressionType,
    FunctionReturnAnalysis,
    ReadonlyReductionRef,
    StorageInfo,
)
from ..model.render_smt import expression_smt_bit_width
from .param_semantics import (
    ParameterSemanticHint,
    infer_parameter_semantics_by_identity,
)


SAFE_TRUNCATING_BINARY_OPS = frozenset(
    {
        "INT_ADD",
        "INT_SUB",
        "INT_MULT",
        "INT_AND",
        "INT_OR",
        "INT_XOR",
        "INT_SDIV",
        "INT_DIV",
        "INT_SREM",
        "INT_REM",
    }
)

COMPARISON_OPS = frozenset(
    {
        "INT_EQUAL",
        "INT_NOTEQUAL",
        "INT_LESS",
        "INT_SLESS",
        "INT_LESSEQUAL",
        "INT_SLESSEQUAL",
    }
)

SIGNED_BINARY_OPS = frozenset({"INT_SDIV", "INT_SREM"})
UNSIGNED_BINARY_OPS = frozenset({"INT_DIV", "INT_REM"})
SIGNED_COMPARE_REWRITE_MAP = {
    "INT_LESS": "INT_SLESS",
    "INT_LESSEQUAL": "INT_SLESSEQUAL",
}
UNSIGNED_COMPARE_REWRITE_MAP = {
    "INT_SLESS": "INT_LESS",
    "INT_SLESSEQUAL": "INT_LESSEQUAL",
}
SIGNEDNESS_KINDS = frozenset({"signed", "unsigned"})
RETURN_EXTENSION_SURFACE_CANDIDATE_BITS = (64, 32, 16, 8)
RETURN_VALUE_EXTENSION_OPS = frozenset({"INT_ZEXT", "INT_SEXT"})
RETURN_EXTENSION_SURFACE_SOURCE = "cross_side_return_extension_surface"
RETURN_EXTENSION_SURFACE_COERCION = "equal_width_or_object_proven_extract"
RETURN_EXTENSION_SURFACE_KINDS = frozenset({"INT_ZEXT", "INT_SEXT", "none"})


def return_extension_surface_diagnostic_metadata(
    comparison_surface,
) -> Optional[Dict[str, Any]]:
    """Return sanitized extension-surface diagnostics without proof authority."""

    if getattr(comparison_surface, "kind", None) != "return_value":
        return None
    evidence = getattr(comparison_surface, "evidence", None)
    if not isinstance(evidence, dict):
        return None
    if evidence.get("source") != RETURN_EXTENSION_SURFACE_SOURCE:
        return None
    try:
        surface_bits = int(evidence.get("extension_surface_bit_width"))
    except (TypeError, ValueError):
        return None
    if surface_bits <= 0 or surface_bits % 8 != 0:
        return None
    try:
        active_surface_bits = int(getattr(comparison_surface, "explicit_bit_width", 0) or 0)
    except (TypeError, ValueError):
        return None
    if active_surface_bits != surface_bits:
        return None
    coercion = evidence.get("extension_surface_coercion")
    if coercion != RETURN_EXTENSION_SURFACE_COERCION:
        return None
    extension_kind = evidence.get("extension_surface_extension_kind")
    if extension_kind not in RETURN_EXTENSION_SURFACE_KINDS:
        return None
    source_widths_value = evidence.get("extension_surface_source_bit_widths", ())
    if source_widths_value is None:
        source_widths_value = ()
    if not isinstance(source_widths_value, (tuple, list, set)):
        return None
    try:
        source_widths = tuple(sorted(int(width) for width in source_widths_value))
    except (TypeError, ValueError):
        return None
    if any(width <= 0 or width > surface_bits for width in source_widths):
        return None
    if extension_kind in RETURN_VALUE_EXTENSION_OPS and not source_widths:
        return None
    if extension_kind == "none" and source_widths:
        return None
    return {
        "source": RETURN_EXTENSION_SURFACE_SOURCE,
        "surface_bits": surface_bits,
        "coercion": coercion,
        "extension_kind": extension_kind,
        "source_widths": source_widths,
        "return_width_sign_artifact": bool(
            evidence.get("return_width_sign_artifact")
            or evidence.get("allow_return_width_sign_artifact")
        ),
    }


def return_extension_surface_evidence_key(
    comparison_surface,
) -> Optional[Tuple[int, str, str, Tuple[int, ...]]]:
    """Do not promote return-width sign-artifact metadata into semantic keys."""

    return None


class SemanticWidthNormalizer:
    """Normalize expressions using explicit semantic-width hints."""

    def __init__(
        self,
        hints_by_identity: Dict[Tuple[object, ...], ParameterSemanticHint],
        fragment_infos_by_name: Optional[Dict[str, Any]] = None,
    ):
        self.hints_by_identity = hints_by_identity
        self.fragment_infos_by_name = fragment_infos_by_name or {}

    def rewrite_expression(self, expr: Optional[Expression]) -> Optional[Expression]:
        if expr is None:
            return expr

        if expr.expr_type == ExpressionType.PHI and expr.value:
            changed = False
            branches = []
            for cond, value in expr.value:
                new_cond = None
                if cond is not None:
                    new_cond_expr = self.rewrite_expression(cond.expression)
                    new_cond = Condition(new_cond_expr, cond.negated)
                    changed = changed or (new_cond_expr is not cond.expression)
                new_value = self.rewrite_expression(value)
                changed = changed or (new_value is not value)
                branches.append((new_cond, new_value))
            if not changed:
                return expr
            rebuilt = Expression.phi(branches)
            rebuilt.size = expr.size
            rebuilt.data_type = expr.data_type
            rebuilt.data_type_obj = getattr(expr, "data_type_obj", None)
            rebuilt.storage_info = expr.storage_info
            rebuilt.read_order_key = expr.read_order_key
            return rebuilt

        operands = getattr(expr, "operands", None) or []
        new_operands = [self.rewrite_expression(operand) for operand in operands]
        changed = any(new is not old for new, old in zip(new_operands, operands))

        candidate = expr
        if changed:
            candidate = Expression(
                expr_type=expr.expr_type,
                value=expr.value,
                operator=expr.operator,
                operands=new_operands,
                size=expr.size,
                name=expr.name,
                data_type=expr.data_type,
                data_type_obj=getattr(expr, "data_type_obj", None),
                opcode=getattr(expr, "opcode", None),
                storage_info=expr.storage_info,
                read_order_key=expr.read_order_key,
                runtime_ref=getattr(expr, "runtime_ref", None),
            )

        normalized = self._apply_rules(candidate)
        return normalized

    def _apply_rules(self, expr: Expression) -> Expression:
        if expr.expr_type == ExpressionType.BINARY_OP:
            if expr.operator in {"PIECE", "INT_OR"}:
                collapsed = self._normalize_parameter_fragment_extension(expr)
                if collapsed is not None:
                    return collapsed
            if expr.operator == "SUBPIECE":
                collapsed = self._normalize_subpiece(expr)
                if collapsed is not None:
                    return collapsed
            if expr.operator in SAFE_TRUNCATING_BINARY_OPS:
                collapsed = self._normalize_semantic_binary(expr)
                if collapsed is not None:
                    return collapsed
            if expr.operator in COMPARISON_OPS:
                collapsed = self._normalize_comparison(expr)
                if collapsed is not None:
                    return collapsed
        return expr

    def _normalize_parameter_fragment_extension(self, expr: Expression) -> Optional[Expression]:
        if expr.operator == "PIECE" and len(expr.operands) == 2:
            return self._build_fragment_extension_expr(expr.operands[0], expr.operands[1])

        if expr.operator != "INT_OR" or len(expr.operands) != 2:
            return None

        left, right = expr.operands
        collapsed = self._match_shift_or_fragment_expr(left, right)
        if collapsed is not None:
            return collapsed
        return self._match_shift_or_fragment_expr(right, left)

    def _match_shift_or_fragment_expr(
        self,
        shifted_expr: Expression,
        low_expr: Expression,
    ) -> Optional[Expression]:
        if (
            shifted_expr.expr_type != ExpressionType.BINARY_OP
            or shifted_expr.operator != "INT_LEFT"
            or len(shifted_expr.operands) != 2
        ):
            return None

        shift_amount = shifted_expr.operands[1]
        if shift_amount.expr_type != ExpressionType.CONSTANT:
            return None

        return self._build_fragment_extension_expr(
            shifted_expr.operands[0],
            low_expr,
            expected_shift_bits=int(shift_amount.value),
        )

    def _build_fragment_extension_expr(
        self,
        high_expr: Expression,
        low_expr: Expression,
        expected_shift_bits: Optional[int] = None,
    ) -> Optional[Expression]:
        if high_expr.expr_type != ExpressionType.VARIABLE or not high_expr.name:
            return None

        fragment_info = self.fragment_infos_by_name.get(high_expr.name)
        if fragment_info is None:
            return None

        if low_expr.expr_type not in {ExpressionType.PARAMETER, ExpressionType.VARIABLE}:
            return None
        if low_expr.name != fragment_info.parent_param_name:
            return None

        if (
            expected_shift_bits is not None
            and expected_shift_bits != fragment_info.parent_param_bit_width
        ):
            return None

        ext_op = (
            "INT_SEXT"
            if fragment_info.extension_type.name == "SIGN_EXTEND"
            else "INT_ZEXT"
        )
        rebuilt = Expression.unary_op(ext_op, low_expr)
        rebuilt.size = max(1, fragment_info.base_register_size_bits // 8)
        rebuilt.data_type = getattr(low_expr, "data_type", None)
        return rebuilt

    def _normalize_subpiece(self, expr: Expression) -> Optional[Expression]:
        if len(expr.operands) != 2:
            return None

        source, offset = expr.operands
        if offset.expr_type != ExpressionType.CONSTANT or int(offset.value) != 0:
            return None

        output_bits = expr.get_bit_width()
        if output_bits <= 0:
            return None

        if (
            source.expr_type == ExpressionType.UNARY_OP
            and source.operator in {"INT_SEXT", "INT_ZEXT"}
            and source.operands
        ):
            operand = source.operands[0]
            if operand.get_bit_width() == output_bits:
                return operand

        if (
            source.expr_type != ExpressionType.BINARY_OP
            or source.operator not in SAFE_TRUNCATING_BINARY_OPS
            or len(source.operands) != 2
        ):
            return None

        left_info = self._match_semantic_extension(source.operands[0])
        right_info = self._match_semantic_extension(source.operands[1])
        if left_info is None or right_info is None:
            return None
        if left_info["bits"] != output_bits or right_info["bits"] != output_bits:
            return None
        if left_info["bits"] != right_info["bits"]:
            return None

        if source.operator in SIGNED_BINARY_OPS:
            if left_info["signedness"] != "signed" or right_info["signedness"] != "signed":
                return None
        if source.operator in UNSIGNED_BINARY_OPS:
            if left_info["signedness"] != "unsigned" or right_info["signedness"] != "unsigned":
                return None

        rebuilt = Expression.binary_op(
            source.operator,
            left_info["expr"],
            right_info["expr"],
        )
        rebuilt.size = output_bits // 8
        rebuilt.data_type = source.data_type
        return rebuilt

    def _normalize_comparison(self, expr: Expression) -> Optional[Expression]:
        if len(expr.operands) != 2:
            return None

        left, right = expr.operands
        left_info = self._match_comparison_operand(left)
        right_info = self._match_comparison_operand(right)
        requires_signedness = expr.operator in {
            "INT_LESS",
            "INT_SLESS",
            "INT_LESSEQUAL",
            "INT_SLESSEQUAL",
        }

        left_constant_signedness = self._comparison_constant_signedness(expr.operator, left_info)
        if (
            left_info is not None
            and right.expr_type == ExpressionType.CONSTANT
            and left_constant_signedness in SIGNEDNESS_KINDS
        ):
            right_narrow = self._narrow_constant(right, left_info["bits"], left_constant_signedness)
            if right_narrow is not None:
                rebuilt = Expression.binary_op(
                    self._normalize_comparison_operator(expr.operator, left_info, None),
                    left_info["expr"],
                    right_narrow,
                )
                rebuilt.size = expr.size
                return rebuilt

        right_constant_signedness = self._comparison_constant_signedness(expr.operator, right_info)
        if (
            right_info is not None
            and left.expr_type == ExpressionType.CONSTANT
            and right_constant_signedness in SIGNEDNESS_KINDS
        ):
            left_narrow = self._narrow_constant(left, right_info["bits"], right_constant_signedness)
            if left_narrow is not None:
                rebuilt = Expression.binary_op(
                    self._normalize_comparison_operator(expr.operator, None, right_info),
                    left_narrow,
                    right_info["expr"],
                )
                rebuilt.size = expr.size
                return rebuilt

        if left_info is None or right_info is None:
            return None
        if left_info["bits"] != right_info["bits"]:
            return None
        if requires_signedness and (
            left_info.get("signedness") not in SIGNEDNESS_KINDS
            or right_info.get("signedness") not in SIGNEDNESS_KINDS
        ):
            return None

        rebuilt = Expression.binary_op(
            self._normalize_comparison_operator(expr.operator, left_info, right_info),
            left_info["expr"],
            right_info["expr"],
        )
        rebuilt.size = expr.size
        return rebuilt

    def _normalize_comparison_operator(
        self,
        operator: str,
        left_info,
        right_info,
    ) -> str:
        target_signedness = self._comparison_target_signedness(left_info, right_info)
        if target_signedness == "signed":
            return SIGNED_COMPARE_REWRITE_MAP.get(operator, operator)
        if target_signedness == "unsigned":
            return UNSIGNED_COMPARE_REWRITE_MAP.get(operator, operator)
        return operator

    def _comparison_target_signedness(self, left_info, right_info) -> Optional[str]:
        explicit_infos = [
            info
            for info in (left_info, right_info)
            if info is not None and bool(info.get("explicit_signedness"))
        ]
        if not explicit_infos:
            return None

        signednesses = {info.get("signedness") for info in explicit_infos}
        if len(signednesses) != 1:
            return None
        signedness = next(iter(signednesses))
        if signedness not in {"signed", "unsigned"}:
            return None
        return signedness

    def _comparison_constant_signedness(self, operator: str, info) -> Optional[str]:
        if info is None:
            return None
        signedness = info.get("signedness")
        if signedness in SIGNEDNESS_KINDS:
            return signedness
        if operator in {"INT_EQUAL", "INT_NOTEQUAL"}:
            return "unsigned"
        return None

    def _normalize_semantic_binary(self, expr: Expression) -> Optional[Expression]:
        if len(expr.operands) != 2:
            return None

        left, right = expr.operands
        left_info = self._match_semantic_low_expr(left)
        right_info = self._match_semantic_low_expr(right)

        if (
            left_info is not None
            and right.expr_type == ExpressionType.CONSTANT
            and left_info.get("signedness") in SIGNEDNESS_KINDS
        ):
            narrowed = self._narrow_constant(
                right,
                left_info["bits"],
                left_info["signedness"],
            )
            if narrowed is not None:
                if self._is_all_ones_mask(narrowed, left_info["bits"]) and expr.operator == "INT_AND":
                    return left_info["expr"]
                right_info = {
                    "expr": narrowed,
                    "bits": left_info["bits"],
                    "signedness": left_info["signedness"],
                }

        if (
            right_info is not None
            and left.expr_type == ExpressionType.CONSTANT
            and right_info.get("signedness") in SIGNEDNESS_KINDS
        ):
            narrowed = self._narrow_constant(
                left,
                right_info["bits"],
                right_info["signedness"],
            )
            if narrowed is not None:
                if self._is_all_ones_mask(narrowed, right_info["bits"]) and expr.operator == "INT_AND":
                    return right_info["expr"]
                left_info = {
                    "expr": narrowed,
                    "bits": right_info["bits"],
                    "signedness": right_info["signedness"],
                }

        if left_info is None or right_info is None:
            return None
        if left_info["bits"] != right_info["bits"]:
            return None

        narrow_bits = left_info["bits"]
        if narrow_bits <= 0 or narrow_bits >= expr.get_bit_width():
            return None

        if expr.operator in SIGNED_BINARY_OPS:
            if left_info["signedness"] != "signed" or right_info["signedness"] != "signed":
                return None
        if expr.operator in UNSIGNED_BINARY_OPS:
            if left_info["signedness"] != "unsigned" or right_info["signedness"] != "unsigned":
                return None

        rebuilt = Expression.binary_op(
            expr.operator,
            left_info["expr"],
            right_info["expr"],
        )
        rebuilt.size = max(1, narrow_bits // 8)
        rebuilt.data_type = expr.data_type
        return rebuilt

    def _is_all_ones_mask(self, expr: Expression, bits: int) -> bool:
        if expr.expr_type != ExpressionType.CONSTANT or bits <= 0:
            return False
        mask = (1 << bits) - 1
        value = int(expr.value)
        return (value & mask) == mask

    def _match_comparison_operand(self, expr: Expression):
        widened = self._match_semantic_extension(expr)
        if widened is not None:
            return widened
        return self._match_semantic_low_expr(expr)

    def _match_semantic_extension(self, expr: Expression):
        if expr.expr_type == ExpressionType.PARAMETER:
            hint = self._parameter_hint(expr)
            if hint is not None and expr.get_bit_width() > hint.narrow_bits:
                semantic_signedness = (
                    hint.signedness if hint.signedness in SIGNEDNESS_KINDS else None
                )
                return {
                    "expr": self._low_bits_expr(expr, hint.narrow_bits),
                    "bits": hint.narrow_bits,
                    "signedness": semantic_signedness,
                    "explicit_signedness": hint.signedness_source == "explicit",
                }

        if (
            expr.expr_type == ExpressionType.UNARY_OP
            and expr.operator in {"INT_SEXT", "INT_ZEXT"}
            and expr.operands
        ):
            inner = self._match_any_low_expr(expr.operands[0], expected_signedness=None)
            if inner is None:
                return None
            expected = "signed" if expr.operator == "INT_SEXT" else "unsigned"
            return {
                "expr": inner["expr"],
                "bits": inner["bits"],
                "signedness": expected,
                "explicit_signedness": bool(inner.get("explicit_signedness")),
            }

        return None

    def _match_semantic_low_expr(self, expr: Expression):
        return self._match_any_low_expr(expr, expected_signedness=None)

    def _match_any_low_expr(
        self,
        expr: Expression,
        expected_signedness: Optional[str],
    ):
        if expr.expr_type == ExpressionType.PARAMETER:
            hint = self._parameter_hint(expr)
            if hint is None:
                bits = expr.get_bit_width()
                if bits <= 32:
                    signedness = expected_signedness or "signed"
                    return {
                        "expr": expr,
                        "bits": bits,
                        "signedness": signedness,
                        "explicit_signedness": False,
                    }
                return None
            if expr.get_bit_width() == hint.narrow_bits:
                semantic_signedness = (
                    hint.signedness if hint.signedness in SIGNEDNESS_KINDS else None
                )
                return {
                    "expr": expr,
                    "bits": hint.narrow_bits,
                    "signedness": semantic_signedness,
                    "explicit_signedness": hint.signedness_source == "explicit",
                }
            if expr.get_bit_width() > hint.narrow_bits:
                semantic_signedness = (
                    hint.signedness if hint.signedness in SIGNEDNESS_KINDS else None
                )
                return {
                    "expr": self._low_bits_expr(expr, hint.narrow_bits),
                    "bits": hint.narrow_bits,
                    "signedness": semantic_signedness,
                    "explicit_signedness": hint.signedness_source == "explicit",
                }

        if (
            expr.expr_type == ExpressionType.BINARY_OP
            and expr.operator == "SUBPIECE"
            and len(expr.operands) == 2
        ):
            source, offset = expr.operands
            if offset.expr_type != ExpressionType.CONSTANT or int(offset.value) != 0:
                return None
            if source.expr_type == ExpressionType.PARAMETER:
                hint = self._parameter_hint(source)
                if hint is not None and expr.get_bit_width() == hint.narrow_bits:
                    semantic_signedness = (
                        hint.signedness if hint.signedness in SIGNEDNESS_KINDS else None
                    )
                    return {
                        "expr": expr,
                        "bits": hint.narrow_bits,
                        "signedness": semantic_signedness,
                        "explicit_signedness": hint.signedness_source == "explicit",
                    }
            if expr.get_bit_width() <= 32:
                signedness = expected_signedness or "signed"
                return {
                    "expr": expr,
                    "bits": expr.get_bit_width(),
                    "signedness": signedness,
                    "explicit_signedness": False,
                }

        if (
            expr.expr_type == ExpressionType.BINARY_OP
            and expr.operator == "INT_AND"
            and len(expr.operands) == 2
        ):
            param_expr, const_expr = self._split_mask_expr(expr)
            if param_expr is None or const_expr is None:
                return None
            hint = self._parameter_hint(param_expr)
            if hint is None or hint.narrow_bits >= param_expr.get_bit_width():
                return None
            expected_mask = (1 << hint.narrow_bits) - 1
            mask_bits = const_expr.get_bit_width()
            mask_value = int(const_expr.value) & ((1 << mask_bits) - 1)
            if mask_value != expected_mask:
                return None
            semantic_signedness = (
                hint.signedness if hint.signedness in SIGNEDNESS_KINDS else None
            )
            return {
                "expr": self._low_bits_expr(param_expr, hint.narrow_bits),
                "bits": hint.narrow_bits,
                "signedness": semantic_signedness,
                "explicit_signedness": hint.signedness_source == "explicit",
            }

        return None

    def _parameter_hint(self, expr: Expression) -> Optional[ParameterSemanticHint]:
        if expr.expr_type != ExpressionType.PARAMETER:
            return None
        try:
            index = int(getattr(expr, "value", -1))
        except (TypeError, ValueError):
            index = -1
        if index >= 0:
            hint = self.hints_by_identity.get(("parameter_index", index))
            if hint is not None:
                return hint
        storage_key = _storage_identity_key(getattr(expr, "storage_info", None))
        if storage_key is not None:
            return self.hints_by_identity.get(("parameter_storage", storage_key))
        return None

    def _split_mask_expr(self, expr: Expression):
        left, right = expr.operands
        if left.expr_type == ExpressionType.PARAMETER and right.expr_type == ExpressionType.CONSTANT:
            return left, right
        if right.expr_type == ExpressionType.PARAMETER and left.expr_type == ExpressionType.CONSTANT:
            return right, left
        return None, None

    def _low_bits_expr(self, expr: Expression, narrow_bits: int) -> Expression:
        if expr.get_bit_width() == narrow_bits:
            return expr
        subpiece = Expression.binary_op(
            "SUBPIECE",
            expr,
            Expression.constant(0, size=max(1, expr.size or 1)),
        )
        subpiece.size = max(1, narrow_bits // 8)
        return subpiece

    def _narrow_constant(
        self,
        expr: Expression,
        narrow_bits: int,
        signedness: str,
    ) -> Optional[Expression]:
        if expr.expr_type != ExpressionType.CONSTANT:
            return None

        original_bits = expr.get_bit_width()
        if original_bits < narrow_bits or narrow_bits <= 0:
            return None

        original_mask = (1 << original_bits) - 1
        narrow_mask = (1 << narrow_bits) - 1
        value_mod = int(expr.value) & original_mask
        low_value = value_mod & narrow_mask

        if signedness == "signed":
            sign_bit = 1 << (narrow_bits - 1)
            if low_value & sign_bit:
                expected = low_value | (((1 << (original_bits - narrow_bits)) - 1) << narrow_bits)
            else:
                expected = low_value
        else:
            expected = low_value

        if expected != value_mod:
            return None

        narrowed = low_value
        if signedness == "signed" and narrow_bits > 0:
            sign_bit = 1 << (narrow_bits - 1)
            if low_value & sign_bit:
                narrowed = low_value - (1 << narrow_bits)

        return Expression.constant(narrowed, size=max(1, narrow_bits // 8))


def normalize_analysis_semantic_width(
    analysis: FunctionReturnAnalysis,
    hints: Optional[Dict[int, ParameterSemanticHint]] = None,
    fragment_infos: Optional[Any] = None,
) -> FunctionReturnAnalysis:
    """Return a copy of the analysis with semantic-width rewrites applied."""

    analysis = _synchronize_parameter_expression_metadata(analysis)

    inferred_hints_by_identity = infer_parameter_semantics_by_identity(analysis)
    if hints is None:
        hints_by_identity = inferred_hints_by_identity
    else:
        hints_by_identity = dict(inferred_hints_by_identity)
        hints_by_identity.update(_build_hints_by_object_identity(analysis, hints))
    fragment_infos_by_name = _build_fragment_info_map(fragment_infos)

    normalizer = SemanticWidthNormalizer(hints_by_identity, fragment_infos_by_name)
    return _rewrite_analysis_expressions(
        analysis,
        normalizer.rewrite_expression,
        simplify_conditions=True,
    )


def align_return_value_extension_surfaces(
    analysis1: FunctionReturnAnalysis,
    analysis2: FunctionReturnAnalysis,
) -> Tuple[FunctionReturnAnalysis, FunctionReturnAnalysis]:
    """Align return comparison surfaces only from cross-side extension evidence."""

    surface_alignment = _common_return_extension_surface_alignment(analysis1, analysis2)
    if surface_alignment is None:
        return analysis1, analysis2
    target_bits, evidence = surface_alignment
    return (
        _with_return_extension_surface(analysis1, target_bits, evidence),
        _with_return_extension_surface(analysis2, target_bits, evidence),
    )


def _common_return_extension_surface_alignment(
    analysis1: FunctionReturnAnalysis,
    analysis2: FunctionReturnAnalysis,
) -> Optional[Tuple[int, Dict[str, Any]]]:
    surface1 = analysis1.get_comparison_surface()
    surface2 = analysis2.get_comparison_surface()
    if getattr(surface1, "kind", None) != "return_value" or getattr(surface2, "kind", None) != "return_value":
        return None

    bits1 = _positive_int(getattr(surface1, "explicit_bit_width", None))
    bits2 = _positive_int(getattr(surface2, "explicit_bit_width", None))
    if bits1 is None or bits2 is None:
        return None
    wide_bits = min(bits1, bits2)

    for candidate_bits in RETURN_EXTENSION_SURFACE_CANDIDATE_BITS:
        if candidate_bits > wide_bits or (candidate_bits == wide_bits and bits1 == bits2):
            continue
        profiles1 = _analysis_return_extension_surface_profiles(analysis1, candidate_bits)
        profiles2 = _analysis_return_extension_surface_profiles(analysis2, candidate_bits)
        if profiles1 is None or profiles2 is None:
            continue
        evidence = _return_extension_surface_evidence(candidate_bits, profiles1, profiles2)
        if evidence is not None:
            return candidate_bits, evidence
    return None


def _analysis_return_extension_surface_profiles(
    analysis: FunctionReturnAnalysis,
    candidate_bits: int,
) -> Optional[Tuple[Tuple[str, int], ...]]:
    profiles = []
    for ret in list(getattr(analysis, "returns", None) or []):
        compatible, ret_profiles = _return_expr_supports_extension_surface(
            getattr(ret, "value", None),
            candidate_bits,
        )
        if not compatible:
            return None
        profiles.extend(ret_profiles)
    if not profiles:
        return None
    return tuple(sorted(set(profiles)))


def _return_extension_surface_evidence(
    candidate_bits: int,
    profiles1: Tuple[Tuple[str, int], ...],
    profiles2: Tuple[Tuple[str, int], ...],
) -> Optional[Dict[str, Any]]:
    all_profiles = tuple(sorted(set(tuple(profiles1) + tuple(profiles2))))
    extension_profiles = tuple(profile for profile in all_profiles if profile[0] in RETURN_VALUE_EXTENSION_OPS)
    if not extension_profiles:
        return None
    extension_kinds = tuple(sorted({profile[0] for profile in extension_profiles}))
    if len(extension_kinds) > 1:
        return None
    source_widths = tuple(sorted({int(profile[1]) for profile in extension_profiles}))
    return {
        "source": RETURN_EXTENSION_SURFACE_SOURCE,
        "extension_surface_bit_width": int(candidate_bits),
        "return_width_sign_artifact": True,
        "extension_surface_coercion": RETURN_EXTENSION_SURFACE_COERCION,
        "extension_surface_extension_kind": extension_kinds[0] if extension_kinds else "none",
        "extension_surface_source_bit_widths": source_widths,
    }


def _return_expr_supports_extension_surface(
    expr: Optional[Expression],
    candidate_bits: int,
) -> Tuple[bool, Tuple[Tuple[str, int], ...]]:
    if expr is None:
        return False, ()

    expr_bits = _expression_bit_width(expr)
    if getattr(expr, "expr_type", None) == ExpressionType.CONSTANT:
        if expr_bits == candidate_bits:
            return True, ()
        return False, ()

    if getattr(expr, "expr_type", None) == ExpressionType.PHI and getattr(expr, "value", None):
        profiles = []
        for _condition, value in tuple(getattr(expr, "value", ()) or ()):
            compatible, branch_profiles = _return_expr_supports_extension_surface(value, candidate_bits)
            if not compatible:
                return False, ()
            profiles.extend(branch_profiles)
        return True, tuple(sorted(set(profiles)))

    if getattr(expr, "expr_type", None) == ExpressionType.UNARY_OP and getattr(expr, "operator", None) in RETURN_VALUE_EXTENSION_OPS:
        operands = list(getattr(expr, "operands", None) or [])
        if len(operands) != 1:
            return False, ()
        operand_bits = _expression_bit_width(operands[0])
        if expr_bits >= candidate_bits and 0 < operand_bits <= candidate_bits:
            return True, ((str(getattr(expr, "operator", "")).upper(), int(operand_bits)),)
        return False, ()

    high_zero_piece = _return_piece_zero_extension_profile(expr, candidate_bits)
    if high_zero_piece is not None:
        return True, (high_zero_piece,)

    if expr_bits == candidate_bits:
        return True, (("EXACT_WIDTH", int(candidate_bits)),)
    if 0 < expr_bits < candidate_bits:
        return False, ()

    readonly_evidence = _readonly_reduction_supports_extension_surface(expr, candidate_bits)
    if readonly_evidence is not None:
        return readonly_evidence

    return False, ()


def _return_piece_zero_extension_profile(
    expr: Expression,
    candidate_bits: int,
) -> Optional[Tuple[str, int]]:
    if getattr(expr, "expr_type", None) != ExpressionType.BINARY_OP:
        return None
    if str(getattr(expr, "operator", "") or "").upper() != "PIECE":
        return None
    operands = list(getattr(expr, "operands", None) or [])
    if len(operands) != 2:
        return None
    high, low = operands
    expr_bits = _expression_bit_width(expr)
    low_bits = _expression_bit_width(low)
    high_bits = _expression_bit_width(high)
    if expr_bits <= candidate_bits or low_bits != candidate_bits or high_bits <= 0:
        return None
    if expr_bits != high_bits + low_bits:
        return None
    if getattr(high, "expr_type", None) != ExpressionType.CONSTANT:
        return None
    try:
        high_value = int(getattr(high, "value", None))
    except (TypeError, ValueError):
        return None
    if high_value != 0:
        return None
    return "INT_ZEXT", int(candidate_bits)


def _readonly_reduction_supports_extension_surface(
    expr: Expression,
    candidate_bits: int,
) -> Optional[Tuple[bool, Tuple[Tuple[str, int], ...]]]:
    if getattr(expr, "expr_type", None) != ExpressionType.INTRINSIC:
        return None
    runtime_ref = getattr(expr, "runtime_ref", None)
    if not isinstance(runtime_ref, ReadonlyReductionRef):
        return None

    expr_bits = _expression_bit_width(expr)
    if expr_bits == candidate_bits:
        return True, (("READONLY_EXACT_WIDTH", int(candidate_bits)),)
    if expr_bits < candidate_bits:
        return False, ()

    proof = getattr(runtime_ref, "accumulator_proof", None)
    if proof is None:
        return False, ()
    if not bool(getattr(proof, "return_region_value_proven", False)):
        return False, ()
    if not _readonly_reduction_terms_fit_surface(runtime_ref, candidate_bits):
        return False, ()
    profiles = _readonly_reduction_return_extension_profiles(
        runtime_ref,
        candidate_bits,
        target_bits=expr_bits,
    )
    if not profiles:
        return False, ()
    return True, profiles


def _readonly_reduction_terms_fit_surface(
    runtime_ref: ReadonlyReductionRef,
    candidate_bits: int,
) -> bool:
    candidate_size = max(1, candidate_bits // 8)
    proof = getattr(runtime_ref, "accumulator_proof", None)
    owners = (runtime_ref, proof, getattr(runtime_ref, "loop_summary", None))
    for owner in owners:
        if owner is None:
            continue
        for attr_name in ("element_size", "result_size"):
            value = _positive_int(getattr(owner, attr_name, None))
            if value is not None and value <= candidate_size:
                return True
        for attr_name in (
            "seed_terms",
            "lane_terms",
            "loop_body_witnesses",
            "exact_return_witnesses",
            "semantic_witnesses",
            "witnesses",
        ):
            if _readonly_term_container_fits_surface(getattr(owner, attr_name, None), candidate_size):
                return True
    return False


def _readonly_term_container_fits_surface(value: Any, candidate_size: int) -> bool:
    saw_term = False
    for item in tuple(value or ()):
        access_size = _positive_int(getattr(item, "access_size", None))
        if access_size is not None:
            if access_size > candidate_size:
                return False
            saw_term = True
            continue
        if isinstance(item, tuple) and len(item) >= 2:
            tuple_size = _positive_int(item[1])
            if tuple_size is not None:
                if tuple_size > candidate_size:
                    return False
                saw_term = True
                continue
        terms = getattr(item, "terms", None)
        if terms is not None:
            nested_items = tuple(terms or ())
            if not nested_items:
                continue
            if not _readonly_term_container_fits_surface(nested_items, candidate_size):
                return False
            saw_term = True
    return saw_term


def _readonly_reduction_return_extension_profiles(
    runtime_ref: ReadonlyReductionRef,
    candidate_bits: int,
    *,
    target_bits: int,
) -> Tuple[Tuple[str, int], ...]:
    profiles = []
    proof = getattr(runtime_ref, "accumulator_proof", None)
    for owner in (proof, getattr(runtime_ref, "loop_summary", None), runtime_ref):
        for op_ref in tuple(getattr(owner, "return_value_op_refs", ()) or ()):
            profile = _readonly_return_extension_profile_from_op_ref(
                op_ref,
                candidate_bits,
                target_bits=target_bits,
            )
            if profile is not None:
                profiles.append(profile)
    return tuple(sorted(set(profiles)))


def _readonly_return_extension_profile_from_op_ref(
    op_ref: Any,
    candidate_bits: int,
    *,
    target_bits: int,
) -> Optional[Tuple[str, int]]:
    mnemonic = str(getattr(op_ref, "mnemonic", "") or "").upper()
    if mnemonic not in RETURN_VALUE_EXTENSION_OPS:
        return None
    input_size_fn = getattr(op_ref, "input_size", None)
    if callable(input_size_fn):
        source_size = _positive_int(input_size_fn(0))
    else:
        input_sizes = tuple(getattr(op_ref, "input_sizes", ()) or ())
        source_size = _positive_int(input_sizes[0]) if input_sizes else None
    if source_size is None:
        return None
    source_bits = int(source_size) * 8
    if source_bits != int(candidate_bits):
        return None
    output_size = _positive_int(getattr(op_ref, "output_size", None))
    if output_size is None:
        return None
    output_bits = int(output_size) * 8
    if output_bits <= source_bits:
        return None
    if int(target_bits or 0) > 0 and output_bits < int(target_bits):
        return None
    return mnemonic, source_bits


def _with_return_extension_surface(
    analysis: FunctionReturnAnalysis,
    target_bits: int,
    alignment_evidence: Dict[str, Any],
) -> FunctionReturnAnalysis:
    surface = analysis.get_comparison_surface()
    old_bits = _positive_int(getattr(surface, "explicit_bit_width", None))
    if old_bits == target_bits:
        return analysis

    evidence = dict(getattr(surface, "evidence", None) or {})
    evidence.update(alignment_evidence)
    evidence.update(
        {
            "declared_bit_width": old_bits,
            "extension_surface_bit_width": target_bits,
        }
    )
    return replace(
        analysis,
        comparison_surface=ComparisonSurface(
            kind="return_value",
            explicit_bit_width=target_bits,
            type_name=getattr(surface, "type_name", None),
            type_obj=getattr(surface, "type_obj", None),
            use_sign_extension=False,
            evidence=evidence,
        ),
    )


def _positive_int(value: Any) -> Optional[int]:
    try:
        int_value = int(value)
    except (TypeError, ValueError):
        return None
    return int_value if int_value > 0 else None


def _expression_bit_width(expr: Optional[Expression]) -> int:
    if expr is None:
        return 0
    try:
        return max(0, int(expression_smt_bit_width(expr) or 0))
    except Exception:
        pass
    get_bit_width = getattr(expr, "get_bit_width", None)
    if callable(get_bit_width):
        try:
            return max(0, int(get_bit_width() or 0))
        except Exception:
            return 0
    return 0


def _synchronize_parameter_expression_metadata(
    analysis: FunctionReturnAnalysis,
) -> FunctionReturnAnalysis:
    parameters = list(analysis.parameters or [])
    if not parameters:
        return analysis

    params_by_index: Dict[int, Dict[str, Any]] = {}
    params_by_storage_candidates: Dict[Tuple[object, ...], list[Dict[str, Any]]] = {}
    for param in parameters:
        descriptor = dict(param)
        index = descriptor.get("index")
        if isinstance(index, int) and index >= 0:
            params_by_index[index] = descriptor
        storage_key = _storage_identity_key(descriptor.get("storage_info", descriptor.get("storage")))
        if storage_key is not None:
            params_by_storage_candidates.setdefault(storage_key, []).append(descriptor)
    params_by_storage = {
        storage_key: descriptors[0]
        for storage_key, descriptors in params_by_storage_candidates.items()
        if len(descriptors) == 1
    }

    return _rewrite_analysis_expressions(
        analysis,
        lambda expr: _rewrite_parameter_expression_metadata(
            expr,
            params_by_index,
            params_by_storage,
        ),
        simplify_conditions=False,
    )


def _rewrite_analysis_expressions(
    analysis: FunctionReturnAnalysis,
    rewrite_expr,
    *,
    simplify_conditions: bool,
) -> FunctionReturnAnalysis:
    changed = False
    rewritten_returns = []
    for ret in analysis.returns:
        new_value = rewrite_expr(ret.value)
        new_conditions, conditions_changed = _rewrite_conditions(
            ret.conditions,
            rewrite_expr,
            simplify=simplify_conditions,
        )
        if new_value is not ret.value or conditions_changed:
            changed = True
        rewritten_returns.append(
            replace(
                ret,
                value=new_value,
                conditions=new_conditions,
            )
        )

    rewritten_return_outcomes = []
    for outcome in getattr(analysis, "return_outcomes", ()) or ():
        new_value = rewrite_expr(outcome.value)
        new_guard, guard_changed = _rewrite_conditions(
            outcome.guard,
            rewrite_expr,
            simplify=simplify_conditions,
        )
        new_return_info = outcome.return_info
        if new_return_info is not None:
            info_value = rewrite_expr(new_return_info.value)
            info_conditions, info_conditions_changed = _rewrite_conditions(
                new_return_info.conditions,
                rewrite_expr,
                simplify=simplify_conditions,
            )
            if info_value is not new_return_info.value or info_conditions_changed:
                new_return_info = replace(
                    new_return_info,
                    value=info_value,
                    conditions=info_conditions,
                )
                changed = True
        if new_value is not outcome.value or guard_changed:
            changed = True
        rewritten_return_outcomes.append(
            replace(
                outcome,
                value=new_value,
                guard=tuple(new_guard),
                return_info=new_return_info,
            )
        )

    rewritten_divergence_outcomes = []
    for outcome in getattr(analysis, "divergence_outcomes", ()) or ():
        new_guard, guard_changed = _rewrite_conditions(
            outcome.guard,
            rewrite_expr,
            simplify=simplify_conditions,
        )
        if guard_changed:
            changed = True
        rewritten_divergence_outcomes.append(replace(outcome, guard=tuple(new_guard)))

    rewritten_unknown_outcomes = []
    for outcome in getattr(analysis, "unknown_outcomes", ()) or ():
        new_guard, guard_changed = _rewrite_conditions(
            outcome.guard,
            rewrite_expr,
            simplify=simplify_conditions,
        )
        if guard_changed:
            changed = True
        rewritten_unknown_outcomes.append(replace(outcome, guard=tuple(new_guard)))

    rewritten_effect_summary = _rewrite_effect_summary_expressions(
        getattr(analysis, "effect_summary", None),
        rewrite_expr,
        simplify_conditions=simplify_conditions,
    )
    if rewritten_effect_summary is not getattr(analysis, "effect_summary", None):
        changed = True

    rewritten_comparison_surface = getattr(analysis, "comparison_surface", None)
    if rewritten_comparison_surface is not None and rewritten_comparison_surface.kind == "memory_effect":
        synthetic_expr = (
            getattr(rewritten_effect_summary, "synthetic_expr", None)
            if rewritten_effect_summary is not None
            else None
        )
        explicit_bits = 0
        if synthetic_expr is not None:
            get_bit_width = getattr(synthetic_expr, "get_bit_width", None)
            if callable(get_bit_width):
                try:
                    explicit_bits = max(0, int(get_bit_width() or 0))
                except Exception:
                    explicit_bits = 0
        if explicit_bits > 0 and explicit_bits != rewritten_comparison_surface.explicit_bit_width:
            changed = True
            rewritten_comparison_surface = replace(
                rewritten_comparison_surface,
                explicit_bit_width=explicit_bits,
            )

    if not changed:
        return analysis

    return replace(
        analysis,
        returns=rewritten_returns,
        return_outcomes=tuple(rewritten_return_outcomes),
        divergence_outcomes=tuple(rewritten_divergence_outcomes),
        unknown_outcomes=tuple(rewritten_unknown_outcomes),
        effect_summary=rewritten_effect_summary,
        comparison_surface=rewritten_comparison_surface,
    )

def _rewrite_conditions(
    conditions,
    rewrite_expr,
    *,
    simplify: bool,
):
    rewritten = []
    width_changed = False
    for cond in conditions or []:
        condition_expr = rewrite_expr(cond.expression)
        condition_expr, condition_width_changed = _normalize_condition_comparison_constant_widths(condition_expr)
        width_changed = width_changed or condition_width_changed
        rewritten.append(Condition(condition_expr, cond.negated))
    if simplify:
        rewritten = ConditionSimplifier.simplify_conditions(rewritten)

    changed = width_changed
    original = list(conditions or [])
    if len(rewritten) != len(original):
        changed = True
    else:
        changed = any(
            new.expression is not old.expression or new.negated != old.negated
            for new, old in zip(rewritten, original)
        )
    return rewritten, changed


def _normalize_condition_comparison_constant_widths(expr: Optional[Expression]) -> Tuple[Optional[Expression], bool]:
    if expr is None or not getattr(expr, "operands", None):
        return expr, False

    changed = False
    new_operands = []
    for operand in expr.operands:
        new_operand, operand_changed = _normalize_condition_comparison_constant_widths(operand)
        changed = changed or operand_changed
        new_operands.append(new_operand)

    current = expr.clone_with(operands=new_operands) if changed else expr
    if (
        current.expr_type != ExpressionType.BINARY_OP
        or current.operator not in COMPARISON_OPS
        or len(current.operands or ()) != 2
    ):
        return current, changed

    left, right = current.operands
    coerced_left, left_changed = _coerce_constant_operand_width(left, right)
    coerced_right, right_changed = _coerce_constant_operand_width(right, left)
    if not left_changed and not right_changed:
        return current, changed
    return current.clone_with(operands=[coerced_left, coerced_right]), True


def _coerce_constant_operand_width(candidate: Expression, peer: Expression) -> Tuple[Expression, bool]:
    if candidate is None or peer is None or candidate.expr_type != ExpressionType.CONSTANT:
        return candidate, False
    try:
        if int(candidate.value) != 0:
            return candidate, False
    except (TypeError, ValueError):
        return candidate, False
    peer_size = int(getattr(peer, "size", 0) or 0)
    if peer_size > 0:
        desired_size = peer_size
    else:
        peer_bits = _expression_bit_width(peer)
        if peer_bits <= 0 or peer_bits % 8 != 0:
            return candidate, False
        desired_size = max(1, peer_bits // 8)
    if int(getattr(candidate, "size", 0) or 0) == desired_size:
        return candidate, False
    return candidate.clone_with(size=desired_size), True


def _rewrite_effect_summary_expressions(
    effect_summary,
    rewrite_expr,
    *,
    simplify_conditions: bool,
):
    if effect_summary is None:
        return None

    changed = False
    rewritten_effects = []
    for effect in getattr(effect_summary, "effects", []) or []:
        new_value = rewrite_expr(effect.value)
        new_conditions, conditions_changed = _rewrite_conditions(
            effect.conditions,
            rewrite_expr,
            simplify=simplify_conditions,
        )
        if new_value is not effect.value or conditions_changed:
            changed = True
        rewritten_effects.append(
            replace(
                effect,
                value=new_value,
                conditions=new_conditions,
            )
        )

    new_synthetic_expr = rewrite_expr(getattr(effect_summary, "synthetic_expr", None))
    if new_synthetic_expr is not getattr(effect_summary, "synthetic_expr", None):
        changed = True

    if not changed:
        return effect_summary

    return replace(
        effect_summary,
        effects=rewritten_effects,
        synthetic_expr=new_synthetic_expr,
    )


def _rewrite_parameter_expression_metadata(
    expr: Optional[Expression],
    params_by_index: Dict[int, Dict[str, Any]],
    params_by_storage: Dict[Tuple[object, ...], Dict[str, Any]],
) -> Optional[Expression]:
    if expr is None:
        return expr

    if expr.expr_type == ExpressionType.PARAMETER:
        descriptor = None
        has_index = isinstance(expr.value, int) and expr.value >= 0
        if has_index:
            descriptor = params_by_index.get(expr.value)
        else:
            storage_key = _storage_identity_key(getattr(expr, "storage_info", None))
            if storage_key is not None:
                descriptor = params_by_storage.get(storage_key)
        if descriptor is None:
            return expr

        desired_size = int(descriptor.get("size", 0) or 0)
        desired_type = descriptor.get("data_type") or expr.data_type
        desired_index = descriptor.get("index", expr.value)
        if (
            desired_size <= 0 or
            (
                desired_size == expr.size and
                desired_type == expr.data_type and
                desired_index == expr.value
            )
        ):
            return expr

        return Expression(
            expr_type=expr.expr_type,
            value=desired_index,
            operator=expr.operator,
            operands=list(expr.operands or []),
            size=desired_size,
            name=expr.name,
            data_type=desired_type,
            storage_info=expr.storage_info,
            read_order_key=expr.read_order_key,
            runtime_ref=getattr(expr, "runtime_ref", None),
            opcode=getattr(expr, "opcode", None),
        )

    if expr.expr_type == ExpressionType.PHI and expr.value:
        changed = False
        branches = []
        for cond, value in expr.value:
            new_cond = None
            if cond is not None:
                new_cond_expr = _rewrite_parameter_expression_metadata(
                    cond.expression,
                    params_by_index,
                    params_by_storage,
                )
                new_cond = Condition(new_cond_expr, cond.negated)
                changed = changed or (new_cond_expr is not cond.expression)
            new_value = _rewrite_parameter_expression_metadata(
                value,
                params_by_index,
                params_by_storage,
            )
            changed = changed or (new_value is not value)
            branches.append((new_cond, new_value))
        if not changed:
            return expr
        rebuilt = Expression.phi(branches)
        rebuilt.size = expr.size
        rebuilt.data_type = expr.data_type
        rebuilt.data_type_obj = getattr(expr, "data_type_obj", None)
        rebuilt.storage_info = expr.storage_info
        rebuilt.read_order_key = expr.read_order_key
        return rebuilt

    operands = getattr(expr, "operands", None) or []
    if not operands:
        return expr

    new_operands = [
        _rewrite_parameter_expression_metadata(
            operand,
            params_by_index,
            params_by_storage,
        )
        for operand in operands
    ]
    if all(new is old for new, old in zip(new_operands, operands)):
        return expr

    return Expression(
        expr_type=expr.expr_type,
        value=expr.value,
        operator=expr.operator,
        operands=new_operands,
        size=expr.size,
        name=expr.name,
        data_type=expr.data_type,
        data_type_obj=getattr(expr, "data_type_obj", None),
        storage_info=expr.storage_info,
        read_order_key=expr.read_order_key,
        runtime_ref=getattr(expr, "runtime_ref", None),
        opcode=getattr(expr, "opcode", None),
    )


def _build_hints_by_object_identity(
    analysis: FunctionReturnAnalysis,
    hints: Dict[int, ParameterSemanticHint],
) -> Dict[Tuple[object, ...], ParameterSemanticHint]:
    hints_by_identity: Dict[Tuple[object, ...], ParameterSemanticHint] = {}
    for param in analysis.parameters or []:
        try:
            index = int(param.get("index"))
        except (TypeError, ValueError):
            continue
        if index < 0:
            continue
        hint = hints.get(index)
        if hint is None:
            continue
        hints_by_identity[("parameter_index", index)] = hint
        storage_key = _storage_identity_key(param.get("storage_info", param.get("storage")))
        if storage_key is not None:
            hints_by_identity[("parameter_storage", storage_key)] = hint
    return hints_by_identity


def _storage_identity_key(storage_info) -> Optional[Tuple[object, ...]]:
    storage_info = _coerce_storage_info(storage_info)
    if storage_info is None:
        return None
    storage_key_fn = getattr(storage_info, "storage_identity_key", None)
    if not callable(storage_key_fn):
        return None
    try:
        storage_key = storage_key_fn()
    except (TypeError, ValueError):
        return None
    return storage_key if storage_key is not None else None


def _coerce_storage_info(storage_info) -> Optional[StorageInfo]:
    if storage_info is None:
        return None
    if isinstance(storage_info, StorageInfo):
        return storage_info
    if not isinstance(storage_info, dict):
        return None
    try:
        kind = str(storage_info.get("kind", "") or storage_info.get("space_name", "") or "").lower()
        is_register = bool(storage_info.get("is_register", False)) or kind == "register"
        return StorageInfo(
            is_register=is_register,
            space_name=str(storage_info.get("space_name") or ("register" if is_register else "")),
            space_id=storage_info.get("space_id"),
            offset=int(storage_info.get("offset", 0) or 0),
            size=int(storage_info.get("size", 0) or 0),
            size_bits=int(storage_info.get("size_bits", 0) or 0),
            register_name=storage_info.get("register_name"),
            register_offset=storage_info.get("register_offset"),
            register_size=storage_info.get("register_size"),
            register_size_bits=storage_info.get("register_size_bits"),
            base_register_name=storage_info.get("base_register_name"),
            base_register_offset=int(storage_info.get("base_register_offset", 0) or 0),
            base_register_size=int(storage_info.get("base_register_size", 0) or 0),
            base_register_size_bits=int(storage_info.get("base_register_size_bits", 0) or 0),
            bit_offset_in_base=int(storage_info.get("bit_offset_in_base", 0) or 0),
            is_stack_pointer=bool(storage_info.get("is_stack_pointer", False)),
            is_frame_pointer=bool(storage_info.get("is_frame_pointer", False)),
        )
    except Exception:
        return None


def _build_fragment_info_map(fragment_infos: Optional[Any]) -> Dict[str, Any]:
    if fragment_infos is None:
        return {}

    if isinstance(fragment_infos, dict):
        items: Iterable[Any] = fragment_infos.values()
    else:
        items = fragment_infos

    result: Dict[str, Any] = {}
    for item in items:
        if item is None:
            continue

        analysis = getattr(item, "analysis", None)
        candidate = analysis if analysis is not None else item
        fragment_info = getattr(candidate, "fragment_info", None)
        if fragment_info is None:
            continue

        fragment_name = (
            getattr(item, "original_name", None)
            or getattr(candidate, "name", None)
            or getattr(fragment_info, "fragment_name", None)
        )
        if fragment_name:
            result[fragment_name] = fragment_info

    return result
