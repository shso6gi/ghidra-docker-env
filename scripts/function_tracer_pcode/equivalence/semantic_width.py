# -*- coding: utf-8 -*-
"""Semantic-width aware expression normalization."""

from __future__ import annotations

from dataclasses import replace
from typing import Any, Dict, Iterable, Optional

from ..analysis.condition.simplifier import ConditionSimplifier
from ..model import Condition, Expression, ExpressionType, FunctionReturnAnalysis, ReturnInfo
from .param_semantics import ParameterSemanticHint, infer_parameter_semantics


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


class SemanticWidthNormalizer:
    """Normalize expressions using explicit semantic-width hints."""

    def __init__(
        self,
        hints_by_name: Dict[str, ParameterSemanticHint],
        fragment_infos_by_name: Optional[Dict[str, Any]] = None,
    ):
        self.hints_by_name = hints_by_name
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

        if left_info is not None and right.expr_type == ExpressionType.CONSTANT:
            right_narrow = self._narrow_constant(right, left_info["bits"], left_info["signedness"])
            if right_narrow is not None:
                rebuilt = Expression.binary_op(expr.operator, left_info["expr"], right_narrow)
                rebuilt.size = expr.size
                return rebuilt

        if right_info is not None and left.expr_type == ExpressionType.CONSTANT:
            left_narrow = self._narrow_constant(left, right_info["bits"], right_info["signedness"])
            if left_narrow is not None:
                rebuilt = Expression.binary_op(expr.operator, left_narrow, right_info["expr"])
                rebuilt.size = expr.size
                return rebuilt

        if left_info is None or right_info is None:
            return None
        if left_info["bits"] != right_info["bits"]:
            return None

        rebuilt = Expression.binary_op(expr.operator, left_info["expr"], right_info["expr"])
        rebuilt.size = expr.size
        return rebuilt

    def _match_comparison_operand(self, expr: Expression):
        widened = self._match_semantic_extension(expr)
        if widened is not None:
            return widened
        return self._match_semantic_low_expr(expr)

    def _match_semantic_extension(self, expr: Expression):
        if expr.expr_type == ExpressionType.PARAMETER and expr.name:
            hint = self.hints_by_name.get(expr.name)
            if hint is not None and expr.get_bit_width() > hint.narrow_bits:
                return {
                    "expr": self._low_bits_expr(expr, hint.narrow_bits),
                    "bits": hint.narrow_bits,
                    "signedness": hint.signedness,
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
            }

        return None

    def _match_semantic_low_expr(self, expr: Expression):
        return self._match_any_low_expr(expr, expected_signedness=None)

    def _match_any_low_expr(
        self,
        expr: Expression,
        expected_signedness: Optional[str],
    ):
        if expr.expr_type == ExpressionType.PARAMETER and expr.name:
            hint = self.hints_by_name.get(expr.name)
            if hint is None:
                bits = expr.get_bit_width()
                if bits <= 32:
                    signedness = expected_signedness or "signed"
                    return {"expr": expr, "bits": bits, "signedness": signedness}
                return None
            if expr.get_bit_width() == hint.narrow_bits:
                return {"expr": expr, "bits": hint.narrow_bits, "signedness": hint.signedness}
            if expr.get_bit_width() > hint.narrow_bits:
                return {
                    "expr": self._low_bits_expr(expr, hint.narrow_bits),
                    "bits": hint.narrow_bits,
                    "signedness": hint.signedness,
                }

        if (
            expr.expr_type == ExpressionType.BINARY_OP
            and expr.operator == "SUBPIECE"
            and len(expr.operands) == 2
        ):
            source, offset = expr.operands
            if offset.expr_type != ExpressionType.CONSTANT or int(offset.value) != 0:
                return None
            if source.expr_type == ExpressionType.PARAMETER and source.name:
                hint = self.hints_by_name.get(source.name)
                if hint is not None and expr.get_bit_width() == hint.narrow_bits:
                    return {"expr": expr, "bits": hint.narrow_bits, "signedness": hint.signedness}
            if expr.get_bit_width() <= 32:
                signedness = expected_signedness or "signed"
                return {"expr": expr, "bits": expr.get_bit_width(), "signedness": signedness}

        if (
            expr.expr_type == ExpressionType.BINARY_OP
            and expr.operator == "INT_AND"
            and len(expr.operands) == 2
        ):
            param_expr, const_expr = self._split_mask_expr(expr)
            if param_expr is None or const_expr is None or not param_expr.name:
                return None
            hint = self.hints_by_name.get(param_expr.name)
            if hint is None or hint.narrow_bits >= param_expr.get_bit_width():
                return None
            expected_mask = (1 << hint.narrow_bits) - 1
            mask_bits = const_expr.get_bit_width()
            mask_value = int(const_expr.value) & ((1 << mask_bits) - 1)
            if mask_value != expected_mask:
                return None
            return {
                "expr": self._low_bits_expr(param_expr, hint.narrow_bits),
                "bits": hint.narrow_bits,
                "signedness": hint.signedness,
            }

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

    if hints is None:
        hints = infer_parameter_semantics(analysis)

    hints_by_name = _build_hints_by_name(analysis, hints)
    fragment_infos_by_name = _build_fragment_info_map(fragment_infos)

    normalizer = SemanticWidthNormalizer(hints_by_name, fragment_infos_by_name)
    return _rewrite_analysis_expressions(
        analysis,
        normalizer.rewrite_expression,
        simplify_conditions=True,
    )


def _synchronize_parameter_expression_metadata(
    analysis: FunctionReturnAnalysis,
) -> FunctionReturnAnalysis:
    parameters = list(analysis.parameters or [])
    if not parameters:
        return analysis

    params_by_name: Dict[str, Dict[str, Any]] = {}
    params_by_index: Dict[int, Dict[str, Any]] = {}
    for fallback_index, param in enumerate(parameters):
        descriptor = dict(param)
        name = descriptor.get("name")
        if isinstance(name, str) and name:
            params_by_name[name] = descriptor
        index = descriptor.get("index", fallback_index)
        if isinstance(index, int) and index >= 0:
            params_by_index[index] = descriptor

    return _rewrite_analysis_expressions(
        analysis,
        lambda expr: _rewrite_parameter_expression_metadata(
            expr,
            params_by_name,
            params_by_index,
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
        effect_summary=rewritten_effect_summary,
        comparison_surface=rewritten_comparison_surface,
    )


def _rewrite_conditions(
    conditions,
    rewrite_expr,
    *,
    simplify: bool,
):
    rewritten = [
        Condition(rewrite_expr(cond.expression), cond.negated)
        for cond in (conditions or [])
    ]
    if simplify:
        rewritten = ConditionSimplifier.simplify_conditions(rewritten)

    changed = False
    original = list(conditions or [])
    if len(rewritten) != len(original):
        changed = True
    else:
        changed = any(
            new.expression is not old.expression or new.negated != old.negated
            for new, old in zip(rewritten, original)
        )
    return rewritten, changed


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
    params_by_name: Dict[str, Dict[str, Any]],
    params_by_index: Dict[int, Dict[str, Any]],
) -> Optional[Expression]:
    if expr is None:
        return expr

    if expr.expr_type == ExpressionType.PARAMETER:
        descriptor = None
        if expr.name:
            descriptor = params_by_name.get(expr.name)
        if descriptor is None and isinstance(expr.value, int) and expr.value >= 0:
            descriptor = params_by_index.get(expr.value)
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
                    params_by_name,
                    params_by_index,
                )
                new_cond = Condition(new_cond_expr, cond.negated)
                changed = changed or (new_cond_expr is not cond.expression)
            new_value = _rewrite_parameter_expression_metadata(
                value,
                params_by_name,
                params_by_index,
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
            params_by_name,
            params_by_index,
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


def _rewrite_effect_summary(effect_summary, normalizer: SemanticWidthNormalizer):
    return _rewrite_effect_summary_expressions(
        effect_summary,
        normalizer.rewrite_expression,
        simplify_conditions=True,
    )


def _build_hints_by_name(
    analysis: FunctionReturnAnalysis,
    hints: Dict[int, ParameterSemanticHint],
) -> Dict[str, ParameterSemanticHint]:
    hints_by_name: Dict[str, ParameterSemanticHint] = {}
    for fallback_index, param in enumerate(analysis.parameters or []):
        index = param.get("index", fallback_index)
        hint = hints.get(index)
        if hint is None:
            continue
        name = param.get("name", f"param_{fallback_index}")
        hints_by_name[name] = hint
    return hints_by_name


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
