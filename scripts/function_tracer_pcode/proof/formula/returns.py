# -*- coding: utf-8 -*-
"""FormulaBuilder の return 定義関連ヘルパー。"""

from __future__ import annotations

from functools import cmp_to_key
from typing import Dict, List, Optional, Tuple

from scripts.function_tracer_pcode.analysis.effects.summary import (
    lower_post_state_expression_for_smt_if_needed,
)
from scripts.function_tracer_pcode.analysis.condition.simplifier import ConditionSimplifier
from scripts.function_tracer_pcode.core import (
    Expression,
    FunctionReturnAnalysis,
    ReadonlyReductionRef,
)
from scripts.function_tracer_pcode.core.signature import (
    get_declared_type_size_bits,
    get_declared_type_signedness,
    is_undefined_data_type,
    is_unsigned_data_type,
)
from scripts.function_tracer_pcode.core.render_smt import (
    expression_contains_unsupported_smt_ops,
    expression_contains_signed_comparison,
    expression_returns_bool,
    expression_renders_as_fp_sort,
    expression_smt_bit_width,
)
from scripts.function_tracer_pcode.analysis.condition.normalizer import ConditionNormalizer
from scripts.function_tracer_pcode.proof.formula.params import build_symbol_name_mapping
from scripts.function_tracer_pcode.proof.formula.types import ParameterInfo


RETURN_WIDTH_BRIDGE_MISSING_REASON = "return_width_bridge_missing"


class ReturnWidthMismatchError(ValueError):
    """Raised when a proof would compare only overlapping return bits."""

    def __init__(
        self,
        message: str,
        *,
        context: Optional[str] = None,
        return_size1: Optional[int] = None,
        return_size2: Optional[int] = None,
        reason_id: str = RETURN_WIDTH_BRIDGE_MISSING_REASON,
    ):
        super().__init__(message)
        self.context = context
        self.return_size1 = return_size1
        self.return_size2 = return_size2
        self.reason_id = reason_id


def require_equal_return_bit_widths(
    return_size1: int,
    return_size2: int,
    *,
    context: str = "return value comparison",
) -> int:
    """Return the common width, or reject an unbridged return-width mismatch."""
    try:
        bits1 = int(return_size1)
        bits2 = int(return_size2)
    except (TypeError, ValueError) as exc:
        raise ReturnWidthMismatchError(
            f"{context}: invalid return width ({return_size1!r} vs {return_size2!r})",
            context=context,
            return_size1=None,
            return_size2=None,
        ) from exc
    if bits1 <= 0 or bits2 <= 0:
        raise ReturnWidthMismatchError(
            f"{context}: invalid return width ({bits1} vs {bits2})",
            context=context,
            return_size1=bits1,
            return_size2=bits2,
        )
    if bits1 != bits2:
        raise ReturnWidthMismatchError(
            f"{context}: return width mismatch ({bits1} vs {bits2}); explicit bridge proof required",
            context=context,
            return_size1=bits1,
            return_size2=bits2,
        )
    return bits1


def get_return_size(analysis: FunctionReturnAnalysis) -> int:
    """SMT return variable width for the active comparison surface."""
    comparison_surface_getter = getattr(analysis, "get_comparison_surface", None)
    comparison_surface = comparison_surface_getter() if callable(comparison_surface_getter) else None
    surface_kind = getattr(comparison_surface, "kind", None)

    if surface_kind == "memory_effect":
        get_memory_effect_bit_width = getattr(analysis, "get_memory_effect_bit_width", None)
        if callable(get_memory_effect_bit_width):
            bits = int(get_memory_effect_bit_width() or 0)
            if bits > 0:
                return bits
        explicit_bits = getattr(comparison_surface, "explicit_bit_width", None)
        try:
            bits = int(explicit_bits or 0)
        except (TypeError, ValueError):
            bits = 0
        if bits > 0:
            return bits

    if surface_kind == "return_value":
        get_return_value_solver_bit_width = getattr(analysis, "get_return_value_solver_bit_width", None)
        if callable(get_return_value_solver_bit_width):
            bits = int(get_return_value_solver_bit_width() or 0)
            if bits > 0:
                return bits
        explicit_bits = getattr(comparison_surface, "explicit_bit_width", None)
        try:
            bits = int(explicit_bits or 0)
        except (TypeError, ValueError):
            bits = 0
        if bits > 0:
            return bits

    declared_bits = get_declared_return_size_bits(
        analysis.return_type,
        return_type_obj=getattr(analysis, "return_type_obj", None),
    )
    if declared_bits is not None:
        return declared_bits

    expr_bits = [
        ret.value.get_bit_width()
        for ret in analysis.returns
        if ret.value is not None
    ]
    if expr_bits:
        return max(expr_bits)
    return 32


def get_declared_return_size_bits(
    return_type: Optional[str],
    return_type_obj=None,
) -> Optional[int]:
    """型名から戻り値のビット幅を推定する。"""
    return get_declared_type_size_bits(
        return_type_obj,
        return_type,
    )


def is_boolean_return_expr(expr: Expression) -> bool:
    """戻り値式が SMT 上で Bool sort を返すかを判定する。"""
    return expression_returns_bool(expr)


def coerce_return_value_to_bitvec(
    expr: Expression,
    value_smt: str,
    return_size: int,
) -> str:
    """Bool sort の戻り値を bitvector 0/1 に正規化する。"""
    if is_boolean_return_expr(expr):
        return f"(ite {value_smt} (_ bv1 {return_size}) (_ bv0 {return_size}))"
    if expression_renders_as_fp_sort(expr, float_mode="fp"):
        return f"((_ fp.to_ieee_bv) {value_smt})"
    return value_smt


def should_sign_extend_return_type(
    return_type: Optional[str],
    return_type_obj=None,
) -> bool:
    """return型名から sign extension の要否を判定する。"""
    if not return_type and return_type_obj is None:
        return False
    if is_undefined_data_type(return_type_obj, return_type):
        return False
    if is_unsigned_data_type(return_type_obj, return_type):
        return False
    signedness = get_declared_type_signedness(
        return_type_obj,
        return_type,
        fallback_signed=True,
    )
    return bool(signedness)


def has_signed_branch_evidence(expr: Expression, conditions) -> bool:
    """値式やガード条件に signed 比較の証拠があるか判定する。"""
    if expression_contains_signed_comparison(expr):
        return True

    for condition in conditions or []:
        condition_expr = getattr(condition, "expression", None)
        if condition_expr is not None and expression_contains_signed_comparison(condition_expr):
            return True

    return False


def should_sign_extend_value(
    return_type: Optional[str],
    expr: Expression,
    conditions,
    return_type_obj=None,
) -> bool:
    """return_type だけでなく branch evidence も見て sign extension の要否を判定する。"""
    if should_sign_extend_return_type(return_type, return_type_obj=return_type_obj):
        return True
    return has_signed_branch_evidence(expr, conditions)


def expression_has_unresolved_value(expr: Optional[Expression]) -> bool:
    """ソルバへ流せない未解決値を含むか判定する。"""
    if expr is None:
        return True

    expr_type = getattr(expr, "expr_type", None)
    expr_kind = getattr(expr_type, "__class__", None)
    if expr_type is None or expr_kind is None:
        return True

    if expr_type == expr_kind.UNKNOWN:
        return True
    if expression_contains_unsupported_smt_ops(expr):
        return True

    if expr_type == expr_kind.PHI and expr.value:
        for cond, value in expr.value:
            cond_expr = getattr(cond, "expression", None) if cond is not None else None
            if cond_expr is not None and expression_has_unresolved_value(cond_expr):
                return True
            if expression_has_unresolved_value(value):
                return True
        return False

    for operand in getattr(expr, "operands", []) or []:
        if expression_has_unresolved_value(operand):
            return True

    return False


def _rewrite_ambiguous_negative_constant(
    expr: Expression,
    value_smt: str,
    target_size: int,
    use_sign_extension: bool,
) -> str:
    """32bit 由来の負定数が 64bit で zero-extended されていたら sign-extended に補正する。"""
    if not use_sign_extension:
        return value_smt
    if expr.expr_type != expr.expr_type.__class__.CONSTANT:
        return value_smt
    if target_size <= 32:
        return value_smt
    if not isinstance(expr.value, int) or expr.value < 0 or expr.value > 0xffffffff:
        return value_smt
    if (expr.value & 0x80000000) == 0:
        return value_smt

    sign_extended = expr.value | (((1 << (target_size - 32)) - 1) << 32)
    return f"(_ bv{sign_extended} {target_size})"


def coerce_value_to_bitvec_width(
    expr: Expression,
    value_smt: str,
    target_size: int,
    use_sign_extension: bool = False,
) -> str:
    """値式を target_size の bitvector に揃える。"""
    value_smt = coerce_return_value_to_bitvec(expr, value_smt, target_size)
    value_smt = _rewrite_ambiguous_negative_constant(
        expr,
        value_smt,
        target_size,
        use_sign_extension,
    )

    expr_bits = expression_smt_bit_width(expr)
    if expr_bits == target_size:
        return value_smt

    if expr_bits < target_size:
        extend_bits = target_size - expr_bits
        op = "sign_extend" if use_sign_extension else "zero_extend"
        return f"((_ {op} {extend_bits}) {value_smt})"

    return f"((_ extract {target_size - 1} 0) {value_smt})"


def build_ite_expression(return_defs: List[Dict[str, str]], return_size: int) -> str:
    """条件付き return 定義から ite 式を構築する。"""
    if not return_defs:
        return f"(_ bv0 {return_size})"

    result = f"(_ bv0 {return_size})"
    for ret_def in reversed(return_defs):
        cond = ret_def["condition"]
        value = ret_def["value"]
        if cond == "true":
            result = value
        else:
            result = f"(ite {cond} {value} {result})"
    return result


def _build_relation_return_definition(
    return_defs: List[Dict[str, object]],
    return_var_name: str,
    return_size: int,
) -> List[str]:
    lines = [f"(declare-const {return_var_name} (_ BitVec {return_size}))"]

    disjuncts: List[str] = []
    negated_conditions: List[str] = []
    has_unconditional = False
    for ret_def in return_defs:
        cond = str(ret_def["condition"])
        value = str(ret_def["value"])
        if cond == "true":
            disjuncts.append(f"(= {return_var_name} {value})")
            has_unconditional = True
            break
        negated_conditions.append(f"(not {cond})")
        disjuncts.append(f"(and {cond} (= {return_var_name} {value}))")

    if not has_unconditional:
        default_guard = "true"
        if negated_conditions:
            default_guard = (
                negated_conditions[0]
                if len(negated_conditions) == 1
                else f"(and {' '.join(negated_conditions)})"
            )
        disjuncts.append(f"(and {default_guard} (= {return_var_name} (_ bv0 {return_size})))")
    if len(disjuncts) == 1:
        lines.append(f"(assert {disjuncts[0]})")
    else:
        lines.append(f"(assert (or {' '.join(disjuncts)}))")
    return lines


def _return_defs_require_relation(return_defs: List[Dict[str, object]]) -> bool:
    for i, left in enumerate(return_defs):
        for right in return_defs[i + 1 :]:
            if left["value_key"] == right["value_key"]:
                continue
            combined = list(left["raw_conditions"]) + list(right["raw_conditions"])
            if not ConditionSimplifier.object_centric_is_contradiction(combined):
                left_implies_right = left["condition_set"].implies_all(right["raw_conditions"])
                right_implies_left = right["condition_set"].implies_all(left["raw_conditions"])
                if left_implies_right != right_implies_left:
                    continue
                return True
    return False


def _readonly_ref_from_value(value) -> Optional[ReadonlyReductionRef]:
    runtime_ref = getattr(value, "runtime_ref", None)
    if isinstance(runtime_ref, ReadonlyReductionRef):
        return runtime_ref
    return None


def _readonly_ref_count_storage_identity(ref: ReadonlyReductionRef) -> Optional[Tuple[object, ...]]:
    storage_key = getattr(ref, "count_parameter_storage_identity_key", None)
    if storage_key is None:
        return None
    return ("parameter_storage", tuple(storage_key))


def _readonly_ref_count_index_identity(ref: ReadonlyReductionRef) -> Optional[Tuple[object, ...]]:
    index = getattr(ref, "count_parameter_index", None)
    try:
        if index is not None and int(index) >= 0:
            return ("parameter", int(index))
    except (TypeError, ValueError):
        return None
    return None


def _readonly_refs_count_identity_compatible(
    left: ReadonlyReductionRef,
    right: ReadonlyReductionRef,
) -> bool:
    left_storage = _readonly_ref_count_storage_identity(left)
    right_storage = _readonly_ref_count_storage_identity(right)
    if left_storage is not None and right_storage is not None:
        return left_storage == right_storage
    left_index = _readonly_ref_count_index_identity(left)
    right_index = _readonly_ref_count_index_identity(right)
    return left_index is not None and right_index is not None and left_index == right_index


def _readonly_refs_share_surface(left: ReadonlyReductionRef, right: ReadonlyReductionRef) -> bool:
    left_pointer = left.pointer_base_ref.semantic_key()
    right_pointer = right.pointer_base_ref.semantic_key()
    if left_pointer is None or right_pointer is None or left_pointer != right_pointer:
        return False
    if not _readonly_refs_count_identity_compatible(left, right):
        return False
    return (
        str(left.reduction_kind) == str(right.reduction_kind)
        and max(1, int(left.result_size or 0)) == max(1, int(right.result_size or 0))
        and bool(left.signed_counter) == bool(right.signed_counter)
        and int(getattr(left, "constant_bias", 0) or 0)
        == int(getattr(right, "constant_bias", 0) or 0)
    )


def _readonly_ref_priority_key(
    ref: ReadonlyReductionRef,
    *,
    return_size: int,
) -> Tuple[int, int, int, int, int]:
    contract_key = ref.readonly_term_sequence_contract_key(result_size=return_size)
    has_contract = 1 if contract_key is not None else 0
    proof = getattr(ref, "accumulator_proof", None)
    has_proof = 1 if proof is not None else 0
    return_region_proven = 1 if bool(getattr(proof, "return_region_value_proven", False)) else 0
    score_fn = getattr(ref, "readonly_term_sequence_specificity_score", None)
    try:
        specificity = max(0, int(score_fn())) if callable(score_fn) else 0
    except (TypeError, ValueError):
        specificity = 0
    witness_count = len(tuple(getattr(ref, "semantic_witnesses", ()) or ()))
    if proof is not None:
        witness_count += len(tuple(getattr(proof, "loop_body_witnesses", ()) or ()))
        witness_count += len(tuple(getattr(proof, "exact_return_witnesses", ()) or ()))
    return (
        has_contract,
        has_proof,
        return_region_proven,
        int(specificity),
        int(witness_count),
    )


def _compare_readonly_summary_priority(
    left: Dict[str, object],
    right: Dict[str, object],
    *,
    return_size: int,
) -> int:
    return compare_readonly_summary_values_by_priority(
        left.get("raw_value"),
        left["raw_conditions"],
        right.get("raw_value"),
        right["raw_conditions"],
        return_size=return_size,
    )


def compare_readonly_summary_values_by_priority(
    left_value,
    left_conditions,
    right_value,
    right_conditions,
    *,
    return_size: int,
) -> int:
    """Order overlapping readonly summaries by object-level proof precision.

    Returns ``-1`` when the left value should shadow the right value, ``1`` for
    the reverse, and ``0`` when normal condition ordering should decide.
    """

    left_ref = _readonly_ref_from_value(left_value)
    right_ref = _readonly_ref_from_value(right_value)
    if left_ref is None or right_ref is None:
        return 0
    if not _readonly_refs_share_surface(left_ref, right_ref):
        return 0
    left_contract = left_ref.readonly_term_sequence_contract_key(result_size=return_size)
    right_contract = right_ref.readonly_term_sequence_contract_key(result_size=return_size)
    if left_contract is not None and left_contract == right_contract:
        return 0
    if ConditionSimplifier.object_centric_is_contradiction(
        list(left_conditions or []) + list(right_conditions or [])
    ):
        return 0
    left_set = ConditionSimplifier.build_constraint_set(left_conditions or [])
    right_set = ConditionSimplifier.build_constraint_set(right_conditions or [])
    left_implies_right = left_set.implies_all(right_conditions or [])
    right_implies_left = right_set.implies_all(left_conditions or [])
    left_priority = _readonly_ref_priority_key(left_ref, return_size=return_size)
    right_priority = _readonly_ref_priority_key(right_ref, return_size=return_size)
    if left_priority == right_priority:
        return 0
    if left_priority > right_priority:
        return -1 if left_implies_right else 0
    return 1 if right_implies_left else 0


def _order_return_defs_by_specificity(
    return_defs: List[Dict[str, object]],
    *,
    return_size: int,
) -> List[Dict[str, object]]:
    def _compare(left: Dict[str, object], right: Dict[str, object]) -> int:
        readonly_priority = _compare_readonly_summary_priority(
            left,
            right,
            return_size=return_size,
        )
        if readonly_priority != 0:
            return readonly_priority

        left_implies_right = left["condition_set"].implies_all(right["raw_conditions"])
        right_implies_left = right["condition_set"].implies_all(left["raw_conditions"])
        if left_implies_right and not right_implies_left:
            return -1
        if right_implies_left and not left_implies_right:
            return 1
        left_len = len(left["raw_conditions"])
        right_len = len(right["raw_conditions"])
        if left_len != right_len:
            return -1 if left_len > right_len else 1
        return -1 if int(left["index"]) < int(right["index"]) else (1 if int(left["index"]) > int(right["index"]) else 0)

    return sorted(return_defs, key=cmp_to_key(_compare))


def build_return_definition(
    analysis: FunctionReturnAnalysis,
    return_var_name: str,
    param_infos: List[ParameterInfo],
    *,
    side: Optional[int] = None,
) -> List[str]:
    """return 値の定義式を構築する。"""
    lines: List[str] = []
    return_size = get_return_size(analysis)
    comparison_surface_getter = getattr(analysis, "get_comparison_surface", None)
    comparison_surface = comparison_surface_getter() if callable(comparison_surface_getter) else None
    comparison_type_name_getter = getattr(analysis, "get_comparison_type_name", None)
    comparison_type_obj_getter = getattr(analysis, "get_comparison_type_obj", None)
    comparison_type_name = (
        comparison_type_name_getter()
        if callable(comparison_type_name_getter)
        else analysis.return_type
    )
    comparison_type_obj = (
        comparison_type_obj_getter()
        if callable(comparison_type_obj_getter)
        else getattr(analysis, "return_type_obj", None)
    )
    symbol_name_mapping = build_symbol_name_mapping(param_infos, side=side)

    return_defs: List[Dict[str, object]] = []
    seen_defs = set()
    for ret in analysis.returns:
        raw_conditions = ConditionSimplifier.simplify_conditions_object_centric(ret.conditions)
        if ConditionSimplifier.object_centric_is_contradiction(raw_conditions):
            continue

        if raw_conditions:
            cond_parts = []
            for condition in raw_conditions:
                cond_smt = condition.to_smt(
                    symbol_name_mapping=symbol_name_mapping,
                    float_mode="fp",
                )
                cond_parts.append(cond_smt)
            cond_str = cond_parts[0] if len(cond_parts) == 1 else f"(and {' '.join(cond_parts)})"
        else:
            cond_str = "true"

        rendered_value = ret.value
        effect_summary = getattr(analysis, "effect_summary", None)
        if (
            effect_summary is not None
            and getattr(effect_summary, "effects", None)
        ):
            lowered_value = lower_post_state_expression_for_smt_if_needed(
                ret.value,
                raw_conditions,
                effect_summary.effects,
                analysis.parameters,
            )
            if lowered_value is not None:
                rendered_value = lowered_value

        value_smt = rendered_value.to_smt(
            symbol_name_mapping=symbol_name_mapping,
            float_mode="fp",
        )
        surface_override = getattr(comparison_surface, "use_sign_extension", None)
        if surface_override is not None:
            use_sign_extension = bool(surface_override)
        else:
            use_sign_extension = should_sign_extend_value(
                comparison_type_name,
                rendered_value,
                raw_conditions,
                return_type_obj=comparison_type_obj,
            )
        value_smt = coerce_value_to_bitvec_width(
            rendered_value,
            value_smt,
            return_size,
            use_sign_extension=use_sign_extension,
        )
        value_key = ConditionNormalizer.expression_signature(rendered_value)
        condition_set = ConditionSimplifier.build_constraint_set(raw_conditions)
        dedup_key = (
            ConditionSimplifier.object_centric_conditions_signature(raw_conditions),
            value_key,
        )
        if dedup_key in seen_defs:
            continue
        seen_defs.add(dedup_key)
        return_defs.append(
            {
                "index": len(return_defs),
                "condition": cond_str,
                "value": value_smt,
                "raw_value": rendered_value,
                "raw_conditions": raw_conditions,
                "condition_set": condition_set,
                "value_key": value_key,
            }
        )

    ordered_return_defs = _order_return_defs_by_specificity(return_defs, return_size=return_size)
    if _return_defs_require_relation(ordered_return_defs):
        return _build_relation_return_definition(
            ordered_return_defs,
            return_var_name,
            return_size,
        )

    unified_return = build_ite_expression(
        [{"condition": str(ret_def["condition"]), "value": str(ret_def["value"])} for ret_def in ordered_return_defs],
        return_size,
    )
    lines.append(f"(define-fun {return_var_name} () (_ BitVec {return_size})")
    lines.append(f"  {unified_return})")
    return lines
