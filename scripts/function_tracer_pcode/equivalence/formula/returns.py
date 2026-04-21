# -*- coding: utf-8 -*-
"""FormulaBuilder の return 定義関連ヘルパー。"""

from __future__ import annotations

from functools import cmp_to_key
from typing import Dict, List, Optional

from ...analysis.effect_summary import (
    lower_post_state_expression_for_smt_if_needed,
)
from ...analysis.condition.simplifier import ConditionSimplifier
from ...model import Expression, FunctionReturnAnalysis
from ...model.signature import (
    get_declared_type_size_bits,
    get_declared_type_signedness,
    is_undefined_data_type,
    is_unsigned_data_type,
)
from ...model.render_smt import (
    expression_contains_unsupported_smt_ops,
    expression_contains_signed_comparison,
    expression_returns_bool,
    expression_smt_bit_width,
)
from ...analysis.condition.normalizer import ConditionNormalizer
from .params import build_symbol_name_mapping
from .types import ParameterInfo


def get_return_size(analysis: FunctionReturnAnalysis) -> int:
    """return値のビット幅を取得する。"""
    get_comparison_bit_width = getattr(analysis, "get_comparison_bit_width", None)
    if callable(get_comparison_bit_width):
        bits = int(get_comparison_bit_width() or 0)
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
    if not is_boolean_return_expr(expr):
        return value_smt
    return f"(ite {value_smt} (_ bv1 {return_size}) (_ bv0 {return_size}))"


def should_sign_extend_to_return_size(analysis: FunctionReturnAnalysis) -> bool:
    """return値の幅補正で sign extension を使うべきか判定する。"""
    surface_getter = getattr(analysis, "get_comparison_surface", None)
    if callable(surface_getter):
        surface = surface_getter()
        override = getattr(surface, "use_sign_extension", None)
        if override is not None:
            return bool(override)

        type_name_getter = getattr(analysis, "get_comparison_type_name", None)
        type_obj_getter = getattr(analysis, "get_comparison_type_obj", None)
        if callable(type_name_getter) or callable(type_obj_getter):
            return should_sign_extend_return_type(
                type_name_getter() if callable(type_name_getter) else analysis.return_type,
                return_type_obj=(
                    type_obj_getter()
                    if callable(type_obj_getter)
                    else getattr(analysis, "return_type_obj", None)
                ),
            )
    return should_sign_extend_return_type(
        analysis.return_type,
        return_type_obj=getattr(analysis, "return_type_obj", None),
    )


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


def _order_return_defs_by_specificity(
    return_defs: List[Dict[str, object]],
) -> List[Dict[str, object]]:
    def _compare(left: Dict[str, object], right: Dict[str, object]) -> int:
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
    symbol_name_mapping = build_symbol_name_mapping(param_infos)

    return_defs: List[Dict[str, object]] = []
    seen_defs = set()
    for ret in analysis.returns:
        raw_conditions = ConditionSimplifier.simplify_conditions_object_centric(ret.conditions)
        if ConditionSimplifier.object_centric_is_contradiction(raw_conditions):
            continue

        if raw_conditions:
            cond_parts = []
            for condition in raw_conditions:
                cond_smt = condition.to_smt(symbol_name_mapping=symbol_name_mapping)
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

        value_smt = rendered_value.to_smt(symbol_name_mapping=symbol_name_mapping)
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
                "raw_conditions": raw_conditions,
                "condition_set": condition_set,
                "value_key": value_key,
            }
        )

    ordered_return_defs = _order_return_defs_by_specificity(return_defs)
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
