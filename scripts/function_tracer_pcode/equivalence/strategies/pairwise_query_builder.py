# -*- coding: utf-8 -*-
"""SMT query builders for PairwiseStrategy."""

import os
from typing import Any, Dict, List, Tuple

from ...model import FunctionReturnAnalysis
from ...analysis.condition.simplifier import ConditionSimplifier
from ...analysis.condition.smt_oracle import ConditionSMTOracle
from ..normalize import normalize_expression, NormalizationContext, NormalizationSettings
from ..formula.returns import (
    coerce_value_to_bitvec_width,
)
from .pairwise_models import ReturnCase


def extract_return_cases(
    analysis: FunctionReturnAnalysis,
    normalization_settings: NormalizationSettings | None = None,
) -> List[ReturnCase]:
    """FunctionReturnAnalysis から ReturnCase を抽出"""
    cases = []
    merged_cases: Dict[Tuple[tuple, tuple], ReturnCase] = {}
    settings = normalization_settings or NormalizationSettings.safe()

    for index, ret_info in enumerate(analysis.returns):
        query_conditions = _build_object_centric_condition_basis(ret_info.conditions)
        if _condition_region_is_unsat(query_conditions):
            continue
        normalized_value = normalize_expression(
            ret_info.value,
            NormalizationContext(settings=settings),
        )

        case = ReturnCase(
            index=index,
            conditions=query_conditions,
            value_expr=ret_info.value,
            normalized_value_expr=normalized_value,
            return_info=ret_info,
            return_type=analysis.get_comparison_type_name(),
            return_type_obj=analysis.get_comparison_type_obj(),
            parameters=list(analysis.parameters or []),
            effect_summary=getattr(analysis, "effect_summary", None),
            comparison_surface=analysis.get_comparison_surface(),
            summary_conditions=query_conditions,
        )
        key = _build_return_case_key(case)
        existing = merged_cases.get(key)
        if existing is not None:
            existing.source_indices.append(index)
            continue

        merged_cases[key] = case
        cases.append(case)

    return cases


def _build_return_case_key(case: ReturnCase) -> Tuple[tuple, tuple]:
    """分岐ケースの統合キーを生成する"""
    cond_key = _build_object_centric_condition_signature(case.conditions)
    key_expr = getattr(case, "normalized_value_expr", None) or case.value_expr
    value_key = key_expr.structural_key(
        budget=256,
        normalize_commutative=True,
        include_memory_read_order=True,
        include_semantic_runtime_refs=True,
    )
    return cond_key, value_key


def _build_object_centric_condition_basis(conditions) -> List[Any]:
    unique = []
    for condition in list(conditions or []):
        if condition is None:
            continue
        truth_value = ConditionSimplifier.evaluate_condition_truth(condition)
        if truth_value is True:
            continue
        if any(condition.equals(existing) for existing in unique):
            continue
        unique.append(condition)
    return unique


def _condition_region_is_unsat(conditions) -> bool:
    condition_list = list(conditions or [])
    if not condition_list:
        return False

    solver_unsat = ConditionSMTOracle.conjunction_is_unsat(condition_list)
    if solver_unsat is not None:
        return solver_unsat

    return ConditionSimplifier.object_centric_is_contradiction(condition_list)


def _build_object_centric_condition_signature(conditions) -> Tuple[tuple, ...]:
    signature = []
    for condition in list(conditions or []):
        if condition is None:
            continue
        signature.append(condition.structural_key(budget=256))
    signature.sort()
    return tuple(signature)


def build_condition_only_query(
    base_ctx: Dict[str, Any],
    case1: ReturnCase,
    case2: ReturnCase,
    param_replace_fn1,
    param_replace_fn2,
    pair_id: str
) -> str:
    """条件のみの SMT クエリを構築する"""
    lines = _build_query_header(
        f"; Pairwise Query (Conditions Only): Pair {pair_id}",
        f"; Case1[{case1.index}]: {case1.get_condition_summary()}",
        f"; Case2[{case2.index}]: {case2.get_condition_summary()}",
    )
    lines.extend(base_ctx["header_lines"])
    lines.extend(_build_case_conditions(case1, param_replace_fn1, "Case1"))
    lines.extend(_build_case_conditions(case2, param_replace_fn2, "Case2"))
    lines.append("(check-sat)")
    return "\n".join(lines)


def build_single_case_condition_query(
    base_ctx: Dict[str, Any],
    case: ReturnCase,
    param_replace_fn,
    label: str,
) -> str:
    """単一ケースの到達可能性チェック用 SMT クエリを構築する。"""
    lines = _build_query_header(
        f"; Single Case Reachability: {label}[{case.index}]",
        f"; {label}[{case.index}]: {case.get_condition_summary()}",
    )
    lines.extend(base_ctx["header_lines"])
    lines.extend(_build_case_conditions(case, param_replace_fn, label))
    lines.append("(check-sat)")
    return "\n".join(lines)


def build_pair_query(
    base_ctx: Dict[str, Any],
    case1: ReturnCase,
    case2: ReturnCase,
    param_replace_fn1,
    param_replace_fn2,
    pair_id: str
) -> str:
    """値不等式つきの pair query を構築する"""
    lines = _build_query_header(
        f"; Pairwise Query: Pair {pair_id}",
        f"; Case1[{case1.index}]: {case1.get_condition_summary()}",
        f"; Case2[{case2.index}]: {case2.get_condition_summary()}",
    )
    lines.extend(base_ctx["header_lines"])
    lines.extend(_build_case_conditions(case1, param_replace_fn1, "Case1"))
    lines.extend(_build_case_conditions(case2, param_replace_fn2, "Case2"))
    lines.extend(
        _build_value_inequality_section(
            case1.get_value_smt(
                param_replace_fn1,
                target_bits=base_ctx.get("return_size1", 32),
                use_sign_extension=case1.should_sign_extend_value(),
            ),
            case2.get_value_smt(
                param_replace_fn2,
                target_bits=base_ctx.get("return_size2", 32),
                use_sign_extension=case2.should_sign_extend_value(),
            ),
            base_ctx.get("return_size1", 32),
            base_ctx.get("return_size2", 32),
            title="; Value inequality",
            note_lines=[],
        )
    )
    lines.append("")
    lines.append("(check-sat)")
    lines.append("(get-model)")
    return "\n".join(lines)


def build_normalized_inequality_query(
    base_ctx: Dict[str, Any],
    case1: ReturnCase,
    case2: ReturnCase,
    param_replace_fn1,
    param_replace_fn2,
    value1_norm_expr,
    value2_norm_expr,
    value1_smt_norm: str,
    value2_smt_norm: str,
    pair_id: str
) -> str:
    """正規化後の値不等式クエリを構築する"""
    lines = _build_query_header(
        f"; Normalized Inequality Query: Pair {pair_id}",
        "; Check if normalized values are equivalent under base constraints",
    )
    lines.extend(base_ctx["header_lines"])
    lines.extend(_build_case_conditions(case1, param_replace_fn1, "Case1"))
    lines.extend(_build_case_conditions(case2, param_replace_fn2, "Case2"))
    return_size1 = base_ctx.get("return_size1", 32)
    return_size2 = base_ctx.get("return_size2", 32)
    value1_smt_norm = coerce_value_to_bitvec_width(
        value1_norm_expr,
        value1_smt_norm,
        return_size1,
        use_sign_extension=case1.should_sign_extend_value(),
    )
    value2_smt_norm = coerce_value_to_bitvec_width(
        value2_norm_expr,
        value2_smt_norm,
        return_size2,
        use_sign_extension=case2.should_sign_extend_value(),
    )
    lines.extend(
        _build_value_inequality_section(
            value1_smt_norm,
            value2_smt_norm,
            return_size1,
            return_size2,
            title="; Normalized value inequality",
            note_lines=["; (param_*_1 and param_*_2 are constrained to be equal by base_ctx)"],
        )
    )
    lines.append("")
    lines.append("(check-sat)")
    lines.append("(get-model)")
    return "\n".join(lines)


def save_unknown_query(debug_print, query: str, pair_id: str, stage: str, output_dir: str) -> None:
    """UNKNOWN クエリを保存する"""
    filename = f"unknown_query_{pair_id.replace(',', '_').replace('(', '').replace(')', '')}_{stage}.smt2"
    filepath = os.path.join(output_dir, filename)
    try:
        with open(filepath, "w") as handle:
            handle.write(query)
        debug_print(f"  Saved unknown query to: {filepath}")
    except Exception as exc:
        debug_print(f"  Failed to save unknown query: {exc}")


def _build_query_header(*comment_lines: str) -> List[str]:
    lines = []
    lines.append("; " + "=" * 60)
    lines.extend(comment_lines)
    lines.append("; " + "=" * 60)
    lines.append("")
    lines.append("(set-logic QF_BV)")
    lines.append("")
    return lines


def _build_case_conditions(case: ReturnCase, param_replace_fn, label: str) -> List[str]:
    lines = []
    conds_smt = case.get_conditions_smt(param_replace_fn)
    if not conds_smt:
        return lines

    lines.append("; " + "-" * 40)
    lines.append(f"; {label}[{case.index}] conditions")
    lines.append("; " + "-" * 40)
    for cond_str in conds_smt:
        lines.append(f"(assert {cond_str})")
    lines.append("")
    return lines


def _build_value_inequality_section(
    value1_smt: str,
    value2_smt: str,
    return_size1: int,
    return_size2: int,
    title: str,
    note_lines: List[str]
) -> List[str]:
    lines = []
    lines.append("; " + "-" * 40)
    lines.append(title)
    for note in note_lines:
        lines.append(note)
    lines.append("; " + "-" * 40)

    if return_size1 == return_size2:
        lines.append(f"(assert (not (= {value1_smt} {value2_smt})))")
        return lines

    overlap = min(return_size1, return_size2)
    if return_size1 < return_size2:
        lines.append(
            f"(assert (not (= {value1_smt} ((_ extract {overlap - 1} 0) {value2_smt}))))"
        )
    else:
        lines.append(
            f"(assert (not (= ((_ extract {overlap - 1} 0) {value1_smt}) {value2_smt})))"
        )
    return lines
