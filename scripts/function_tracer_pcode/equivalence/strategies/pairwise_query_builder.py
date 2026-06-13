# -*- coding: utf-8 -*-
"""SMT query builders for PairwiseStrategy."""

import os
from functools import cmp_to_key
from typing import Any, Dict, List, Optional, Tuple

from ...model import Condition, Expression, ExpressionType, FunctionReturnAnalysis, StorageInfo
from ...model.render_smt import expression_smt_bit_width
from ...analysis.condition.simplifier import ConditionSimplifier
from ...analysis.condition.smt_oracle import ConditionSMTOracle
from ..param_semantics import hint_objects_by_identity
from ..semantic_width import SemanticWidthNormalizer
from ..normalize import normalize_expression, NormalizationContext, NormalizationSettings
from ..formula.returns import (
    compare_readonly_summary_values_by_priority,
    coerce_value_to_bitvec_width,
    get_return_size,
    require_equal_return_bit_widths,
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
    condition_rewriter = _build_condition_rewriter(analysis)

    for index, ret_info in enumerate(analysis.returns):
        raw_conditions = [
            _rewrite_guard_condition(condition, condition_rewriter)
            for condition in list(ret_info.conditions or [])
        ]
        query_conditions = _build_object_centric_condition_basis(
            raw_conditions
            + _runtime_summary_guard_conditions(ret_info.value, condition_rewriter)
        )
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
            program_is_big_endian=getattr(analysis, "program_is_big_endian", None),
        )
        key = _build_return_case_key(case)
        existing = merged_cases.get(key)
        if existing is not None:
            existing.source_indices.append(index)
            continue

        merged_cases[key] = case
        cases.append(case)

    return _build_effective_return_case_partition(
        cases,
        return_size=get_return_size(analysis),
    )


def _build_condition_rewriter(analysis: FunctionReturnAnalysis):
    parameter_rewriter = _ParameterMetadataRewriter(getattr(analysis, "parameters", []) or [])
    semantic_rewriter = SemanticWidthNormalizer(hint_objects_by_identity(analysis)).rewrite_expression

    def rewrite(expr: Expression | None) -> Expression | None:
        if expr is None:
            return None
        metadata_normalized = parameter_rewriter.rewrite(expr)
        return semantic_rewriter(metadata_normalized)

    return rewrite


class _ParameterMetadataRewriter:
    """Align parameter Expression objects with the active analysis descriptors."""

    def __init__(self, parameters):
        self._params_by_index: Dict[int, Dict[str, Any]] = {}
        self._params_by_storage: Dict[Tuple[object, ...], Dict[str, Any]] = {}
        params_by_storage: Dict[Tuple[object, ...], List[Dict[str, Any]]] = {}
        for parameter in parameters or []:
            descriptor = dict(parameter or {})
            index = descriptor.get("index")
            if isinstance(index, int) and index >= 0:
                self._params_by_index[index] = descriptor
            storage_key = _storage_identity_key(descriptor.get("storage_info", descriptor.get("storage")))
            if storage_key is not None:
                params_by_storage.setdefault(storage_key, []).append(descriptor)
        self._params_by_storage = {
            storage_key: descriptors[0]
            for storage_key, descriptors in params_by_storage.items()
            if len(descriptors) == 1
        }

    def rewrite(self, expr: Expression | None) -> Expression | None:
        if expr is None:
            return None
        if expr.expr_type == ExpressionType.PARAMETER:
            return self._rewrite_parameter(expr)
        if expr.expr_type == ExpressionType.PHI and expr.value:
            return self._rewrite_phi(expr)

        operands = getattr(expr, "operands", None) or []
        if not operands:
            return expr
        rewritten_operands = [self.rewrite(operand) for operand in operands]
        if all(new is old for new, old in zip(rewritten_operands, operands)):
            return expr
        return _clone_expression_with(expr, operands=rewritten_operands)

    def _rewrite_parameter(self, expr: Expression) -> Expression:
        descriptor = None
        has_index = isinstance(expr.value, int) and expr.value >= 0
        if has_index:
            descriptor = self._params_by_index.get(expr.value)
        else:
            storage_key = _storage_identity_key(getattr(expr, "storage_info", None))
            if storage_key is not None:
                descriptor = self._params_by_storage.get(storage_key)
        if descriptor is None:
            return expr

        desired_size = int(descriptor.get("size", 0) or 0)
        desired_type = descriptor.get("data_type") or expr.data_type
        desired_index = descriptor.get("index", expr.value)
        if (
            desired_size <= 0
            or (
                desired_size == expr.size
                and desired_type == expr.data_type
                and desired_index == expr.value
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
            data_type_obj=getattr(expr, "data_type_obj", None),
            storage_info=expr.storage_info,
            read_order_key=expr.read_order_key,
            runtime_ref=getattr(expr, "runtime_ref", None),
            opcode=getattr(expr, "opcode", None),
        )

    def _rewrite_phi(self, expr: Expression) -> Expression:
        changed = False
        branches = []
        for condition, value in expr.value:
            rewritten_condition = None
            if condition is not None:
                rewritten_condition_expr = self.rewrite(condition.expression)
                rewritten_condition = Condition(rewritten_condition_expr, condition.negated)
                changed = changed or (rewritten_condition_expr is not condition.expression)
            rewritten_value = self.rewrite(value)
            changed = changed or (rewritten_value is not value)
            branches.append((rewritten_condition, rewritten_value))

        if not changed:
            return expr
        rebuilt = Expression.phi(branches)
        rebuilt.size = expr.size
        rebuilt.data_type = expr.data_type
        rebuilt.data_type_obj = getattr(expr, "data_type_obj", None)
        rebuilt.storage_info = expr.storage_info
        rebuilt.read_order_key = expr.read_order_key
        rebuilt.runtime_ref = getattr(expr, "runtime_ref", None)
        return rebuilt


def _clone_expression_with(expr: Expression, *, operands) -> Expression:
    return Expression(
        expr_type=expr.expr_type,
        value=expr.value,
        operator=expr.operator,
        operands=list(operands or []),
        size=expr.size,
        name=expr.name,
        data_type=expr.data_type,
        data_type_obj=getattr(expr, "data_type_obj", None),
        storage_info=expr.storage_info,
        read_order_key=expr.read_order_key,
        runtime_ref=getattr(expr, "runtime_ref", None),
        opcode=getattr(expr, "opcode", None),
    )


def _storage_identity_key(storage_info) -> Tuple[object, ...] | None:
    storage_info = _coerce_storage_info(storage_info)
    if storage_info is None:
        return None
    storage_key_fn = getattr(storage_info, "storage_identity_key", None)
    if not callable(storage_key_fn):
        return None
    try:
        return storage_key_fn()
    except (TypeError, ValueError):
        return None


def _coerce_storage_info(storage_info) -> StorageInfo | None:
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


def _runtime_summary_guard_conditions(
    value_expr: Expression | None,
    guard_rewriter=None,
) -> List[Condition]:
    guards: List[Condition] = []
    seen: set[tuple] = set()
    for node in _iter_expression_nodes(value_expr):
        runtime_ref = getattr(node, "runtime_ref", None)
        for owner in (
            runtime_ref,
            getattr(runtime_ref, "accumulator_proof", None),
            getattr(runtime_ref, "loop_summary", None),
        ):
            for guard in tuple(getattr(owner, "guard_constraints", ()) or ()):
                if not isinstance(guard, Condition):
                    continue
                key = guard.structural_key(budget=256)
                if key in seen:
                    continue
                seen.add(key)
                guards.append(_rewrite_guard_condition(guard, guard_rewriter))
    return guards


def _rewrite_guard_condition(condition: Condition, guard_rewriter=None) -> Condition:
    if guard_rewriter is None:
        return condition
    rewritten_expr = guard_rewriter(condition.expression)
    if rewritten_expr is condition.expression:
        return condition
    return Condition(rewritten_expr, condition.negated)


def _iter_expression_nodes(expr: Expression | None):
    if expr is None:
        return
    yield expr
    if getattr(expr, "expr_type", None) == ExpressionType.PHI:
        return
    for operand in getattr(expr, "operands", None) or ():
        yield from _iter_expression_nodes(operand)


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


def _build_effective_return_case_partition(
    cases: List[ReturnCase],
    *,
    return_size: int,
) -> List[ReturnCase]:
    """Make pairwise cases match the ordered SMT return partition.

    Pairwise checks each return case independently, so overlapping cases must
    carry the same shadowing semantics as the full ``ite`` return definition:
    a later case is active only outside all earlier, higher-priority cases.
    Conditions stay as ``Condition``/``Expression`` objects and are lowered to
    SMT later by the normal renderer.
    """

    if len(cases) <= 1:
        return cases
    ordered = _order_return_cases_for_effective_partition(
        cases,
        return_size=return_size,
    )
    effective_cases: List[ReturnCase] = []
    prior_cases: List[ReturnCase] = []
    for case in ordered:
        effective_conditions = list(case.conditions or [])
        for prior in prior_cases:
            if _condition_region_is_unsat(effective_conditions + list(prior.conditions or [])):
                continue
            prior_condition = Condition.combine_and(list(prior.conditions or []))
            if prior_condition is not None:
                effective_conditions.append(prior_condition.negate())
        effective_conditions = _build_object_centric_condition_basis(effective_conditions)
        if _condition_region_is_unsat(effective_conditions):
            prior_cases.append(case)
            continue
        case.update_conditions(effective_conditions, summary_conditions=effective_conditions)
        effective_cases.append(case)
        prior_cases.append(case)
    return effective_cases


def _order_return_cases_for_effective_partition(
    cases: List[ReturnCase],
    *,
    return_size: int,
) -> List[ReturnCase]:
    def _compare(left: ReturnCase, right: ReturnCase) -> int:
        readonly_priority = compare_readonly_summary_values_by_priority(
            left.value_expr,
            left.conditions,
            right.value_expr,
            right.conditions,
            return_size=return_size,
        )
        if readonly_priority != 0:
            return readonly_priority

        left_set = ConditionSimplifier.build_constraint_set(left.conditions or [])
        right_set = ConditionSimplifier.build_constraint_set(right.conditions or [])
        left_implies_right = left_set.implies_all(right.conditions or [])
        right_implies_left = right_set.implies_all(left.conditions or [])
        if left_implies_right and not right_implies_left:
            return -1
        if right_implies_left and not left_implies_right:
            return 1
        left_len = len(left.conditions or [])
        right_len = len(right.conditions or [])
        if left_len != right_len:
            return -1 if left_len > right_len else 1
        return -1 if int(left.index) < int(right.index) else (1 if int(left.index) > int(right.index) else 0)

    return sorted(cases, key=cmp_to_key(_compare))


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
    lines.extend(_build_loop_summary_case_comments(case1.value_expr, "Case1"))
    lines.extend(_build_loop_summary_case_comments(case2.value_expr, "Case2"))
    lines.extend(_build_pairwise_extra_assertions(base_ctx, pair_id))
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


def _build_pairwise_extra_assertions(
    base_ctx: Dict[str, Any],
    pair_id: str,
) -> List[str]:
    assertions_by_pair = base_ctx.get("pairwise_extra_assertions_by_pair") or {}
    raw_assertions = assertions_by_pair.get(pair_id) or ()
    assertions = [str(item) for item in raw_assertions if str(item).strip()]
    if not assertions:
        return []
    return [
        "",
        "; " + "-" * 40,
        "; Pair-local object-derived assumptions",
        "; " + "-" * 40,
        *assertions,
    ]


def build_return_width_bridge_narrow_query(
    base_ctx: Dict[str, Any],
    case1: ReturnCase,
    case2: ReturnCase,
    param_replace_fn1,
    param_replace_fn2,
    pair_id: str,
    *,
    target_bits: int,
) -> str:
    """Build a value-inequality query at the proven narrow return width."""

    target_bits = max(1, int(target_bits))
    lines = _build_query_header(
        f"; Return Width Bridge Narrow Query: Pair {pair_id}",
        f"; Case1[{case1.index}]: {case1.get_condition_summary()}",
        f"; Case2[{case2.index}]: {case2.get_condition_summary()}",
    )
    lines.extend(base_ctx["header_lines"])
    lines.extend(_build_case_conditions(case1, param_replace_fn1, "Case1"))
    lines.extend(_build_case_conditions(case2, param_replace_fn2, "Case2"))
    lines.extend(_build_loop_summary_case_comments(case1.value_expr, "Case1"))
    lines.extend(_build_loop_summary_case_comments(case2.value_expr, "Case2"))
    lines.extend(
        _build_value_inequality_section(
            case1.get_value_smt(
                param_replace_fn1,
                target_bits=target_bits,
                use_sign_extension=case1.should_sign_extend_value(),
            ),
            case2.get_value_smt(
                param_replace_fn2,
                target_bits=target_bits,
                use_sign_extension=case2.should_sign_extend_value(),
            ),
            target_bits,
            target_bits,
            title="; Return width bridge narrow value inequality",
            note_lines=[
                "; Completed ABI/high-bit proof is required before this query can discharge a width mismatch",
                f"; Narrow comparison width: {target_bits}",
            ],
        )
    )
    lines.append("")
    lines.append("(check-sat)")
    lines.append("(get-model)")
    return "\n".join(lines)


def build_return_width_bridge_high_bit_query(
    base_ctx: Dict[str, Any],
    case1: ReturnCase,
    case2: ReturnCase,
    param_replace_fn1,
    param_replace_fn2,
    pair_id: str,
    *,
    narrow_bits: int,
    return_size1: int,
    return_size2: int,
) -> Optional[str]:
    """Build a query proving the wide return is the expected extension of its low bits."""

    narrow_bits = int(narrow_bits)
    return_size1 = int(return_size1)
    return_size2 = int(return_size2)
    if narrow_bits <= 0 or return_size1 <= 0 or return_size2 <= 0:
        return None
    if return_size1 == return_size2:
        return None
    if return_size1 > return_size2:
        wide_case = case1
        wide_replace_fn = param_replace_fn1
        wide_label = "Case1"
        wide_bits = return_size1
        narrow_case = case2
    else:
        wide_case = case2
        wide_replace_fn = param_replace_fn2
        wide_label = "Case2"
        wide_bits = return_size2
        narrow_case = case1
    if wide_bits <= narrow_bits:
        return None

    extension_op = "sign_extend" if narrow_case.should_sign_extend_value() else "zero_extend"
    wide_expr_bits = int(expression_smt_bit_width(wide_case.value_expr) or 0)
    if wide_expr_bits < wide_bits:
        has_object_extension = _return_case_has_object_extension_to_width(
            wide_case,
            input_bits=wide_expr_bits,
            output_bits=wide_bits,
            extension_op=extension_op,
        )
        has_constant_extension = _return_case_has_constant_literal_extension_to_width(
            wide_case,
            input_bits=wide_expr_bits,
            output_bits=wide_bits,
            extension_op=extension_op,
        )
        if not (has_object_extension or has_constant_extension):
            return None

    wide_value_smt = wide_case.get_value_smt(
        wide_replace_fn,
        target_bits=wide_bits,
        use_sign_extension=wide_case.should_sign_extend_value(),
    )
    low_bits = f"((_ extract {narrow_bits - 1} 0) {wide_value_smt})"
    extend_bits = wide_bits - narrow_bits
    expected_wide_smt = f"((_ {extension_op} {extend_bits}) {low_bits})"

    lines = _build_query_header(
        f"; Return Width Bridge High-Bit Query: Pair {pair_id}",
        f"; Case1[{case1.index}]: {case1.get_condition_summary()}",
        f"; Case2[{case2.index}]: {case2.get_condition_summary()}",
    )
    lines.extend(base_ctx["header_lines"])
    lines.extend(_build_case_conditions(case1, param_replace_fn1, "Case1"))
    lines.extend(_build_case_conditions(case2, param_replace_fn2, "Case2"))
    lines.extend(_build_loop_summary_case_comments(case1.value_expr, "Case1"))
    lines.extend(_build_loop_summary_case_comments(case2.value_expr, "Case2"))
    lines.extend(
        [
            "; " + "-" * 40,
            "; Return width bridge high-bit extension proof",
            "; Completed high-bit proof requires this query to be UNSAT",
            f"; Wide side: {wide_label}, wide width: {wide_bits}, narrow width: {narrow_bits}",
            f"; Expected extension: {extension_op}",
            "; " + "-" * 40,
            f"(assert (not (= {wide_value_smt} {expected_wide_smt})))",
            "",
            "(check-sat)",
            "(get-model)",
        ]
    )
    return "\n".join(lines)


def _return_case_has_object_extension_to_width(
    return_case: ReturnCase,
    *,
    input_bits: int,
    output_bits: int,
    extension_op: str,
) -> bool:
    if input_bits <= 0 or output_bits <= 0 or input_bits >= output_bits:
        return False
    expected_mnemonic = {
        "sign_extend": "INT_SEXT",
        "zero_extend": "INT_ZEXT",
    }.get(extension_op)
    if expected_mnemonic is None:
        return False
    return_info = getattr(return_case, "return_info", None)
    for ref in getattr(return_info, "return_value_pcode_op_refs", ()) or ():
        if getattr(ref, "mnemonic", None) != expected_mnemonic:
            continue
        input_size = None
        try:
            input_size = ref.input_size(0)
        except Exception:
            input_size = None
        output_size = getattr(ref, "output_size", None)
        try:
            ref_input_bits = int(input_size) * 8 if input_size else None
            ref_output_bits = int(output_size) * 8 if output_size else None
        except (TypeError, ValueError):
            continue
        if ref_input_bits == int(input_bits) and ref_output_bits == int(output_bits):
            return True
    return False


def _return_case_has_constant_literal_extension_to_width(
    return_case: ReturnCase,
    *,
    input_bits: int,
    output_bits: int,
    extension_op: str,
) -> bool:
    if input_bits <= 0 or output_bits <= 0 or input_bits >= output_bits:
        return False
    if extension_op not in {"sign_extend", "zero_extend"}:
        return False
    expr = getattr(return_case, "value_expr", None)
    expr_type = getattr(expr, "expr_type", None)
    expr_kind = getattr(expr_type, "__class__", None)
    if expr_type is None or expr_kind is None or expr_type != expr_kind.CONSTANT:
        return False
    try:
        value = int(getattr(expr, "value"))
    except (TypeError, ValueError):
        return False
    source_mask = (1 << int(input_bits)) - 1
    low_value = value & source_mask
    has_material_high_bits = (value >> int(input_bits)) != 0
    has_signed_negative_low_bits = (
        extension_op == "sign_extend"
        and bool(low_value & (1 << (int(input_bits) - 1)))
    )
    if not (has_material_high_bits or has_signed_negative_low_bits):
        return False
    if extension_op == "zero_extend":
        extended = low_value
    else:
        sign_bit = 1 << (int(input_bits) - 1)
        if low_value & sign_bit:
            extended = low_value | (((1 << (int(output_bits) - int(input_bits))) - 1) << int(input_bits))
        else:
            extended = low_value
    return (value & ((1 << int(output_bits)) - 1)) == extended


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
    lines.extend(_build_loop_summary_case_comments(case1.value_expr, "Case1"))
    lines.extend(_build_loop_summary_case_comments(case2.value_expr, "Case2"))
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


def _build_loop_summary_case_comments(expr, label: str) -> List[str]:
    runtime_ref = getattr(expr, "runtime_ref", None)
    loop_summary = getattr(runtime_ref, "loop_summary", None)
    cases = tuple(getattr(loop_summary, "cases", ()) or ())
    if not cases:
        return []
    lines = [f"; {label} loop summary cases: {len(cases)}"]
    for index, loop_case in enumerate(cases):
        path_conditions = ", ".join(
            _safe_loop_case_text(condition)
            for condition in getattr(loop_case, "path_conditions", ()) or ()
        ) or "<unconditional>"
        term_expr = _safe_loop_case_text(getattr(loop_case, "term_expr", None))
        lines.append(
            f"; {label} loop_case[{index}] "
            f"kind={getattr(loop_case, 'case_kind', 'unknown')} "
            f"path=[{path_conditions}] term={term_expr}"
        )
    return lines


def _safe_loop_case_text(value) -> str:
    if value is None:
        return "None"
    to_string = getattr(value, "to_string", None)
    if callable(to_string):
        try:
            return str(to_string())
        except (AttributeError, TypeError, ValueError, RecursionError):
            pass
    return str(value)


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

    require_equal_return_bit_widths(
        return_size1,
        return_size2,
        context=title.strip("; ").lower() or "pairwise return value comparison",
    )
    lines.append(f"(assert (not (= {value1_smt} {value2_smt})))")
    return lines
