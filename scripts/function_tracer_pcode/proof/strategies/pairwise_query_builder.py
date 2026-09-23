# -*- coding: utf-8 -*-
"""SMT query builders for PairwiseStrategy."""

import hashlib
import os
from functools import cmp_to_key
from typing import Any, Dict, List, Optional, Tuple

from scripts.function_tracer_pcode.core.stage_clock import stage_region
from scripts.function_tracer_pcode.core.storage import storage_identity_key_of as _storage_identity_key
from scripts.function_tracer_pcode.core import (
    Condition,
    Expression,
    ExpressionType,
    FunctionReturnAnalysis,
    ReturnInfo,
)
from scripts.function_tracer_pcode.analysis.condition.simplifier import ConditionSimplifier
from scripts.function_tracer_pcode.analysis.condition.smt_oracle import ConditionSMTOracle
from scripts.function_tracer_pcode.semantics.param_semantics import hint_objects_by_identity
from scripts.function_tracer_pcode.semantics.rewrite_contract import RewriteAuthorization
from scripts.function_tracer_pcode.semantics.semantic_width import SemanticWidthNormalizer
from scripts.function_tracer_pcode.semantics.normalize import (
    normalize_expression,
    NormalizationContext,
    NormalizationSettings,
)
from scripts.function_tracer_pcode.proof.formula.returns import (
    compare_readonly_summary_values_by_priority,
    coerce_value_to_bitvec_width,
    get_return_size,
    require_equal_return_bit_widths,
)
from scripts.function_tracer_pcode.proof.strategies.pairwise_models import ReturnCase
from scripts.function_tracer_pcode.proof.return_width.surface import (
    ConsumerBindingReceipt,
    PairReturnObservationView,
)


def _query_parameter_lowering_key(base_ctx: Dict[str, Any]) -> Tuple[Any, ...]:
    def identity(item: Any) -> Tuple[Any, ...]:
        return (
            "query_parameter",
            int(getattr(item, "index", -1)),
            str(getattr(item, "original_name", "") or ""),
            str(getattr(item, "smt_name", "") or ""),
            int(getattr(item, "bit_width", 0) or 0),
        )
    return (
        "ordered_query_parameter_lowering_v1",
        tuple(identity(item) for item in base_ctx.get("params1", ())),
        tuple(identity(item) for item in base_ctx.get("params2", ())),
    )


def validate_canonical_binding_receipt(
    base_ctx: Dict[str, Any],
    view: PairReturnObservationView,
    receipt: ConsumerBindingReceipt,
) -> None:
    if (
        receipt.observation_target_key != view.contract.target_id.stable_key()
        or receipt.observation_view_digest != view.digest
        or receipt.proof_closure_id != view.proof_bundle.validated_closure_id
        or receipt.query_parameter_lowering_key != _query_parameter_lowering_key(base_ctx)
        or not receipt.proof_bundle_applicability_digest
        or not receipt.lowered_left_term
        or not receipt.lowered_right_term
    ):
        raise ValueError("canonical_return_width_binding_receipt_inapplicable")


def build_canonical_return_observation_query(
    base_ctx: Dict[str, Any],
    case1: ReturnCase,
    case2: ReturnCase,
    param_replace_fn1,
    param_replace_fn2,
    pair_id: str,
    *,
    view: PairReturnObservationView,
    receipt: ConsumerBindingReceipt,
    equality: bool = False,
    model_assertions: Tuple[str, ...] = (),
) -> str:
    """Lower the exact terms captured by the applicable binding receipt."""

    validate_canonical_binding_receipt(base_ctx, view, receipt)
    replay_marker = ""
    if base_ctx.get("require_original_canonical_return_query_bundle"):
        authorization = base_ctx.get("canonical_return_replay_authorization") or {}
        order = tuple(authorization.get("binding_projection_order") or ())
        receipt_order = tuple(authorization.get("ordered_receipt_digests") or ())
        if (
            len(authorization.get("bundle_digest", "")) != 64
            or len(authorization.get("production_query_digest", "")) != 64
            or len(order) != len(receipt_order)
            or str(pair_id) not in order
            or receipt_order[order.index(str(pair_id))] != receipt.binding_digest
        ):
            raise ValueError("canonical_return_replay_authorization_inapplicable")
        model_assertions_digest = hashlib.sha256(
            repr(tuple(model_assertions)).encode("utf-8")
        ).hexdigest()
        authorization_digest = hashlib.sha256(repr((
            "canonical_return_replay_authorization_v1",
            authorization["bundle_digest"],
            authorization["production_query_digest"],
            order,
            receipt_order,
            str(pair_id),
            receipt.binding_digest,
            tuple(model_assertions),
        )).encode("utf-8")).hexdigest()
        replay_marker = (
            f"; canonical_return_replay_authorization {authorization_digest} "
            f"production_query_sha256={authorization['production_query_digest']} "
            f"model_assertions_sha256={model_assertions_digest}"
        )
    target_bits = int(view.canonical_comparison_width)
    title = "Equality Replay" if equality else "Inequality"
    lines = _build_query_header(
        f"; Canonical Return Observation {title}: Pair {pair_id}",
        f"; binding-receipt {receipt.binding_digest}",
        f"; projection-lowering {receipt.projection_lowering_digest}",
        logic=base_ctx.get("smt_logic", "QF_BV"),
    )
    if replay_marker:
        lines.append(replay_marker)
    lines.extend(base_ctx["header_lines"])
    lines.extend(str(item) for item in model_assertions)
    lines.extend(_build_case_conditions(case1, param_replace_fn1, "Case1"))
    lines.extend(_build_case_conditions(case2, param_replace_fn2, "Case2"))
    lines.extend(_build_pairwise_extra_assertions(base_ctx, pair_id))
    relation = "=" if equality else "distinct"
    lines.extend([
        "",
        "; Canonical terms are copied verbatim from the validated binding receipt",
        f"; binding-receipt {receipt.binding_digest}",
        f"; projection-lowering {receipt.projection_lowering_digest}",
        f"(assert ({relation} {receipt.lowered_left_term} {receipt.lowered_right_term}))",
        f"; canonical comparison width: {target_bits}",
        "",
        "(check-sat)",
        "(get-model)",
    ])
    query = "\n".join(lines)
    if (
        f"; binding-receipt {receipt.binding_digest}" not in query
        or f"; projection-lowering {receipt.projection_lowering_digest}" not in query
        or receipt.lowered_left_term not in query
        or receipt.lowered_right_term not in query
        or (replay_marker and replay_marker not in query)
    ):
        raise ValueError("canonical_return_width_query_binding_mismatch")
    return query


def extract_return_cases(
    analysis: FunctionReturnAnalysis,
    normalization_settings: NormalizationSettings | None = None,
    *,
    apply_effective_partition: bool = True,
    authorization: Optional[RewriteAuthorization] = None,
) -> List[ReturnCase]:
    """FunctionReturnAnalysis から ReturnCase を抽出

    ``authorization`` は prepared surface を作ったときと同じ最終
    ``InputCorrespondence`` 由来の値を渡す（二重 normalize も同じ前提で行う）。
    省略時は空で、恒等規則だけが効く。
    """
    cases = []
    merged_cases: Dict[Tuple[tuple, tuple], ReturnCase] = {}
    settings = normalization_settings or NormalizationSettings.safe()
    condition_rewriter = _build_condition_rewriter(analysis, authorization)

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

    if not apply_effective_partition:
        return cases
    return _build_effective_return_case_partition(cases, return_size=get_return_size(analysis))


def return_cases_require_relation(cases: List[ReturnCase]) -> bool:
    """Return whether overlapping values cannot use deterministic ordered ITEs.

    This is the object-level counterpart of the formula renderer's relation
    choice.  The monolithic region planner calls it before any SMT string is
    rendered and falls back to the legacy whole query when the choice is
    ambiguous.
    """

    for index, left in enumerate(cases):
        left_value = _build_return_case_key(left)[1]
        left_set = ConditionSimplifier.build_constraint_set(left.conditions or [])
        for right in cases[index + 1 :]:
            if left_value == _build_return_case_key(right)[1]:
                continue
            combined = list(left.conditions or []) + list(right.conditions or [])
            if ConditionSimplifier.object_centric_is_contradiction(combined):
                continue
            right_set = ConditionSimplifier.build_constraint_set(right.conditions or [])
            left_implies_right = left_set.implies_all(right.conditions or [])
            right_implies_left = right_set.implies_all(left.conditions or [])
            if left_implies_right != right_implies_left:
                continue
            return True
    return False


def append_ordered_ite_default_case(
    analysis: FunctionReturnAnalysis,
    cases: List[ReturnCase],
) -> List[ReturnCase]:
    """Append the renderer's zero-valued default region, when reachable.

    The default guard is built from structured conditions as
    ``not(C0) and ... and not(Cn)``.  It is never recovered by parsing the
    rendered ITE expression.
    """

    default_conditions: List[Condition] = []
    for case in cases:
        combined = Condition.combine_and(list(case.conditions or []))
        if combined is None:
            return list(cases)
        default_conditions.append(combined.negate())
    if _condition_region_is_unsat(default_conditions):
        return list(cases)
    return_size = get_return_size(analysis)
    zero = Expression.constant(0, size=max(1, (int(return_size) + 7) // 8))
    default_info = ReturnInfo(
        address="<ordered-ite-default>",
        value=zero,
        conditions=list(default_conditions),
        return_kind="ordered_ite_default",
    )
    default_case = ReturnCase(
        index=-1,
        conditions=list(default_conditions),
        value_expr=zero,
        normalized_value_expr=zero,
        return_info=default_info,
        return_type=analysis.get_comparison_type_name(),
        return_type_obj=analysis.get_comparison_type_obj(),
        source_indices=[-1],
        parameters=list(analysis.parameters or []),
        effect_summary=getattr(analysis, "effect_summary", None),
        comparison_surface=analysis.get_comparison_surface(),
        summary_conditions=list(default_conditions),
        program_is_big_endian=getattr(analysis, "program_is_big_endian", None),
    )
    return [*cases, default_case]


def _build_condition_rewriter(
    analysis: FunctionReturnAnalysis,
    authorization: Optional[RewriteAuthorization] = None,
):
    parameter_rewriter = _ParameterMetadataRewriter(getattr(analysis, "parameters", []) or [])
    semantic_rewriter = SemanticWidthNormalizer(
        hint_objects_by_identity(analysis),
        authorization,
    ).rewrite_expression

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
    signature.sort(key=repr)
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
    header_lines = tuple(base_ctx["header_lines"])
    header_has_logic = any(
        str(line).lstrip().startswith("(set-logic ")
        for line in header_lines
    )
    lines = _build_query_header(
        f"; Pairwise Query (Conditions Only): Pair {pair_id}",
        f"; Case1[{case1.index}]: {case1.get_condition_summary()}",
        f"; Case2[{case2.index}]: {case2.get_condition_summary()}",
        logic="" if header_has_logic else base_ctx.get("smt_logic", "QF_BV"),
    )
    lines.extend(header_lines)
    lines.extend(_build_case_conditions(case1, param_replace_fn1, "Case1"))
    lines.extend(_build_case_conditions(case2, param_replace_fn2, "Case2"))
    lines.extend(_build_pairwise_extra_assertions(base_ctx, pair_id, guard_only=True))
    lines.append("(check-sat)")
    return "\n".join(lines)


def build_void_return_disequivalence_query(
    base_ctx: Dict[str, Any],
    case1: ReturnCase,
    case2: ReturnCase,
    param_replace_fn1,
    param_replace_fn2,
    pair_id: str,
) -> str:
    """Build the full observable-difference query for two void returns.

    There is no return value to compare.  Pair-local call/effect projection
    assertions still have to be present in an executed query so their binding
    uses can be audited.  Once those certified observations are assumed, the
    remaining return-value disequality is false by construction.
    """

    lines = _build_query_header(
        f"; Pairwise Void-Return Disequivalence: Pair {pair_id}",
        f"; Case1[{case1.index}]: {case1.get_condition_summary()}",
        f"; Case2[{case2.index}]: {case2.get_condition_summary()}",
        logic=base_ctx.get("smt_logic", "QF_BV"),
    )
    lines.extend(base_ctx["header_lines"])
    lines.extend(_build_case_conditions(case1, param_replace_fn1, "Case1"))
    lines.extend(_build_case_conditions(case2, param_replace_fn2, "Case2"))
    lines.extend(_build_pairwise_extra_assertions(base_ctx, pair_id))
    lines.extend([
        "",
        "; Both functions return void; no return-value difference exists",
        "(assert false)",
        "(check-sat)",
        "(get-model)",
    ])
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
        logic=base_ctx.get("smt_logic", "QF_BV"),
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
    # Issue #124: pair query のレンダリングを計測する（全 renderer がここを通る）。
    with stage_region("query_build"):
        lines = _build_query_header(
            f"; Pairwise Query: Pair {pair_id}",
            f"; Case1[{case1.index}]: {case1.get_condition_summary()}",
            f"; Case2[{case2.index}]: {case2.get_condition_summary()}",
            logic=base_ctx.get("smt_logic", "QF_BV"),
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
    *,
    guard_only: bool = False,
) -> List[str]:
    assertions_by_pair = base_ctx.get("pairwise_extra_assertions_by_pair") or {}
    if guard_only:
        bundles = tuple(
            (base_ctx.get("call_projection_assertion_bundles_by_pair") or {}).get(pair_id, ())
            or ()
        )
        call_assertions = tuple(
            assertion
            for bundle in bundles
            if callable(getattr(bundle, "is_guard_bound", None)) and bundle.is_guard_bound()
            for assertion in bundle.assertions
        )
        extra = tuple(
            (base_ctx.get("guard_extra_assertions_by_pair") or {}).get(pair_id, ()) or ()
        )
    else:
        call_projection_by_pair = base_ctx.get("call_projection_assertions_by_pair") or {}
        call_assertions = tuple(call_projection_by_pair.get(pair_id) or ())
        extra = tuple(assertions_by_pair.get(pair_id) or ())
    raw_assertions = call_assertions + extra
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
        logic=base_ctx.get("smt_logic", "QF_BV"),
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


def _build_query_header(*comment_lines: str, logic: str = "QF_BV") -> List[str]:
    lines = []
    lines.append("; " + "=" * 60)
    lines.extend(comment_lines)
    lines.append("; " + "=" * 60)
    lines.append("")
    if logic:
        lines.append(f"(set-logic {logic})")
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
