# -*- coding: utf-8 -*-
"""Acceptance gates for loop-summary-derived return candidates."""

from __future__ import annotations

from dataclasses import dataclass, replace
from typing import Any, Dict, Iterable, List, Mapping, Optional, Sequence, Tuple

from ..model import Condition, Expression, FunctionReturnAnalysis, ReturnInfo, SummaryReturnCandidate
from ..model import ExpressionType
from ..model.structural import key_contains_placeholder
from .condition.simplifier import ConditionSimplifier
from .condition.smt_oracle import ConditionSMTOracle


SUMMARY_RETURN_SCHEMA_VERSION = "summary-return-candidate-v1"


@dataclass(frozen=True)
class SummaryReturnAcceptanceResult:
    accepted_returns: Tuple[ReturnInfo, ...]
    candidates: Tuple[SummaryReturnCandidate, ...]
    blockers: Tuple[str, ...]
    coverage_complete: bool


def accept_summary_return_candidates(
    analysis: FunctionReturnAnalysis,
    proposed_returns: Sequence[ReturnInfo],
    *,
    summary_note: str,
    enable_completed_recovery_proofs: bool = True,
) -> SummaryReturnAcceptanceResult:
    """Validate summary-derived returns before exposing them as normal returns.

    ``proposed_returns`` is the summarizer's proposed full return partition. The
    candidates are the proposed returns that are not already present in
    ``analysis.returns``. They are accepted only after candidate-level checks,
    overlap checks against exact returns, and a proposed-partition coverage proof.
    """

    exact_returns = tuple(
        ret
        for ret in (getattr(analysis, "returns", ()) or ())
        if _return_is_exact_seed(ret)
    )
    proposed_returns = tuple(proposed_returns or ())
    if not proposed_returns:
        return SummaryReturnAcceptanceResult((), (), ("summary_return_candidate_invalid:no_proposed_returns",), False)

    exact_keys = {_return_info_identity_key(ret) for ret in exact_returns}
    candidates: List[SummaryReturnCandidate] = []
    candidate_indices: set[int] = set()
    for index, ret in enumerate(proposed_returns):
        if _return_info_identity_key(ret) in exact_keys:
            continue
        if not _return_has_summary_provenance(ret):
            continue
        candidate = build_summary_return_candidate(
            analysis,
            ret,
            summary_note=summary_note,
            candidate_index=index,
        )
        candidates.append(candidate)
        candidate_indices.add(index)

    if not candidates:
        blockers = ("summary_return_candidate_invalid:no_new_summary_returns",)
        return SummaryReturnAcceptanceResult((), tuple(candidates), blockers, False)

    blockers: List[str] = []
    valid_candidates: Dict[int, SummaryReturnCandidate] = {}
    for candidate in candidates:
        candidate_blockers = _validate_candidate(
            candidate,
            analysis,
            enable_completed_recovery_proofs=enable_completed_recovery_proofs,
        )
        if candidate_blockers:
            blockers.extend(candidate_blockers)
            candidate.validation_blockers = tuple(candidate_blockers)
            candidate.acceptance_status = "rejected"
            candidate.eq_eligible = False
            continue
        candidate.acceptance_status = "valid_candidate"
        candidate.eq_eligible = True
        candidate.validation_blockers = ()
        valid_candidates[int(candidate.evidence.get("candidate_index", -1))] = candidate

    if not valid_candidates:
        if not blockers:
            blockers.append("summary_return_candidate_invalid:no_valid_candidates")
        return SummaryReturnAcceptanceResult((), tuple(candidates), tuple(dict.fromkeys(blockers)), False)

    proposed_partition = tuple(exact_returns) + tuple(
        _candidate_return_for_partition(valid_candidates[index])
        for index in sorted(valid_candidates)
    )

    overlap_blockers = _check_candidate_overlaps(
        analysis,
        valid_candidates.values(),
        exact_returns,
    )
    blockers.extend(overlap_blockers)

    coverage_complete = False
    if not overlap_blockers:
        coverage_complete = _return_partition_covers_active_precondition(
            proposed_partition,
            _active_preconditions(analysis),
        )
        if not coverage_complete:
            blockers.append("summary_partition_not_total:active_precondition_not_covered")

    if blockers:
        unique_blockers = tuple(dict.fromkeys(blockers))
        for candidate in candidates:
            if candidate.acceptance_status == "valid_candidate":
                candidate.acceptance_status = "rejected"
                candidate.eq_eligible = False
                candidate.validation_blockers = unique_blockers
        return SummaryReturnAcceptanceResult((), tuple(candidates), unique_blockers, coverage_complete)

    accepted: List[ReturnInfo] = []
    accepted.extend(exact_returns)
    for index in sorted(valid_candidates):
        candidate = valid_candidates[index]
        candidate.acceptance_status = "accepted"
        candidate.eq_eligible = True
        accepted_return = _accepted_candidate_return(candidate)
        candidate.return_info = accepted_return
        accepted.append(accepted_return)

    return SummaryReturnAcceptanceResult(tuple(accepted), tuple(candidates), (), True)


def build_summary_return_candidate(
    analysis: FunctionReturnAnalysis,
    ret: ReturnInfo,
    *,
    summary_note: str,
    candidate_index: int,
) -> SummaryReturnCandidate:
    guard_key = _conditions_key(ret.conditions or ())
    value_key = _expression_key(getattr(ret, "value", None))
    active_precondition_key = _active_precondition_key(analysis)
    loop_summary_key = _loop_summary_structural_key(ret)
    memory_read_key = _memory_read_set_key(ret)
    effect_key = _effect_region_key(analysis, guard_key, memory_read_key)
    candidate_id = (
        SUMMARY_RETURN_SCHEMA_VERSION,
        _analysis_key(analysis),
        str(summary_note or "structural_summary"),
        int(candidate_index),
        guard_key,
        value_key,
        effect_key,
    )
    return SummaryReturnCandidate(
        candidate_id=candidate_id,
        return_info=ret,
        guard_structural_key=guard_key,
        value_structural_key=value_key,
        loop_summary_structural_key=loop_summary_key,
        transition_evidence_key=_summary_transition_evidence_key(ret),
        active_precondition_key=active_precondition_key,
        summary_applicability_guard_key=guard_key if guard_key else None,
        effect_region_key=effect_key,
        memory_read_set_key=memory_read_key,
        memory_write_set_key=_memory_write_set_key(analysis),
        call_effect_key=_call_effect_key(analysis),
        ub_assumption_key=("ub_assumptions", "none"),
        eq_eligible=False,
        acceptance_status="candidate",
        evidence={
            "schema_version": SUMMARY_RETURN_SCHEMA_VERSION,
            "summary_note": str(summary_note or "structural_summary"),
            "candidate_index": int(candidate_index),
        },
    )


def _return_has_summary_provenance(ret: ReturnInfo) -> bool:
    if str(getattr(ret, "return_kind", "exact") or "exact") == "summary_derived":
        return True
    if getattr(ret, "summary_candidate_source_key", None):
        return True
    return _loop_summary_structural_key(ret) is not None


def _return_is_exact_seed(ret: ReturnInfo) -> bool:
    return str(getattr(ret, "return_kind", "exact") or "exact") == "exact"


def _validate_candidate(
    candidate: SummaryReturnCandidate,
    analysis: FunctionReturnAnalysis,
    *,
    enable_completed_recovery_proofs: bool,
) -> Tuple[str, ...]:
    blockers: List[str] = []
    ret = candidate.return_info
    if not getattr(ret, "conditions", None):
        blockers.append("summary_precondition_incomplete:summary_applicability_guard_missing")
    if getattr(ret, "value", None) is None:
        blockers.append("summary_return_candidate_invalid:value_missing")
    if key_contains_placeholder(candidate.guard_structural_key):
        blockers.append("summary_return_candidate_invalid:unstable_guard_key")
    if key_contains_placeholder(candidate.value_structural_key):
        blockers.append("summary_return_candidate_invalid:unstable_value_key")
    if _key_contains_forbidden_identity(candidate.guard_structural_key):
        blockers.append("summary_return_candidate_invalid:opaque_guard_key")
    if _key_contains_forbidden_identity(candidate.value_structural_key):
        blockers.append("summary_return_candidate_invalid:opaque_value_key")
    if not candidate.loop_summary_structural_key:
        blockers.append("summary_return_candidate_invalid:loop_summary_identity_missing")
    elif _key_contains_forbidden_identity(candidate.loop_summary_structural_key):
        blockers.append("summary_return_candidate_invalid:unstable_loop_summary_identity")
    if not candidate.transition_evidence_key:
        blockers.append("summary_return_candidate_invalid:transition_evidence_missing")
    elif _key_contains_forbidden_identity(candidate.transition_evidence_key):
        blockers.append("summary_return_candidate_invalid:unstable_transition_evidence")
    elif _key_contains_incomplete_summary_metadata(candidate.transition_evidence_key):
        blockers.append("summary_return_candidate_invalid:transition_evidence_incomplete")
    elif not _transition_evidence_has_required_parts(
        candidate.transition_evidence_key,
        analysis,
        enable_completed_recovery_proofs=enable_completed_recovery_proofs,
    ):
        blockers.append("summary_return_candidate_invalid:transition_evidence_incomplete")
    if _key_contains_incomplete_summary_metadata(candidate.loop_summary_structural_key):
        blockers.append("summary_effect_unmodeled:side_effect_provenance_incomplete")
    if _key_contains_incomplete_summary_metadata(candidate.effect_region_key):
        blockers.append("summary_effect_unmodeled:effect_region_incomplete")
    if _return_info_contains_phi_circular(ret):
        blockers.append("phi_circular_replacement_unproven:replacement_obligation_missing")
    if not _return_storage_width_key(ret):
        blockers.append("summary_return_candidate_invalid:return_width_missing")
    if _memory_read_unmodeled(candidate.memory_read_set_key):
        blockers.append("summary_effect_unmodeled:memory_read_unmodeled")
    effect_blocker = _effect_eligibility_blocker(analysis)
    if effect_blocker is not None:
        blockers.append(effect_blocker)
    return tuple(dict.fromkeys(blockers))


def _check_candidate_overlaps(
    analysis: FunctionReturnAnalysis,
    candidates: Iterable[SummaryReturnCandidate],
    exact_returns: Sequence[ReturnInfo],
) -> Tuple[str, ...]:
    blockers: List[str] = []
    active_preconditions = _active_preconditions(analysis)
    candidate_list = list(candidates)
    for candidate in candidate_list:
        candidate_return = candidate.return_info
        for exact_return in exact_returns:
            blockers.extend(
                _check_return_overlap_value_equality(
                    candidate_return,
                    exact_return,
                    active_preconditions,
                )
            )
    for left_index, left_candidate in enumerate(candidate_list):
        for right_candidate in candidate_list[left_index + 1:]:
            blockers.extend(
                _check_return_overlap_value_equality(
                    left_candidate.return_info,
                    right_candidate.return_info,
                    active_preconditions,
                )
            )
    return tuple(dict.fromkeys(blockers))


def _check_return_overlap_value_equality(
    left: ReturnInfo,
    right: ReturnInfo,
    active_preconditions: Sequence[Condition],
) -> Tuple[str, ...]:
    overlap_conditions = (
        list(left.conditions or [])
        + list(right.conditions or [])
        + list(active_preconditions)
    )
    overlap_unsat = _conditions_unsat(overlap_conditions)
    if overlap_unsat is True:
        return ()
    if overlap_unsat is None:
        return ("summary_return_overlap_unproven:overlap_feasibility_unknown",)
    compatibility_blockers = _return_merge_compatibility_blockers(left, right)
    if compatibility_blockers:
        return compatibility_blockers
    inequality = _value_inequality_condition(left, right)
    if inequality is None:
        return ("summary_return_overlap_unproven:value_comparison_unavailable",)
    equality_obligation = list(overlap_conditions) + [inequality]
    equality_unsat = _conditions_unsat(equality_obligation)
    if equality_unsat is not True:
        return ("summary_return_overlap_unproven:value_equality_not_proved",)
    return ()


def _return_partition_covers_active_precondition(
    returns: Sequence[ReturnInfo],
    active_preconditions: Sequence[Condition] = (),
) -> bool:
    conditions_by_return = [list(ret.conditions or []) for ret in returns or ()]
    if not conditions_by_return:
        return False
    region_exprs = []
    has_unconditional = False
    for ret, conditions in zip(returns or (), conditions_by_return):
        if not conditions:
            if getattr(ret, "return_kind", "exact") == "summary_derived":
                return False
            has_unconditional = True
            break
        combined = Condition.combine_and(conditions)
        if combined is None:
            return False
        region_exprs.append(_condition_as_expression(combined))
    if has_unconditional:
        return True
    if not region_exprs:
        return False
    disjunction = _combine_or(region_exprs)
    miss_condition = Condition(disjunction, True)
    miss_unsat = _conditions_unsat(list(active_preconditions or ()) + [miss_condition])
    return miss_unsat is True


def _candidate_return_for_partition(candidate: SummaryReturnCandidate) -> ReturnInfo:
    return replace(
        candidate.return_info,
        return_kind="summary_derived",
        acceptance_status="valid_candidate",
        summary_candidate_id=candidate.candidate_id,
        summary_transition_evidence_key=candidate.transition_evidence_key,
        validation_blockers=(),
    )


def _accepted_candidate_return(candidate: SummaryReturnCandidate) -> ReturnInfo:
    return replace(
        candidate.return_info,
        return_kind="summary_derived",
        acceptance_status="accepted",
        summary_candidate_id=candidate.candidate_id,
        summary_transition_evidence_key=candidate.transition_evidence_key,
        validation_blockers=(),
    )


def _conditions_unsat(conditions: Sequence[Condition]) -> Optional[bool]:
    condition_list = [condition for condition in conditions or () if condition is not None]
    if not condition_list:
        return False
    try:
        solver_unsat = ConditionSMTOracle.conjunction_is_unsat(condition_list)
    except Exception:
        solver_unsat = None
    if solver_unsat is not None:
        return bool(solver_unsat)
    try:
        if ConditionSimplifier.object_centric_is_contradiction(condition_list):
            return True
    except Exception:
        pass
    return None


def _value_inequality_condition(left: ReturnInfo, right: ReturnInfo) -> Optional[Condition]:
    left_value = getattr(left, "value", None)
    right_value = getattr(right, "value", None)
    if left_value is None or right_value is None:
        return None
    left_bits = _expr_width_bits(left_value)
    right_bits = _expr_width_bits(right_value)
    if left_bits <= 0 or right_bits <= 0 or left_bits != right_bits:
        return None
    return Condition(Expression.binary_op("INT_NOTEQUAL", left_value, right_value), False)


def _return_merge_compatibility_blockers(left: ReturnInfo, right: ReturnInfo) -> Tuple[str, ...]:
    blockers: List[str] = []
    if _return_storage_width_key(left) != _return_storage_width_key(right):
        blockers.append("summary_return_overlap_unproven:return_width_mismatch")
    left_signedness = _expression_signedness_key(getattr(left, "value", None))
    right_signedness = _expression_signedness_key(getattr(right, "value", None))
    if left_signedness != right_signedness:
        blockers.append("summary_return_overlap_unproven:signedness_mismatch")
    if _memory_read_set_key(left) != _memory_read_set_key(right):
        blockers.append("summary_return_overlap_unproven:memory_read_model_mismatch")
    return tuple(dict.fromkeys(blockers))


def _combine_or(expressions: Sequence[Expression]) -> Expression:
    if not expressions:
        raise ValueError("Cannot OR an empty expression list")
    result = expressions[0]
    for expr in expressions[1:]:
        result = Expression.binary_op("BOOL_OR", result, expr)
    return result


def _condition_as_expression(condition: Condition) -> Expression:
    if condition.negated:
        return Expression.unary_op("BOOL_NEGATE", condition.expression)
    return condition.expression


def _return_info_identity_key(ret: ReturnInfo) -> Tuple[Any, ...]:
    return (
        "return_info",
        getattr(ret, "address", None),
        getattr(ret, "pcode_identity", None),
        getattr(ret, "pcode_order", None),
        getattr(ret, "pcode_time", None),
        _stable_key_or_none(getattr(ret, "pcode_op_ref", None)),
        _conditions_key(getattr(ret, "conditions", ()) or ()),
        _expression_key(getattr(ret, "value", None)),
    )


def _conditions_key(conditions: Sequence[Condition]) -> Tuple[Any, ...]:
    keys = []
    for condition in conditions or ():
        try:
            keys.append(condition.structural_key(budget=256))
        except Exception:
            keys.append(("opaque_condition", type(condition).__name__))
    keys.sort(key=repr)
    return ("conditions", tuple(keys))


def _expression_key(expr: Optional[Expression]) -> Tuple[Any, ...]:
    if expr is None:
        return ("expr", "none")
    try:
        return expr.structural_key(
            budget=256,
            normalize_commutative=True,
            include_memory_read_order=True,
            include_semantic_runtime_refs=True,
        )
    except Exception:
        return ("opaque_expression", type(expr).__name__)


def _key_contains_forbidden_identity(value: Any) -> bool:
    if isinstance(value, tuple):
        if value and value[0] in {
            "opaque",
            "object_id",
            "opaque_condition",
            "opaque_expression",
            "expression_object",
            "varnode_id",
            "block_id",
            "id",
        }:
            return True
        return any(_key_contains_forbidden_identity(item) for item in value)
    if isinstance(value, list):
        return any(_key_contains_forbidden_identity(item) for item in value)
    if isinstance(value, dict):
        return any(
            _key_contains_forbidden_identity(key) or _key_contains_forbidden_identity(item)
            for key, item in value.items()
        )
    return False


def _key_contains_incomplete_summary_metadata(value: Any) -> bool:
    if value is None:
        return True
    if isinstance(value, str):
        return value in {"unavailable", "incomplete", "not_modeled_by_summary_return_v1"}
    if isinstance(value, tuple):
        if value in {
            ("side_effect_profile", "unavailable"),
            ("memory_reads", "not_modeled_by_summary_return_v1"),
            ("memory_reads", "unmodeled"),
        }:
            return True
        return any(_key_contains_incomplete_summary_metadata(item) for item in value)
    if isinstance(value, list):
        return any(_key_contains_incomplete_summary_metadata(item) for item in value)
    if isinstance(value, dict):
        return any(
            _key_contains_incomplete_summary_metadata(key)
            or _key_contains_incomplete_summary_metadata(item)
            for key, item in value.items()
        )
    return False


def _transition_evidence_has_required_parts(
    value: Any,
    analysis: FunctionReturnAnalysis,
    *,
    enable_completed_recovery_proofs: bool,
) -> bool:
    evidence = _unwrap_counted_loop_transition_evidence(value)
    if evidence is None:
        return False
    fields = _tagged_tuple_fields(evidence[1:])
    required_markers = {
        "header_block",
        "latch_block",
        "exit_block",
        "induction_phi",
        "accumulator_phi",
        "exit_guard",
        "exit_guard_binding",
        "bound_binding",
        "accumulator_base",
        "updates",
        "loop_cases",
        "replacement_obligation",
    }
    if not required_markers.issubset(fields):
        return False

    block_tags = ("header_block", "latch_block", "exit_block")
    op_tags = ("induction_phi", "accumulator_phi", "exit_guard")
    if any(not _tag_has_scoped_pcode_block_payload(fields[tag]) for tag in block_tags):
        return False
    if any(not _tag_has_nonempty_payload(fields[tag], expected_arity=2) for tag in op_tags):
        return False
    if not _tag_has_nonempty_payload(fields["exit_guard_binding"], expected_arity=2):
        return False
    if not _tag_has_nonempty_payload(fields["bound_binding"], expected_arity=2):
        return False

    accumulator_base = fields["accumulator_base"]
    if not isinstance(accumulator_base, tuple) or len(accumulator_base) != 4:
        return False
    if accumulator_base[0] != "accumulator_base":
        return False
    if any(_key_contains_incomplete_summary_metadata(item) for item in accumulator_base[1:]):
        return False
    if not _accumulator_base_dependency_is_proved(
        accumulator_base,
        analysis,
        enable_completed_recovery_proofs=enable_completed_recovery_proofs,
    ):
        return False

    updates = fields["updates"]
    if not isinstance(updates, tuple) or len(updates) != 2:
        return False
    update_entries = updates[1]
    if not isinstance(update_entries, tuple) or not update_entries:
        return False
    for update in update_entries:
        if not isinstance(update, tuple) or len(update) != 3:
            return False
        if _key_contains_incomplete_summary_metadata(update):
            return False

    loop_cases = fields["loop_cases"]
    if not isinstance(loop_cases, tuple) or len(loop_cases) != 2:
        return False
    loop_case_entries = loop_cases[1]
    if not isinstance(loop_case_entries, tuple) or not loop_case_entries:
        return False
    if _key_contains_incomplete_summary_metadata(loop_case_entries):
        return False

    replacement = fields["replacement_obligation"]
    if not isinstance(replacement, tuple) or len(replacement) != 2:
        return False
    return not _key_contains_incomplete_summary_metadata(replacement[1])


def _unwrap_counted_loop_transition_evidence(value: Any) -> Optional[Tuple[Any, ...]]:
    if not isinstance(value, tuple) or not value:
        return None
    if value[0] == "counted_loop_transition_evidence":
        return value
    for item in value:
        nested = _unwrap_counted_loop_transition_evidence(item)
        if nested is not None:
            return nested
    return None


def _tagged_tuple_fields(items: Sequence[Any]) -> Dict[str, Tuple[Any, ...]]:
    fields: Dict[str, Tuple[Any, ...]] = {}
    for item in items:
        if not isinstance(item, tuple) or not item:
            continue
        tag = item[0]
        if not isinstance(tag, str):
            continue
        fields[tag] = item
    return fields


def _tag_has_nonempty_payload(value: Any, *, expected_arity: int) -> bool:
    if not isinstance(value, tuple) or len(value) != expected_arity:
        return False
    return not _key_contains_incomplete_summary_metadata(value[1])


def _accumulator_base_dependency_is_proved(
    accumulator_base: Tuple[Any, ...],
    analysis: FunctionReturnAnalysis,
    *,
    enable_completed_recovery_proofs: bool,
) -> bool:
    if len(accumulator_base) != 4:
        return False
    init_key = accumulator_base[1]
    loop_base_key = accumulator_base[2]
    dependency_key = accumulator_base[3]
    if dependency_key == ("prior_summary_dependency", "none") or dependency_key == ("prior_summary", "none"):
        return init_key == loop_base_key
    if _key_contains_forbidden_identity(dependency_key):
        return False
    if _key_contains_incomplete_summary_metadata(dependency_key):
        return False
    return _prior_summary_dependency_key_is_strong(
        dependency_key,
        analysis,
        enable_completed_recovery_proofs=enable_completed_recovery_proofs,
    )


def _tag_has_scoped_pcode_block_payload(value: Any) -> bool:
    if not _tag_has_nonempty_payload(value, expected_arity=2):
        return False
    return _is_scoped_pcode_block_key(value[1])


def _is_scoped_pcode_block_key(value: Any) -> bool:
    if not isinstance(value, tuple) or len(value) != 5:
        return False
    if value[0] != "pcode_block":
        return False
    if _key_contains_incomplete_summary_metadata(value[1]):
        return False
    function_entry = value[2]
    if not isinstance(function_entry, tuple) or len(function_entry) != 3:
        return False
    if function_entry[0] != "function_entry":
        return False
    if _key_contains_incomplete_summary_metadata(function_entry[1]):
        return False
    if _key_contains_incomplete_summary_metadata(function_entry[2]):
        return False
    return not _key_contains_incomplete_summary_metadata(value[3:])


def _prior_summary_dependency_key_is_strong(
    value: Any,
    analysis: FunctionReturnAnalysis,
    *,
    enable_completed_recovery_proofs: bool,
) -> bool:
    if not isinstance(value, tuple) or not value:
        return False
    tag = value[0]
    if tag == "counted_loop_summary_parts":
        return _counted_loop_summary_parts_key_is_strong(value)
    if tag == "counted_loop_summary_fallback":
        return _counted_loop_summary_fallback_key_is_strong(value)
    if tag == "prior_state_transition_handoff_proof_ref":
        return _prior_state_transition_handoff_proof_ref_is_strong(
            value,
            analysis,
            enable_completed_recovery_proofs=enable_completed_recovery_proofs,
        )
    return False


def _prior_state_transition_handoff_proof_ref_is_strong(
    value: Tuple[Any, ...],
    analysis: FunctionReturnAnalysis,
    *,
    enable_completed_recovery_proofs: bool,
) -> bool:
    if not enable_completed_recovery_proofs:
        return False
    if len(value) != 3:
        return False
    if _key_contains_forbidden_identity(value) or _key_contains_incomplete_summary_metadata(value):
        return False
    _tag, proof_obligation_id, object_target_key = value
    if not proof_obligation_id or not _prior_state_transition_handoff_target_key_is_strong(object_target_key):
        return False
    if not _prior_state_transition_handoff_proof_id_matches_target(
        proof_obligation_id,
        object_target_key,
    ):
        return False
    completed = _completed_prior_state_transition_handoff_proof_ids(analysis)
    return proof_obligation_id in completed


def _prior_state_transition_handoff_target_key_is_strong(value: Any) -> bool:
    if not isinstance(value, tuple) or len(value) != 8 or value[0] != "prior_state_transition_handoff_target":
        return False
    (
        _tag,
        target_summary_key,
        handoff_blocks,
        value_flow,
        guard_handoff,
        loop_identity,
        side_effect_key,
        widths,
    ) = value
    if not _counted_state_transition_summary_key_is_strong(target_summary_key):
        return False
    if not _handoff_blocks_key_is_strong(handoff_blocks):
        return False
    if not _value_preserving_flow_key_is_strong(value_flow):
        return False
    if not _guard_handoff_key_is_strong(guard_handoff):
        return False
    if not _loop_identity_key_is_strong(loop_identity):
        return False
    if not _counted_state_transition_side_effect_profile_key_is_strong(side_effect_key):
        return False
    return _handoff_widths_key_is_strong(widths)


def _completed_prior_state_transition_handoff_proof_ids(
    analysis: FunctionReturnAnalysis,
) -> Tuple[Tuple[Any, ...], ...]:
    proof_ids: List[Tuple[Any, ...]] = []
    for evidence in getattr(analysis, "completed_recovery_proof_evidence", ()) or ():
        proof_id = _prior_state_transition_handoff_proof_id_from_evidence(evidence)
        if proof_id is not None:
            proof_ids.append(proof_id)
    return tuple(dict.fromkeys(proof_ids))


def _prior_state_transition_handoff_proof_id_from_evidence(evidence: Any) -> Optional[Tuple[Any, ...]]:
    if not isinstance(evidence, Mapping):
        return None
    if not bool(evidence.get("object_derived")):
        return None
    if str(evidence.get("status") or "") not in {"complete", "completed", "proven"}:
        return None
    if str(evidence.get("proof_stage") or "") != "prior_state_transition_handoff":
        return None
    if str(evidence.get("evidence_kind") or "") != "value_preserving_handoff":
        return None
    proof_id = _nested_tuple(evidence.get("proof_obligation_id"))
    object_target_key = _nested_tuple(evidence.get("object_target_key"))
    if proof_id is None or not _prior_state_transition_handoff_target_key_is_strong(object_target_key):
        return None
    if not _prior_state_transition_handoff_proof_id_matches_target(proof_id, object_target_key):
        return None
    proof_content = evidence.get("proof_content")
    if not isinstance(proof_content, Mapping):
        return None
    content_target_key = _nested_tuple(proof_content.get("object_target_key"))
    if content_target_key != object_target_key:
        return None
    if str(proof_content.get("handoff_status") or "") != "proved":
        return None
    if not bool(proof_content.get("object_derived")):
        return None
    if not _prior_state_transition_handoff_proof_content_matches_target(
        proof_content,
        object_target_key,
    ):
        return None
    return proof_id


def _prior_state_transition_handoff_proof_id_matches_target(
    proof_id: Any,
    object_target_key: Any,
) -> bool:
    return (
        isinstance(proof_id, tuple)
        and len(proof_id) == 3
        and proof_id[0] == "proof_obligation_id"
        and proof_id[1] == "prior_state_transition_handoff"
        and proof_id[2] == object_target_key
    )


def _prior_state_transition_handoff_proof_content_matches_target(
    proof_content: Mapping[str, Any],
    object_target_key: Tuple[Any, ...],
) -> bool:
    if not _prior_state_transition_handoff_target_key_is_strong(object_target_key):
        return False
    (
        _tag,
        target_summary_key,
        handoff_blocks,
        value_flow,
        guard_handoff,
        loop_identity,
        side_effect_key,
        widths,
    ) = object_target_key
    expected_parts = {
        "target_summary_key": target_summary_key,
        "handoff_blocks": handoff_blocks,
        "value_flow": value_flow,
        "guard_handoff": guard_handoff,
        "loop_identity": loop_identity,
        "side_effect_profile": side_effect_key,
        "widths": widths,
    }
    for field, expected in expected_parts.items():
        if _nested_tuple(proof_content.get(field)) != expected:
            return False
    if not _value_flow_edges_are_bound_to_handoff_blocks(value_flow, handoff_blocks):
        return False
    checks = proof_content.get("checks")
    checks = _nested_tuple(checks)
    if not isinstance(checks, tuple):
        return False
    required_checks = {
        ("phi_predecessor_edge", "proved"),
        ("clean_handoff_paths", "proved"),
        ("value_preserving_flow", "proved"),
        ("guard_handoff", "proved"),
        ("loop_identity", "proved"),
        ("widths", "proved"),
        ("side_effects", "proved"),
    }
    return required_checks.issubset(set(checks))


def _value_flow_edges_are_bound_to_handoff_blocks(value_flow: Any, handoff_blocks: Any) -> bool:
    if not _value_preserving_flow_key_is_strong(value_flow):
        return False
    if not _handoff_blocks_key_is_strong(handoff_blocks):
        return False
    allowed_blocks = set(handoff_blocks[1:4])
    for edge in value_flow[3]:
        location = edge[6]
        if location == ("edge_location", "identity"):
            continue
        if not isinstance(location, tuple) or len(location) != 3 or location[0] != "edge_location":
            return False
        block_key = location[2]
        if block_key not in allowed_blocks:
            return False
    return True


def _nested_tuple(value: Any) -> Any:
    if isinstance(value, tuple):
        return tuple(_nested_tuple(item) for item in value)
    if isinstance(value, list):
        return tuple(_nested_tuple(item) for item in value)
    if isinstance(value, dict):
        return {
            key: _nested_tuple(item)
            for key, item in value.items()
        }
    return value


def _counted_state_transition_summary_key_is_strong(value: Any) -> bool:
    if not isinstance(value, tuple) or len(value) != 13:
        return False
    (
        tag,
        init_key,
        start_key,
        limit_key,
        step_key,
        transition_key,
        placeholder_key,
        side_effect_key,
        guard_keys,
        state_size,
        result_size,
        signed_loop,
        source,
    ) = value
    if tag != "counted_state_transition_loop_summary":
        return False
    if _key_contains_forbidden_identity(value) or _key_contains_incomplete_summary_metadata(value):
        return False
    return (
        bool(init_key)
        and bool(start_key)
        and bool(limit_key)
        and bool(step_key)
        and bool(transition_key)
        and bool(placeholder_key)
        and _counted_state_transition_side_effect_profile_key_is_strong(side_effect_key)
        and _guard_constraints_collection_is_strong(guard_keys)
        and isinstance(state_size, int)
        and state_size > 0
        and isinstance(result_size, int)
        and result_size > 0
        and isinstance(signed_loop, bool)
        and isinstance(source, str)
        and bool(source)
    )


def _handoff_blocks_key_is_strong(value: Any) -> bool:
    if not isinstance(value, tuple) or len(value) != 5 or value[0] != "handoff_blocks":
        return False
    if value[4] != "all_paths_clean_to_phi_predecessor":
        return False
    return all(_is_scoped_pcode_block_key(item) for item in value[1:4])


def _value_preserving_flow_key_is_strong(value: Any) -> bool:
    if not isinstance(value, tuple) or len(value) != 4 or value[0] != "value_preserving_flow":
        return False
    source_key, target_key, edges = value[1], value[2], value[3]
    if not source_key or not target_key:
        return False
    if not isinstance(edges, tuple) or not edges:
        return False
    for edge in edges:
        if not isinstance(edge, tuple) or len(edge) != 7:
            return False
        if edge[0] != "edge" or edge[1] not in {"identity", "COPY", "SUBPIECE_ZERO_SAME_WIDTH", "INT_ZEXT", "INT_SEXT"}:
            return False
        if not isinstance(edge[4], int) or not isinstance(edge[5], int):
            return False
        location = edge[6]
        if edge[1] == "identity":
            if location != ("edge_location", "identity"):
                return False
            continue
        if not isinstance(location, tuple) or len(location) != 3 or location[0] != "edge_location":
            return False
        if not _is_scoped_pcode_block_key(location[2]):
            return False
    return True


def _guard_handoff_key_is_strong(value: Any) -> bool:
    if not isinstance(value, tuple) or len(value) != 6 or value[0] != "guard_handoff_proof":
        return False
    _tag, proof_kind, prior_guard, current_guard, implication_status, active_conditions = value
    return (
        proof_kind in {"smt_implication", "identical_guard_domain"}
        and bool(prior_guard)
        and bool(current_guard)
        and implication_status == "proved"
        and bool(active_conditions)
    )


def _loop_identity_key_is_strong(value: Any) -> bool:
    if not isinstance(value, tuple) or len(value) != 8 or value[0] != "loop_identity":
        return False
    _tag, init_key, bound_key, step, guard_key, exit_key, signed_loop, overflow_model = value
    return (
        bool(init_key)
        and bool(bound_key)
        and isinstance(step, int)
        and bool(guard_key)
        and bool(exit_key)
        and isinstance(signed_loop, bool)
        and overflow_model == "bv_modular"
    )


def _handoff_widths_key_is_strong(value: Any) -> bool:
    if not isinstance(value, tuple) or len(value) != 5 or value[0] != "handoff_widths":
        return False
    _tag, source_width, target_width, return_width, conversion = value
    return (
        isinstance(source_width, int)
        and source_width > 0
        and isinstance(target_width, int)
        and target_width > 0
        and isinstance(return_width, int)
        and return_width > 0
        and conversion in {"same_width", "zero_extend", "sign_extend"}
    )


def _counted_state_transition_side_effect_profile_key_is_strong(value: Any) -> bool:
    if not isinstance(value, tuple) or len(value) < 15:
        return False
    if value[0] != "loop_side_effect_profile":
        return False
    if value[1] not in {"pure", "pure_conditional"}:
        return False
    bool_fields = value[2:11]
    if len(bool_fields) != 9 or not all(isinstance(item, bool) for item in bool_fields):
        return False
    (
        memory_reads,
        memory_writes,
        calls,
        escapes,
        _conditional_guards,
        context_memory_writes,
        context_calls,
        context_escapes,
        _context_conditional_guards,
    ) = bool_fields
    if any((memory_reads, memory_writes, calls, escapes, context_memory_writes, context_calls, context_escapes)):
        return False
    if not isinstance(value[11], int) or not isinstance(value[12], int):
        return False
    if not isinstance(value[13], tuple) or not isinstance(value[14], tuple):
        return False
    effect_descriptors = value[13]
    context_descriptors = value[14]
    if context_descriptors:
        return False
    for descriptor in effect_descriptors:
        if not isinstance(descriptor, tuple) or len(descriptor) < 2:
            return False
        if descriptor[0] != "loop_body_effect" or descriptor[1] != "conditional_guard":
            return False
    return True


def _counted_loop_summary_parts_key_is_strong(value: Tuple[Any, ...]) -> bool:
    if len(value) != 10:
        return False
    _, start_key, limit_key, induction_step, result_size, signed_loop, cases, guard_key, side_effect_key, source = value
    if _key_contains_forbidden_identity(value) or _key_contains_incomplete_summary_metadata(value):
        return False
    if not isinstance(induction_step, int):
        return False
    if not isinstance(result_size, int) or result_size <= 0:
        return False
    if not isinstance(signed_loop, bool):
        return False
    if not _summary_residue_cases_key_is_strong(cases):
        return False
    if not _guard_constraints_key_is_strong(guard_key):
        return False
    if not _loop_side_effect_profile_key_is_strong(side_effect_key):
        return False
    if not isinstance(source, str) or not source:
        return False
    return bool(start_key) and bool(limit_key)


def _counted_loop_summary_fallback_key_is_strong(value: Tuple[Any, ...]) -> bool:
    if len(value) != 8:
        return False
    _, induction_step, result_size, signed_loop, residue_cases, residue_bias_terms, source, loop_summary_key = value
    if _key_contains_forbidden_identity(value) or _key_contains_incomplete_summary_metadata(value):
        return False
    if not isinstance(induction_step, int):
        return False
    if not isinstance(result_size, int) or result_size <= 0:
        return False
    if not isinstance(signed_loop, bool):
        return False
    if not isinstance(residue_cases, tuple) or not residue_cases:
        return False
    if not isinstance(residue_bias_terms, tuple):
        return False
    if not isinstance(source, str) or not source:
        return False
    return _loop_summary_fallback_key_is_strong(loop_summary_key)


def _loop_summary_fallback_key_is_strong(value: Any) -> bool:
    if not isinstance(value, tuple) or len(value) != 7:
        return False
    tag, start_key, limit_key, step_key, guard_keys, side_effect_key, source = value
    if tag != "loop_summary_fallback":
        return False
    if _key_contains_forbidden_identity(value) or _key_contains_incomplete_summary_metadata(value):
        return False
    if not _guard_constraints_collection_is_strong(guard_keys):
        return False
    if not _loop_side_effect_profile_key_is_strong(side_effect_key):
        return False
    if not isinstance(source, str) or not source:
        return False
    return bool(start_key) and bool(limit_key) and bool(step_key)


def _summary_residue_cases_key_is_strong(value: Any) -> bool:
    if not isinstance(value, tuple) or not value:
        return False
    for case in value:
        if not isinstance(case, tuple) or len(case) != 5:
            return False
        modulus, residue, coeff, bias, bias_expr = case
        if not all(isinstance(item, int) for item in (modulus, residue, coeff, bias)):
            return False
        if not bias_expr:
            return False
    return True


def _guard_constraints_key_is_strong(value: Any) -> bool:
    if not isinstance(value, tuple) or len(value) != 2:
        return False
    if value[0] != "guard_constraints":
        return False
    return isinstance(value[1], tuple) and bool(value[1])


def _guard_constraints_collection_is_strong(value: Any) -> bool:
    if not isinstance(value, tuple) or not value:
        return False
    return all(bool(guard_key) for guard_key in value)


def _loop_side_effect_profile_key_is_strong(value: Any) -> bool:
    if not isinstance(value, tuple) or len(value) < 15:
        return False
    if value[0] != "loop_side_effect_profile":
        return False
    if value[1] != "pure":
        return False
    bool_fields = value[2:11]
    if len(bool_fields) != 9 or not all(isinstance(item, bool) for item in bool_fields):
        return False
    if any(bool_fields):
        return False
    if not isinstance(value[11], int) or not isinstance(value[12], int):
        return False
    if not isinstance(value[13], tuple) or not isinstance(value[14], tuple):
        return False
    return True


def _loop_summary_structural_key(ret: ReturnInfo) -> Optional[Tuple[Any, ...]]:
    source_key = getattr(ret, "summary_candidate_source_key", None)
    if source_key is not None:
        return ("loop_summary_identity", (source_key,))
    keys: List[Tuple[Any, ...]] = []
    for node in _iter_return_info_expression_nodes(ret):
        runtime_ref = getattr(node, "runtime_ref", None)
        for owner in (
            runtime_ref,
            getattr(runtime_ref, "loop_summary", None),
            getattr(runtime_ref, "accumulator_proof", None),
            getattr(runtime_ref, "proof", None),
        ):
            stable = _stable_key_or_none(owner)
            if stable is not None:
                stable_tuple = stable if isinstance(stable, tuple) else ("stable", stable)
                if _stable_key_looks_like_loop_summary(stable_tuple):
                    keys.append(stable_tuple)
    if not keys:
        return None
    keys.sort(key=repr)
    return ("loop_summary_identity", tuple(keys))


def _summary_transition_evidence_key(ret: ReturnInfo) -> Optional[Tuple[Any, ...]]:
    explicit = getattr(ret, "summary_transition_evidence_key", None)
    if explicit is not None:
        return explicit if isinstance(explicit, tuple) else ("transition_evidence", explicit)
    return None


def _counted_loop_transition_evidence_from_runtime_ref(runtime_ref: Any) -> Optional[Tuple[Any, ...]]:
    if runtime_ref is None or type(runtime_ref).__name__ != "CountedLoopSummaryRef":
        return None
    loop_summary = getattr(runtime_ref, "loop_summary", None)
    loop_key = _loop_summary_transition_evidence(loop_summary)
    if loop_key is None:
        return None
    return (
        "counted_loop_transition_evidence",
        int(getattr(runtime_ref, "induction_step", 0) or 0),
        int(getattr(runtime_ref, "result_size", 0) or 0),
        tuple(getattr(runtime_ref, "residue_cases", ()) or ()),
        loop_key,
    )


def _loop_summary_transition_evidence(loop_summary: Any) -> Optional[Tuple[Any, ...]]:
    if loop_summary is None:
        return None
    cases = tuple(getattr(loop_summary, "cases", ()) or ())
    if not cases:
        return None
    case_keys = tuple(_stable_key_or_none(case) for case in cases)
    if any(key is None for key in case_keys):
        return None
    guard_keys = tuple(_stable_key_or_none(guard) for guard in getattr(loop_summary, "guard_constraints", ()) or ())
    if any(key is None for key in guard_keys):
        return None
    side_effect_profile = getattr(loop_summary, "side_effect_profile", None)
    side_effect_key = _stable_key_or_none(side_effect_profile)
    if side_effect_key is None:
        return None
    if getattr(side_effect_profile, "requires_effect_proof", lambda: True)():
        return None
    return (
        "loop_summary_transition_evidence",
        _stable_key_or_none(getattr(loop_summary, "term_descriptor", None)),
        side_effect_key,
        guard_keys,
        case_keys,
        ("replacement_obligation", "not_required_without_phi_circular"),
    )


def _stable_key_looks_like_loop_summary(key: Tuple[Any, ...]) -> bool:
    text = repr(key)
    return any(
        marker in text
        for marker in (
            "counted_loop_summary",
            "readonly_reduction",
            "loop_summary",
            "state_transition_loop_summary",
            "reduction_accumulator_proof",
        )
    )


def _analysis_key(analysis: FunctionReturnAnalysis) -> Tuple[Any, ...]:
    return (
        "analysis",
        getattr(analysis, "binary_id", None),
        getattr(analysis, "function_name", None),
        getattr(analysis, "entry_point", None),
        tuple(_parameter_key(param) for param in getattr(analysis, "parameters", ()) or ()),
        getattr(analysis, "return_type", None),
    )


def _parameter_key(parameter: Dict[str, Any]) -> Tuple[Any, ...]:
    storage = parameter.get("storage_info", parameter.get("storage")) if isinstance(parameter, dict) else None
    return (
        "param",
        parameter.get("index") if isinstance(parameter, dict) else None,
        parameter.get("size") if isinstance(parameter, dict) else None,
        parameter.get("data_type") if isinstance(parameter, dict) else None,
        _stable_key_or_none(storage),
    )


def _active_precondition_key(analysis: FunctionReturnAnalysis) -> Tuple[Any, ...]:
    preconditions = _active_preconditions(analysis)
    return (
        "active_precondition",
        SUMMARY_RETURN_SCHEMA_VERSION,
        _analysis_key(analysis),
        _conditions_key(preconditions),
        _effect_region_key(analysis, ("conditions", ()), ("memory_reads", "none")),
    )


def _active_preconditions(analysis: FunctionReturnAnalysis) -> Tuple[Condition, ...]:
    preconditions = getattr(analysis, "active_function_preconditions", None)
    if preconditions is None:
        preconditions = getattr(analysis, "active_preconditions", None)
    return tuple(condition for condition in (preconditions or ()) if isinstance(condition, Condition))


def _effect_region_key(
    analysis: FunctionReturnAnalysis,
    guard_key: Tuple[Any, ...],
    memory_read_key: Tuple[Any, ...],
) -> Tuple[Any, ...]:
    effect_summary = getattr(analysis, "effect_summary", None)
    return (
        "effect_region",
        guard_key,
        memory_read_key,
        _memory_write_set_key(analysis),
        _call_effect_key(analysis),
        tuple(getattr(effect_summary, "incomplete_reasons", ()) or ()),
    )


def _memory_read_set_key(ret: ReturnInfo) -> Tuple[Any, ...]:
    read_keys: List[Any] = []
    unmodeled = False
    for node in _iter_return_info_expression_nodes(ret):
        if getattr(node, "expr_type", None) == ExpressionType.MEMORY:
            stable = _stable_key_or_none(getattr(node, "runtime_ref", None))
            if stable is None:
                unmodeled = True
            else:
                read_keys.append(stable)
        runtime_ref = getattr(node, "runtime_ref", None)
        stable = _stable_key_or_none(runtime_ref)
        if stable is not None and _stable_key_looks_like_modeled_memory_read(
            stable if isinstance(stable, tuple) else ("stable", stable)
        ):
            read_keys.append(stable)
    if unmodeled:
        return ("memory_reads", "unmodeled")
    if not read_keys:
        return ("memory_reads", "none")
    read_keys.sort(key=repr)
    return ("memory_reads", "modeled", tuple(read_keys))


def _stable_key_looks_like_modeled_memory_read(key: Tuple[Any, ...]) -> bool:
    text = repr(key)
    return any(
        marker in text
        for marker in (
            "readonly_reduction",
            "observed_memory_read",
            "post_state_read",
            "memory_read",
        )
    )


def _memory_read_unmodeled(memory_read_key: Optional[Tuple[Any, ...]]) -> bool:
    if not memory_read_key:
        return True
    if memory_read_key == ("memory_reads", "none"):
        return False
    if len(memory_read_key) >= 2 and memory_read_key[1] == "modeled":
        return _key_contains_forbidden_identity(memory_read_key)
    return True


def _memory_write_set_key(analysis: FunctionReturnAnalysis) -> Tuple[Any, ...]:
    effect_summary = getattr(analysis, "effect_summary", None)
    effects = tuple(getattr(effect_summary, "effects", ()) or ())
    return ("memory_writes", tuple(_stable_key_or_none(effect) for effect in effects))


def _call_effect_key(analysis: FunctionReturnAnalysis) -> Tuple[Any, ...]:
    effect_summary = getattr(analysis, "effect_summary", None)
    return (
        "call_effect",
        bool(getattr(effect_summary, "has_unsupported_call", False)),
        tuple(_stable_key_or_none(site) for site in getattr(effect_summary, "unsupported_call_sites", ()) or ()),
    )


def _effect_eligibility_blocker(analysis: FunctionReturnAnalysis) -> Optional[str]:
    effect_summary = getattr(analysis, "effect_summary", None)
    if effect_summary is None:
        return "summary_effect_unmodeled:effect_summary_missing"
    if getattr(effect_summary, "effects", None):
        return "summary_effect_unmodeled:memory_write_effects_present"
    if getattr(effect_summary, "has_unsupported_call", False):
        return "summary_effect_unmodeled:unsupported_call_effect"
    incomplete = tuple(getattr(effect_summary, "incomplete_reasons", ()) or ())
    if incomplete:
        return "summary_effect_unmodeled:" + ",".join(str(reason) for reason in incomplete)
    return None


def _iter_return_info_expression_nodes(ret: ReturnInfo):
    yield from _iter_expression_nodes(getattr(ret, "value", None))
    for condition in getattr(ret, "conditions", ()) or ():
        yield from _iter_expression_nodes(getattr(condition, "expression", None))


def _iter_expression_nodes(expr: Optional[Expression]):
    if expr is None:
        return
    yield expr
    if getattr(expr, "expr_type", None) == ExpressionType.PHI:
        for condition, value in getattr(expr, "value", None) or ():
            if condition is not None:
                yield from _iter_expression_nodes(getattr(condition, "expression", None))
            yield from _iter_expression_nodes(value)
        return
    for operand in getattr(expr, "operands", None) or ():
        yield from _iter_expression_nodes(operand)


def _return_info_contains_phi_circular(ret: ReturnInfo) -> bool:
    for node in _iter_return_info_expression_nodes(ret):
        runtime_ref = getattr(node, "runtime_ref", None)
        if getattr(runtime_ref, "reason", None) == "phi_circular":
            return True
        if getattr(runtime_ref, "kind", None) == "phi_circular":
            return True
        if getattr(node, "expr_type", None) == ExpressionType.UNKNOWN and "phi_circular" in str(
            getattr(node, "name", "")
        ):
            return True
    return False


def _expression_signedness_key(expr: Optional[Expression]) -> Tuple[Any, ...]:
    if expr is None:
        return ("signedness", "unknown")
    data_type = str(getattr(expr, "data_type", "") or "").lower()
    if "unsigned" in data_type:
        return ("signedness", "unsigned")
    if data_type:
        return ("signedness", "declared", data_type)
    return ("signedness", "unknown")


def _return_storage_width_key(ret: ReturnInfo) -> Tuple[Any, ...]:
    value = getattr(ret, "value", None)
    bits = _expr_width_bits(value)
    if bits <= 0:
        return ()
    return ("return_width", bits)


def _expr_width_bits(expr: Optional[Expression]) -> int:
    if expr is None:
        return 0
    size = int(getattr(expr, "size", 0) or 0)
    if size <= 0:
        get_width = getattr(expr, "get_bit_width", None)
        if callable(get_width):
            try:
                return int(get_width() or 0)
            except Exception:
                return 0
        return 0
    return size * 8


def _stable_key_or_none(value: Any) -> Any:
    if value is None:
        return None
    stable_key = getattr(value, "stable_key", None)
    if callable(stable_key):
        try:
            return stable_key()
        except Exception:
            return None
    if isinstance(value, dict):
        items = []
        for key, item in value.items():
            if str(key).startswith("_"):
                continue
            items.append((key, _stable_key_or_none(item)))
        items.sort(key=repr)
        return ("dict", tuple(items))
    if isinstance(value, (tuple, list)):
        return tuple(_stable_key_or_none(item) for item in value)
    if isinstance(value, (str, int, bool, bytes)):
        return value
    return None
