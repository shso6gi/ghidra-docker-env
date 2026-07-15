# -*- coding: utf-8 -*-
"""Acceptance gates for loop-summary-derived return candidates."""

from __future__ import annotations

from dataclasses import dataclass, replace
from typing import Any, Dict, Iterable, List, Mapping, Optional, Sequence, Tuple

from ..model import (
    Condition,
    CallTargetRef,
    DeferredCallRef,
    Expression,
    FunctionReturnAnalysis,
    ReadonlyReductionRef,
    ReadonlyReductionTermRef,
    ReturnInfo,
    SummaryReturnCandidate,
    UnknownValueRef,
)
from ..model import ExpressionType
from ..model.recurrence_contracts import (
    ImmutableRecurrenceCondition,
    ImmutableRecurrenceExpression,
    QuarantinedRecurrenceProposal,
    QuarantinedRecurrenceReturn,
    RecurrenceDigestCodec,
    RecurrenceSMTQueryReceipt,
    RecurrenceSeedCore,
    RetainedExactReturnRef,
)
from ..model.render_smt import expression_smt_bit_width
from ..model.structural import key_contains_placeholder
from . import effect_summary
from .effect_summary import canonicalize_location
from .condition.normalizer import ConditionNormalizer
from .condition.simplifier import ConditionSimplifier
from .condition.smt_oracle import ConditionSMTOracle


SUMMARY_RETURN_SCHEMA_VERSION = "summary-return-candidate-v1"


@dataclass(frozen=True)
class SummaryReturnAcceptanceResult:
    accepted_returns: Tuple[ReturnInfo, ...]
    candidates: Tuple[SummaryReturnCandidate, ...]
    blockers: Tuple[str, ...]
    coverage_complete: bool
    overlap_query_receipts: Tuple[RecurrenceSMTQueryReceipt, ...] = ()
    coverage_query_receipts: Tuple[RecurrenceSMTQueryReceipt, ...] = ()


def accept_summary_return_candidates(
    analysis: FunctionReturnAnalysis,
    proposed_returns: Sequence[ReturnInfo],
    *,
    summary_note: str,
    enable_completed_recovery_proofs: bool = True,
    require_smt_receipts: bool = False,
) -> SummaryReturnAcceptanceResult:
    """Validate summary-derived returns before exposing them as normal returns.

    ``proposed_returns`` is the summarizer's proposed full return partition. The
    candidates are the proposed returns that are not already present in
    ``analysis.returns``. They are accepted only after candidate-level checks,
    overlap checks against exact returns, and a proposed-partition coverage proof.
    """

    proposed_returns = tuple(proposed_returns or ())
    if not proposed_returns:
        return SummaryReturnAcceptanceResult((), (), ("summary_return_candidate_invalid:no_proposed_returns",), False)
    proposed_summary_returns = tuple(
        ret for ret in proposed_returns if _return_has_summary_provenance(ret)
    )
    active_preconditions = _active_preconditions(analysis)
    exact_returns = tuple(
        ret
        for ret in (getattr(analysis, "returns", ()) or ())
        if _return_is_exact_seed(ret)
        or _return_is_disjoint_resolved_phi_expansion_seed(
            ret,
            proposed_summary_returns,
            active_preconditions,
        )
    )
    exact_return_keys = {_return_info_identity_key(ret) for ret in exact_returns}
    proposed_exact_returns = tuple(
        ret
        for ret in proposed_returns
        if _return_info_identity_key(ret) not in exact_return_keys
        and (
            _return_is_exact_seed(ret)
            or _return_is_disjoint_resolved_phi_expansion_seed(
                ret,
                proposed_summary_returns,
                active_preconditions,
            )
        )
    )
    if proposed_exact_returns:
        exact_returns = tuple(exact_returns) + proposed_exact_returns

    exact_keys = {_return_info_identity_key(ret) for ret in exact_returns}
    candidates: List[SummaryReturnCandidate] = []
    candidate_indices: set[int] = set()
    for index, ret in enumerate(proposed_returns):
        if _return_info_identity_key(ret) in exact_keys:
            continue
        marker = getattr(ret, "retained_exact_return_ref", None)
        if marker is not None and any(
            _retained_exact_marker_matches_return(marker, exact_ret)
            for exact_ret in exact_returns
        ):
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

    superseded_exact_keys = _superseded_exact_return_keys_from_candidates(
        valid_candidates.values(),
        analysis,
        enable_completed_recovery_proofs=enable_completed_recovery_proofs,
    )
    effective_exact_returns = tuple(
        ret
        for ret in exact_returns
        if not _return_info_is_superseded_by_keys(ret, superseded_exact_keys)
    )

    proposed_partition = tuple(effective_exact_returns) + tuple(
        _candidate_return_for_partition(valid_candidates[index])
        for index in sorted(valid_candidates)
    )

    overlap_query_receipts: List[RecurrenceSMTQueryReceipt] = []
    coverage_query_receipts: List[RecurrenceSMTQueryReceipt] = []
    overlap_blockers = _check_candidate_overlaps(
        analysis,
        valid_candidates.values(),
        effective_exact_returns,
        enable_completed_recovery_proofs=enable_completed_recovery_proofs,
        query_receipts=overlap_query_receipts if require_smt_receipts else None,
    )
    blockers.extend(overlap_blockers)

    coverage_complete = False
    if not overlap_blockers:
        coverage_complete = _return_partition_covers_active_precondition(
            proposed_partition,
            _active_preconditions(analysis),
            parameters=getattr(analysis, "parameters", None),
            query_receipts=coverage_query_receipts if require_smt_receipts else None,
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
        return SummaryReturnAcceptanceResult(
            (), tuple(candidates), unique_blockers, coverage_complete,
            tuple(overlap_query_receipts), tuple(coverage_query_receipts),
        )

    accepted: List[ReturnInfo] = []
    accepted.extend(effective_exact_returns)
    for index in sorted(valid_candidates):
        candidate = valid_candidates[index]
        candidate.acceptance_status = "accepted"
        candidate.eq_eligible = True
        accepted_return = _accepted_candidate_return(candidate)
        candidate.return_info = accepted_return
        accepted.append(accepted_return)

    if require_smt_receipts and (
        not overlap_query_receipts or len(coverage_query_receipts) != 1
    ):
        return SummaryReturnAcceptanceResult(
            (), tuple(candidates),
            ("summary_proof_receipt_incomplete:required_smt_receipt_missing",),
            False, tuple(overlap_query_receipts), tuple(coverage_query_receipts),
        )
    return SummaryReturnAcceptanceResult(
        tuple(accepted), tuple(candidates), (), True,
        tuple(overlap_query_receipts), tuple(coverage_query_receipts),
    )


def _retained_exact_marker_matches_return(
    marker: Any,
    exact_return: ReturnInfo,
) -> bool:
    if not (
        isinstance(marker, tuple)
        and len(marker) == 3
        and marker[0] == "retained_exact_return_v1"
    ):
        return False
    try:
        condition_key = tuple(
            ImmutableRecurrenceCondition.from_condition(condition).stable_key()
            for condition in tuple(exact_return.conditions or ())
        )
        value_key = ImmutableRecurrenceExpression.from_expression(
            exact_return.value
        ).stable_key()
    except (TypeError, ValueError):
        return False
    expected_identity = (
        "return_info",
        exact_return.address,
        exact_return.pcode_identity,
        exact_return.pcode_order,
        exact_return.pcode_time,
        exact_return.pcode_op_ref.stable_key()
        if callable(getattr(exact_return.pcode_op_ref, "stable_key", None))
        else None,
        condition_key,
        value_key,
    )
    expected_payload = (condition_key, value_key, "exact")
    return tuple(marker[1]) == expected_identity and marker[2] == expected_payload


def attach_quarantined_recurrence_proposal(
    analysis: FunctionReturnAnalysis,
    *,
    proposed_returns: Sequence[ReturnInfo],
    summary_note: str,
) -> Optional[QuarantinedRecurrenceProposal]:
    """Attach an immutable proof-free proposal without changing normal returns."""

    candidates = tuple(
        build_summary_return_candidate(
            analysis,
            ret,
            summary_note=summary_note,
            candidate_index=index,
        )
        for index, ret in enumerate(tuple(proposed_returns or ()))
    )
    if not candidates:
        return None
    for candidate in candidates:
        candidate.acceptance_status = "proposed"
        candidate.eq_eligible = False
        candidate.validation_blockers = ()

    retained_markers = tuple(
        marker
        for candidate in candidates
        for marker in (getattr(candidate.return_info, "retained_exact_return_ref", None),)
        if isinstance(marker, tuple)
        and len(marker) == 3
        and marker[0] == "retained_exact_return_v1"
    )
    retained_candidate_ids = {
        candidate.candidate_id
        for candidate in candidates
        if getattr(candidate.return_info, "retained_exact_return_ref", None)
        in retained_markers
    }
    proposal_candidates = tuple(
        candidate
        for candidate in candidates
        if candidate.candidate_id not in retained_candidate_ids
    )
    if not proposal_candidates:
        return None
    retained_refs = tuple(
        RetainedExactReturnRef(
            tuple(marker[1]),
            RecurrenceDigestCodec.digest("retained_exact_return_payload_v1", marker[2]),
        )
        for marker in retained_markers
    )
    retained_refs = tuple(sorted(
        retained_refs,
        key=lambda item: RecurrenceDigestCodec.canonical_bytes(
            "retained_exact_return_sort_v1", item.stable_key()
        ),
    ))
    proposal_candidates = tuple(sorted(
        proposal_candidates,
        key=lambda candidate: RecurrenceDigestCodec.canonical_bytes(
            "recurrence_candidate_sort_v1",
            (
                candidate.guard_structural_key,
                candidate.value_structural_key,
                candidate.transition_evidence_key,
                candidate.effect_region_key,
            ),
        ),
    ))
    seed_core = RecurrenceSeedCore(
        analysis.outcome_function_identity(),
        _active_precondition_key(analysis),
        retained_refs,
        tuple(
            (
                candidate.effect_region_key,
                candidate.memory_read_set_key,
                candidate.memory_write_set_key,
                candidate.call_effect_key,
                candidate.ub_assumption_key,
            )
            for candidate in proposal_candidates
        ),
    )
    proposal = QuarantinedRecurrenceProposal(
        seed_core.digest,
        str(summary_note or "structural_summary"),
        tuple(
            QuarantinedRecurrenceReturn(
                tuple(
                    ImmutableRecurrenceCondition.from_condition(condition)
                    for condition in candidate.return_info.conditions
                ),
                ImmutableRecurrenceExpression.from_expression(candidate.return_info.value),
                tuple(candidate.candidate_id),
                tuple(candidate.transition_evidence_key or ()),
            )
            for candidate in proposal_candidates
        ),
        retained_refs,
    )
    proposals = tuple(getattr(analysis, "quarantined_recurrence_proposals", ()) or ())
    if all(item.digest != proposal.digest for item in proposals):
        analysis.quarantined_recurrence_proposals = proposals + (proposal,)
    prior_candidates = tuple(getattr(analysis, "summary_return_candidates", ()) or ())
    known_ids = {candidate.candidate_id for candidate in prior_candidates}
    analysis.summary_return_candidates = prior_candidates + tuple(
        candidate for candidate in candidates if candidate.candidate_id not in known_ids
    )
    note = f"recurrence_proposal_quarantined:{proposal.digest}"
    if note not in analysis.analysis_notes:
        analysis.analysis_notes.append(note)
    return proposal


def summary_return_acceptance_proof_id_from_evidence(
    evidence: Any,
) -> Optional[Tuple[Any, ...]]:
    if not isinstance(evidence, Mapping):
        return None
    if str(evidence.get("status") or "") != "complete":
        return None
    if str(evidence.get("proof_stage") or "") != "summary_return_acceptance":
        return None
    if str(evidence.get("evidence_kind") or "") != "summary_return_candidate_acceptance":
        return None
    object_target_key = evidence.get("object_target_key")
    proof_id = evidence.get("proof_obligation_id")
    if not _summary_return_acceptance_target_key_is_strong(object_target_key):
        return None
    if not _summary_return_acceptance_proof_id_matches_target(proof_id, object_target_key):
        return None
    proof_content = evidence.get("proof_content")
    if not _summary_return_acceptance_proof_content_matches_target(
        proof_content,
        object_target_key,
    ):
        return None
    return proof_id


def _summary_return_acceptance_target_key_is_strong(value: Any) -> bool:
    if not isinstance(value, tuple) or len(value) != 7:
        return False
    if value[0] != "summary_return_acceptance_target":
        return False
    if _key_contains_forbidden_identity(value):
        return False
    accepted_partition_key = value[3]
    candidate_ids = value[4]
    transition_keys = value[5]
    if not isinstance(accepted_partition_key, tuple) or not accepted_partition_key:
        return False
    if not isinstance(candidate_ids, tuple) or not candidate_ids:
        return False
    if not isinstance(transition_keys, tuple) or not transition_keys:
        return False
    return True


def _summary_return_acceptance_proof_id_matches_target(
    proof_id: Any,
    object_target_key: Tuple[Any, ...],
) -> bool:
    return (
        isinstance(proof_id, tuple)
        and len(proof_id) == 3
        and proof_id[0] == "proof_obligation_id"
        and proof_id[1] == "summary_return_acceptance"
        and proof_id[2] == object_target_key
    )


def _summary_return_acceptance_proof_content_matches_target(
    proof_content: Any,
    object_target_key: Tuple[Any, ...],
) -> bool:
    if not isinstance(proof_content, Mapping):
        return False
    if proof_content.get("object_target_key") != object_target_key:
        return False
    expected = {
        "accepted_partition_key": object_target_key[3],
        "candidate_ids": object_target_key[4],
        "transition_evidence_keys": object_target_key[5],
        "candidate_validation": "proved",
        "overlap_proof": "proved",
        "candidate_partition_coverage": "proved",
        "final_pairwise_coverage": "not_claimed",
    }
    for key, expected_value in expected.items():
        if proof_content.get(key) != expected_value:
            return False
    return str(proof_content.get("status") or "") in {"complete", "completed", "proven"}


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
        guard_key,
        value_key,
        _summary_transition_evidence_key(ret),
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
    try:
        return _loop_summary_structural_key(ret) is not None
    except RecursionError:
        return False


def _return_is_exact_seed(ret: ReturnInfo) -> bool:
    return_kind = str(getattr(ret, "return_kind", "exact") or "exact")
    if return_kind != "exact":
        return False
    if _expression_contains_unresolved_value(getattr(ret, "value", None)):
        return False
    if _return_has_summary_provenance(ret):
        return False
    return True


def _return_is_disjoint_resolved_phi_expansion_seed(
    ret: ReturnInfo,
    proposed_summary_returns: Sequence[ReturnInfo],
    active_preconditions: Sequence[Condition],
) -> bool:
    if str(getattr(ret, "return_kind", "exact") or "exact") == "summary_derived":
        return False
    if _expression_contains_unresolved_value(getattr(ret, "value", None)):
        return False
    if _return_has_summary_provenance(ret):
        return False
    for summary_return in proposed_summary_returns or ():
        overlap_conditions = (
            list(getattr(ret, "conditions", None) or [])
            + list(getattr(summary_return, "conditions", None) or [])
            + list(active_preconditions or ())
        )
        if _conditions_unsat(overlap_conditions) is not True:
            return False
    return True


def _expression_contains_unresolved_value(
    expr: Optional[Expression],
    _active_stack: Optional[set[int]] = None,
) -> bool:
    if expr is None:
        return True
    active_stack = _active_stack if _active_stack is not None else set()
    expr_id = id(expr)
    if expr_id in active_stack:
        return True
    active_stack.add(expr_id)
    try:
        return _expression_contains_unresolved_value_inner(expr, active_stack)
    finally:
        active_stack.discard(expr_id)


def _expression_contains_unresolved_value_inner(
    expr: Expression,
    active_stack: set[int],
) -> bool:
    expr_type = getattr(expr, "expr_type", None)
    if expr_type == ExpressionType.UNKNOWN:
        return True
    if expr_type == ExpressionType.CALL and _call_expression_is_unresolved(expr):
        return True
    for operand in getattr(expr, "operands", ()) or ():
        if _expression_contains_unresolved_value(operand, active_stack):
            return True
    if expr_type == ExpressionType.PHI:
        for cond, value in getattr(expr, "value", ()) or ():
            cond_expr = getattr(cond, "expression", None) if cond is not None else None
            if cond_expr is not None and _expression_contains_unresolved_value(cond_expr, active_stack):
                return True
            if _expression_contains_unresolved_value(value, active_stack):
                return True
    return False


def _call_expression_is_unresolved(expr: Expression) -> bool:
    runtime_ref = getattr(expr, "runtime_ref", None)
    if runtime_ref is None:
        return True
    if isinstance(runtime_ref, (UnknownValueRef, DeferredCallRef)):
        return True
    if isinstance(runtime_ref, CallTargetRef):
        return not _call_target_ref_is_resolved(runtime_ref)
    unresolved = _call_resolution_flag(runtime_ref, "is_unresolved_call")
    if unresolved is True:
        return True
    resolved = _call_resolution_flag(runtime_ref, "is_resolved_call")
    if resolved is True and _runtime_ref_has_stable_call_identity(runtime_ref):
        return False
    return True


def _call_target_ref_is_resolved(ref: CallTargetRef) -> bool:
    if ref.is_unknown():
        return False
    if ref.is_code_address():
        return getattr(ref, "address_offset", None) is not None
    if ref.is_function():
        if getattr(ref, "entry_offset", None) is not None:
            return True
        if getattr(ref, "is_external", None) is True:
            return bool(getattr(ref, "function_name", None) and getattr(ref, "library_name", None))
        return False
    return False


def _runtime_ref_has_stable_call_identity(runtime_ref: Any) -> bool:
    analysis_key = getattr(runtime_ref, "analysis_key", None)
    if callable(analysis_key):
        try:
            key = analysis_key()
        except (AttributeError, TypeError, ValueError, RecursionError):
            return False
        return _runtime_ref_key_is_stable_call_identity(key)

    stable_key = getattr(runtime_ref, "stable_key", None)
    if not callable(stable_key):
        return False
    try:
        key = stable_key()
    except (AttributeError, TypeError, ValueError, RecursionError):
        return False
    return _runtime_ref_key_is_stable_call_identity(key)


def _runtime_ref_key_is_stable_call_identity(key: Any) -> bool:
    if not isinstance(key, tuple) or not key:
        return False
    return not key_contains_placeholder(key)


def _call_resolution_flag(runtime_ref: Any, name: str) -> Optional[bool]:
    marker = getattr(runtime_ref, name, None)
    if marker is None:
        return None
    try:
        value = marker() if callable(marker) else marker
    except (AttributeError, TypeError, ValueError, RecursionError):
        return None
    if isinstance(value, bool):
        return value
    return None


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
    elif _return_region_summary_proof_ref_is_strong(
        candidate.transition_evidence_key,
        analysis,
        enable_completed_recovery_proofs=enable_completed_recovery_proofs,
    ):
        pass
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
    if (
        not _return_region_summary_proof_ref_is_strong(
            candidate.transition_evidence_key,
            analysis,
            enable_completed_recovery_proofs=enable_completed_recovery_proofs,
        )
        and _key_contains_incomplete_summary_metadata(candidate.loop_summary_structural_key)
    ):
        blockers.append("summary_effect_unmodeled:side_effect_provenance_incomplete")
    if _key_contains_incomplete_summary_metadata(candidate.effect_region_key):
        blockers.append("summary_effect_unmodeled:effect_region_incomplete")
    if _return_info_contains_phi_circular(ret):
        blockers.append("phi_circular_replacement_unproven:replacement_obligation_missing")
    if not _return_storage_width_key(ret):
        blockers.append("summary_return_candidate_invalid:return_width_missing")
    if _memory_read_unmodeled(candidate.memory_read_set_key):
        blockers.append("summary_effect_unmodeled:memory_read_unmodeled")
    effect_blocker = _effect_eligibility_blocker(
        analysis, candidate.transition_evidence_key
    )
    if effect_blocker is not None:
        blockers.append(effect_blocker)
    return tuple(dict.fromkeys(blockers))


def _check_candidate_overlaps(
    analysis: FunctionReturnAnalysis,
    candidates: Iterable[SummaryReturnCandidate],
    exact_returns: Sequence[ReturnInfo],
    *,
    enable_completed_recovery_proofs: bool,
    query_receipts: Optional[List[RecurrenceSMTQueryReceipt]] = None,
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
                    analysis=analysis,
                    enable_completed_recovery_proofs=enable_completed_recovery_proofs,
                    query_receipts=query_receipts,
                )
            )
    for left_index, left_candidate in enumerate(candidate_list):
        for right_candidate in candidate_list[left_index + 1:]:
            blockers.extend(
                _check_return_overlap_value_equality(
                    left_candidate.return_info,
                    right_candidate.return_info,
                    active_preconditions,
                    analysis=analysis,
                    enable_completed_recovery_proofs=enable_completed_recovery_proofs,
                    query_receipts=query_receipts,
                )
            )
    return tuple(dict.fromkeys(blockers))


def _check_return_overlap_value_equality(
    left: ReturnInfo,
    right: ReturnInfo,
    active_preconditions: Sequence[Condition],
    *,
    analysis: FunctionReturnAnalysis,
    enable_completed_recovery_proofs: bool,
    query_receipts: Optional[List[RecurrenceSMTQueryReceipt]] = None,
) -> Tuple[str, ...]:
    if _return_region_summary_overlap_is_proved_by_completed_evidence(
        left,
        right,
        analysis,
        enable_completed_recovery_proofs=enable_completed_recovery_proofs,
    ):
        return ()
    if _readonly_reduction_exact_overlap_is_proved(
        left,
        right,
        active_preconditions,
        analysis,
    ):
        return ()
    parameters = getattr(analysis, "parameters", None)
    overlap_conditions = (
        list(_canonicalize_conditions_for_analysis_parameters(left.conditions or [], parameters))
        + list(_canonicalize_conditions_for_analysis_parameters(right.conditions or [], parameters))
        + list(_canonicalize_conditions_for_analysis_parameters(active_preconditions or [], parameters))
    )
    comparison_id = RecurrenceDigestCodec.digest(
        "recurrence_overlap_comparison_v1",
        (_return_info_identity_key(left), _return_info_identity_key(right)),
    )
    overlap_surface = (
        "overlap_query_surface_v1",
        comparison_id,
        _width_sort_identity(getattr(left, "value", None)),
        _width_sort_identity(getattr(right, "value", None)),
        tuple(
            ImmutableRecurrenceCondition.from_condition(condition).stable_key()
            for condition in _canonicalize_conditions_for_analysis_parameters(
                active_preconditions or (), parameters
            )
        ),
    )
    overlap_unsat = _conditions_unsat(
        overlap_conditions,
        query_role="overlap_feasibility" if query_receipts is not None else None,
        width_sort_precondition_key=overlap_surface,
        query_receipts=query_receipts,
    )
    if overlap_unsat is True:
        return ()
    if overlap_unsat is None:
        return ("summary_return_overlap_unproven:overlap_feasibility_unknown",)
    compatibility_blockers = _return_merge_compatibility_blockers(left, right)
    if compatibility_blockers:
        return compatibility_blockers
    if query_receipts is None and _expression_key(left.value) == _expression_key(right.value):
        return ()
    if query_receipts is None and effect_summary._expressions_equivalent_under_conditions(
        left.value,
        right.value,
        overlap_conditions,
        getattr(analysis, "parameters", None) or (),
    ):
        return ()
    inequality = _value_inequality_condition(left, right)
    if inequality is None:
        return ("summary_return_overlap_unproven:value_comparison_unavailable",)
    equality_obligation = list(overlap_conditions) + [inequality]
    equality_unsat = _conditions_unsat(
        equality_obligation,
        query_role="overlap_value_inequality" if query_receipts is not None else None,
        width_sort_precondition_key=overlap_surface,
        query_receipts=query_receipts,
    )
    if equality_unsat is not True:
        return ("summary_return_overlap_unproven:value_equality_not_proved",)
    return ()


def _return_region_summary_overlap_is_proved_by_completed_evidence(
    left: ReturnInfo,
    right: ReturnInfo,
    analysis: FunctionReturnAnalysis,
    *,
    enable_completed_recovery_proofs: bool,
) -> bool:
    for summary_ret, exact_ret in ((left, right), (right, left)):
        if str(getattr(summary_ret, "return_kind", "exact") or "exact") != "summary_derived":
            continue
        proof_ref = getattr(summary_ret, "summary_transition_evidence_key", None)
        if not _return_region_summary_proof_ref_is_strong(
            proof_ref,
            analysis,
            enable_completed_recovery_proofs=enable_completed_recovery_proofs,
        ):
            continue
        if _return_region_summary_proof_witnesses_include_return(
            proof_ref,
            exact_ret,
            analysis,
        ):
            return True
        if not isinstance(proof_ref, tuple) or len(proof_ref) != 3:
            continue
        superseded_keys = _return_region_summary_superseded_return_keys_from_target(proof_ref[2])
        if _return_info_is_superseded_by_keys(exact_ret, set(superseded_keys)):
            return True
    return False


def _return_region_summary_proof_witnesses_include_return(
    proof_ref: Any,
    exact_ret: ReturnInfo,
    analysis: FunctionReturnAnalysis,
) -> bool:
    if not isinstance(proof_ref, tuple) or len(proof_ref) != 3:
        return False
    proof_id = proof_ref[1]
    for evidence in getattr(analysis, "completed_recovery_proof_evidence", ()) or ():
        if not isinstance(evidence, Mapping):
            continue
        if evidence.get("proof_obligation_id") != proof_id:
            continue
        proof_content = evidence.get("proof_content") or {}
        if not isinstance(proof_content, Mapping):
            return False
        witnesses_key = proof_content.get("exact_witnesses_key")
        return _exact_witnesses_key_contains_return(witnesses_key, exact_ret)
    return False


def _superseded_exact_return_keys_from_candidates(
    candidates: Iterable[SummaryReturnCandidate],
    analysis: FunctionReturnAnalysis,
    *,
    enable_completed_recovery_proofs: bool,
) -> set[Tuple[Any, ...]]:
    superseded: set[Tuple[Any, ...]] = set()
    for candidate in candidates:
        proof_ref = getattr(candidate.return_info, "summary_transition_evidence_key", None)
        if not _return_region_summary_proof_ref_is_strong(
            proof_ref,
            analysis,
            enable_completed_recovery_proofs=enable_completed_recovery_proofs,
        ):
            continue
        if not isinstance(proof_ref, tuple) or len(proof_ref) != 3:
            continue
        for key in _return_region_summary_superseded_return_keys_from_target(proof_ref[2]):
            superseded.add(key)
    return superseded


def _exact_witnesses_key_contains_return(
    witnesses_key: Any,
    exact_ret: ReturnInfo,
) -> bool:
    if not isinstance(witnesses_key, tuple) or len(witnesses_key) != 2:
        return False
    if witnesses_key[0] != "exact_return_witnesses":
        return False
    target = (
        ConditionNormalizer.conditions_signature(tuple(getattr(exact_ret, "conditions", None) or ())),
        ConditionNormalizer.expression_signature(getattr(exact_ret, "value", None)),
        getattr(exact_ret, "pcode_identity", None),
        getattr(exact_ret, "branch_index", None),
    )
    for entry in witnesses_key[1] or ():
        if not isinstance(entry, tuple) or len(entry) != 5:
            continue
        if entry[0] != "exact_return_value_witness":
            continue
        if entry[4] == getattr(exact_ret, "branch_index", None):
            return True
        if tuple(entry[1:]) == target:
            return True
    return False


def _return_partition_covers_active_precondition(
    returns: Sequence[ReturnInfo],
    active_preconditions: Sequence[Condition] = (),
    *,
    parameters: Optional[Sequence[Dict[str, Any]]] = None,
    query_receipts: Optional[List[RecurrenceSMTQueryReceipt]] = None,
) -> bool:
    conditions_by_return = [
        list(_canonicalize_conditions_for_analysis_parameters(ret.conditions or [], parameters))
        for ret in returns or ()
    ]
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
        canonical_singleton_conditions = _full_width_mask_singleton_canonical_conditions(conditions)
        if canonical_singleton_conditions is not None:
            canonical_combined = Condition.combine_and(canonical_singleton_conditions)
            if canonical_combined is not None:
                region_exprs.append(_condition_as_expression(canonical_combined))
    if has_unconditional:
        return True
    if not region_exprs:
        return False
    miss_conditions = list(_canonicalize_conditions_for_analysis_parameters(active_preconditions or [], parameters))
    for conditions in conditions_by_return:
        combined = Condition.combine_and(conditions)
        if combined is None:
            return False
        miss_conditions.append(Condition(_condition_as_expression(combined), True))
    coverage_surface = (
        "coverage_query_surface_v1",
        "active_partition",
        tuple(_width_sort_identity(getattr(ret, "value", None)) for ret in returns or ()),
        tuple(
            ImmutableRecurrenceCondition.from_condition(condition).stable_key()
            for condition in _canonicalize_conditions_for_analysis_parameters(
                active_preconditions or (), parameters
            )
        ),
    )
    miss_unsat = _conditions_unsat(
        miss_conditions,
        query_role="partition_coverage_miss" if query_receipts is not None else None,
        width_sort_precondition_key=coverage_surface,
        query_receipts=query_receipts,
    )
    return miss_unsat is True


def _full_width_mask_singleton_canonical_conditions(
    conditions: Sequence[Condition],
) -> Optional[List[Condition]]:
    rewritten: List[Condition] = []
    changed = False
    for condition in conditions or ():
        replacement = _full_width_mask_singleton_condition(condition)
        if replacement is None:
            rewritten.append(condition)
            continue
        rewritten.append(replacement)
        changed = True
    return rewritten if changed else None


def _full_width_mask_singleton_condition(condition: Condition) -> Optional[Condition]:
    expr = getattr(condition, "expression", None)
    if (
        getattr(expr, "expr_type", None) != ExpressionType.BINARY_OP
        or len(getattr(expr, "operands", ()) or ()) != 2
    ):
        return None
    operator = getattr(expr, "operator", None)
    if bool(getattr(condition, "negated", False)):
        if operator != "INT_NOTEQUAL":
            return None
    elif operator != "INT_EQUAL":
        return None
    left, right = expr.operands
    if (
        getattr(left, "expr_type", None) != ExpressionType.BINARY_OP
        or getattr(left, "operator", None) != "INT_SUB"
        or len(getattr(left, "operands", ()) or ()) != 2
    ):
        if (
            getattr(right, "expr_type", None) != ExpressionType.BINARY_OP
            or getattr(right, "operator", None) != "INT_SUB"
            or len(getattr(right, "operands", ()) or ()) != 2
        ):
            return None
        if _raw_constant_value(left) != 0:
            return None
        left = right
    elif _raw_constant_value(right) != 0:
        return None
    masked, target = left.operands
    target_value = _raw_constant_value(target)
    if target_value is None:
        return None
    if (
        getattr(masked, "expr_type", None) != ExpressionType.BINARY_OP
        or getattr(masked, "operator", None) != "INT_AND"
        or len(getattr(masked, "operands", ()) or ()) != 2
    ):
        return None
    first, second = masked.operands
    first_const = _raw_constant_value(first)
    second_const = _raw_constant_value(second)
    if first_const is not None and getattr(second, "expr_type", None) == ExpressionType.PARAMETER:
        mask = first
        source = second
        mask_value = first_const
    elif second_const is not None and getattr(first, "expr_type", None) == ExpressionType.PARAMETER:
        source = first
        mask = second
        mask_value = second_const
    else:
        return None
    if getattr(source, "expr_type", None) != ExpressionType.PARAMETER or mask_value is None:
        return None
    source_bits = _expr_width_bits(source)
    if source_bits <= 0:
        return None
    if int(mask_value) != (1 << int(source_bits)) - 1:
        return None
    return Condition(
        Expression.binary_op(
            "INT_EQUAL",
            source,
            Expression.constant(int(target_value), size=max(1, int(source_bits) // 8)),
        ),
        False,
    )


def _canonicalize_conditions_for_analysis_parameters(
    conditions: Sequence[Condition],
    parameters: Optional[Sequence[Dict[str, Any]]],
) -> Tuple[Condition, ...]:
    if not parameters:
        return tuple(conditions or ())
    by_index: Dict[int, Dict[str, Any]] = {}
    by_name = _unique_parameters_by_name(parameters)
    for param in parameters or ():
        if not isinstance(param, dict):
            continue
        try:
            by_index[int(param.get("index"))] = param
        except (TypeError, ValueError):
            pass
    if not by_index and not by_name:
        return tuple(conditions or ())
    return tuple(
        Condition(
            _canonicalize_expression_parameters_for_analysis(
                condition.expression,
                by_index=by_index,
                by_name=by_name,
            ),
            bool(getattr(condition, "negated", False)),
        )
        for condition in conditions or ()
        if condition is not None
    )


def _unique_parameters_by_name(
    parameters: Optional[Sequence[Dict[str, Any]]],
) -> Dict[str, Dict[str, Any]]:
    by_name: Dict[str, Dict[str, Any]] = {}
    name_counts: Dict[str, int] = {}
    for param in parameters or ():
        if not isinstance(param, dict):
            continue
        name = str(param.get("name") or "")
        if not name:
            continue
        name_counts[name] = name_counts.get(name, 0) + 1
        by_name.setdefault(name, param)
    return {
        name: param
        for name, param in by_name.items()
        if name_counts.get(name, 0) == 1
    }


def _canonicalize_expression_parameters_for_analysis(
    expr: Expression,
    *,
    by_index: Dict[int, Dict[str, Any]],
    by_name: Dict[str, Dict[str, Any]],
) -> Expression:
    if getattr(expr, "expr_type", None) == ExpressionType.PARAMETER:
        descriptor = None
        try:
            descriptor = by_index.get(int(getattr(expr, "value", -1)))
        except (TypeError, ValueError):
            descriptor = None
        if descriptor is None:
            descriptor = by_name.get(str(getattr(expr, "name", "") or ""))
        if descriptor is not None:
            return Expression.parameter(
                str(descriptor.get("name") or getattr(expr, "name", "") or "param"),
                index=int(descriptor.get("index", getattr(expr, "value", -1)) or 0),
                data_type=descriptor.get("data_type"),
                data_type_obj=descriptor.get("data_type_obj"),
                size=int(descriptor.get("size", getattr(expr, "size", 4)) or 4),
                storage_info=descriptor.get("storage_info", descriptor.get("storage")),
            )
    operands = [
        _canonicalize_expression_parameters_for_analysis(
            operand,
            by_index=by_index,
            by_name=by_name,
        )
        for operand in (getattr(expr, "operands", None) or ())
    ]
    return Expression(
        getattr(expr, "expr_type", None),
        value=getattr(expr, "value", None),
        operator=getattr(expr, "operator", None),
        operands=operands,
        size=int(getattr(expr, "size", 0) or 0),
        name=getattr(expr, "name", None),
        data_type=getattr(expr, "data_type", None),
        data_type_obj=getattr(expr, "data_type_obj", None),
        storage_info=getattr(expr, "storage_info", None),
        read_order_key=getattr(expr, "read_order_key", None),
        runtime_ref=getattr(expr, "runtime_ref", None),
        opcode=getattr(expr, "opcode", None),
        call_argument_width_evidence=getattr(expr, "call_argument_width_evidence", None),
    )


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


def _width_sort_identity(expression: Optional[Expression]) -> Tuple[Any, ...]:
    immutable = ImmutableRecurrenceExpression.from_expression(expression)
    return (
        "width_sort_v1",
        int(immutable.size),
        "bitvec" if immutable.sort == "bitvector" else str(immutable.sort),
        "neutral" if immutable.signedness == "signless" else str(immutable.signedness),
    )


def _conditions_unsat(
    conditions: Sequence[Condition],
    *,
    query_role: Optional[str] = None,
    width_sort_precondition_key: Tuple[Any, ...] = (),
    query_receipts: Optional[List[RecurrenceSMTQueryReceipt]] = None,
) -> Optional[bool]:
    condition_list = [condition for condition in conditions or () if condition is not None]
    if not condition_list:
        return False
    try:
        solver_unsat = ConditionSMTOracle.conjunction_is_unsat(condition_list)
    except Exception:
        solver_unsat = None
    if solver_unsat is not None:
        if query_role is not None and query_receipts is not None:
            normalized_keys = tuple(
                ImmutableRecurrenceCondition.from_condition(condition).stable_key()
                for condition in condition_list
            )
            query_receipts.append(RecurrenceSMTQueryReceipt(
                query_role,
                normalized_keys,
                width_sort_precondition_key,
                "z3",
                "unsat" if solver_unsat else "sat",
            ))
        return bool(solver_unsat)
    if query_role is not None:
        return None
    if _conditions_have_direct_negated_pair(condition_list):
        return True
    try:
        if ConditionSimplifier.object_centric_is_contradiction(condition_list):
            return True
    except Exception:
        pass
    return None


def _conditions_have_direct_negated_pair(conditions: Sequence[Condition]) -> bool:
    condition_list = list(conditions or ())
    for left_index, left in enumerate(condition_list):
        for right in condition_list[left_index + 1:]:
            try:
                if left.negate().equals(right) or right.negate().equals(left):
                    return True
            except Exception:
                pass
            try:
                if ConditionNormalizer.are_equivalent(left.negate(), right) or ConditionNormalizer.are_equivalent(
                    right.negate(),
                    left,
                ):
                    return True
            except Exception:
                pass
            if _conditions_are_complementary_comparisons(left, right):
                return True
    return False


def _conditions_are_complementary_comparisons(left: Condition, right: Condition) -> bool:
    if bool(getattr(left, "negated", False)) != bool(getattr(right, "negated", False)):
        try:
            if _expression_key(getattr(left, "expression", None)) == _expression_key(
                getattr(right, "expression", None)
            ):
                return True
        except Exception:
            pass
    if bool(getattr(left, "negated", False)) or bool(getattr(right, "negated", False)):
        return False
    left_expr = getattr(left, "expression", None)
    right_expr = getattr(right, "expression", None)
    if (
        getattr(left_expr, "expr_type", None) != ExpressionType.BINARY_OP
        or getattr(right_expr, "expr_type", None) != ExpressionType.BINARY_OP
        or len(getattr(left_expr, "operands", ()) or ()) != 2
        or len(getattr(right_expr, "operands", ()) or ()) != 2
    ):
        return False
    left_op = getattr(left_expr, "operator", None)
    right_op = getattr(right_expr, "operator", None)
    left_operands = tuple(_expression_key(operand) for operand in left_expr.operands)
    right_operands = tuple(_expression_key(operand) for operand in right_expr.operands)
    if {left_op, right_op} == {"INT_EQUAL", "INT_NOTEQUAL"}:
        return left_operands == right_operands or left_operands == tuple(reversed(right_operands))
    less_complements = {
        ("INT_SLESS", "INT_SLESSEQUAL"),
        ("INT_LESS", "INT_LESSEQUAL"),
    }
    if (left_op, right_op) in less_complements:
        return left_operands == tuple(reversed(right_operands))
    if (right_op, left_op) in less_complements:
        return right_operands == tuple(reversed(left_operands))
    return False


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
    # Return overlap is discharged below with same-width bit-vector equality.
    # Declared signedness does not change that equality relation; it matters
    # only inside typed comparisons/extensions already encoded in each value.
    # Keeping a metadata-only mismatch here prevented the actual UNSAT value
    # proof from running for otherwise identical return bit patterns.
    if _memory_read_set_key(left) != _memory_read_set_key(right):
        blockers.append("summary_return_overlap_unproven:memory_read_model_mismatch")
    return tuple(dict.fromkeys(blockers))


def _readonly_reduction_exact_overlap_is_proved(
    left: ReturnInfo,
    right: ReturnInfo,
    active_preconditions: Sequence[Condition],
    analysis: FunctionReturnAnalysis,
) -> bool:
    return (
        _readonly_reduction_exact_matches_summary(left, right, active_preconditions, analysis)
        or _readonly_reduction_exact_matches_summary(right, left, active_preconditions, analysis)
    )


def _readonly_reduction_exact_matches_summary(
    exact_ret: ReturnInfo,
    summary_ret: ReturnInfo,
    active_preconditions: Sequence[Condition],
    analysis: FunctionReturnAnalysis,
) -> bool:
    summary_value = getattr(summary_ret, "value", None)
    summary_ref = getattr(summary_value, "runtime_ref", None)
    if not isinstance(summary_ref, ReadonlyReductionRef):
        return False
    accumulator_proof = getattr(summary_ref, "accumulator_proof", None)
    if accumulator_proof is None:
        return False
    if _readonly_reduction_return_region_overlap_is_proved(
        exact_ret,
        summary_ret,
        active_preconditions,
        accumulator_proof,
    ):
        return True
    exact_value = getattr(exact_ret, "value", None)
    exact_bits = int(expression_smt_bit_width(exact_value) or 0)
    if exact_bits <= 0 or exact_bits % 8 != 0:
        return False
    result_size = max(1, exact_bits // 8)
    proof_result_size = max(1, int(getattr(accumulator_proof, "result_size", 0) or 0))
    if result_size > proof_result_size:
        return False
    if _normalize_constant_bias(int(getattr(summary_ref, "constant_bias", 0) or 0), result_size) != _normalize_constant_bias(
        int(getattr(accumulator_proof, "constant_bias", 0) or 0),
        result_size,
    ):
        return False
    extracted = _extract_readonly_reduction_terms_and_bias(
        exact_value,
        getattr(analysis, "parameters", None) or (),
        getattr(accumulator_proof, "pointer_base_ref", None),
    )
    if extracted is None:
        return False
    exact_terms, exact_bias = extracted
    if _normalize_constant_bias(exact_bias, result_size) != _normalize_constant_bias(
        int(getattr(accumulator_proof, "constant_bias", 0) or 0),
        result_size,
    ):
        return False
    exact_key = tuple(term.stable_key() for term in exact_terms)
    full_terms_for_count = getattr(accumulator_proof, "full_terms_for_count_value", None)
    if not callable(full_terms_for_count):
        return False
    for count_value in range(1, _readonly_exact_count_search_bound(accumulator_proof, len(exact_terms)) + 1):
        try:
            expected_terms = full_terms_for_count(count_value)
        except (AttributeError, TypeError, ValueError):
            expected_terms = None
        if expected_terms is None:
            continue
        if exact_key != tuple(term.stable_key() for term in expected_terms):
            continue
        if _combined_return_conditions_imply_reduction_count(
            exact_ret,
            summary_ret,
            active_preconditions,
            summary_value,
            accumulator_proof,
            getattr(analysis, "parameters", None) or (),
            int(count_value),
        ):
            return True
    return False


def _readonly_reduction_return_region_overlap_is_proved(
    exact_ret: ReturnInfo,
    summary_ret: ReturnInfo,
    active_preconditions: Sequence[Condition],
    accumulator_proof: Any,
) -> bool:
    if not bool(getattr(accumulator_proof, "return_region_value_proven", False)):
        return False
    site_refs = tuple(getattr(accumulator_proof, "return_op_refs", ()) or ()) + tuple(
        getattr(accumulator_proof, "return_value_op_refs", ()) or ()
    )
    if not site_refs:
        return False
    if not any(_return_info_matches_pcode_ref(exact_ret, ref) for ref in site_refs):
        return False
    overlap_conditions = (
        list(getattr(exact_ret, "conditions", None) or ())
        + list(getattr(summary_ret, "conditions", None) or ())
        + list(active_preconditions or ())
    )
    return _conditions_unsat(overlap_conditions) is not True


def _return_info_matches_pcode_ref(ret: ReturnInfo, ref: Any) -> bool:
    ref_key_fn = getattr(ref, "stable_key", None)
    ref_key = None
    if callable(ref_key_fn):
        try:
            ref_key = ref_key_fn()
        except (AttributeError, TypeError, ValueError):
            ref_key = None
    if ref_key is not None:
        ret_ref = getattr(ret, "pcode_op_ref", None)
        ret_key_fn = getattr(ret_ref, "stable_key", None)
        if callable(ret_key_fn):
            try:
                if ret_key_fn() == ref_key:
                    return True
            except (AttributeError, TypeError, ValueError):
                pass
        for value_ref in getattr(ret, "return_value_pcode_op_refs", ()) or ():
            value_key_fn = getattr(value_ref, "stable_key", None)
            if not callable(value_key_fn):
                continue
            try:
                if value_key_fn() == ref_key:
                    return True
            except (AttributeError, TypeError, ValueError):
                continue
    ref_time = getattr(ref, "seq_time", None)
    ret_time = getattr(ret, "pcode_time", None)
    if ref_time is not None and ret_time is not None:
        try:
            if int(ref_time) == int(ret_time):
                return _return_info_address_matches_ref(ret, ref)
        except (TypeError, ValueError):
            return False
    ref_order = getattr(ref, "seq_order", None)
    ret_order = getattr(ret, "pcode_order", None)
    if ref_order is not None and ret_order is not None:
        try:
            if int(ref_order) != int(ret_order):
                return False
        except (TypeError, ValueError):
            return False
        return _return_info_address_matches_ref(ret, ref)
    return False


def _return_info_address_matches_ref(ret: ReturnInfo, ref: Any) -> bool:
    ref_address = getattr(ref, "address_offset", None)
    if ref_address is None:
        return True
    ret_address = _return_info_address_offset(ret)
    return ret_address is not None and int(ret_address) == int(ref_address)


def _return_info_address_offset(ret: ReturnInfo) -> Optional[int]:
    ret_ref = getattr(ret, "pcode_op_ref", None)
    address = getattr(ret_ref, "address_offset", None)
    if address is not None:
        try:
            return int(address)
        except (TypeError, ValueError):
            return None
    for candidate in (getattr(ret, "address", None), getattr(ret, "pcode_identity", None)):
        if not isinstance(candidate, str) or not candidate.strip():
            continue
        token = candidate.strip().split(":", 1)[0]
        try:
            return int(token, 16)
        except ValueError:
            try:
                return int(token, 0)
            except ValueError:
                continue
    return None


def _readonly_exact_count_search_bound(accumulator_proof: Any, exact_term_count: int) -> int:
    witness_counts = [
        int(getattr(witness, "exact_count", 0) or 0)
        for witness in tuple(getattr(accumulator_proof, "loop_body_witnesses", ()) or ())
    ] + [
        int(getattr(witness, "exact_count", 0) or 0)
        for witness in tuple(getattr(accumulator_proof, "exact_return_witnesses", ()) or ())
    ]
    start_index = max(0, int(getattr(accumulator_proof, "start_index", 0) or 0))
    index_step = max(1, int(getattr(accumulator_proof, "index_step", 1) or 1))
    seed_count = max(
        len(tuple(getattr(accumulator_proof, "seed_terms", ()) or ())),
        max(0, int(getattr(accumulator_proof, "seed_term_count", 0) or 0)),
    )
    term_budget = max(1, int(exact_term_count or 0) + seed_count + 1)
    return max(1, start_index + term_budget * index_step + 1, *witness_counts)


def _combined_return_conditions_imply_reduction_count(
    exact_ret: ReturnInfo,
    summary_ret: ReturnInfo,
    active_preconditions: Sequence[Condition],
    summary_value: Expression,
    accumulator_proof: Any,
    parameters: Sequence[Dict[str, Any]],
    count_value: int,
) -> bool:
    base_conditions = (
        list(getattr(exact_ret, "conditions", None) or ())
        + list(getattr(summary_ret, "conditions", None) or ())
        + list(active_preconditions or ())
    )
    for count_expr in _reduction_count_candidate_expressions(summary_value, accumulator_proof, parameters):
        if _conditions_imply_count_value(base_conditions, count_expr, count_value):
            return True
    return False


def _reduction_count_candidate_expressions(
    summary_value: Expression,
    accumulator_proof: Any,
    parameters: Sequence[Dict[str, Any]],
) -> Tuple[Expression, ...]:
    candidates: List[Expression] = []
    operands = tuple(getattr(summary_value, "operands", ()) or ())
    if len(operands) >= 2:
        candidates.append(operands[1])
    proof_count = _reduction_count_parameter_expression(parameters, accumulator_proof)
    if proof_count is not None:
        candidates.append(proof_count)
    unique: List[Expression] = []
    seen: set[Tuple[Any, ...]] = set()
    for expr in candidates:
        key = _expression_key(expr)
        if key in seen:
            continue
        seen.add(key)
        unique.append(expr)
    return tuple(unique)


def _conditions_imply_count_value(
    conditions: Sequence[Condition],
    count_expr: Expression,
    count_value: int,
) -> bool:
    if any(_condition_contains_count_storage_conflict(condition, count_expr) for condition in conditions or ()):
        return False
    count_bits = max(1, int(expression_smt_bit_width(count_expr) or 0))
    count_size = max(1, (count_bits + 7) // 8)
    not_equal = Condition(
        Expression.binary_op(
            "INT_NOTEQUAL",
            count_expr,
            Expression.constant(int(count_value), size=count_size),
        ),
        False,
    )
    if _conditions_unsat(list(conditions or ()) + [not_equal]) is True:
        return True
    return any(
        _condition_structurally_implies_count_value(condition, count_expr, count_value)
        for condition in conditions or ()
    )


def _condition_contains_count_storage_conflict(condition: Condition, count_expr: Expression) -> bool:
    return _expression_contains_count_storage_conflict(getattr(condition, "expression", None), count_expr)


def _expression_contains_count_storage_conflict(expr: Optional[Expression], count_expr: Expression) -> bool:
    if expr is None:
        return False
    if _parameter_expression_storage_conflicts_with_count(expr, count_expr):
        return True
    for operand in getattr(expr, "operands", ()) or ():
        if _expression_contains_count_storage_conflict(operand, count_expr):
            return True
    if getattr(expr, "expr_type", None) == ExpressionType.PHI:
        for condition, value in getattr(expr, "value", ()) or ():
            if _expression_contains_count_storage_conflict(getattr(condition, "expression", None), count_expr):
                return True
            if _expression_contains_count_storage_conflict(value, count_expr):
                return True
    return False


def _parameter_expression_storage_conflicts_with_count(expr: Expression, count_expr: Expression) -> bool:
    if getattr(expr, "expr_type", None) != ExpressionType.PARAMETER:
        return False
    if getattr(count_expr, "expr_type", None) != ExpressionType.PARAMETER:
        return False
    expr_storage = _expression_storage_identity_key(expr)
    count_storage = _expression_storage_identity_key(count_expr)
    if expr_storage is None or count_storage is None or expr_storage == count_storage:
        return False
    expr_index = getattr(expr, "value", None)
    count_index = getattr(count_expr, "value", None)
    try:
        if int(expr_index) >= 0 and int(count_index) >= 0 and int(expr_index) == int(count_index):
            return True
    except (TypeError, ValueError):
        pass
    expr_name = str(getattr(expr, "name", "") or "")
    count_name = str(getattr(count_expr, "name", "") or "")
    return bool(expr_name and count_name and expr_name == count_name)


def _condition_structurally_implies_count_value(
    condition: Condition,
    count_expr: Expression,
    count_value: int,
) -> bool:
    if _condition_is_count_singleton(condition, count_expr, count_value):
        return True
    canonical = _full_width_mask_singleton_condition(condition)
    if canonical is not None and _condition_is_count_singleton(canonical, count_expr, count_value):
        return True
    expr = getattr(condition, "expression", None)
    if (
        getattr(expr, "expr_type", None) != ExpressionType.BINARY_OP
        or len(getattr(expr, "operands", ()) or ()) != 2
    ):
        return False
    operator = getattr(expr, "operator", None)
    equality = operator == "INT_EQUAL" and not bool(getattr(condition, "negated", False))
    negated_notequal = operator == "INT_NOTEQUAL" and bool(getattr(condition, "negated", False))
    if not (equality or negated_notequal):
        return False
    left, right = expr.operands
    return _ptradd_index_equality_implies_count_value(left, right, count_expr, count_value) or _ptradd_index_equality_implies_count_value(
        right,
        left,
        count_expr,
        count_value,
    )


def _condition_is_count_singleton(
    condition: Condition,
    count_expr: Expression,
    count_value: int,
) -> bool:
    expr = getattr(condition, "expression", None)
    if (
        getattr(expr, "expr_type", None) != ExpressionType.BINARY_OP
        or len(getattr(expr, "operands", ()) or ()) != 2
    ):
        return False
    operator = getattr(expr, "operator", None)
    equality = operator == "INT_EQUAL" and not bool(getattr(condition, "negated", False))
    negated_notequal = operator == "INT_NOTEQUAL" and bool(getattr(condition, "negated", False))
    if not (equality or negated_notequal):
        return False
    left, right = expr.operands
    left_const = _raw_constant_value(left)
    right_const = _raw_constant_value(right)
    if right_const is not None and _expression_is_count_view(left, count_expr):
        return int(right_const) == int(count_value)
    if left_const is not None and _expression_is_count_view(right, count_expr):
        return int(left_const) == int(count_value)
    return False


def _ptradd_index_equality_implies_count_value(
    ptradd_expr: Expression,
    other_expr: Expression,
    count_expr: Expression,
    count_value: int,
) -> bool:
    ptradd_parts = _ptradd_base_index_scale(ptradd_expr)
    other_parts = _ptradd_base_index_scale(other_expr)
    if ptradd_parts is None or other_parts is None:
        return False
    base, index_expr, scale = ptradd_parts
    other_base, other_index_expr, other_scale = other_parts
    if _expression_key(base) != _expression_key(other_base):
        return False
    if scale != other_scale:
        return False
    affine = _count_affine_from_expression(index_expr, count_expr)
    other_affine = _count_affine_from_expression(other_index_expr, count_expr)
    if affine is None or other_affine is None:
        return False
    coeff, bias = affine
    other_coeff, other_bias = other_affine
    if coeff == other_coeff:
        return False
    delta_coeff = coeff - other_coeff
    delta_bias = other_bias - bias
    if delta_coeff != 1:
        return False
    return int(delta_bias) == int(count_value)


def _ptradd_base_index_scale(expr: Expression) -> Optional[Tuple[Expression, Expression, int]]:
    if (
        getattr(expr, "expr_type", None) != ExpressionType.INTRINSIC
        or str(getattr(expr, "operator", None) or getattr(expr, "name", "") or "").upper() != "PTRADD"
    ):
        return None
    operands = tuple(getattr(expr, "operands", ()) or ())
    if len(operands) != 3:
        return None
    scale = _raw_constant_value(operands[2])
    if scale is None:
        return None
    return operands[0], operands[1], int(scale)


def _count_affine_from_expression(
    expr: Expression,
    count_expr: Expression,
) -> Optional[Tuple[int, int]]:
    if _expression_is_count_view(expr, count_expr):
        return 1, 0
    if getattr(expr, "expr_type", None) == ExpressionType.CONSTANT:
        value = _raw_constant_value(expr)
        return None if value is None else (0, int(value))
    if getattr(expr, "expr_type", None) == ExpressionType.UNARY_OP and getattr(expr, "operands", None):
        operator = getattr(expr, "operator", None)
        if operator in {"INT_ZEXT", "COPY"}:
            return _count_affine_from_expression(expr.operands[0], count_expr)
        if operator == "CAST":
            operand = expr.operands[0]
            if int(getattr(expr, "size", 0) or 0) != int(getattr(operand, "size", 0) or 0):
                return None
            return _count_affine_from_expression(operand, count_expr)
        return None
    if (
        getattr(expr, "expr_type", None) != ExpressionType.BINARY_OP
        or len(getattr(expr, "operands", ()) or ()) != 2
    ):
        return None
    left = _count_affine_from_expression(expr.operands[0], count_expr)
    right = _count_affine_from_expression(expr.operands[1], count_expr)
    if getattr(expr, "operator", None) == "INT_ADD" and left is not None and right is not None:
        return left[0] + right[0], left[1] + right[1]
    if getattr(expr, "operator", None) == "INT_SUB" and left is not None and right is not None:
        return left[0] - right[0], left[1] - right[1]
    return None


def _expression_is_count_view(expr: Expression, count_expr: Expression) -> bool:
    if _parameter_expression_matches(expr, count_expr):
        return True
    if getattr(expr, "expr_type", None) == ExpressionType.UNARY_OP and getattr(expr, "operands", None):
        if getattr(expr, "operator", None) in {"INT_ZEXT", "COPY"}:
            return _expression_is_count_view(expr.operands[0], count_expr)
        if getattr(expr, "operator", None) == "CAST":
            operand = expr.operands[0]
            return int(getattr(expr, "size", 0) or 0) == int(getattr(operand, "size", 0) or 0) and _expression_is_count_view(
                operand,
                count_expr,
            )
    if (
        getattr(expr, "expr_type", None) == ExpressionType.BINARY_OP
        and getattr(expr, "operator", None) == "SUBPIECE"
        and len(getattr(expr, "operands", ()) or ()) == 2
    ):
        source, offset = expr.operands
        if _raw_constant_value(offset) == 0 and _parameter_expression_matches(source, count_expr):
            bits = _expr_width_bits(expr)
            return bits > 0 and int(bits) <= int(_expr_width_bits(source) or bits)
    if (
        getattr(expr, "expr_type", None) == ExpressionType.BINARY_OP
        and getattr(expr, "operator", None) == "INT_AND"
        and len(getattr(expr, "operands", ()) or ()) == 2
    ):
        left, right = expr.operands
        for source, mask_expr in ((left, right), (right, left)):
            mask = _raw_constant_value(mask_expr)
            if mask is None or not _expression_is_count_view(source, count_expr):
                continue
            source_bits = _expr_width_bits(source)
            if source_bits <= 0:
                continue
            if int(mask) == (1 << int(source_bits)) - 1:
                return True
    return False


def _parameter_expression_matches(left: Expression, right: Expression) -> bool:
    if getattr(left, "expr_type", None) != ExpressionType.PARAMETER:
        return False
    if getattr(right, "expr_type", None) != ExpressionType.PARAMETER:
        return False
    left_storage = _expression_storage_identity_key(left)
    right_storage = _expression_storage_identity_key(right)
    if left_storage is not None and right_storage is not None:
        return left_storage == right_storage
    left_index = getattr(left, "value", None)
    right_index = getattr(right, "value", None)
    try:
        if int(left_index) >= 0 and int(right_index) >= 0:
            return int(left_index) == int(right_index)
    except (TypeError, ValueError):
        pass
    return str(getattr(left, "name", "") or "") == str(getattr(right, "name", "") or "") and bool(
        getattr(left, "name", None)
    )


def _expression_storage_identity_key(expr: Expression) -> Optional[Tuple[Any, ...]]:
    storage = getattr(expr, "storage_info", None)
    storage_key_fn = getattr(storage, "storage_identity_key", None)
    if callable(storage_key_fn):
        try:
            storage_key = storage_key_fn()
        except (AttributeError, TypeError, ValueError):
            storage_key = None
        if storage_key is not None:
            return _normalize_parameter_storage_identity_key(tuple(storage_key))
    return None


def _reduction_count_parameter_expression(
    parameters: Sequence[Dict[str, Any]],
    accumulator_proof: Any,
) -> Optional[Expression]:
    if accumulator_proof is None:
        return None
    proof_index = getattr(accumulator_proof, "count_parameter_index", None)
    proof_storage = getattr(accumulator_proof, "count_parameter_storage_identity_key", None)
    proof_name = str(getattr(accumulator_proof, "count_parameter_name", "") or "")
    matches: List[Dict[str, Any]] = []
    for parameter in parameters or ():
        if not isinstance(parameter, dict):
            continue
        if _parameter_descriptor_matches_reduction_count(
            parameter,
            proof_index=proof_index,
            proof_storage=proof_storage,
            proof_name=proof_name,
        ):
            matches.append(parameter)
    if not matches and proof_name and proof_index is None and proof_storage is None:
        name_matches = [
            parameter
            for parameter in parameters or ()
            if isinstance(parameter, dict) and str(parameter.get("name") or "") == proof_name
        ]
        if len(name_matches) == 1:
            matches = name_matches
    if len(matches) != 1:
        return None
    descriptor = matches[0]
    try:
        index = int(descriptor.get("index", -1))
    except (TypeError, ValueError):
        index = -1
    size = max(1, int(descriptor.get("size", 0) or descriptor.get("size_bytes", 0) or 4))
    return Expression.parameter(
        str(descriptor.get("name") or proof_name or f"param_{index}"),
        index=index,
        data_type=descriptor.get("data_type") or descriptor.get("type_name"),
        size=size,
        storage_info=descriptor.get("storage_info"),
        runtime_ref=descriptor.get("runtime_ref"),
    )


def _parameter_descriptor_matches_reduction_count(
    parameter: Dict[str, Any],
    *,
    proof_index: Any,
    proof_storage: Optional[Tuple[Any, ...]],
    proof_name: str,
) -> bool:
    descriptor_index = _parameter_descriptor_index(parameter)
    descriptor_storage = _parameter_descriptor_storage_identity_key(parameter)
    descriptor_name = str(parameter.get("name") or "")
    normalized_proof_index = None
    if proof_index is not None:
        try:
            normalized_proof_index = int(proof_index)
        except (TypeError, ValueError):
            return False
        if descriptor_index != normalized_proof_index:
            return False
    if proof_storage is not None and descriptor_storage != proof_storage:
        return False
    if proof_name and descriptor_name and descriptor_name != proof_name:
        return False
    return proof_index is not None or proof_storage is not None


def _parameter_descriptor_index(parameter: Dict[str, Any]) -> Optional[int]:
    try:
        index = parameter.get("index")
        if index is not None and int(index) >= 0:
            return int(index)
    except (TypeError, ValueError):
        return None
    return None


def _parameter_descriptor_storage_identity_key(parameter: Dict[str, Any]) -> Optional[Tuple[Any, ...]]:
    storage = parameter.get("storage_info", parameter.get("storage"))
    storage_key_fn = getattr(storage, "storage_identity_key", None)
    if callable(storage_key_fn):
        try:
            storage_key = storage_key_fn()
        except (AttributeError, TypeError, ValueError):
            storage_key = None
        if storage_key is not None:
            return _normalize_parameter_storage_identity_key(tuple(storage_key))
    direct = parameter.get("storage_identity_key")
    if isinstance(direct, tuple):
        return _normalize_parameter_storage_identity_key(direct)
    return None


def _normalize_parameter_storage_identity_key(storage_key: Tuple[Any, ...]) -> Tuple[Any, ...]:
    if (
        isinstance(storage_key, tuple)
        and len(storage_key) == 2
        and storage_key[0] == "parameter_storage"
        and isinstance(storage_key[1], tuple)
    ):
        return tuple(storage_key[1])
    return tuple(storage_key)


def _extract_readonly_reduction_terms_and_bias(
    expr: Optional[Expression],
    parameters: Sequence[Dict[str, Any]],
    pointer_base_ref: Any,
) -> Optional[Tuple[Tuple[ReadonlyReductionTermRef, ...], int]]:
    if expr is None or pointer_base_ref is None:
        return None
    extracted: List[ReadonlyReductionTermRef] = []
    constant_bias = 0
    for sign, term in _flatten_readonly_add_terms(expr):
        if getattr(term, "expr_type", None) == ExpressionType.CONSTANT:
            value = _raw_constant_value(term)
            if value is None:
                return None
            constant_bias += int(sign) * int(value)
            continue
        if sign != 1:
            return None
        descriptor = _extract_readonly_reduction_term_descriptor(term, parameters, pointer_base_ref)
        if descriptor is None:
            return None
        extracted.append(descriptor)
    if not extracted:
        return None
    extracted.sort(key=lambda item: (int(item.byte_offset), int(item.access_size)))
    return tuple(extracted), int(constant_bias)


def _flatten_readonly_add_terms(expr: Expression, sign: int = 1) -> List[Tuple[int, Expression]]:
    if getattr(expr, "expr_type", None) == ExpressionType.BINARY_OP and len(getattr(expr, "operands", ()) or ()) == 2:
        if getattr(expr, "operator", None) == "INT_ADD":
            return _flatten_readonly_add_terms(expr.operands[0], sign) + _flatten_readonly_add_terms(expr.operands[1], sign)
        if getattr(expr, "operator", None) == "INT_SUB":
            return _flatten_readonly_add_terms(expr.operands[0], sign) + _flatten_readonly_add_terms(expr.operands[1], -sign)
    return [(sign, expr)]


def _extract_readonly_reduction_term_descriptor(
    expr: Optional[Expression],
    parameters: Sequence[Dict[str, Any]],
    pointer_base_ref: Any,
) -> Optional[ReadonlyReductionTermRef]:
    if expr is None:
        return None
    if getattr(expr, "expr_type", None) == ExpressionType.UNARY_OP and getattr(expr, "operands", None):
        if getattr(expr, "operator", None) == "INT_SEXT":
            return None
        if getattr(expr, "operator", None) == "CAST":
            operand = expr.operands[0]
            if int(getattr(expr, "size", 0) or 0) != int(getattr(operand, "size", 0) or 0):
                return None
            return _extract_readonly_reduction_term_descriptor(operand, parameters, pointer_base_ref)
        if getattr(expr, "operator", None) in {"INT_ZEXT", "COPY"}:
            return _extract_readonly_reduction_term_descriptor(expr.operands[0], parameters, pointer_base_ref)
    if getattr(expr, "expr_type", None) != ExpressionType.MEMORY or not getattr(expr, "operands", None):
        return None
    load_size = max(1, int(getattr(expr, "size", 0) or 0))
    location = canonicalize_location(expr.operands[0], parameters, size=load_size)
    if location is None:
        return None
    base_ref = getattr(location, "base_ref", None)
    if base_ref is None:
        return None
    base_key = getattr(base_ref, "semantic_key", lambda: None)()
    proof_base_key = getattr(pointer_base_ref, "semantic_key", lambda: None)()
    if base_key is None or proof_base_key is None or base_key != proof_base_key:
        return None
    return ReadonlyReductionTermRef(byte_offset=int(getattr(location, "offset", 0) or 0), access_size=load_size)


def _normalize_constant_bias(value: int, result_size: int) -> int:
    bits = max(1, int(result_size or 0)) * 8
    return int(value) % (1 << bits)


def _raw_constant_value(expr: Optional[Expression]) -> Optional[int]:
    if expr is None or getattr(expr, "expr_type", None) != ExpressionType.CONSTANT:
        return None
    try:
        return int(expr.value)
    except (TypeError, ValueError):
        return None


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


def _return_info_summary_identity_key(ret: ReturnInfo) -> Tuple[Any, ...]:
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


def _return_info_is_superseded_by_keys(
    ret: ReturnInfo,
    superseded_keys: set[Tuple[Any, ...]],
) -> bool:
    if not superseded_keys:
        return False
    return any(
        key in superseded_keys
        for key in (
            _return_info_identity_key(ret),
            _return_info_summary_identity_key(ret),
        )
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
    if _return_region_summary_proof_ref_is_strong(
        value,
        analysis,
        enable_completed_recovery_proofs=enable_completed_recovery_proofs,
    ):
        return True
    if _linear_self_recursion_evidence_is_strong(value, analysis):
        return True
    state_transition_evidence = _unwrap_state_transition_loop_evidence(value)
    if state_transition_evidence is not None:
        return _state_transition_loop_evidence_has_required_parts(state_transition_evidence)
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


def _state_transition_loop_evidence_has_required_parts(value: Any) -> bool:
    if not isinstance(value, tuple) or not value or value[0] != "state_transition_loop_evidence":
        return False
    fields = _tagged_tuple_fields(value[1:])
    required_markers = {
        "summary_key",
        "guard_key",
        "transition_key",
        "accumulator_init_key",
        "accumulator_delta_key",
        "transition_cases_key",
        "side_effect_profile_key",
        "replacement_obligation",
    }
    if not required_markers.issubset(fields):
        return False
    for marker in required_markers:
        item = fields[marker]
        if not isinstance(item, tuple) or len(item) != 2:
            return False
        if _key_contains_incomplete_summary_metadata(item[1]):
            return False
    return True


def _unwrap_state_transition_loop_evidence(value: Any) -> Optional[Tuple[Any, ...]]:
    if not isinstance(value, tuple) or not value:
        return None
    if value[0] == "state_transition_loop_evidence":
        return value
    for item in value:
        nested = _unwrap_state_transition_loop_evidence(item)
        if nested is not None:
            return nested
    return None


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


def _return_region_summary_proof_ref_is_strong(
    value: Any,
    analysis: FunctionReturnAnalysis,
    *,
    enable_completed_recovery_proofs: bool,
) -> bool:
    if not enable_completed_recovery_proofs:
        return False
    if not isinstance(value, tuple) or len(value) != 3:
        return False
    if value[0] != "return_region_summary_proof_ref":
        return False
    proof_obligation_id = value[1]
    object_target_key = value[2]
    if not _return_region_summary_target_key_is_strong(object_target_key):
        return False
    if not _return_region_summary_proof_id_matches_target(proof_obligation_id, object_target_key):
        return False
    return proof_obligation_id in _completed_return_region_summary_proof_ids(analysis)


def _return_region_summary_target_key_is_strong(value: Any) -> bool:
    if not isinstance(value, tuple) or len(value) not in {6, 7}:
        return False
    if value[0] != "return_region_summary_target":
        return False
    if len(value) == 7 and not _return_region_summary_superseded_target_part_is_strong(value[6]):
        return False
    if _key_contains_forbidden_identity(value):
        return False
    return True


def _return_region_summary_superseded_target_part_is_strong(value: Any) -> bool:
    if not isinstance(value, tuple) or len(value) != 2:
        return False
    if value[0] != "superseded_return_keys":
        return False
    keys = value[1]
    if not isinstance(keys, tuple):
        return False
    return all(isinstance(key, tuple) for key in keys)


def _return_region_summary_superseded_return_keys_from_target(
    object_target_key: Any,
) -> Tuple[Tuple[Any, ...], ...]:
    if not isinstance(object_target_key, tuple) or len(object_target_key) != 7:
        return ()
    superseded_part = object_target_key[6]
    if not _return_region_summary_superseded_target_part_is_strong(superseded_part):
        return ()
    return tuple(key for key in superseded_part[1] if isinstance(key, tuple))


def _completed_return_region_summary_proof_ids(
    analysis: FunctionReturnAnalysis,
) -> Tuple[Tuple[Any, ...], ...]:
    completed: List[Tuple[Any, ...]] = []
    for evidence in getattr(analysis, "completed_recovery_proof_evidence", ()) or ():
        proof_id = _return_region_summary_proof_id_from_evidence(evidence)
        if proof_id is not None:
            completed.append(proof_id)
    return tuple(completed)


def _return_region_summary_proof_id_from_evidence(evidence: Any) -> Optional[Tuple[Any, ...]]:
    if not isinstance(evidence, Mapping):
        return None
    if str(evidence.get("status") or "") != "complete":
        return None
    if str(evidence.get("proof_stage") or "") != "return_region_summary":
        return None
    if str(evidence.get("evidence_kind") or "") != "smt_value_equivalence":
        return None
    object_target_key = evidence.get("object_target_key")
    proof_id = evidence.get("proof_obligation_id")
    if not _return_region_summary_target_key_is_strong(object_target_key):
        return None
    if not _return_region_summary_proof_id_matches_target(proof_id, object_target_key):
        return None
    proof_content = evidence.get("proof_content")
    if not _return_region_summary_proof_content_matches_target(proof_content, object_target_key):
        return None
    return proof_id


def _return_region_summary_proof_id_matches_target(
    proof_id: Any,
    object_target_key: Any,
) -> bool:
    return (
        isinstance(proof_id, tuple)
        and len(proof_id) == 3
        and proof_id[0] == "proof_obligation_id"
        and proof_id[1] == "return_region_summary"
        and proof_id[2] == object_target_key
    )


def _return_region_summary_proof_content_matches_target(
    proof_content: Any,
    object_target_key: Any,
) -> bool:
    if not isinstance(proof_content, Mapping):
        return False
    if proof_content.get("object_target_key") != object_target_key:
        return False
    if str(proof_content.get("proof_status") or "") != "proved":
        return False
    if len(object_target_key) == 6:
        (
            _tag,
            summary_value_key,
            summary_conditions_key,
            exact_witnesses_key,
            coverage_key,
            source_key,
        ) = object_target_key
        superseded_keys = ()
    else:
        (
            _tag,
            summary_value_key,
            summary_conditions_key,
            exact_witnesses_key,
            coverage_key,
            source_key,
            superseded_part,
        ) = object_target_key
        if not _return_region_summary_superseded_target_part_is_strong(superseded_part):
            return False
        superseded_keys = tuple(superseded_part[1])
    expected = {
        "summary_value_key": summary_value_key,
        "summary_conditions_key": summary_conditions_key,
        "exact_witnesses_key": exact_witnesses_key,
        "coverage_key": coverage_key,
        "source_key": source_key,
    }
    for key, expected_value in expected.items():
        if proof_content.get(key) != expected_value:
            return False
    if len(object_target_key) == 7 and tuple(proof_content.get("superseded_return_keys") or ()) != superseded_keys:
        return False
    checks = tuple(proof_content.get("checks") or ())
    required = {
        ("summary_value_equivalence", "proved"),
        ("summary_side_effects", "pure"),
    }
    if not required.issubset(set(checks)):
        return False
    return ("summary_region_coverage", "proved") in set(checks)


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
    expr_evidence = _state_transition_loop_evidence_from_expression(getattr(ret, "value", None))
    if expr_evidence is not None:
        return expr_evidence
    return None


def _state_transition_loop_evidence_from_expression(expr: Any) -> Optional[Tuple[Any, ...]]:
    if expr is None:
        return None
    evidence = _state_transition_loop_evidence_from_runtime_ref(getattr(expr, "runtime_ref", None))
    if evidence is not None:
        return evidence
    for operand in getattr(expr, "operands", ()) or ():
        evidence = _state_transition_loop_evidence_from_expression(operand)
        if evidence is not None:
            return evidence
    return None


def _state_transition_loop_evidence_from_runtime_ref(runtime_ref: Any) -> Optional[Tuple[Any, ...]]:
    if runtime_ref is None or type(runtime_ref).__name__ != "StateTransitionLoopSummaryRef":
        return None
    side_effect_profile = getattr(runtime_ref, "side_effect_profile", None)
    if side_effect_profile is None:
        return None
    if getattr(side_effect_profile, "requires_effect_proof", lambda: True)():
        return None
    summary_key = _stable_key_or_none(runtime_ref)
    guard_key = _expression_key(getattr(runtime_ref, "state_guard", None))
    transition_key = _expression_key(getattr(runtime_ref, "transition_expr", None))
    transition_cases_key = _state_transition_cases_key(getattr(runtime_ref, "transition_cases", None))
    accumulator_init_key = _expression_key(getattr(runtime_ref, "accumulator_init", None))
    accumulator_delta_key = _expression_key(getattr(runtime_ref, "accumulator_delta", None))
    side_effect_key = _stable_key_or_none(side_effect_profile)
    if any(
        key is None
        for key in (
            summary_key,
            guard_key,
            transition_key,
            transition_cases_key,
            accumulator_init_key,
            accumulator_delta_key,
            side_effect_key,
        )
    ):
        return None
    return (
        "state_transition_loop_evidence",
        ("summary_key", summary_key),
        ("guard_key", guard_key),
        ("transition_key", transition_key),
        ("accumulator_init_key", accumulator_init_key),
        ("accumulator_delta_key", accumulator_delta_key),
        ("transition_cases_key", transition_cases_key),
        ("side_effect_profile_key", side_effect_key),
        ("replacement_obligation", "not_required_without_phi_circular"),
    )


def _state_transition_cases_key(cases: Any) -> Optional[Tuple[Any, ...]]:
    if not isinstance(cases, (tuple, list)) or not cases:
        return None
    entries = []
    for case in cases:
        if not isinstance(case, (tuple, list)) or len(case) != 2:
            return None
        conditions, expr = case
        condition_key = _conditions_key(tuple(conditions or ()))
        expr_key = _expression_key(expr)
        if not condition_key or not expr_key:
            return None
        entries.append(("transition_case", condition_key, expr_key))
    entries.sort(key=repr)
    return ("transition_cases", tuple(entries))


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


def _effect_eligibility_blocker(
    analysis: FunctionReturnAnalysis,
    transition_evidence_key: Optional[Tuple[Any, ...]] = None,
) -> Optional[str]:
    effect_summary = getattr(analysis, "effect_summary", None)
    if effect_summary is None:
        return "summary_effect_unmodeled:effect_summary_missing"
    if getattr(effect_summary, "effects", None):
        return "summary_effect_unmodeled:memory_write_effects_present"
    if getattr(effect_summary, "has_unsupported_call", False):
        if _linear_self_recursion_evidence_is_strong(
            transition_evidence_key, analysis
        ):
            return None
        return "summary_effect_unmodeled:unsupported_call_effect"
    incomplete = tuple(getattr(effect_summary, "incomplete_reasons", ()) or ())
    if incomplete:
        return "summary_effect_unmodeled:" + ",".join(str(reason) for reason in incomplete)
    return None


def _linear_self_recursion_evidence_is_strong(
    value: Any,
    analysis: FunctionReturnAnalysis,
) -> bool:
    if not isinstance(value, tuple) or not value:
        return False
    if value[0] != "linear_self_recursion_transition_evidence_v1":
        return False
    fields = _tagged_tuple_fields(value[1:])
    required = {
        "function", "self_call", "counter", "step", "split_bound",
        "base_affine", "addend_affine", "effect_profile",
        "termination_measure", "width", "replacement_obligation",
    }
    if not required.issubset(fields):
        return False
    if fields["step"] != ("step", -1):
        return False
    if fields["effect_profile"] != (
        "effect_profile", "single_direct_self_call_no_store"
    ):
        return False
    if fields["termination_measure"] != (
        "termination_measure", "signed_unit_decrement_to_bound"
    ):
        return False
    if not isinstance(fields["width"][1], int) or fields["width"][1] <= 0:
        return False
    function_ref = getattr(analysis, "function_ref", None)
    function_key = (
        function_ref.stable_key()
        if callable(getattr(function_ref, "stable_key", None))
        else None
    )
    if fields["function"] != ("function", function_key):
        return False
    effect_summary = getattr(analysis, "effect_summary", None)
    if effect_summary is None or tuple(getattr(effect_summary, "effects", ()) or ()):
        return False
    if any(
        str(reason) not in {
            "callee_effect_summary_missing",
            "unsupported_call_effect",
            "effect_call_argument_evidence_incomplete",
        }
        for reason in getattr(effect_summary, "incomplete_reasons", ()) or ()
    ):
        return False
    sites = tuple(getattr(effect_summary, "unsupported_call_sites", ()) or ())
    if len(sites) != 1:
        return False
    site = sites[0]
    target_ref = getattr(site, "target_ref", None)
    if not callable(getattr(target_ref, "stable_key", None)):
        return False
    if target_ref.stable_key() != function_key:
        return False
    pcode_ref = getattr(site, "pcode_op_ref", None)
    if not callable(getattr(pcode_ref, "stable_key", None)):
        return False
    if fields["self_call"] != ("self_call", pcode_ref.stable_key()):
        return False
    evidence = tuple(
        item
        for item in getattr(effect_summary, "call_argument_evidence", {}).values()
        if item is not None
    )
    return all(
        callable(getattr(getattr(item, "target_ref", None), "stable_key", None))
        and item.target_ref.stable_key() == function_key
        for item in evidence
    )


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
