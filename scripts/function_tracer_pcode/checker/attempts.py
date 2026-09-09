# -*- coding: utf-8 -*-
"""Attempt 記録と遷移理由判定のヘルパー"""

from typing import Any, Dict, List, Mapping, Optional, Tuple

from scripts.function_tracer_pcode.checker.debug_trace import (
    Attempt,
    AttemptIdentity,
    DebugTrace,
    NormalizationRuleApplication,
    PairwiseDecisiveInfo,
    ProofCompletionEvent,
    ReasonCompletionEvent,
    TransitionReason,
)
from scripts.function_tracer_pcode.checker.result import EquivalenceResult, RewriteInfo
from scripts.function_tracer_pcode.proof.cause_identity import ProofRequirementId
from scripts.function_tracer_pcode.semantics.typing.fixer import TypeFixResult
from scripts.function_tracer_pcode.checker.unknown_reason import coerce_unknown_reason_records
from scripts.function_tracer_pcode.smt import ParallelResult


def get_transition_reason(
    result: EquivalenceResult,
    retry_with_type_fix: bool,
    phase_id: Optional[str] = None,
    will_try_phase4b: bool = False
) -> str:
    """結果から phase レベルの遷移理由を返す"""
    del retry_with_type_fix
    del phase_id

    if result.is_equivalent is True:
        return TransitionReason.UNSAT.value
    if result.is_equivalent is False:
        if will_try_phase4b:
            return TransitionReason.SAT_PHASE4B.value
        return TransitionReason.SAT.value
    if result.has_critical_error():
        return TransitionReason.CRITICAL_ERROR.value
    if result.is_timeout():
        return TransitionReason.TIMEOUT.value
    return TransitionReason.UNKNOWN.value


def record_attempt(
    debug_trace: DebugTrace,
    attempt_id: int,
    retry_count: int,
    phase: str,
    stage_path: List[str],
    strategy: str,
    result: Optional[bool],
    transition_reason: str,
    type_fix_result: Optional[TypeFixResult],
    rewrite_info: Optional[RewriteInfo],
    original_function1_signature: Optional[Dict[str, Any]],
    original_function2_signature: Optional[Dict[str, Any]],
    effective_function1_signature: Optional[Dict[str, Any]],
    effective_function2_signature: Optional[Dict[str, Any]],
    function1_signature_hypotheses: Optional[List[Dict[str, Any]]],
    function2_signature_hypotheses: Optional[List[Dict[str, Any]]],
    solver_results: Optional[ParallelResult],
    final_smt: Optional[str],
    counterexample: Optional[Dict[str, Any]],
    pairwise_decisive: Optional[PairwiseDecisiveInfo],
    pairwise_debug_stats: Optional[Mapping[str, int]],
    normalization_rules: Optional[List[Any]],
    mips64_abi_constraints: Optional[Dict[str, Any]],
    elapsed_time: float,
    unknown_reasons: Optional[List[Any]] = None,
    phase_diagnostics: Optional[Mapping[str, Any]] = None,
) -> None:
    """Attempt を追加する

    ``phase_diagnostics`` は `PhaseTimeline.end()` が返した phase 行（Issue #107）。
    その attempt に対応する phase の観測をそのまま載せるだけで、判定には関与しない。
    """
    phase_observation = _phase_observation(phase_diagnostics)
    attempt = Attempt(
        attempt_id=attempt_id,
        retry_count=retry_count,
        phase=phase,
        stage_path=stage_path.copy() if stage_path else [],
        strategy=strategy,
        result=result,
        transition_reason=transition_reason,
        type_fix_result=type_fix_result.to_dict() if type_fix_result else None,
        rewrite_info=rewrite_info.to_dict() if rewrite_info else None,
        original_function1_signature=original_function1_signature,
        original_function2_signature=original_function2_signature,
        effective_function1_signature=effective_function1_signature,
        effective_function2_signature=effective_function2_signature,
        function1_signature_hypotheses=function1_signature_hypotheses or [],
        function2_signature_hypotheses=function2_signature_hypotheses or [],
        solver_results=solver_results.to_dict() if solver_results else None,
        final_smt_excerpt=final_smt[:500] if final_smt else None,
        final_smt=final_smt,
        counterexample=counterexample,
        pairwise_decisive=pairwise_decisive,
        pairwise_debug_stats=dict(pairwise_debug_stats or {}),
        normalization_rules=normalization_rules or [],
        unknown_reasons=list(coerce_unknown_reason_records(unknown_reasons)),
        mips64_abi_constraints=mips64_abi_constraints,
        elapsed_time=elapsed_time,
        **phase_observation,
    )
    debug_trace.add_attempt(attempt)


def _phase_observation(phase_diagnostics: Optional[Mapping[str, Any]]) -> Dict[str, Any]:
    """phase 行から attempt に載せる観測を取り出す（診断専用・fail-open）。

    phase 行が無い attempt（ABI 制約リトライなど）は `applied=None` と空集合になる。
    """
    empty: Dict[str, Any] = {
        "applied": None,
        "reanalyzed_sides": [],
        "skipped_reason": None,
        "reason_before": [],
        "reason_after": [],
    }
    if not isinstance(phase_diagnostics, Mapping):
        return empty
    try:
        return {
            "applied": phase_diagnostics.get("applied"),
            "reanalyzed_sides": [str(side) for side in phase_diagnostics.get("reanalyzed_sides") or ()],
            "skipped_reason": phase_diagnostics.get("skipped_reason"),
            "reason_before": [str(reason) for reason in phase_diagnostics.get("reason_before") or ()],
            "reason_after": [str(reason) for reason in phase_diagnostics.get("reason_after") or ()],
        }
    except Exception:  # diagnostics never fail the verdict
        return empty


def record_attempt_from_result(
    debug_trace: DebugTrace,
    attempt_id: int,
    retry_count: int,
    phase: str,
    result: EquivalenceResult,
    transition_reason: str,
    type_fix_result: TypeFixResult,
    strategy_name: str,
    phase_diagnostics: Optional[Mapping[str, Any]] = None,
) -> None:
    """EquivalenceResult から Attempt を構築して追加する"""
    pairwise_decisive = _build_pairwise_decisive_info(result)
    normalization_rules = _extract_normalization_rules(result)
    counterexample_dict = result.counterexample.to_dict() if result.counterexample else None
    mips64_abi_dict = _build_mips64_abi_dict(result)

    record_attempt(
        debug_trace=debug_trace,
        attempt_id=attempt_id,
        retry_count=retry_count,
        phase=phase,
        stage_path=result.stage_path,
        strategy=strategy_name,
        result=result.is_equivalent,
        transition_reason=transition_reason,
        type_fix_result=type_fix_result,
        rewrite_info=result.rewrite_info,
        original_function1_signature=result.function1_signature.to_dict() if result.function1_signature else None,
        original_function2_signature=result.function2_signature.to_dict() if result.function2_signature else None,
        effective_function1_signature=result.get_effective_function1_signature().to_dict() if result.get_effective_function1_signature() else None,
        effective_function2_signature=result.get_effective_function2_signature().to_dict() if result.get_effective_function2_signature() else None,
        function1_signature_hypotheses=list(result.function1_signature_hypotheses),
        function2_signature_hypotheses=list(result.function2_signature_hypotheses),
        solver_results=result.solver_results,
        final_smt=result.smt_formula,
        counterexample=counterexample_dict,
        pairwise_decisive=pairwise_decisive,
        pairwise_debug_stats=result.pairwise_debug_stats,
        normalization_rules=normalization_rules,
        mips64_abi_constraints=mips64_abi_dict,
        elapsed_time=result.total_time,
        unknown_reasons=list(result.unknown_reasons),
        phase_diagnostics=phase_diagnostics,
    )
    _record_explicit_proof_completions(debug_trace, result)


def _freeze_identity(value: Any) -> Any:
    if isinstance(value, dict):
        return tuple(
            (str(key), _freeze_identity(item))
            for key, item in sorted(value.items(), key=lambda pair: str(pair[0]))
        )
    if isinstance(value, (list, tuple)):
        return tuple(_freeze_identity(item) for item in value)
    return value


def _record_explicit_proof_completions(
    debug_trace: DebugTrace,
    result: EquivalenceResult,
) -> None:
    """Record only proof completions carrying an exact requirement identity.

    Recovery evidence without this identity remains useful diagnostic evidence,
    but must not discharge a blocker by proof-kind or proof-stage heuristics.
    """
    if not debug_trace.attempts:
        return
    attempt = debug_trace.attempts[-1]
    attempt_identity = AttemptIdentity(attempt.strategy, attempt.attempt_id)
    successful_statuses = {"complete", "completed", "discharged", "proven", "verified"}
    seen = {
        _freeze_identity(item.proof_requirement_id)
        for item in debug_trace.proof_completion_events
    }
    for wrapper in result.completed_recovery_proof_evidence or ():
        if not isinstance(wrapper, Mapping):
            continue
        evidence = wrapper.get("evidence")
        if not isinstance(evidence, Mapping):
            continue
        requirement = evidence.get("proof_requirement_id")
        if not isinstance(requirement, Mapping):
            requirement = _requirement_for_completed_evidence(debug_trace, evidence)
        if not isinstance(requirement, Mapping):
            continue
        try:
            canonical_requirement = ProofRequirementId.from_dict(requirement).to_dict()
        except (TypeError, ValueError):
            continue
        status = str(
            evidence.get("proof_status") or evidence.get("status") or ""
        ).lower()
        if status not in successful_statuses:
            continue
        frozen_requirement = _freeze_identity(canonical_requirement)
        if frozen_requirement in seen:
            continue
        artifact = evidence.get("proof_artifact_ref")
        if artifact is None:
            artifact = evidence.get("proof_obligation_id")
        if artifact is None:
            continue
        artifact_ref = _freeze_identity(artifact)
        if not isinstance(artifact_ref, tuple):
            artifact_ref = (artifact_ref,)
        completion = ProofCompletionEvent(
            completion_id=(
                "proof_completion",
                attempt.attempt_id,
                len(debug_trace.proof_completion_events),
                frozen_requirement,
            ),
            proof_requirement_id=canonical_requirement,
            proof_artifact_ref=artifact_ref,
            proof_status="proven",
            completed_at_attempt=attempt_identity,
        )
        debug_trace.add_proof_completion(completion)
        seen.add(frozen_requirement)

        context = _completion_applicability_context(
            result,
            canonical_requirement,
            artifact_ref,
        )
        for previous in debug_trace.attempts[:-1]:
            for occurrence in previous.reason_occurrences:
                reason_requirements = getattr(
                    occurrence.reason_record,
                    "proof_requirement_ids",
                    (),
                ) or ()
                if not any(
                    _freeze_identity(item) == frozen_requirement
                    for item in reason_requirements
                ):
                    continue
                snapshot_fingerprint = str(
                    evidence.get("source_snapshot_fingerprint") or ""
                )
                premise_digest = str(
                    evidence.get("semantic_seed_or_premise_digest") or ""
                )
                artifact_digest = str(
                    evidence.get("evidence_or_artifact_digest") or ""
                )
                recognizing_stage = str(
                    evidence.get("recognizing_stage") or ""
                )
                target = tuple(
                    getattr(occurrence.reason_record, "object_target_key", ()) or ()
                )
                slot = str(canonical_requirement.get("proof_kind") or "")
                if all((snapshot_fingerprint, premise_digest, artifact_digest, recognizing_stage, target, slot)):
                    debug_trace.add_reason_completion(
                        ReasonCompletionEvent(
                            completion_event_id=(
                                "reason_completion",
                                completion.completion_id,
                                occurrence.occurrence_id.reason_ordinal,
                            ),
                            completed_occurrence_id=occurrence.occurrence_id,
                            exact_target_id=target,
                            exact_missing_fact_or_proof_slot=slot,
                            source_snapshot_fingerprint=snapshot_fingerprint,
                            semantic_seed_or_premise_digest=premise_digest,
                            evidence_or_artifact_digest=artifact_digest,
                            recognizing_stage=recognizing_stage,
                            completed_at_attempt=attempt_identity,
                            applicability_status="unvalidated",
                        ),
                        current_snapshot_fingerprint=(
                            str(context.get("current_snapshot_fingerprint") or "")
                            if context is not None else ""
                        ),
                        current_semantic_seed_or_premise_digest=(
                            str(context.get("current_semantic_seed_or_premise_digest") or "")
                            if context is not None else ""
                        ),
                        artifact_is_valid=bool(
                            context is not None
                            and context.get("artifact_is_valid")
                            and str(context.get("current_evidence_or_artifact_digest") or "")
                            == artifact_digest
                        ),
                    )


def _completion_applicability_context(
    result: EquivalenceResult,
    requirement: Mapping[str, Any],
    artifact_ref: Tuple[Any, ...],
) -> Optional[Mapping[str, Any]]:
    frozen_requirement = _freeze_identity(requirement)
    matches = []
    for context in getattr(result, "reason_completion_applicability_contexts", ()) or ():
        if not isinstance(context, Mapping):
            continue
        if (
            _freeze_identity(context.get("proof_requirement_id")) == frozen_requirement
            and _freeze_identity(context.get("proof_artifact_ref")) == artifact_ref
        ):
            matches.append(context)
    return matches[0] if len(matches) == 1 else None


def _requirement_for_completed_evidence(
    debug_trace: DebugTrace,
    evidence: Mapping[str, Any],
) -> Optional[Mapping[str, Any]]:
    """Resolve a production artifact through an exact legacy obligation id.

    A legacy obligation may fan out to multiple typed requirements.  In that
    case the artifact is intentionally left unlinked until its producer emits
    the exact typed requirement identity.
    """
    proof_obligation_id = evidence.get("proof_obligation_id")
    if proof_obligation_id is None:
        return None
    frozen_obligation = _freeze_identity(proof_obligation_id)
    requirements: Dict[Any, Mapping[str, Any]] = {}
    for attempt in debug_trace.attempts:
        for occurrence in attempt.reason_occurrences:
            reason = occurrence.reason_record
            if _freeze_identity(getattr(reason, "proof_obligation_id", None)) != frozen_obligation:
                continue
            for requirement in getattr(reason, "proof_requirement_ids", ()) or ():
                if not isinstance(requirement, Mapping):
                    continue
                try:
                    canonical = ProofRequirementId.from_dict(requirement).to_dict()
                except (TypeError, ValueError):
                    continue
                requirements[_freeze_identity(canonical)] = canonical
    if len(requirements) != 1:
        return None
    return next(iter(requirements.values()))


def _build_pairwise_decisive_info(
    result: EquivalenceResult
) -> Optional[PairwiseDecisiveInfo]:
    if not result.pairwise_stats or result.pairwise_stats["total_pairs"] <= 0:
        return None

    decisive_result_str = "UNKNOWN"
    if result.is_equivalent is True:
        decisive_result_str = "UNSAT"
    elif result.is_equivalent is False:
        decisive_result_str = "SAT"

    decisive = PairwiseDecisiveInfo(
        decisive_result=decisive_result_str,
        total_pairs=result.pairwise_stats["total_pairs"],
        unsat_pairs=result.pairwise_stats["unsat_pairs"],
        sat_pairs=result.pairwise_stats["sat_pairs"],
        unknown_pairs=result.pairwise_stats["unknown_pairs"],
    )

    if result.sat_pair_info:
        info = result.sat_pair_info
        decisive.decisive_pair = (info["i"], info["j"])
        decisive.pair_stage = info.get("pair_stage", "unknown")
        decisive.case1_summary = info.get("case1_summary")
        decisive.case2_summary = info.get("case2_summary")
        decisive.value1_expr = info.get("value1", "")[:200]
        decisive.value2_expr = info.get("value2", "")[:200]

        final_query_full = info.get("final_query")
        if final_query_full:
            decisive.final_query = final_query_full
            decisive.final_query_excerpt = final_query_full[:200]
        elif result.smt_formula:
            decisive.final_query = result.smt_formula
            decisive.final_query_excerpt = result.smt_formula[:200]

    return decisive


def _extract_normalization_rules(result: EquivalenceResult) -> List[Any]:
    extracted: List[Any] = []
    if not hasattr(result, "normalization_rules") or not result.normalization_rules:
        return extracted

    for rule in result.normalization_rules:
        if isinstance(rule, NormalizationRuleApplication):
            extracted.append(rule)
        else:
            extracted.append(rule)
    return extracted


def _build_mips64_abi_dict(result: EquivalenceResult) -> Optional[Dict[str, Any]]:
    if not result.mips64_abi_constraints:
        return None

    return {
        key: {"signedness": value[0], "narrow_bits": value[1]}
        for key, value in result.mips64_abi_constraints.items()
    }
