"""Typed obligation-branch runner replacing checker stage orchestration."""

from __future__ import annotations

from dataclasses import dataclass
import hashlib
from typing import Any, Dict, List, Optional, Tuple
from uuid import uuid4

from scripts.function_tracer_pcode.proof.cause_identity import (
    ProofRequirementContract,
    ProofRequirementId,
)
from scripts.function_tracer_pcode.proof.obligations.model import (
    ActivationState,
    FunctionProofOutcome,
)
from scripts.function_tracer_pcode.proof.obligations.decision import DecisionAggregator
from scripts.function_tracer_pcode.proof.obligations.proof import (
    BranchActivationController,
    BranchSpec,
)
from scripts.function_tracer_pcode.proof.obligations.runtime import ObligationRuntimeSession


@dataclass(frozen=True)
class ProofGateProjection:
    gate_kind: str
    outcome: str
    reason_ids: Tuple[str, ...] = ()


@dataclass(frozen=True)
class BranchExecutionRecord:
    branch_id: str
    activation_state: ActivationState
    outcome: FunctionProofOutcome
    view_identity: Tuple[Any, ...]
    proof_gates: Tuple[ProofGateProjection, ...] = ()
    diagnostic_only: bool = False


@dataclass(frozen=True)
class InternalBranchTrace:
    policy_version: str
    records: Tuple[BranchExecutionRecord, ...]
    terminal_branch: Optional[str]


_RECOVERY_TO_GATE = {
    "return_coverage_completion": "return_coverage",
    "guard_partition_completion": "return_coverage",
    "return_partition_overlap_proof": "return_coverage",
    "call_effect_summary_proof": "call_effect",
    "effect_summary_completion": "call_effect",
    "loop_summary_completion": "loop_summary",
    "loop_recurrence_proof": "loop_summary",
    "sat_unsafety_resolution": "counterexample_safety",
}

_FINAL_DISPOSITION_DEBUG_KEYS = {
    "unsat_results": "unsat_pairs",
    "sat_results": "sat_pairs",
    "unknown_results": "unknown_pairs",
}


def merge_stage_debug_statistics(
    accumulated: Dict[str, int],
    result: Any,
) -> None:
    """Keep terminal dispositions separate from cross-stage attempt totals."""

    current = dict(getattr(result, "pairwise_debug_stats", None) or {})
    for key, value in current.items():
        target_key = (
            f"stage_attempt_{key}"
            if key in _FINAL_DISPOSITION_DEBUG_KEYS
            else key
        )
        accumulated[target_key] = (
            accumulated.get(target_key, 0) + int(value or 0)
        )

    final_stats = dict(getattr(result, "pairwise_stats", None) or {})
    for debug_key, pairwise_key in _FINAL_DISPOSITION_DEBUG_KEYS.items():
        if pairwise_key in final_stats:
            accumulated[debug_key] = int(final_stats[pairwise_key] or 0)
        elif debug_key in current:
            accumulated[debug_key] = int(current[debug_key] or 0)

    if accumulated:
        result.pairwise_debug_stats = dict(accumulated)


def project_proof_gates(result: Any) -> Tuple[ProofGateProjection, ...]:
    grouped: Dict[str, List[str]] = {}
    for reason in getattr(result, "unknown_reasons", ()) or ():
        reason_id = getattr(reason, "reason_id", None)
        if not isinstance(reason_id, str) or not reason_id:
            continue
        proof_kind = str(getattr(reason, "recovery_proof_kind", "") or "")
        gate_kind = _RECOVERY_TO_GATE.get(proof_kind, "other_blocker")
        grouped.setdefault(gate_kind, []).append(reason_id)
    projections = [
        ProofGateProjection(kind, "inconclusive", tuple(dict.fromkeys(reason_ids)))
        for kind, reason_ids in sorted(grouped.items())
    ]
    if getattr(result, "is_equivalent", None) is True:
        projections.append(ProofGateProjection("function_proof", "satisfied"))
    elif getattr(result, "is_equivalent", None) is False:
        projections.append(ProofGateProjection("counterexample_safety", "safe_decisive"))
    return tuple(projections)


def _outcome(result: Any) -> FunctionProofOutcome:
    is_timeout = getattr(result, "is_timeout", None)
    if callable(is_timeout) and is_timeout():
        return FunctionProofOutcome.INCONCLUSIVE
    value = getattr(result, "is_equivalent", None)
    if value is True:
        return FunctionProofOutcome.EQUIVALENT
    if value is False:
        return FunctionProofOutcome.NOT_EQUIVALENT
    return FunctionProofOutcome.INCONCLUSIVE


def _cutover_attempt_outcome(result: Any) -> Any:
    """Classify one strategy attempt without claiming final decision authority."""

    from scripts.function_tracer_pcode.authority.contracts import Outcome

    if getattr(result, "error_message", None) or getattr(
        result, "failure_status", None
    ) in {"strategy_exception", "unexpected_pairwise_state"}:
        return Outcome.ERROR
    is_timeout = getattr(result, "is_timeout", None)
    if callable(is_timeout) and is_timeout():
        return Outcome.TIMEOUT
    value = getattr(result, "is_equivalent", None)
    if value is True:
        return Outcome.EQUIVALENT
    if value is False:
        return Outcome.NOT_EQ
    return Outcome.UNKNOWN


def normalize_timeout_contradiction(result: Any) -> None:
    """Fail closed when a stale decisive value also reports a timeout."""

    is_timeout = getattr(result, "is_timeout", None)
    if not callable(is_timeout) or not is_timeout():
        return
    if getattr(result, "is_equivalent", None) not in {True, False}:
        return
    result.is_equivalent = None
    strategy_result = getattr(result, "_strategy_result", None)
    if strategy_result is not None:
        strategy_result.is_equivalent = None
    stats = dict(getattr(result, "pairwise_debug_stats", None) or {})
    stats["timeout_decisive_state_contradiction"] = (
        int(stats.get("timeout_decisive_state_contradiction", 0) or 0) + 1
    )
    result.pairwise_debug_stats = stats


def _cutover_branch_policy(result: Any) -> tuple[Any, tuple[str, ...], bool]:
    """Select the actual fallback action from the sealed all-five matrix."""

    from scripts.function_tracer_pcode.authority.decision.production_cutover import (
        RETRY_FALLBACK_MATRIX,
    )

    attempt_outcome = _cutover_attempt_outcome(result)
    actions = RETRY_FALLBACK_MATRIX[attempt_outcome]
    continue_fallback = "FALLBACK_NEXT_STRATEGY" in actions
    return attempt_outcome, actions, continue_fallback


def run_obligation_branch_plan(
    checker: Any,
    analysis1: Any,
    analysis2: Any,
    binary1_name: str,
    binary2_name: str,
    save_formula: bool,
    type_fix_result: Any,
    retry_count: int,
    original_signature1: Any,
    original_signature2: Any,
) -> Any:
    """Execute branch obligations under the versioned activation policy."""

    runtime = ObligationRuntimeSession.create(analysis1, analysis2)
    checker._obligation_runtime_session = runtime
    last_result = None
    stage_path: List[str] = []
    records: List[BranchExecutionRecord] = []
    last_call_effect_manifest = None
    accumulated_pairwise_debug_stats: Dict[str, int] = {}
    by_id = {spec.stage_id.value: spec for spec in checker.stage_plan}

    def eligible(branch_id: str):
        if branch_id == "S_LOOP_TEMPLATE_ABSTRACTION":
            return lambda _outcomes: checker._should_try_loop_template_stage(last_result)
        if branch_id == "S_MONOLITHIC_FALLBACK":
            return lambda _outcomes: not checker._should_skip_monolithic_fallback(analysis1, analysis2)
        return None

    controller = BranchActivationController(tuple(
        BranchSpec(branch_id, eligibility=eligible(branch_id)) for branch_id in by_id
    ))

    while True:
        branch_id = controller.next_branch()
        if branch_id is None:
            break
        spec = by_id[branch_id]
        checker._debug_print("-" * 60)
        checker._debug_print(f"Stage {branch_id}: {spec.description}")
        checker._debug_print("-" * 60)

        def execute_branch(replan_plan=None):
            from scripts.function_tracer_pcode.proof.monolithic_authority import (
                issue_production_branch_authority,
                revoke_production_branch_authority,
            )
            # 6c-3 (#93): branch 文脈は BranchCheckContext の明示引数のみで checker へ渡す（facade の
            # _active_* への set/restore/delete は撤去済み）。builder の import は lease 発行より前に置く:
            # lease 発行成功後は例外を投げ得る処理を挟まず直ちに try/finally（revoke）に入る。
            from scripts.function_tracer_pcode.checker.branch_context import (
                build_branch_check_context,
            )
            session_id = uuid4().hex
            generation = int(getattr(checker, "_call_proof_generation", 0) or 0) + 1
            view_digest = hashlib.sha256(repr((
                runtime.current_view.view_id, runtime.premise_digest,
            )).encode("utf-8")).hexdigest()
            branch_lease = issue_production_branch_authority(
                session_id, branch_id, generation, view_digest,
            )
            try:
                if spec.strategy == "abstract_pairwise":
                    # 6c-2 (#93): inner check() の effective context: session / generation / lease は runner
                    # 発行値、active branch id は None（strategy class 名 fallback）、strategy は pairwise。
                    # outer の S_ABSTRACT_RECURSIVE_SUMMARY を渡してはならない（"S_" 判定が変わる）。
                    inner_context = build_branch_check_context(
                        strategy=checker.pairwise_strategy,
                        replan_plan=replan_plan,
                        call_proof_generation=generation,
                        active_comparison_generation=generation,
                        active_comparison_session_id=session_id,
                        active_call_proof_branch_id=None,
                        decision_mode=getattr(checker, "call_proof_decision_mode", None),
                        production_branch_authority_lease=branch_lease,
                    )
                    return checker._run_recursive_abstraction_stage(
                        analysis1, analysis2, binary1_name, binary2_name, save_formula,
                        type_fix_result, retry_count, original_signature1, original_signature2,
                        branch_context=inner_context,
                    )
                strategies = {
                    "pairwise": checker.pairwise_strategy,
                    "loop_template_pairwise": checker.loop_template_strategy,
                    "monolithic": checker.monolithic_strategy,
                }
                if spec.strategy not in strategies:
                    raise ValueError(f"Unknown strategy: {spec.strategy}")
                try:
                    strategies[spec.strategy]._obligation_runtime_session = runtime
                except (AttributeError, TypeError):
                    pass
                # replan の precedence（plan の frame_generation / session / branch が runner 発行値に勝つ）は
                # checker と同じ builder に任せる。lease は今発行した branch_lease object そのもの。
                explicit_context = build_branch_check_context(
                    strategy=strategies[spec.strategy],
                    replan_plan=replan_plan,
                    call_proof_generation=generation,
                    active_comparison_generation=generation,
                    active_comparison_session_id=session_id,
                    active_call_proof_branch_id=branch_id,
                    decision_mode=getattr(checker, "call_proof_decision_mode", None),
                    production_branch_authority_lease=branch_lease,
                )
                return checker.check(
                    analysis1, analysis2, binary1_name, binary2_name, save_formula,
                    type_fix_result=type_fix_result, retry_count=retry_count,
                    original_signature1=original_signature1,
                    original_signature2=original_signature2,
                    force_strategy=strategies[spec.strategy],
                    branch_context=explicit_context,
                )
            finally:
                revoke_production_branch_authority(branch_lease)

        active_strategy = (
            checker.pairwise_strategy
            if spec.strategy == "abstract_pairwise"
            else {
                "pairwise": checker.pairwise_strategy,
                "loop_template_pairwise": checker.loop_template_strategy,
                "monolithic": checker.monolithic_strategy,
            }.get(spec.strategy)
        )

        branch_requirement = ProofRequirementId.create(
            "function_branch",
            ("branch", branch_id),
            ProofRequirementContract(
                proposition="function equivalence alternative branch",
                observation_surface=(branch_id,),
                active_precondition=(runtime.current_view.view_id,),
            ),
        )
        runtime.schedule(branch_requirement, "function_branch", execute_branch)
        _item, result = runtime.run_next()
        if result is None:
            controller.mark_inapplicable(branch_id)
            records.append(BranchExecutionRecord(
                branch_id, ActivationState.INAPPLICABLE,
                FunctionProofOutcome.INCONCLUSIVE, runtime.current_view.view_id,
            ))
            continue

        normalize_timeout_contradiction(result)

        stage_path.append(branch_id)
        result.stage_path = stage_path.copy()
        merge_stage_debug_statistics(
            accumulated_pairwise_debug_stats,
            result,
        )
        if getattr(result, "call_effect_shadow_manifest", None) is not None:
            last_call_effect_manifest = result.call_effect_shadow_manifest
        elif last_call_effect_manifest is not None:
            result.call_effect_shadow_manifest = last_call_effect_manifest
        checker._merge_completed_recovery_proofs_from_result(analysis1, analysis2, result)
        def gate_producer(gate_kind, reason, _requirement):
            def produce():
                if active_strategy is None:
                    return FunctionProofOutcome.INCONCLUSIVE
                if gate_kind == "return_coverage":
                    complete = active_strategy._return_coverage_proof_is_complete(
                        reason, analysis1, analysis2
                    )
                elif gate_kind == "call_effect":
                    complete = active_strategy._call_effect_summary_proof_is_complete(
                        reason, analysis1, analysis2
                    )
                elif gate_kind == "loop_summary":
                    complete = active_strategy._recovery_proof_is_complete(
                        reason, analysis1, analysis2
                    )
                elif gate_kind == "counterexample_safety":
                    complete = active_strategy._sat_unsafety_resolution_proof_is_complete(
                        reason,
                        analysis1,
                        analysis2,
                        current_counterexample_raw=getattr(result, "counterexample_raw", None),
                    )
                    if complete:
                        return FunctionProofOutcome.NOT_EQUIVALENT
                else:
                    complete = False
                return (
                    FunctionProofOutcome.EQUIVALENT
                    if complete
                    else FunctionProofOutcome.INCONCLUSIVE
                )
            return produce

        replan_generation = 0
        while True:
            runtime.plan_proof_gates(result, _RECOVERY_TO_GATE, gate_producer)
            while True:
                gate_item, _gate_value = runtime.run_next()
                if gate_item is None:
                    break
            # Evidence may derive a new analysis view only for an
            # inconclusive branch.  The old ledger is superseded and the same
            # pairwise branch is then executed against the successor view.
            produced_views = ()
            if _outcome(result) == FunctionProofOutcome.INCONCLUSIVE:
                produced_views = runtime.apply_completed_evidence(
                    getattr(result, "completed_recovery_proof_evidence", ()) or (),
                    reasons=getattr(result, "unknown_reasons", ()) or (),
                )
                while True:
                    affected_item, _affected_value = runtime.run_next()
                    if affected_item is None:
                        break
            if not produced_views:
                break
            if spec.strategy not in {"pairwise", "loop_template_pairwise"}:
                break
            prior_dispatch_frame = getattr(
                result, "_prepared_dispatch_frame", None
            )
            if (
                prior_dispatch_frame is None
                or prior_dispatch_frame.pair_disposition_ledger is None
            ):
                # Compatibility/test branches without a production ledger
                # have no pair surface to replan.
                break
            replan_generation += 1
            successor_plan = runtime.pair_ledger_manager.pending_successor
            if successor_plan is None:
                break
            # 6c-3: successor plan は明示 context 経由でのみ渡す（facade 属性は使わない）。
            replanned = execute_branch(replan_plan=successor_plan)
            if replanned is None:
                break
            result = replanned
            normalize_timeout_contradiction(result)
            result.stage_path = stage_path.copy()
            replanned_stats = dict(
                getattr(result, "pairwise_debug_stats", None) or {}
            )
            replanned_stats["derived_view_pair_replans"] = (
                int(replanned_stats.get("derived_view_pair_replans", 0) or 0)
                + 1
            )
            result.pairwise_debug_stats = replanned_stats
            merge_stage_debug_statistics(
                accumulated_pairwise_debug_stats,
                result,
            )
            if getattr(result, "call_effect_shadow_manifest", None) is not None:
                last_call_effect_manifest = result.call_effect_shadow_manifest
            elif last_call_effect_manifest is not None:
                result.call_effect_shadow_manifest = last_call_effect_manifest
            checker._merge_completed_recovery_proofs_from_result(
                analysis1, analysis2, result
            )
        pre_aggregation_outcome = result.is_equivalent
        DecisionAggregator.apply(result, runtime)
        post_aggregation_outcome = result.is_equivalent
        dispatch_frame = getattr(result, "_prepared_dispatch_frame", None)
        strategy_result = getattr(result, "_strategy_result", None)
        if (
            strategy_result is not None
            and post_aggregation_outcome != pre_aggregation_outcome
            and post_aggregation_outcome != strategy_result.is_equivalent
        ):
            result.is_equivalent = None
            strategy_result.is_equivalent = None
            result.error_message = "decision_aggregator_terminal_receipt_mismatch"
            result.failure_status = "strategy_exception"
            result.failure_message = (
                "Decision aggregation changed the terminal outcome after query "
                "evidence was prepared; a new generation is required."
            )
            strategy_result.error_kind = "strategy_exception"
            strategy_result.error_message = result.failure_message
        if dispatch_frame is not None and strategy_result is not None:
            if (
                dispatch_frame.pair_disposition_ledger is not None
                and dispatch_frame.receipt is None
            ):
                try:
                    from scripts.function_tracer_pcode.proof.call_effect.preflight import (
                        diagnostic_projection,
                        finalize_pairwise_comparison_receipt,
                    )

                    strategy_result.comparison_execution_receipt = (
                        finalize_pairwise_comparison_receipt(dispatch_frame)
                    )
                    debug_stats = dict(
                        getattr(result, "pairwise_debug_stats", None) or {}
                    )
                    debug_stats["pair_ledger_sealed"] = 1
                    result.pairwise_debug_stats = debug_stats
                    manifest = getattr(result, "call_effect_shadow_manifest", None)
                    if isinstance(manifest, dict):
                        result.call_effect_shadow_manifest = diagnostic_projection(
                            manifest, dispatch_frame
                        )
                except RuntimeError:
                    # A proof gate derived a newer view or left work pending.
                    # The final gate below converts the missing receipt into a
                    # typed UNKNOWN blocker; it is never surfaced as ERROR.
                    strategy_result.comparison_execution_receipt = None
            elif dispatch_frame.monolithic_terminal_receipt is not None:
                try:
                    from scripts.function_tracer_pcode.proof.call_effect.preflight import (
                        finalize_monolithic_comparison_receipt,
                    )

                    strategy_result.comparison_execution_receipt = (
                        finalize_monolithic_comparison_receipt(dispatch_frame)
                    )
                except RuntimeError:
                    strategy_result.comparison_execution_receipt = None
            checker._apply_preflight_final_gate(
                strategy_result,
                dispatch_frame,
                cleanup_complete=bool(dispatch_frame.cleanup_complete),
            )
            result.is_equivalent = strategy_result.is_equivalent
            result.unknown_reasons = list(strategy_result.unknown_reasons)
            provenance = getattr(result, "call_proof_terminal_provenance", None)
            receipt = getattr(dispatch_frame, "receipt", None)
            if isinstance(provenance, dict):
                from scripts.function_tracer_pcode.authority.domains.comparison_closure import (
                    InconclusiveComparisonAuthority,
                    query_execution_record_projection,
                )
                trusted = bool(
                    receipt is not None and receipt.is_trusted_for(dispatch_frame)
                )
                provenance["comparison_receipt_id"] = (
                    receipt.receipt_id if trusted else None
                )
                terminal_receipt = dispatch_frame.monolithic_terminal_receipt
                provenance["monolithic_terminal_receipt"] = (
                    {
                        "receipt_digest": terminal_receipt.receipt_digest,
                        "comparison_receipt_id": (
                            terminal_receipt.comparison_receipt_id
                        ),
                        "outcome_kind": terminal_receipt.outcome_kind,
                        "parent_lease_digest": terminal_receipt.parent_lease_digest,
                        "execution_lease_digest": terminal_receipt.execution_lease_digest,
                        "frozen_surface_digest": terminal_receipt.frozen_surface_digest,
                        "census_digest": terminal_receipt.census_digest,
                        "region_receipt_digests": list(
                            terminal_receipt.region_receipt_digests
                        ),
                        "sat_region_id": terminal_receipt.sat_region_id,
                        "model_digest": terminal_receipt.model_digest,
                        "fixed_model_assertion_digest": terminal_receipt.fixed_model_assertion_digest,
                        "legacy_replay_receipt_digest": terminal_receipt.legacy_replay_receipt_digest,
                        "counterexample_safety_receipt_digest": terminal_receipt.counterexample_safety_receipt_digest,
                        "gate_reference_digests": list(terminal_receipt.gate_reference_digests),
                        "validated": terminal_receipt.validates(),
                    }
                    if terminal_receipt is not None else None
                )
                provenance["query_execution_receipts"] = [
                    query_execution_record_projection(record)
                    for record in tuple(
                        getattr(receipt, "query_records", ()) or ()
                    )
                ] if trusted else []
                provenance["pair_closure_snapshot"] = (
                    receipt.closure_snapshot if trusted else ()
                )
                provenance["pair_closure_snapshot_digest"] = (
                    receipt.closure_snapshot_digest if trusted else None
                )
                provenance["receipt_ledger_binding_digest"] = (
                    receipt.ledger_binding_digest if trusted else None
                )
                provenance["receipt_quiescence_certificate_digest"] = (
                    receipt.quiescence_certificate_digest if trusted else None
                )
                provenance["receipt_disposition_counts"] = (
                    dict(receipt.disposition_counts) if trusted else None
                )
                provenance["receipt_required_projection_binding_ids"] = (
                    list(receipt.required_projection_binding_ids)
                    if trusted else None
                )
                provenance["receipt_consumed_projection_binding_ids"] = (
                    list(receipt.consumed_projection_binding_ids)
                    if trusted else None
                )
                provenance["receipt_excluded_projection_binding_ids"] = (
                    list(receipt.excluded_projection_binding_ids)
                    if trusted else None
                )
                provenance["terminal_runtime_view_id"] = runtime.current_view.view_id
                provenance["terminal_runtime_premise_digest"] = runtime.premise_digest
                provenance["receipt_final_runtime_binding_valid"] = trusted
                provenance["receipt_successor_ledger_reused"] = (
                    bool(trusted and dispatch_frame.successor_ledger_reused)
                    if dispatch_frame.replan_successor_plan is not None
                    else None
                )
                terminal_receipt = dispatch_frame.monolithic_terminal_receipt
                result._inconclusive_comparison_authority = (
                    InconclusiveComparisonAuthority.issue(dispatch_frame)
                    if (
                        trusted
                        and terminal_receipt is not None
                        and terminal_receipt.outcome_kind
                        == "inconclusive_diagnostic"
                        and tuple(receipt.query_records)
                    )
                    else None
                )
        from scripts.function_tracer_pcode.authority.lifecycle.production_signals import (
            active_production_pilot_session,
        )

        if (
            result.is_equivalent is True
            and active_production_pilot_session() is not None
        ):
            receipt = getattr(dispatch_frame, "receipt", None)
            if receipt is None or not receipt.is_trusted_for(dispatch_frame):
                result.is_equivalent = None
                result.error_message = "eq_closure_comparison_receipt_invalid"
                result.failure_status = "strategy_exception"
                result.failure_message = (
                    "EQUIVALENT lacks its trusted comparison execution receipt"
                )
            else:
                from scripts.function_tracer_pcode.authority.lifecycle.production_signals import (
                    issue_pending_eq_closure_authority,
                )

                issue_pending_eq_closure_authority(
                    active_production_pilot_session(), receipt, dispatch_frame,
                )
        last_result = result
        attempt_outcome, cutover_actions, continue_fallback = (
            _cutover_branch_policy(result)
        )
        result.cutover_attempt_outcome = attempt_outcome.value
        result.cutover_retry_fallback_actions = cutover_actions
        outcome = _outcome(result)
        controller.record(branch_id, outcome)
        view_id = runtime.current_view.view_id
        records.append(BranchExecutionRecord(
            branch_id, ActivationState.COMPLETED, outcome, view_id,
            project_proof_gates(result),
        ))
        if outcome != FunctionProofOutcome.INCONCLUSIVE or not continue_fallback:
            controller.next_branch()
            break

    for branch_id, state in controller.states.items():
        if state in {ActivationState.INAPPLICABLE, ActivationState.SHORT_CIRCUITED} and not any(
            record.branch_id == branch_id for record in records
        ):
            records.append(BranchExecutionRecord(
                branch_id, state, FunctionProofOutcome.INCONCLUSIVE,
                runtime.current_view.view_id,
            ))
    terminal = next((
        record.branch_id for record in records
        if record.outcome in {FunctionProofOutcome.EQUIVALENT, FunctionProofOutcome.NOT_EQUIVALENT}
    ), None)
    stage_order = {branch_id: index for index, branch_id in enumerate(by_id)}
    records.sort(key=lambda record: stage_order[record.branch_id])
    checker._last_obligation_branch_trace = InternalBranchTrace(
        controller.policy_version, tuple(records), terminal
    )
    if last_result is None:
        from scripts.function_tracer_pcode.smt import ParallelResult
        from scripts.function_tracer_pcode.checker.result import EquivalenceResult
        from scripts.function_tracer_pcode.checker.unknown_reason import (
            make_internal_v2_reason_diagnostic,
        )

        blockers = tuple(dict.fromkeys(
            str(item)
            for analysis in (analysis1, analysis2)
            for item in (
                analysis.get_equivalence_blocking_unsafety_reasons()
                if callable(getattr(
                    analysis, "get_equivalence_blocking_unsafety_reasons", None
                ))
                else ()
            )
        ))
        return EquivalenceResult(
            is_equivalent=None,
            function1_name=analysis1.function_name,
            function2_name=analysis2.function_name,
            binary1_name=binary1_name,
            binary2_name=binary2_name,
            solver_results=ParallelResult(results=[]),
            type_fix_result=type_fix_result,
            retry_count=retry_count,
            function1_signature=original_signature1,
            function2_signature=original_signature2,
            stage_path=[],
            unknown_reasons=[
                make_internal_v2_reason_diagnostic(
                    "expression_translation_incomplete",
                    stage="S_MONOLITHIC_FALLBACK",
                    evidence_refs=(
                        "monolithic_branch_inapplicable",
                        *(blockers or ("incomplete_control_flow_summary",)),
                    ),
                    detail=(
                        "Monolithic comparison was inapplicable because the "
                        "control-flow summary is incomplete."
                    ),
                )
            ],
        )
    return last_result
