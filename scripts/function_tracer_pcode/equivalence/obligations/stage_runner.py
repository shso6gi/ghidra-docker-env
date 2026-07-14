"""Typed obligation-branch runner replacing checker stage orchestration."""

from __future__ import annotations

from dataclasses import dataclass
from typing import Any, Dict, List, Optional, Tuple

from ..cause_identity import ProofRequirementContract, ProofRequirementId
from .model import ActivationState, FunctionProofOutcome
from .decision import DecisionAggregator
from .proof import BranchActivationController, BranchSpec
from .runtime import ObligationRuntimeSession


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


def project_proof_gates(result: Any) -> Tuple[ProofGateProjection, ...]:
    grouped: Dict[str, List[str]] = {}
    for reason in getattr(result, "unknown_reasons", ()) or ():
        proof_kind = str(getattr(reason, "recovery_proof_kind", "") or "")
        gate_kind = _RECOVERY_TO_GATE.get(proof_kind, "other_blocker")
        grouped.setdefault(gate_kind, []).append(str(getattr(reason, "reason_id", "unknown")))
    projections = [
        ProofGateProjection(kind, "inconclusive", tuple(dict.fromkeys(reason_ids)))
        for kind, reason_ids in sorted(grouped.items())
    ]
    if getattr(result, "is_equivalent", None) is True:
        projections.append(ProofGateProjection("function_proof", "satisfied"))
    elif getattr(result, "is_equivalent", None) is False:
        projections.append(ProofGateProjection("counterexample_safety", "safe_decisive"))
    return tuple(projections)


def _view_identity(analysis1: Any, analysis2: Any, branch_id: str) -> Tuple[Any, ...]:
    def side(analysis: Any) -> Tuple[Any, ...]:
        function_ref = getattr(analysis, "function_ref", None)
        stable_key = getattr(function_ref, "stable_key", None)
        function_key = stable_key() if callable(stable_key) else (
            getattr(analysis, "function_name", None), getattr(analysis, "entry_point", None)
        )
        return (
            getattr(analysis, "binary_id", None), function_key,
            getattr(analysis, "analysis_view_identity", None),
            int(getattr(analysis, "partition_revision", 0) or 0),
        )
    return ("obligation_branch_view", branch_id, side(analysis1), side(analysis2))


def _outcome(result: Any) -> FunctionProofOutcome:
    value = getattr(result, "is_equivalent", None)
    if value is True:
        return FunctionProofOutcome.EQUIVALENT
    if value is False:
        return FunctionProofOutcome.NOT_EQUIVALENT
    return FunctionProofOutcome.INCONCLUSIVE


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

        def execute_branch():
            if spec.strategy == "abstract_pairwise":
                return checker._run_recursive_abstraction_stage(
                    analysis1, analysis2, binary1_name, binary2_name, save_formula,
                    type_fix_result, retry_count, original_signature1, original_signature2,
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
                # Characterization tests may use immutable opaque sentinels.
                # Real strategy instances always accept the runtime binding.
                pass
            previous_branch = getattr(checker, "_active_call_proof_branch_id", None)
            checker._active_call_proof_branch_id = branch_id
            try:
                return checker.check(
                    analysis1, analysis2, binary1_name, binary2_name, save_formula,
                    type_fix_result=type_fix_result, retry_count=retry_count,
                    original_signature1=original_signature1,
                    original_signature2=original_signature2,
                    force_strategy=strategies[spec.strategy],
                )
            finally:
                if previous_branch is None:
                    try:
                        del checker._active_call_proof_branch_id
                    except AttributeError:
                        pass
                else:
                    checker._active_call_proof_branch_id = previous_branch

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

        stage_path.append(branch_id)
        result.stage_path = stage_path.copy()
        current_debug_stats = dict(getattr(result, "pairwise_debug_stats", None) or {})
        for key, value in current_debug_stats.items():
            accumulated_pairwise_debug_stats[key] = (
                accumulated_pairwise_debug_stats.get(key, 0) + int(value or 0)
            )
        if accumulated_pairwise_debug_stats:
            result.pairwise_debug_stats = dict(accumulated_pairwise_debug_stats)
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

        runtime.plan_proof_gates(result, _RECOVERY_TO_GATE, gate_producer)
        while True:
            gate_item, _gate_value = runtime.run_next()
            if gate_item is None:
                break
        runtime.apply_completed_evidence(
            getattr(result, "completed_recovery_proof_evidence", ()) or (),
            reasons=getattr(result, "unknown_reasons", ()) or (),
        )
        while True:
            affected_item, _affected_value = runtime.run_next()
            if affected_item is None:
                break
        DecisionAggregator.apply(result, runtime)
        last_result = result
        outcome = _outcome(result)
        controller.record(branch_id, outcome)
        view_id = runtime.current_view.view_id
        records.append(BranchExecutionRecord(
            branch_id, ActivationState.COMPLETED, outcome, view_id,
            project_proof_gates(result),
        ))
        if outcome != FunctionProofOutcome.INCONCLUSIVE:
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
        raise RuntimeError("No applicable obligation branch produced a result")
    return last_result
