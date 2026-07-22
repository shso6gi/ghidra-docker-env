# -*- coding: utf-8 -*-

from dataclasses import replace
import hashlib
import json
from pathlib import Path
from types import SimpleNamespace

import pytest

from scripts.function_tracer_pcode.equivalence.v2.census_contract import (
    ActiveOccurrenceMaterialization,
    CensusEntry,
    CensusManifest,
    CensusMode,
    CensusStatus,
    CoverageInputs,
)
from scripts.function_tracer_pcode.equivalence.v2.contracts import (
    CauseOccurrence,
    CauseOccurrenceAuthority,
    CauseTransformationEvent,
    CauseTransformationProofReceipt,
    IdentityScope,
    Outcome,
    ProofRequirement,
    ReasonDefinition,
    RecoveryAddressability,
    RequirementCompletionReceipt,
    RequirementSlotDefinition,
    ResultKind,
    SatisfactionContractDefinition,
    TransformationKind,
    all_of,
    any_of,
    authority_digest,
    requirement_slot,
)
from scripts.function_tracer_pcode.equivalence.v2.pilot import (
    PILOT_TYPED_CAUSE_KINDS,
    PilotDifferenceEntry,
    PilotDifferenceManifest,
    ProductionDualWriteEvidence,
    ProductionDualWritePilotConnector,
    TerminalizationIntent,
    run_dual_write_pilot,
)
from scripts.function_tracer_pcode.equivalence.v2.production_signals import (
    ComparisonClosureProductionSignal,
    ComparisonClosurePilotEncoder,
    CompositeProductionSignalEncoder,
    OutcomePartitionPilotEncoder,
    OutcomePartitionProductionSignal,
    emit_comparison_closure_signal,
    production_signal_scope,
)
from scripts.function_tracer_pcode.equivalence.v2.process_supervisor import (
    PROCESS_DURABLE_REASON_REGISTRY,
    PROCESS_DURABLE_RECOVERY_REGISTRY,
)
from scripts.function_tracer_pcode.equivalence.obligations.outcome_partition import (
    UnaryProducerResult,
    prove_unary_partition,
)
from scripts.function_tracer_pcode.equivalence.v2.reducer import ShadowLifecycleReducer
from scripts.function_tracer_pcode.equivalence.checker import EquivalenceChecker
from scripts.function_tracer_pcode.equivalence.result import EquivalenceResult
from scripts.function_tracer_pcode.smt import ParallelResult
from scripts.function_tracer_pcode.equivalence.v2.registry import (
    SatisfactionBindingFactory,
    SealedReasonRegistry,
    SealedRecoveryRegistry,
    SemanticCauseIdentityFactory,
)
from scripts.function_tracer_pcode.equivalence.v2.shadow_compare import (
    build_shadow_census_preview,
)
from scripts.function_tracer_pcode.equivalence.v2.stream import (
    CauseObservedEventAuthority,
    CauseTransformedEventAuthority,
    DecisiveProofEventAuthority,
    EventIntent,
    EventRecorder,
    EventType,
    ProcessExecutionEventAuthority,
    RequirementCompletedEventAuthority,
    SolverExecutionEventAuthority,
)


def _reason(reason_id, addressability):
    return ReasonDefinition(
        reason_id,
        "return_outcome_totality",
        "coverage_gap",
        "blocks_equivalence",
        frozenset(("outcome_partition",)),
        ("partition_identity", "residual_region"),
        frozenset(("totality", "alternative_totality", "safety")),
        True,
        "return-outcome-totality-v2",
        addressability,
    )


def _contract():
    return SatisfactionContractDefinition(
        "return-outcome-totality-pilot",
        1,
        (
            RequirementSlotDefinition("A", frozenset(("totality",))),
            RequirementSlotDefinition("B", frozenset(("alternative_totality",))),
            RequirementSlotDefinition("C", frozenset(("safety",))),
        ),
        all_of(
            any_of(requirement_slot("A"), requirement_slot("B")),
            requirement_slot("C"),
        ),
    )


def _environment():
    reasons = SealedReasonRegistry.build((
        _reason(
            "return_coverage_inconclusive",
            RecoveryAddressability.REQUIREMENT_REQUIRED,
        ),
        _reason(
            "return_coverage_gap",
            RecoveryAddressability.REQUIREMENT_OPTIONAL,
        ),
        _reason(
            "outcome_partition_residual_sat",
            RecoveryAddressability.REQUIREMENT_REQUIRED,
        ),
    ))
    recovery = SealedRecoveryRegistry.build((_contract(),))
    return reasons, recovery, ShadowLifecycleReducer(
        reason_registry=reasons,
        recovery_registry=recovery,
    )


def _authority(
    occurrence_id="occ-1",
    *,
    prefix="req",
    reason_id="return_coverage_inconclusive",
    optional_without_requirement=False,
    target_key=None,
    source_snapshot_fingerprint="snapshot",
):
    reasons, recovery, _ = _environment()
    cause = SemanticCauseIdentityFactory(reasons).create(
        reason_id=reason_id,
        identity_scope=IdentityScope.UNARY,
        target_kind="outcome_partition",
        canonical_target_key=("partition", target_key or prefix),
        missing_semantic_fact=("totality_unproved", target_key or prefix),
        semantic_proposition=("return_outcome_partition_is_total",),
        observation_surface=("reachable_return_regions",),
        active_semantic_precondition=("function_reachable", True),
        correspondence_contract=("unary_partition",),
    )
    if optional_without_requirement:
        occurrence = CauseOccurrence(
            occurrence_id, cause, reason_id, "partition", "outcome_partition",
            IdentityScope.UNARY, None, None, None, None, (),
            ("partition-evidence", "residual-evidence"),
            "v2-pilot", source_snapshot_fingerprint,
            "outcome-totality-producer", "attempt",
        )
        return CauseOccurrenceAuthority(occurrence, None)
    contract = _contract()
    requirements = {
        "A": ProofRequirement(f"{prefix}-A", "totality", ("primary",)),
        "B": ProofRequirement(
            f"{prefix}-B", "alternative_totality", ("alternative",)
        ),
        "C": ProofRequirement(f"{prefix}-C", "safety", ("safety",)),
    }
    bound = SatisfactionBindingFactory(recovery).bind(
        contract_definition_id=contract.contract_definition_id,
        contract_version=contract.contract_version,
        bindings=requirements,
    )
    occurrence = CauseOccurrence(
        occurrence_id, cause, reason_id, "partition", "outcome_partition",
        IdentityScope.UNARY, contract.contract_definition_id,
        contract.contract_version, contract.normalized_expression_digest,
        bound.bound_expression_digest, tuple(sorted(bound.requirement_ids())),
        ("partition-evidence", "residual-evidence"),
        "v2-pilot", source_snapshot_fingerprint,
        "outcome-totality-producer", "attempt",
    )
    return CauseOccurrenceAuthority(occurrence, bound)


def _completion(authority, requirement_id):
    bound = authority.bound_contract
    return RequirementCompletionReceipt(
        authority.occurrence.cause_id.value,
        authority.occurrence.occurrence_id,
        requirement_id,
        bound.contract_definition_id,
        bound.contract_version,
        bound.bound_expression_digest,
        f"proof-{requirement_id}",
        f"applicability-{requirement_id}",
    )


def _stream(*intents, result_id="result-1"):
    recorder = EventRecorder(
        stream_id=f"stream-{result_id}",
        result_occurrence_id=result_id,
        source_snapshot_fingerprint="snapshot",
    )
    for intent in intents:
        recorder.append(intent)
    return recorder.seal()


def _run(stream, *, legacy=Outcome.UNKNOWN, terminalizations=()):
    result = run_dual_write_pilot(
        legacy_outcome=legacy,
        reducer=_environment()[2],
        stream=stream,
        terminalizations=terminalizations,
    )
    assert result.legacy_outcome_before == legacy
    assert result.legacy_outcome_after == legacy
    assert result.lifecycle_inference_count == 0
    return result


class _ObservedLegacyResult:
    def __init__(self, outcome):
        self.is_equivalent = (
            True if outcome == Outcome.EQUIVALENT
            else False if outcome == Outcome.NOT_EQ
            else None
        )
        self.error_message = "error" if outcome == Outcome.ERROR else None
        self.failure_status = None
        self.failure_message = None
        self._timeout = outcome == Outcome.TIMEOUT

    def is_timeout(self):
        return self._timeout


def _materialized_phase5_difference_manifest():
    connector = ProductionDualWritePilotConnector(_environment()[2])
    evidences = []

    def materialize(case_id, builder, *, legacy=Outcome.UNKNOWN, terminalize=()):
        session = connector.begin({"phase": 5, "case_id": case_id})
        intents = builder(session)
        for intent in intents:
            session.emit(intent)
        for sequence, requirement_id in terminalize:
            session.terminalize(sequence, requirement_id)
        evidence = connector.finish(
            session, _ObservedLegacyResult(legacy), case_id=case_id
        )
        evidences.append(evidence)
        return evidence

    def single_cause(session, *, reason_id="return_coverage_inconclusive", optional=False):
        authority = _authority(
            reason_id=reason_id,
            optional_without_requirement=optional,
            source_snapshot_fingerprint=session.identity.source_snapshot_fingerprint,
        )
        return authority

    materialize(
        "01_totality_query_timeout",
        lambda session: (
            EventIntent(EventType.CAUSE_OBSERVED, CauseObservedEventAuthority(single_cause(session))),
            EventIntent(EventType.SOLVER_TIMEOUT, SolverExecutionEventAuthority("req-A", "solver-1", "TIMEOUT", 1000)),
        ),
        terminalize=((2, "req-A"),),
    )
    materialize(
        "02_solver_unknown",
        lambda session: (
            EventIntent(EventType.CAUSE_OBSERVED, CauseObservedEventAuthority(single_cause(session))),
            EventIntent(EventType.SOLVER_UNKNOWN, SolverExecutionEventAuthority("req-A", "solver-2", "UNKNOWN")),
        ),
    )

    def fallback_unsat(session):
        authority = single_cause(session)
        return (
            EventIntent(EventType.CAUSE_OBSERVED, CauseObservedEventAuthority(authority)),
            EventIntent(EventType.SOLVER_TIMEOUT, SolverExecutionEventAuthority("req-A", "solver-3", "TIMEOUT", 1000)),
            EventIntent(EventType.REQUIREMENT_COMPLETED, RequirementCompletedEventAuthority(_completion(authority, "req-B"))),
            EventIntent(EventType.REQUIREMENT_COMPLETED, RequirementCompletedEventAuthority(_completion(authority, "req-C"))),
            EventIntent(EventType.EQ_CLOSURE, DecisiveProofEventAuthority("eq-proof-3")),
        )

    materialize(
        "03_nonterminal_timeout_fallback_unsat",
        fallback_unsat,
        legacy=Outcome.EQUIVALENT,
    )
    materialize(
        "04_nonterminal_timeout_other_blocker",
        lambda session: (
            EventIntent(EventType.CAUSE_OBSERVED, CauseObservedEventAuthority(single_cause(session))),
            EventIntent(EventType.SOLVER_TIMEOUT, SolverExecutionEventAuthority("req-A", "solver-4", "TIMEOUT", 1000)),
        ),
    )
    materialize(
        "05_residual_sat_coverage_blocker",
        lambda session: (EventIntent(
            EventType.CAUSE_OBSERVED,
            CauseObservedEventAuthority(single_cause(
                session, reason_id="outcome_partition_residual_sat"
            )),
        ),),
    )
    materialize(
        "06_process_timeout_checkpoint",
        lambda session: (
            EventIntent(EventType.CAUSE_OBSERVED, CauseObservedEventAuthority(single_cause(session))),
            EventIntent(EventType.PROCESS_TIMEOUT, ProcessExecutionEventAuthority("req-A", "process-6")),
        ),
        terminalize=((2, "req-A"),),
    )

    def frontier_case(session):
        authority = single_cause(session)
        return (
            EventIntent(EventType.CAUSE_OBSERVED, CauseObservedEventAuthority(authority)),
            EventIntent(EventType.REQUIREMENT_COMPLETED, RequirementCompletedEventAuthority(_completion(authority, "req-A"))),
        )

    materialize("07_any_of_all_of_frontier", frontier_case)

    def refinement_case(session):
        old = _authority(
            "old", prefix="old",
            source_snapshot_fingerprint=session.identity.source_snapshot_fingerprint,
        )
        news = tuple(_authority(
            f"new-{index}", prefix=f"new-{index}",
            source_snapshot_fingerprint=session.identity.source_snapshot_fingerprint,
        ) for index in range(2))
        event = CauseTransformationEvent(
            TransformationKind.REFINEMENT,
            ("old",),
            tuple(item.occurrence.occurrence_id for item in news),
            "manifest-refinement", "outcome-totality",
            session.identity.source_snapshot_fingerprint,
        )
        proof = CauseTransformationProofReceipt(
            "manifest-refinement",
            (("old", old.occurrence.cause_id.value),),
            tuple((item.occurrence.occurrence_id, item.occurrence.cause_id.value) for item in news),
            (), session.identity.source_snapshot_fingerprint, False,
        )
        return tuple(
            EventIntent(EventType.CAUSE_OBSERVED, CauseObservedEventAuthority(item))
            for item in (old, *news)
        ) + (EventIntent(
            EventType.CAUSE_TRANSFORMED,
            CauseTransformedEventAuthority(event, proof),
        ),)

    materialize("08_refinement_and_coalescence", refinement_case)
    materialize(
        "09_one_cause_multiple_requirements",
        lambda session: (EventIntent(
            EventType.CAUSE_OBSERVED,
            CauseObservedEventAuthority(single_cause(session)),
        ),),
    )
    materialize(
        "10_optional_unmaterialized_requirement",
        lambda session: (EventIntent(
            EventType.CAUSE_OBSERVED,
            CauseObservedEventAuthority(single_cause(
                session, reason_id="return_coverage_gap", optional=True
            )),
        ),),
    )

    def timeout_without_open(session):
        authority = single_cause(session)
        return (
            EventIntent(EventType.CAUSE_OBSERVED, CauseObservedEventAuthority(authority)),
            EventIntent(EventType.SOLVER_TIMEOUT, SolverExecutionEventAuthority("req-A", "solver-11", "TIMEOUT", 1000)),
            EventIntent(EventType.REQUIREMENT_COMPLETED, RequirementCompletedEventAuthority(_completion(authority, "req-A"))),
            EventIntent(EventType.REQUIREMENT_COMPLETED, RequirementCompletedEventAuthority(_completion(authority, "req-C"))),
        )

    materialize(
        "11_timeout_without_open_requirement",
        timeout_without_open,
        terminalize=((2, "req-A"),),
    )

    def arrival_order(session):
        first = _authority(
            "first", prefix="first",
            source_snapshot_fingerprint=session.identity.source_snapshot_fingerprint,
        )
        second = _authority(
            "second", prefix="second",
            source_snapshot_fingerprint=session.identity.source_snapshot_fingerprint,
        )
        return (
            EventIntent(EventType.CAUSE_OBSERVED, CauseObservedEventAuthority(second)),
            EventIntent(EventType.CAUSE_OBSERVED, CauseObservedEventAuthority(first)),
        )

    materialize("12_independent_arrival_order", arrival_order)
    materialize(
        "13_invalid_manifest_entry",
        lambda session: (EventIntent(
            EventType.CAUSE_OBSERVED,
            CauseObservedEventAuthority(single_cause(session)),
        ),),
    )
    manifest = PilotDifferenceManifest.seal(
        "unknown-taxonomy-v2-phase5-production-pilot",
        tuple(evidence.difference_entry for evidence in evidences),
    )
    return {
        "typed_difference_manifest": manifest.to_dict(),
        "legacy_outcome_observation_receipts": [
            evidence.legacy_observation_receipt.to_dict()
            for evidence in sorted(
                evidences,
                key=lambda item: item.difference_entry.case_id,
            )
        ],
    }


def test_totality_query_timeout_is_terminal_only_with_explicit_terminalization():
    authority = _authority()
    stream = _stream(
        EventIntent(EventType.CAUSE_OBSERVED, CauseObservedEventAuthority(authority)),
        EventIntent(
            EventType.SOLVER_TIMEOUT,
            SolverExecutionEventAuthority("req-A", "solver-1", "TIMEOUT", 1000),
        ),
    )
    result = _run(
        stream,
        terminalizations=(TerminalizationIntent(2, "req-A"),),
    )
    assert result.candidate.decision_receipt.outcome == Outcome.TIMEOUT
    assert result.attempted_requirement_identity_coverage == 1.0
    assert result.terminal_timeout_receipt_count == 1


def test_solver_unknown_is_unknown_and_never_creates_a_timeout_reason():
    authority = _authority()
    result = _run(_stream(
        EventIntent(EventType.CAUSE_OBSERVED, CauseObservedEventAuthority(authority)),
        EventIntent(
            EventType.SOLVER_UNKNOWN,
            SolverExecutionEventAuthority("req-A", "solver-1", "UNKNOWN"),
        ),
    ))
    assert result.candidate.decision_receipt.outcome == Outcome.UNKNOWN
    assert result.attempted_requirement_identity_coverage == 1.0
    assert {row.reason_id for row in result.reduction.projection.c_active_base} == {
        "return_coverage_inconclusive"
    }


def test_nonterminal_timeout_then_alternative_unsat_closes_to_equivalent():
    authority = _authority()
    result = _run(_stream(
        EventIntent(EventType.CAUSE_OBSERVED, CauseObservedEventAuthority(authority)),
        EventIntent(
            EventType.SOLVER_TIMEOUT,
            SolverExecutionEventAuthority("req-A", "solver-1", "TIMEOUT", 1000),
        ),
        EventIntent(
            EventType.REQUIREMENT_COMPLETED,
            RequirementCompletedEventAuthority(_completion(authority, "req-B")),
        ),
        EventIntent(
            EventType.REQUIREMENT_COMPLETED,
            RequirementCompletedEventAuthority(_completion(authority, "req-C")),
        ),
        EventIntent(EventType.EQ_CLOSURE, DecisiveProofEventAuthority("eq-proof")),
    ), legacy=Outcome.EQUIVALENT)
    assert result.candidate.decision_receipt.outcome == Outcome.EQUIVALENT
    assert result.observed_nonterminal_timeout_event_count == 1
    assert result.terminal_timeout_receipt_count == 0


def test_nonterminal_timeout_then_different_active_blocker_is_unknown():
    first = _authority("first", prefix="first")
    second = _authority("second", prefix="second", reason_id="return_coverage_gap")
    result = _run(_stream(
        EventIntent(EventType.CAUSE_OBSERVED, CauseObservedEventAuthority(first)),
        EventIntent(
            EventType.SOLVER_TIMEOUT,
            SolverExecutionEventAuthority("first-A", "solver-1", "TIMEOUT", 1000),
        ),
        EventIntent(
            EventType.REQUIREMENT_COMPLETED,
            RequirementCompletedEventAuthority(_completion(first, "first-A")),
        ),
        EventIntent(
            EventType.REQUIREMENT_COMPLETED,
            RequirementCompletedEventAuthority(_completion(first, "first-C")),
        ),
        EventIntent(EventType.CAUSE_OBSERVED, CauseObservedEventAuthority(second)),
    ))
    assert result.candidate.decision_receipt.outcome == Outcome.UNKNOWN
    assert {row.occurrence_id for row in result.reduction.projection.c_active_base} == {
        "second"
    }


def test_residual_sat_is_a_semantic_coverage_blocker():
    authority = _authority(reason_id="outcome_partition_residual_sat")
    result = _run(_stream(EventIntent(
        EventType.CAUSE_OBSERVED, CauseObservedEventAuthority(authority)
    )))
    assert result.candidate.decision_receipt.outcome == Outcome.UNKNOWN
    assert result.reduction.projection.c_active_base[0].reason_id == (
        "outcome_partition_residual_sat"
    )


def test_process_timeout_with_checkpointed_live_requirement_is_timeout():
    authority = _authority()
    result = _run(
        _stream(
            EventIntent(
                EventType.CAUSE_OBSERVED,
                CauseObservedEventAuthority(authority),
            ),
            EventIntent(
                EventType.PROCESS_TIMEOUT,
                ProcessExecutionEventAuthority("req-A", "process-1"),
            ),
        ),
        terminalizations=(TerminalizationIntent(2, "req-A"),),
    )
    assert result.candidate.decision_receipt.outcome == Outcome.TIMEOUT


@pytest.mark.parametrize(
    ("completed", "expected_live"),
    (
        ((), {"req-A", "req-B", "req-C"}),
        (("req-A",), {"req-C"}),
        (("req-B",), {"req-C"}),
        (("req-C",), {"req-A", "req-B"}),
        (("req-A", "req-C"), set()),
        (("req-B", "req-C"), set()),
    ),
)
def test_pilot_live_frontier_for_any_of_and_all_of(completed, expected_live):
    authority = _authority()
    intents = [EventIntent(
        EventType.CAUSE_OBSERVED, CauseObservedEventAuthority(authority)
    )]
    intents.extend(
        EventIntent(
            EventType.REQUIREMENT_COMPLETED,
            RequirementCompletedEventAuthority(_completion(authority, requirement_id)),
        )
        for requirement_id in completed
    )
    result = _run(_stream(*intents))
    assert {row.proof_requirement_id for row in result.reduction.projection.q_open_base} == expected_live


@pytest.mark.parametrize(
    ("old_count", "new_count", "kind"),
    (
        (1, 2, TransformationKind.REFINEMENT),
        (2, 1, TransformationKind.COALESCENCE),
    ),
)
def test_pilot_atomic_refinement_and_coalescence(old_count, new_count, kind):
    olds = tuple(_authority(f"old-{i}", prefix=f"old-{i}") for i in range(old_count))
    news = tuple(_authority(f"new-{i}", prefix=f"new-{i}") for i in range(new_count))
    event = CauseTransformationEvent(
        kind,
        tuple(item.occurrence.occurrence_id for item in olds),
        tuple(item.occurrence.occurrence_id for item in news),
        "pilot-transform", "outcome-totality", "snapshot",
    )
    proof = CauseTransformationProofReceipt(
        "pilot-transform",
        tuple((item.occurrence.occurrence_id, item.occurrence.cause_id.value) for item in olds),
        tuple((item.occurrence.occurrence_id, item.occurrence.cause_id.value) for item in news),
        (), "snapshot", False,
    )
    intents = [
        EventIntent(EventType.CAUSE_OBSERVED, CauseObservedEventAuthority(item))
        for item in (*olds, *news)
    ]
    intents.append(EventIntent(
        EventType.CAUSE_TRANSFORMED,
        CauseTransformedEventAuthority(event, proof),
    ))
    result = _run(_stream(*intents))
    assert {row.occurrence_id for row in result.reduction.projection.c_active_base} == {
        item.occurrence.occurrence_id for item in news
    }


def test_one_cause_with_multiple_requirements_is_not_duplicate_cause_counting():
    authority = _authority()
    result = _run(_stream(EventIntent(
        EventType.CAUSE_OBSERVED, CauseObservedEventAuthority(authority)
    )))
    assert len(result.reduction.projection.c_active_base) == 1
    assert len(result.reduction.projection.q_open_base) == 3
    assert len(result.candidate.active_cause_ids) == 1


def test_active_optional_semantic_cause_may_have_no_materialized_requirement():
    authority = _authority(
        reason_id="return_coverage_gap",
        optional_without_requirement=True,
    )
    result = _run(_stream(EventIntent(
        EventType.CAUSE_OBSERVED, CauseObservedEventAuthority(authority)
    )))
    assert len(result.reduction.projection.c_active_base) == 1
    assert result.reduction.projection.q_open_base == ()
    assert result.candidate.decision_receipt.outcome == Outcome.UNKNOWN


def test_terminal_timeout_with_no_final_open_requirement_is_rejected_as_error():
    authority = _authority()
    result = _run(
        _stream(
            EventIntent(
                EventType.CAUSE_OBSERVED,
                CauseObservedEventAuthority(authority),
            ),
            EventIntent(
                EventType.SOLVER_TIMEOUT,
                SolverExecutionEventAuthority("req-A", "solver-1", "TIMEOUT", 1000),
            ),
            EventIntent(
                EventType.REQUIREMENT_COMPLETED,
                RequirementCompletedEventAuthority(_completion(authority, "req-A")),
            ),
            EventIntent(
                EventType.REQUIREMENT_COMPLETED,
                RequirementCompletedEventAuthority(_completion(authority, "req-C")),
            ),
        ),
        terminalizations=(TerminalizationIntent(2, "req-A"),),
    )
    assert result.candidate.decision_receipt.outcome == Outcome.ERROR
    assert result.candidate.decision_receipt.outcome != Outcome.TIMEOUT


def test_independent_cause_arrival_order_has_equal_semantic_projection():
    first = _authority("first", prefix="first")
    second = _authority("second", prefix="second")
    left = _run(_stream(
        EventIntent(EventType.CAUSE_OBSERVED, CauseObservedEventAuthority(first)),
        EventIntent(EventType.CAUSE_OBSERVED, CauseObservedEventAuthority(second)),
    ))
    right = _run(_stream(
        EventIntent(EventType.CAUSE_OBSERVED, CauseObservedEventAuthority(second)),
        EventIntent(EventType.CAUSE_OBSERVED, CauseObservedEventAuthority(first)),
    ))
    assert left.reduction.projection.semantic_cause_projection_digest == (
        right.reduction.projection.semantic_cause_projection_digest
    )
    assert left.reduction.projection.c_active_base == right.reduction.projection.c_active_base
    assert left.reduction.projection.q_open_base == right.reduction.projection.q_open_base


def test_invalid_manifest_entry_invalidates_entire_pilot_census():
    authority = _authority()
    result = _run(_stream(EventIntent(
        EventType.CAUSE_OBSERVED, CauseObservedEventAuthority(authority)
    )))
    entry = CensusEntry(
        "result-1", ResultKind.V2_NATIVE, ("return_outcome",),
        ("left", "right"), ("f", "f"),
        result.reduction.snapshot.event_stream_authority_digest,
        result.reduction.projection.lifecycle_projection_digest,
        result.candidate.decision_receipt.receipt_digest,
        "artifact",
    )
    manifest = CensusManifest(
        "phase5", CensusMode.V2_CANONICAL, "head", "config", (entry,)
    )
    row = result.reduction.projection.c_active_base[0]
    coverage = CoverageInputs((ActiveOccurrenceMaterialization(
        row.result_occurrence_id,
        row.occurrence_id,
        row.cause_id,
        RecoveryAddressability.REQUIREMENT_REQUIRED,
    ),))
    invalid = build_shadow_census_preview(
        CensusManifest(
            "tampered", CensusMode.V2_CANONICAL, "head", "config",
            (replace(entry, lifecycle_projection_digest="wrong"),),
        ),
        (result.candidate,),
        (result.reduction.projection,),
        (result.sealed_event_stream,),
        coverage_inputs=coverage,
    )
    assert invalid.status == CensusStatus.INVALID
    assert invalid.canonical_metrics is None


def test_pilot_scope_excludes_timeout_diagnostics_as_semantic_reasons():
    assert "solver_unknown_timeout" not in PILOT_TYPED_CAUSE_KINDS
    assert "outcome_partition_totality_timeout" not in PILOT_TYPED_CAUSE_KINDS
    assert "outcome_partition_unknown" not in PILOT_TYPED_CAUSE_KINDS


def test_difference_manifest_binds_each_unique_result_and_rejects_duplicates():
    first = _run(_stream(
        EventIntent(
            EventType.CAUSE_OBSERVED,
            CauseObservedEventAuthority(_authority("first", prefix="first")),
        ),
        result_id="case-first",
    ))
    second = _run(_stream(
        EventIntent(
            EventType.CAUSE_OBSERVED,
            CauseObservedEventAuthority(_authority("second", prefix="second")),
        ),
        result_id="case-second",
    ))
    rows = (
        PilotDifferenceEntry.create(
            "first", first,
            legacy_outcome_observation_receipt_digest="legacy-first",
        ),
        PilotDifferenceEntry.create(
            "second", second,
            legacy_outcome_observation_receipt_digest="legacy-second",
        ),
    )
    manifest = PilotDifferenceManifest.seal("phase5", rows)
    manifest.validate()
    with pytest.raises(ValueError, match="duplicate pilot difference case"):
        PilotDifferenceManifest.seal("phase5", (rows[0], rows[0]))
    forged = replace(rows[0], candidate_outcome=Outcome.ERROR)
    with pytest.raises(ValueError, match="entry digest"):
        forged.validate()


def test_saved_difference_manifest_is_digest_and_source_bound():
    path = Path("artifacts/unknown_taxonomy_v2/phase5/difference_manifest.json")
    payload = json.loads(path.read_text(encoding="utf-8"))
    saved_digest = payload.pop("manifest_digest")
    assert authority_digest(payload) == saved_digest
    regenerated = _materialized_phase5_difference_manifest()
    assert payload["typed_difference_manifest"] == regenerated["typed_difference_manifest"]
    assert payload["legacy_outcome_observation_receipts"] == (
        regenerated["legacy_outcome_observation_receipts"]
    )
    assert len(regenerated["typed_difference_manifest"]["entries"]) == 13
    for source, expected in payload["files"].items():
        assert hashlib.sha256(Path(source).read_bytes()).hexdigest() == expected


def test_pilot_receipt_validation_rederives_coverage_and_v1_preservation():
    authority = _authority()
    result = _run(_stream(
        EventIntent(EventType.CAUSE_OBSERVED, CauseObservedEventAuthority(authority)),
        EventIntent(
            EventType.SOLVER_UNKNOWN,
            SolverExecutionEventAuthority("req-A", "solver-1", "UNKNOWN"),
        ),
    ))
    with pytest.raises(ValueError, match="attempted solver event count"):
        replace(result, attempted_solver_event_count=2).validate()
    with pytest.raises(ValueError, match="changed the v1 final outcome"):
        replace(result, legacy_outcome_after=Outcome.ERROR).validate()


def test_production_evidence_rejects_cross_bound_valid_receipt_and_entry():
    connector = ProductionDualWritePilotConnector(_environment()[2])

    def materialize(case_id):
        session = connector.begin({"cross_bound_case": case_id})
        session.emit(EventIntent(
            EventType.CAUSE_OBSERVED,
            CauseObservedEventAuthority(_authority(
                occurrence_id=f"occ-{case_id}",
                prefix=case_id,
                source_snapshot_fingerprint=session.identity.source_snapshot_fingerprint,
            )),
        ))
        return connector.finish(
            session, _ObservedLegacyResult(Outcome.UNKNOWN), case_id=case_id
        )

    first = materialize("first")
    second = materialize("second")
    forged_entry = PilotDifferenceEntry.create(
        "forged",
        first.pilot_result,
        legacy_outcome_observation_receipt_digest=(
            second.legacy_observation_receipt.receipt_digest
        ),
    )
    forged = ProductionDualWriteEvidence(
        first.pilot_result,
        second.legacy_observation_receipt,
        forged_entry,
    )
    with pytest.raises(ValueError, match="observation result differs"):
        forged.validate()


def test_real_outcome_partition_producer_emits_typed_signal_without_monkeypatch():
    observed = []

    def authority_for_signal(session, signal):
        assert isinstance(signal, OutcomePartitionProductionSignal)
        observed.append(signal)
        return _authority(
            occurrence_id=f"outcome-{signal.stage}",
            prefix="production-outcome",
            target_key=signal.outcome_seed_digest,
            source_snapshot_fingerprint=session.identity.source_snapshot_fingerprint,
        )

    connector = ProductionDualWritePilotConnector(
        _environment()[2],
        domain_signal_encoder=OutcomePartitionPilotEncoder(authority_for_signal),
    )
    session = connector.begin({"production_fixture": "outcome_partition"})
    seed = SimpleNamespace(
        function_identity=("function", "bin-a", 0x1000),
        input_domain_contract=("all_inputs",),
        partition_revision=1,
        extraction_schema_version=1,
        stable_key=lambda: ("production-outcome-seed",),
    )
    analysis = SimpleNamespace(
        function_name="f",
        entry_point="0x1000",
        binary_id="bin-a",
        outcome_seed=seed,
    )
    producers = {
        stage: (lambda: UnaryProducerResult("unknown", {"solver_status": "unknown"}))
        for stage in (
            "termination_classification", "cfg_reachability",
            "path_region_completeness", "member_classification",
            "same_kind_consistency", "cross_kind_disjointness",
            "residual_totality", "partition_complete",
        )
    }
    with production_signal_scope(session):
        proof = prove_unary_partition(
            analysis,
            domain_contract=("all_inputs",),
            normalization_policy_digest="production-fixture-v1",
            producers=producers,
        )
    evidence = connector.finish(
        session,
        _ObservedLegacyResult(Outcome.UNKNOWN),
        case_id="real-outcome-producer",
    )
    assert proof.status == "unknown"
    assert proof.blocker_kind == "outcome_termination_classification_unknown"
    assert session.observed_domain_signal_count == 1
    assert len(observed) == 1
    assert observed[0].stage == "termination_classification"
    assert observed[0].producer_status == "unknown"
    assert observed[0].proof_requirement_identity["proof_kind"] == (
        "unary_outcome_termination_classification"
    )
    assert observed[0].producer_evidence == {"solver_status": "unknown"}
    evidence.validate()
    assert len(evidence.pilot_result.sealed_event_stream.events) == 1
    assert evidence.pilot_result.candidate.decision_receipt.outcome == Outcome.UNKNOWN


def test_inconclusive_comparison_materializes_receipt_bound_typed_backlog():
    connector = ProductionDualWritePilotConnector(
        ShadowLifecycleReducer(
            reason_registry=PROCESS_DURABLE_REASON_REGISTRY,
            recovery_registry=PROCESS_DURABLE_RECOVERY_REGISTRY,
        ),
        domain_signal_encoder=CompositeProductionSignalEncoder({
            ComparisonClosureProductionSignal: ComparisonClosurePilotEncoder(),
        }),
    )
    session = connector.begin({"production_fixture": "comparison-inconclusive"})
    signal = ComparisonClosureProductionSignal(
        comparison_receipt_id="comparison-receipt",
        terminal_receipt_digest="terminal-receipt",
        branch_id="S_MONOLITHIC_FALLBACK",
        runtime_premise_digest="runtime-premise",
        runtime_view_id=("derived-view", "pair"),
        query_receipt_digests=("query-receipt",),
    )
    with production_signal_scope(session):
        assert emit_comparison_closure_signal(signal) == 1
    evidence = connector.finish(
        session,
        _ObservedLegacyResult(Outcome.UNKNOWN),
        case_id="comparison-inconclusive",
    )
    projection = evidence.pilot_result.reduction.projection
    assert evidence.pilot_result.candidate.decision_receipt.outcome is Outcome.UNKNOWN
    assert len(projection.c_active_base) == 1
    assert len(projection.q_open_base) == 1
    assert projection.c_active_base[0].reason_id == (
        "comparison_equivalence_closure_unproven"
    )


def test_production_signal_encoder_failure_is_shadow_only_and_fail_closed():
    def broken_encoder(_session, _signal):
        raise RuntimeError("shadow encoder failure")

    connector = ProductionDualWritePilotConnector(
        _environment()[2], domain_signal_encoder=broken_encoder
    )
    session = connector.begin({"production_fixture": "broken_encoder"})
    signal = OutcomePartitionProductionSignal(
        stage="residual_totality",
        producer_status="unknown",
        proof_requirement_identity={"proof_kind": "unary_outcome_residual_totality"},
        function_identity=("function", "bin", 1),
        outcome_seed_digest="seed-digest",
        producer_evidence={},
    )
    assert session.emit_domain_signal(signal) == 0
    assert session.domain_signal_error_kinds == ["RuntimeError"]
    result = _ObservedLegacyResult(Outcome.UNKNOWN)
    with pytest.raises(ValueError, match="signal encoding is incomplete"):
        connector.finish(session, result, case_id="broken-encoder")
    assert result.is_equivalent is None


def test_terminalization_must_bind_one_exact_recorded_timeout_requirement():
    authority = _authority()
    stream = _stream(
        EventIntent(EventType.CAUSE_OBSERVED, CauseObservedEventAuthority(authority)),
        EventIntent(
            EventType.SOLVER_TIMEOUT,
            SolverExecutionEventAuthority("req-A", "solver-1", "TIMEOUT", 1000),
        ),
    )
    with pytest.raises(ValueError, match="differs from timeout event"):
        _run(stream, terminalizations=(TerminalizationIntent(2, "req-B"),))
    with pytest.raises(ValueError, match="duplicate terminalization"):
        _run(stream, terminalizations=(
            TerminalizationIntent(2, "req-A"),
            TerminalizationIntent(2, "req-A"),
        ))
    with pytest.raises(ValueError, match="does not reference a timeout"):
        _run(stream, terminalizations=(TerminalizationIntent(1, "req-A"),))


def test_production_binary_boundary_legacy_opt_out_and_cutover_fail_closed(monkeypatch):
    def fake_run(checker, *_args, **_kwargs):
        session = getattr(checker, "_active_v2_dual_write_pilot_session", None)
        if session is not None:
            authority = _authority(
                source_snapshot_fingerprint=(
                    session.identity.source_snapshot_fingerprint
                )
            )
            checker.emit_v2_dual_write_pilot_event(EventIntent(
                EventType.CAUSE_OBSERVED,
                CauseObservedEventAuthority(authority),
            ))
            sequence = checker.emit_v2_dual_write_pilot_event(EventIntent(
                EventType.SOLVER_TIMEOUT,
                SolverExecutionEventAuthority(
                    "req-A", "production-solver", "TIMEOUT", 1000
                ),
            ))
            checker.terminalize_v2_dual_write_pilot_timeout(sequence, "req-A")
        return EquivalenceResult(
            is_equivalent=None,
            function1_name="f",
            function2_name="f",
            binary1_name="left",
            binary2_name="right",
            solver_results=ParallelResult(results=[]),
        )

    monkeypatch.setattr(
        "scripts.function_tracer_pcode.equivalence.v2.production_boundary._run_legacy_check_from_binaries",
        fake_run,
    )
    default_checker = EquivalenceChecker(canonical_decision_cutover=False)
    default_result = default_checker.check_from_binaries(None, None, "f", "f")
    assert default_result.is_equivalent is None
    assert not hasattr(default_result, "v2_dual_write_pilot")
    assert "v2_dual_write_pilot" not in default_result.to_dict()

    connector = ProductionDualWritePilotConnector(_environment()[2])
    enabled_checker = EquivalenceChecker()
    enabled_checker.v2_dual_write_pilot_connector = connector
    enabled_result = enabled_checker.check_from_binaries(
        None,
        None,
        "f",
        "f",
        binary1_id="left-id",
        binary2_id="right-id",
        binary1_content_identity=("sha256", "left"),
        binary2_content_identity=("sha256", "right"),
    )
    evidence = enabled_result._v2_dual_write_evidence
    evidence.validate()
    assert enabled_result.final_outcome == "TIMEOUT"
    assert evidence.legacy_observation_receipt.before_outcome == Outcome.UNKNOWN
    assert evidence.legacy_observation_receipt.after_outcome == Outcome.UNKNOWN
    assert evidence.legacy_observation_receipt.before_surface_digest == (
        evidence.legacy_observation_receipt.after_surface_digest
    )
    assert evidence.pilot_result.candidate.decision_receipt.outcome == Outcome.TIMEOUT
    assert enabled_result.v2_dual_write_pilot["non_authoritative_shadow"] is False

    def no_emission(_checker, *_args, **_kwargs):
        return EquivalenceResult(
            is_equivalent=True,
            function1_name="f",
            function2_name="f",
            binary1_name="left",
            binary2_name="right",
            solver_results=ParallelResult(results=[]),
        )

    monkeypatch.setattr(
        "scripts.function_tracer_pcode.equivalence.v2.production_boundary._run_legacy_check_from_binaries",
        no_emission,
    )
    incomplete_checker = EquivalenceChecker()
    incomplete_checker.v2_dual_write_pilot_connector = connector
    incomplete = incomplete_checker.check_from_binaries(None, None, "f", "f")
    assert incomplete.is_equivalent is None
    assert incomplete.final_outcome == "ERROR"
    assert incomplete.v2_dual_write_pilot["status"] == "SHADOW_EVIDENCE_INCOMPLETE"
