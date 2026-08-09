# -*- coding: utf-8 -*-

from unittest.mock import Mock
from dataclasses import replace
import hashlib
import json
from pathlib import Path

import pytest

from scripts.function_tracer_pcode.equivalence.obligations.pair_disposition import (
    CounterexampleSafetyReceipt,
    emit_safe_counterexample_production_signal,
)
from scripts.function_tracer_pcode.equivalence.strategies.pairwise import PairwiseStrategy
from scripts.function_tracer_pcode.equivalence.v2.contracts import Outcome
from scripts.function_tracer_pcode.model import (
    Expression,
    FunctionReturnAnalysis,
    ReturnInfo,
)
from scripts.function_tracer_pcode.equivalence.v2.pilot import (
    ProductionDualWritePilotConnector,
)
from scripts.function_tracer_pcode.equivalence.v2.production_signals import (
    SafeCounterexampleProductionSignal,
    SatCounterexampleEvidenceBinding,
    SatSafetyBlockerProductionSignal,
    complete_observed_sat_safety_for_counterexample,
    emit_sat_safety_completion_if_observed,
    emit_sat_safety_signal,
    production_signal_scope,
)
from scripts.function_tracer_pcode.equivalence.v2.reducer import ShadowLifecycleReducer
from scripts.function_tracer_pcode.equivalence.v2.sat_safety import (
    SAT_SAFETY_REASON_REGISTRY,
    SAT_SAFETY_RECOVERY_REGISTRY,
    SatSafetyPilotEncoder,
)
from scripts.function_tracer_pcode.tests.unit.test_phase3_sat_unsafety_lane5 import _case
from scripts.function_tracer_pcode.validation.unknown_taxonomy_audit import (
    build_inventory_review_template,
)


class _LegacyResult:
    def __init__(self, outcome):
        self.is_equivalent = False if outcome == Outcome.NOT_EQ else None
        self.error_message = None
        self.failure_status = None
        self.failure_message = None

    def is_timeout(self):
        return False


def _connector():
    return ProductionDualWritePilotConnector(
        ShadowLifecycleReducer(
            reason_registry=SAT_SAFETY_REASON_REGISTRY,
            recovery_registry=SAT_SAFETY_RECOVERY_REGISTRY,
        ),
        domain_signal_encoder=SatSafetyPilotEncoder(),
    )


def _manifest_connector():
    from scripts.function_tracer_pcode.equivalence.v2.phase7_runtime import (
        runtime_from_audited_manifest,
    )
    from scripts.function_tracer_pcode.equivalence.v2.production_signals import (
        CompositeProductionSignalEncoder,
    )
    from scripts.function_tracer_pcode.validation.phase7_producer_manifest import (
        build_phase7_producer_manifest,
    )

    root = Path(__file__).resolve().parents[4]
    manifest = build_phase7_producer_manifest(root)
    encoder = SatSafetyPilotEncoder()
    return ProductionDualWritePilotConnector(
        ShadowLifecycleReducer(
            reason_registry=SAT_SAFETY_REASON_REGISTRY,
            recovery_registry=SAT_SAFETY_RECOVERY_REGISTRY,
        ),
        domain_signal_encoder=CompositeProductionSignalEncoder({
            SatSafetyBlockerProductionSignal: encoder,
            SafeCounterexampleProductionSignal: encoder,
        }),
        phase7_runtime_factory=lambda identity: runtime_from_audited_manifest(
            manifest, identity
        ),
    )


def _strategy_and_surface():
    strategy = PairwiseStrategy(Mock(), Mock(), debug=False)
    strategy.enable_completed_recovery_proofs = True
    analysis1, case1 = _case("B10", 0x1000, 0)
    analysis2, case2 = _case("B9", 0x2000, 1)
    return strategy, analysis1, analysis2, case1, case2


def _safe_pairwise_receipt(
    *, query="(assert distinct)\n(check-sat)", model=None,
    premise="typed-premise", pair_key=(0, 1),
):
    return CounterexampleSafetyReceipt.from_pairwise_validation(
        query=query,
        model={"x": 1} if model is None else model,
        premise_digest=premise,
        pair_key=pair_key,
        analysis_safe=True,
        global_case_replay_safe=True,
        same_function_replay_safe=True,
    )


def test_sat_observation_without_safety_completion_remains_unknown():
    connector = _connector()
    session = connector.begin({"phase": "10", "case": "sat-safety-open"})
    signal = SatSafetyBlockerProductionSignal(
        action="OBSERVED",
        reason_id="counterexample_analysis_safety_unproven",
        canonical_target_key=("model-bound-near-miss",),
        missing_semantic_fact=("counterexample_safety_gate_unproven", "model"),
        evidence_refs=("sat-model-requires-safety-replay",),
        producer_id="phase10-high-bit-sat-transform",
    )
    with production_signal_scope(session):
        assert emit_sat_safety_signal(signal) == 1
    evidence = connector.finish(
        session, _LegacyResult(Outcome.UNKNOWN), case_id="sat-safety-open"
    )
    assert evidence.pilot_result.candidate.decision_receipt.outcome is Outcome.UNKNOWN
    assert {
        row.reason_id for row in evidence.pilot_result.reduction.projection.c_active_base
    } == {"counterexample_analysis_safety_unproven"}
    assert {
        row.proof_kind for row in evidence.pilot_result.reduction.projection.q_open_base
    } == {"counterexample_safety"}


def test_shared_typed_safe_counterexample_signal_promotes_not_eq():
    connector = _connector()
    session = connector.begin({"phase": "monolithic", "case": "safe-sat"})
    receipt = _safe_pairwise_receipt()
    retry_receipt = _safe_pairwise_receipt(
        query="(assert (= x 2))\n(check-sat)", model={"x": 2},
        premise="retry-premise", pair_key=(1, 2),
    )
    with production_signal_scope(session):
        assert emit_safe_counterexample_production_signal(
            safety_receipt=receipt,
        ) == 1
        assert emit_safe_counterexample_production_signal(
            safety_receipt=retry_receipt,
        ) == 0
    evidence = connector.finish(
        session, _LegacyResult(Outcome.NOT_EQ), case_id="monolithic-safe-sat"
    )
    assert evidence.pilot_result.candidate.decision_receipt.outcome is Outcome.NOT_EQ
    assert [
        event.header.event_type.value
        for event in evidence.pilot_result.sealed_event_stream.events
    ] == ["COUNTEREXAMPLE"]


def test_safe_independent_counterexample_discards_deferred_pairwise_blockers():
    connector = _connector()
    session = connector.begin({"phase": "pairwise-fallback", "case": "safe-sat"})
    strategy, analysis1, analysis2, case1, case2 = _strategy_and_surface()
    pairwise_binding = SatCounterexampleEvidenceBinding(
        "1" * 64, "2" * 64, "3" * 64, (0, 1)
    )
    receipt = _safe_pairwise_receipt(
        query="(assert distinct)\n(check-sat)", model={"x": 7},
        premise="monolithic-independent", pair_key=("monolithic", "region:0"),
    )
    with production_signal_scope(session):
        strategy._make_sat_unsafety_unknown_reason(
            ("function1:incomplete_control_flow",),
            analysis1,
            analysis2,
            case1=case1,
            case2=case2,
            pair_id="(0,1)",
            stage="S_PAIRWISE",
            counterexample_binding=pairwise_binding,
        )
        assert session.recorder.event_count == 0
        assert emit_safe_counterexample_production_signal(
            safety_receipt=receipt,
        ) == 1
    evidence = connector.finish(
        session, _LegacyResult(Outcome.NOT_EQ), case_id="safe-independent-sat"
    )
    assert [
        event.header.event_type.value
        for event in evidence.pilot_result.sealed_event_stream.events
    ] == ["COUNTEREXAMPLE"]
    assert evidence.pilot_result.reduction.projection.c_active_base == ()
    assert evidence.pilot_result.reduction.projection.q_open_base == ()
    assert evidence.pilot_result.candidate.decision_receipt.outcome is Outcome.NOT_EQ


def test_same_case_pair_different_sat_bindings_are_distinct_occurrences():
    connector = _connector()
    session = connector.begin({"phase": "pairwise", "case": "two-sat-attempts"})
    strategy, analysis1, analysis2, case1, case2 = _strategy_and_surface()
    bindings = (
        SatCounterexampleEvidenceBinding(
            "1" * 64, "2" * 64, "3" * 64, (0, 1)
        ),
        SatCounterexampleEvidenceBinding(
            "4" * 64, "5" * 64, "6" * 64, (0, 1)
        ),
    )
    with production_signal_scope(session):
        for binding in bindings:
            strategy._make_sat_unsafety_unknown_reason(
                ("function1:incomplete_control_flow",),
                analysis1,
                analysis2,
                case1=case1,
                case2=case2,
                pair_id="(0,1)",
                stage="S_PAIRWISE",
                counterexample_binding=binding,
            )
    assert len(session.domain_signal_state["sat_safety_deferred_observations"]) == 2
    evidence = connector.finish(
        session, _LegacyResult(Outcome.UNKNOWN), case_id="two-sat-attempts"
    )
    assert len(evidence.pilot_result.reduction.projection.c_active_base) == 2
    assert len(evidence.pilot_result.reduction.projection.q_open_base) == 2
    assert evidence.pilot_result.candidate.decision_receipt.outcome is Outcome.UNKNOWN


def test_same_function_multiple_sat_pairs_complete_only_the_exact_occurrence():
    connector = _connector()
    session = connector.begin({"phase": "10", "case": "safe-sat-closes-open"})
    receipt = _safe_pairwise_receipt(
        query="(assert (= x 1))\n(check-sat)", model={"x": 1},
        premise="region-zero", pair_key=("monolithic", "region:0"),
    )
    safe_signal = SafeCounterexampleProductionSignal.from_pairwise_receipt(receipt)
    binding = safe_signal.counterexample_binding
    unrelated_receipt = _safe_pairwise_receipt(
        query="(assert (= x 2))\n(check-sat)", model={"x": 2},
        premise="region-one", pair_key=("monolithic", "region:1"),
    )
    unrelated_binding = (
        SafeCounterexampleProductionSignal.from_pairwise_receipt(
            unrelated_receipt
        ).counterexample_binding
    )
    observed = SatSafetyBlockerProductionSignal(
        action="OBSERVED",
        reason_id="counterexample_analysis_safety_unproven",
        canonical_target_key=(
            "legacy-case", ("pair", "region:0"), ("function", "left", 1),
            ("function", "right", 2), ("safety_gate_ref", "return"),
        ),
        missing_semantic_fact=("counterexample_safety_gate_unproven", "return"),
        evidence_refs=("return",),
        producer_id="phase10-high-bit-sat-transform",
        counterexample_binding=binding,
    )
    unrelated = SatSafetyBlockerProductionSignal(
        action="OBSERVED",
        reason_id="counterexample_analysis_safety_unproven",
        canonical_target_key=(
            "legacy-case", ("pair", "region:1"), ("function", "left", 1),
            ("function", "right", 2), ("safety_gate_ref", "return"),
        ),
        missing_semantic_fact=("counterexample_safety_gate_unproven", "return"),
        evidence_refs=("other-return",),
        producer_id="phase10-high-bit-sat-transform",
        counterexample_binding=unrelated_binding,
    )
    unrelated_occurrence_id = session.domain_signal_encoder.authority_for_signal(
        session, unrelated
    ).occurrence.occurrence_id
    mismatches = (
        _safe_pairwise_receipt(
            query="(assert (= x 9))\n(check-sat)", model={"x": 1},
            premise="region-zero", pair_key=("monolithic", "region:0"),
        ),
        _safe_pairwise_receipt(
            query="(assert (= x 1))\n(check-sat)", model={"x": 9},
            premise="region-zero", pair_key=("monolithic", "region:0"),
        ),
        _safe_pairwise_receipt(
            query="(assert (= x 1))\n(check-sat)", model={"x": 1},
            premise="different-premise", pair_key=("monolithic", "region:0"),
        ),
        _safe_pairwise_receipt(
            query="(assert (= x 1))\n(check-sat)", model={"x": 1},
            premise="region-zero", pair_key=("monolithic", "region:1"),
        ),
    )
    with production_signal_scope(session):
        assert emit_sat_safety_signal(observed) == 1
        assert emit_sat_safety_signal(unrelated) == 1
        for mismatch_receipt in mismatches:
            mismatch = SafeCounterexampleProductionSignal.from_pairwise_receipt(
                mismatch_receipt
            )
            assert complete_observed_sat_safety_for_counterexample(mismatch) == 0
        assert complete_observed_sat_safety_for_counterexample(safe_signal) == 1
        assert emit_safe_counterexample_production_signal(
            safety_receipt=receipt,
        ) == 1
    evidence = connector.finish(
        session, _LegacyResult(Outcome.NOT_EQ), case_id="safe-sat-closes-open"
    )
    assert [
        event.header.event_type.value
        for event in evidence.pilot_result.sealed_event_stream.events
    ] == [
        "CAUSE_OBSERVED",
        "CAUSE_OBSERVED",
        "REQUIREMENT_COMPLETED",
        "COUNTEREXAMPLE",
    ]
    active = evidence.pilot_result.reduction.projection.c_active_base
    assert len(active) == 1
    assert active[0].occurrence_id == unrelated_occurrence_id
    assert len(evidence.pilot_result.reduction.projection.q_open_base) == 1
    assert evidence.pilot_result.candidate.decision_receipt.outcome is not Outcome.NOT_EQ


def test_safe_counterexample_rejects_raw_digests_and_tampered_typed_receipt():
    with pytest.raises(TypeError, match="typed safety receipt"):
        SafeCounterexampleProductionSignal(
            proof_artifact_digest="a" * 64,
            formula_digest="b" * 64,
            model_digest="c" * 64,
            premise_digest="d" * 64,
            pair_key=(0, 1),
            receipt_kind="pairwise_counterexample_safety_receipt_v1",
            safety_receipt=None,
            verification_context=(),
        )

    receipt = _safe_pairwise_receipt()
    tampered = replace(receipt, formula_digest="0" * 64)
    with pytest.raises(ValueError, match="receipt is invalid"):
        emit_safe_counterexample_production_signal(safety_receipt=tampered)

    schema_tampered = replace(
        receipt, schema_version="counterexample_safety_receipt_v2"
    )
    assert schema_tampered.validates_authority() is False
    with pytest.raises(ValueError, match="receipt is invalid"):
        emit_safe_counterexample_production_signal(
            safety_receipt=schema_tampered
        )


def test_monolithic_strategy_publishes_safe_counterexample_to_v2():
    from scripts.function_tracer_pcode.equivalence.checker import EquivalenceChecker

    connector = _connector()
    session = connector.begin({"phase": "monolithic", "case": "strategy-sat"})
    checker = EquivalenceChecker(
        strategy="monolithic",
        timeout=5,
        monolithic_timeout=5,
        enable_rewrite=False,
    )
    with production_signal_scope(session):
        result = checker.check(
            FunctionReturnAnalysis(
                function_name="left",
                entry_point="0x1000",
                parameters=[],
                returns=[ReturnInfo("0x1010", Expression.constant(7, size=4), [])],
                return_type="int",
            ),
            FunctionReturnAnalysis(
                function_name="right",
                entry_point="0x1000",
                parameters=[],
                returns=[ReturnInfo("0x1010", Expression.constant(8, size=4), [])],
                return_type="int",
            ),
        )
    evidence = connector.finish(session, result, case_id="monolithic-strategy-sat")
    assert result.is_equivalent is False
    assert evidence.pilot_result.candidate.decision_receipt.outcome is Outcome.NOT_EQ
    assert [
        event.header.event_type.value
        for event in evidence.pilot_result.sealed_event_stream.events
    ] == ["COUNTEREXAMPLE"]


def test_real_sat_safety_producer_observes_completes_and_issues_decisive_authority():
    connector = _manifest_connector()
    session = connector.begin({"phase": "6.1", "case": "sat-safety-complete"})
    strategy, analysis1, analysis2, case1, case2 = _strategy_and_surface()
    model = {"x_1": 0, "x_2": 1}
    with production_signal_scope(session):
        reason = strategy._make_sat_unsafety_unknown_reason(
            (
                "function1:incomplete_control_flow",
                "counterexample_replay_missing",
            ),
            analysis1,
            analysis2,
            case1=case1,
            case2=case2,
            pair_id="(0,1)",
            stage="S_PAIRWISE",
        )
        # Re-observing the same legacy umbrella must not duplicate one v2 cause.
        strategy._make_sat_unsafety_unknown_reason(
            tuple(reason.evidence_refs),
            analysis1,
            analysis2,
            case1=case1,
            case2=case2,
            pair_id="(0,1)",
            stage="S_PAIRWISE",
        )
        strategy._record_completed_sat_counterexample_replay_proof(
            reason,
            analysis1,
            analysis2,
            counterexample_raw=model,
            fixed_model_assertion_count=2,
            replay_source="phase6-production-fixture",
        )
        assert strategy._sat_unsafety_resolution_proof_is_complete(
            reason,
            analysis1,
            analysis2,
            current_counterexample_raw=model,
        )
        receipt = CounterexampleSafetyReceipt.from_pairwise_validation(
            query="(assert (not (= x_1 x_2)))\n(check-sat)",
            model=model,
            premise_digest="phase6-premise",
            pair_key=(0, 1),
            analysis_safe=True,
            global_case_replay_safe=True,
            same_function_replay_safe=True,
        )
    evidence = connector.finish(
        session,
        _LegacyResult(Outcome.NOT_EQ),
        case_id="phase6-sat-safety-complete",
    )
    evidence.validate()
    assert reason.reason_id == "counterexample_analysis_safety_unproven"
    assert receipt.validates(
        type("Binding", (), {"premise_digest": "phase6-premise"})(),
        (0, 1),
    )
    observed = [
        event for event in evidence.pilot_result.sealed_event_stream.events
        if event.header.event_type.value == "CAUSE_OBSERVED"
    ]
    completed = [
        event for event in evidence.pilot_result.sealed_event_stream.events
        if event.header.event_type.value == "REQUIREMENT_COMPLETED"
    ]
    # Pairwise blockers proven before terminalization remain provisional and
    # never enter the canonical lifecycle stream.
    assert observed == []
    assert completed == []
    assert evidence.pilot_result.reduction.projection.c_active_base == ()
    assert evidence.pilot_result.reduction.projection.q_open_base == ()
    assert evidence.pilot_result.candidate.decision_receipt.outcome == Outcome.NOT_EQ


def test_real_ambiguity_producer_is_distinct_from_analysis_safety_cause():
    connector = _manifest_connector()
    session = connector.begin({"phase": "6.1", "case": "ambiguity"})
    strategy, analysis1, analysis2, case1, case2 = _strategy_and_surface()
    model = {"x_1": 0, "x_2": 1}
    with production_signal_scope(session):
        strategy._observe_v2_sat_counterexample_ambiguity(
            ("partition-a", "partition-b"),
            analysis1,
            analysis2,
            case1=case1,
            case2=case2,
            pair_id="(0,1)",
        )
        # A failed legacy projection re-observes the already-live v2 requirement.
        legacy = strategy._make_sat_counterexample_ambiguous_unknown_reason(
            ("partition-a", "partition-b"),
            analysis1,
            analysis2,
            case1=case1,
            case2=case2,
            pair_id="(0,1)",
            stage="S_PAIRWISE",
        )
        strategy._complete_v2_sat_counterexample_ambiguity_if_observed(
            ("partition-a", "partition-b"),
            analysis1,
            analysis2,
            case1=case1,
            case2=case2,
            pair_id="(0,1)",
            counterexample_raw=model,
        )
        CounterexampleSafetyReceipt.from_pairwise_validation(
            query="(assert distinct)\n(check-sat)",
            model=model,
            premise_digest="ambiguity-premise",
            pair_key=(0, 1),
            analysis_safe=True,
            global_case_replay_safe=True,
            same_function_replay_safe=True,
        )
    evidence = connector.finish(
        session, _LegacyResult(Outcome.NOT_EQ), case_id="phase6-ambiguity"
    )
    assert legacy.reason_id == "sat_counterexample_ambiguous"
    event_types = [
        event.header.event_type.value
        for event in evidence.pilot_result.sealed_event_stream.events
    ]
    assert event_types == ["CAUSE_OBSERVED", "REQUIREMENT_COMPLETED", "COUNTEREXAMPLE"]
    assert evidence.pilot_result.reduction.projection.c_active_base == ()
    assert evidence.pilot_result.reduction.projection.q_open_base == ()
    assert evidence.pilot_result.candidate.decision_receipt.outcome == Outcome.NOT_EQ


def test_manifest_bound_ambiguity_observation_remains_unknown_until_completed():
    connector = _manifest_connector()
    session = connector.begin({
        "phase": "7",
        "case": "manifest-bound-ambiguity-open",
    })
    strategy, analysis1, analysis2, case1, case2 = _strategy_and_surface()
    with production_signal_scope(session):
        strategy._observe_v2_sat_counterexample_ambiguity(
            ("partition-a", "partition-b"),
            analysis1,
            analysis2,
            case1=case1,
            case2=case2,
            pair_id="(0,1)",
        )

    evidence = connector.finish(
        session,
        _LegacyResult(Outcome.UNKNOWN),
        case_id="manifest-bound-ambiguity-open",
    )
    assert [
        event.header.event_type.value
        for event in evidence.pilot_result.sealed_event_stream.events
    ] == ["CAUSE_OBSERVED"]
    assert {
        row.reason_id
        for row in evidence.pilot_result.reduction.projection.c_active_base
    } == {"counterexample_partition_replay_ambiguous"}
    assert evidence.pilot_result.candidate.decision_receipt.outcome is Outcome.UNKNOWN


def test_manifest_bound_multiple_sat_case_pairs_deduplicate_per_occurrence():
    connector = _manifest_connector()
    session = connector.begin({
        "phase": "7",
        "case": "manifest-bound-multiple-sat-case-pairs",
    })
    strategy, analysis1, analysis2, case1, case2 = _strategy_and_surface()
    _, alternate_case1 = _case("B10", 0x1100, 2)
    _, alternate_case2 = _case("B9", 0x2100, 3)
    with production_signal_scope(session):
        for current_case1, current_case2, pair_id in (
            (case1, case2, "(0,1)"),
            (alternate_case1, alternate_case2, "(2,3)"),
            (case1, case2, "(0,1)"),
        ):
            strategy._observe_v2_sat_counterexample_ambiguity(
                ("partition-a", "partition-b"),
                analysis1,
                analysis2,
                case1=current_case1,
                case2=current_case2,
                pair_id=pair_id,
            )

    evidence = connector.finish(
        session,
        _LegacyResult(Outcome.UNKNOWN),
        case_id="manifest-bound-multiple-sat-case-pairs",
    )
    observed = [
        event
        for event in evidence.pilot_result.sealed_event_stream.events
        if event.header.event_type.value == "CAUSE_OBSERVED"
    ]
    assert len(observed) == 2
    assert len({
        event.authority_payload.occurrence_authority.occurrence.occurrence_id
        for event in observed
    }) == 2
    assert len(evidence.pilot_result.reduction.projection.c_active_base) == 2
    assert evidence.pilot_result.candidate.decision_receipt.outcome is Outcome.UNKNOWN


def test_phase7_rejects_explicit_invalid_sat_completion_producer():
    from scripts.function_tracer_pcode.equivalence.v2.production_signals import (
        emit_sat_safety_completion_if_observed,
    )
    from scripts.function_tracer_pcode.equivalence.v2.sat_safety_sites import (
        SAT_SAFETY_AMBIGUITY_OBSERVED_SITE,
    )

    connector = _manifest_connector()
    session = connector.begin({
        "phase": "7",
        "case": "invalid-explicit-completion-producer",
    })
    observed = SatSafetyBlockerProductionSignal(
        action="OBSERVED",
        reason_id="counterexample_partition_replay_ambiguous",
        canonical_target_key=("invalid-explicit-completion-producer",),
        missing_semantic_fact=("unique_counterexample_partition_witness", False),
        evidence_refs=("partition-a", "partition-b"),
        producer_id=SAT_SAFETY_AMBIGUITY_OBSERVED_SITE.producer_id,
    )
    invalid_completion = SatSafetyBlockerProductionSignal(
        action="COMPLETED",
        reason_id=observed.reason_id,
        canonical_target_key=observed.canonical_target_key,
        missing_semantic_fact=observed.missing_semantic_fact,
        evidence_refs=observed.evidence_refs,
        producer_id="explicit-invalid-completion-producer",
        proof_artifact_digest="invalid-completion-producer-proof",
    )
    with production_signal_scope(session):
        assert emit_sat_safety_signal(
            observed,
            producer_site_manifest_id="sat-safety-ambiguity-observed",
        ) == 1
        assert emit_sat_safety_completion_if_observed(
            invalid_completion,
            producer_site_manifest_id="sat-safety-ambiguity-completed",
        ) == 0

    assert session.recorder.event_count == 1
    assert "sat_safety_completed" not in session.domain_signal_state
    assert session.domain_signal_error_details == [
        "SatSafetyBlockerProductionSignal: "
        "discovered activation producer is not site-sealed"
    ]
    assert session.phase7_runtime._pending == {}
    assert len(session.phase7_runtime._materialized) == 1
    assert session._phase7_signal_sites == {}
    assert session._phase7_signal_transactions == {}


def test_sat_safety_dedup_state_is_isolated_between_identical_sessions():
    connector = _connector()
    signal = SatSafetyBlockerProductionSignal(
        action="OBSERVED",
        reason_id="counterexample_analysis_safety_unproven",
        canonical_target_key=("same-execution-payload",),
        missing_semantic_fact=("analysis_safety", False),
        evidence_refs=("incomplete_control_flow",),
        producer_id="session-isolation-fixture",
    )
    event_counts = []
    for _ in range(2):
        session = connector.begin({"identical": "payload"})
        with production_signal_scope(session):
            assert emit_sat_safety_signal(signal) == 1
        evidence = connector.finish(
            session, _LegacyResult(Outcome.UNKNOWN), case_id=session.identity.result_occurrence_id
        )
        event_counts.append(len(evidence.pilot_result.sealed_event_stream.events))
    assert event_counts == [1, 1]


def test_sat_safety_completion_commits_only_after_stream_append(monkeypatch):
    connector = _connector()
    session = connector.begin({"phase": "6.1", "case": "completion-append-failure"})
    observed = SatSafetyBlockerProductionSignal(
        action="OBSERVED",
        reason_id="counterexample_analysis_safety_unproven",
        canonical_target_key=("completion-transaction",),
        missing_semantic_fact=("analysis_safety", False),
        evidence_refs=("completion-transaction",),
        producer_id="completion-transaction-fixture",
    )
    completed = SatSafetyBlockerProductionSignal(
        action="COMPLETED",
        reason_id=observed.reason_id,
        canonical_target_key=observed.canonical_target_key,
        missing_semantic_fact=observed.missing_semantic_fact,
        evidence_refs=observed.evidence_refs,
        producer_id=observed.producer_id,
        proof_artifact_digest="completion-transaction-proof",
    )
    with production_signal_scope(session):
        assert emit_sat_safety_signal(observed) == 1
        real_emit_many = session.emit_many

        def fail_append(_intents, _commit_callback=None):
            raise RuntimeError("forced SAT safety completion append failure")

        monkeypatch.setattr(session, "emit_many", fail_append)
        assert emit_sat_safety_signal(completed) == 0
        assert session.recorder.event_count == 1
        assert "sat_safety_completed" not in session.domain_signal_state
        assert "sat_safety_pending_emission_transactions" not in (
            session.domain_signal_state
        )

        monkeypatch.setattr(session, "emit_many", real_emit_many)
        assert emit_sat_safety_signal(completed) == 1
    assert session.recorder.event_count == 2
    assert len(session.domain_signal_state["sat_safety_completed"]) == 1


def test_sat_safety_phase7_execution_buffer_failure_rolls_back_before_stream(
    monkeypatch,
):
    from scripts.function_tracer_pcode.equivalence.v2.phase7_runtime import (
        runtime_from_audited_manifest,
    )
    from scripts.function_tracer_pcode.equivalence.v2.production_signals import (
        CompositeProductionSignalEncoder,
        emit_sat_safety_completion_if_observed,
    )

    root = Path(__file__).resolve().parents[4]
    manifest = json.loads((root / (
        "artifacts/unknown_taxonomy_v2/phase7/producer-sites.json"
    )).read_text(encoding="utf-8"))
    safety_encoder = SatSafetyPilotEncoder()
    connector = ProductionDualWritePilotConnector(
        ShadowLifecycleReducer(
            reason_registry=SAT_SAFETY_REASON_REGISTRY,
            recovery_registry=SAT_SAFETY_RECOVERY_REGISTRY,
        ),
        domain_signal_encoder=CompositeProductionSignalEncoder({
            SatSafetyBlockerProductionSignal: safety_encoder,
        }),
        phase7_runtime_factory=lambda identity: runtime_from_audited_manifest(
            manifest, identity
        ),
    )
    session = connector.begin({
        "phase": "7",
        "case": "sat-completion-execution-buffer-failure",
    })
    observed = SatSafetyBlockerProductionSignal(
        action="OBSERVED",
        reason_id="counterexample_partition_replay_ambiguous",
        canonical_target_key=("phase7-completion-transaction",),
        missing_semantic_fact=("unique_counterexample_partition_witness", False),
        evidence_refs=("phase7-completion-transaction",),
        producer_id="sat_counterexample_ambiguity_producer",
    )
    completed = SatSafetyBlockerProductionSignal(
        action="COMPLETED",
        reason_id=observed.reason_id,
        canonical_target_key=observed.canonical_target_key,
        missing_semantic_fact=observed.missing_semantic_fact,
        evidence_refs=observed.evidence_refs,
        producer_id="sat_counterexample_ambiguity_resolution_producer",
        proof_artifact_digest="phase7-completion-transaction-proof",
    )
    with production_signal_scope(session):
        assert emit_sat_safety_signal(
            observed,
            producer_site_manifest_id="sat-safety-ambiguity-observed",
        ) == 1
        runtime = session.phase7_runtime
        real_buffer = runtime.buffer_execution_intent

        def fail_after_buffer(intent):
            real_buffer(intent)
            raise RuntimeError("forced Phase 7 execution buffer failure")

        monkeypatch.setattr(runtime, "buffer_execution_intent", fail_after_buffer)
        assert emit_sat_safety_completion_if_observed(
            completed,
            producer_site_manifest_id="sat-safety-ambiguity-completed",
        ) == 0
        assert session.recorder.event_count == 1
        assert "sat_safety_completed" not in session.domain_signal_state
        assert "sat_safety_pending_emission_transactions" not in (
            session.domain_signal_state
        )
        assert runtime._pending == {}
        assert len(runtime._materialized) == 1
        assert runtime._execution_intents == []
        assert runtime._signal_transactions == {}
        assert runtime._discovery_factory._ordinals == {
            "sat-safety-ambiguity-observed": 1
        }
        assert session._phase7_signal_sites == {}
        assert session._phase7_signal_transactions == {}

        monkeypatch.setattr(runtime, "buffer_execution_intent", real_buffer)
        assert emit_sat_safety_completion_if_observed(
            completed,
            producer_site_manifest_id="sat-safety-ambiguity-completed",
        ) == 1
    assert session.recorder.event_count == 2
    assert len(session.domain_signal_state["sat_safety_completed"]) == 1
    assert len(session.phase7_runtime._materialized) == 2
    assert len(session.phase7_runtime._execution_intents) == 1
    with pytest.raises(
        ValueError, match="production domain signal encoding is incomplete"
    ):
        connector.finish(
            session,
            _LegacyResult(Outcome.NOT_EQ),
            case_id="sat-completion-execution-buffer-failure",
        )


def test_sat_safety_completion_near_miss_cannot_close_an_unobserved_cause():
    connector = _connector()
    session = connector.begin({"phase": "6.1", "case": "near-miss"})
    with production_signal_scope(session):
        emitted = emit_sat_safety_signal(SatSafetyBlockerProductionSignal(
            action="COMPLETED",
            reason_id="counterexample_analysis_safety_unproven",
            canonical_target_key=("different-pair",),
            missing_semantic_fact=("counterexample_safety_gate_unproven", "x"),
            evidence_refs=("x",),
            producer_id="near-miss",
            proof_artifact_digest="proof-near-miss",
        ))
    assert emitted == 0
    assert session.domain_signal_error_kinds == ["ValueError"]
    with pytest.raises(ValueError, match="cannot seal an empty"):
        session.recorder.seal()
    with pytest.raises(ValueError, match="signal encoding is incomplete"):
        connector.finish(
            session, _LegacyResult(Outcome.UNKNOWN), case_id="phase6-near-miss"
        )


def test_invalid_counterexample_safety_never_emits_decisive_event():
    connector = _connector()
    session = connector.begin({"phase": "6.1", "case": "invalid-decisive"})
    with production_signal_scope(session):
        with pytest.raises(ValueError, match="validation is incomplete"):
            CounterexampleSafetyReceipt.from_pairwise_validation(
                query="(check-sat)",
                model={"x": 1},
                premise_digest="premise",
                pair_key=(0, 0),
                analysis_safe=True,
                global_case_replay_safe=False,
                same_function_replay_safe=True,
            )
    assert session.observed_domain_signal_count == 0
    with pytest.raises(ValueError, match="cannot seal an empty"):
        session.recorder.seal()


def test_slice1_inventory_delta_remains_a_frozen_historical_transition():
    root = Path(__file__).resolve().parents[4]
    frozen = json.loads(
        (root / "artifacts/unknown_reason_audit/current-head/inventory-review.json").read_text()
    )
    delta = json.loads(
        (root / "artifacts/unknown_taxonomy_v2/phase6/slice1_inventory_delta.json").read_text()
    )
    frozen_ids = {row["site_id"] for row in frozen["entries"]}
    added_ids = {row["site_id"] for row in delta["added"]}
    removed_ids = {row["site_id"] for row in delta["removed"]}
    assert delta["frozen_phase0"] == {
        "candidate_set_digest": frozen["candidate_set_digest"],
        "candidate_count": len(frozen_ids),
    }
    assert delta["current_source"]["candidate_count"] == (
        len(frozen_ids) - len(removed_ids) + len(added_ids)
    )
    assert added_ids.isdisjoint(frozen_ids)
    assert removed_ids <= frozen_ids
    assert all(row["review_status"] == "reviewed_by_main_pending_fixed_review" for row in delta["added"])


def test_representative_result_is_repo_local_and_bound_by_slice_evidence():
    root = Path(__file__).resolve().parents[4]
    relative_path = "artifacts/unknown_taxonomy_v2/phase6/slice1_representative_result.json"
    result_path = root / relative_path
    result_bytes = result_path.read_bytes()
    result = json.loads(result_bytes)
    slice_evidence = json.loads(
        (root / "artifacts/unknown_taxonomy_v2/phase6/slice1_sat_safety.json").read_text()
    )
    assert slice_evidence["representative_current_source_run"]["result_artifact"] == {
        "path": relative_path,
        "sha256": hashlib.sha256(result_bytes).hexdigest(),
    }
    assert result["decision"] == "NOT_EQ"
    assert result["process_exit_code"] == 1
    assert result["result_payload_projection"]["is_timeout"] is False
    assert result["result_payload_projection"]["unknown_reasons"] == []
    assert result["result_payload_projection"]["pairwise_stats"] == {
        "total_pairs": 4,
        "unsat_pairs": 3,
        "sat_pairs": 1,
        "unknown_pairs": 0,
        "error_pairs": 0,
    }
