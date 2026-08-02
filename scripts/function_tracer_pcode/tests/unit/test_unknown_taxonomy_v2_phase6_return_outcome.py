# -*- coding: utf-8 -*-

from dataclasses import replace
import json
from pathlib import Path
from types import SimpleNamespace

import pytest

from scripts.function_tracer_pcode.equivalence.v2.return_outcome import (
    OUTCOME_STAGE_REASON_MATRIX,
    RETURN_OUTCOME_REASON_REGISTRY,
    RETURN_OUTCOME_RECOVERY_REGISTRY,
    WITNESSED_REASON_PROPOSITIONS,
    OutcomeStageExecutionReceipt,
    ReturnOutcomePilotEncoder,
    UnaryOutcomeWitnessArtifact,
    reason_for_stage_status,
)
from scripts.function_tracer_pcode.equivalence.v2.production_signals import (
    CompositeProductionSignalEncoder,
    OutcomePartitionProductionSignal,
    production_signal_scope,
)
from scripts.function_tracer_pcode.equivalence.v2.phase7_runtime import (
    runtime_from_audited_manifest,
)
from scripts.function_tracer_pcode.equivalence.v2.stream import (
    EventRecorder,
    EventIntent,
    EventType,
    ReceiptBoundSolverExecutionEventAuthority,
)
from scripts.function_tracer_pcode.smt.interface import SolverResult, SolverStatus
from scripts.function_tracer_pcode.smt.parallel import ParallelResult
from scripts.function_tracer_pcode.equivalence.v2.contracts import Outcome, authority_digest
from scripts.function_tracer_pcode.equivalence.v2.codecs import StrictV2JsonCodec
from scripts.function_tracer_pcode.equivalence.v2.pilot import (
    ProductionDualWritePilotConnector,
    TerminalCandidateView,
    TerminalizationIntent,
    run_dual_write_pilot,
)
from scripts.function_tracer_pcode.equivalence.v2.phase7_cutover import (
    TerminalTimeoutCandidateSelectionReceipt,
)
from scripts.function_tracer_pcode.equivalence.v2.reducer import ShadowLifecycleReducer
from scripts.function_tracer_pcode.equivalence.obligations.outcome_partition import (
    UnaryProducerResult,
    outcome_seed_digest,
    prove_unary_partition,
    requirement_for_stage,
)
from scripts.function_tracer_pcode.equivalence.cause_identity import ProofRequirementId
from scripts.function_tracer_pcode.validation.unknown_taxonomy_audit import build_inventory_review_template


_WITNESSES = (
    (
        "same_kind_consistency",
        "conflict",
        "outcome_return_value_conflict_witnessed",
    ),
    (
        "cross_kind_disjointness",
        "overlap",
        "outcome_cross_kind_overlap_witnessed",
    ),
    (
        "residual_totality",
        "residual_sat",
        "outcome_partition_residual_sat_witnessed",
    ),
)


def _seed(**changes):
    values = {
        "function_identity": ("function", "bin-a", 4096),
        "input_domain_contract": ("all_inputs",),
        "partition_revision": 3,
        "extraction_schema_version": 1,
        "stable_key": lambda: ("production-shaped-outcome-seed", "bin-a", 4096),
    }
    values.update(changes)
    return SimpleNamespace(**values)


def _receipt(stage, model={"x": 1}, seed=None):
    seed = seed or _seed()
    return OutcomeStageExecutionReceipt.create(
        stage=stage,
        seed=seed,
        premise_digest="premise-a",
        function_snapshot_fingerprint="snapshot-a",
        outcome_seed_digest=outcome_seed_digest(seed),
        outcome_seed_revision=3,
        query="(assert witness)\n(check-sat)\n(get-model)",
        model=model,
        solver_output={"status": "sat", "model": model},
        solver_identity="Z3",
        execution_identity_digest="test-execution-a",
        producer_attempt_identity=f"attempt-{stage}-1",
        producer_attempt_ordinal=1,
        invocation_identity=f"invoke-{stage}",
        invocation_ordinal=1,
        configured_timeout_ms=10000,
        elapsed_ms=7,
        observed_status="sat",
    )


def _execution_receipt(
    stage, status, *, ordinal=1, producer_attempt_ordinal=None,
    execution_identity_digest="test-execution-a",
):
    seed = _seed()
    model = {"x": 1} if status == "sat" else None
    return OutcomeStageExecutionReceipt.create(
        stage=stage,
        seed=seed,
        premise_digest="premise-a",
        function_snapshot_fingerprint="function-snapshot-a",
        outcome_seed_digest=outcome_seed_digest(seed),
        outcome_seed_revision=3,
        query="(check-sat)\n(get-model)",
        model=model,
        solver_output={"status": status, "model": model},
        solver_identity="Z3",
        execution_identity_digest=execution_identity_digest,
        producer_attempt_identity=(
            f"attempt-{stage}-{producer_attempt_ordinal or ordinal}"
        ),
        producer_attempt_ordinal=producer_attempt_ordinal or ordinal,
        invocation_identity=f"invoke-{stage}-{ordinal}",
        invocation_ordinal=ordinal,
        configured_timeout_ms=10000,
        elapsed_ms=7,
        observed_status=status,
    )


def _session():
    return SimpleNamespace(
        identity=SimpleNamespace(
            result_occurrence_id="result-occ-a",
            source_snapshot_fingerprint="source-snapshot-a",
            execution_identity_digest="test-execution-a",
        ),
        domain_signal_state={},
    )


def _analysis(seed=None):
    seed = seed or _seed()
    return SimpleNamespace(
        function_name="f",
        entry_point="0x1000",
        binary_id="bin-a",
        outcome_seed=seed,
    )


def _signal(stage, status, receipt=None, *, witness=None, artifact=None):
    seed = _seed()
    requirement = (
        receipt.proof_requirement_identity
        if receipt is not None
        else requirement_for_stage(seed, stage)
    )
    return OutcomePartitionProductionSignal(
        stage=stage,
        producer_status=status,
        proof_requirement_identity=requirement.to_dict(),
        function_identity=seed.function_identity,
        outcome_seed_digest=outcome_seed_digest(seed),
        producer_evidence={"producer_status": status},
        outcome_seed_revision=3,
        function_snapshot_fingerprint="function-snapshot-a",
        premise_digest="premise-a",
        producer_attempt_identity=(
            receipt.producer_attempt_identity
            if receipt is not None
            else f"attempt-{stage}-1"
        ),
        producer_attempt_ordinal=(
            receipt.producer_attempt_ordinal if receipt is not None else 1
        ),
        execution_identity_digest=(
            receipt.execution_identity_digest
            if receipt is not None
            else "test-execution-a"
        ),
        execution_receipts=() if receipt is None else (receipt,),
        witness_artifact=witness,
        validated_artifact_authority=artifact,
    )


def _completion_artifact(receipt):
    artifact_payload = {
        "artifact_id": "artifact-a",
        "requirement_id": receipt.proof_requirement_identity.to_dict(),
        "produced_from_view_id": "view-a",
        "premise_digest": "premise-a",
        "dependency_artifact_ids": (),
        "producer_id": f"unary_outcome_{receipt.stage}",
        "producer_version": "reachable-outcome-producer-v1",
        "encoding_version": "reachable-outcome-smt-v1",
        "artifact_validation_status": "validated",
        "function_snapshot_fingerprint": "function-snapshot-a",
        "outcome_seed_digest": receipt.outcome_seed_digest,
        "outcome_seed_revision": 3,
        "stage": receipt.stage,
    }
    return {
        **artifact_payload,
        "artifact_authority_digest": authority_digest(artifact_payload),
    }


def _run_actual_timeout_attempt(session, seed_key):
    from scripts.function_tracer_pcode.equivalence.strategies.proof_gates.return_coverage import (
        _unary_solver_status,
    )

    aggregate = ParallelResult([
        SolverResult("Z3", SolverStatus.TIMEOUT, elapsed_time=0.006)
    ])
    owner = SimpleNamespace(
        solver_runner=SimpleNamespace(
            timeout=10,
            run_sequential=lambda _query: aggregate,
        ),
        _normalize_zero_constant_widths_for_declared_symbols=(
            lambda assertions, _header: assertions
        ),
    )

    def timeout_producer():
        status = _unary_solver_status(
            owner,
            {"header_lines": ("(declare-fun x () Bool)",)},
            ("x",),
            "actual producer timeout",
        )
        return UnaryProducerResult(status, {"solver_status": status})

    producers = {
        "termination_classification": lambda: UnaryProducerResult("proved"),
        "cfg_reachability": lambda: UnaryProducerResult("proved"),
        "path_region_completeness": lambda: UnaryProducerResult("proved"),
        "member_classification": lambda: UnaryProducerResult("proved"),
        "same_kind_consistency": timeout_producer,
    }
    analysis = _analysis(_seed(stable_key=lambda: (seed_key,)))
    with production_signal_scope(session):
        proof = prove_unary_partition(
            analysis,
            domain_contract=("all_inputs",),
            normalization_policy_digest=f"{seed_key}-policy-v1",
            producers=producers,
        )
    return analysis, proof


def _artifact(stage, reason_id):
    receipt = _receipt(stage)
    return receipt, UnaryOutcomeWitnessArtifact.create(
        receipt,
        reason_id=reason_id,
        witnessed_proposition=WITNESSED_REASON_PROPOSITIONS[reason_id],
        producer_version="reachable-outcome-producer-v1",
        encoding_version="reachable-outcome-smt-v1",
    )


def test_stage_status_matrix_is_exact_and_rejects_unknown_pairs():
    assert len(OUTCOME_STAGE_REASON_MATRIX) == 24
    assert reason_for_stage_status("same_kind_consistency", "timeout") == (
        "outcome_same_kind_consistency_unproven"
    )
    assert reason_for_stage_status("cross_kind_disjointness", "overlap") == (
        "outcome_cross_kind_overlap_witnessed"
    )
    with pytest.raises(ValueError, match="not sealed"):
        reason_for_stage_status("cross_kind_disjointness", "sat")
    with pytest.raises(TypeError, match="exact strings"):
        reason_for_stage_status("residual_totality", 1)


@pytest.mark.parametrize("stage,status,reason_id", _WITNESSES)
def test_each_witnessed_status_requires_a_validated_unary_artifact(
    stage, status, reason_id
):
    receipt, artifact = _artifact(stage, reason_id)
    assert reason_for_stage_status(stage, status) == reason_id
    artifact.validate_against(receipt)
    assert artifact.reason_id == reason_id
    assert artifact.solver_invocation_receipt_digest == receipt.receipt_digest
    # Unary blocker evidence is deliberately not a decisive counterexample event.
    assert not hasattr(artifact, "pair_key")
    assert not hasattr(artifact, "formula_digest")


@pytest.mark.parametrize(
    "field_name,bad_value,error",
    (
        ("query_digest", "wrong-query", "query_digest binding mismatch"),
        (
            "solver_invocation_receipt_digest",
            "wrong-receipt",
            "solver_invocation_receipt_digest binding mismatch",
        ),
        ("premise_digest", "wrong-premise", "premise_digest binding mismatch"),
        (
            "function_snapshot_fingerprint",
            "wrong-snapshot",
            "function_snapshot_fingerprint binding mismatch",
        ),
    ),
)
def test_witness_artifact_rejects_exact_binding_mismatches(
    field_name, bad_value, error
):
    receipt, artifact = _artifact(
        "cross_kind_disjointness", "outcome_cross_kind_overlap_witnessed"
    )
    with pytest.raises(ValueError, match=error):
        replace(artifact, **{field_name: bad_value}).validate_against(receipt)


def test_witness_artifact_rejects_proposition_model_and_stage_mismatches():
    with pytest.raises(ValueError, match="lacks a captured model"):
        _receipt("residual_totality", model=None)
    receipt = _receipt("residual_totality")
    with pytest.raises(ValueError, match="does not match reason"):
        UnaryOutcomeWitnessArtifact.create(
            receipt,
            reason_id="outcome_partition_residual_sat_witnessed",
            witnessed_proposition="reachable_outcome_kinds_overlap",
            producer_version="producer-v1",
            encoding_version="encoding-v1",
        )
    with pytest.raises(ValueError, match="stage does not match reason"):
        UnaryOutcomeWitnessArtifact.create(
            receipt,
            reason_id="outcome_cross_kind_overlap_witnessed",
            witnessed_proposition="reachable_outcome_kinds_overlap",
            producer_version="producer-v1",
            encoding_version="encoding-v1",
        )


def test_model_digest_tampering_is_rejected_without_counterexample_authority():
    receipt, artifact = _artifact(
        "same_kind_consistency", "outcome_return_value_conflict_witnessed"
    )
    with pytest.raises(ValueError, match="model_digest binding mismatch"):
        replace(artifact, model_digest="wrong-model").validate_against(receipt)


def test_factory_issued_artifact_revalidates_stage_reason_matrix():
    receipt, artifact = _artifact(
        "residual_totality", "outcome_partition_residual_sat_witnessed"
    )
    forged = replace(
        artifact,
        reason_id="outcome_cross_kind_overlap_witnessed",
        witnessed_proposition="reachable_outcome_kinds_overlap",
    )
    forged_payload = {
        name: getattr(forged, name)
        for name in (
            "reason_id", "stage", "proof_requirement_identity", "premise_digest",
            "function_snapshot_fingerprint", "outcome_seed_digest",
            "outcome_seed_revision", "query_digest", "model_digest",
            "solver_invocation_receipt_digest", "witnessed_proposition",
            "producer_version", "encoding_version",
        )
    }
    forged = replace(forged, artifact_digest=authority_digest(forged_payload))
    with pytest.raises(ValueError, match="stage/reason binding mismatch"):
        forged.validate_against(receipt)


def test_execution_receipt_rejects_reconstructed_requirement_authority_mismatch():
    receipt = _receipt("residual_totality")
    requirement = receipt.proof_requirement_identity
    wrong_requirement_schema = ProofRequirementId(
        requirement.proof_kind,
        requirement.proof_target_key,
        requirement.proof_contract_key,
        schema_version=2,
    )
    wrong_contract_schema = ProofRequirementId(
        requirement.proof_kind,
        requirement.proof_target_key,
        (2, *requirement.proof_contract_key[1:]),
    )
    mismatches = (
        replace(receipt, function_identity=("function", "other-bin", 8192)),
        replace(receipt, input_domain_contract=("restricted_inputs",)),
        replace(receipt, extraction_schema_version=2),
        replace(receipt, outcome_encoding_version="other-encoding"),
        replace(receipt, proof_requirement_identity=wrong_requirement_schema),
        replace(receipt, proof_requirement_identity=wrong_contract_schema),
    )
    for forged in mismatches:
        with pytest.raises(ValueError, match="not the exact stage authority"):
            forged.validate()


def test_execution_receipt_rejects_solver_output_model_provenance_mismatch():
    seed = _seed()
    with pytest.raises(ValueError, match="output model differs"):
        OutcomeStageExecutionReceipt.create(
            stage="same_kind_consistency",
            seed=seed,
            premise_digest="premise-a",
            function_snapshot_fingerprint="snapshot-a",
            outcome_seed_digest=outcome_seed_digest(seed),
            outcome_seed_revision=3,
            query="(check-sat)",
            model={"x": 1},
            solver_output={"status": "sat", "model": {"x": 2}},
            solver_identity="Z3",
            execution_identity_digest="test-execution-a",
            producer_attempt_identity="attempt-same-kind-1",
            producer_attempt_ordinal=1,
            invocation_identity="mismatched-model-invocation",
            invocation_ordinal=1,
            configured_timeout_ms=10000,
            elapsed_ms=1,
            observed_status="sat",
        )


def test_execution_receipt_requires_factory_and_exact_proof_requirement_schema():
    receipt = _receipt("same_kind_consistency")
    payload = dict(receipt.__dict__)
    payload["_factory_token"] = None
    with pytest.raises(TypeError, match="factory-issued"):
        OutcomeStageExecutionReceipt(**payload)
    with pytest.raises((TypeError, ValueError)):
        seed = _seed()
        OutcomeStageExecutionReceipt.create(
            stage="same_kind_consistency",
            seed=seed,
            premise_digest="premise",
            function_snapshot_fingerprint="snapshot",
            outcome_seed_digest="wrong-seed-digest",
            outcome_seed_revision=3,
            query="(check-sat)",
            model={"x": 1},
            solver_output={"status": "sat", "model": {"x": 1}},
            solver_identity="Z3",
            execution_identity_digest="test-execution-a",
            producer_attempt_identity="attempt-same-kind-1",
            producer_attempt_ordinal=1,
            invocation_identity="invocation",
            invocation_ordinal=1,
            configured_timeout_ms=1000,
            elapsed_ms=1,
            observed_status="sat",
        )


def test_unary_witness_requires_factory_issuance():
    _receipt_value, artifact = _artifact(
        "residual_totality", "outcome_partition_residual_sat_witnessed"
    )
    payload = dict(artifact.__dict__)
    payload["_factory_token"] = None
    with pytest.raises(TypeError, match="factory-issued"):
        UnaryOutcomeWitnessArtifact(**payload)


def test_return_outcome_encoder_preserves_unknown_receipt_and_deduplicates_retry():
    encoder = ReturnOutcomePilotEncoder()
    session = _session()
    receipt = _execution_receipt("same_kind_consistency", "unknown")
    signal = _signal("same_kind_consistency", "unknown", receipt)
    intents = encoder(session, signal)
    assert tuple(intent.event_type for intent in intents) == (
        EventType.CAUSE_OBSERVED,
        EventType.OUTCOME_PRODUCER_ATTEMPT,
        EventType.SOLVER_UNKNOWN,
    )
    solver_authority = intents[2].authority_payload
    assert type(solver_authority) is ReceiptBoundSolverExecutionEventAuthority
    assert solver_authority.execution_receipt_digest == receipt.receipt_digest
    assert solver_authority.query_digest == receipt.query_digest
    assert solver_authority.elapsed_ms == receipt.elapsed_ms
    assert encoder(session, signal) == ()


def test_return_outcome_encoder_emits_timeout_from_raw_solver_status():
    encoder = ReturnOutcomePilotEncoder()
    receipt = _execution_receipt("residual_totality", "timeout")
    intents = encoder(
        _session(), _signal("residual_totality", "timeout", receipt)
    )
    assert tuple(intent.event_type for intent in intents) == (
        EventType.CAUSE_OBSERVED,
        EventType.OUTCOME_PRODUCER_ATTEMPT,
        EventType.SOLVER_TIMEOUT,
    )
    assert intents[2].authority_payload.observed_status == "TIMEOUT"


def test_return_outcome_witness_is_blocker_evidence_not_counterexample_event():
    encoder = ReturnOutcomePilotEncoder()
    receipt = _execution_receipt("cross_kind_disjointness", "sat")
    witness = UnaryOutcomeWitnessArtifact.create(
        receipt,
        reason_id="outcome_cross_kind_overlap_witnessed",
        witnessed_proposition="reachable_outcome_kinds_overlap",
        producer_version="reachable-outcome-producer-v1",
        encoding_version="reachable-outcome-smt-v1",
    )
    intents = encoder(
        _session(),
        _signal("cross_kind_disjointness", "overlap", receipt, witness=witness),
    )
    assert tuple(intent.event_type for intent in intents) == (
        EventType.CAUSE_OBSERVED,
        EventType.OUTCOME_PRODUCER_ATTEMPT,
    )
    assert witness.artifact_digest in (
        intents[0].authority_payload.occurrence_authority.occurrence.evidence_refs
    )


def test_return_outcome_completion_requires_same_observed_requirement_and_digest():
    encoder = ReturnOutcomePilotEncoder()
    session = _session()
    receipt = _execution_receipt("same_kind_consistency", "unknown")
    observed = _signal("same_kind_consistency", "unknown", receipt)
    encoder(session, observed)
    artifact = _completion_artifact(receipt)
    completion = _signal(
        "same_kind_consistency", "proved", artifact=artifact
    )
    intents = encoder(session, completion)
    assert tuple(intent.event_type for intent in intents) == (
        EventType.REQUIREMENT_COMPLETED,
    )
    assert encoder(session, completion) == ()
    forged = dict(artifact)
    forged["artifact_id"] = "forged"
    with pytest.raises(ValueError, match="digest mismatch"):
        ReturnOutcomePilotEncoder()(
            _session(),
            _signal("same_kind_consistency", "proved", artifact=forged),
        )


def test_timeout_capture_uses_solver_status_not_aggregate_error_text():
    from scripts.function_tracer_pcode.equivalence.v2.return_outcome import (
        outcome_stage_capture_scope,
        capture_active_outcome_solver_result,
    )

    seed = _seed()
    raw = SolverResult("Z3", SolverStatus.TIMEOUT, elapsed_time=0.012)
    aggregate = ParallelResult([raw])
    with outcome_stage_capture_scope(
        seed=seed,
        stage="residual_totality",
        premise_digest="premise-a",
        function_snapshot_fingerprint="function-snapshot-a",
    ) as capture:
        captured = capture_active_outcome_solver_result(
            query="(check-sat)",
            parallel_result=aggregate,
            configured_timeout_ms=10000,
        )
    assert captured == tuple(capture.receipts)
    assert captured[0].observed_status == "timeout"
    assert captured[0].elapsed_ms == 12


def test_unary_solver_status_propagates_raw_timeout_to_producer_status():
    from scripts.function_tracer_pcode.equivalence.strategies.proof_gates.return_coverage import (
        _unary_solver_status,
    )
    from scripts.function_tracer_pcode.equivalence.v2.return_outcome import (
        outcome_stage_capture_scope,
    )

    aggregate = ParallelResult([
        SolverResult("Z3", SolverStatus.TIMEOUT, elapsed_time=0.004)
    ])
    owner = SimpleNamespace(
        solver_runner=SimpleNamespace(
            timeout=10,
            run_sequential=lambda _query: aggregate,
        ),
        _normalize_zero_constant_widths_for_declared_symbols=(
            lambda assertions, _header: assertions
        ),
    )
    with outcome_stage_capture_scope(
        seed=_seed(),
        stage="residual_totality",
        premise_digest="premise-a",
        function_snapshot_fingerprint="function-snapshot-a",
    ) as capture:
        status = _unary_solver_status(
            owner,
            {"header_lines": ("(declare-fun x () Bool)",)},
            ("x",),
            "timeout fixture",
        )
    assert status == "timeout"
    assert capture.receipts[0].observed_status == "timeout"


def test_production_session_terminalizes_blocking_solver_timeout_as_timeout():
    connector = ProductionDualWritePilotConnector(
        ShadowLifecycleReducer(
            reason_registry=RETURN_OUTCOME_REASON_REGISTRY,
            recovery_registry=RETURN_OUTCOME_RECOVERY_REGISTRY,
        ),
        domain_signal_encoder=ReturnOutcomePilotEncoder(),
    )
    session = connector.begin({"phase": "6.2", "case": "blocking-solver-timeout"})
    receipt = _execution_receipt(
        "residual_totality",
        "timeout",
        execution_identity_digest=session.identity.execution_identity_digest,
    )
    assert session.emit_domain_signal(
        _signal("residual_totality", "timeout", receipt)
    ) == 3
    assert session.terminalizations == []

    legacy = SimpleNamespace(
        is_equivalent=None,
        error_message=None,
        failure_status=None,
        failure_message=None,
        is_timeout=lambda: True,
    )
    evidence = connector.finish(
        session, legacy, case_id="phase6.2-blocking-solver-timeout"
    )
    evidence.validate()
    assert len(session.terminalizations) == 1
    assert session.terminalizations[0].event_sequence_number == 3
    result = evidence.pilot_result
    assert result.legacy_outcome_after == Outcome.TIMEOUT
    assert result.candidate.decision_receipt.outcome == Outcome.TIMEOUT
    assert result.attempted_solver_event_count == 1
    assert len(result.reduction.projection.c_active_base) == 1
    assert len(result.reduction.projection.q_open_base) == 1


def test_recovered_solver_timeout_stays_historical_and_nonterminal():
    from scripts.function_tracer_pcode.equivalence.v2.stream import EventRecorder

    encoder = ReturnOutcomePilotEncoder()
    session = _session()
    reducer = ShadowLifecycleReducer(
        reason_registry=RETURN_OUTCOME_REASON_REGISTRY,
        recovery_registry=RETURN_OUTCOME_RECOVERY_REGISTRY,
    )
    session.reducer = reducer
    recorder = EventRecorder(
        stream_id="stream-a",
        result_occurrence_id=session.identity.result_occurrence_id,
        source_snapshot_fingerprint=session.identity.source_snapshot_fingerprint,
    )
    receipt = _execution_receipt("residual_totality", "timeout")
    timeout_signal = _signal("residual_totality", "timeout", receipt)
    for intent in encoder(session, timeout_signal):
        recorder.append(intent)
    assert encoder(session, timeout_signal) == ()
    completion = _signal(
        "residual_totality",
        "proved",
        artifact=_completion_artifact(receipt),
    )
    for intent in encoder(session, completion):
        recorder.append(intent)
    stream = recorder.seal()
    assert encoder.finalize_terminal_timeout_bindings(session, stream) == ()
    reduction = reducer.replay(stream)
    assert reduction.snapshot.active_occurrence_ids == ()
    assert len(reduction.snapshot.execution_event_digests) == 1
    assert len(reduction.snapshot.terminal_timeout_event_digests) == 1
    assert reduction.projection.c_active_base == ()
    assert reduction.projection.q_open_base == ()


@pytest.mark.parametrize(
    "retry_status,producer_status,expected_outcome,expects_terminal",
    (
        ("unknown", "unknown", Outcome.UNKNOWN, False),
        ("error", "unknown", Outcome.UNKNOWN, False),
        ("timeout", "timeout", Outcome.TIMEOUT, True),
    ),
)
def test_latest_retry_supersedes_older_terminal_timeout_candidate(
    retry_status, producer_status, expected_outcome, expects_terminal
):
    reducer = ShadowLifecycleReducer(
        reason_registry=RETURN_OUTCOME_REASON_REGISTRY,
        recovery_registry=RETURN_OUTCOME_RECOVERY_REGISTRY,
    )
    encoder = ReturnOutcomePilotEncoder()
    session = _session()
    session.reducer = reducer
    recorder = EventRecorder(
        stream_id=f"retry-{retry_status}",
        result_occurrence_id=session.identity.result_occurrence_id,
        source_snapshot_fingerprint=session.identity.source_snapshot_fingerprint,
    )
    first = _execution_receipt("residual_totality", "timeout", ordinal=1)
    second = _execution_receipt(
        "residual_totality", retry_status, ordinal=2
    )
    for signal in (
        _signal("residual_totality", "timeout", first),
        _signal("residual_totality", producer_status, second),
    ):
        for intent in encoder(session, signal):
            recorder.append(intent)
    stream = recorder.seal()
    bindings = encoder.finalize_terminal_timeout_bindings(session, stream)
    assert bool(bindings) is expects_terminal
    if expects_terminal:
        assert bindings == ((5, next(iter(
            reducer.replay(stream).projection.q_open_base
        )).proof_requirement_id),)
    result = run_dual_write_pilot(
        legacy_outcome=expected_outcome,
        reducer=reducer,
        stream=stream,
        terminalizations=tuple(
            TerminalizationIntent(sequence, requirement)
            for sequence, requirement in bindings
        ),
    )
    assert result.candidate.decision_receipt.outcome == expected_outcome
    if retry_status == "error":
        assert stream.events[-1].header.event_type == EventType.SOLVER_ERROR


def test_production_finish_seals_latest_retry_timeout_selection_receipt():
    root = Path(__file__).resolve().parents[4]
    producer_manifest = json.loads((root / (
        "artifacts/unknown_taxonomy_v2/phase7/producer-sites.json"
    )).read_text(encoding="utf-8"))
    connector = ProductionDualWritePilotConnector(
        ShadowLifecycleReducer(
            reason_registry=RETURN_OUTCOME_REASON_REGISTRY,
            recovery_registry=RETURN_OUTCOME_RECOVERY_REGISTRY,
        ),
        domain_signal_encoder=CompositeProductionSignalEncoder({
            OutcomePartitionProductionSignal: ReturnOutcomePilotEncoder(),
        }),
        phase7_runtime_factory=lambda identity: runtime_from_audited_manifest(
            producer_manifest, identity
        ),
    )
    session = connector.begin({"phase": "6.2", "case": "retry-timeout-selection"})
    for ordinal in (1, 2):
        receipt = _execution_receipt(
            "residual_totality",
            "timeout",
            ordinal=ordinal,
            producer_attempt_ordinal=ordinal,
            execution_identity_digest=session.identity.execution_identity_digest,
        )
        signal = _signal("residual_totality", "timeout", receipt)
        session.record_phase7_pre_emission_activation(
            "outcome-partition-stage-result", signal
        )
        assert session.emit_domain_signal(signal) > 0
    legacy = SimpleNamespace(
        is_equivalent=None,
        error_message=None,
        failure_status=None,
        failure_message=None,
        is_timeout=lambda: True,
    )
    evidence = connector.finish(
        session, legacy, case_id="phase6.2-retry-timeout-selection"
    )
    evidence.validate()
    selection = session.domain_signal_state[
        "terminal_timeout_candidate_selection"
    ]
    assert selection.producer_attempt_ordinal == 2
    assert selection.execution_identity_digest == session.identity.execution_identity_digest
    assignment = session.phase7_runtime_result.terminal_timeout_assignment_receipt
    assert assignment.assignment_requirement_ids == (
        selection.proof_requirement_id,
    )
    assert assignment.execution_receipt_digests == (
        selection.execution_receipt_digest,
    )
    assert session.terminalizations == [
        TerminalizationIntent(
            selection.event_sequence_number, selection.proof_requirement_id
        )
    ]


def test_latest_timeout_selection_is_deterministic_across_requirements():
    reducer = ShadowLifecycleReducer(
        reason_registry=RETURN_OUTCOME_REASON_REGISTRY,
        recovery_registry=RETURN_OUTCOME_RECOVERY_REGISTRY,
    )
    encoder = ReturnOutcomePilotEncoder()
    session = _session()
    session.reducer = reducer
    recorder = EventRecorder(
        stream_id="different-requirement-timeouts",
        result_occurrence_id=session.identity.result_occurrence_id,
        source_snapshot_fingerprint=session.identity.source_snapshot_fingerprint,
    )
    for stage in ("same_kind_consistency", "residual_totality"):
        receipt = _execution_receipt(stage, "timeout", ordinal=1)
        for intent in encoder(session, _signal(stage, "timeout", receipt)):
            recorder.append(intent)
    stream = recorder.seal()
    bindings = encoder.finalize_terminal_timeout_bindings(session, stream)
    assert len(bindings) == 1
    selected = stream.events[bindings[0][0] - 1]
    assert selected.authority_payload.proof_requirement_id == bindings[0][1]
    assert selected == stream.events[-1]


def test_composite_timeout_selection_arbitrates_multiple_proof_domains():
    reducer = ShadowLifecycleReducer(
        reason_registry=RETURN_OUTCOME_REASON_REGISTRY,
        recovery_registry=RETURN_OUTCOME_RECOVERY_REGISTRY,
    )
    session = _session()
    session.reducer = reducer
    encoder = ReturnOutcomePilotEncoder()
    recorder = EventRecorder(
        stream_id="cross-domain-timeouts",
        result_occurrence_id=session.identity.result_occurrence_id,
        source_snapshot_fingerprint=session.identity.source_snapshot_fingerprint,
    )
    session.recorder = recorder
    for stage in ("same_kind_consistency", "residual_totality"):
        receipt = _execution_receipt(stage, "timeout", ordinal=1)
        for intent in encoder(session, _signal(stage, "timeout", receipt)):
            recorder.append(intent)
    stream = session.recorder.prefix_view().to_sealed_stream()
    timeout_events = tuple(
        event for event in stream.events
        if event.header.event_type is EventType.SOLVER_TIMEOUT
    )
    assert len(timeout_events) == 2

    class FirstDomain:
        def __call__(self, _session, _signal):
            return ()

        def finalize_terminal_timeout_bindings(self, _session, _stream):
            event = timeout_events[0]
            return ((
                event.header.sequence_number,
                event.authority_payload.proof_requirement_id,
            ),)

    class SecondDomain:
        def __call__(self, _session, _signal):
            return ()

        def finalize_terminal_timeout_bindings(self, _session, _stream):
            event = timeout_events[1]
            return ((
                event.header.sequence_number,
                event.authority_payload.proof_requirement_id,
            ),)

    class FirstSignal:
        pass

    class SecondSignal:
        pass

    composite = CompositeProductionSignalEncoder({
        FirstSignal: FirstDomain(),
        SecondSignal: SecondDomain(),
    })
    winner = composite.finalize_terminal_timeout_bindings(session, stream)
    expected = timeout_events[-1]
    assert winner == ((
        expected.header.sequence_number,
        expected.authority_payload.proof_requirement_id,
    ),)
    domain_candidates = session.domain_signal_state[
        "terminal_timeout_domain_candidate_bindings"
    ]
    projection = reducer.replay_prefix(session.recorder.prefix_view())
    view = TerminalCandidateView.freeze(session, projection)
    selection = TerminalTimeoutCandidateSelectionReceipt.issue(
        stream,
        view,
        event_sequence_number=winner[0][0],
        proof_requirement_id=winner[0][1],
        resolver_candidate_bindings=domain_candidates,
    )
    assert selection.resolver_candidate_bindings == domain_candidates
    with pytest.raises(ValueError, match="deterministic winner"):
        TerminalTimeoutCandidateSelectionReceipt.issue(
            stream,
            view,
            event_sequence_number=timeout_events[0].header.sequence_number,
            proof_requirement_id=(
                timeout_events[0].authority_payload.proof_requirement_id
            ),
            resolver_candidate_bindings=domain_candidates,
        )
    assert len({
        event.authority_payload.proof_requirement_id
        for event in stream.events
        if event.header.event_type is EventType.SOLVER_TIMEOUT
    }) == 2


@pytest.mark.parametrize("reverse_receipts", (False, True))
def test_multi_solver_receipts_share_one_timeout_producer_attempt(reverse_receipts):
    reducer = ShadowLifecycleReducer(
        reason_registry=RETURN_OUTCOME_REASON_REGISTRY,
        recovery_registry=RETURN_OUTCOME_RECOVERY_REGISTRY,
    )
    encoder = ReturnOutcomePilotEncoder()
    session = _session()
    session.reducer = reducer
    timeout_receipt = _execution_receipt(
        "residual_totality", "timeout", ordinal=1, producer_attempt_ordinal=1
    )
    unknown_receipt = _execution_receipt(
        "residual_totality", "unknown", ordinal=2, producer_attempt_ordinal=1
    )
    receipts = (timeout_receipt, unknown_receipt)
    if reverse_receipts:
        receipts = tuple(reversed(receipts))
    signal = replace(
        _signal("residual_totality", "timeout", timeout_receipt),
        execution_receipts=receipts,
    )
    recorder = EventRecorder(
        stream_id=f"multi-solver-{reverse_receipts}",
        result_occurrence_id=session.identity.result_occurrence_id,
        source_snapshot_fingerprint=session.identity.source_snapshot_fingerprint,
    )
    for intent in encoder(session, signal):
        recorder.append(intent)
    stream = recorder.seal()
    bindings = encoder.finalize_terminal_timeout_bindings(session, stream)
    assert len(bindings) == 1
    selected = stream.events[bindings[0][0] - 1]
    assert selected.header.event_type == EventType.SOLVER_TIMEOUT
    result = run_dual_write_pilot(
        legacy_outcome=Outcome.TIMEOUT,
        reducer=reducer,
        stream=stream,
        terminalizations=(TerminalizationIntent(*bindings[0]),),
    )
    assert result.candidate.decision_receipt.outcome == Outcome.TIMEOUT


def test_later_unknown_producer_attempt_supersedes_multi_solver_timeout_attempt():
    reducer = ShadowLifecycleReducer(
        reason_registry=RETURN_OUTCOME_REASON_REGISTRY,
        recovery_registry=RETURN_OUTCOME_RECOVERY_REGISTRY,
    )
    encoder = ReturnOutcomePilotEncoder()
    session = _session()
    session.reducer = reducer
    first_timeout = _execution_receipt(
        "residual_totality", "timeout", ordinal=1, producer_attempt_ordinal=1
    )
    first_unknown = _execution_receipt(
        "residual_totality", "unknown", ordinal=2, producer_attempt_ordinal=1
    )
    second_unknown = _execution_receipt(
        "residual_totality", "unknown", ordinal=3, producer_attempt_ordinal=2
    )
    signals = (
        replace(
            _signal("residual_totality", "timeout", first_timeout),
            execution_receipts=(first_timeout, first_unknown),
        ),
        _signal("residual_totality", "unknown", second_unknown),
    )
    recorder = EventRecorder(
        stream_id="multi-solver-retry",
        result_occurrence_id=session.identity.result_occurrence_id,
        source_snapshot_fingerprint=session.identity.source_snapshot_fingerprint,
    )
    for signal in signals:
        for intent in encoder(session, signal):
            recorder.append(intent)
    stream = recorder.seal()
    assert encoder.finalize_terminal_timeout_bindings(session, stream) == ()
    result = run_dual_write_pilot(
        legacy_outcome=Outcome.UNKNOWN,
        reducer=reducer,
        stream=stream,
    )
    assert result.candidate.decision_receipt.outcome == Outcome.UNKNOWN


def test_receiptless_unknown_attempt_supersedes_prior_timeout_attempt():
    reducer = ShadowLifecycleReducer(
        reason_registry=RETURN_OUTCOME_REASON_REGISTRY,
        recovery_registry=RETURN_OUTCOME_RECOVERY_REGISTRY,
    )
    encoder = ReturnOutcomePilotEncoder()
    session = _session()
    session.reducer = reducer
    timeout_receipt = _execution_receipt(
        "residual_totality", "timeout", ordinal=1, producer_attempt_ordinal=1
    )
    receiptless_unknown = replace(
        _signal("residual_totality", "unknown"),
        producer_attempt_identity="attempt-residual_totality-2",
        producer_attempt_ordinal=2,
    )
    recorder = EventRecorder(
        stream_id="receiptless-unknown-retry",
        result_occurrence_id=session.identity.result_occurrence_id,
        source_snapshot_fingerprint=session.identity.source_snapshot_fingerprint,
    )
    for signal in (
        _signal("residual_totality", "timeout", timeout_receipt),
        receiptless_unknown,
    ):
        for intent in encoder(session, signal):
            recorder.append(intent)
    stream = recorder.seal()
    assert stream.events[-1].header.event_type == EventType.OUTCOME_PRODUCER_ATTEMPT
    assert encoder.finalize_terminal_timeout_bindings(session, stream) == ()
    result = run_dual_write_pilot(
        legacy_outcome=Outcome.UNKNOWN,
        reducer=reducer,
        stream=stream,
    )
    assert result.candidate.decision_receipt.outcome == Outcome.UNKNOWN


def test_default_off_never_enters_v2_capture_or_signal_authority(monkeypatch):
    import scripts.function_tracer_pcode.equivalence.obligations.outcome_partition as module
    import scripts.function_tracer_pcode.equivalence.v2.return_outcome as return_module

    def forbidden(*_args, **_kwargs):
        raise AssertionError("default-off production path entered v2 authority")

    monkeypatch.setattr(return_module, "outcome_stage_capture_scope", forbidden)
    monkeypatch.setattr(module, "_emit_outcome_producer_pilot_signal", forbidden)
    producers = {
        stage: (lambda: UnaryProducerResult("proved"))
        for stage in (
            "termination_classification", "cfg_reachability",
            "path_region_completeness", "member_classification",
            "same_kind_consistency", "cross_kind_disjointness",
            "residual_totality", "partition_complete",
        )
    }
    proof = prove_unary_partition(
        _analysis(_seed(stable_key=lambda: ("default-off-isolation",))),
        domain_contract=("all_inputs",),
        normalization_policy_digest="default-off-isolation-v1",
        producers=producers,
    )
    assert proof.complete


def test_active_shadow_validation_failure_does_not_change_v1_producer_result():
    connector = ProductionDualWritePilotConnector(
        ShadowLifecycleReducer(
            reason_registry=RETURN_OUTCOME_REASON_REGISTRY,
            recovery_registry=RETURN_OUTCOME_RECOVERY_REGISTRY,
        ),
        domain_signal_encoder=ReturnOutcomePilotEncoder(),
    )
    session = connector.begin({"phase": "6.2", "case": "shadow-fail-closed"})
    with production_signal_scope(session):
        proof = prove_unary_partition(
            _analysis(_seed(stable_key=lambda: ("shadow-fail-closed",))),
            domain_contract=("all_inputs",),
            normalization_policy_digest="shadow-fail-closed-v1",
            producers={
                "termination_classification": lambda: UnaryProducerResult("unknown")
            },
        )
    assert proof.status == "unknown"
    assert proof.blocker_kind == "outcome_termination_classification_unknown"
    assert session.domain_signal_error_kinds == ["ValueError"]
    assert session.observed_domain_signal_count == 1


def test_retry_invocations_bind_session_identity_and_monotonic_ordinal():
    from scripts.function_tracer_pcode.equivalence.v2.return_outcome import (
        capture_active_outcome_solver_result,
        outcome_stage_capture_scope,
    )

    counter = {"value": 0}

    def next_ordinal():
        counter["value"] += 1
        return counter["value"]

    aggregate = ParallelResult([
        SolverResult("Z3", SolverStatus.UNKNOWN, elapsed_time=0.001)
    ])
    receipts = []
    for _attempt in range(2):
        with outcome_stage_capture_scope(
            seed=_seed(),
            stage="same_kind_consistency",
            premise_digest="premise-a",
            function_snapshot_fingerprint="function-snapshot-a",
            execution_identity_digest="session-execution-a",
            next_invocation_ordinal=next_ordinal,
        ):
            receipts.extend(capture_active_outcome_solver_result(
                query="(check-sat)",
                parallel_result=aggregate,
                configured_timeout_ms=10000,
            ))
    assert tuple(item.invocation_ordinal for item in receipts) == (1, 2)
    assert all(
        item.execution_identity_digest == "session-execution-a"
        for item in receipts
    )
    assert receipts[0].invocation_identity != receipts[1].invocation_identity
    assert receipts[0].receipt_digest != receipts[1].receipt_digest


def test_receipt_bound_solver_event_round_trips_with_recomputable_body():
    encoder = ReturnOutcomePilotEncoder()
    session = _session()
    receipt = _execution_receipt("same_kind_consistency", "unknown")
    recorder = EventRecorder(
        stream_id="receipt-roundtrip",
        result_occurrence_id=session.identity.result_occurrence_id,
        source_snapshot_fingerprint=session.identity.source_snapshot_fingerprint,
    )
    for intent in encoder(
        session, _signal("same_kind_consistency", "unknown", receipt)
    ):
        recorder.append(intent)
    stream = recorder.seal()
    codec = StrictV2JsonCodec(
        reason_registry=RETURN_OUTCOME_REASON_REGISTRY,
        recovery_registry=RETURN_OUTCOME_RECOVERY_REGISTRY,
    )
    decoded = codec.loads(codec.dumps(stream))
    assert decoded == stream
    payload = decoded.events[2].authority_payload
    assert payload.execution_receipt_digest == receipt.receipt_digest
    assert payload.execution_receipt_authority["query_digest"] == receipt.query_digest
    forged_body = dict(payload.execution_receipt_authority)
    forged_body["query_digest"] = "forged-query"
    with pytest.raises(ValueError, match="receipt authority digest mismatch"):
        ReceiptBoundSolverExecutionEventAuthority(
            payload.proof_requirement_id,
            forged_body,
            False,
        )
    wrong_type = dict(payload.execution_receipt_authority)
    wrong_type["query_digest"] = 7
    unsigned = dict(wrong_type)
    unsigned.pop("receipt_digest")
    wrong_type["receipt_digest"] = authority_digest(unsigned)
    with pytest.raises(TypeError, match="non-empty exact strings"):
        ReceiptBoundSolverExecutionEventAuthority(
            payload.proof_requirement_id, wrong_type, False
        )
    wrong_status = dict(payload.execution_receipt_authority)
    wrong_status["observed_status"] = "timeout"
    unsigned = dict(wrong_status)
    unsigned.pop("receipt_digest")
    wrong_status["receipt_digest"] = authority_digest(unsigned)
    forged_status_payload = ReceiptBoundSolverExecutionEventAuthority(
        payload.proof_requirement_id, wrong_status, True
    )
    with pytest.raises(ValueError, match="event type and observed status differ"):
        EventIntent(EventType.SOLVER_UNKNOWN, forged_status_payload)


def test_actual_producer_timeout_reaches_terminal_time_out_decision():
    connector = ProductionDualWritePilotConnector(
        ShadowLifecycleReducer(
            reason_registry=RETURN_OUTCOME_REASON_REGISTRY,
            recovery_registry=RETURN_OUTCOME_RECOVERY_REGISTRY,
        ),
        domain_signal_encoder=ReturnOutcomePilotEncoder(),
    )
    session = connector.begin({"phase": "6.2", "case": "actual-producer-timeout"})
    _analysis_value, proof = _run_actual_timeout_attempt(
        session, "actual-timeout-seed"
    )
    assert proof.status == "timeout"
    assert session.domain_signal_error_kinds == [], session.domain_signal_error_details
    legacy = SimpleNamespace(
        is_equivalent=None,
        error_message=None,
        failure_status=None,
        failure_message=None,
        is_timeout=lambda: True,
    )
    evidence = connector.finish(
        session, legacy, case_id="phase6.2-actual-producer-timeout"
    )
    evidence.validate()
    assert evidence.pilot_result.candidate.decision_receipt.outcome == Outcome.TIMEOUT
    timeout_events = tuple(
        event for event in evidence.pilot_result.sealed_event_stream.events
        if event.header.event_type == EventType.SOLVER_TIMEOUT
    )
    assert len(timeout_events) == 1
    assert session.terminalizations[0].event_sequence_number == (
        timeout_events[0].header.sequence_number
    )


def test_actual_timeout_then_same_session_proved_completion_is_nonterminal():
    reducer = ShadowLifecycleReducer(
        reason_registry=RETURN_OUTCOME_REASON_REGISTRY,
        recovery_registry=RETURN_OUTCOME_RECOVERY_REGISTRY,
    )
    connector = ProductionDualWritePilotConnector(
        reducer,
        domain_signal_encoder=ReturnOutcomePilotEncoder(),
    )
    session = connector.begin({"phase": "6.2", "case": "actual-timeout-recovery"})
    analysis, first = _run_actual_timeout_attempt(
        session, "actual-timeout-recovery-seed"
    )
    assert first.status == "timeout"
    proved_producers = {
        stage: (lambda: UnaryProducerResult("proved"))
        for stage in (
            "termination_classification", "cfg_reachability",
            "path_region_completeness", "member_classification",
            "same_kind_consistency", "cross_kind_disjointness",
            "residual_totality", "partition_complete",
        )
    }
    with production_signal_scope(session):
        recovered = prove_unary_partition(
            analysis,
            domain_contract=("all_inputs",),
            normalization_policy_digest="actual-timeout-recovery-seed-policy-v1",
            producers=proved_producers,
        )
    assert recovered.complete
    assert session.domain_signal_error_kinds == [], session.domain_signal_error_details
    stream = session.recorder.seal()
    assert session.domain_signal_encoder.finalize_terminal_timeout_bindings(
        session, stream
    ) == ()
    reduction = reducer.replay(stream)
    assert reduction.projection.c_active_base == ()
    assert reduction.projection.q_open_base == ()
    assert len(tuple(
        event for event in stream.events
        if event.header.event_type == EventType.SOLVER_TIMEOUT
    )) == 1


def test_slice2_inventory_delta_exactly_matches_current_source():
    root = Path(__file__).resolve().parents[4]
    frozen = json.loads(
        (root / "artifacts/unknown_reason_audit/current-head/inventory-review.json").read_text()
    )
    slice1 = json.loads(
        (root / "artifacts/unknown_taxonomy_v2/phase6/slice1_inventory_delta.json").read_text()
    )
    delta = json.loads(
        (root / "artifacts/unknown_taxonomy_v2/phase6/slice2_inventory_delta.json").read_text()
    )
    current = build_inventory_review_template(root)
    previous_ids = {row["site_id"] for row in frozen["entries"]}
    previous_ids -= {row["site_id"] for row in slice1["removed"]}
    previous_ids |= {row["site_id"] for row in slice1["added"]}
    current_ids = {row["site_id"] for row in current["entries"]}
    assert delta["previous_slice"] == slice1["current_source"]
    assert delta["current_source"] == {
        "candidate_set_digest": current["candidate_set_digest"],
        "candidate_count": len(current_ids),
    }
    assert {row["site_id"] for row in delta["added"]} == current_ids - previous_ids
    assert {row["site_id"] for row in delta["removed"]} == previous_ids - current_ids
    assert all(row["review_status"] == "reviewed_by_main_pending_fixed_review" for row in delta["added"])
