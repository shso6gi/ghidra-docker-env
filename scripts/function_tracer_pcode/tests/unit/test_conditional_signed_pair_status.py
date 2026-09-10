# -*- coding: utf-8 -*-
"""Issue #20 PR-A: the conditional column survives the production status path.

These tests drive the real chain -- production pilot -> signed canonical result
bundle -> persisted result envelope -> ``classify_pair_status`` -> sealed
pair-status -> ``validate_signed_pair_status`` -> ``PairOutcome`` -> benchmark
gate -- so the assumption-dependent column cannot silently be dropped between
the checker and the runner.  Nothing here hand-writes a status body for the
conditional part: every conditional field comes from a real
``ConditionalDecisionReceipt``.
"""
from __future__ import annotations

import json
from pathlib import Path
from types import SimpleNamespace

import pytest

from scripts.function_tracer_pcode.authority.contracts import (
    Outcome,
    VerifiedLifecycleProjection,
    authority_digest,
)
from scripts.function_tracer_pcode.authority.decision.canonical_result import (
    BUNDLE_KIND,
    SupervisorCanonicalResultResolvedReceipt,
    build_canonical_result_finalization_bundle,
    classify_pair_status,
    persist_canonical_result_envelope,
    validate_canonical_result_finalization_bundle,
)
from scripts.function_tracer_pcode.authority.decision.conditional import (
    ConditionalDecisiveProofKind,
    conditional_decision_receipt_from_payload,
    ConditionalDecisiveProofReceipt,
    ConditionalFinalizationAuthority,
    conditional_decision_receipt_payload,
    finalize_conditional_decision,
)
from scripts.function_tracer_pcode.authority.decision.pair_status_authority import (
    PAIR_STATUS_CONDITIONAL_FIELDS,
    PAIR_STATUS_PUBLIC_KEY_FILE,
    generate_pair_status_keypair,
    seal_pair_status,
    validate_signed_pair_status,
)
from scripts.function_tracer_pcode.authority.decision.production_cutover import (
    attach_canonical_decision,
    attach_conditional_decision,
)
from scripts.function_tracer_pcode.authority.lifecycle.execution_authority import (
    PINNED_SOLVER_EXECUTION_ISSUER,
)
from scripts.function_tracer_pcode.authority.lifecycle.pilot import (
    ProductionDualWritePilotConnector,
)
from scripts.function_tracer_pcode.authority.lifecycle.production_signals import (
    CompositeProductionSignalEncoder,
)
from scripts.function_tracer_pcode.authority.lifecycle.reducer import ShadowLifecycleReducer
from scripts.function_tracer_pcode.authority.process.operational_extraction import (
    OPERATIONAL_REASON_REGISTRY,
    OPERATIONAL_RECOVERY_REGISTRY,
    OperationalBlockerSignal,
    OperationalCompletionSignal,
    OperationalExtractionPilotEncoder,
)
from scripts.function_tracer_pcode.authority.process.supervisor import (
    DurableCheckpointStore,
    ProcessSupervisorAuthorityFactory,
)
from scripts.function_tracer_pcode.authority.process.supervisor_command import COMMAND_SCHEMA
from scripts.function_tracer_pcode.checker.result import EquivalenceResult
from scripts.function_tracer_pcode.proof.assumptions import (
    AssumptionKind,
    AssumptionPremise,
)
from scripts.function_tracer_pcode.reporting import benchmark_validation_gate as gate
from scripts.function_tracer_pcode.reporting.pair_outcomes import iter_pair_outcomes
from scripts.function_tracer_pcode.reporting.result_summary import (
    aggregate_validation_logs,
)
from scripts.function_tracer_pcode.smt import ParallelResult

from scripts.function_tracer_pcode.tests.unit.test_benchmark_validation_gate import (
    EQ,
    NEQ,
    _manifest,
)

SUPERVISOR_KEY = b"s" * 32
WORKER_KEY = b"w" * 32
DIGEST = "a" * 64


def _unknown_pilot(case: str):
    """Run a real production pilot to an unconditional UNKNOWN decision."""
    from scripts.function_tracer_pcode.tests.unit.test_unknown_taxonomy_v2_phase6_operational_extraction import (
        Function,
        Program,
    )

    operational = OperationalExtractionPilotEncoder()
    connector = ProductionDualWritePilotConnector(
        ShadowLifecycleReducer(
            reason_registry=OPERATIONAL_REASON_REGISTRY,
            recovery_registry=OPERATIONAL_RECOVERY_REGISTRY,
        ),
        domain_signal_encoder=CompositeProductionSignalEncoder({
            OperationalBlockerSignal: operational,
            OperationalCompletionSignal: operational,
        }),
    )
    execution_payload = {"case": case}
    session = connector.begin(execution_payload)
    session.result_entry_occurrence_receipt = (
        PINNED_SOLVER_EXECUTION_ISSUER.issue_result_entry_occurrence(
            result_occurrence_id=session.identity.result_occurrence_id,
            execution_payload_digest=authority_digest(execution_payload),
            startup_receipt_digests=("startup-receipt",),
            occurrence_nonce="occurrence-nonce-1",
        )
    )
    factory = operational.authority_factory_for_session(session)
    manager = type("Manager", (), {
        "functions": (),
        "getFunctions": lambda self, forward: iter(self.functions),
    })()
    program = Program(manager)
    function = Function(program=program)
    manager.functions = (function,)
    seed = factory.issue_program_seed(program, binary_content_identity="sha256:binary")
    assert session.emit_domain_signal(OperationalBlockerSignal(
        "function_decompilation_artifact_unavailable",
        factory.target_from_ghidra(seed, function),
        ("return-analyzer-top-level-decompile-v2",),
        "function-decompilation-artifact-producer-v2",
    )) == 1
    evidence = connector.finish(session, SimpleNamespace(
        is_equivalent=None, error_message=None, failure_status=None,
        failure_message=None, unknown_reasons=[], unknown_recovery_actions=[],
        is_timeout=lambda: False,
    ), case_id=case)
    decision = evidence.pilot_result.candidate.decision_receipt
    assert decision.outcome is Outcome.UNKNOWN
    return session, evidence, decision


def _conditional_receipt(decision, conditional_outcome: Outcome):
    """Issue a real conditional decision against one unconditional UNKNOWN."""
    result_id = decision.result_occurrence_id
    projection = VerifiedLifecycleProjection.seal(
        result_occurrence_id=result_id,
        snapshot_digest="conditional-snapshot",
        c_active_base=(), q_open_base=(), blocker_eligibility_base=(),
        satisfaction_projection={"live": ()},
    )
    premise = AssumptionPremise(
        kind=AssumptionKind.EXTERNAL_CALLEE_SPEC, subject="log",
        payload={"canonical_symbol": "log", "no_observable_memory_write": True},
    )
    proof = ConditionalDecisiveProofReceipt.create(
        result_occurrence_id=result_id,
        lifecycle_projection_digest=projection.lifecycle_projection_digest,
        proof_kind=(
            ConditionalDecisiveProofKind.CONDITIONAL_EQ_CLOSURE
            if conditional_outcome is Outcome.EQUIVALENT
            else ConditionalDecisiveProofKind.CONDITIONAL_SAFE_COUNTEREXAMPLE
        ),
        proof_artifact_digest="conditional-proof",
        assumption_dependencies=(premise,),
    )
    receipt = finalize_conditional_decision(ConditionalFinalizationAuthority(
        result_id, decision, projection, (premise,),
        conditional_decisive_proof_receipts=(proof,),
    ))
    assert receipt.conditional_outcome is conditional_outcome
    return receipt


def _execution_target(sample: str, function: str, left: str, right: str):
    target = {
        "schema": "eqbench-pair-execution-target-v1",
        "authority_kind": "PairExecutionTargetReceipt",
        "sample_identity": sample, "output_sample_relative_path": sample,
        "function_name": function, "left_binary_id": left,
        "right_binary_id": right, "source_path": "source.c",
        "source_sha256": DIGEST, "left_binary_path": "left.bin",
        "left_binary_sha256": DIGEST, "right_binary_path": "right.bin",
        "right_binary_sha256": DIGEST, "analysis_source_digest": DIGEST,
        "analysis_config_digest": DIGEST,
    }
    target["target_digest"] = authority_digest(target)
    return target


def _classified_pair_status(
    tmp_path: Path, monkeypatch, *, case: str, conditional_outcome=None,
):
    """Drive the whole production path and return ``classify_pair_status``."""
    workspace = tmp_path / case
    workspace.mkdir(parents=True, exist_ok=True)
    supervisor_key_file = workspace / "supervisor.key"
    supervisor_key_file.write_bytes(SUPERVISOR_KEY)
    worker_key_file = workspace / "worker.key"
    worker_key_file.write_bytes(WORKER_KEY)
    checkpoint_root = workspace / "checkpoints"
    nonce = "execution-nonce-1"
    monkeypatch.setenv("UNKNOWN_TAXONOMY_V2_SUPERVISOR_KEY_ID", "supervisor-key-v1")
    monkeypatch.setenv("UNKNOWN_TAXONOMY_V2_SUPERVISOR_KEY_FILE", str(supervisor_key_file))
    monkeypatch.setenv("UNKNOWN_TAXONOMY_V2_SUPERVISOR_ROOT", str(checkpoint_root))
    monkeypatch.setenv("UNKNOWN_TAXONOMY_V2_EXECUTION_NONCE", nonce)
    monkeypatch.setenv(
        "UNKNOWN_TAXONOMY_V2_RESULT_ENTRY_OCCURRENCE_NONCE", "occurrence-nonce-1"
    )

    session, evidence, decision = _unknown_pilot(case)
    result = EquivalenceResult(
        is_equivalent=None, function1_name="f", function2_name="f",
        binary1_name="left.bin", binary2_name="right.bin",
        solver_results=ParallelResult(results=[]),
    )
    attach_canonical_decision(result, decision)
    conditional = None
    if conditional_outcome is not None:
        conditional = _conditional_receipt(decision, conditional_outcome)
        attach_conditional_decision(result, conditional)
    preimage = result.to_dict()
    bundle = build_canonical_result_finalization_bundle(
        result_payload_preimage=preimage, evidence=evidence, session=session,
    )
    full_payload = {**preimage, "canonical_result_finalization_bundle": bundle}
    assert persist_canonical_result_envelope(full_payload) is not None
    validated = validate_canonical_result_finalization_bundle(
        bundle, result_payload_preimage=preimage,
        bundle_verification_key_id="supervisor-key-v1",
        bundle_verification_key=SUPERVISOR_KEY,
    )
    identity = validated["execution_identity"]

    factory = ProcessSupervisorAuthorityFactory(
        supervisor_signing_key_id="supervisor-key-v1",
        supervisor_signing_key=SUPERVISOR_KEY,
        worker_signing_key_id="worker-key-v1",
        worker_signing_key=WORKER_KEY,
    )
    store = DurableCheckpointStore(checkpoint_root, factory, nonce)
    launch = factory.issue_launch(
        result_occurrence_id=identity["result_occurrence_id"],
        manifest_entry_preimage_digest="manifest-entry-digest",
        execution_nonce=nonce, child_pid=4242,
        child_start_token="pid-start-token", stream_id=identity["stream_id"],
        source_snapshot_fingerprint=identity["source_snapshot_fingerprint"],
        deadline_policy_digest="deadline-policy-digest",
    )
    store.persist_launch(launch)
    canonical_receipt = SupervisorCanonicalResultResolvedReceipt.create(
        launch_receipt_digest=launch.receipt_digest,
        result_occurrence_id=identity["result_occurrence_id"],
        execution_identity_digest=identity["execution_identity_digest"],
        child_returncode=2,
        canonical_result_bundle_digest=validated["bundle_digest"],
        payload_preimage_digest=validated["payload_preimage_digest"],
        decision_receipt_digest=validated["decision_receipt_digest"],
    )
    (store.directory / "canonical-resolved-receipt.json").write_text(
        json.dumps({
            name: getattr(canonical_receipt, name)
            for name in canonical_receipt.__dataclass_fields__
        }, sort_keys=True), encoding="utf-8",
    )
    projection_body = {
        "status": "RESOLVED",
        "authority_kind": "SupervisorCanonicalResultResolvedReceipt",
        "supervisor_authority_kind": "SupervisorCanonicalResultResolvedReceipt",
        "supervisor_final_authority_digest": canonical_receipt.receipt_digest,
        "launch_receipt_digest": launch.receipt_digest,
        "canonical_outcome": validated["outcome"],
        "decision_receipt_digest": validated["decision_receipt_digest"],
        "result_occurrence_id": identity["result_occurrence_id"],
        "result_entry_occurrence_receipt_digest": (
            bundle["result_entry_occurrence_receipt"]["receipt_digest"]
        ),
        "execution_identity_digest": identity["execution_identity_digest"],
        "stream_id": identity["stream_id"],
        "source_snapshot_fingerprint": identity["source_snapshot_fingerprint"],
        "canonical_result_bundle_digest": validated["bundle_digest"],
        "canonical_result_bundle_kind": BUNDLE_KIND,
        "canonical_result_payload_preimage_digest": validated["payload_preimage_digest"],
        "semantic_projection_digest": validated["semantic_projection_digest"],
        "error_kind": None, "child_returncode": 2,
        "classification_valid": True, "projection_schema": COMMAND_SCHEMA,
    }
    projection_body["projection_digest"] = authority_digest(projection_body)
    projection_path = workspace / "supervisor.json"
    projection_path.write_text(json.dumps(projection_body, sort_keys=True), encoding="utf-8")
    log_path = workspace / "f_B1_B2.log"
    log_path.write_text("\n".join((
        "=== EQUIVALENCE_RESULT_JSON_BEGIN ===",
        json.dumps(full_payload, sort_keys=True),
        "=== EQUIVALENCE_RESULT_JSON_END ===",
    )), encoding="utf-8")

    status = classify_pair_status(
        log_path, projection_path, checkpoint_root=checkpoint_root,
        execution_nonce=nonce, supervisor_signing_key_id="supervisor-key-v1",
        supervisor_signing_key_file=supervisor_key_file,
        worker_signing_key_id="worker-key-v1",
        worker_signing_key_file=worker_key_file,
    )
    return SimpleNamespace(
        status=status, decision=decision, conditional=conditional,
        result_payload=full_payload, log_path=log_path,
    )


def _seal(root: Path, sample: str, function: str, left: str, right: str, status):
    path = root / sample / function / f"{function}_{left}_{right}.pair-status.json"
    path.parent.mkdir(parents=True, exist_ok=True)
    private_key = root / ".pair-status-test.key"
    public_key = root / PAIR_STATUS_PUBLIC_KEY_FILE
    if not private_key.exists():
        generate_pair_status_keypair(private_key, public_key)
    sealed = seal_pair_status(
        {**status, "pair_execution_target": _execution_target(sample, function, left, right)},
        private_key_path=private_key, public_key_path=public_key,
    )
    path.write_text(json.dumps(sealed, sort_keys=True), encoding="utf-8")
    return path, sealed, public_key


# --- the production chain ---------------------------------------------------


def test_conditional_column_survives_classify_seal_validate_and_pair_outcome(
    tmp_path, monkeypatch,
):
    run = _classified_pair_status(
        tmp_path, monkeypatch, case="conditional-eq", conditional_outcome=Outcome.EQUIVALENT,
    )
    status = run.status

    # classify_pair_status lifted the column out of the signed result payload.
    assert status["canonical_outcome"] == "UNKNOWN"
    assert status["conditional_outcome"] == "EQUIVALENT"
    assert status["conditional_decision_receipt"] == conditional_decision_receipt_payload(
        run.conditional
    )
    # It joins this pair's unconditional decision, not just any receipt.
    assert status["conditional_decision_receipt"]["unconditional_receipt_digest"] == (
        status["decision_receipt_digest"]
    )
    assert status["conditional_decision_receipt"]["result_occurrence_id"] == (
        status["result_occurrence_id"]
    )

    root = tmp_path / "results"
    path, sealed, public_key = _seal(root, EQ, "f", "B1", "B2", status)
    body = validate_signed_pair_status(
        json.loads(path.read_text(encoding="utf-8")), public_key_path=public_key,
    )
    assert body["conditional_outcome"] == "EQUIVALENT"
    assert set(PAIR_STATUS_CONDITIONAL_FIELDS) <= set(sealed)

    outcomes = list(iter_pair_outcomes(root))
    assert len(outcomes) == 1
    assert outcomes[0].outcome == "UNKNOWN"
    assert outcomes[0].conditional_outcome == "EQUIVALENT"

    # The summary reads the same column from the log payload, in its own count.
    record = aggregate_validation_logs([run.log_path], canonical_only=False)
    assert record.counts["UNKNOWN"] == 1
    assert record.conditional_counts == {"EQUIVALENT": 1}

    # In canonical mode the signed body is the authority for the column, and
    # the log payload has to agree with it.
    canonical_log = path.with_suffix("").with_suffix(".log")
    canonical_log.write_text(run.log_path.read_text(encoding="utf-8"), encoding="utf-8")
    canonical = aggregate_validation_logs([canonical_log], canonical_only=True)
    assert canonical.counts["UNKNOWN"] == 1
    assert canonical.conditional_counts == {"EQUIVALENT": 1}

    tampered = dict(json.loads(path.read_text(encoding="utf-8")))
    body_without_seal = {
        key: value for key, value in tampered.items()
        if not key.startswith("pair_status_")
    }
    assert body_without_seal["conditional_outcome"] == "EQUIVALENT"
    payload = json.loads(
        run.log_path.read_text(encoding="utf-8").split(
            "=== EQUIVALENCE_RESULT_JSON_BEGIN ==="
        )[1].split("=== EQUIVALENCE_RESULT_JSON_END ===")[0]
    )
    payload.pop("conditional_outcome")
    payload.pop("conditional_decision_receipt")
    canonical_log.write_text("\n".join((
        "=== EQUIVALENCE_RESULT_JSON_BEGIN ===",
        json.dumps(payload, sort_keys=True),
        "=== EQUIVALENCE_RESULT_JSON_END ===",
    )), encoding="utf-8")
    with pytest.raises(ValueError, match="differs from the result payload"):
        aggregate_validation_logs([canonical_log], canonical_only=True)


def test_a_pair_without_a_conditional_decision_keeps_the_v1_field_set(
    tmp_path, monkeypatch,
):
    run = _classified_pair_status(tmp_path, monkeypatch, case="no-conditional")
    status = run.status
    assert not set(PAIR_STATUS_CONDITIONAL_FIELDS) & set(status)

    root = tmp_path / "results"
    path, sealed, public_key = _seal(root, EQ, "f", "B1", "B2", status)
    assert not set(PAIR_STATUS_CONDITIONAL_FIELDS) & set(sealed)
    body = validate_signed_pair_status(
        json.loads(path.read_text(encoding="utf-8")), public_key_path=public_key,
    )
    assert "conditional_outcome" not in body
    assert list(iter_pair_outcomes(root))[0].conditional_outcome is None


# --- benchmark gate, both directions ----------------------------------------


@pytest.mark.parametrize("sample,function,conditional,kind", [
    (EQ, "f", Outcome.NOT_EQ, gate.KIND_EQ_NOT_EQ),
    (NEQ, "confirmed", Outcome.EQUIVALENT, gate.KIND_NEQ_CONFIRMED_NOT_EQ_EQUIVALENT),
])
def test_gate_detects_a_conditional_ground_truth_violation_through_signed_status(
    tmp_path, monkeypatch, sample, function, conditional, kind,
):
    run = _classified_pair_status(
        tmp_path, monkeypatch, case=f"gate-{kind}", conditional_outcome=conditional,
    )
    root = tmp_path / "results"
    _seal(root, sample, function, "N_B1" if sample == NEQ else "B1",
          "O_B1" if sample == NEQ else "B2", run.status)
    manifest = gate.FunctionDiffManifest.load(_manifest(tmp_path))
    report = gate.build_gate_report([root], manifest)

    # The unconditional lane saw only UNKNOWN and has nothing to report.
    assert report.hard_violations == ()
    assert [item.kind for item in report.conditional_hard_violations] == [kind]
    assert report.status == gate.GATE_STATUS_FAIL
    assert report.exit_code == gate.EXIT_VIOLATION
    section = report.health_section()
    assert section["hard_violations"][kind] == 0
    assert section["conditional"]["hard_violations"][kind] == 1


# --- tamper and cross-pair rejection ----------------------------------------


def _reseal(root: Path, path: Path, body, public_key: Path):
    private_key = root / ".pair-status-test.key"
    sealed = seal_pair_status(body, private_key_path=private_key, public_key_path=public_key)
    path.write_text(json.dumps(sealed, sort_keys=True), encoding="utf-8")
    return sealed


def test_sealing_rejects_a_conditional_column_that_does_not_join_its_pair(
    tmp_path, monkeypatch,
):
    run = _classified_pair_status(
        tmp_path, monkeypatch, case="join-eq", conditional_outcome=Outcome.EQUIVALENT,
    )
    other = _classified_pair_status(
        tmp_path, monkeypatch, case="join-other", conditional_outcome=Outcome.EQUIVALENT,
    )
    root = tmp_path / "results"
    generate_pair_status_keypair(
        root / ".pair-status-test.key", root / PAIR_STATUS_PUBLIC_KEY_FILE,
    )
    public_key = root / PAIR_STATUS_PUBLIC_KEY_FILE
    target = _execution_target(EQ, "f", "B1", "B2")

    def _body(**overrides):
        return {**run.status, "pair_execution_target": target, **overrides}

    # A receipt issued for another pair.
    with pytest.raises(ValueError, match="different pair"):
        seal_pair_status(
            _body(conditional_decision_receipt=other.status["conditional_decision_receipt"]),
            private_key_path=root / ".pair-status-test.key", public_key_path=public_key,
        )
    # The outcome flipped without touching the receipt.
    with pytest.raises(ValueError, match="contradicts its receipt"):
        seal_pair_status(
            _body(conditional_outcome="NOT_EQ"),
            private_key_path=root / ".pair-status-test.key", public_key_path=public_key,
        )
    # A tampered receipt digest.
    forged = dict(run.status["conditional_decision_receipt"])
    forged["conditional_outcome"] = "NOT_EQ"
    with pytest.raises(ValueError, match="digest mismatch"):
        seal_pair_status(
            _body(conditional_outcome="NOT_EQ", conditional_decision_receipt=forged),
            private_key_path=root / ".pair-status-test.key", public_key_path=public_key,
        )
    # Half a column: an outcome with no receipt behind it.
    half = dict(_body())
    half.pop("conditional_decision_receipt")
    with pytest.raises(ValueError, match="authority fields differ"):
        seal_pair_status(
            half, private_key_path=root / ".pair-status-test.key",
            public_key_path=public_key,
        )


def test_validation_rejects_a_conditional_column_swapped_into_a_signed_status(
    tmp_path, monkeypatch,
):
    run = _classified_pair_status(
        tmp_path, monkeypatch, case="swap-eq", conditional_outcome=Outcome.EQUIVALENT,
    )
    other = _classified_pair_status(
        tmp_path, monkeypatch, case="swap-other", conditional_outcome=Outcome.NOT_EQ,
    )
    root = tmp_path / "results"
    path, sealed, public_key = _seal(root, EQ, "f", "B1", "B2", run.status)
    body = {key: value for key, value in sealed.items() if not key.startswith("pair_status_")}

    # Re-signing with a foreign conditional receipt is rejected at seal time,
    # and a hand-forged seal is rejected at validation time.
    forged = {
        **body,
        "conditional_outcome": other.status["conditional_outcome"],
        "conditional_decision_receipt": other.status["conditional_decision_receipt"],
    }
    with pytest.raises(ValueError, match="different pair"):
        _reseal(root, path, forged, public_key)

    signed = json.loads(path.read_text(encoding="utf-8"))
    signed["conditional_decision_receipt"] = other.status["conditional_decision_receipt"]
    with pytest.raises(ValueError, match="pair-status seal metadata is invalid"):
        validate_signed_pair_status(signed, public_key_path=public_key)


def test_a_conditional_column_is_refused_on_a_decided_pair(tmp_path, monkeypatch):
    """The lane runs only after an unconditional UNKNOWN, and sealing agrees."""
    run = _classified_pair_status(
        tmp_path, monkeypatch, case="decided", conditional_outcome=Outcome.EQUIVALENT,
    )
    root = tmp_path / "results"
    generate_pair_status_keypair(
        root / ".pair-status-test.key", root / PAIR_STATUS_PUBLIC_KEY_FILE,
    )
    decided = {
        **run.status,
        "canonical_outcome": "EQUIVALENT",
        "child_returncode": 0,
        "pair_execution_target": _execution_target(EQ, "f", "B1", "B2"),
    }
    with pytest.raises(ValueError, match="requires an unconditional UNKNOWN"):
        seal_pair_status(
            decided, private_key_path=root / ".pair-status-test.key",
            public_key_path=root / PAIR_STATUS_PUBLIC_KEY_FILE,
        )


def test_assumption_dependencies_are_recoverable_from_the_signed_pair_status(
    tmp_path, monkeypatch,
):
    """The signed artifact alone answers: what did this conditional EQ assume?"""
    run = _classified_pair_status(
        tmp_path, monkeypatch, case="audit", conditional_outcome=Outcome.EQUIVALENT,
    )
    root = tmp_path / "results"
    path, _sealed, public_key = _seal(root, EQ, "f", "B1", "B2", run.status)

    # Read the file back the way a reviewer would: nothing but the bytes on disk.
    body = validate_signed_pair_status(
        json.loads(path.read_text(encoding="utf-8")), public_key_path=public_key,
    )
    receipt = conditional_decision_receipt_from_payload(body["conditional_decision_receipt"])
    assert body["conditional_outcome"] == "EQUIVALENT"
    assert receipt.conditional_outcome is Outcome.EQUIVALENT
    assert [premise.subject for premise in receipt.assumption_set] == ["log"]
    premise = receipt.assumption_set[0]
    assert premise.kind is AssumptionKind.EXTERNAL_CALLEE_SPEC
    assert premise.payload_value("canonical_symbol") == "log"
    assert premise.payload_value("no_observable_memory_write") is True
    assert authority_digest(receipt.assumption_set) == receipt.assumption_set_digest
    assert receipt == run.conditional


def test_sealing_rejects_a_conditional_receipt_whose_assumption_set_was_edited(
    tmp_path, monkeypatch,
):
    run = _classified_pair_status(
        tmp_path, monkeypatch, case="assumption-tamper",
        conditional_outcome=Outcome.EQUIVALENT,
    )
    root = tmp_path / "results"
    generate_pair_status_keypair(
        root / ".pair-status-test.key", root / PAIR_STATUS_PUBLIC_KEY_FILE,
    )
    target = _execution_target(EQ, "f", "B1", "B2")

    for mutate, message in (
        (lambda column: column["assumption_set"][0].__setitem__("subject", "sqrt"),
         "assumption set digest mismatch"),
        (lambda column: column["assumption_set"].append(column["assumption_set"][0]),
         "not canonical"),
        (lambda column: column["assumption_set"].clear(),
         "requires its assumption set"),
    ):
        column = json.loads(json.dumps(run.status["conditional_decision_receipt"]))
        mutate(column)
        with pytest.raises(ValueError, match=message):
            seal_pair_status(
                {**run.status, "conditional_decision_receipt": column,
                 "pair_execution_target": target},
                private_key_path=root / ".pair-status-test.key",
                public_key_path=root / PAIR_STATUS_PUBLIC_KEY_FILE,
            )
