from types import SimpleNamespace
from copy import copy, deepcopy
import json
from pathlib import Path

import pytest

from scripts.function_tracer_pcode.equivalence.result import EquivalenceResult
from scripts.function_tracer_pcode.equivalence.v2.contracts import (
    BlockerEligibilityBaseRow,
    CActiveBaseRow,
    Outcome,
    QOpenBaseRow,
    VerifiedLifecycleProjection,
    authority_digest,
)
from scripts.function_tracer_pcode.equivalence.v2.decision import (
    DecisiveProofKind,
    DecisiveProofReceipt,
    ErrorReceipt,
    FinalizationAuthority,
    TerminalTimeoutReceipt,
    finalize_decision,
)
from scripts.function_tracer_pcode.equivalence.v2.phase8_cutover import (
    BATCH_RESUME_MATRIX,
    CLI_EXIT_MATRIX,
    RETRY_FALLBACK_MATRIX,
    attach_canonical_decision,
    attach_canonical_relations,
    outcome_from_payload,
    rematerialize_process_timeout_decision,
)
from scripts.function_tracer_pcode.equivalence.v2.pair_status_authority import (
    PAIR_STATUS_PUBLIC_KEY_FILE,
    generate_pair_status_keypair,
    seal_pair_status,
)
from scripts.function_tracer_pcode.smt import ParallelResult
from scripts.function_tracer_pcode.validation.result_summary import (
    aggregate_validation_logs_by_function,
    build_run_health_summary,
    classify_canonical_log_text,
    classify_result_payload,
    read_validation_log_record,
)


def _projection(result_id, *, active=False, open_requirement=False):
    causes = (
        CActiveBaseRow(
            result_id, "occurrence", "cause", "reason", "domain",
            "blocks_decision", "target",
        ),
    ) if active else ()
    requirements = (
        QOpenBaseRow(
            result_id, "occurrence", "cause", "requirement", "proof",
            "target-digest",
        ),
    ) if open_requirement else ()
    return VerifiedLifecycleProjection.seal(
        result_occurrence_id=result_id,
        snapshot_digest=authority_digest((result_id, "snapshot")),
        c_active_base=causes,
        q_open_base=requirements,
        blocker_eligibility_base=(
            (BlockerEligibilityBaseRow(result_id, "occurrence", "cause"),)
            if active else ()
        ),
        satisfaction_projection=(),
    )


def _receipt(outcome):
    result_id = "result-" + outcome.value.lower()
    projection = _projection(
        result_id,
        active=outcome in {Outcome.UNKNOWN, Outcome.TIMEOUT},
        open_requirement=outcome is Outcome.TIMEOUT,
    )
    decisive = ()
    timeout = ()
    errors = ()
    if outcome in {Outcome.EQUIVALENT, Outcome.NOT_EQ}:
        kind = (
            DecisiveProofKind.EQ_CLOSURE
            if outcome is Outcome.EQUIVALENT
            else DecisiveProofKind.SAFE_COUNTEREXAMPLE
        )
        decisive = (DecisiveProofReceipt.create(
            result_occurrence_id=result_id,
            lifecycle_projection_digest=projection.lifecycle_projection_digest,
            proof_kind=kind,
            proof_artifact_digest="proof-artifact",
        ),)
    elif outcome is Outcome.TIMEOUT:
        timeout = (TerminalTimeoutReceipt.create(
            result_occurrence_id=result_id,
            lifecycle_projection_digest=projection.lifecycle_projection_digest,
            proof_requirement_id="requirement",
            execution_event_digest="timeout-event",
        ),)
    elif outcome is Outcome.ERROR:
        errors = (ErrorReceipt.create(
            result_occurrence_id=result_id,
            lifecycle_projection_digest=projection.lifecycle_projection_digest,
            error_kind="strategy_exception",
            error_artifact_digest="error-artifact",
        ),)
    receipt = finalize_decision(FinalizationAuthority(
        result_id, projection, decisive, timeout, errors,
    ))
    assert receipt.outcome is outcome
    return receipt


@pytest.mark.parametrize("outcome", tuple(Outcome))
def test_decision_receipt_is_only_serialized_status_authority(outcome):
    result = EquivalenceResult(
        is_equivalent=None,
        function1_name="left",
        function2_name="right",
        binary1_name="left.o",
        binary2_name="right.o",
        solver_results=ParallelResult(results=[]),
    )
    attach_canonical_decision(result, _receipt(outcome))
    payload = result.to_dict()

    assert outcome_from_payload(payload) is outcome
    expected = "EQ" if outcome is Outcome.EQUIVALENT else outcome.value
    assert classify_result_payload(payload) == expected
    assert ("Result: " + (
        "NOT EQUIVALENT" if outcome is Outcome.NOT_EQ else outcome.value
    )) in result.to_string()


def test_serialized_legacy_contradiction_is_rejected():
    result = EquivalenceResult(
        is_equivalent=None,
        function1_name="left", function2_name="right",
        binary1_name="left.o", binary2_name="right.o",
        solver_results=ParallelResult(results=[]),
    )
    attach_canonical_decision(result, _receipt(Outcome.TIMEOUT))
    payload = result.to_dict()
    payload["is_equivalent"] = True
    with pytest.raises(ValueError, match="compatibility projection"):
        classify_result_payload(payload)
    payload = result.to_dict()
    payload["decision_receipt"]["receipt_digest"] = "forged"
    with pytest.raises(ValueError, match="receipt digest"):
        classify_result_payload(payload)


def test_all_five_outcomes_have_explicit_retry_batch_and_cli_policy():
    assert set(RETRY_FALLBACK_MATRIX) == set(Outcome)
    assert set(BATCH_RESUME_MATRIX) == set(Outcome)
    assert set(CLI_EXIT_MATRIX) == set(Outcome)
    assert len(set(CLI_EXIT_MATRIX.values())) == len(Outcome)
    assert BATCH_RESUME_MATRIX[Outcome.UNKNOWN] != BATCH_RESUME_MATRIX[Outcome.TIMEOUT]
    assert RETRY_FALLBACK_MATRIX[Outcome.UNKNOWN] != RETRY_FALLBACK_MATRIX[Outcome.TIMEOUT]


@pytest.mark.parametrize("outcome", tuple(Outcome))
def test_stage_fallback_consumes_the_all_five_policy(outcome):
    from scripts.function_tracer_pcode.equivalence.obligations.stage_runner import (
        _cutover_branch_policy,
    )

    result = SimpleNamespace(
        is_equivalent={
            Outcome.EQUIVALENT: True,
            Outcome.NOT_EQ: False,
        }.get(outcome),
        error_message="boom" if outcome is Outcome.ERROR else None,
        failure_status="strategy_exception" if outcome is Outcome.ERROR else None,
        is_timeout=lambda: outcome is Outcome.TIMEOUT,
    )
    observed, actions, continues = _cutover_branch_policy(result)

    assert observed is outcome
    assert actions == RETRY_FALLBACK_MATRIX[outcome]
    assert continues is ("FALLBACK_NEXT_STRATEGY" in actions)
    if outcome is Outcome.ERROR:
        assert continues is False


def test_cli_startup_error_emits_canonical_error_and_exit_four(monkeypatch, capsys):
    from scripts.function_tracer_pcode.cli.commands import equivalence as cli

    monkeypatch.setattr(cli, "apply_runtime_environment", lambda: SimpleNamespace())
    monkeypatch.setattr(
        cli, "load_pyghidra", lambda: (_ for _ in ()).throw(RuntimeError("startup"))
    )
    args = SimpleNamespace(
        equiv=("left.o", "right.o"), binary_ids=None, output=None,
        quiet=False, verbose=False, debug=False,
    )

    with pytest.raises(SystemExit) as stopped:
        cli.run_equivalence_check(args)

    assert stopped.value.code == CLI_EXIT_MATRIX[Outcome.ERROR] == 4
    text = capsys.readouterr().out
    assert classify_canonical_log_text(text, matrix_context=True) == "ERROR"


def test_cli_no_solver_emits_canonical_error_and_exit_four(monkeypatch, capsys):
    from scripts.function_tracer_pcode.cli.commands import equivalence as cli
    import scripts.function_tracer_pcode.equivalence as equivalence_package
    import scripts.function_tracer_pcode.equivalence.source_declarations as declarations

    class FakeChecker:
        def __init__(self, **_kwargs):
            self.solver_runner = SimpleNamespace(get_available_solvers=lambda: [])

    monkeypatch.setattr(cli, "apply_runtime_environment", lambda: SimpleNamespace(
        ghidra_install_dir=None
    ))
    monkeypatch.setattr(cli, "load_pyghidra", lambda: object())
    monkeypatch.setattr(cli, "start_headless_pyghidra", lambda *_args, **_kwargs: None)
    monkeypatch.setattr(cli, "get_target_functions", lambda _args: ["f"])
    monkeypatch.setattr(equivalence_package, "EquivalenceChecker", FakeChecker)
    monkeypatch.setattr(declarations, "infer_adjacent_c_return_type", lambda *_args: None)
    args = SimpleNamespace(
        equiv=("left.o", "right.o"), binary_ids=None, output=None,
        quiet=False, verbose=False, debug=False, equiv_timeout=1,
    )

    with pytest.raises(SystemExit) as stopped:
        cli.run_equivalence_check(args)

    assert stopped.value.code == CLI_EXIT_MATRIX[Outcome.ERROR] == 4
    assert classify_canonical_log_text(
        capsys.readouterr().out, matrix_context=True
    ) == "ERROR"


def test_cli_missing_function_emits_canonical_error_and_exit_four(monkeypatch, capsys):
    from scripts.function_tracer_pcode.cli.commands import equivalence as cli

    monkeypatch.setattr(cli, "apply_runtime_environment", lambda: SimpleNamespace(
        ghidra_install_dir=None
    ))
    monkeypatch.setattr(cli, "load_pyghidra", lambda: object())
    monkeypatch.setattr(cli, "start_headless_pyghidra", lambda *_args, **_kwargs: None)
    monkeypatch.setattr(cli, "get_target_functions", lambda _args: [])
    args = SimpleNamespace(
        equiv=("left.o", "right.o"), binary_ids=None, output=None,
        quiet=False, verbose=False, debug=False, equiv_timeout=1,
    )

    with pytest.raises(SystemExit) as stopped:
        cli.run_equivalence_check(args)

    assert stopped.value.code == CLI_EXIT_MATRIX[Outcome.ERROR] == 4
    assert classify_canonical_log_text(
        capsys.readouterr().out, matrix_context=True
    ) == "ERROR"


def test_timeout_requires_terminal_receipt_not_solver_row_heuristic():
    result = EquivalenceResult(
        is_equivalent=None,
        function1_name="left", function2_name="right",
        binary1_name="left.o", binary2_name="right.o",
        solver_results=SimpleNamespace(results=(SimpleNamespace(status="TIMEOUT"),)),
    )
    attach_canonical_decision(result, _receipt(Outcome.UNKNOWN))
    assert result.is_timeout() is False
    assert result.is_unknown() is True


def test_serialized_lifecycle_relations_remain_base_relations_without_outcome():
    result_id = "result-unknown"
    projection = _projection(result_id, active=True)
    result = EquivalenceResult(
        is_equivalent=None,
        function1_name="left", function2_name="right",
        binary1_name="left.o", binary2_name="right.o",
        solver_results=ParallelResult(results=[]),
    )
    attach_canonical_decision(result, _receipt(Outcome.UNKNOWN))
    attach_canonical_relations(result, projection)

    payload = result.to_dict()

    assert len(payload["c_active_base"]) == 1
    assert payload["q_open_base"] == []
    assert "final_outcome" not in payload["c_active_base"][0]


def test_canonical_matrix_parser_rejects_result_line_and_legacy_json():
    assert classify_canonical_log_text("Result: TIMEOUT\n", matrix_context=True) == (
        "INCOMPLETE"
    )
    legacy = "\n".join((
        "=== EQUIVALENCE_RESULT_JSON_BEGIN ===",
        '{"is_equivalent":null,"is_timeout":true}',
        "=== EQUIVALENCE_RESULT_JSON_END ===",
    ))
    assert classify_canonical_log_text(legacy, matrix_context=True) == "INCOMPLETE"


def test_canonical_summary_mode_never_uses_legacy_timeout_heuristics(tmp_path):
    log = tmp_path / "f_B1_B2.log"
    log.write_text("Result: TIMEOUT\nsolver status: TIMEOUT\n", encoding="utf-8")

    assert read_validation_log_record(log).status == "TIMEOUT"
    assert read_validation_log_record(log, canonical_only=True).status == "INCOMPLETE"


def _json_result_log(payload):
    return "\n".join((
        "=== EQUIVALENCE_RESULT_JSON_BEGIN ===",
        json.dumps(payload, sort_keys=True),
        "=== EQUIVALENCE_RESULT_JSON_END ===",
    ))


def _write_signed_unknown_pair_status(log: Path) -> None:
    digest = "a" * 64
    private_key = log.parent / ".pair-status-test.key"
    public_key = log.parent / PAIR_STATUS_PUBLIC_KEY_FILE
    generate_pair_status_keypair(private_key, public_key)
    body = {
        "authority_kind": "SupervisorCanonicalResultResolvedReceipt",
        "supervisor_authority_kind": "SupervisorCanonicalResultResolvedReceipt",
        "supervisor_final_authority_digest": digest,
        "launch_receipt_digest": digest,
        "canonical_outcome": "UNKNOWN",
        "decision_receipt_digest": digest,
        "result_occurrence_id": "result-occurrence",
        "result_entry_occurrence_receipt_digest": digest,
        "execution_identity_digest": digest,
        "execution_nonce": "execution-nonce",
        "stream_id": "stream-id",
        "source_snapshot_fingerprint": digest,
        "canonical_result_bundle_digest": digest,
        "canonical_result_bundle_kind": "CanonicalResultFinalizationBundle",
        "canonical_result_payload_preimage_digest": digest,
        "semantic_projection_digest": digest,
        "error_kind": None,
        "child_returncode": 2,
        "supervisor_status": "RESOLVED",
        "supervisor_projection_digest": digest,
        "classification_valid": True,
        "pair_execution_target": {
            "schema": "eqbench-pair-execution-target-v1",
            "authority_kind": "PairExecutionTargetReceipt",
            "sample_identity": "sample/Eq/newV",
            "output_sample_relative_path": "sample/Eq/newV",
            "function_name": "f", "left_binary_id": "B1",
            "right_binary_id": "B2", "source_path": "source.c",
            "source_sha256": digest, "left_binary_path": "left.bin",
            "left_binary_sha256": digest, "right_binary_path": "right.bin",
            "right_binary_sha256": digest, "analysis_source_digest": digest,
            "analysis_config_digest": digest,
        },
    }
    body["pair_execution_target"]["target_digest"] = authority_digest(
        body["pair_execution_target"]
    )
    sealed = seal_pair_status(
        body, private_key_path=private_key, public_key_path=public_key
    )
    log.with_suffix(".pair-status.json").write_text(
        json.dumps(sealed), encoding="utf-8"
    )


def test_pair_status_resume_policy_keeps_unknown_and_timeout_resumable():
    from scripts.function_tracer_pcode.equivalence.v2.pair_status_authority import (
        pair_status_resume_disposition,
    )
    from scripts.function_tracer_pcode.equivalence.v2.phase8_cutover import (
        CLI_EXIT_MATRIX,
    )
    from scripts.function_tracer_pcode.equivalence.v2.contracts import (
        CLI_EXIT_CODE_BY_OUTCOME,
    )

    assert CLI_EXIT_MATRIX is CLI_EXIT_CODE_BY_OUTCOME
    assert pair_status_resume_disposition.__name__ == "pair_status_resume_disposition"
    assert BATCH_RESUME_MATRIX[Outcome.UNKNOWN].startswith("RESUMABLE_")
    assert BATCH_RESUME_MATRIX[Outcome.TIMEOUT].startswith("RESUMABLE_")
    assert BATCH_RESUME_MATRIX[Outcome.EQUIVALENT].startswith("COMPLETE_")


def test_canonical_summary_drops_receiptless_unknown_payload_metrics(tmp_path):
    log = tmp_path / "f_B1_B2.log"
    log.write_text(_json_result_log({
        "is_equivalent": None,
        "unknown_reasons": [{"reason_id": "legacy_contamination"}],
    }), encoding="utf-8")

    summary = aggregate_validation_logs_by_function((log,), canonical_only=True)
    health = build_run_health_summary(summary)

    assert summary.overall.records[0].payloads == ()
    assert health["unknown_results"] == 0
    assert health["unknown_by_reason"] == {}


def test_canonical_summary_keeps_only_final_receipt_bound_payload(tmp_path):
    result = EquivalenceResult(
        is_equivalent=None,
        function1_name="f", function2_name="f",
        binary1_name="left.o", binary2_name="right.o",
        solver_results=ParallelResult(results=[]),
    )
    attach_canonical_decision(result, _receipt(Outcome.UNKNOWN))
    canonical = result.to_dict()
    legacy = {
        "is_equivalent": None,
        "unknown_reasons": [{"reason_id": "legacy_contamination"}],
    }
    log = tmp_path / "f_B1_B2.log"
    log.write_text(
        _json_result_log(legacy) + "\n" + _json_result_log(canonical),
        encoding="utf-8",
    )
    _write_signed_unknown_pair_status(log)

    summary = aggregate_validation_logs_by_function((log,), canonical_only=True)
    health = build_run_health_summary(summary)

    assert summary.overall.records[0].payloads == (canonical,)
    assert "legacy_contamination" not in health["unknown_by_reason"]


def test_process_timeout_is_rematerialized_from_durable_terminal_bundle(tmp_path):
    root = Path(__file__).resolve().parents[4]
    payload = json.loads((root / (
        "artifacts/unknown_taxonomy_v2/phase7/real-process-timeout.json"
    )).read_text(encoding="utf-8"))
    durable = payload["durable_store"]
    store_root = tmp_path / "store"
    directory = store_root / durable["execution_nonce"]
    directory.mkdir(parents=True)
    for name, content in durable["files"].items():
        (directory / name).write_text(content, encoding="utf-8")
    supervisor_key = tmp_path / "supervisor.key"
    worker_key = tmp_path / "worker.key"
    supervisor_key.write_bytes(bytes.fromhex(durable["supervisor_signing_key_hex"]))
    worker_key.write_bytes(bytes.fromhex(durable["worker_signing_key_hex"]))

    receipt = rematerialize_process_timeout_decision(
        checkpoint_root=store_root,
        execution_nonce=durable["execution_nonce"],
        supervisor_signing_key_id=durable["supervisor_signing_key_id"],
        supervisor_signing_key_file=supervisor_key,
        worker_signing_key_id=durable["worker_signing_key_id"],
        worker_signing_key_file=worker_key,
    )

    assert receipt.outcome is Outcome.TIMEOUT
    assert receipt.receipt_digest == payload["decision_receipt"]["receipt_digest"]


def test_eq_cutover_is_bound_to_audited_comparison_receipt_signal(
    tmp_path, monkeypatch,
):
    from scripts.function_tracer_pcode.equivalence.v2.pilot import (
        ProductionDualWritePilotConnector,
    )
    from scripts.function_tracer_pcode.equivalence.v2.process_supervisor import (
        PROCESS_DURABLE_REASON_REGISTRY,
        PROCESS_DURABLE_RECOVERY_REGISTRY,
    )
    from scripts.function_tracer_pcode.equivalence.v2.production_signals import (
        CompositeProductionSignalEncoder,
        PendingEqClosureAuthority,
        SatSafetyBlockerProductionSignal,
        issue_pending_eq_closure_authority,
        production_signal_scope,
    )
    from scripts.function_tracer_pcode.equivalence.v2.reducer import (
        ShadowLifecycleReducer,
    )
    from scripts.function_tracer_pcode.equivalence.v2.sat_safety import (
        SatSafetyPilotEncoder,
    )
    from scripts.function_tracer_pcode.equivalence.v2.execution_authority import (
        PINNED_SOLVER_EXECUTION_ISSUER,
    )
    occurrence_nonce = "phase8-eq-closure-occurrence"
    monkeypatch.setenv(
        "UNKNOWN_TAXONOMY_V2_RESULT_ENTRY_OCCURRENCE_NONCE",
        occurrence_nonce,
    )
    connector = ProductionDualWritePilotConnector(
        ShadowLifecycleReducer(
            reason_registry=PROCESS_DURABLE_REASON_REGISTRY,
            recovery_registry=PROCESS_DURABLE_RECOVERY_REGISTRY,
        ),
        domain_signal_encoder=CompositeProductionSignalEncoder({
            SatSafetyBlockerProductionSignal: SatSafetyPilotEncoder(),
        }),
    )
    session = connector.begin({"case": "phase8-eq-closure"})
    from scripts.function_tracer_pcode.equivalence.checker import EquivalenceChecker
    from scripts.function_tracer_pcode.tests.unit.test_monolithic_region_split import (
        _analysis,
    )

    with production_signal_scope(session):
        trusted_result = EquivalenceChecker(
            strategy="monolithic", timeout=5, monolithic_timeout=5,
            enable_rewrite=False, canonical_decision_cutover=False,
        ).check(_analysis("left", 7), _analysis("right", 7))
    frame = trusted_result._prepared_dispatch_frame
    receipt = frame.receipt
    assert receipt is not None and receipt.is_trusted_for(frame)
    with pytest.raises(ValueError, match="not the dispatch-frame receipt"):
        issue_pending_eq_closure_authority(session, copy(receipt), frame)
    forged_receipt = copy(receipt)
    frame.receipt = forged_receipt
    with pytest.raises(ValueError, match="not trusted"):
        issue_pending_eq_closure_authority(session, forged_receipt, frame)
    frame.receipt = receipt
    with pytest.raises(ValueError, match="not trusted"):
        issue_pending_eq_closure_authority(session, receipt, copy(frame))
    foreign_session = connector.begin({"case": "phase8-eq-closure-foreign"})
    with pytest.raises(ValueError, match="another production session"):
        issue_pending_eq_closure_authority(foreign_session, receipt, frame)
    with pytest.raises(TypeError, match="verifier-owned issuer"):
        PendingEqClosureAuthority(_token=object())
    pending = issue_pending_eq_closure_authority(session, receipt, frame)
    assert pending.comparison_receipt_id == receipt.receipt_id
    occurrence_payload = dict(session.execution_payload)
    assert occurrence_payload.pop("result_entry_occurrence_nonce") == occurrence_nonce
    session.result_entry_occurrence_receipt = (
        PINNED_SOLVER_EXECUTION_ISSUER.issue_result_entry_occurrence(
            result_occurrence_id=session.identity.result_occurrence_id,
            execution_payload_digest=authority_digest(occurrence_payload),
            startup_receipt_digests=(receipt.receipt_id,),
            occurrence_nonce=occurrence_nonce,
        )
    )
    result = SimpleNamespace(
        is_equivalent=True,
        error_message=None,
        failure_status=None,
        failure_message=None,
        unknown_reasons=[],
        unknown_recovery_actions=[],
        is_timeout=lambda: False,
    )

    evidence = connector.finish(session, result, case_id="phase8-eq-closure")

    assert evidence.pilot_result.candidate.decision_receipt.outcome is Outcome.EQUIVALENT
    assert session.phase7_runtime_result is None

    from scripts.function_tracer_pcode.equivalence.v2.canonical_result import (
        RESULT_ENVELOPE_FILE,
        _semantic_projection,
        build_canonical_result_finalization_bundle,
        persist_canonical_result_envelope,
        validate_canonical_result_finalization_bundle,
    )

    preimage = {"final_outcome": "EQUIVALENT", "total_time": 0.0}
    bundle_key = tmp_path / "canonical-bundle.key"
    bundle_key.write_bytes(b"k" * 32)
    monkeypatch.setenv(
        "UNKNOWN_TAXONOMY_V2_SUPERVISOR_KEY_ID", "phase10-test-key"
    )
    monkeypatch.setenv(
        "UNKNOWN_TAXONOMY_V2_SUPERVISOR_KEY_FILE", str(bundle_key)
    )
    bundle = build_canonical_result_finalization_bundle(
        result_payload_preimage=preimage,
        evidence=evidence,
        session=session,
    )
    assert validate_canonical_result_finalization_bundle(
        bundle,
        bundle_verification_key_id="phase10-test-key",
        bundle_verification_key=b"k" * 32,
    )["outcome"] == "EQUIVALENT"
    forged_signature = deepcopy(bundle)
    forged_signature["bundle_signature"] = "0" * 64
    with pytest.raises(ValueError, match="signature is invalid"):
        validate_canonical_result_finalization_bundle(
            forged_signature,
            bundle_verification_key_id="phase10-test-key",
            bundle_verification_key=b"k" * 32,
        )
    semantic_a = _semantic_projection(
        preimage, evidence.pilot_result,
        (("binary1_id", "B1"), ("result_entry_occurrence_nonce", "a")),
    )
    semantic_b = _semantic_projection(
        preimage, evidence.pilot_result,
        (("binary1_id", "B1"), ("result_entry_occurrence_nonce", "b")),
    )
    assert semantic_a == semantic_b
    payload = {**preimage, "canonical_result_finalization_bundle": bundle}
    monkeypatch.setenv("UNKNOWN_TAXONOMY_V2_SUPERVISOR_ROOT", str(tmp_path))
    monkeypatch.setenv("UNKNOWN_TAXONOMY_V2_EXECUTION_NONCE", "eq-bundle")
    path = persist_canonical_result_envelope(payload)
    assert path == tmp_path / "eq-bundle" / RESULT_ENVELOPE_FILE
    envelope = json.loads(path.read_text(encoding="utf-8"))
    persisted = envelope["canonical_result_payload"]
    persisted_bundle = persisted["canonical_result_finalization_bundle"]
    assert persisted == json.loads(json.dumps(payload, sort_keys=True))
    assert validate_canonical_result_finalization_bundle(
        persisted_bundle,
        result_payload_preimage={
            key: value for key, value in persisted.items()
            if key != "canonical_result_finalization_bundle"
        },
    )["outcome"] == "EQUIVALENT"

    forged = deepcopy(persisted_bundle)
    forged["terminalizations"] = [{
        "event_sequence_number": 1,
        "proof_requirement_id": "foreign-timeout",
    }]
    forged_body = {
        key: value for key, value in forged.items()
        if key not in {"bundle_digest", "bundle_signature"}
    }
    forged["bundle_digest"] = authority_digest(forged_body)
    with pytest.raises(ValueError, match="terminalization"):
        validate_canonical_result_finalization_bundle(
            forged, result_payload_preimage=preimage
        )

    forged = deepcopy(persisted_bundle)
    forged["canonical_semantic_result_projection"]["payload"][
        "binary1_content_identity"
    ] = "foreign-binary"
    forged["canonical_semantic_result_projection"][
        "semantic_projection_digest"
    ] = authority_digest(
        forged["canonical_semantic_result_projection"]["payload"]
    )
    forged_body = {
        key: value for key, value in forged.items()
        if key not in {"bundle_digest", "bundle_signature"}
    }
    forged["bundle_digest"] = authority_digest(forged_body)
    with pytest.raises(ValueError, match="semantic result projection"):
        validate_canonical_result_finalization_bundle(
            forged, result_payload_preimage=preimage
        )


def test_pending_eq_revalidates_from_immutable_post_cleanup_receipt_only():
    from scripts.function_tracer_pcode.equivalence.v2.pilot import (
        ProductionDualWritePilotConnector,
    )
    from scripts.function_tracer_pcode.equivalence.v2.process_supervisor import (
        PROCESS_DURABLE_REASON_REGISTRY,
        PROCESS_DURABLE_RECOVERY_REGISTRY,
    )
    from scripts.function_tracer_pcode.equivalence.v2.production_signals import (
        issue_pending_eq_closure_authority,
        production_signal_scope,
    )
    from scripts.function_tracer_pcode.equivalence.v2.reducer import (
        ShadowLifecycleReducer,
    )
    from scripts.function_tracer_pcode.equivalence.checker import EquivalenceChecker
    from scripts.function_tracer_pcode.tests.unit.test_monolithic_region_split import (
        _analysis,
    )

    connector = ProductionDualWritePilotConnector(ShadowLifecycleReducer(
        reason_registry=PROCESS_DURABLE_REASON_REGISTRY,
        recovery_registry=PROCESS_DURABLE_RECOVERY_REGISTRY,
    ))
    session = connector.begin({"case": "phase10-stale-pending-eq"})
    with production_signal_scope(session):
        trusted_result = EquivalenceChecker(
            strategy="monolithic", timeout=5, monolithic_timeout=5,
            enable_rewrite=False, canonical_decision_cutover=False,
        ).check(_analysis("left", 7), _analysis("right", 7))
    frame = trusted_result._prepared_dispatch_frame
    issue_pending_eq_closure_authority(session, frame.receipt, frame)
    frame.cleanup_complete = False
    result = SimpleNamespace(
        is_equivalent=True, error_message=None, failure_status=None,
        failure_message=None, unknown_reasons=[], unknown_recovery_actions=[],
        is_timeout=lambda: False,
    )
    evidence = connector.finish(
        session, result, case_id="phase10-stale-pending-eq"
    )
    assert evidence.pilot_result.candidate.decision_receipt.outcome is Outcome.EQUIVALENT


def test_canonical_bundle_rejects_foreign_result_entry_occurrence(
    tmp_path, monkeypatch,
):
    import hashlib
    import hmac

    from scripts.function_tracer_pcode.equivalence.v2.canonical_result import (
        build_canonical_result_finalization_bundle,
        validate_canonical_result_finalization_bundle,
    )
    from scripts.function_tracer_pcode.equivalence.v2.execution_authority import (
        PINNED_SOLVER_EXECUTION_ISSUER,
    )
    from scripts.function_tracer_pcode.equivalence.v2.pilot import (
        ProductionDualWritePilotConnector,
    )
    from scripts.function_tracer_pcode.equivalence.v2.process_supervisor import (
        PROCESS_DURABLE_REASON_REGISTRY,
        PROCESS_DURABLE_RECOVERY_REGISTRY,
    )
    from scripts.function_tracer_pcode.equivalence.v2.reducer import (
        ShadowLifecycleReducer,
    )
    from scripts.function_tracer_pcode.equivalence.v2.stream import (
        DecisiveProofEventAuthority, EventIntent, EventType,
    )

    nonce = "canonical-occurrence-nonce"
    monkeypatch.setenv(
        "UNKNOWN_TAXONOMY_V2_RESULT_ENTRY_OCCURRENCE_NONCE", nonce
    )
    connector = ProductionDualWritePilotConnector(ShadowLifecycleReducer(
        reason_registry=PROCESS_DURABLE_REASON_REGISTRY,
        recovery_registry=PROCESS_DURABLE_RECOVERY_REGISTRY,
    ))
    execution_payload = {"case": "canonical-occurrence-join"}
    session = connector.begin(execution_payload)
    receipt = PINNED_SOLVER_EXECUTION_ISSUER.issue_result_entry_occurrence(
        result_occurrence_id=session.identity.result_occurrence_id,
        execution_payload_digest=authority_digest(execution_payload),
        startup_receipt_digests=("startup-receipt",),
        occurrence_nonce=nonce,
    )
    session.result_entry_occurrence_receipt = receipt
    session.emit(EventIntent(
        EventType.EQ_CLOSURE, DecisiveProofEventAuthority("eq-proof")
    ))
    result = SimpleNamespace(
        is_equivalent=True, error_message=None, failure_status=None,
        failure_message=None, unknown_reasons=[], unknown_recovery_actions=[],
        is_timeout=lambda: False,
    )
    evidence = connector.finish(
        session, result, case_id="canonical-occurrence-join"
    )
    key = b"o" * 32
    key_file = tmp_path / "occurrence.key"
    key_file.write_bytes(key)
    monkeypatch.setenv("UNKNOWN_TAXONOMY_V2_SUPERVISOR_KEY_ID", "occurrence-key")
    monkeypatch.setenv(
        "UNKNOWN_TAXONOMY_V2_SUPERVISOR_KEY_FILE", str(key_file)
    )
    bundle = build_canonical_result_finalization_bundle(
        result_payload_preimage={"final_outcome": "EQUIVALENT"},
        evidence=evidence,
        session=session,
    )
    foreign = PINNED_SOLVER_EXECUTION_ISSUER.issue_result_entry_occurrence(
        result_occurrence_id="foreign-result-occurrence",
        execution_payload_digest=authority_digest(execution_payload),
        startup_receipt_digests=("startup-receipt",),
        occurrence_nonce=nonce,
    )
    forged = deepcopy(bundle)
    forged["result_entry_occurrence_receipt"] = foreign.to_authority_dict()
    body = {
        name: value for name, value in forged.items()
        if name not in {"bundle_digest", "bundle_signature"}
    }
    forged["bundle_digest"] = authority_digest(body)
    forged["bundle_signature"] = hmac.new(
        key, forged["bundle_digest"].encode("ascii"), hashlib.sha256
    ).hexdigest()
    with pytest.raises(ValueError, match="result-entry occurrence"):
        validate_canonical_result_finalization_bundle(
            forged,
            result_payload_preimage={"final_outcome": "EQUIVALENT"},
            bundle_verification_key_id="occurrence-key",
            bundle_verification_key=key,
        )


def test_signed_early_error_bundle_requires_typed_result_entry_occurrence(
    tmp_path, monkeypatch,
):
    import hashlib
    import hmac

    from scripts.function_tracer_pcode.equivalence.v2.canonical_result import (
        attach_durable_error_finalization,
        build_canonical_result_finalization_bundle,
        validate_canonical_result_finalization_bundle,
    )

    key = b"e" * 32
    key_file = tmp_path / "early-error.key"
    key_file.write_bytes(key)
    monkeypatch.setenv(
        "UNKNOWN_TAXONOMY_V2_SUPERVISOR_KEY_ID", "early-error-key"
    )
    monkeypatch.setenv(
        "UNKNOWN_TAXONOMY_V2_SUPERVISOR_KEY_FILE", str(key_file)
    )
    result = SimpleNamespace(
        is_equivalent=None, error_message="early failure",
        failure_status="ERROR", failure_message="early failure",
        unknown_reasons=[], unknown_recovery_actions=[],
        is_timeout=lambda: False,
    )
    attach_durable_error_finalization(
        result,
        execution_payload={"case": "signed-early-error"},
        error_kind="operational_authority_invalid",
        error_artifact_digest="early-error-artifact",
    )
    evidence, session = result._canonical_finalization_context
    bundle = build_canonical_result_finalization_bundle(
        result_payload_preimage={"final_outcome": "ERROR"},
        evidence=evidence, session=session,
    )
    occurrence = bundle["result_entry_occurrence_receipt"]
    assert occurrence["authority_kind"] == (
        "EarlyErrorResultEntryOccurrenceReceipt"
    )
    forged = deepcopy(bundle)
    forged["result_entry_occurrence_receipt"] = None
    body = {
        name: value for name, value in forged.items()
        if name not in {"bundle_digest", "bundle_signature"}
    }
    forged["bundle_digest"] = authority_digest(body)
    forged["bundle_signature"] = hmac.new(
        key, forged["bundle_digest"].encode("ascii"), hashlib.sha256
    ).hexdigest()
    with pytest.raises(ValueError, match="lacks entry occurrence authority"):
        validate_canonical_result_finalization_bundle(
            forged,
            result_payload_preimage={"final_outcome": "ERROR"},
            bundle_verification_key_id="early-error-key",
            bundle_verification_key=key,
        )
