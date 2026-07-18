from types import SimpleNamespace
from copy import copy
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


def test_eq_cutover_is_bound_to_audited_comparison_receipt_signal():
    from scripts.function_tracer_pcode.equivalence.v2.phase7_runtime import (
        runtime_from_audited_manifest,
    )
    from scripts.function_tracer_pcode.equivalence.v2.pilot import (
        ProductionDualWritePilotConnector,
    )
    from scripts.function_tracer_pcode.equivalence.v2.process_supervisor import (
        PROCESS_DURABLE_REASON_REGISTRY,
        PROCESS_DURABLE_RECOVERY_REGISTRY,
    )
    from scripts.function_tracer_pcode.equivalence.v2.production_signals import (
        CompositeProductionSignalEncoder,
        EqClosureProductionSignal,
        emit_sat_safety_signal,
        issue_eq_closure_signal,
        production_signal_scope,
    )
    from scripts.function_tracer_pcode.equivalence.v2.reducer import (
        ShadowLifecycleReducer,
    )
    from scripts.function_tracer_pcode.equivalence.v2.sat_safety import (
        SatSafetyPilotEncoder,
    )
    from scripts.function_tracer_pcode.validation.phase7_producer_manifest import (
        build_phase7_producer_manifest,
    )

    root = Path(__file__).resolve().parents[4]
    manifest = build_phase7_producer_manifest(root)
    connector = ProductionDualWritePilotConnector(
        ShadowLifecycleReducer(
            reason_registry=PROCESS_DURABLE_REASON_REGISTRY,
            recovery_registry=PROCESS_DURABLE_RECOVERY_REGISTRY,
        ),
        domain_signal_encoder=CompositeProductionSignalEncoder({
            EqClosureProductionSignal: SatSafetyPilotEncoder(),
        }),
        phase7_runtime_factory=lambda identity: runtime_from_audited_manifest(
            manifest, identity
        ),
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
        issue_eq_closure_signal(session, copy(receipt), frame)
    forged_receipt = copy(receipt)
    frame.receipt = forged_receipt
    with pytest.raises(TypeError, match="issuer-owned"):
        issue_eq_closure_signal(session, forged_receipt, frame)
    frame.receipt = receipt
    with pytest.raises(TypeError, match="issuer-owned"):
        issue_eq_closure_signal(session, receipt, copy(frame))
    foreign_session = connector.begin({"case": "phase8-eq-closure-foreign"})
    with pytest.raises(ValueError, match="different production session"):
        issue_eq_closure_signal(foreign_session, receipt, frame)
    with pytest.raises(TypeError, match="verifier-owned issuer"):
        EqClosureProductionSignal(
            "comparison-digest", "comparison-receipt",
            _token=object(),
        )
    signal = issue_eq_closure_signal(session, receipt, frame)
    forged_copy = object.__new__(EqClosureProductionSignal)
    for name in ("proof_artifact_digest", "comparison_receipt_id", "producer_id"):
        object.__setattr__(forged_copy, name, getattr(signal, name))
    with pytest.raises(ValueError, match="copied, forged"):
        SatSafetyPilotEncoder()(session, forged_copy)
    # The comparison receipt was issued while this exact production session was
    # active.  Only the verifier-issued exact signal may cross the encoder.
    with production_signal_scope(session):
        emit_sat_safety_signal(
            signal,
            producer_site_manifest_id="obligation-stage-final-eq-closure",
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
    assert session.phase7_runtime_result.expected_activation_count == 1
    assert session.phase7_runtime_result.runtime_activation_count == 1
