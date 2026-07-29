import os
from pathlib import Path

import pytest

from scripts.function_tracer_pcode.analysis.decompilation_broker import (
    TOP_LEVEL_SOURCE_CONTRACT,
    decompile_function,
)
from scripts.function_tracer_pcode.equivalence.v2.contracts import authority_digest
from scripts.function_tracer_pcode.equivalence.v2.operational_extraction import (
    OPERATIONAL_REASON_REGISTRY,
    OPERATIONAL_RECOVERY_REGISTRY,
    OperationalBlockerSignal,
    OperationalCompletionSignal,
    OperationalExtractionPilotEncoder,
)
from scripts.function_tracer_pcode.equivalence.v2.pilot import (
    ProductionDualWritePilotSession,
    ProductionPilotExecutionIdentity,
)
from scripts.function_tracer_pcode.equivalence.v2.process_supervisor import (
    CheckpointState,
    DurableCheckpointStore,
    ProcessSupervisorAuthorityFactory,
)
from scripts.function_tracer_pcode.equivalence.v2.process_census import (
    ProcessAttemptCensusFactory,
    consume_durable_supervisor_projection,
)
from scripts.function_tracer_pcode.equivalence.v2.process_supervisor_command import (
    CHILD_ENV_LAUNCH,
    CHILD_ENV_NONCE,
    CHILD_ENV_ROOT,
    CHILD_ENV_SUPERVISOR_KEY_FILE,
    CHILD_ENV_SUPERVISOR_KEY_ID,
    CHILD_ENV_WORKER_KEY_FILE,
    CHILD_ENV_WORKER_KEY_ID,
    COMMAND_SCHEMA,
    read_process_start_token,
)
from scripts.function_tracer_pcode.equivalence.v2.process_worker_runtime import (
    CanonicalCensusInvalid,
    ProcessWorkerRuntime,
    require_canonical_supervisor_projection,
)
from scripts.function_tracer_pcode.equivalence.v2.production_signals import (
    CompositeProductionSignalEncoder,
    production_signal_scope,
)
from scripts.function_tracer_pcode.equivalence.v2.reducer import (
    ShadowLifecycleReducer,
)
from scripts.function_tracer_pcode.tests.unit.test_unknown_taxonomy_v2_phase6_operational_extraction import (
    BrokerAnalyzer,
    BrokerDecompiler,
    Function,
    Program,
    Result,
)


def _runtime_case(tmp_path, *, result, case):
    manager = type("Manager", (), {
        "getFunctions": lambda self, forward: iter(())
    })()
    program = Program(manager)
    function = Function(program=program)
    result.function = function
    encoder = OperationalExtractionPilotEncoder()
    session = ProductionDualWritePilotSession(
        ProductionPilotExecutionIdentity.create({"case": case}),
        ShadowLifecycleReducer(
            reason_registry=OPERATIONAL_REASON_REGISTRY,
            recovery_registry=OPERATIONAL_RECOVERY_REGISTRY,
        ),
        CompositeProductionSignalEncoder({
            OperationalBlockerSignal: encoder,
            OperationalCompletionSignal: encoder,
        }),
    )
    session.domain_signal_state["operational_program_binary_identities"] = {
        id(program): "sha256:binary",
    }
    process_factory = ProcessSupervisorAuthorityFactory(
        supervisor_signing_key_id="supervisor-key-v1",
        supervisor_signing_key=b"s" * 32,
        worker_signing_key_id="worker-key-v1",
        worker_signing_key=b"w" * 32,
    )
    launch = process_factory.issue_launch(
        result_occurrence_id=session.identity.result_occurrence_id,
        manifest_entry_preimage_digest="manifest-preimage",
        execution_nonce="execution-nonce-1",
        child_pid=os.getpid(), child_start_token="test-start-token",
        stream_id=f"stream-{session.identity.result_occurrence_id}",
        source_snapshot_fingerprint=session.identity.source_snapshot_fingerprint,
        deadline_policy_digest="deadline-policy-digest",
    )
    store = DurableCheckpointStore(
        tmp_path, process_factory, "execution-nonce-1"
    )
    store.persist_launch(launch)
    runtime = ProcessWorkerRuntime.for_testing(
        process_factory=process_factory, store=store, launch=launch,
        worker_start_token="test-start-token",
    )
    session.domain_signal_state[
        "unknown_taxonomy_v2_process_worker_runtime"
    ] = runtime
    analyzer = BrokerAnalyzer(program, BrokerDecompiler(result))
    return session, store, analyzer, function


@pytest.mark.parametrize(
    "kwargs,expected_kind",
    (
        ({"completed": True}, "COMPLETED"),
        ({"timed_out": True}, "TIMED_OUT_ATTEMPT"),
        ({"failed": True}, "ERROR"),
    ),
)
def test_broker_worker_runtime_persists_active_then_resolves(
    tmp_path, kwargs, expected_kind,
):
    session, store, analyzer, function = _runtime_case(
        tmp_path, result=Result(**kwargs), case=expected_kind,
    )
    with production_signal_scope(session):
        observed = decompile_function(
            analyzer, function, 60, None,
            source_contract_id=TOP_LEVEL_SOURCE_CONTRACT,
        )
    assert observed is analyzer.decompiler.result or observed._raw_result is (
        analyzer.decompiler.result
    )
    assert analyzer.decompiler.calls == 1
    assert store.read_state().payload["state"] == CheckpointState.RESOLVED.value
    continuation = process_factory_receipt(store, "continuation.json")
    assert continuation.payload["continuation_kind"] == expected_kind
    assert store.rematerialize_resolved_state(
        prefix=store.rematerialize_active_prefix()
    ).payload["state"] == CheckpointState.RESOLVED.value
    assert not (store.directory / "timeout.json").exists()
    projection = session.reducer.replay_prefix(session.recorder.prefix_view())
    if expected_kind == "COMPLETED":
        assert projection.q_open_base == ()
    elif expected_kind == "TIMED_OUT_ATTEMPT":
        assert len(projection.q_open_base) == 1
    active = session.domain_signal_state["process_worker_checkpoint_records"][0]
    census_factory = ProcessAttemptCensusFactory(
        session.identity.result_occurrence_id
    )
    membership = census_factory.register_operational(
        active.invocation, active.operational_factory,
        assignment=active.assignment,
        process_authority_factory=active.runtime.process_factory,
    )
    state = store.read_state()
    resolved_projection = _projection("RESOLVED", 0)
    resolved_projection["launch_receipt_digest"] = active.runtime.launch.receipt_digest
    resolved_projection["finalization_bundle_digest"] = state.receipt_digest
    body = dict(resolved_projection)
    body.pop("projection_digest")
    resolved_projection["projection_digest"] = authority_digest(body)
    foreign_assignment_census = ProcessAttemptCensusFactory(
        session.identity.result_occurrence_id
    )
    foreign_assignment_membership = foreign_assignment_census._register(
        active.invocation, active.operational_factory,
        assignment_receipt_digest="foreign-assignment-receipt",
        terminal_priority=active.assignment.payload["terminal_priority"],
        ownership_kind="OPERATIONAL",
    )
    with pytest.raises(ValueError, match="continuation differs from process membership"):
        consume_durable_supervisor_projection(
            resolved_projection, store=store,
            process_authority_factory=active.runtime.process_factory,
            census_factory=foreign_assignment_census,
            membership=foreign_assignment_membership,
        )
    consumed = consume_durable_supervisor_projection(
        resolved_projection, store=store,
        process_authority_factory=active.runtime.process_factory,
        census_factory=census_factory, membership=membership,
    )
    assert consumed.status == "RESOLVED"
    assert consumed.continuation_kind == expected_kind
    census = census_factory.seal()
    assert census.entries[0].disposition == {
        "COMPLETED": "COMPLETED",
        "TIMED_OUT_ATTEMPT": "TIMED_OUT",
        "ERROR": "ERROR",
    }[expected_kind]


def test_worker_runtime_chains_sequential_decompile_checkpoints(tmp_path):
    session, store, analyzer, function = _runtime_case(
        tmp_path, result=Result(timed_out=True), case="sequential-checkpoints",
    )
    with production_signal_scope(session):
        decompile_function(
            analyzer, function, 60, None,
            source_contract_id=TOP_LEVEL_SOURCE_CONTRACT,
        )
        first_resolved = store.read_state()
        completed = Result(completed=True)
        completed.function = function
        analyzer.decompiler.result = completed
        decompile_function(
            analyzer, function, 60, None,
            source_contract_id=TOP_LEVEL_SOURCE_CONTRACT,
        )
    second_resolved = store.read_state()
    assert session.domain_signal_error_details == []
    assert second_resolved.receipt_digest != first_resolved.receipt_digest
    checkpoint = process_factory_receipt(store, "checkpoint.json")
    assert checkpoint.payload["prior_resolved_receipt_digest"] == (
        first_resolved.receipt_digest
    )
    history = (
        store.directory / "checkpoint-history" / first_resolved.receipt_digest
    )
    assert (history / "checkpoint.json").is_file()
    assert (history / "state.json").is_file()


def test_worker_prepare_failure_does_not_commit_observation(
    tmp_path, monkeypatch,
):
    session, _store, analyzer, function = _runtime_case(
        tmp_path, result=Result(completed=True), case="prepare-failure",
    )
    runtime = session.domain_signal_state[
        "unknown_taxonomy_v2_process_worker_runtime"
    ]

    def reject_assignment(**_kwargs):
        raise ValueError("forced prospective assignment failure")

    monkeypatch.setattr(
        runtime.process_factory, "issue_live_assignment", reject_assignment,
    )

    with production_signal_scope(session):
        observed = decompile_function(
            analyzer, function, 60, None,
            source_contract_id=TOP_LEVEL_SOURCE_CONTRACT,
        )

    assert observed is analyzer.decompiler.result
    assert session.recorder.event_count == 0
    assert session.domain_signal_state.get(
        "process_worker_checkpoint_records", []
    ) == []
    assert any(
        "forced prospective assignment failure" in detail
        for detail in session.domain_signal_error_details
    )


def test_worker_persist_failure_rolls_back_observation_phase7_and_store(
    tmp_path, monkeypatch,
):
    from scripts.function_tracer_pcode.equivalence.v2.phase7_runtime import (
        runtime_from_audited_manifest,
    )
    from scripts.function_tracer_pcode.validation.phase7_producer_manifest import (
        build_phase7_producer_manifest,
    )

    session, store, analyzer, function = _runtime_case(
        tmp_path, result=Result(completed=True), case="persist-failure",
    )
    root = Path(__file__).resolve().parents[4]
    phase7 = runtime_from_audited_manifest(
        build_phase7_producer_manifest(root), session.identity
    )
    session.phase7_runtime = phase7
    persist_active = store.persist_active

    def persist_then_fail(receipt, prefix):
        persist_active(receipt, prefix)
        raise OSError("forced post-persist failure")

    monkeypatch.setattr(store, "persist_active", persist_then_fail)

    with production_signal_scope(session):
        observed = decompile_function(
            analyzer, function, 60, None,
            source_contract_id=TOP_LEVEL_SOURCE_CONTRACT,
        )

    assert observed is analyzer.decompiler.result
    assert session.recorder.event_count == 0
    assert session.domain_signal_state.get(
        "process_worker_checkpoint_records", []
    ) == []
    assert phase7._pending == {}
    assert phase7._materialized == []
    assert phase7._execution_intents == []
    assert phase7._signal_transactions == {}
    assert phase7._discovery_factory._issued == {}
    assert phase7._discovery_factory._ordinals == {}
    for filename in (
        "pending-active-transaction.json",
        "checkpoint-prefix-stream.json",
        "checkpoint.json",
        "state.json",
    ):
        assert not (store.directory / filename).exists()
    assert any(
        "forced post-persist failure" in detail
        for detail in session.domain_signal_error_details
    )


def test_worker_phase7_commit_failure_rolls_back_observation_and_checkpoint(
    tmp_path, monkeypatch,
):
    from scripts.function_tracer_pcode.equivalence.v2.phase7_runtime import (
        runtime_from_audited_manifest,
    )
    from scripts.function_tracer_pcode.validation.phase7_producer_manifest import (
        build_phase7_producer_manifest,
    )

    session, store, analyzer, function = _runtime_case(
        tmp_path, result=Result(completed=True), case="phase7-commit-failure",
    )
    root = Path(__file__).resolve().parents[4]
    phase7 = runtime_from_audited_manifest(
        build_phase7_producer_manifest(root), session.identity
    )
    session.phase7_runtime = phase7

    def reject_commit(_transaction):
        raise OSError("forced Phase 7 commit failure")

    monkeypatch.setattr(phase7, "commit_signal_transaction", reject_commit)

    with production_signal_scope(session):
        observed = decompile_function(
            analyzer, function, 60, None,
            source_contract_id=TOP_LEVEL_SOURCE_CONTRACT,
        )

    assert observed is analyzer.decompiler.result
    assert session.recorder.event_count == 0
    assert session.domain_signal_state.get(
        "process_worker_checkpoint_records", []
    ) == []
    assert phase7._pending == {}
    assert phase7._materialized == []
    assert phase7._execution_intents == []
    assert phase7._signal_transactions == {}
    assert phase7._discovery_factory._issued == {}
    assert phase7._discovery_factory._ordinals == {}
    for filename in (
        "pending-active-transaction.json",
        "checkpoint-prefix-stream.json",
        "checkpoint.json",
        "state.json",
    ):
        assert not (store.directory / filename).exists()
    assert any(
        "forced Phase 7 commit failure" in detail
        for detail in session.domain_signal_error_details
    )


def process_factory_receipt(store, filename):
    import json

    return store.factory.decode(json.loads(
        (store.directory / filename).read_text(encoding="utf-8")
    ))


def test_broker_worker_runtime_resolves_exact_raw_exception_and_reraises(tmp_path):
    error = RuntimeError("native decompiler failure")

    class RaisingDecompiler:
        calls = 0

        def decompileFunction(self, function, timeout, monitor):
            self.calls += 1
            raise error

    session, store, analyzer, function = _runtime_case(
        tmp_path, result=Result(), case="exception",
    )
    analyzer.decompiler = RaisingDecompiler()
    with production_signal_scope(session):
        with pytest.raises(RuntimeError) as captured:
            decompile_function(
                analyzer, function, 60, None,
                source_contract_id=TOP_LEVEL_SOURCE_CONTRACT,
            )
    assert captured.value is error
    assert analyzer.decompiler.calls == 1
    assert store.read_state().payload["state"] == CheckpointState.RESOLVED.value
    continuation = process_factory_receipt(store, "continuation.json")
    assert continuation.payload["continuation_kind"] == "ERROR"


def test_invalid_supervisor_projection_only_invalidates_canonical_census():
    body = {
        "status": "INVALID",
        "authority_kind": "InvalidSupervisorCommandProjection",
        "launch_receipt_digest": "launch-digest",
        "error_code": "DURABLE_RESTART_AUTHORITY_INVALID",
        "child_returncode": None,
        "projection_schema": COMMAND_SCHEMA,
    }
    payload = {**body, "projection_digest": authority_digest(body)}
    with pytest.raises(CanonicalCensusInvalid, match="canonical census INVALID"):
        require_canonical_supervisor_projection(payload)


def _projection(status, child_returncode):
    kinds = {
        "ERROR": "DurableErrorFinalizationBundle",
        "TIMEOUT": "DurableTimeoutFinalizationBundle",
        "RESOLVED": "CheckpointStateTransitionReceipt",
    }
    body = {
        "status": status,
        "authority_kind": kinds[status],
        "launch_receipt_digest": "launch-digest",
        "finalization_bundle_digest": "final-digest",
        "child_returncode": child_returncode,
        "projection_schema": COMMAND_SCHEMA,
    }
    if status in {"ERROR", "TIMEOUT"}:
        body["event_stream_authority_digest"] = "stream-digest"
    if status == "TIMEOUT":
        body["proof_requirement_id"] = "requirement-id"
    return {**body, "projection_digest": authority_digest(body)}


@pytest.mark.parametrize("status", ("ERROR", "TIMEOUT", "RESOLVED"))
@pytest.mark.parametrize("child_returncode", (None, 0, -15))
def test_canonical_supervisor_projection_accepts_exact_return_code(
    status, child_returncode,
):
    payload = _projection(status, child_returncode)
    assert require_canonical_supervisor_projection(payload) is payload


@pytest.mark.parametrize("value", (True, "0", [], {}))
def test_canonical_supervisor_projection_rejects_nonexact_return_code(value):
    with pytest.raises(CanonicalCensusInvalid, match="return code"):
        require_canonical_supervisor_projection(_projection("ERROR", value))


def test_worker_runtime_environment_is_complete_or_rejected(tmp_path, monkeypatch):
    keys = (
        CHILD_ENV_ROOT, CHILD_ENV_NONCE, CHILD_ENV_LAUNCH,
        CHILD_ENV_SUPERVISOR_KEY_ID, CHILD_ENV_SUPERVISOR_KEY_FILE,
        CHILD_ENV_WORKER_KEY_ID, CHILD_ENV_WORKER_KEY_FILE,
    )
    for key in keys:
        monkeypatch.delenv(key, raising=False)
    monkeypatch.setenv(CHILD_ENV_ROOT, str(tmp_path))
    with pytest.raises(ValueError, match="environment is partial"):
        ProcessWorkerRuntime.from_environment()
    monkeypatch.delenv(CHILD_ENV_ROOT)

    supervisor_key = tmp_path / "supervisor.key"
    worker_key = tmp_path / "worker.key"
    supervisor_key.write_bytes(b"s" * 32)
    worker_key.write_bytes(b"w" * 32)
    process_factory = ProcessSupervisorAuthorityFactory(
        supervisor_signing_key_id="supervisor-key-v1",
        supervisor_signing_key=b"s" * 32,
        worker_signing_key_id="worker-key-v1",
        worker_signing_key=b"w" * 32,
    )
    start_token = read_process_start_token(os.getpid())
    launch = process_factory.issue_launch(
        result_occurrence_id="result-id",
        manifest_entry_preimage_digest="manifest-preimage",
        execution_nonce="execution-nonce-1",
        child_pid=os.getpid(), child_start_token=start_token,
        stream_id="stream-id", source_snapshot_fingerprint="source-id",
        deadline_policy_digest="deadline-policy",
    )
    store = DurableCheckpointStore(tmp_path, process_factory, "execution-nonce-1")
    store.persist_launch(launch)
    environment = {
        CHILD_ENV_ROOT: str(tmp_path),
        CHILD_ENV_NONCE: "execution-nonce-1",
        CHILD_ENV_LAUNCH: str(store.directory / "launch.json"),
        CHILD_ENV_SUPERVISOR_KEY_ID: "supervisor-key-v1",
        CHILD_ENV_SUPERVISOR_KEY_FILE: str(supervisor_key),
        CHILD_ENV_WORKER_KEY_ID: "worker-key-v1",
        CHILD_ENV_WORKER_KEY_FILE: str(worker_key),
    }
    for key, value in environment.items():
        monkeypatch.setenv(key, value)
    runtime = ProcessWorkerRuntime.from_environment()
    assert runtime.launch.receipt_digest == launch.receipt_digest
    assert runtime.worker_start_token == start_token


def test_active_session_without_supervisor_environment_is_transparent(
    tmp_path, monkeypatch,
):
    for key in (
        CHILD_ENV_ROOT, CHILD_ENV_NONCE, CHILD_ENV_LAUNCH,
        CHILD_ENV_SUPERVISOR_KEY_ID, CHILD_ENV_SUPERVISOR_KEY_FILE,
        CHILD_ENV_WORKER_KEY_ID, CHILD_ENV_WORKER_KEY_FILE,
    ):
        monkeypatch.delenv(key, raising=False)
    raw = Result(timed_out=True)
    session, store, analyzer, function = _runtime_case(
        tmp_path, result=raw, case="no-supervisor-environment",
    )
    del session.domain_signal_state["unknown_taxonomy_v2_process_worker_runtime"]
    with production_signal_scope(session):
        observed = decompile_function(
            analyzer, function, 60, None,
            source_contract_id=TOP_LEVEL_SOURCE_CONTRACT,
        )
    assert observed is raw
    assert analyzer.decompiler.calls == 1
    assert not (store.directory / "checkpoint.json").exists()
