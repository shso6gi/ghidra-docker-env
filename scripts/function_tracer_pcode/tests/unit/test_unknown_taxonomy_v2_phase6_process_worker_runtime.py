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


def process_factory_receipt(store, filename):
    import json

    return store.factory.decode(json.loads(
        (store.directory / filename).read_text(encoding="utf-8")
    ))


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

