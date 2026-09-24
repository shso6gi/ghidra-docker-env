import os

import pytest

from scripts.function_tracer_pcode.authority.contracts import authority_digest
from scripts.function_tracer_pcode.authority.process.supervisor import (
    DurableCheckpointStore,
    ProcessSupervisorAuthorityFactory,
)
from scripts.function_tracer_pcode.authority.process.supervisor_command import (
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
from scripts.function_tracer_pcode.authority.process.worker_runtime import (
    CanonicalCensusInvalid,
    ProcessWorkerRuntime,
    require_canonical_supervisor_projection,
)


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
        "RESOLVED": "SupervisorCanonicalResultResolvedReceipt",
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


@pytest.mark.parametrize("kind", (
    "CheckpointStateTransitionReceipt", "SupervisorChildExitReceipt",
))
def test_decompile_checkpoint_or_exit_observation_is_not_a_pair_resolution(kind):
    """Issue #165: checkpoint の RESOLVED や E は pair の RESOLVED ではない。"""
    body = dict(_projection("RESOLVED", 0))
    body.pop("projection_digest")
    body["authority_kind"] = kind
    payload = {**body, "projection_digest": authority_digest(body)}
    with pytest.raises(CanonicalCensusInvalid, match="status/authority differs"):
        require_canonical_supervisor_projection(payload)


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

