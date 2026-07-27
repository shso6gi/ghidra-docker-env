import json
import os
from dataclasses import replace
from pathlib import Path
import sys
from enum import Enum

import pytest

from scripts.function_tracer_pcode.equivalence.v2.contracts import (
    authority_digest,
)
from scripts.function_tracer_pcode.equivalence.v2.decision import (
    FinalizationAuthority,
    TerminalTimeoutReceipt,
    finalize_decision,
)
from scripts.function_tracer_pcode.equivalence.v2.operational_extraction import (
    OPERATIONAL_REASON_REGISTRY,
    OPERATIONAL_RECOVERY_REGISTRY,
)
from scripts.function_tracer_pcode.equivalence.v2.reducer import ShadowLifecycleReducer
from scripts.function_tracer_pcode.equivalence.v2.stream import EventIntent
from scripts.function_tracer_pcode.equivalence.v2.process_supervisor_command import (
    ProcessSupervisorCommand,
    SupervisorCommandConfig,
    read_process_start_token,
)
from scripts.function_tracer_pcode.equivalence.v2.process_supervisor import (
    CHECKPOINT_AUTHORITY_FILENAMES,
    CheckpointState,
)
from scripts.function_tracer_pcode.equivalence.v2.canonical_result import (
    classify_pair_status,
)
from scripts.function_tracer_pcode.tests.unit.test_unknown_taxonomy_v2_phase6_process_supervisor import (
    _active_process_authority,
    _completed_continuation,
)


def _config(tmp_path, child_command, *, timeout=30.0):
    authority = _active_process_authority()
    supervisor_key = tmp_path / "supervisor.key"
    worker_key = tmp_path / "worker.key"
    supervisor_key.write_bytes(b"s" * 32)
    worker_key.write_bytes(b"w" * 32)
    return authority, SupervisorCommandConfig(
        checkpoint_root=tmp_path / "checkpoints",
        authority_output=tmp_path / "authority.json",
        working_directory=Path.cwd(),
        execution_nonce="execution-nonce-1",
        result_occurrence_id=(
            authority["session"].identity.result_occurrence_id
        ),
        source_snapshot_fingerprint=(
            authority["session"].identity.source_snapshot_fingerprint
        ),
        stream_id=authority["prefix"].stream_id,
        deadline_policy_digest="deadline-policy-digest",
        supervisor_signing_key_id="supervisor-key-v1",
        supervisor_signing_key_file=supervisor_key,
        worker_signing_key_id="worker-key-v1",
        worker_signing_key_file=worker_key,
        timeout_seconds=timeout,
        kill_grace_seconds=0.1,
        child_command=tuple(child_command),
    )


def _projection(path):
    payload = json.loads(path.read_text(encoding="utf-8"))
    digest = payload.pop("projection_digest")
    assert digest == authority_digest(payload)
    return payload


def _classify_durable_projection(command):
    config = command.config
    return classify_pair_status(
        config.working_directory / "unused-terminal-log",
        config.authority_output,
        checkpoint_root=config.checkpoint_root,
        execution_nonce=config.execution_nonce,
        supervisor_signing_key_id=config.supervisor_signing_key_id,
        supervisor_signing_key_file=config.supervisor_signing_key_file,
        worker_signing_key_id=config.worker_signing_key_id,
        worker_signing_key_file=config.worker_signing_key_file,
    )


def _json_authority_value(value):
    if isinstance(value, Enum):
        return value.value
    if isinstance(value, dict):
        return {str(key): _json_authority_value(item) for key, item in value.items()}
    if isinstance(value, (tuple, list)):
        return [_json_authority_value(item) for item in value]
    return value


def _persistable_authority(value):
    return _json_authority_value({
        name: getattr(value, name)
        for name in value.__dataclass_fields__
        if not name.startswith("_")
    })


def _persist_active_for_command(command, authority):
    launch = command.factory.issue_launch(
        result_occurrence_id=command.config.result_occurrence_id,
        manifest_entry_preimage_digest=command.config.manifest_entry_preimage_digest,
        execution_nonce=command.config.execution_nonce,
        child_pid=4242, child_start_token="pid-start-token",
        stream_id=command.config.stream_id,
        source_snapshot_fingerprint=command.config.source_snapshot_fingerprint,
        deadline_policy_digest=command.config.deadline_policy_digest,
    )
    assignment = command.factory.decode(authority["assignment"].to_dict())
    checkpoint = command.factory.issue_active_checkpoint(
        launch=launch, prefix=authority["prefix"],
        projection=authority["projection"], assignment=assignment,
        invocation=authority["invocation"],
        operational_factory=authority["operational_factory"],
        worker_pid=4242, worker_start_token="pid-start-token",
    )
    command.store.persist_launch(launch)
    command.store.persist_active(checkpoint, authority["prefix"])
    return launch, checkpoint


def _child_persist_active(*, sleep_seconds, ignore_sigterm=False):
    """Subprocess entry used to exercise the real launch/checkpoint boundary."""
    import signal
    import time
    from scripts.function_tracer_pcode.equivalence.v2.process_supervisor import (
        DurableCheckpointStore,
        ProcessSupervisorAuthorityFactory,
    )

    authority = _active_process_authority()
    supervisor = ProcessSupervisorAuthorityFactory(
        supervisor_signing_key_id=os.environ[
            "UNKNOWN_TAXONOMY_V2_SUPERVISOR_KEY_ID"
        ],
        supervisor_signing_key=Path(os.environ[
            "UNKNOWN_TAXONOMY_V2_SUPERVISOR_KEY_FILE"
        ]).read_bytes(),
        worker_signing_key_id=os.environ["UNKNOWN_TAXONOMY_V2_WORKER_KEY_ID"],
        worker_signing_key=Path(os.environ[
            "UNKNOWN_TAXONOMY_V2_WORKER_KEY_FILE"
        ]).read_bytes(),
    )
    launch = supervisor.decode(json.loads(Path(os.environ[
        "UNKNOWN_TAXONOMY_V2_LAUNCH_PATH"
    ]).read_text()))
    assignment = supervisor.issue_live_assignment(
        prefix=authority["prefix"], projection=authority["projection"],
        reason_id="function_decompilation_artifact_unavailable",
    )
    checkpoint = supervisor.issue_active_checkpoint(
        launch=launch, prefix=authority["prefix"],
        projection=authority["projection"], assignment=assignment,
        invocation=authority["invocation"],
        operational_factory=authority["operational_factory"],
        worker_pid=os.getpid(),
        worker_start_token=launch.payload["child_start_token"],
    )
    store = DurableCheckpointStore(
        Path(os.environ["UNKNOWN_TAXONOMY_V2_SUPERVISOR_ROOT"]),
        supervisor, os.environ["UNKNOWN_TAXONOMY_V2_EXECUTION_NONCE"],
    )
    store.persist_active(checkpoint, authority["prefix"])
    if ignore_sigterm:
        signal.signal(signal.SIGTERM, signal.SIG_IGN)
    if sleep_seconds:
        time.sleep(sleep_seconds)


def test_process_start_token_is_bound_to_current_linux_process():
    token = read_process_start_token(os.getpid())
    assert token.startswith("linux-proc-starttime-")
    assert token.removeprefix("linux-proc-starttime-").isascii()
    assert token.removeprefix("linux-proc-starttime-").isdecimal()


def test_command_fails_closed_without_deployment_signing_keys(tmp_path):
    _authority, config = _config(tmp_path, (sys.executable, "-c", "pass"))
    config.supervisor_signing_key_file.unlink()
    with pytest.raises(ValueError, match="signing key"):
        ProcessSupervisorCommand(config)


def test_error_restart_rejects_every_checkpoint_authority_filename(tmp_path):
    expected = {
        "pending-active-transaction.json",
        "checkpoint.json", "state.json", "checkpoint-prefix-stream.json",
        "continuation.json", "continuation-stream.json", "ready.json",
        "recovery-resolution.json", "claimed.json", "timeout.json",
        "terminal-segment.json", "terminal-stream.json",
        "child-exit.json",
    }
    assert set(CHECKPOINT_AUTHORITY_FILENAMES) == expected
    for index, filename in enumerate(CHECKPOINT_AUTHORITY_FILENAMES):
        case_root = tmp_path / str(index)
        case_root.mkdir()
        authority, config = _config(
            case_root, (sys.executable, "-c", "pass")
        )
        command = ProcessSupervisorCommand(config)
        launch = command.factory.issue_launch(
            result_occurrence_id=config.result_occurrence_id,
            manifest_entry_preimage_digest=config.manifest_entry_preimage_digest,
            execution_nonce=config.execution_nonce,
            child_pid=4242, child_start_token="pid-start-token",
            stream_id=config.stream_id,
            source_snapshot_fingerprint=config.source_snapshot_fingerprint,
            deadline_policy_digest=config.deadline_policy_digest,
        )
        command.store.persist_launch(launch)
        command.store.supervisor_finalize_operational_error(
            launch=launch, error_kind="operational_authority_invalid",
            deadline_stage="BEFORE_CHECKPOINT",
            child_exit_disposition="EXIT_CODE_2",
        )
        (command.store.directory / filename).write_text("{}", encoding="utf-8")
        assert ProcessSupervisorCommand(config).run() == 2
        projection = _projection(config.authority_output)
        assert projection["status"] == "INVALID"


def test_launch_is_durable_before_child_exec_and_no_checkpoint_is_error(tmp_path):
    marker = tmp_path / "child-marker.json"
    code = (
        "import json,os,pathlib;"
        "launch=pathlib.Path(os.environ['UNKNOWN_TAXONOMY_V2_LAUNCH_PATH']);"
        "assert launch.exists();"
        f"pathlib.Path({str(marker)!r}).write_text(json.dumps({{'launch':str(launch)}}))"
    )
    _authority, config = _config(
        tmp_path, (sys.executable, "-c", code), timeout=30.0
    )
    command = ProcessSupervisorCommand(config)
    assert command.run() == 2
    assert marker.exists()
    projection = _projection(config.authority_output)
    assert projection["status"] == "ERROR"
    assert projection["authority_kind"] == "DurableErrorFinalizationBundle"
    bundle = command.store.rematerialize_operational_error_bundle()
    assert bundle.bundle_digest == projection["finalization_bundle_digest"]
    assert bundle.error_kind == "operational_authority_invalid"
    classified = _classify_durable_projection(command)
    assert classified["canonical_outcome"] == "ERROR"
    assert classified["classification_valid"] is True
    original_projection = config.authority_output.read_bytes()
    forged_projection = json.loads(original_projection)
    forged_projection["child_returncode"] = 17
    forged_projection["projection_digest"] = authority_digest({
        key: value for key, value in forged_projection.items()
        if key != "projection_digest"
    })
    config.authority_output.write_text(
        json.dumps(forged_projection), encoding="utf-8"
    )
    with pytest.raises(ValueError, match="return code differs"):
        _classify_durable_projection(command)
    config.authority_output.write_bytes(original_projection)
    config.authority_output.unlink()
    assert ProcessSupervisorCommand(config).run() == 2
    restarted = _projection(config.authority_output)
    assert restarted["status"] == "ERROR"
    assert restarted["finalization_bundle_digest"] == bundle.bundle_digest
    (command.store.directory / "state.json").write_text(
        (command.store.directory / "operational-error.json").read_text(),
        encoding="utf-8",
    )
    assert ProcessSupervisorCommand(config).run() == 2
    conflicted = _projection(config.authority_output)
    assert conflicted["status"] == "INVALID"


def test_whole_process_mode_rejects_bundleless_child_exit(tmp_path):
    _authority, base_config = _config(
        tmp_path, (sys.executable, "-c", "pass"), timeout=30.0
    )
    config = replace(base_config, allow_child_exit_resolution=True)

    command = ProcessSupervisorCommand(config)
    assert command.run() == 2
    projection = _projection(config.authority_output)
    assert projection["status"] == "INVALID"
    assert projection["authority_kind"] == "InvalidSupervisorCommandProjection"
    assert projection["error_code"] == "CANONICAL_CHILD_RESULT_INVALID"
    assert projection["child_returncode"] == 0

    config.authority_output.unlink()
    assert ProcessSupervisorCommand(config).run() == 2
    assert _projection(config.authority_output)["status"] == "INVALID"


def test_deadline_without_worker_checkpoint_gets_durable_process_timeout(tmp_path):
    _authority, config = _config(
        tmp_path,
        (sys.executable, "-c", "import time; time.sleep(30)"),
        timeout=0.2,
    )
    command = ProcessSupervisorCommand(config)
    assert command.run() == 124
    projection = _projection(config.authority_output)
    assert projection["status"] == "TIMEOUT"
    assert projection["authority_kind"] == "DurableTimeoutFinalizationBundle"
    classified = _classify_durable_projection(command)
    assert classified["canonical_outcome"] == "TIMEOUT"
    assert classified["classification_valid"] is True


def test_deadline_recovers_active_transaction_interrupted_before_state_commit(
    tmp_path, monkeypatch,
):
    authority, config = _config(tmp_path, (sys.executable, "-c", "pass"))
    command = ProcessSupervisorCommand(config)
    launch = command.factory.issue_launch(
        result_occurrence_id=config.result_occurrence_id,
        manifest_entry_preimage_digest=config.manifest_entry_preimage_digest,
        execution_nonce=config.execution_nonce,
        child_pid=4242,
        child_start_token="pid-start-token",
        stream_id=config.stream_id,
        source_snapshot_fingerprint=config.source_snapshot_fingerprint,
        deadline_policy_digest=config.deadline_policy_digest,
    )
    assignment = command.factory.decode(authority["assignment"].to_dict())
    checkpoint = command.factory.issue_active_checkpoint(
        launch=launch,
        prefix=authority["prefix"],
        projection=authority["projection"],
        assignment=assignment,
        invocation=authority["invocation"],
        operational_factory=authority["operational_factory"],
        worker_pid=4242,
        worker_start_token="pid-start-token",
    )
    command.store.persist_launch(launch)
    original_replace = command.store._atomic_replace
    interrupted = False

    def interrupt_state_commit(path, data):
        nonlocal interrupted
        if path.name == "state.json" and not interrupted:
            interrupted = True
            raise RuntimeError("fault injection before ACTIVE state commit")
        return original_replace(path, data)

    monkeypatch.setattr(command.store, "_atomic_replace", interrupt_state_commit)
    with pytest.raises(RuntimeError, match="fault injection"):
        command.store.persist_active(checkpoint, authority["prefix"])
    assert (command.store.directory / "pending-active-transaction.json").is_file()
    assert (command.store.directory / "checkpoint-prefix-stream.json").is_file()
    assert (command.store.directory / "checkpoint.json").is_file()
    assert not (command.store.directory / "state.json").exists()

    process = type("DeadlineProcess", (), {"returncode": 143})()
    monkeypatch.setattr(
        command,
        "_terminate_exact_process_group",
        lambda _process, _token: "EXITED_143_AFTER_SIGTERM",
    )
    exit_code, projection = command._finalize_deadline(
        launch=launch,
        process=process,
        start_token="pid-start-token",
    )
    command._write_projection(projection)

    assert exit_code == 124
    assert projection["status"] == "TIMEOUT"
    assert not (command.store.directory / "pending-active-transaction.json").exists()
    classified = _classify_durable_projection(command)
    assert classified["canonical_outcome"] == "TIMEOUT"
    assert classified["classification_valid"] is True


def test_deadline_ignores_uncommitted_continuation_stream(
    tmp_path, monkeypatch,
):
    authority, config = _config(tmp_path, (sys.executable, "-c", "pass"))
    command = ProcessSupervisorCommand(config)
    launch, checkpoint = _persist_active_for_command(command, authority)
    continuation, stream = _completed_continuation(
        authority, supervisor=command.factory, checkpoint=checkpoint,
    )
    original_write = command.store._atomic_write
    continuation_member_writes = 0

    def interrupt_continuation_marker(path, data, *, identical_ok=False):
        nonlocal continuation_member_writes
        if path.name in {"continuation.json", "continuation-stream.json"}:
            continuation_member_writes += 1
            if continuation_member_writes == 2:
                raise RuntimeError("fault injection before continuation commit")
        return original_write(path, data, identical_ok=identical_ok)

    monkeypatch.setattr(
        command.store, "_atomic_write", interrupt_continuation_marker,
    )
    with pytest.raises(RuntimeError, match="fault injection"):
        command.store.worker_publish_continuation(
            active=checkpoint, continuation=continuation,
            prefix=authority["prefix"], continuation_stream=stream,
        )
    assert (command.store.directory / "continuation-stream.json").is_file()
    assert not (command.store.directory / "continuation.json").exists()

    monkeypatch.setattr(command.store, "_atomic_write", original_write)
    process = type("DeadlineProcess", (), {"returncode": 143})()
    monkeypatch.setattr(
        command,
        "_terminate_exact_process_group",
        lambda _process, _token: "EXITED_143_AFTER_SIGTERM",
    )
    exit_code, projection = command._finalize_deadline(
        launch=launch,
        process=process,
        start_token="pid-start-token",
    )
    command._write_projection(projection)

    assert exit_code == 124
    assert projection["status"] == "TIMEOUT"
    classified = _classify_durable_projection(command)
    assert classified["canonical_outcome"] == "TIMEOUT"
    assert classified["classification_valid"] is True


def test_active_transaction_recovers_when_interrupted_before_member_writes(
    tmp_path, monkeypatch,
):
    authority, config = _config(tmp_path, (sys.executable, "-c", "pass"))
    command = ProcessSupervisorCommand(config)
    launch = command.factory.issue_launch(
        result_occurrence_id=config.result_occurrence_id,
        manifest_entry_preimage_digest=config.manifest_entry_preimage_digest,
        execution_nonce=config.execution_nonce,
        child_pid=4242,
        child_start_token="pid-start-token",
        stream_id=config.stream_id,
        source_snapshot_fingerprint=config.source_snapshot_fingerprint,
        deadline_policy_digest=config.deadline_policy_digest,
    )
    assignment = command.factory.decode(authority["assignment"].to_dict())
    checkpoint = command.factory.issue_active_checkpoint(
        launch=launch,
        prefix=authority["prefix"],
        projection=authority["projection"],
        assignment=assignment,
        invocation=authority["invocation"],
        operational_factory=authority["operational_factory"],
        worker_pid=4242,
        worker_start_token="pid-start-token",
    )
    command.store.persist_launch(launch)
    original_write = command.store._atomic_write
    interrupted = False

    def interrupt_first_member(path, data, *, identical_ok=False):
        nonlocal interrupted
        if path.name == "checkpoint-prefix-stream.json" and not interrupted:
            interrupted = True
            raise RuntimeError("fault injection before ACTIVE member writes")
        return original_write(path, data, identical_ok=identical_ok)

    monkeypatch.setattr(command.store, "_atomic_write", interrupt_first_member)
    with pytest.raises(RuntimeError, match="fault injection"):
        command.store.persist_active(checkpoint, authority["prefix"])
    assert (command.store.directory / "pending-active-transaction.json").is_file()
    assert not (command.store.directory / "checkpoint-prefix-stream.json").exists()
    assert not (command.store.directory / "checkpoint.json").exists()
    assert not (command.store.directory / "state.json").exists()

    monkeypatch.setattr(command.store, "_atomic_write", original_write)
    recovered, recovered_prefix = command.store.recover_pending_active_commit()

    assert recovered.receipt_digest == checkpoint.receipt_digest
    assert recovered_prefix.prefix_authority_digest == (
        authority["prefix"].prefix_authority_digest
    )
    assert command.store.read_state().receipt_digest == checkpoint.receipt_digest
    assert not (command.store.directory / "pending-active-transaction.json").exists()


def test_active_transaction_recovers_after_state_commit_before_pending_removal(
    tmp_path, monkeypatch,
):
    authority, config = _config(tmp_path, (sys.executable, "-c", "pass"))
    command = ProcessSupervisorCommand(config)
    launch = command.factory.issue_launch(
        result_occurrence_id=config.result_occurrence_id,
        manifest_entry_preimage_digest=config.manifest_entry_preimage_digest,
        execution_nonce=config.execution_nonce,
        child_pid=4242,
        child_start_token="pid-start-token",
        stream_id=config.stream_id,
        source_snapshot_fingerprint=config.source_snapshot_fingerprint,
        deadline_policy_digest=config.deadline_policy_digest,
    )
    assignment = command.factory.decode(authority["assignment"].to_dict())
    checkpoint = command.factory.issue_active_checkpoint(
        launch=launch,
        prefix=authority["prefix"],
        projection=authority["projection"],
        assignment=assignment,
        invocation=authority["invocation"],
        operational_factory=authority["operational_factory"],
        worker_pid=4242,
        worker_start_token="pid-start-token",
    )
    command.store.persist_launch(launch)
    original_remove = command.store._remove_pending_active_locked
    interrupted = False

    def interrupt_pending_removal():
        nonlocal interrupted
        if not interrupted:
            interrupted = True
            raise RuntimeError("fault injection after ACTIVE state commit")
        return original_remove()

    monkeypatch.setattr(
        command.store, "_remove_pending_active_locked",
        interrupt_pending_removal,
    )
    with pytest.raises(RuntimeError, match="fault injection"):
        command.store.persist_active(checkpoint, authority["prefix"])
    assert command.store.read_state().receipt_digest == checkpoint.receipt_digest
    assert (command.store.directory / "checkpoint-prefix-stream.json").is_file()
    assert (command.store.directory / "checkpoint.json").is_file()
    assert (command.store.directory / "pending-active-transaction.json").is_file()

    monkeypatch.setattr(
        command.store, "_remove_pending_active_locked", original_remove,
    )
    recovered, _recovered_prefix = command.store.recover_pending_active_commit()

    assert recovered.receipt_digest == checkpoint.receipt_digest
    assert command.store.read_state().receipt_digest == checkpoint.receipt_digest
    assert not (command.store.directory / "pending-active-transaction.json").exists()


def test_active_transaction_recovery_rejects_cross_nonce_replay(
    tmp_path, monkeypatch,
):
    authority, config = _config(tmp_path, (sys.executable, "-c", "pass"))
    source = ProcessSupervisorCommand(config)
    launch = source.factory.issue_launch(
        result_occurrence_id=config.result_occurrence_id,
        manifest_entry_preimage_digest=config.manifest_entry_preimage_digest,
        execution_nonce=config.execution_nonce,
        child_pid=4242,
        child_start_token="pid-start-token",
        stream_id=config.stream_id,
        source_snapshot_fingerprint=config.source_snapshot_fingerprint,
        deadline_policy_digest=config.deadline_policy_digest,
    )
    assignment = source.factory.decode(authority["assignment"].to_dict())
    checkpoint = source.factory.issue_active_checkpoint(
        launch=launch,
        prefix=authority["prefix"],
        projection=authority["projection"],
        assignment=assignment,
        invocation=authority["invocation"],
        operational_factory=authority["operational_factory"],
        worker_pid=4242,
        worker_start_token="pid-start-token",
    )
    source.store.persist_launch(launch)
    monkeypatch.setattr(
        source.store, "_commit_pending_active_locked",
        lambda: (_ for _ in ()).throw(
            RuntimeError("fault injection after pending persistence")
        ),
    )
    with pytest.raises(RuntimeError, match="fault injection"):
        source.store.persist_active(checkpoint, authority["prefix"])

    replay_config = replace(config, execution_nonce="execution-nonce-2")
    replay = ProcessSupervisorCommand(replay_config)
    (replay.store.directory / "launch.json").write_bytes(
        (source.store.directory / "launch.json").read_bytes()
    )
    pending = json.loads(
        (source.store.directory / "pending-active-transaction.json").read_text()
    )
    pending["invocation_nonce"] = replay_config.execution_nonce
    pending["transaction_digest"] = authority_digest({
        key: value for key, value in pending.items()
        if key != "transaction_digest"
    })
    (replay.store.directory / "pending-active-transaction.json").write_text(
        json.dumps(pending, sort_keys=True, separators=(",", ":")) + "\n"
    )

    with pytest.raises(
        ValueError, match="pending ACTIVE transaction launch authority differs",
    ):
        replay.store.recover_pending_active_commit()
    assert not (replay.store.directory / "checkpoint.json").exists()
    assert not (replay.store.directory / "state.json").exists()


def test_interrupted_next_active_transaction_retains_resolved_predecessor(
    tmp_path, monkeypatch,
):
    authority, config = _config(tmp_path, (sys.executable, "-c", "pass"))
    command = ProcessSupervisorCommand(config)
    launch, first = _persist_active_for_command(command, authority)
    continuation, stream = _completed_continuation(
        authority,
        supervisor=command.factory,
        checkpoint=first,
    )
    _ready, resolved = command.store.worker_publish_completion(
        active=first,
        continuation=continuation,
        prefix=authority["prefix"],
        continuation_stream=stream,
    )
    assignment = command.factory.decode(authority["assignment"].to_dict())
    second = command.factory.issue_active_checkpoint(
        launch=launch,
        prefix=authority["prefix"],
        projection=authority["projection"],
        assignment=assignment,
        invocation=authority["invocation"],
        operational_factory=authority["operational_factory"],
        worker_pid=4242,
        worker_start_token="pid-start-token",
        prior_resolved=resolved,
    )
    original_replace = command.store._atomic_replace
    interrupted = False

    def interrupt_state_commit(path, data):
        nonlocal interrupted
        if path.name == "state.json" and not interrupted:
            interrupted = True
            raise RuntimeError("fault injection before ACTIVE state commit")
        return original_replace(path, data)

    monkeypatch.setattr(command.store, "_atomic_replace", interrupt_state_commit)
    with pytest.raises(RuntimeError, match="fault injection"):
        command.store.persist_active(second, authority["prefix"])
    history = (
        command.store.directory
        / "checkpoint-history"
        / resolved.receipt_digest
    )
    assert (history / "state.json").is_file()
    assert command.factory.decode(json.loads(
        (history / "state.json").read_text(encoding="utf-8")
    )).receipt_digest == resolved.receipt_digest

    recovered, recovered_prefix = command.store.recover_pending_active_commit()

    assert recovered.receipt_digest == second.receipt_digest
    assert recovered_prefix.prefix_authority_digest == (
        authority["prefix"].prefix_authority_digest
    )
    assert command.store.read_state().receipt_digest == second.receipt_digest
    assert (history / "state.json").is_file()


def test_interrupted_resolved_archive_is_resumed_before_active_commit(
    tmp_path, monkeypatch,
):
    authority, config = _config(tmp_path, (sys.executable, "-c", "pass"))
    command = ProcessSupervisorCommand(config)
    launch, first = _persist_active_for_command(command, authority)
    continuation, stream = _completed_continuation(
        authority,
        supervisor=command.factory,
        checkpoint=first,
    )
    _ready, resolved = command.store.worker_publish_completion(
        active=first,
        continuation=continuation,
        prefix=authority["prefix"],
        continuation_stream=stream,
    )
    assignment = command.factory.decode(authority["assignment"].to_dict())
    second = command.factory.issue_active_checkpoint(
        launch=launch,
        prefix=authority["prefix"],
        projection=authority["projection"],
        assignment=assignment,
        invocation=authority["invocation"],
        operational_factory=authority["operational_factory"],
        worker_pid=4242,
        worker_start_token="pid-start-token",
        prior_resolved=resolved,
    )
    original_replace = os.replace
    interrupted = False

    def interrupt_archive(source, destination):
        nonlocal interrupted
        source_path = Path(source)
        destination_path = Path(destination)
        if (
            source_path == command.store.directory / "checkpoint.json"
            and destination_path.parent.name == resolved.receipt_digest
            and not interrupted
        ):
            interrupted = True
            raise RuntimeError("fault injection during RESOLVED archive")
        return original_replace(source, destination)

    monkeypatch.setattr(os, "replace", interrupt_archive)
    with pytest.raises(RuntimeError, match="fault injection"):
        command.store.persist_active(second, authority["prefix"])
    history = (
        command.store.directory
        / "checkpoint-history"
        / resolved.receipt_digest
    )
    assert (history / "checkpoint-prefix-stream.json").is_file()
    assert not (history / "state.json").exists()
    assert (command.store.directory / "state.json").is_file()

    monkeypatch.setattr(os, "replace", original_replace)
    recovered, _recovered_prefix = command.store.recover_pending_active_commit()

    assert recovered.receipt_digest == second.receipt_digest
    assert command.store.read_state().receipt_digest == second.receipt_digest
    assert command.factory.decode(json.loads(
        (history / "state.json").read_text(encoding="utf-8")
    )).receipt_digest == resolved.receipt_digest


@pytest.mark.parametrize(
    ("tamper_name", "tamper_payload"),
    (
        ("checkpoint.json", b"{}\n"),
        ("checkpoint-prefix-stream.json", b"{}\n"),
        ("pending-active-transaction.json", b"{}\n"),
    ),
)
def test_interrupted_active_transaction_rejects_tampered_authority(
    tmp_path, monkeypatch, tamper_name, tamper_payload,
):
    authority, config = _config(tmp_path, (sys.executable, "-c", "pass"))
    command = ProcessSupervisorCommand(config)
    launch = command.factory.issue_launch(
        result_occurrence_id=config.result_occurrence_id,
        manifest_entry_preimage_digest=config.manifest_entry_preimage_digest,
        execution_nonce=config.execution_nonce,
        child_pid=4242,
        child_start_token="pid-start-token",
        stream_id=config.stream_id,
        source_snapshot_fingerprint=config.source_snapshot_fingerprint,
        deadline_policy_digest=config.deadline_policy_digest,
    )
    assignment = command.factory.decode(authority["assignment"].to_dict())
    checkpoint = command.factory.issue_active_checkpoint(
        launch=launch,
        prefix=authority["prefix"],
        projection=authority["projection"],
        assignment=assignment,
        invocation=authority["invocation"],
        operational_factory=authority["operational_factory"],
        worker_pid=4242,
        worker_start_token="pid-start-token",
    )
    command.store.persist_launch(launch)
    original_replace = command.store._atomic_replace

    def interrupt_state_commit(path, data):
        if path.name == "state.json":
            raise RuntimeError("fault injection before ACTIVE state commit")
        return original_replace(path, data)

    monkeypatch.setattr(command.store, "_atomic_replace", interrupt_state_commit)
    with pytest.raises(RuntimeError, match="fault injection"):
        command.store.persist_active(checkpoint, authority["prefix"])
    (command.store.directory / tamper_name).write_bytes(tamper_payload)
    with pytest.raises(ValueError, match="pending ACTIVE transaction"):
        command.store.recover_pending_active_commit()


def test_deadline_does_not_misclassify_resolved_child_checkpoint_as_pair_result(
    tmp_path, monkeypatch,
):
    authority, config = _config(tmp_path, (sys.executable, "-c", "pass"))
    command = ProcessSupervisorCommand(config)
    launch, checkpoint = _persist_active_for_command(command, authority)
    continuation, stream = _completed_continuation(
        authority, supervisor=command.factory, checkpoint=checkpoint,
    )
    _ready, resolved = command.store.worker_publish_completion(
        active=checkpoint, continuation=continuation,
        prefix=authority["prefix"], continuation_stream=stream,
    )
    assert resolved.payload["state"] == CheckpointState.RESOLVED.value
    process = type("DeadlineProcess", (), {"returncode": 143})()
    monkeypatch.setattr(
        command, "_terminate_exact_process_group",
        lambda _process, _token: "EXITED_143_AFTER_SIGTERM",
    )
    exit_code, projection = command._finalize_deadline(
        launch=launch, process=process, start_token="pid-start-token",
    )
    command._write_projection(projection)
    assert exit_code == 124
    assert projection["status"] == "TIMEOUT"
    classified = _classify_durable_projection(command)
    assert classified["canonical_outcome"] == "TIMEOUT"
    assert classified["classification_valid"] is True
    history = command.store.directory / "checkpoint-history" / resolved.receipt_digest
    assert history.is_dir()


def test_deadline_with_exact_durable_active_checkpoint_is_timeout(tmp_path):
    child_code = (
        "from scripts.function_tracer_pcode.tests.unit."
        "test_unknown_taxonomy_v2_phase6_process_supervisor_command "
        "import _child_persist_active;"
        "_child_persist_active(sleep_seconds=120)"
    )
    authority, config = _config(
        # Importing the full authority fixture is intentionally outside the
        # supervisor model under test and can take several seconds on WSL.
        # Leave enough time for the worker to durably publish ACTIVE before
        # exercising the deadline transition.
        tmp_path, (sys.executable, "-c", child_code), timeout=120.0
    )
    command = ProcessSupervisorCommand(config)
    assert command.run() == 124
    projection = _projection(config.authority_output)
    assert projection["status"] == "TIMEOUT", projection
    assert projection["authority_kind"] == "DurableTimeoutFinalizationBundle"
    prefix = command.store.rematerialize_active_prefix()
    bundle = command.store.rematerialize_timeout_bundle(prefix=prefix)
    assert bundle.bundle_digest == projection["finalization_bundle_digest"]
    assert bundle.result_occurrence_id == authority["session"].identity.result_occurrence_id
    classified = _classify_durable_projection(command)
    assert classified["canonical_outcome"] == "TIMEOUT"
    assert classified["classification_valid"] is True
    timeout_receipt = json.loads(
        (command.store.directory / "timeout.json").read_text()
    )
    assert timeout_receipt["payload"]["kill_disposition"] == "SIGTERM_AFTER_DEADLINE"
    reduction = ShadowLifecycleReducer(
        reason_registry=OPERATIONAL_REASON_REGISTRY,
        recovery_registry=OPERATIONAL_RECOVERY_REGISTRY,
    ).replay(bundle.terminal_segment.composite_stream)
    terminal_event = bundle.terminal_segment.composite_stream.events[-1]
    terminal_timeout_receipt = TerminalTimeoutReceipt.create(
        result_occurrence_id=bundle.result_occurrence_id,
        lifecycle_projection_digest=(
            reduction.projection.lifecycle_projection_digest
        ),
        proof_requirement_id=bundle.proof_requirement_id,
        execution_event_digest=terminal_event.authority_digest,
    )
    decision = finalize_decision(FinalizationAuthority(
        result_occurrence_id=bundle.result_occurrence_id,
        lifecycle_projection=reduction.projection,
        terminal_timeout_receipts=(terminal_timeout_receipt,),
    ))
    assert decision.outcome.value == "TIMEOUT"
    assert len(reduction.projection.c_active_base) >= 1
    assert len(reduction.projection.q_open_base) >= 1
    assert all(
        "timeout" not in row.reason_id.lower()
        for row in reduction.projection.c_active_base
    )
    phase7_runtime = None
    if authority["session"].phase7_runtime is not None:
        terminal_intent = EventIntent(
            terminal_event.header.event_type,
            terminal_event.authority_payload,
            terminal_event.diagnostic_payload,
        )
        authority["session"].phase7_runtime.buffer_execution_intent(terminal_intent)
        phase7_runtime = authority["session"].phase7_runtime.finalize(
            stream_id=bundle.terminal_segment.composite_stream.envelope.stream_id,
            result_occurrence_id=authority["session"].identity.result_occurrence_id,
            source_snapshot_fingerprint=(
                authority["session"].identity.source_snapshot_fingerprint
            ),
        )
        assert phase7_runtime.coverage["v2_native_typed_cause_coverage"] == 1.0
        assert len(phase7_runtime.projection_receipts) == 1
        typed_projection = phase7_runtime.projection_receipts[0]
        assert typed_projection.result_occurrence_id == bundle.result_occurrence_id
        assert (
            phase7_runtime.finalization_bundle.sealed_event_stream.envelope.authority_chain_digest
            == bundle.composite_stream_authority_digest
        )
        assert typed_projection.lifecycle_projection_digest == (
            reduction.projection.lifecycle_projection_digest
        )
        matching_active_causes = tuple(
            row for row in reduction.projection.c_active_base
            if (
                row.result_occurrence_id == typed_projection.result_occurrence_id
                and row.occurrence_id == typed_projection.occurrence_id
                and row.cause_id == typed_projection.cause_id
                and row.reason_id == typed_projection.reason_id
            )
        )
        assert len(matching_active_causes) == 1
    evidence_path = os.environ.get("PHASE7_TIMEOUT_EVIDENCE_PATH")
    if evidence_path:
        body = {
            "manifest_kind": "unknown-taxonomy-v2-phase7-real-process-timeout-v1",
            "result_occurrence_id": bundle.result_occurrence_id,
            "source_snapshot_fingerprint": (
                bundle.terminal_segment.composite_stream.envelope.source_snapshot_fingerprint
            ),
            "durable_timeout_bundle_digest": bundle.bundle_digest,
            "event_stream_digest": bundle.composite_stream_authority_digest,
            "terminal_event_digest": terminal_event.authority_digest,
            "proof_requirement_id": bundle.proof_requirement_id,
            "lifecycle_projection_digest": (
                reduction.projection.lifecycle_projection_digest
            ),
            "decision_receipt_digest": decision.receipt_digest,
            "final_outcome": decision.outcome.value,
            "active_cause_count": len(reduction.projection.c_active_base),
            "open_requirement_count": len(reduction.projection.q_open_base),
            "terminal_timeout_event_count": 1,
            "timeout_derived_reason_count": sum(
                "timeout" in row.reason_id.lower()
                for row in reduction.projection.c_active_base
            ),
            "kill_disposition": timeout_receipt["payload"]["kill_disposition"],
            "typed_projection_receipt_digest": (
                phase7_runtime.projection_receipts[0].receipt_digest
            ),
            "typed_projection_lifecycle_projection_digest": (
                phase7_runtime.projection_receipts[0].lifecycle_projection_digest
            ),
            "typed_projection_semantic_projection_digest": (
                phase7_runtime.projection_receipts[0].semantic_projection_digest
            ),
            "typed_projection_occurrence_id": (
                phase7_runtime.projection_receipts[0].occurrence_id
            ),
            "typed_projection_cause_id": (
                phase7_runtime.projection_receipts[0].cause_id
            ),
            "typed_projection_reason_id": (
                phase7_runtime.projection_receipts[0].reason_id
            ),
            "typed_projection_active_cause_join_count": len(
                matching_active_causes
            ),
            "typed_projection_receipt": _persistable_authority(
                phase7_runtime.projection_receipts[0]
            ),
            "decision_receipt": _persistable_authority(decision),
            "terminal_timeout_receipt": _persistable_authority(
                terminal_timeout_receipt
            ),
            "c_active_rows": tuple(
                _persistable_authority(row)
                for row in reduction.projection.c_active_base
            ),
            "q_open_rows": tuple(
                _persistable_authority(row)
                for row in reduction.projection.q_open_base
            ),
            "durable_live_assignment": _json_authority_value(
                authority["assignment"].to_dict()
            ),
            "durable_store": {
                "execution_nonce": config.execution_nonce,
                "supervisor_signing_key_id": config.supervisor_signing_key_id,
                "supervisor_signing_key_hex": (b"s" * 32).hex(),
                "worker_signing_key_id": config.worker_signing_key_id,
                "worker_signing_key_hex": (b"w" * 32).hex(),
                "files": {
                    path.name: path.read_text(encoding="utf-8")
                    for path in sorted(command.store.directory.iterdir())
                    if path.is_file()
                },
            },
            "runtime_activation_ledger_digest": (
                phase7_runtime.runtime_activation_ledger_digest
            ),
            "expected_activation_ledger_digest": (
                phase7_runtime.expected_activation_ledger_digest
            ),
            "expected_activation_count": phase7_runtime.expected_activation_count,
            "runtime_activation_count": phase7_runtime.runtime_activation_count,
            "not_reached_activation_count": (
                phase7_runtime.not_reached_activation_count
            ),
            "static_producer_site_count": (
                phase7_runtime.static_producer_site_count
            ),
            "discovered_activation_count": (
                phase7_runtime.discovered_activation_count
            ),
            "v2_native_typed_cause_coverage": (
                phase7_runtime.coverage["v2_native_typed_cause_coverage"]
            ),
        }
        payload = {**body, "artifact_digest": authority_digest(body)}
        output = Path(evidence_path)
        output.parent.mkdir(parents=True, exist_ok=True)
        output.write_text(
            json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8"
        )


def test_normal_exit_with_active_checkpoint_is_invalid_not_timeout(tmp_path):
    child_code = (
        "from scripts.function_tracer_pcode.tests.unit."
        "test_unknown_taxonomy_v2_phase6_process_supervisor_command "
        "import _child_persist_active;"
        "_child_persist_active(sleep_seconds=0)"
    )
    _authority, config = _config(
        tmp_path, (sys.executable, "-c", child_code), timeout=120.0
    )
    assert ProcessSupervisorCommand(config).run() == 2
    projection = _projection(config.authority_output)
    assert projection["status"] == "INVALID"
    assert projection["error_code"] == "NONFINAL_ACTIVE_WITHOUT_DEADLINE_AUTHORITY"


def test_deadline_escalates_to_sigkill_and_binds_disposition(tmp_path):
    child_code = (
        "from scripts.function_tracer_pcode.tests.unit."
        "test_unknown_taxonomy_v2_phase6_process_supervisor_command "
        "import _child_persist_active;"
        "_child_persist_active(sleep_seconds=120,ignore_sigterm=True)"
    )
    _authority, config = _config(
        tmp_path, (sys.executable, "-c", child_code), timeout=120.0
    )
    assert ProcessSupervisorCommand(config).run() == 124
    projection = _projection(config.authority_output)
    assert projection["status"] == "TIMEOUT"
    timeout_receipt = json.loads(
        (config.checkpoint_root / config.execution_nonce / "timeout.json").read_text()
    )
    assert timeout_receipt["payload"]["kill_disposition"] == "SIGKILL_AFTER_DEADLINE"


def test_restart_recovers_ready_continuation_as_resolved(tmp_path):
    authority, config = _config(tmp_path, (sys.executable, "-c", "pass"))
    command = ProcessSupervisorCommand(config)
    _launch, checkpoint = _persist_active_for_command(command, authority)
    continuation, stream = _completed_continuation(
        authority, supervisor=command.factory, checkpoint=checkpoint,
    )
    ready, _resolved = command.store.worker_publish_completion(
        active=checkpoint, continuation=continuation,
        prefix=authority["prefix"], continuation_stream=stream,
    )
    # Recreate the durable crash window after READY and before RESOLVED.
    command.store._replace_state_locked(ready)
    assert ProcessSupervisorCommand(config).run() == 0
    projection = _projection(config.authority_output)
    assert projection["status"] == "RESOLVED"
    assert command.store.read_state().payload["state"] == CheckpointState.RESOLVED.value


def test_restart_rejects_resolved_state_with_missing_ready_chain(tmp_path):
    authority, config = _config(tmp_path, (sys.executable, "-c", "pass"))
    command = ProcessSupervisorCommand(config)
    _launch, checkpoint = _persist_active_for_command(command, authority)
    continuation, stream = _completed_continuation(
        authority, supervisor=command.factory, checkpoint=checkpoint,
    )
    command.store.worker_publish_completion(
        active=checkpoint, continuation=continuation,
        prefix=authority["prefix"], continuation_stream=stream,
    )
    (command.store.directory / "ready.json").unlink()
    assert ProcessSupervisorCommand(config).run() == 2
    projection = _projection(config.authority_output)
    assert projection["status"] == "INVALID"
    assert projection["error_code"] == "DURABLE_RESTART_AUTHORITY_INVALID"


def test_restart_finishes_claimed_timeout_and_rematerializes_final_timeout(tmp_path):
    authority, config = _config(tmp_path, (sys.executable, "-c", "pass"))
    command = ProcessSupervisorCommand(config)
    _launch, checkpoint = _persist_active_for_command(command, authority)
    claimed = command.store.supervisor_claim_timeout(
        active=checkpoint, prefix=authority["prefix"],
        kill_disposition="SIGKILL_AFTER_DEADLINE",
    )
    assert claimed.payload["state"] == CheckpointState.TIMED_OUT_CLAIMED.value
    assert ProcessSupervisorCommand(config).run() == 124
    first = _projection(config.authority_output)
    assert first["status"] == "TIMEOUT"
    assert command.store.read_state().payload["state"] == CheckpointState.TIMED_OUT.value
    assert ProcessSupervisorCommand(config).run() == 124
    second = _projection(config.authority_output)
    assert second["finalization_bundle_digest"] == first["finalization_bundle_digest"]


def test_restart_active_without_deadline_authority_is_invalid_not_timeout(tmp_path):
    authority, config = _config(tmp_path, (sys.executable, "-c", "pass"))
    command = ProcessSupervisorCommand(config)
    _persist_active_for_command(command, authority)
    assert ProcessSupervisorCommand(config).run() == 2
    projection = _projection(config.authority_output)
    assert projection["status"] == "INVALID"
    assert projection["error_code"] == "NONFINAL_ACTIVE_WITHOUT_DEADLINE_AUTHORITY"


def test_restart_rejects_tampered_durable_prefix_as_invalid(tmp_path):
    authority, config = _config(tmp_path, (sys.executable, "-c", "pass"))
    command = ProcessSupervisorCommand(config)
    _launch, checkpoint = _persist_active_for_command(command, authority)
    command.store.supervisor_claim_timeout(
        active=checkpoint, prefix=authority["prefix"],
        kill_disposition="SIGTERM_AFTER_DEADLINE",
    )
    (command.store.directory / "checkpoint-prefix-stream.json").write_text(
        "{}", encoding="utf-8"
    )
    assert ProcessSupervisorCommand(config).run() == 2
    projection = _projection(config.authority_output)
    assert projection["status"] == "INVALID"
    assert projection["error_code"] == "DURABLE_RESTART_AUTHORITY_INVALID"


def test_process_exit_between_poll_and_sigterm_is_canonicalized(tmp_path, monkeypatch):
    _authority, config = _config(tmp_path, (sys.executable, "-c", "pass"))
    command = ProcessSupervisorCommand(config)

    class RacedProcess:
        pid = os.getpid()
        returncode = None
        polls = 0

        def poll(self):
            self.polls += 1
            if self.polls >= 3:
                self.returncode = 0
            return self.returncode

    process = RacedProcess()
    monkeypatch.setattr(command, "_same_process", lambda *_args: True)
    monkeypatch.setattr(os, "killpg", lambda *_args: (_ for _ in ()).throw(ProcessLookupError()))
    disposition = command._terminate_exact_process_group(process, "token")
    assert disposition == "EXITED_0_BEFORE_SIGTERM"


def test_live_pid_start_token_mismatch_is_rejected_before_signal(tmp_path, monkeypatch):
    _authority, config = _config(tmp_path, (sys.executable, "-c", "pass"))
    command = ProcessSupervisorCommand(config)

    class ReusedProcess:
        pid = os.getpid()
        returncode = None

        def poll(self):
            return None

    monkeypatch.setattr(command, "_same_process", lambda *_args: False)
    with pytest.raises(ValueError, match="PID/start-token identity changed"):
        command._terminate_exact_process_group(ReusedProcess(), "stale-token")


def test_exception_cleanup_never_signals_pid_with_mismatched_start_token(
    tmp_path, monkeypatch,
):
    _authority, config = _config(tmp_path, (sys.executable, "-c", "pass"))
    command = ProcessSupervisorCommand(config)
    signals = []

    class ReusedProcess:
        pid = os.getpid()

        def poll(self):
            return None

    monkeypatch.setattr(command, "_same_process", lambda *_args: False)
    monkeypatch.setattr(os, "killpg", lambda *args: signals.append(args))
    disposition = command._cleanup_exact_process_group(
        ReusedProcess(), "stale-token"
    )
    assert disposition == "SKIPPED_UNVERIFIED_PROCESS_IDENTITY"
    assert signals == []


def test_exception_cleanup_canonicalizes_exit_before_sigkill(tmp_path, monkeypatch):
    _authority, config = _config(tmp_path, (sys.executable, "-c", "pass"))
    command = ProcessSupervisorCommand(config)

    class RacedProcess:
        pid = os.getpid()
        polls = 0

        def poll(self):
            self.polls += 1
            return 0 if self.polls >= 2 else None

    process = RacedProcess()
    monkeypatch.setattr(command, "_same_process", lambda *_args: True)
    monkeypatch.setattr(
        os, "killpg",
        lambda *_args: (_ for _ in ()).throw(AssertionError("must not signal")),
    )
    disposition = command._cleanup_exact_process_group(process, "token")
    assert disposition == "EXITED_0_BEFORE_CLEANUP_SIGKILL"
