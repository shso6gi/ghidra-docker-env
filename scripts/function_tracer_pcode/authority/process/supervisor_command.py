"""Canonical OS-process supervisor for UNKNOWN-taxonomy v2 workers."""

from __future__ import annotations

import argparse
from dataclasses import dataclass
import json
import os
from pathlib import Path
import signal
import subprocess
import sys
import tempfile
from typing import Any, Mapping, Optional, Sequence

from scripts.function_tracer_pcode.authority.contracts import authority_digest, canonical_value
from scripts.function_tracer_pcode.authority.process.supervisor import (
    CheckpointState,
    DurableCheckpointStore,
    ProcessSupervisorAuthorityFactory,
)
from scripts.function_tracer_pcode.authority.decision.canonical_result import (
    BUNDLE_KIND,
    RESULT_ENVELOPE_FILE,
    SupervisorCanonicalResultResolvedReceipt,
    validate_durable_child_returncode_observation,
    validate_canonical_result_finalization_bundle,
)


COMMAND_SCHEMA = "unknown-taxonomy-v2-process-supervisor-command-v1"
CHILD_ENV_ROOT = "UNKNOWN_TAXONOMY_V2_SUPERVISOR_ROOT"
CHILD_ENV_NONCE = "UNKNOWN_TAXONOMY_V2_EXECUTION_NONCE"
CHILD_ENV_LAUNCH = "UNKNOWN_TAXONOMY_V2_LAUNCH_PATH"
CHILD_ENV_SUPERVISOR_KEY_ID = "UNKNOWN_TAXONOMY_V2_SUPERVISOR_KEY_ID"
CHILD_ENV_SUPERVISOR_KEY_FILE = "UNKNOWN_TAXONOMY_V2_SUPERVISOR_KEY_FILE"
CHILD_ENV_WORKER_KEY_ID = "UNKNOWN_TAXONOMY_V2_WORKER_KEY_ID"
CHILD_ENV_WORKER_KEY_FILE = "UNKNOWN_TAXONOMY_V2_WORKER_KEY_FILE"


def _exact_string(name: str, value: Any) -> str:
    if type(value) is not str or not value:
        raise TypeError(f"{name} must be a non-empty exact string")
    return value


def read_process_start_token(pid: int, *, proc_root: Path = Path("/proc")) -> str:
    if type(pid) is not int or pid <= 0:
        raise TypeError("process PID is invalid")
    try:
        stat = (proc_root / str(pid) / "stat").read_text(encoding="utf-8")
        closing = stat.rfind(")")
        fields_after_comm = stat[closing + 2:].split()
        start_time = fields_after_comm[19]
    except Exception as exc:
        raise ValueError("process start token is unavailable") from exc
    if not start_time.isascii() or not start_time.isdecimal():
        raise ValueError("process start token is not canonical")
    return f"linux-proc-starttime-{start_time}"


def _read_key(path: Path) -> bytes:
    try:
        key = Path(path).read_bytes()
    except Exception as exc:
        raise ValueError("deployment signing key is unavailable") from exc
    if len(key) < 32:
        raise ValueError("deployment signing key is shorter than 32 bytes")
    return key


@dataclass(frozen=True)
class SupervisorCommandConfig:
    checkpoint_root: Path
    authority_output: Path
    working_directory: Path
    execution_nonce: str
    result_occurrence_id: str
    source_snapshot_fingerprint: str
    stream_id: str
    deadline_policy_digest: str
    supervisor_signing_key_id: str
    supervisor_signing_key_file: Path
    worker_signing_key_id: str
    worker_signing_key_file: Path
    timeout_seconds: float
    kill_grace_seconds: float
    child_command: tuple[str, ...]
    allow_child_exit_resolution: bool = False

    def __post_init__(self) -> None:
        for name in (
            "execution_nonce", "result_occurrence_id",
            "source_snapshot_fingerprint", "stream_id",
            "deadline_policy_digest", "supervisor_signing_key_id",
            "worker_signing_key_id",
        ):
            _exact_string(name, getattr(self, name))
        if (
            type(self.timeout_seconds) not in {int, float}
            or self.timeout_seconds <= 0
            or type(self.kill_grace_seconds) not in {int, float}
            or self.kill_grace_seconds < 0
        ):
            raise TypeError("process deadline/grace is invalid")
        if type(self.allow_child_exit_resolution) is not bool:
            raise TypeError("child exit resolution mode must be exact bool")
        if (
            type(self.child_command) is not tuple
            or not self.child_command
            or not all(type(item) is str and item for item in self.child_command)
        ):
            raise TypeError("child command must be a non-empty exact tuple")
        if self.supervisor_signing_key_id == self.worker_signing_key_id:
            raise ValueError("worker and supervisor signing key IDs must differ")

    @property
    def manifest_entry_preimage_digest(self) -> str:
        return authority_digest({
            "schema": COMMAND_SCHEMA,
            "result_occurrence_id": self.result_occurrence_id,
            "source_snapshot_fingerprint": self.source_snapshot_fingerprint,
            "stream_id": self.stream_id,
            "execution_nonce": self.execution_nonce,
            "deadline_policy_digest": self.deadline_policy_digest,
            "allow_child_exit_resolution": self.allow_child_exit_resolution,
            "working_directory": str(self.working_directory.resolve()),
            "child_command": canonical_value(self.child_command),
        })


class ProcessSupervisorCommand:
    def __init__(self, config: SupervisorCommandConfig) -> None:
        if type(config) is not SupervisorCommandConfig:
            raise TypeError("process supervisor requires exact command config")
        self.config = config
        worker_key = _read_key(config.worker_signing_key_file)
        from scripts.function_tracer_pcode.authority.lifecycle.execution_authority import (
            activate_process_worker_execution_authority_deployment,
        )

        self.execution_authority_startup_receipt = (
            activate_process_worker_execution_authority_deployment(
                key_id=config.worker_signing_key_id,
                key=worker_key,
                key_source_id=str(config.worker_signing_key_file.resolve()),
            )
        )
        self.factory = ProcessSupervisorAuthorityFactory(
            supervisor_signing_key_id=config.supervisor_signing_key_id,
            supervisor_signing_key=_read_key(config.supervisor_signing_key_file),
            worker_signing_key_id=config.worker_signing_key_id,
            worker_signing_key=worker_key,
        )
        self.store = DurableCheckpointStore(
            config.checkpoint_root, self.factory, config.execution_nonce
        )

    def _durable_terminal_projection(
        self, launch: Any, bundle: Any, *, status: str,
        child_returncode: Any,
    ) -> dict[str, Any]:
        from scripts.function_tracer_pcode.authority.contracts import Outcome

        outcome = Outcome.TIMEOUT if status == "TIMEOUT" else Outcome.ERROR
        error_kind = bundle.error_kind if outcome is Outcome.ERROR else None
        validated = self.factory._validate_supervisor_canonical_bundle(
            bundle.canonical_result_bundle,
            launch=launch,
            outcome=outcome,
            error_kind=error_kind,
        )
        canonical = bundle.canonical_result_bundle
        occurrence = canonical["result_entry_occurrence_receipt"]
        identity = validated["execution_identity"]
        observation_kind = (
            "LIVE_PROCESS_WAIT" if child_returncode is not None
            else "DURABLE_RESTART_NO_CHILD_STATUS"
        )
        validate_durable_child_returncode_observation(
            child_exit_disposition=bundle.child_exit_disposition,
            child_returncode=child_returncode,
            observation_kind=observation_kind,
        )
        return {
            "status": status,
            "authority_kind": type(bundle).__name__,
            "supervisor_authority_kind": type(bundle).__name__,
            "supervisor_final_authority_digest": bundle.bundle_digest,
            "launch_receipt_digest": launch.receipt_digest,
            "finalization_bundle_digest": bundle.bundle_digest,
            "event_stream_authority_digest": (
                bundle.composite_stream_authority_digest
            ),
            "canonical_outcome": validated["outcome"],
            "decision_receipt_digest": validated["decision_receipt_digest"],
            "result_occurrence_id": identity["result_occurrence_id"],
            "result_entry_occurrence_receipt_digest": occurrence[
                "receipt_digest"
            ],
            "execution_identity_digest": identity[
                "execution_identity_digest"
            ],
            "stream_id": identity["stream_id"],
            "source_snapshot_fingerprint": identity[
                "source_snapshot_fingerprint"
            ],
            "canonical_result_bundle_digest": validated["bundle_digest"],
            "canonical_result_bundle_kind": "CanonicalResultFinalizationBundle",
            "canonical_result_payload_preimage_digest": validated[
                "payload_preimage_digest"
            ],
            "semantic_projection_digest": validated[
                "semantic_projection_digest"
            ],
            "error_kind": error_kind,
            "child_exit_disposition": bundle.child_exit_disposition,
            "child_returncode_observation_kind": observation_kind,
            "child_returncode": child_returncode,
            "classification_valid": True,
        }

    def _child_environment(self) -> dict[str, str]:
        environment = dict(os.environ)
        environment.update({
            CHILD_ENV_ROOT: str(self.config.checkpoint_root.resolve()),
            CHILD_ENV_NONCE: self.config.execution_nonce,
            CHILD_ENV_LAUNCH: str((self.store.directory / "launch.json").resolve()),
            CHILD_ENV_SUPERVISOR_KEY_ID: self.config.supervisor_signing_key_id,
            CHILD_ENV_SUPERVISOR_KEY_FILE: str(
                self.config.supervisor_signing_key_file.resolve()
            ),
            CHILD_ENV_WORKER_KEY_ID: self.config.worker_signing_key_id,
            CHILD_ENV_WORKER_KEY_FILE: str(
                self.config.worker_signing_key_file.resolve()
            ),
        })
        return environment

    @staticmethod
    def _barrier_command(read_fd: int, child_command: Sequence[str]) -> tuple[str, ...]:
        return (
            sys.executable, "-m",
            "scripts.function_tracer_pcode.authority.process.supervisor_command",
            "_barrier", str(read_fd), "--", *child_command,
        )

    def _write_projection(self, payload: Mapping[str, Any]) -> None:
        body = dict(payload)
        body["projection_schema"] = COMMAND_SCHEMA
        body["projection_digest"] = authority_digest(body)
        path = self.config.authority_output
        path.parent.mkdir(parents=True, exist_ok=True)
        fd, temporary = tempfile.mkstemp(prefix=".supervisor-", dir=str(path.parent))
        try:
            with os.fdopen(fd, "w", encoding="utf-8") as handle:
                json.dump(body, handle, sort_keys=True, separators=(",", ":"))
                handle.write("\n")
                handle.flush()
                os.fsync(handle.fileno())
            os.replace(temporary, path)
            directory_fd = os.open(path.parent, os.O_RDONLY)
            try:
                os.fsync(directory_fd)
            finally:
                os.close(directory_fd)
        finally:
            if os.path.exists(temporary):
                os.unlink(temporary)

    def _write_canonical_resolved_receipt(
        self, receipt: SupervisorCanonicalResultResolvedReceipt
    ) -> None:
        receipt.validate()
        path = self.store.directory / "canonical-resolved-receipt.json"
        payload = {
            name: getattr(receipt, name) for name in receipt.__dataclass_fields__
        }
        fd, temporary = tempfile.mkstemp(
            prefix=".canonical-resolved-", dir=str(path.parent)
        )
        try:
            with os.fdopen(fd, "w", encoding="utf-8") as handle:
                json.dump(payload, handle, sort_keys=True, separators=(",", ":"))
                handle.write("\n")
                handle.flush()
                os.fsync(handle.fileno())
            os.replace(temporary, path)
        finally:
            if os.path.exists(temporary):
                os.unlink(temporary)

    def _load_canonical_child_result(
        self, launch: Any, child_returncode: int,
    ) -> tuple[SupervisorCanonicalResultResolvedReceipt, dict[str, Any]]:
        from scripts.function_tracer_pcode.authority.decision.production_cutover import (
            CLI_EXIT_MATRIX,
        )
        from scripts.function_tracer_pcode.authority.contracts import Outcome

        path = self.store.directory / RESULT_ENVELOPE_FILE
        envelope = json.loads(path.read_text(encoding="utf-8"))
        if set(envelope) != {
            "schema", "canonical_result_payload",
            "canonical_result_bundle_digest", "envelope_digest",
        }:
            raise ValueError("canonical result envelope fields differ")
        envelope_body = {
            key: value for key, value in envelope.items()
            if key != "envelope_digest"
        }
        if (
            envelope["schema"] != "canonical-result-envelope-v1"
            or authority_digest(envelope_body) != envelope["envelope_digest"]
        ):
            raise ValueError("canonical result envelope seal is invalid")
        payload = envelope["canonical_result_payload"]
        bundle = payload["canonical_result_finalization_bundle"]
        preimage = {
            key: value for key, value in payload.items()
            if key != "canonical_result_finalization_bundle"
        }
        validated = validate_canonical_result_finalization_bundle(
            bundle,
            result_payload_preimage=preimage,
            bundle_verification_key_id=self.config.supervisor_signing_key_id,
            bundle_verification_key=_read_key(
                self.config.supervisor_signing_key_file
            ),
        )
        identity = validated["execution_identity"]
        outcome = Outcome(validated["outcome"])
        if (
            bundle["bundle_digest"]
            != envelope["canonical_result_bundle_digest"]
            or identity["result_occurrence_id"]
            != self.config.result_occurrence_id
            or identity["source_snapshot_fingerprint"]
            != self.config.source_snapshot_fingerprint
            or identity["stream_id"] != self.config.stream_id
            or launch.payload["result_occurrence_id"]
            != identity["result_occurrence_id"]
            or launch.payload["source_snapshot_fingerprint"]
            != identity["source_snapshot_fingerprint"]
            or launch.payload["stream_id"] != identity["stream_id"]
            or child_returncode != CLI_EXIT_MATRIX[outcome]
        ):
            raise ValueError("canonical child result does not join launch/exit")
        receipt = SupervisorCanonicalResultResolvedReceipt.create(
            launch_receipt_digest=launch.receipt_digest,
            result_occurrence_id=identity["result_occurrence_id"],
            execution_identity_digest=identity["execution_identity_digest"],
            child_returncode=child_returncode,
            canonical_result_bundle_digest=validated["bundle_digest"],
            payload_preimage_digest=validated["payload_preimage_digest"],
            decision_receipt_digest=validated["decision_receipt_digest"],
        )
        receipt.validate()
        occurrence = bundle.get("result_entry_occurrence_receipt") or {}
        semantic = bundle["canonical_semantic_result_projection"]
        error_kind = semantic["payload"].get("error_kind")
        projection = {
            "status": "RESOLVED",
            "authority_kind": type(receipt).__name__,
            "supervisor_authority_kind": type(receipt).__name__,
            "supervisor_final_authority_digest": receipt.receipt_digest,
            "launch_receipt_digest": launch.receipt_digest,
            "canonical_outcome": outcome.value,
            "decision_receipt_digest": validated["decision_receipt_digest"],
            "result_occurrence_id": identity["result_occurrence_id"],
            "result_entry_occurrence_receipt_digest": occurrence.get(
                "receipt_digest"
            ),
            "execution_identity_digest": identity["execution_identity_digest"],
            "stream_id": identity["stream_id"],
            "source_snapshot_fingerprint": identity[
                "source_snapshot_fingerprint"
            ],
            "canonical_result_bundle_digest": validated["bundle_digest"],
            "canonical_result_bundle_kind": BUNDLE_KIND,
            "canonical_result_payload_preimage_digest": validated[
                "payload_preimage_digest"
            ],
            "semantic_projection_digest": validated[
                "semantic_projection_digest"
            ],
            "error_kind": error_kind,
            "child_returncode": child_returncode,
            "classification_valid": True,
        }
        return receipt, projection

    def _same_process(self, process: subprocess.Popen[Any], start_token: str) -> bool:
        try:
            return read_process_start_token(process.pid) == start_token
        except ValueError:
            return process.poll() is not None

    @staticmethod
    def _resolved_projection(launch: Any, state: Any, returncode: Any) -> dict[str, Any]:
        return {
            "status": "RESOLVED",
            "authority_kind": state.receipt_kind,
            "launch_receipt_digest": launch.receipt_digest,
            "finalization_bundle_digest": state.receipt_digest,
            "child_returncode": returncode,
        }

    @staticmethod
    def _invalid_projection(launch: Any, error_code: str) -> dict[str, Any]:
        return {
            "status": "INVALID",
            "authority_kind": "InvalidSupervisorCommandProjection",
            "launch_receipt_digest": launch.receipt_digest,
            "error_code": error_code,
            "child_returncode": None,
        }

    def _terminate_exact_process_group(
        self, process: subprocess.Popen[Any], start_token: str,
    ) -> str:
        if process.poll() is not None:
            return f"EXITED_{process.returncode}"
        if not self._same_process(process, start_token):
            raise ValueError("child PID/start-token identity changed before kill")
        if process.poll() is not None:
            return f"EXITED_{process.returncode}"
        try:
            os.killpg(process.pid, signal.SIGTERM)
        except ProcessLookupError:
            return_code = process.poll()
            if return_code is not None:
                return f"EXITED_{return_code}_BEFORE_SIGTERM"
            raise
        try:
            process.wait(timeout=self.config.kill_grace_seconds)
            return (
                "SIGTERM_AFTER_DEADLINE"
                if process.returncode == -signal.SIGTERM
                else f"EXITED_{process.returncode}_AFTER_SIGTERM"
            )
        except subprocess.TimeoutExpired:
            if not self._same_process(process, start_token):
                raise ValueError("child PID/start-token identity changed before SIGKILL")
            if process.poll() is not None:
                return f"EXITED_{process.returncode}_BEFORE_SIGKILL"
            try:
                os.killpg(process.pid, signal.SIGKILL)
            except ProcessLookupError:
                return_code = process.poll()
                if return_code is not None:
                    return f"EXITED_{return_code}_BEFORE_SIGKILL"
                raise
            process.wait()
            return (
                "SIGKILL_AFTER_DEADLINE"
                if process.returncode == -signal.SIGKILL
                else f"EXITED_{process.returncode}_AFTER_SIGKILL"
            )

    def _cleanup_exact_process_group(
        self, process: subprocess.Popen[Any], start_token: Optional[str],
    ) -> str:
        """Best-effort cleanup that never signals an unverified/reused PID."""
        return_code = process.poll()
        if return_code is not None:
            return f"EXITED_{return_code}"
        if start_token is None or not self._same_process(process, start_token):
            return "SKIPPED_UNVERIFIED_PROCESS_IDENTITY"
        return_code = process.poll()
        if return_code is not None:
            return f"EXITED_{return_code}_BEFORE_CLEANUP_SIGKILL"
        try:
            os.killpg(process.pid, signal.SIGKILL)
        except ProcessLookupError:
            return_code = process.poll()
            return (
                f"EXITED_{return_code}_BEFORE_CLEANUP_SIGKILL"
                if return_code is not None
                else "PROCESS_LOOKUP_RACE_DURING_CLEANUP"
            )
        process.wait()
        return "SIGKILL_DURING_EXCEPTION_CLEANUP"

    def _finalize_claimed(
        self, *, launch: Any, claimed: Any, prefix: Any,
        child_returncode: Any,
    ) -> dict[str, Any]:
        timeout, segment = self.factory.issue_supervisor_timeout(
            claimed=claimed, prefix=prefix,
        )
        final = self.store.finalize_timeout(
            claimed=claimed, timeout=timeout, segment=segment, prefix=prefix,
        )
        bundle = self.factory.issue_timeout_bundle(
            launch=launch,
            checkpoint=self.factory.decode(json.loads(
                (self.store.directory / "checkpoint.json").read_text(encoding="utf-8")
            )),
            claimed=claimed, timeout=timeout, segment=segment,
            final_transition=final, prefix=prefix,
        )
        return self._durable_terminal_projection(
            launch, bundle, status="TIMEOUT",
            child_returncode=child_returncode,
        )

    def _recover_durable_state(
        self, *, launch: Any, state: Any, child_returncode: Any,
        allow_active_timeout: bool = False,
        kill_disposition: Optional[str] = None,
    ) -> tuple[int, dict[str, Any]]:
        state_value = CheckpointState(state.payload["state"])
        if state_value is CheckpointState.RESOLVED:
            prefix = self.store.rematerialize_active_prefix()
            resolved = self.store.rematerialize_resolved_state(prefix=prefix)
            return 0, self._resolved_projection(
                launch, resolved, child_returncode
            )
        prefix = self.store.rematerialize_active_prefix()
        if state_value is CheckpointState.COMPLETION_READY:
            resolved = self.store.recover_completion_ready(
                ready=state, prefix=prefix,
            )
            return 0, self._resolved_projection(launch, resolved, child_returncode)
        if state_value is CheckpointState.TIMED_OUT_CLAIMED:
            return 124, self._finalize_claimed(
                launch=launch, claimed=state, prefix=prefix,
                child_returncode=child_returncode,
            )
        if state_value is CheckpointState.TIMED_OUT:
            bundle = self.store.rematerialize_timeout_bundle(prefix=prefix)
            return 124, self._durable_terminal_projection(
                launch, bundle, status="TIMEOUT",
                child_returncode=child_returncode,
            )
        if state_value is CheckpointState.ACTIVE and allow_active_timeout:
            if type(kill_disposition) is not str or not kill_disposition:
                raise ValueError("ACTIVE deadline recovery lacks kill disposition")
            claimed = self.store.supervisor_claim_timeout(
                active=state, prefix=prefix,
                kill_disposition=kill_disposition,
            )
            if claimed.payload["state"] == CheckpointState.RESOLVED.value:
                return 0, self._resolved_projection(
                    launch, claimed, child_returncode
                )
            return 124, self._finalize_claimed(
                launch=launch, claimed=claimed, prefix=prefix,
                child_returncode=child_returncode,
            )
        return 2, self._invalid_projection(
            launch, "NONFINAL_ACTIVE_WITHOUT_DEADLINE_AUTHORITY"
        )

    def _finalize_deadline(
        self, *, launch: Any, process: subprocess.Popen[Any], start_token: str,
    ) -> tuple[int, dict[str, Any]]:
        kill_disposition = self._terminate_exact_process_group(process, start_token)
        recovered_pending = self.store.recover_pending_active_commit()
        state_path = self.store.directory / "state.json"
        state = (
            recovered_pending[0]
            if recovered_pending is not None
            else self.store.read_state() if state_path.exists() else None
        )
        if state is None or CheckpointState(
            state.payload["state"]
        ) is CheckpointState.RESOLVED:
            checkpoint, prefix = self.factory.issue_deadline_bootstrap_checkpoint(
                launch=launch, prior_resolved=state,
            )
            self.store.persist_active(checkpoint, prefix)
            state = checkpoint
        return self._recover_durable_state(
            launch=launch, state=state, child_returncode=process.returncode,
            allow_active_timeout=True, kill_disposition=kill_disposition,
        )

    def _load_durable_launch(self) -> Any:
        launch = self.factory.decode(json.loads(
            (self.store.directory / "launch.json").read_text(encoding="utf-8")
        ))
        if (
            launch.payload["result_occurrence_id"]
            != self.config.result_occurrence_id
            or launch.payload["manifest_entry_preimage_digest"]
            != self.config.manifest_entry_preimage_digest
            or launch.payload["execution_nonce"] != self.config.execution_nonce
            or launch.payload["stream_id"] != self.config.stream_id
            or launch.payload["source_snapshot_fingerprint"]
            != self.config.source_snapshot_fingerprint
            or launch.payload["deadline_policy_digest"]
            != self.config.deadline_policy_digest
        ):
            raise ValueError("durable launch differs from supervisor command config")
        return launch

    def _resume(self) -> int:
        launch = self._load_durable_launch()
        try:
            self.store.recover_pending_active_commit()
            canonical_receipt_path = (
                self.store.directory / "canonical-resolved-receipt.json"
            )
            canonical_envelope_path = self.store.directory / RESULT_ENVELOPE_FILE
            if canonical_receipt_path.exists() and canonical_envelope_path.exists():
                stored = json.loads(canonical_receipt_path.read_text(encoding="utf-8"))
                child_returncode = stored["child_returncode"]
                receipt, projection = self._load_canonical_child_result(
                    launch, child_returncode
                )
                if receipt.receipt_digest != stored["receipt_digest"]:
                    raise ValueError("persisted canonical resolved receipt drifted")
                self._write_projection(projection)
                return 0
            if (self.store.directory / "child-exit.json").exists():
                resolved = self.store.rematerialize_child_exit_resolution()
                projection = self._resolved_projection(
                    launch, resolved, resolved.payload["child_returncode"]
                )
                self._write_projection(projection)
                return 0
            if (self.store.directory / "operational-error-bundle.json").exists():
                bundle = self.store.rematerialize_operational_error_bundle()
                if bundle.launch_receipt_digest != launch.receipt_digest:
                    raise ValueError("durable ERROR bundle differs from launch")
                projection = self._durable_terminal_projection(
                    launch, bundle, status="ERROR", child_returncode=None
                )
                self._write_projection(projection)
                return 2
            state = self.store.read_state()
            exit_code, projection = self._recover_durable_state(
                launch=launch, state=state, child_returncode=None,
            )
        except Exception:
            projection = self._invalid_projection(
                launch, "DURABLE_RESTART_AUTHORITY_INVALID"
            )
            exit_code = 2
        self._write_projection(projection)
        return exit_code

    def run(self) -> int:
        if (self.store.directory / "launch.json").exists():
            return self._resume()
        read_fd, write_fd = os.pipe()
        process: Optional[subprocess.Popen[Any]] = None
        launch: Any = None
        start_token: Optional[str] = None
        try:
            process = subprocess.Popen(
                self._barrier_command(read_fd, self.config.child_command),
                cwd=self.config.working_directory,
                env=self._child_environment(),
                pass_fds=(read_fd,),
                start_new_session=True,
            )
            os.close(read_fd)
            read_fd = -1
            start_token = read_process_start_token(process.pid)
            launch = self.factory.issue_launch(
                result_occurrence_id=self.config.result_occurrence_id,
                manifest_entry_preimage_digest=(
                    self.config.manifest_entry_preimage_digest
                ),
                execution_nonce=self.config.execution_nonce,
                child_pid=process.pid,
                child_start_token=start_token,
                stream_id=self.config.stream_id,
                source_snapshot_fingerprint=(
                    self.config.source_snapshot_fingerprint
                ),
                deadline_policy_digest=self.config.deadline_policy_digest,
            )
            self.store.persist_launch(launch)
            os.write(write_fd, b"1")
            os.close(write_fd)
            write_fd = -1
            try:
                return_code = process.wait(timeout=self.config.timeout_seconds)
            except subprocess.TimeoutExpired:
                exit_code, projection = self._finalize_deadline(
                    launch=launch, process=process, start_token=start_token
                )
            else:
                state_path = self.store.directory / "state.json"
                canonical_envelope_path = (
                    self.store.directory / RESULT_ENVELOPE_FILE
                )
                if (
                    self.config.allow_child_exit_resolution
                    and canonical_envelope_path.exists()
                ):
                    try:
                        resolved, projection = self._load_canonical_child_result(
                            launch, return_code
                        )
                    except Exception:
                        projection = self._invalid_projection(
                            launch, "CANONICAL_CHILD_RESULT_INVALID"
                        )
                        projection["child_returncode"] = return_code
                        exit_code = 2
                    else:
                        self._write_canonical_resolved_receipt(resolved)
                        exit_code = 0
                elif state_path.exists():
                    state = self.store.read_state()
                    exit_code, projection = self._recover_durable_state(
                        launch=launch, state=state,
                        child_returncode=return_code,
                    )
                elif self.config.allow_child_exit_resolution:
                    try:
                        resolved, projection = self._load_canonical_child_result(
                            launch, return_code
                        )
                    except Exception:
                        projection = self._invalid_projection(
                            launch, "CANONICAL_CHILD_RESULT_INVALID"
                        )
                        projection["child_returncode"] = return_code
                        exit_code = 2
                    else:
                        self._write_canonical_resolved_receipt(resolved)
                        exit_code = 0
                else:
                    bundle = self.store.supervisor_finalize_operational_error(
                        launch=launch,
                        error_kind="operational_authority_invalid",
                        deadline_stage="BEFORE_CHECKPOINT",
                        child_exit_disposition=f"EXIT_CODE_{return_code}",
                    )
                    projection = self._durable_terminal_projection(
                        launch, bundle, status="ERROR",
                        child_returncode=return_code,
                    )
                    exit_code = return_code if return_code else 2
            self._write_projection(projection)
            return exit_code
        except Exception:
            if launch is not None:
                return self._resume()
            raise
        finally:
            for descriptor in (read_fd, write_fd):
                if descriptor >= 0:
                    os.close(descriptor)
            if process is not None and process.poll() is None:
                self._cleanup_exact_process_group(process, start_token)


def _barrier_main(arguments: Sequence[str]) -> int:
    if len(arguments) < 3 or arguments[1] != "--":
        raise ValueError("worker barrier arguments are invalid")
    descriptor = int(arguments[0])
    token = os.read(descriptor, 1)
    os.close(descriptor)
    if token != b"1":
        raise ValueError("worker barrier release authority is invalid")
    os.execvpe(arguments[2], tuple(arguments[2:]), os.environ)
    raise AssertionError("exec returned unexpectedly")


def _parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--checkpoint-root", required=True)
    parser.add_argument("--authority-output", required=True)
    parser.add_argument("--working-directory", required=True)
    parser.add_argument("--execution-nonce", required=True)
    parser.add_argument("--result-occurrence-id", required=True)
    parser.add_argument("--source-snapshot-fingerprint", required=True)
    parser.add_argument("--stream-id", required=True)
    parser.add_argument("--deadline-policy-digest", required=True)
    parser.add_argument("--supervisor-signing-key-id", required=True)
    parser.add_argument("--supervisor-signing-key-file", required=True)
    parser.add_argument("--worker-signing-key-id", required=True)
    parser.add_argument("--worker-signing-key-file", required=True)
    parser.add_argument("--timeout-seconds", required=True, type=float)
    parser.add_argument("--kill-grace-seconds", type=float, default=30.0)
    parser.add_argument("--allow-child-exit-resolution", action="store_true")
    parser.add_argument("child_command", nargs=argparse.REMAINDER)
    return parser


def main(arguments: Optional[Sequence[str]] = None) -> int:
    values = tuple(sys.argv[1:] if arguments is None else arguments)
    if values and values[0] == "_barrier":
        return _barrier_main(values[1:])
    args = _parser().parse_args(values)
    child_command = tuple(args.child_command)
    if child_command and child_command[0] == "--":
        child_command = child_command[1:]
    config = SupervisorCommandConfig(
        checkpoint_root=Path(args.checkpoint_root),
        authority_output=Path(args.authority_output),
        working_directory=Path(args.working_directory),
        execution_nonce=args.execution_nonce,
        result_occurrence_id=args.result_occurrence_id,
        source_snapshot_fingerprint=args.source_snapshot_fingerprint,
        stream_id=args.stream_id,
        deadline_policy_digest=args.deadline_policy_digest,
        supervisor_signing_key_id=args.supervisor_signing_key_id,
        supervisor_signing_key_file=Path(args.supervisor_signing_key_file),
        worker_signing_key_id=args.worker_signing_key_id,
        worker_signing_key_file=Path(args.worker_signing_key_file),
        timeout_seconds=args.timeout_seconds,
        kill_grace_seconds=args.kill_grace_seconds,
        allow_child_exit_resolution=args.allow_child_exit_resolution,
        child_command=child_command,
    )
    return ProcessSupervisorCommand(config).run()


if __name__ == "__main__":
    raise SystemExit(main())
