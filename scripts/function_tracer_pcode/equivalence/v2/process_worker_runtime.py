"""Worker-side durable checkpoint lifecycle for brokered decompilation."""

from __future__ import annotations

from dataclasses import dataclass
import json
import os
from pathlib import Path
from typing import Any, Mapping, Optional

from .contracts import authority_digest
from .process_supervisor import (
    DurableCheckpointStore,
    ProcessSupervisorAuthorityFactory,
)
from .process_supervisor_command import (
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


_WORKER_ENVIRONMENT_KEYS = (
    CHILD_ENV_ROOT,
    CHILD_ENV_NONCE,
    CHILD_ENV_LAUNCH,
    CHILD_ENV_SUPERVISOR_KEY_ID,
    CHILD_ENV_SUPERVISOR_KEY_FILE,
    CHILD_ENV_WORKER_KEY_ID,
    CHILD_ENV_WORKER_KEY_FILE,
)
PROCESS_WORKER_RUNTIME_DISABLED_ENV = (
    "UNKNOWN_TAXONOMY_V2_DISABLE_PROCESS_WORKER_RUNTIME"
)
_PREPARED_TOKEN = object()
_ACTIVE_TOKEN = object()
_RUNTIME_TOKEN = object()


class CanonicalCensusInvalid(ValueError):
    """A supervisor diagnostic projection cannot become a canonical outcome."""


def require_canonical_supervisor_projection(
    payload: Mapping[str, Any],
) -> Mapping[str, Any]:
    """Validate command projection; diagnostic INVALID always invalidates census."""
    if type(payload) is not dict or payload.get("projection_schema") != COMMAND_SCHEMA:
        raise CanonicalCensusInvalid("supervisor projection schema is invalid")
    body = dict(payload)
    digest = body.pop("projection_digest", None)
    if type(digest) is not str or digest != authority_digest(body):
        raise CanonicalCensusInvalid("supervisor projection digest is invalid")
    if (
        body.get("status") == "INVALID"
        or body.get("authority_kind") == "InvalidSupervisorCommandProjection"
    ):
        raise CanonicalCensusInvalid(
            "diagnostic supervisor INVALID makes canonical census INVALID"
        )
    expected = {
        "ERROR": "DurableErrorFinalizationBundle",
        "TIMEOUT": "DurableTimeoutFinalizationBundle",
        "RESOLVED": {
            "CheckpointStateTransitionReceipt", "SupervisorChildExitReceipt",
        },
    }
    expected_kind = expected.get(body.get("status"))
    if (
        body.get("authority_kind") not in expected_kind
        if isinstance(expected_kind, set)
        else expected_kind != body.get("authority_kind")
    ):
        raise CanonicalCensusInvalid("supervisor projection status/authority differs")
    required = {
        "ERROR": {
            "status", "authority_kind", "launch_receipt_digest",
            "finalization_bundle_digest", "event_stream_authority_digest",
            "child_returncode", "projection_schema",
        },
        "TIMEOUT": {
            "status", "authority_kind", "launch_receipt_digest",
            "finalization_bundle_digest", "event_stream_authority_digest",
            "proof_requirement_id", "child_returncode", "projection_schema",
        },
        "RESOLVED": {
            "status", "authority_kind", "launch_receipt_digest",
            "finalization_bundle_digest", "child_returncode",
            "projection_schema",
        },
    }[body["status"]]
    if set(body) != required or any(
        type(body[name]) is not str or not body[name]
        for name in required
        if name not in {"child_returncode"}
    ):
        raise CanonicalCensusInvalid("supervisor projection authority is incomplete")
    if (
        body["child_returncode"] is not None
        and type(body["child_returncode"]) is not int
    ):
        raise CanonicalCensusInvalid("supervisor child return code is invalid")
    return payload


@dataclass(frozen=True)
class PreparedWorkerCheckpoint:
    runtime: "ProcessWorkerRuntime"
    session: Any
    operational_factory: Any
    prefix: Any
    projection: Any
    assignment: Any
    assignment_factory: Any
    subordinate: bool
    _token: object

    def persist(self, invocation: Any) -> "ActiveWorkerCheckpoint":
        if self._token is not _PREPARED_TOKEN:
            raise TypeError("prepared worker checkpoint is not runtime issued")
        assigned_requirement = (
            self.assignment.proof_requirement_id
            if self.subordinate
            else self.assignment.payload["proof_requirement_id"]
        )
        if invocation.proof_requirement_id != assigned_requirement:
            raise ValueError("worker invocation differs from live assignment")
        issue = (
            self.runtime.process_factory.issue_subordinate_active_checkpoint
            if self.subordinate
            else self.runtime.process_factory.issue_active_checkpoint
        )
        arguments = {
            "launch": self.runtime.launch,
            "prefix": self.prefix,
            "projection": self.projection,
            "assignment": self.assignment,
            "invocation": invocation,
            "operational_factory": self.operational_factory,
            "worker_pid": os.getpid(),
            "worker_start_token": self.runtime.worker_start_token,
        }
        if self.subordinate:
            arguments["assignment_factory"] = self.assignment_factory
        checkpoint = issue(**arguments)
        self.runtime.store.persist_active(checkpoint, self.prefix)
        active = ActiveWorkerCheckpoint(
            runtime=self.runtime, session=self.session,
            operational_factory=self.operational_factory,
            prefix=self.prefix, projection=self.projection,
            assignment=self.assignment,
            assignment_factory=self.assignment_factory,
            subordinate=self.subordinate, invocation=invocation,
            checkpoint=checkpoint, _token=_ACTIVE_TOKEN,
        )
        self.session.domain_signal_state.setdefault(
            "process_worker_checkpoint_records", []
        ).append(active)
        return active


@dataclass(frozen=True)
class ActiveWorkerCheckpoint:
    runtime: "ProcessWorkerRuntime"
    session: Any
    operational_factory: Any
    prefix: Any
    projection: Any
    assignment: Any
    assignment_factory: Any
    subordinate: bool
    invocation: Any
    checkpoint: Any
    _token: object

    def resolve(
        self, *, attempt: Any = None, completed_artifact: Any = None,
        error_artifact: Any = None, subordinate_execution: Any = None,
    ) -> Any:
        if self._token is not _ACTIVE_TOKEN:
            raise TypeError("ACTIVE worker checkpoint is not runtime issued")
        continuation_stream = self.session.recorder.prefix_view().to_sealed_stream()
        continuation = self.runtime.process_factory.issue_worker_continuation(
            checkpoint=self.checkpoint,
            prefix=self.prefix,
            continuation_stream=continuation_stream,
            operational_factory=self.operational_factory,
            attempt=attempt,
            completed_artifact=completed_artifact,
            error_artifact=error_artifact,
            subordinate_execution=subordinate_execution,
            subordinate_assignment=(self.assignment if self.subordinate else None),
            subordinate_assignment_factory=(
                self.assignment_factory if self.subordinate else None
            ),
            subordinate_projection=(self.projection if self.subordinate else None),
            subordinate_invocation=(self.invocation if self.subordinate else None),
        )
        _ready, resolved = self.runtime.store.worker_publish_completion(
            active=self.checkpoint,
            continuation=continuation,
            prefix=self.prefix,
            continuation_stream=continuation_stream,
        )
        return resolved


class ProcessWorkerRuntime:
    """Exact child-side decoder and issuer for one supervisor launch."""

    def __init__(
        self, *, process_factory: ProcessSupervisorAuthorityFactory,
        store: DurableCheckpointStore, launch: Any, worker_start_token: str,
        _token: object = None,
    ) -> None:
        if _token is not _RUNTIME_TOKEN:
            raise TypeError("process worker runtime must be authority issued")
        self.process_factory = process_factory
        self.store = store
        self.launch = launch
        self.worker_start_token = worker_start_token

    @classmethod
    def from_environment(cls) -> Optional["ProcessWorkerRuntime"]:
        if os.environ.get(PROCESS_WORKER_RUNTIME_DISABLED_ENV) == "1":
            return None
        present = tuple(key in os.environ for key in _WORKER_ENVIRONMENT_KEYS)
        if not any(present):
            return None
        if not all(present):
            raise ValueError("worker supervisor environment is partial")
        process_factory = ProcessSupervisorAuthorityFactory(
            supervisor_signing_key_id=os.environ[CHILD_ENV_SUPERVISOR_KEY_ID],
            supervisor_signing_key=Path(
                os.environ[CHILD_ENV_SUPERVISOR_KEY_FILE]
            ).read_bytes(),
            worker_signing_key_id=os.environ[CHILD_ENV_WORKER_KEY_ID],
            worker_signing_key=Path(
                os.environ[CHILD_ENV_WORKER_KEY_FILE]
            ).read_bytes(),
        )
        launch = process_factory.decode(json.loads(
            Path(os.environ[CHILD_ENV_LAUNCH]).read_text(encoding="utf-8")
        ))
        start_token = read_process_start_token(os.getpid())
        if (
            launch.payload["child_pid"] != os.getpid()
            or launch.payload["child_start_token"] != start_token
        ):
            raise ValueError("worker process identity differs from supervisor launch")
        store = DurableCheckpointStore(
            Path(os.environ[CHILD_ENV_ROOT]), process_factory,
            os.environ[CHILD_ENV_NONCE],
        )
        return cls(
            process_factory=process_factory, store=store, launch=launch,
            worker_start_token=start_token, _token=_RUNTIME_TOKEN,
        )

    @classmethod
    def for_testing(
        cls, *, process_factory: ProcessSupervisorAuthorityFactory,
        store: DurableCheckpointStore, launch: Any, worker_start_token: str,
    ) -> "ProcessWorkerRuntime":
        return cls(
            process_factory=process_factory, store=store, launch=launch,
            worker_start_token=worker_start_token, _token=_RUNTIME_TOKEN,
        )

    def prepare(
        self, *, session: Any, operational_factory: Any, reason_id: str,
    ) -> PreparedWorkerCheckpoint:
        prefix = session.recorder.prefix_view()
        projection = session.reducer.replay_prefix(prefix)
        if (
            session.identity.result_occurrence_id
            != self.launch.payload["result_occurrence_id"]
            or session.identity.source_snapshot_fingerprint
            != self.launch.payload["source_snapshot_fingerprint"]
            or prefix.stream_id != self.launch.payload["stream_id"]
        ):
            raise ValueError("worker session identity differs from supervisor launch")
        assignment = self.process_factory.issue_live_assignment(
            prefix=prefix, projection=projection, reason_id=reason_id,
        )
        return PreparedWorkerCheckpoint(
            self, session, operational_factory, prefix, projection, assignment,
            None, False, _PREPARED_TOKEN,
        )

    def prepare_subordinate(
        self, *, session: Any, operational_factory: Any,
        assignment: Any, assignment_factory: Any,
        projection: Any, prefix: Any,
    ) -> PreparedWorkerCheckpoint:
        if (
            session.identity.result_occurrence_id
            != self.launch.payload["result_occurrence_id"]
            or session.identity.source_snapshot_fingerprint
            != self.launch.payload["source_snapshot_fingerprint"]
            or prefix.stream_id != self.launch.payload["stream_id"]
        ):
            raise ValueError("worker session identity differs from supervisor launch")
        assignment_factory.validate(assignment, projection, prefix)
        return PreparedWorkerCheckpoint(
            self, session, operational_factory, prefix, projection, assignment,
            assignment_factory, True, _PREPARED_TOKEN,
        )


def runtime_for_session(session: Any) -> Optional[ProcessWorkerRuntime]:
    key = "unknown_taxonomy_v2_process_worker_runtime"
    if key in session.domain_signal_state:
        runtime = session.domain_signal_state[key]
        if runtime is not None and type(runtime) is not ProcessWorkerRuntime:
            raise TypeError("session process worker runtime is invalid")
        return runtime
    runtime = ProcessWorkerRuntime.from_environment()
    session.domain_signal_state[key] = runtime
    return runtime
