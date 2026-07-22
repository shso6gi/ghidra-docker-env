"""Durable decompiler checkpoint, supervisor timeout, and process census authority."""

from __future__ import annotations

from contextlib import contextmanager
from dataclasses import dataclass, field
from enum import Enum
import fcntl
import hashlib
import hmac
import json
import os
from pathlib import Path
import tempfile
from typing import Any, Iterator, Mapping, Optional

from .contracts import (
    CauseOccurrence, CauseOccurrenceAuthority, IdentityScope, Outcome,
    ProofRequirement, ReasonDefinition, RecoveryAddressability,
    RequirementSlotDefinition, SatisfactionContractDefinition,
    VerifiedLifecyclePrefixProjection, authority_digest, requirement_slot,
)
from .stream import (
    CauseObservedEventAuthority,
    EventIntent,
    EventRecorder,
    EventStreamPrefixView,
    EventStreamEnvelope,
    EventType,
    ErrorEventAuthority,
    ProcessCompletionEventAuthority,
    ProcessExecutionEventAuthority,
    SealedEventStream,
)
from .operational_extraction import (
    DecompilationDisposition,
    OPERATIONAL_REASON_REGISTRY,
    OPERATIONAL_RECOVERY_REGISTRY,
    OPERATIONAL_PRODUCER_STAGE_REGISTRY_DIGEST,
)
from .call_effect import CALL_EFFECT_REASON_REGISTRY, CALL_EFFECT_RECOVERY_REGISTRY
from .loop_recurrence import LOOP_REASON_REGISTRY, LOOP_RECOVERY_REGISTRY
from .return_outcome import (
    RETURN_OUTCOME_REASON_REGISTRY,
    RETURN_OUTCOME_RECOVERY_REGISTRY,
)
from .sat_safety import SAT_SAFETY_REASON_REGISTRY, SAT_SAFETY_RECOVERY_REGISTRY
from .abi_width_readonly import (
    ABI_WIDTH_READONLY_REASON_REGISTRY,
    ABI_WIDTH_READONLY_RECOVERY_REGISTRY,
)
from .production_signals import (
    COMPARISON_CLOSURE_REASON_REGISTRY,
    COMPARISON_CLOSURE_RECOVERY_REGISTRY,
)
from .registry import (
    SatisfactionBindingFactory, SealedReasonRegistry, SealedRecoveryRegistry,
    SemanticCauseIdentityFactory,
)
from .subordinate_decompilation import (
    SubordinateProcessAssignmentFactory,
    SubordinateProcessAssignmentReceipt,
    SubordinateProcessExecutionReceipt,
)
from .codecs import StrictV2JsonCodec
from .stream import RequirementCompletedEventAuthority


PROCESS_SUPERVISOR_REGISTRY_ID = "operational-process-supervisor-v1"
PROCESS_SUPERVISOR_REGISTRY_VERSION = 1
PROCESS_SUPERVISOR_ISSUER_ID = "decompiler-process-supervisor-v1"
PROCESS_WORKER_ISSUER_ID = "decompiler-process-runner-v1"
PROCESS_POLICY_ID = "decompiler-deadline-policy-v1"
EMPTY_STREAM_ROOT = "0" * 64
CHECKPOINT_AUTHORITY_FILENAMES = (
    "checkpoint.json",
    "state.json",
    "checkpoint-prefix-stream.json",
    "continuation.json",
    "continuation-stream.json",
    "ready.json",
    "recovery-resolution.json",
    "claimed.json",
    "timeout.json",
    "terminal-segment.json",
    "terminal-stream.json",
    "child-exit.json",
)

_OPERATIONAL_PROCESS_ROWS = {
    "function_decompilation_artifact_unavailable": (
        "function_decompilation_artifact",
        "function-decompilation-artifact-producer-v2",
        190,
    ),
}

PROCESS_COMPLETION_REASON_ID = "pair_process_completion_unavailable"
PROCESS_COMPLETION_PROOF_KIND = "pair_process_completion"
PROCESS_COMPLETION_CONTRACT_ID = "pair-process-completion-recovery"
PROCESS_COMPLETION_REASON_REGISTRY = SealedReasonRegistry.build((
    ReasonDefinition(
        PROCESS_COMPLETION_REASON_ID,
        "process_execution",
        "proof_obligation",
        "blocks_decision",
        frozenset(("pair_process_execution",)),
        ("durable_launch", "deadline_policy", "missing_terminal_result"),
        frozenset((PROCESS_COMPLETION_PROOF_KIND,)),
        True,
        "pair_process_execution_v1",
        RecoveryAddressability.REQUIREMENT_REQUIRED,
    ),
))
PROCESS_COMPLETION_RECOVERY_REGISTRY = SealedRecoveryRegistry.build((
    SatisfactionContractDefinition(
        PROCESS_COMPLETION_CONTRACT_ID,
        1,
        (RequirementSlotDefinition(
            "completion", frozenset((PROCESS_COMPLETION_PROOF_KIND,))
        ),),
        requirement_slot("completion"),
    ),
))

PROCESS_DURABLE_REASON_REGISTRY = SealedReasonRegistry.build((
    *OPERATIONAL_REASON_REGISTRY.snapshot(),
    *CALL_EFFECT_REASON_REGISTRY.snapshot(),
    *LOOP_REASON_REGISTRY.snapshot(),
    *RETURN_OUTCOME_REASON_REGISTRY.snapshot(),
    *SAT_SAFETY_REASON_REGISTRY.snapshot(),
    *ABI_WIDTH_READONLY_REASON_REGISTRY.snapshot(),
    *COMPARISON_CLOSURE_REASON_REGISTRY.snapshot(),
    *PROCESS_COMPLETION_REASON_REGISTRY.snapshot(),
))
PROCESS_DURABLE_RECOVERY_REGISTRY = SealedRecoveryRegistry.build((
    *OPERATIONAL_RECOVERY_REGISTRY.snapshot(),
    *CALL_EFFECT_RECOVERY_REGISTRY.snapshot(),
    *LOOP_RECOVERY_REGISTRY.snapshot(),
    *RETURN_OUTCOME_RECOVERY_REGISTRY.snapshot(),
    *SAT_SAFETY_RECOVERY_REGISTRY.snapshot(),
    *ABI_WIDTH_READONLY_RECOVERY_REGISTRY.snapshot(),
    *COMPARISON_CLOSURE_RECOVERY_REGISTRY.snapshot(),
    *PROCESS_COMPLETION_RECOVERY_REGISTRY.snapshot(),
))

SUPERVISOR_OPERATIONAL_ERROR_KINDS = frozenset({
    "operational_authority_invalid",
})
SUPERVISOR_DEADLINE_STAGES = frozenset({
    "BEFORE_CHECKPOINT",
    "NON_DECOMPILATION",
})
SUPERVISOR_PREFIX_TERMINAL_EVENT_TYPES = frozenset({
    EventType.EQ_CLOSURE,
    EventType.COUNTEREXAMPLE,
    EventType.ERROR,
})


class CheckpointState(str, Enum):
    ACTIVE = "ACTIVE"
    COMPLETION_READY = "COMPLETION_READY"
    RESOLVED = "RESOLVED"
    TIMED_OUT_CLAIMED = "TIMED_OUT_CLAIMED"
    TIMED_OUT = "TIMED_OUT"


_ALLOWED_TRANSITIONS = frozenset({
    (CheckpointState.ACTIVE, CheckpointState.COMPLETION_READY),
    (CheckpointState.COMPLETION_READY, CheckpointState.RESOLVED),
    (CheckpointState.ACTIVE, CheckpointState.TIMED_OUT_CLAIMED),
    (CheckpointState.TIMED_OUT_CLAIMED, CheckpointState.TIMED_OUT),
})
_SIGNED_RECEIPT_TOKEN = object()
_TRANSITION_CAPABILITY_TOKEN = object()
_TIMEOUT_BUNDLE_TOKEN = object()
_ERROR_BUNDLE_TOKEN = object()
_OPERATIONAL_ERROR_CAPABILITY_TOKEN = object()


@dataclass(frozen=True)
class SignedProcessAuthorityReceipt:
    receipt_kind: str
    payload: Mapping[str, Any]
    receipt_digest: str
    signing_key_id: str
    signature: str
    _factory_token: object = field(default=None, repr=False, compare=False)

    def to_dict(self) -> dict[str, Any]:
        return {
            "receipt_kind": self.receipt_kind,
            "payload": dict(self.payload),
            "receipt_digest": self.receipt_digest,
            "signing_key_id": self.signing_key_id,
            "signature": self.signature,
        }


@dataclass(frozen=True)
class SupervisorTerminalSegment:
    worker_prefix_digest: str
    timeout_receipt_digest: str
    terminal_event_sequence: int
    terminal_event_authority_digest: str
    segment_digest: str
    composite_stream: SealedEventStream = field(repr=False, compare=False)

    def validate(
        self, prefix: EventStreamPrefixView,
        timeout_receipt: SignedProcessAuthorityReceipt,
    ) -> None:
        prefix.validate()
        self.composite_stream.validate()
        events = self.composite_stream.events
        if (
            self.worker_prefix_digest != prefix.prefix_authority_digest
            or self.timeout_receipt_digest != timeout_receipt.receipt_digest
            or tuple(events[:-1]) != prefix.events
            or len(events) != len(prefix.events) + 1
            or events[-1].header.event_type is not EventType.PROCESS_TIMEOUT
            or events[-1].header.sequence_number != len(prefix.events) + 1
            or events[-1].header.predecessor_authority_digest
            != prefix.events[-1].authority_digest
            or events[-1].authority_digest != self.terminal_event_authority_digest
        ):
            raise ValueError("supervisor terminal segment is not one logical stream")
        expected = authority_digest({
            "worker_prefix_digest": self.worker_prefix_digest,
            "timeout_receipt_digest": self.timeout_receipt_digest,
            "terminal_event_sequence": self.terminal_event_sequence,
            "terminal_event_authority_digest": self.terminal_event_authority_digest,
            "composite_stream_digest": self.composite_stream.envelope.authority_chain_digest,
        })
        if self.segment_digest != expected:
            raise ValueError("supervisor terminal segment digest mismatch")


@dataclass(frozen=True)
class DurableTimeoutFinalizationBundle:
    launch_receipt_digest: str
    checkpoint_receipt_digest: str
    claimed_transition_digest: str
    timeout_receipt_digest: str
    terminal_segment_digest: str
    final_transition_digest: str
    result_occurrence_id: str
    proof_requirement_id: str
    invocation_identity: str
    child_exit_disposition: str
    composite_stream_authority_digest: str
    canonical_result_bundle_digest: str
    bundle_digest: str
    terminal_segment: SupervisorTerminalSegment = field(repr=False, compare=False)
    canonical_result_bundle: Mapping[str, Any] = field(repr=False, compare=False)
    _factory_token: object = field(default=None, repr=False, compare=False)


@dataclass(frozen=True)
class SupervisorErrorTerminalSegment:
    worker_prefix_kind: str
    worker_prefix_digest: str
    error_receipt_digest: str
    terminal_event_sequence: int
    terminal_event_authority_digest: str
    segment_digest: str
    composite_stream: SealedEventStream = field(repr=False, compare=False)


@dataclass(frozen=True)
class DurableErrorFinalizationBundle:
    launch_receipt_digest: str
    error_receipt_digest: str
    terminal_segment_digest: str
    result_occurrence_id: str
    error_kind: str
    deadline_stage: str
    child_exit_disposition: str
    composite_stream_authority_digest: str
    canonical_result_bundle_digest: str
    bundle_digest: str
    terminal_segment: SupervisorErrorTerminalSegment = field(
        repr=False, compare=False
    )
    canonical_result_bundle: Mapping[str, Any] = field(repr=False, compare=False)
    _factory_token: object = field(default=None, repr=False, compare=False)


class ProcessSupervisorAuthorityFactory:
    """Only signer/decoder for the sealed process-supervisor schemas."""

    def __init__(
        self, *, supervisor_signing_key_id: str,
        supervisor_signing_key: bytes, worker_signing_key_id: str,
        worker_signing_key: bytes,
    ) -> None:
        if (
            not all(type(value) is str and value for value in (
                supervisor_signing_key_id, worker_signing_key_id,
            ))
            or supervisor_signing_key_id == worker_signing_key_id
        ):
            raise TypeError("worker/supervisor signing key identities are invalid")
        if any(type(key) is not bytes or len(key) < 32 for key in (
            supervisor_signing_key, worker_signing_key,
        )):
            raise TypeError("process signing keys must contain at least 32 bytes")
        self.supervisor_signing_key_id = supervisor_signing_key_id
        self.worker_signing_key_id = worker_signing_key_id
        self.__keys = {
            "supervisor": supervisor_signing_key,
            "worker": worker_signing_key,
        }
        self._issued: dict[int, SignedProcessAuthorityReceipt] = {}
        self._bundles: dict[int, DurableTimeoutFinalizationBundle] = {}
        self._error_bundles: dict[int, DurableErrorFinalizationBundle] = {}

    def _issue(
        self, kind: str, payload: Mapping[str, Any], *, signer_role: str,
    ) -> SignedProcessAuthorityReceipt:
        if signer_role not in {"worker", "supervisor"}:
            raise ValueError("process receipt signer role is not sealed")
        body = {
            "receipt_kind": kind,
            "registry_id": PROCESS_SUPERVISOR_REGISTRY_ID,
            "registry_version": PROCESS_SUPERVISOR_REGISTRY_VERSION,
            "payload": dict(payload),
        }
        digest = authority_digest(body)
        signature = hmac.new(
            self.__keys[signer_role], digest.encode("ascii"), hashlib.sha256
        ).hexdigest()
        key_id = (
            self.worker_signing_key_id
            if signer_role == "worker"
            else self.supervisor_signing_key_id
        )
        receipt = SignedProcessAuthorityReceipt(
            kind, dict(payload), digest, key_id, signature,
            _factory_token=_SIGNED_RECEIPT_TOKEN,
        )
        self._issued[id(receipt)] = receipt
        return receipt

    def validate(self, receipt: SignedProcessAuthorityReceipt) -> None:
        if (
            type(receipt) is not SignedProcessAuthorityReceipt
            or receipt._factory_token is not _SIGNED_RECEIPT_TOKEN
            or self._issued.get(id(receipt)) is not receipt
        ):
            raise TypeError("process authority receipt is not exact factory membership")
        role = (
            "worker" if receipt.signing_key_id == self.worker_signing_key_id
            else "supervisor"
            if receipt.signing_key_id == self.supervisor_signing_key_id
            else None
        )
        if role is None:
            raise ValueError("process authority receipt signing key is untrusted")
        expected_roles = {
            "SupervisorLaunchReceipt": "supervisor",
            "SupervisorTimeoutReceipt": "supervisor",
            "SupervisorOperationalErrorReceipt": "supervisor",
            "SupervisorChildExitReceipt": "supervisor",
            "RecoveryResolutionReceipt": "supervisor",
            "ProcessLiveRequirementAssignmentReceipt": "worker",
            "OperationalCheckpointReceipt": "worker",
            "SupervisorBootstrapCheckpointReceipt": "supervisor",
            "WorkerContinuationReceipt": "worker",
        }
        expected_role = expected_roles.get(receipt.receipt_kind)
        if receipt.receipt_kind == "CheckpointStateTransitionReceipt":
            expected_role = (
                "worker"
                if receipt.payload.get("issuer_id") == PROCESS_WORKER_ISSUER_ID
                else "supervisor"
            )
        if expected_role != role:
            raise ValueError("process receipt signer role does not match receipt kind")
        body = {
            "receipt_kind": receipt.receipt_kind,
            "registry_id": PROCESS_SUPERVISOR_REGISTRY_ID,
            "registry_version": PROCESS_SUPERVISOR_REGISTRY_VERSION,
            "payload": dict(receipt.payload),
        }
        digest = authority_digest(body)
        signature = hmac.new(
            self.__keys[role], digest.encode("ascii"), hashlib.sha256
        ).hexdigest()
        if (
            receipt.receipt_digest != digest
            or not hmac.compare_digest(receipt.signature, signature)
        ):
            raise ValueError("process authority receipt signature/digest mismatch")

    def _validate_supervisor_canonical_bundle(
        self, bundle: Mapping[str, Any], *, launch: SignedProcessAuthorityReceipt,
        outcome: Outcome, error_kind: Optional[str],
    ) -> Mapping[str, Any]:
        from .canonical_result import (
            supervisor_canonical_result_payload_preimage,
            validate_canonical_result_finalization_bundle,
        )

        self.validate(launch)
        return validate_canonical_result_finalization_bundle(
            bundle,
            result_payload_preimage=supervisor_canonical_result_payload_preimage(
                launch, outcome=outcome, error_kind=error_kind
            ),
            bundle_verification_key_id=self.supervisor_signing_key_id,
            bundle_verification_key=self.__keys["supervisor"],
        )

    def decode(self, payload: Mapping[str, Any]) -> SignedProcessAuthorityReceipt:
        required = {
            "receipt_kind", "payload", "receipt_digest", "signing_key_id", "signature"
        }
        if type(payload) is not dict or set(payload) != required:
            raise ValueError("persisted process receipt schema mismatch")
        receipt = SignedProcessAuthorityReceipt(
            payload["receipt_kind"], dict(payload["payload"]),
            payload["receipt_digest"], payload["signing_key_id"],
            payload["signature"], _factory_token=_SIGNED_RECEIPT_TOKEN,
        )
        self._issued[id(receipt)] = receipt
        self.validate(receipt)
        return receipt

    def issue_launch(
        self, *, result_occurrence_id: str, manifest_entry_preimage_digest: str,
        execution_nonce: str, child_pid: int, child_start_token: str,
        stream_id: str, source_snapshot_fingerprint: str,
        deadline_policy_digest: str,
    ) -> SignedProcessAuthorityReceipt:
        if type(child_pid) is not int or child_pid <= 0:
            raise TypeError("supervisor launch PID is invalid")
        payload = {
            "result_occurrence_id": result_occurrence_id,
            "manifest_entry_preimage_digest": manifest_entry_preimage_digest,
            "execution_nonce": execution_nonce,
            "child_pid": child_pid,
            "child_start_token": child_start_token,
            "stream_id": stream_id,
            "source_snapshot_fingerprint": source_snapshot_fingerprint,
            "deadline_policy_digest": deadline_policy_digest,
            "policy_id": PROCESS_POLICY_ID,
            "issuer_id": PROCESS_SUPERVISOR_ISSUER_ID,
            "empty_stream_root": EMPTY_STREAM_ROOT,
        }
        if not all(type(value) is str and value for key, value in payload.items() if key != "child_pid"):
            raise TypeError("supervisor launch identity is incomplete")
        return self._issue("SupervisorLaunchReceipt", payload, signer_role="supervisor")

    def issue_deadline_bootstrap_checkpoint(
        self, *, launch: SignedProcessAuthorityReceipt,
        prior_resolved: Optional[SignedProcessAuthorityReceipt] = None,
    ) -> tuple[SignedProcessAuthorityReceipt, EventStreamPrefixView]:
        """Materialize the exact process-completion C/Q when no worker prefix exists."""

        self.validate(launch)
        if prior_resolved is not None:
            self.validate(prior_resolved)
            if (
                prior_resolved.payload.get("state")
                != CheckpointState.RESOLVED.value
                or prior_resolved.payload.get("launch_receipt_digest")
                != launch.receipt_digest
            ):
                raise ValueError(
                    "deadline bootstrap predecessor is not a resolved child checkpoint"
                )
        target = (
            "pair_process_execution_v1",
            launch.payload["manifest_entry_preimage_digest"],
            launch.payload["execution_nonce"],
            launch.payload["deadline_policy_digest"],
        )
        cause = SemanticCauseIdentityFactory(
            PROCESS_COMPLETION_REASON_REGISTRY
        ).create(
            reason_id=PROCESS_COMPLETION_REASON_ID,
            identity_scope=IdentityScope.RELATIONAL,
            target_kind="pair_process_execution",
            canonical_target_key=target,
            missing_semantic_fact=("terminal_pair_result", "unavailable_at_deadline"),
            semantic_proposition=("pair_process_has_terminal_result", target),
            observation_surface=(
                launch.payload["manifest_entry_preimage_digest"],
                launch.payload["deadline_policy_digest"],
            ),
            active_semantic_precondition=(
                "process_launch_is_durable", launch.receipt_digest
            ),
            correspondence_contract=None,
        )
        requirement = ProofRequirement(
            "process-completion-q-" + authority_digest(target)[:32],
            PROCESS_COMPLETION_PROOF_KIND,
            target,
        )
        bound = SatisfactionBindingFactory(
            PROCESS_COMPLETION_RECOVERY_REGISTRY
        ).bind(
            contract_definition_id=PROCESS_COMPLETION_CONTRACT_ID,
            contract_version=1,
            bindings={"completion": requirement},
        )
        occurrence = CauseOccurrence(
            "process-completion-occ-" + authority_digest({
                "result_occurrence_id": launch.payload["result_occurrence_id"],
                "target": target,
            })[:32],
            cause,
            PROCESS_COMPLETION_REASON_ID,
            authority_digest(target),
            "pair_process_execution",
            IdentityScope.RELATIONAL,
            bound.contract_definition_id,
            bound.contract_version,
            bound.normalized_expression_digest,
            bound.bound_expression_digest,
            (requirement.requirement_id,),
            (launch.receipt_digest, launch.payload["deadline_policy_digest"]),
            "process_supervisor_deadline_bootstrap",
            launch.payload["source_snapshot_fingerprint"],
            "pair-process-supervisor-v1",
            launch.payload["execution_nonce"],
        )
        recorder = EventRecorder(
            stream_id=launch.payload["stream_id"],
            result_occurrence_id=launch.payload["result_occurrence_id"],
            source_snapshot_fingerprint=(
                launch.payload["source_snapshot_fingerprint"]
            ),
        )
        observed = recorder.append(EventIntent(
            EventType.CAUSE_OBSERVED,
            CauseObservedEventAuthority(CauseOccurrenceAuthority(occurrence, bound)),
        ))
        prefix = EventStreamPrefixView.from_sealed_stream(recorder.seal())
        from .reducer import ShadowLifecycleReducer

        projection = ShadowLifecycleReducer(
            reason_registry=PROCESS_DURABLE_REASON_REGISTRY,
            recovery_registry=PROCESS_DURABLE_RECOVERY_REGISTRY,
        ).replay_prefix(prefix)
        assignment_digest = authority_digest({
            "assignment_kind": "SUPERVISOR_DEADLINE",
            "launch_receipt_digest": launch.receipt_digest,
            "proof_requirement_id": requirement.requirement_id,
            "prefix_digest": prefix.prefix_authority_digest,
        })
        invocation_identity = "pair-process-" + authority_digest(target)[:32]
        checkpoint = self._issue("SupervisorBootstrapCheckpointReceipt", {
            "state": CheckpointState.ACTIVE.value,
            "launch_receipt_digest": launch.receipt_digest,
            "result_occurrence_id": prefix.result_occurrence_id,
            "stream_id": prefix.stream_id,
            "prefix_digest": prefix.prefix_authority_digest,
            "last_event_authority_digest": observed.authority_digest,
            "lifecycle_prefix_projection_digest": projection.prefix_projection_digest,
            "q_open_base_digest": projection.q_open_base_digest,
            "assignment_kind": "SUPERVISOR_DEADLINE",
            "assignment_receipt_digest": assignment_digest,
            "proof_requirement_id": requirement.requirement_id,
            "invocation_receipt_digest": assignment_digest,
            "invocation_identity": invocation_identity,
            "invocation_ordinal": 1,
            "target_digest": authority_digest(target),
            "worker_pid": launch.payload["child_pid"],
            "worker_start_token": launch.payload["child_start_token"],
            "registry_digest": authority_digest({
                "reason": PROCESS_COMPLETION_REASON_REGISTRY.snapshot(),
                "recovery": PROCESS_COMPLETION_RECOVERY_REGISTRY.snapshot(),
            }),
            "input_surface_digest": launch.payload[
                "manifest_entry_preimage_digest"
            ],
            "operational_authority_root_digest": launch.receipt_digest,
            "configured_timeout_seconds": 0,
            "deadline_policy_digest": launch.payload["deadline_policy_digest"],
            "issuer_id": PROCESS_SUPERVISOR_ISSUER_ID,
            "prior_resolved_receipt_digest": (
                prior_resolved.receipt_digest
                if prior_resolved is not None else None
            ),
        }, signer_role="supervisor")
        return checkpoint, prefix

    def issue_child_exit_resolution(
        self, *, launch: SignedProcessAuthorityReceipt, child_returncode: int,
    ) -> SignedProcessAuthorityReceipt:
        self.validate(launch)
        if type(child_returncode) is not int:
            raise TypeError("supervisor child exit code must be an exact integer")
        return self._issue("SupervisorChildExitReceipt", {
            "result_occurrence_id": launch.payload["result_occurrence_id"],
            "launch_receipt_digest": launch.receipt_digest,
            "child_pid": launch.payload["child_pid"],
            "child_start_token": launch.payload["child_start_token"],
            "child_returncode": child_returncode,
            "deadline_policy_digest": launch.payload["deadline_policy_digest"],
            "issuer_id": PROCESS_SUPERVISOR_ISSUER_ID,
        }, signer_role="supervisor")

    def issue_live_assignment(
        self, *, prefix: EventStreamPrefixView,
        projection: VerifiedLifecyclePrefixProjection,
        reason_id: str,
        proof_requirement_id: Optional[str] = None,
    ) -> SignedProcessAuthorityReceipt:
        prefix.validate()
        projection.validate()
        row = _OPERATIONAL_PROCESS_ROWS.get(reason_id)
        if row is None:
            raise ValueError("process assignment reason is not registry-owned")
        proof_kind, producer_contract_id, priority = row
        if projection.event_stream_prefix_digest != prefix.prefix_chain_digest:
            raise ValueError("process assignment projection/prefix differs")
        candidates = []
        for q_row in projection.q_open_base:
            if q_row.proof_kind != proof_kind:
                continue
            for c_row in projection.c_active_base:
                if (
                    c_row.occurrence_id == q_row.occurrence_id
                    and c_row.cause_id == q_row.cause_id
                    and c_row.reason_id == reason_id
                    and c_row.domain == "operational_extraction"
                    and (
                        proof_requirement_id is None
                        or q_row.proof_requirement_id == proof_requirement_id
                    )
                ):
                    authorities = tuple(
                        event.authority_payload.occurrence_authority
                        for event in prefix.events
                        if (
                            event.header.event_type is EventType.CAUSE_OBSERVED
                            and type(event.authority_payload) is CauseObservedEventAuthority
                            and event.authority_payload.occurrence_authority.occurrence.occurrence_id
                            == q_row.occurrence_id
                        )
                    )
                    if (
                        len(authorities) == 1
                        and authorities[0].occurrence.producer_id
                        == producer_contract_id
                    ):
                        candidates.append((c_row, q_row))
        if len(candidates) != 1:
            raise ValueError("process assignment requires one exact live operational C/Q")
        c_row, q_row = candidates[0]
        return self._issue("ProcessLiveRequirementAssignmentReceipt", {
            "result_occurrence_id": projection.result_occurrence_id,
            "prefix_digest": prefix.prefix_authority_digest,
            "lifecycle_prefix_projection_digest": projection.prefix_projection_digest,
            "q_open_base_digest": projection.q_open_base_digest,
            "occurrence_id": q_row.occurrence_id,
            "cause_id": q_row.cause_id,
            "reason_id": c_row.reason_id,
            "proof_requirement_id": q_row.proof_requirement_id,
            "proof_kind": q_row.proof_kind,
            "semantic_target_digest": q_row.semantic_target_digest,
            "producer_contract_id": producer_contract_id,
            "producer_registry_digest": OPERATIONAL_PRODUCER_STAGE_REGISTRY_DIGEST,
            "terminal_priority": priority,
        }, signer_role="worker")

    def issue_active_checkpoint(
        self, *, launch: SignedProcessAuthorityReceipt,
        prefix: EventStreamPrefixView,
        projection: VerifiedLifecyclePrefixProjection,
        assignment: SignedProcessAuthorityReceipt,
        invocation: Any, operational_factory: Any,
        worker_pid: int, worker_start_token: str,
        prior_resolved: Optional[SignedProcessAuthorityReceipt] = None,
    ) -> SignedProcessAuthorityReceipt:
        self.validate(launch)
        self.validate(assignment)
        operational_factory.validate_invocation_membership(invocation)
        prefix.validate()
        projection.validate()
        if prior_resolved is not None:
            self.validate(prior_resolved)
            if (
                prior_resolved.payload.get("state")
                != CheckpointState.RESOLVED.value
                or prior_resolved.payload.get("launch_receipt_digest")
                != launch.receipt_digest
            ):
                raise ValueError("ACTIVE checkpoint predecessor is not resolved")
        if (
            launch.receipt_kind != "SupervisorLaunchReceipt"
            or prefix.result_occurrence_id != launch.payload["result_occurrence_id"]
            or prefix.stream_id != launch.payload["stream_id"]
            or projection.result_occurrence_id != prefix.result_occurrence_id
            or projection.event_stream_prefix_digest != prefix.prefix_chain_digest
            or assignment.receipt_kind != "ProcessLiveRequirementAssignmentReceipt"
            or assignment.payload["result_occurrence_id"] != projection.result_occurrence_id
            or assignment.payload["prefix_digest"] != prefix.prefix_authority_digest
            or assignment.payload["lifecycle_prefix_projection_digest"]
            != projection.prefix_projection_digest
            or assignment.payload["q_open_base_digest"] != projection.q_open_base_digest
            or assignment.payload["proof_requirement_id"] not in {
                row.proof_requirement_id for row in projection.q_open_base
            }
            or invocation.result_occurrence_id != projection.result_occurrence_id
            or invocation.proof_requirement_id
            != assignment.payload["proof_requirement_id"]
            or worker_pid != launch.payload["child_pid"]
            or worker_start_token != launch.payload["child_start_token"]
        ):
            raise ValueError("ACTIVE checkpoint does not join launch/prefix/live Q")
        payload = {
            "state": CheckpointState.ACTIVE.value,
            "launch_receipt_digest": launch.receipt_digest,
            "result_occurrence_id": prefix.result_occurrence_id,
            "stream_id": prefix.stream_id,
            "prefix_digest": prefix.prefix_authority_digest,
            "last_event_authority_digest": prefix.events[-1].authority_digest,
            "lifecycle_prefix_projection_digest": projection.prefix_projection_digest,
            "q_open_base_digest": projection.q_open_base_digest,
            "assignment_kind": "OPERATIONAL",
            "assignment_receipt_digest": assignment.receipt_digest,
            "proof_requirement_id": assignment.payload["proof_requirement_id"],
            "invocation_receipt_digest": invocation.receipt_digest,
            "invocation_identity": invocation.invocation_identity,
            "invocation_ordinal": invocation.invocation_ordinal,
            "target_digest": invocation.target_digest,
            "worker_pid": worker_pid,
            "worker_start_token": worker_start_token,
            "registry_digest": OPERATIONAL_PRODUCER_STAGE_REGISTRY_DIGEST,
            "input_surface_digest": invocation.input_surface_digest,
            "operational_authority_root_digest": (
                operational_factory.authority_root_digest
            ),
            "configured_timeout_seconds": invocation.configured_timeout_seconds,
            "deadline_policy_digest": launch.payload["deadline_policy_digest"],
            "issuer_id": PROCESS_WORKER_ISSUER_ID,
            "prior_resolved_receipt_digest": (
                prior_resolved.receipt_digest if prior_resolved is not None else None
            ),
        }
        return self._issue("OperationalCheckpointReceipt", payload, signer_role="worker")

    def issue_subordinate_active_checkpoint(
        self, *, launch: SignedProcessAuthorityReceipt,
        prefix: EventStreamPrefixView,
        projection: VerifiedLifecyclePrefixProjection,
        assignment: Any, assignment_factory: Any,
        invocation: Any, operational_factory: Any,
        worker_pid: int, worker_start_token: str,
        prior_resolved: Optional[SignedProcessAuthorityReceipt] = None,
    ) -> SignedProcessAuthorityReceipt:
        """Persist one adapter-owned parent-Q process assignment without relabeling it."""
        self.validate(launch)
        if (
            type(assignment_factory) is not SubordinateProcessAssignmentFactory
            or type(assignment) is not SubordinateProcessAssignmentReceipt
        ):
            raise TypeError("subordinate ACTIVE assignment authority is not sealed")
        assignment_factory.validate(assignment, projection, prefix)
        operational_factory.validate_invocation_membership(invocation)
        prefix.validate()
        projection.validate()
        if prior_resolved is not None:
            self.validate(prior_resolved)
            if (
                prior_resolved.payload.get("state")
                != CheckpointState.RESOLVED.value
                or prior_resolved.payload.get("launch_receipt_digest")
                != launch.receipt_digest
            ):
                raise ValueError("subordinate checkpoint predecessor is not resolved")
        if (
            launch.receipt_kind != "SupervisorLaunchReceipt"
            or prefix.result_occurrence_id != launch.payload["result_occurrence_id"]
            or prefix.stream_id != launch.payload["stream_id"]
            or projection.result_occurrence_id != prefix.result_occurrence_id
            or projection.event_stream_prefix_digest != prefix.prefix_chain_digest
            or assignment.result_occurrence_id != projection.result_occurrence_id
            or assignment.lifecycle_prefix_projection_digest
            != projection.prefix_projection_digest
            or assignment.q_open_base_digest != projection.q_open_base_digest
            or assignment.proof_requirement_id not in {
                row.proof_requirement_id for row in projection.q_open_base
            }
            or invocation.result_occurrence_id != projection.result_occurrence_id
            or invocation.proof_requirement_id != assignment.proof_requirement_id
            or worker_pid != launch.payload["child_pid"]
            or worker_start_token != launch.payload["child_start_token"]
        ):
            raise ValueError(
                "subordinate ACTIVE checkpoint does not join launch/prefix/live Q"
            )
        payload = {
            "state": CheckpointState.ACTIVE.value,
            "launch_receipt_digest": launch.receipt_digest,
            "result_occurrence_id": prefix.result_occurrence_id,
            "stream_id": prefix.stream_id,
            "prefix_digest": prefix.prefix_authority_digest,
            "last_event_authority_digest": prefix.events[-1].authority_digest,
            "lifecycle_prefix_projection_digest": projection.prefix_projection_digest,
            "q_open_base_digest": projection.q_open_base_digest,
            "assignment_kind": "SUBORDINATE",
            "assignment_receipt_digest": assignment.assignment_receipt_digest,
            "proof_requirement_id": assignment.proof_requirement_id,
            "invocation_receipt_digest": invocation.receipt_digest,
            "invocation_identity": invocation.invocation_identity,
            "invocation_ordinal": invocation.invocation_ordinal,
            "target_digest": invocation.target_digest,
            "worker_pid": worker_pid,
            "worker_start_token": worker_start_token,
            "registry_digest": assignment.adapter_registry_digest,
            "input_surface_digest": invocation.input_surface_digest,
            "operational_authority_root_digest": (
                operational_factory.authority_root_digest
            ),
            "configured_timeout_seconds": invocation.configured_timeout_seconds,
            "deadline_policy_digest": launch.payload["deadline_policy_digest"],
            "issuer_id": PROCESS_WORKER_ISSUER_ID,
            "prior_resolved_receipt_digest": (
                prior_resolved.receipt_digest if prior_resolved is not None else None
            ),
        }
        return self._issue(
            "OperationalCheckpointReceipt", payload, signer_role="worker"
        )

    def _issue_transition(
        self, *, prior: SignedProcessAuthorityReceipt,
        next_state: CheckpointState, lock_directory_digest: str,
        continuation_digest: Optional[str] = None,
        kill_disposition: Optional[str] = None,
        timeout_receipt_digest: Optional[str] = None,
        terminal_segment_digest: Optional[str] = None,
        recovery_resolution: Optional[SignedProcessAuthorityReceipt] = None,
        _capability: object = None,
    ) -> SignedProcessAuthorityReceipt:
        if _capability is not _TRANSITION_CAPABILITY_TOKEN:
            raise TypeError("checkpoint transition requires store-owned capability")
        self.validate(prior)
        prior_state = CheckpointState(prior.payload["state"])
        if (prior_state, next_state) not in _ALLOWED_TRANSITIONS:
            raise ValueError("checkpoint state transition is not sealed")
        if next_state in {CheckpointState.COMPLETION_READY, CheckpointState.RESOLVED}:
            if type(continuation_digest) is not str or not continuation_digest:
                raise ValueError("completion transition lacks durable continuation")
        elif continuation_digest is not None:
            raise ValueError("timeout transition cannot bind worker continuation")
        recovery = recovery_resolution is not None
        if recovery:
            self.validate(recovery_resolution)
            if (
                recovery_resolution.receipt_kind != "RecoveryResolutionReceipt"
                or next_state not in {
                    CheckpointState.COMPLETION_READY, CheckpointState.RESOLVED,
                }
                or recovery_resolution.payload["continuation_digest"]
                != continuation_digest
            ):
                raise ValueError("recovery transition lacks exact recovery authority")
        if next_state is CheckpointState.TIMED_OUT:
            if not timeout_receipt_digest or not terminal_segment_digest:
                raise ValueError("TIMED_OUT transition lacks final authority")
        if next_state is CheckpointState.TIMED_OUT_CLAIMED:
            if type(kill_disposition) is not str or not kill_disposition:
                raise ValueError("timeout claim lacks durable kill disposition")
        elif kill_disposition is not None:
            raise ValueError("non-claim transition cannot replace kill disposition")
        payload = dict(prior.payload)
        additions = {
            "state": next_state.value,
            "prior_state_receipt_digest": prior.receipt_digest,
            "lock_directory_digest": lock_directory_digest,
            "continuation_digest": continuation_digest,
            "timeout_receipt_digest": timeout_receipt_digest,
            "terminal_segment_digest": terminal_segment_digest,
            "recovery_resolution_receipt_digest": (
                recovery_resolution.receipt_digest if recovery else None
            ),
            "issuer_id": (
                "durable-continuation-recovery-resolver-v1"
                if recovery
                else PROCESS_WORKER_ISSUER_ID
                if next_state in {CheckpointState.COMPLETION_READY, CheckpointState.RESOLVED}
                else PROCESS_SUPERVISOR_ISSUER_ID
            ),
        }
        if kill_disposition is not None:
            additions["kill_disposition"] = kill_disposition
        payload.update(additions)
        return self._issue(
            "CheckpointStateTransitionReceipt", payload,
            signer_role=(
                "supervisor"
                if recovery
                else "worker"
                if next_state in {CheckpointState.COMPLETION_READY, CheckpointState.RESOLVED}
                else "supervisor"
            ),
        )

    def issue_worker_continuation(
        self, *, checkpoint: SignedProcessAuthorityReceipt,
        prefix: EventStreamPrefixView, continuation_stream: SealedEventStream,
        operational_factory: Any, attempt: Any = None,
        completed_artifact: Any = None, error_artifact: Any = None,
        subordinate_execution: Any = None,
        subordinate_assignment: Any = None,
        subordinate_assignment_factory: Any = None,
        subordinate_projection: Any = None,
        subordinate_invocation: Any = None,
    ) -> SignedProcessAuthorityReceipt:
        self.validate(checkpoint)
        prefix.validate()
        continuation_stream.validate()
        if attempt is not None:
            operational_factory.validate_attempt_membership(attempt)
        if completed_artifact is not None:
            operational_factory.validate_artifact_membership(completed_artifact)
        if error_artifact is not None:
            operational_factory.validate_error_membership(error_artifact)
        if (
            checkpoint.payload["state"] != CheckpointState.ACTIVE.value
            or checkpoint.payload["prefix_digest"] != prefix.prefix_authority_digest
            or tuple(continuation_stream.events[:len(prefix.events)]) != prefix.events
            or continuation_stream.envelope.result_occurrence_id
            != checkpoint.payload["result_occurrence_id"]
            or checkpoint.payload["operational_authority_root_digest"]
            != operational_factory.authority_root_digest
        ):
            raise ValueError("worker continuation dependencies do not join checkpoint")
        appended = continuation_stream.events[len(prefix.events):]
        terminal_events = tuple(event for event in appended if event.header.event_type in {
            EventType.REQUIREMENT_COMPLETED, EventType.PROCESS_COMPLETED,
            EventType.PROCESS_TIMEOUT, EventType.ERROR,
        })
        if len(terminal_events) != 1 or terminal_events[0] is not continuation_stream.events[-1]:
            raise ValueError("worker continuation requires one exact terminal observation")
        terminal = terminal_events[0]
        assignment_kind = checkpoint.payload.get("assignment_kind")
        if assignment_kind not in {"OPERATIONAL", "SUBORDINATE"}:
            raise ValueError("worker checkpoint assignment kind is not sealed")
        if (
            subordinate_execution is not None
            and assignment_kind != "SUBORDINATE"
        ):
            raise ValueError("operational checkpoint cannot use subordinate completion")
        if (
            completed_artifact is not None
            and subordinate_execution is None
            and assignment_kind != "OPERATIONAL"
        ):
            raise ValueError("subordinate checkpoint cannot complete parent requirement")
        if attempt is not None and (
            attempt.invocation_receipt_digest
            != checkpoint.payload["invocation_receipt_digest"]
            or attempt.proof_requirement_id != checkpoint.payload["proof_requirement_id"]
        ):
            raise ValueError("worker attempt differs from checkpoint invocation")
        if subordinate_execution is not None:
            if (
                type(subordinate_execution) is not SubordinateProcessExecutionReceipt
                or type(subordinate_assignment)
                is not SubordinateProcessAssignmentReceipt
                or type(subordinate_assignment_factory)
                is not SubordinateProcessAssignmentFactory
                or completed_artifact is None
                or error_artifact is not None
                or subordinate_assignment is None
                or subordinate_assignment_factory is None
                or subordinate_projection is None
                or subordinate_invocation is None
                or terminal.header.event_type is not EventType.PROCESS_COMPLETED
                or type(terminal.authority_payload)
                is not ProcessCompletionEventAuthority
                or terminal.authority_payload.proof_requirement_id
                != checkpoint.payload["proof_requirement_id"]
                or terminal.authority_payload.process_invocation_id
                != checkpoint.payload["invocation_identity"]
                or terminal.authority_payload.execution_receipt_digest
                != subordinate_execution.execution_receipt_digest
            ):
                raise ValueError("subordinate completion continuation authority differs")
            subordinate_assignment_factory.validate_runtime_execution(
                subordinate_execution, assignment=subordinate_assignment,
                projection=subordinate_projection, prefix=prefix,
                invocation=subordinate_invocation, attempt=attempt,
                completed_artifact=completed_artifact,
                operational_factory=operational_factory,
            )
            if (
                subordinate_assignment.assignment_receipt_digest
                != checkpoint.payload["assignment_receipt_digest"]
                or subordinate_invocation.receipt_digest
                != checkpoint.payload["invocation_receipt_digest"]
            ):
                raise ValueError("subordinate completion differs from checkpoint")
            continuation_kind = "SUBORDINATE_COMPLETED"
            terminal_artifact_digest = (
                subordinate_execution.execution_receipt_digest
            )
            terminal_error_kind = None
        elif completed_artifact is not None:
            if (
                attempt is None
                or attempt.disposition is not DecompilationDisposition.COMPLETED
                or error_artifact is not None
                or completed_artifact.attempt_receipt_digest != attempt.receipt_digest
                or terminal.header.event_type is not EventType.REQUIREMENT_COMPLETED
                or type(terminal.authority_payload)
                is not RequirementCompletedEventAuthority
                or terminal.authority_payload.completion_receipt.proof_requirement_id
                != checkpoint.payload["proof_requirement_id"]
                or terminal.authority_payload.completion_receipt.proof_artifact_digest
                != completed_artifact.artifact_digest
            ):
                raise ValueError("worker completion continuation authority differs")
            continuation_kind = "COMPLETED"
            terminal_artifact_digest = completed_artifact.artifact_digest
            terminal_error_kind = None
        elif error_artifact is not None:
            if (
                terminal.header.event_type is not EventType.ERROR
                or type(terminal.authority_payload) is not ErrorEventAuthority
                or terminal.authority_payload.error_kind != error_artifact.error_kind
                or terminal.authority_payload.error_artifact_digest
                != error_artifact.artifact_digest
                or error_artifact.result_occurrence_id
                != checkpoint.payload["result_occurrence_id"]
                or error_artifact.attempt_receipt_digest
                != (attempt.receipt_digest if attempt is not None else None)
                or (
                    attempt is None
                    and (
                        error_artifact.invocation_receipt_digest
                        != checkpoint.payload["invocation_receipt_digest"]
                        or error_artifact.target_digest
                        != checkpoint.payload["target_digest"]
                        or error_artifact.input_surface_digest
                        != checkpoint.payload["input_surface_digest"]
                        or error_artifact.operational_authority_root_digest
                        != checkpoint.payload["operational_authority_root_digest"]
                    )
                )
            ):
                raise ValueError("worker ERROR continuation authority differs")
            continuation_kind = "ERROR"
            terminal_artifact_digest = error_artifact.artifact_digest
            terminal_error_kind = error_artifact.error_kind
        else:
            if (
                attempt is None
                or attempt.disposition is not DecompilationDisposition.TIMED_OUT
                or terminal.header.event_type is not EventType.PROCESS_TIMEOUT
                or type(terminal.authority_payload)
                is not ProcessExecutionEventAuthority
                or terminal.authority_payload.proof_requirement_id
                != checkpoint.payload["proof_requirement_id"]
                or terminal.authority_payload.process_invocation_id
                != checkpoint.payload["invocation_identity"]
            ):
                raise ValueError("worker timeout continuation authority differs")
            continuation_kind = "TIMED_OUT_ATTEMPT"
            terminal_artifact_digest = attempt.receipt_digest
            terminal_error_kind = None
        receipt = self._issue("WorkerContinuationReceipt", {
            "checkpoint_receipt_digest": checkpoint.receipt_digest,
            "result_occurrence_id": checkpoint.payload["result_occurrence_id"],
            "prefix_authority_digest": prefix.prefix_authority_digest,
            "invocation_identity": checkpoint.payload["invocation_identity"],
            "proof_requirement_id": checkpoint.payload["proof_requirement_id"],
            "operational_authority_root_digest": checkpoint.payload[
                "operational_authority_root_digest"
            ],
            "continuation_kind": continuation_kind,
            "attempt_receipt_digest": (
                attempt.receipt_digest if attempt is not None else None
            ),
            "terminal_artifact_digest": terminal_artifact_digest,
            "terminal_error_kind": terminal_error_kind,
            "terminal_event_authority_digest": terminal.authority_digest,
            "continuation_stream_digest": (
                continuation_stream.envelope.authority_chain_digest
            ),
            "issuer_id": PROCESS_WORKER_ISSUER_ID,
        }, signer_role="worker")
        self.validate_worker_continuation(receipt, prefix, continuation_stream)
        return receipt

    def validate_worker_continuation(
        self, receipt: SignedProcessAuthorityReceipt,
        prefix: EventStreamPrefixView, continuation_stream: SealedEventStream,
    ) -> None:
        self.validate(receipt)
        prefix.validate()
        continuation_stream.validate()
        appended = continuation_stream.events[len(prefix.events):]
        matching = tuple(event for event in appended if (
            event.authority_digest == receipt.payload["terminal_event_authority_digest"]
        ))
        kind = receipt.payload.get("continuation_kind")
        event_type = {
            "COMPLETED": EventType.REQUIREMENT_COMPLETED,
            "SUBORDINATE_COMPLETED": EventType.PROCESS_COMPLETED,
            "TIMED_OUT_ATTEMPT": EventType.PROCESS_TIMEOUT,
            "ERROR": EventType.ERROR,
        }.get(kind)
        semantic_event_valid = False
        if len(matching) == 1 and kind == "COMPLETED":
            payload = matching[0].authority_payload
            semantic_event_valid = (
                type(payload) is RequirementCompletedEventAuthority
                and payload.completion_receipt.proof_requirement_id
                == receipt.payload["proof_requirement_id"]
                and payload.completion_receipt.proof_artifact_digest
                == receipt.payload["terminal_artifact_digest"]
            )
        elif len(matching) == 1 and kind in {
            "SUBORDINATE_COMPLETED", "TIMED_OUT_ATTEMPT",
        }:
            payload = matching[0].authority_payload
            semantic_event_valid = (
                type(payload) is (
                    ProcessCompletionEventAuthority
                    if kind == "SUBORDINATE_COMPLETED"
                    else ProcessExecutionEventAuthority
                )
                and payload.proof_requirement_id
                == receipt.payload["proof_requirement_id"]
                and payload.process_invocation_id
                == receipt.payload["invocation_identity"]
                and (
                    receipt.payload["attempt_receipt_digest"]
                    == receipt.payload["terminal_artifact_digest"]
                    if kind == "TIMED_OUT_ATTEMPT"
                    else type(receipt.payload["terminal_artifact_digest"]) is str
                    and bool(receipt.payload["terminal_artifact_digest"])
                    and payload.execution_receipt_digest
                    == receipt.payload["terminal_artifact_digest"]
                )
            )
        elif len(matching) == 1 and kind == "ERROR":
            payload = matching[0].authority_payload
            semantic_event_valid = (
                type(payload) is ErrorEventAuthority
                and payload.error_artifact_digest
                == receipt.payload["terminal_artifact_digest"]
                and payload.error_kind == receipt.payload["terminal_error_kind"]
            )
        if (
            receipt.receipt_kind != "WorkerContinuationReceipt"
            or receipt.payload["prefix_authority_digest"]
            != prefix.prefix_authority_digest
            or tuple(continuation_stream.events[:len(prefix.events)]) != prefix.events
            or continuation_stream.envelope.result_occurrence_id
            != receipt.payload["result_occurrence_id"]
            or continuation_stream.envelope.authority_chain_digest
            != receipt.payload["continuation_stream_digest"]
            or len(matching) != 1
            or matching[0].header.event_type is not event_type
            or matching[0] is not continuation_stream.events[-1]
            or not semantic_event_valid
            or len(tuple(event for event in appended if event.header.event_type in {
                EventType.REQUIREMENT_COMPLETED, EventType.PROCESS_COMPLETED,
                EventType.PROCESS_TIMEOUT, EventType.ERROR,
            })) != 1
        ):
            raise ValueError("persisted worker continuation authority is invalid")

    def issue_recovery_resolution(
        self, *, active: SignedProcessAuthorityReceipt,
        continuation: SignedProcessAuthorityReceipt,
        lock_directory_digest: str,
    ) -> SignedProcessAuthorityReceipt:
        self.validate(active)
        self.validate(continuation)
        if (
            active.payload["state"] != CheckpointState.ACTIVE.value
            or continuation.receipt_kind != "WorkerContinuationReceipt"
            or continuation.payload["checkpoint_receipt_digest"]
            != active.receipt_digest
        ):
            raise ValueError("recovery resolution does not bind ACTIVE continuation")
        return self._issue("RecoveryResolutionReceipt", {
            "checkpoint_receipt_digest": active.receipt_digest,
            "continuation_digest": continuation.receipt_digest,
            "continuation_stream_digest": continuation.payload[
                "continuation_stream_digest"
            ],
            "terminal_authority_digests": (
                continuation.payload["attempt_receipt_digest"],
                continuation.payload["terminal_artifact_digest"],
                continuation.payload["terminal_event_authority_digest"],
            ),
            "lock_directory_digest": lock_directory_digest,
            "issuer_id": "durable-continuation-recovery-resolver-v1",
        }, signer_role="supervisor")

    def issue_supervisor_timeout(
        self, *, claimed: SignedProcessAuthorityReceipt,
        prefix: EventStreamPrefixView,
    ) -> tuple[SignedProcessAuthorityReceipt, SupervisorTerminalSegment]:
        self.validate(claimed)
        prefix.validate()
        if (
            claimed.payload["state"] != CheckpointState.TIMED_OUT_CLAIMED.value
            or claimed.payload["prefix_digest"] != prefix.prefix_authority_digest
            or claimed.payload["last_event_authority_digest"]
            != prefix.events[-1].authority_digest
            or type(claimed.payload.get("kill_disposition")) is not str
            or not claimed.payload["kill_disposition"]
        ):
            raise ValueError("timeout claim differs from worker prefix")
        payload = {
            "checkpoint_receipt_digest": claimed.payload.get(
                "prior_state_receipt_digest"
            ),
            "claimed_transition_digest": claimed.receipt_digest,
            "result_occurrence_id": claimed.payload["result_occurrence_id"],
            "stream_id": claimed.payload["stream_id"],
            "prefix_digest": prefix.prefix_authority_digest,
            "last_event_authority_digest": prefix.events[-1].authority_digest,
            "assignment_receipt_digest": claimed.payload["assignment_receipt_digest"],
            "proof_requirement_id": claimed.payload["proof_requirement_id"],
            "invocation_receipt_digest": claimed.payload["invocation_receipt_digest"],
            "invocation_identity": claimed.payload["invocation_identity"],
            "worker_pid": claimed.payload["worker_pid"],
            "worker_start_token": claimed.payload["worker_start_token"],
            "kill_disposition": claimed.payload["kill_disposition"],
            "registry_digest": claimed.payload["registry_digest"],
            "deadline_policy_digest": claimed.payload["deadline_policy_digest"],
            "issuer_id": PROCESS_SUPERVISOR_ISSUER_ID,
        }
        timeout = self._issue(
            "SupervisorTimeoutReceipt", payload, signer_role="supervisor"
        )
        recorder = EventRecorder.continue_from_prefix(prefix)
        event = recorder.append(EventIntent(
            EventType.PROCESS_TIMEOUT,
            ProcessExecutionEventAuthority(
                claimed.payload["proof_requirement_id"],
                claimed.payload["invocation_identity"],
            ),
        ))
        stream = recorder.seal()
        segment_payload = {
            "worker_prefix_digest": prefix.prefix_authority_digest,
            "timeout_receipt_digest": timeout.receipt_digest,
            "terminal_event_sequence": event.header.sequence_number,
            "terminal_event_authority_digest": event.authority_digest,
            "composite_stream_digest": stream.envelope.authority_chain_digest,
        }
        segment = SupervisorTerminalSegment(
            prefix.prefix_authority_digest, timeout.receipt_digest,
            event.header.sequence_number, event.authority_digest,
            authority_digest(segment_payload), stream,
        )
        segment.validate(prefix, timeout)
        return timeout, segment

    def issue_timeout_bundle(
        self, *, launch: SignedProcessAuthorityReceipt,
        checkpoint: SignedProcessAuthorityReceipt,
        claimed: SignedProcessAuthorityReceipt,
        timeout: SignedProcessAuthorityReceipt,
        segment: SupervisorTerminalSegment,
        final_transition: SignedProcessAuthorityReceipt,
        prefix: EventStreamPrefixView,
    ) -> DurableTimeoutFinalizationBundle:
        for receipt in (launch, checkpoint, claimed, timeout, final_transition):
            self.validate(receipt)
        segment.validate(prefix, timeout)
        if (
            checkpoint.payload["launch_receipt_digest"] != launch.receipt_digest
            or claimed.payload["prior_state_receipt_digest"] != checkpoint.receipt_digest
            or final_transition.payload["prior_state_receipt_digest"] != claimed.receipt_digest
            or final_transition.payload["state"] != CheckpointState.TIMED_OUT.value
            or final_transition.payload["timeout_receipt_digest"] != timeout.receipt_digest
            or final_transition.payload["terminal_segment_digest"] != segment.segment_digest
        ):
            raise ValueError("timeout finalization chain is not exact")
        from .canonical_result import (
            build_supervisor_canonical_result_finalization_bundle,
        )

        canonical_bundle = build_supervisor_canonical_result_finalization_bundle(
            launch=launch,
            sealed_event_stream=segment.composite_stream,
            terminalizations=((
                segment.terminal_event_sequence,
                checkpoint.payload["proof_requirement_id"],
            ),),
            expected_outcome=Outcome.TIMEOUT,
            error_kind=None,
            seal_key_id=self.supervisor_signing_key_id,
            seal_key=self.__keys["supervisor"],
        )
        payload = {
            "launch_receipt_digest": launch.receipt_digest,
            "checkpoint_receipt_digest": checkpoint.receipt_digest,
            "claimed_transition_digest": claimed.receipt_digest,
            "timeout_receipt_digest": timeout.receipt_digest,
            "terminal_segment_digest": segment.segment_digest,
            "final_transition_digest": final_transition.receipt_digest,
            "result_occurrence_id": checkpoint.payload["result_occurrence_id"],
            "proof_requirement_id": checkpoint.payload["proof_requirement_id"],
            "invocation_identity": checkpoint.payload["invocation_identity"],
            "child_exit_disposition": timeout.payload["kill_disposition"],
            "composite_stream_authority_digest": (
                segment.composite_stream.envelope.authority_chain_digest
            ),
            "canonical_result_bundle_digest": canonical_bundle["bundle_digest"],
        }
        bundle = DurableTimeoutFinalizationBundle(
            **payload, bundle_digest=authority_digest(payload),
            terminal_segment=segment, canonical_result_bundle=canonical_bundle,
            _factory_token=_TIMEOUT_BUNDLE_TOKEN,
        )
        self._bundles[id(bundle)] = bundle
        self.validate_timeout_bundle(
            bundle, launch=launch, checkpoint=checkpoint, claimed=claimed,
            timeout=timeout, segment=segment, final_transition=final_transition,
            prefix=prefix,
        )
        return bundle

    def validate_timeout_bundle(
        self, bundle: DurableTimeoutFinalizationBundle, *,
        launch: SignedProcessAuthorityReceipt,
        checkpoint: SignedProcessAuthorityReceipt,
        claimed: SignedProcessAuthorityReceipt,
        timeout: SignedProcessAuthorityReceipt,
        segment: SupervisorTerminalSegment,
        final_transition: SignedProcessAuthorityReceipt,
        prefix: EventStreamPrefixView,
    ) -> None:
        if (
            type(bundle) is not DurableTimeoutFinalizationBundle
            or bundle._factory_token is not _TIMEOUT_BUNDLE_TOKEN
            or self._bundles.get(id(bundle)) is not bundle
        ):
            raise TypeError("timeout finalization bundle is not exact factory membership")
        for receipt in (launch, checkpoint, claimed, timeout, final_transition):
            self.validate(receipt)
        segment.validate(prefix, timeout)
        canonical = self._validate_supervisor_canonical_bundle(
            bundle.canonical_result_bundle,
            launch=launch,
            outcome=Outcome.TIMEOUT,
            error_kind=None,
        )
        payload = {
            name: getattr(bundle, name) for name in bundle.__dataclass_fields__
            if name not in {
                "bundle_digest", "terminal_segment", "canonical_result_bundle",
                "_factory_token",
            }
        }
        if (
            bundle.bundle_digest != authority_digest(payload)
            or bundle.terminal_segment is not segment
            or bundle.launch_receipt_digest != launch.receipt_digest
            or bundle.checkpoint_receipt_digest != checkpoint.receipt_digest
            or bundle.claimed_transition_digest != claimed.receipt_digest
            or bundle.child_exit_disposition
            != timeout.payload["kill_disposition"]
            or bundle.timeout_receipt_digest != timeout.receipt_digest
            or bundle.terminal_segment_digest != segment.segment_digest
            or bundle.final_transition_digest != final_transition.receipt_digest
            or bundle.composite_stream_authority_digest
            != segment.composite_stream.envelope.authority_chain_digest
            or bundle.canonical_result_bundle_digest
            != bundle.canonical_result_bundle["bundle_digest"]
            or canonical["outcome"] != Outcome.TIMEOUT.value
        ):
            raise ValueError("timeout finalization bundle integrity mismatch")

    def validate_timeout_bundle_membership(
        self, bundle: DurableTimeoutFinalizationBundle,
    ) -> None:
        if (
            type(bundle) is not DurableTimeoutFinalizationBundle
            or bundle._factory_token is not _TIMEOUT_BUNDLE_TOKEN
            or self._bundles.get(id(bundle)) is not bundle
        ):
            raise TypeError("timeout bundle is not exact supervisor-factory membership")
        payload = {
            name: getattr(bundle, name) for name in bundle.__dataclass_fields__
            if name not in {
                "bundle_digest", "terminal_segment", "canonical_result_bundle",
                "_factory_token",
            }
        }
        segment = bundle.terminal_segment
        segment.composite_stream.validate()
        events = segment.composite_stream.events
        if len(events) < 2:
            raise ValueError("timeout bundle terminal segment lacks worker prefix")
        terminal_event = events[-1]
        prefix_events = events[:-1]
        prefix_digest = authority_digest({
            "finality": "PREFIX",
            "stream_id": segment.composite_stream.envelope.stream_id,
            "result_occurrence_id": (
                segment.composite_stream.envelope.result_occurrence_id
            ),
            "source_snapshot_fingerprint": (
                segment.composite_stream.envelope.source_snapshot_fingerprint
            ),
            "event_count": len(prefix_events),
            "last_event_authority_digest": prefix_events[-1].authority_digest,
        })
        segment_payload = {
            "worker_prefix_digest": segment.worker_prefix_digest,
            "timeout_receipt_digest": segment.timeout_receipt_digest,
            "terminal_event_sequence": segment.terminal_event_sequence,
            "terminal_event_authority_digest": (
                segment.terminal_event_authority_digest
            ),
            "composite_stream_digest": (
                segment.composite_stream.envelope.authority_chain_digest
            ),
        }
        timeout_receipts = tuple(
            receipt for receipt in self._issued.values()
            if receipt.receipt_digest == bundle.timeout_receipt_digest
        )
        for receipt in timeout_receipts:
            self.validate(receipt)
        launches_by_digest = {
            receipt.receipt_digest: receipt
            for receipt in self._issued.values()
            if receipt.receipt_digest == bundle.launch_receipt_digest
            and receipt.receipt_kind == "SupervisorLaunchReceipt"
        }
        if set(launches_by_digest) != {bundle.launch_receipt_digest}:
            raise ValueError("timeout bundle launch authority is not unique")
        launch = launches_by_digest[bundle.launch_receipt_digest]
        canonical = self._validate_supervisor_canonical_bundle(
            bundle.canonical_result_bundle,
            launch=launch,
            outcome=Outcome.TIMEOUT,
            error_kind=None,
        )
        if (
            bundle.bundle_digest != authority_digest(payload)
            or bundle.terminal_segment_digest != segment.segment_digest
            or bundle.composite_stream_authority_digest
            != segment.composite_stream.envelope.authority_chain_digest
            or segment.segment_digest != authority_digest(segment_payload)
            or segment.worker_prefix_digest != prefix_digest
            or segment.timeout_receipt_digest != bundle.timeout_receipt_digest
            or bundle.canonical_result_bundle_digest
            != bundle.canonical_result_bundle["bundle_digest"]
            or canonical["outcome"] != Outcome.TIMEOUT.value
            or not timeout_receipts
            or any(
                receipt.receipt_kind != "SupervisorTimeoutReceipt"
                or receipt.payload["result_occurrence_id"]
                != bundle.result_occurrence_id
                or receipt.payload["proof_requirement_id"]
                != bundle.proof_requirement_id
                or receipt.payload["invocation_identity"]
                != bundle.invocation_identity
                for receipt in timeout_receipts
            )
            or terminal_event.header.event_type is not EventType.PROCESS_TIMEOUT
            or terminal_event.header.sequence_number
            != segment.terminal_event_sequence
            or terminal_event.header.sequence_number != len(events)
            or terminal_event.header.predecessor_authority_digest
            != prefix_events[-1].authority_digest
            or terminal_event.authority_digest
            != segment.terminal_event_authority_digest
            or type(terminal_event.authority_payload)
            is not ProcessExecutionEventAuthority
            or terminal_event.authority_payload.proof_requirement_id
            != bundle.proof_requirement_id
            or terminal_event.authority_payload.process_invocation_id
            != bundle.invocation_identity
        ):
            raise ValueError("timeout bundle membership integrity mismatch")

    def validated_timeout_terminal_event(
        self, bundle: DurableTimeoutFinalizationBundle,
    ) -> Any:
        self.validate_timeout_bundle_membership(bundle)
        return bundle.terminal_segment.composite_stream.events[-1]

    def _issue_operational_error(
        self, *, launch: SignedProcessAuthorityReceipt,
        error_kind: str, deadline_stage: str,
        child_exit_disposition: str,
        prefix: Optional[EventStreamPrefixView] = None,
        _capability: object,
    ) -> SignedProcessAuthorityReceipt:
        if _capability is not _OPERATIONAL_ERROR_CAPABILITY_TOKEN:
            raise TypeError("operational ERROR issuance requires store capability")
        self.validate(launch)
        if launch.receipt_kind != "SupervisorLaunchReceipt":
            raise ValueError("operational error requires exact launch authority")
        if error_kind not in SUPERVISOR_OPERATIONAL_ERROR_KINDS:
            raise ValueError("supervisor operational error kind is not sealed")
        if deadline_stage not in SUPERVISOR_DEADLINE_STAGES:
            raise ValueError("supervisor deadline stage is not sealed")
        if type(child_exit_disposition) is not str or not child_exit_disposition:
            raise TypeError("child exit disposition is incomplete")
        if prefix is None:
            prefix_kind = "EMPTY"
            prefix_digest = EMPTY_STREAM_ROOT
            event_count = 0
        else:
            prefix.validate()
            if (
                prefix.stream_id != launch.payload["stream_id"]
                or prefix.result_occurrence_id
                != launch.payload["result_occurrence_id"]
                or prefix.source_snapshot_fingerprint
                != launch.payload["source_snapshot_fingerprint"]
                or any(
                    event.header.event_type
                    in SUPERVISOR_PREFIX_TERMINAL_EVENT_TYPES
                    for event in prefix.events
                )
            ):
                raise ValueError("operational error prefix differs from launch")
            prefix_kind = "PREFIX"
            prefix_digest = prefix.prefix_authority_digest
            event_count = len(prefix.events)
        payload = {
            "launch_receipt_digest": launch.receipt_digest,
            "result_occurrence_id": launch.payload["result_occurrence_id"],
            "manifest_entry_preimage_digest": (
                launch.payload["manifest_entry_preimage_digest"]
            ),
            "execution_nonce": launch.payload["execution_nonce"],
            "stream_id": launch.payload["stream_id"],
            "source_snapshot_fingerprint": (
                launch.payload["source_snapshot_fingerprint"]
            ),
            "deadline_policy_digest": launch.payload["deadline_policy_digest"],
            "error_kind": error_kind,
            "deadline_stage": deadline_stage,
            "child_exit_disposition": child_exit_disposition,
            "worker_prefix_kind": prefix_kind,
            "worker_prefix_digest": prefix_digest,
            "worker_event_count": event_count,
            "issuer_id": PROCESS_SUPERVISOR_ISSUER_ID,
        }
        return self._issue(
            "SupervisorOperationalErrorReceipt", payload,
            signer_role="supervisor",
        )

    def _issue_operational_error_segment(
        self, *, launch: SignedProcessAuthorityReceipt,
        error: SignedProcessAuthorityReceipt,
        prefix: Optional[EventStreamPrefixView] = None,
        _capability: object,
    ) -> SupervisorErrorTerminalSegment:
        if _capability is not _OPERATIONAL_ERROR_CAPABILITY_TOKEN:
            raise TypeError("operational ERROR segment requires store capability")
        self.validate(launch)
        self.validate(error)
        if (
            launch.receipt_kind != "SupervisorLaunchReceipt"
            or error.receipt_kind != "SupervisorOperationalErrorReceipt"
            or error.payload["launch_receipt_digest"] != launch.receipt_digest
        ):
            raise ValueError("operational error receipt/launch chain differs")
        if prefix is None:
            if (
                error.payload["worker_prefix_kind"] != "EMPTY"
                or error.payload["worker_prefix_digest"] != EMPTY_STREAM_ROOT
                or error.payload["worker_event_count"] != 0
            ):
                raise ValueError("empty operational error prefix authority differs")
            recorder = EventRecorder(
                stream_id=launch.payload["stream_id"],
                result_occurrence_id=launch.payload["result_occurrence_id"],
                source_snapshot_fingerprint=(
                    launch.payload["source_snapshot_fingerprint"]
                ),
            )
        else:
            prefix.validate()
            if (
                error.payload["worker_prefix_kind"] != "PREFIX"
                or error.payload["worker_prefix_digest"]
                != prefix.prefix_authority_digest
                or error.payload["worker_event_count"] != len(prefix.events)
            ):
                raise ValueError("operational error prefix authority differs")
            recorder = EventRecorder.continue_from_prefix(prefix)
        event = recorder.append(EventIntent(
            EventType.ERROR,
            ErrorEventAuthority(
                error.payload["error_kind"], error.receipt_digest
            ),
        ))
        stream = recorder.seal()
        payload = {
            "worker_prefix_kind": error.payload["worker_prefix_kind"],
            "worker_prefix_digest": error.payload["worker_prefix_digest"],
            "error_receipt_digest": error.receipt_digest,
            "terminal_event_sequence": event.header.sequence_number,
            "terminal_event_authority_digest": event.authority_digest,
            "composite_stream_digest": stream.envelope.authority_chain_digest,
        }
        return SupervisorErrorTerminalSegment(
            error.payload["worker_prefix_kind"],
            error.payload["worker_prefix_digest"], error.receipt_digest,
            event.header.sequence_number, event.authority_digest,
            authority_digest(payload), stream,
        )

    def _validate_operational_error_segment(
        self, *, launch: SignedProcessAuthorityReceipt,
        error: SignedProcessAuthorityReceipt,
        segment: SupervisorErrorTerminalSegment,
        prefix: Optional[EventStreamPrefixView],
    ) -> None:
        self.validate(launch)
        self.validate(error)
        segment.composite_stream.validate()
        events = segment.composite_stream.events
        expected_prefix_kind = error.payload["worker_prefix_kind"]
        if expected_prefix_kind == "EMPTY":
            prefix_events = ()
            expected_prefix_digest = EMPTY_STREAM_ROOT
            if prefix is not None:
                raise ValueError("empty ERROR authority cannot consume a prefix")
        elif expected_prefix_kind == "PREFIX":
            if len(events) < 2:
                raise ValueError("persisted ERROR prefix is missing")
            prefix_events = events[:-1]
            expected_prefix_digest = authority_digest({
                "finality": "PREFIX",
                "stream_id": segment.composite_stream.envelope.stream_id,
                "result_occurrence_id": (
                    segment.composite_stream.envelope.result_occurrence_id
                ),
                "source_snapshot_fingerprint": (
                    segment.composite_stream.envelope.source_snapshot_fingerprint
                ),
                "event_count": len(prefix_events),
                "last_event_authority_digest": prefix_events[-1].authority_digest,
            })
            if prefix is not None:
                prefix.validate()
                if (
                    tuple(prefix.events) != tuple(prefix_events)
                    or prefix.prefix_authority_digest != expected_prefix_digest
                ):
                    raise ValueError("ERROR segment differs from supplied prefix")
        else:
            raise ValueError("operational ERROR prefix kind is not sealed")
        if any(
            event.header.event_type in SUPERVISOR_PREFIX_TERMINAL_EVENT_TYPES
            for event in prefix_events
        ):
            raise ValueError("operational ERROR prefix is already terminal")
        terminal = events[-1]
        payload = {
            "worker_prefix_kind": segment.worker_prefix_kind,
            "worker_prefix_digest": segment.worker_prefix_digest,
            "error_receipt_digest": segment.error_receipt_digest,
            "terminal_event_sequence": segment.terminal_event_sequence,
            "terminal_event_authority_digest": (
                segment.terminal_event_authority_digest
            ),
            "composite_stream_digest": (
                segment.composite_stream.envelope.authority_chain_digest
            ),
        }
        if (
            error.receipt_kind != "SupervisorOperationalErrorReceipt"
            or error.payload["launch_receipt_digest"] != launch.receipt_digest
            or segment.worker_prefix_kind != expected_prefix_kind
            or segment.worker_prefix_digest != expected_prefix_digest
            or tuple(events[:-1]) != tuple(prefix_events)
            or len(events) != len(prefix_events) + 1
            or segment.composite_stream.envelope.stream_id
            != launch.payload["stream_id"]
            or segment.composite_stream.envelope.result_occurrence_id
            != launch.payload["result_occurrence_id"]
            or segment.composite_stream.envelope.source_snapshot_fingerprint
            != launch.payload["source_snapshot_fingerprint"]
            or segment.error_receipt_digest != error.receipt_digest
            or terminal.header.event_type is not EventType.ERROR
            or terminal.header.sequence_number != len(events)
            or terminal.header.sequence_number != segment.terminal_event_sequence
            or terminal.authority_digest
            != segment.terminal_event_authority_digest
            or type(terminal.authority_payload) is not ErrorEventAuthority
            or terminal.authority_payload.error_kind
            != error.payload["error_kind"]
            or terminal.authority_payload.error_artifact_digest
            != error.receipt_digest
            or segment.segment_digest != authority_digest(payload)
        ):
            raise ValueError("supervisor operational ERROR segment is invalid")

    def _issue_operational_error_bundle(
        self, *, launch: SignedProcessAuthorityReceipt,
        error: SignedProcessAuthorityReceipt,
        segment: SupervisorErrorTerminalSegment,
        prefix: Optional[EventStreamPrefixView] = None,
        _capability: object,
    ) -> DurableErrorFinalizationBundle:
        if _capability is not _OPERATIONAL_ERROR_CAPABILITY_TOKEN:
            raise TypeError("operational ERROR bundle requires store capability")
        self._validate_operational_error_segment(
            launch=launch, error=error, segment=segment, prefix=prefix
        )
        from .canonical_result import (
            build_supervisor_canonical_result_finalization_bundle,
        )

        canonical_bundle = build_supervisor_canonical_result_finalization_bundle(
            launch=launch,
            sealed_event_stream=segment.composite_stream,
            terminalizations=(),
            expected_outcome=Outcome.ERROR,
            error_kind=error.payload["error_kind"],
            seal_key_id=self.supervisor_signing_key_id,
            seal_key=self.__keys["supervisor"],
        )
        payload = {
            "launch_receipt_digest": launch.receipt_digest,
            "error_receipt_digest": error.receipt_digest,
            "terminal_segment_digest": segment.segment_digest,
            "result_occurrence_id": launch.payload["result_occurrence_id"],
            "error_kind": error.payload["error_kind"],
            "deadline_stage": error.payload["deadline_stage"],
            "child_exit_disposition": error.payload[
                "child_exit_disposition"
            ],
            "composite_stream_authority_digest": (
                segment.composite_stream.envelope.authority_chain_digest
            ),
            "canonical_result_bundle_digest": canonical_bundle["bundle_digest"],
        }
        bundle = DurableErrorFinalizationBundle(
            **payload, bundle_digest=authority_digest(payload),
            terminal_segment=segment, canonical_result_bundle=canonical_bundle,
            _factory_token=_ERROR_BUNDLE_TOKEN,
        )
        self._error_bundles[id(bundle)] = bundle
        self.validate_operational_error_bundle(
            bundle, launch=launch, error=error, segment=segment, prefix=prefix
        )
        return bundle

    def validate_operational_error_bundle(
        self, bundle: DurableErrorFinalizationBundle, *,
        launch: SignedProcessAuthorityReceipt,
        error: SignedProcessAuthorityReceipt,
        segment: SupervisorErrorTerminalSegment,
        prefix: Optional[EventStreamPrefixView] = None,
    ) -> None:
        if (
            type(bundle) is not DurableErrorFinalizationBundle
            or bundle._factory_token is not _ERROR_BUNDLE_TOKEN
            or self._error_bundles.get(id(bundle)) is not bundle
        ):
            raise TypeError("operational ERROR bundle is not exact factory membership")
        self._validate_operational_error_segment(
            launch=launch, error=error, segment=segment, prefix=prefix
        )
        canonical = self._validate_supervisor_canonical_bundle(
            bundle.canonical_result_bundle,
            launch=launch,
            outcome=Outcome.ERROR,
            error_kind=error.payload["error_kind"],
        )
        payload = {
            name: getattr(bundle, name) for name in bundle.__dataclass_fields__
            if name not in {
                "bundle_digest", "terminal_segment", "canonical_result_bundle",
                "_factory_token",
            }
        }
        if (
            bundle.bundle_digest != authority_digest(payload)
            or bundle.terminal_segment is not segment
            or bundle.launch_receipt_digest != launch.receipt_digest
            or bundle.error_receipt_digest != error.receipt_digest
            or bundle.child_exit_disposition
            != error.payload["child_exit_disposition"]
            or bundle.terminal_segment_digest != segment.segment_digest
            or bundle.composite_stream_authority_digest
            != segment.composite_stream.envelope.authority_chain_digest
            or bundle.canonical_result_bundle_digest
            != bundle.canonical_result_bundle["bundle_digest"]
            or canonical["outcome"] != Outcome.ERROR.value
        ):
            raise ValueError("operational ERROR bundle integrity mismatch")


class DurableCheckpointStore:
    """Atomic, fsync-backed state/continuation store with one directory lock."""

    def __init__(
        self, root: Path, factory: ProcessSupervisorAuthorityFactory,
        invocation_nonce: str,
    ) -> None:
        self.root = Path(root)
        self.factory = factory
        if (
            type(invocation_nonce) is not str
            or not invocation_nonce
            or any(not (character.isalnum() or character in "-_") for character in invocation_nonce)
        ):
            raise ValueError("checkpoint invocation nonce is not a safe identity")
        self.invocation_nonce = invocation_nonce
        self.directory = self.root / invocation_nonce
        self.directory.mkdir(parents=True, exist_ok=True)
        self.lock_path = self.root / ".checkpoint-directory.lock"
        self.lock_directory_digest = authority_digest({
            "checkpoint_directory": str(self.root.resolve())
        })
        self.codec = StrictV2JsonCodec(
            reason_registry=PROCESS_DURABLE_REASON_REGISTRY,
            recovery_registry=PROCESS_DURABLE_RECOVERY_REGISTRY,
        )

    @contextmanager
    def _locked(self) -> Iterator[None]:
        self.root.mkdir(parents=True, exist_ok=True)
        with self.lock_path.open("a+b") as lock_file:
            fcntl.flock(lock_file.fileno(), fcntl.LOCK_EX)
            try:
                yield
            finally:
                fcntl.flock(lock_file.fileno(), fcntl.LOCK_UN)

    @staticmethod
    def _bytes(receipt: SignedProcessAuthorityReceipt) -> bytes:
        return json.dumps(
            receipt.to_dict(), sort_keys=True, separators=(",", ":")
        ).encode("utf-8") + b"\n"

    def _atomic_write(self, path: Path, data: bytes, *, identical_ok: bool = False) -> None:
        if path.exists():
            existing = path.read_bytes()
            if identical_ok and existing == data:
                return
            raise ValueError("conflicting durable process authority already exists")
        fd, temporary = tempfile.mkstemp(prefix=".pending-", dir=str(path.parent))
        try:
            with os.fdopen(fd, "wb", closefd=True) as handle:
                handle.write(data)
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

    def persist_launch(self, receipt: SignedProcessAuthorityReceipt) -> None:
        self.factory.validate(receipt)
        if receipt.receipt_kind != "SupervisorLaunchReceipt":
            raise ValueError("launch store requires SupervisorLaunchReceipt")
        if receipt.payload["execution_nonce"] != self.invocation_nonce:
            raise ValueError("launch execution nonce differs from checkpoint directory")
        with self._locked():
            self._atomic_write(self.directory / "launch.json", self._bytes(receipt))

    def persist_child_exit_resolution(
        self, receipt: SignedProcessAuthorityReceipt,
    ) -> None:
        self.factory.validate(receipt)
        if receipt.receipt_kind != "SupervisorChildExitReceipt":
            raise ValueError("child exit store requires SupervisorChildExitReceipt")
        with self._locked():
            launch = self.factory.decode(json.loads(
                (self.directory / "launch.json").read_text(encoding="utf-8")
            ))
            if receipt.payload["launch_receipt_digest"] != launch.receipt_digest:
                raise ValueError("child exit resolution differs from durable launch")
            self._atomic_write(
                self.directory / "child-exit.json", self._bytes(receipt),
                identical_ok=True,
            )

    def resolved_predecessor(self) -> Optional[SignedProcessAuthorityReceipt]:
        """Return the exact completed checkpoint that a new ACTIVE must extend."""

        with self._locked():
            state_path = self.directory / "state.json"
            if not state_path.exists():
                return None
            state = self.factory.decode(json.loads(
                state_path.read_text(encoding="utf-8")
            ))
            if state.payload.get("state") != CheckpointState.RESOLVED.value:
                raise ValueError("new checkpoint requires a resolved predecessor")
            return state

    def _archive_resolved_checkpoint_locked(
        self, resolved: SignedProcessAuthorityReceipt,
    ) -> None:
        history = self.directory / "checkpoint-history" / resolved.receipt_digest
        if history.exists():
            raise ValueError("resolved checkpoint history already exists")
        history.mkdir(parents=True)
        names = (
            "checkpoint-prefix-stream.json",
            "checkpoint.json",
            "continuation-stream.json",
            "continuation.json",
            "ready.json",
            "state.json",
        )
        for name in names:
            source = self.directory / name
            if source.exists():
                os.replace(source, history / name)
        directory_fd = os.open(history, os.O_RDONLY)
        try:
            os.fsync(directory_fd)
        finally:
            os.close(directory_fd)

    def rematerialize_child_exit_resolution(self) -> SignedProcessAuthorityReceipt:
        receipt = self.factory.decode(json.loads(
            (self.directory / "child-exit.json").read_text(encoding="utf-8")
        ))
        if receipt.receipt_kind != "SupervisorChildExitReceipt":
            raise ValueError("durable child exit resolution kind is invalid")
        return receipt

    def persist_active(
        self, receipt: SignedProcessAuthorityReceipt,
        prefix: EventStreamPrefixView,
    ) -> None:
        self.factory.validate(receipt)
        prefix.validate()
        if receipt.payload["state"] != CheckpointState.ACTIVE.value:
            raise ValueError("initial checkpoint must be ACTIVE")
        if receipt.payload["prefix_digest"] != prefix.prefix_authority_digest:
            raise ValueError("ACTIVE checkpoint prefix authority differs")
        with self._locked():
            launch_path = self.directory / "launch.json"
            try:
                launch = self.factory.decode(json.loads(
                    launch_path.read_text(encoding="utf-8")
                ))
            except Exception as exc:
                raise ValueError("ACTIVE checkpoint lacks durable launch authority") from exc
            if receipt.payload["launch_receipt_digest"] != launch.receipt_digest:
                raise ValueError("ACTIVE checkpoint launch binding differs")
            state_path = self.directory / "state.json"
            predecessor_digest = receipt.payload.get(
                "prior_resolved_receipt_digest"
            )
            if state_path.exists():
                predecessor = self.factory.decode(json.loads(
                    state_path.read_text(encoding="utf-8")
                ))
                if (
                    predecessor.payload.get("state")
                    != CheckpointState.RESOLVED.value
                    or predecessor.receipt_digest != predecessor_digest
                ):
                    raise ValueError(
                        "ACTIVE checkpoint does not extend durable resolved state"
                    )
                self._archive_resolved_checkpoint_locked(predecessor)
            elif predecessor_digest is not None:
                raise ValueError("first ACTIVE checkpoint carries a predecessor")
            prefix_stream = SealedEventStream(
                EventStreamEnvelope(
                    prefix.stream_id, prefix.result_occurrence_id,
                    prefix.source_snapshot_fingerprint, 1,
                    len(prefix.events), len(prefix.events),
                    prefix.prefix_chain_digest, True,
                ),
                prefix.events,
            )
            prefix_stream.validate()
            self._atomic_write(
                self.directory / "checkpoint-prefix-stream.json",
                self.codec.dumps(prefix_stream).encode("utf-8"),
            )
            self._atomic_write(
                self.directory / "checkpoint.json", self._bytes(receipt)
            )
            self._atomic_write(self.directory / "state.json", self._bytes(receipt))

    def rematerialize_active_prefix(self) -> EventStreamPrefixView:
        try:
            checkpoint = self.factory.decode(json.loads(
                (self.directory / "checkpoint.json").read_text(encoding="utf-8")
            ))
            stream = self.codec.loads(
                (self.directory / "checkpoint-prefix-stream.json").read_text(
                    encoding="utf-8"
                )
            )
        except Exception as exc:
            raise ValueError("durable ACTIVE prefix is missing or invalid") from exc
        prefix = EventStreamPrefixView.from_sealed_stream(stream)
        if (
            checkpoint.payload["state"] != CheckpointState.ACTIVE.value
            or checkpoint.payload["prefix_digest"]
            != prefix.prefix_authority_digest
        ):
            raise ValueError("durable ACTIVE prefix differs from checkpoint")
        return prefix

    def read_state(self) -> SignedProcessAuthorityReceipt:
        path = self.directory / "state.json"
        try:
            payload = json.loads(path.read_text(encoding="utf-8"))
        except Exception as exc:
            raise ValueError("missing or torn durable checkpoint state") from exc
        return self.factory.decode(payload)

    def _publish_continuation_locked(
        self, receipt: SignedProcessAuthorityReceipt,
        prefix: EventStreamPrefixView, continuation_stream: SealedEventStream,
    ) -> None:
        self.factory.validate_worker_continuation(
            receipt, prefix, continuation_stream
        )
        self._atomic_write(
            self.directory / "continuation.json", self._bytes(receipt),
            identical_ok=True,
        )
        stream_bytes = self.codec.dumps(continuation_stream).encode("utf-8")
        self._atomic_write(
            self.directory / "continuation-stream.json", stream_bytes,
            identical_ok=True,
        )

    def _replace_state_locked(
        self, replacement: SignedProcessAuthorityReceipt,
    ) -> None:
        path = self.directory / "state.json"
        data = self._bytes(replacement)
        fd, temporary = tempfile.mkstemp(prefix=".state-", dir=str(path.parent))
        try:
            with os.fdopen(fd, "wb", closefd=True) as handle:
                handle.write(data)
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

    def worker_publish_completion(
        self, *, active: SignedProcessAuthorityReceipt,
        continuation: SignedProcessAuthorityReceipt,
        prefix: EventStreamPrefixView,
        continuation_stream: SealedEventStream,
    ) -> tuple[SignedProcessAuthorityReceipt, SignedProcessAuthorityReceipt]:
        self.factory.validate(active)
        self.factory.validate(continuation)
        if (
            active.payload["state"] != CheckpointState.ACTIVE.value
            or continuation.payload["checkpoint_receipt_digest"]
            != active.receipt_digest
        ):
            raise ValueError("worker continuation differs from ACTIVE checkpoint")
        with self._locked():
            current = self.read_state()
            if current.receipt_digest != active.receipt_digest:
                raise ValueError("worker completion lost checkpoint CAS")
            self._publish_continuation_locked(
                continuation, prefix, continuation_stream
            )
            ready = self.factory._issue_transition(
                prior=active, next_state=CheckpointState.COMPLETION_READY,
                lock_directory_digest=self.lock_directory_digest,
                continuation_digest=continuation.receipt_digest,
                _capability=_TRANSITION_CAPABILITY_TOKEN,
            )
            self._atomic_write(
                self.directory / "ready.json", self._bytes(ready)
            )
            self._replace_state_locked(ready)
            resolved = self.factory._issue_transition(
                prior=ready, next_state=CheckpointState.RESOLVED,
                lock_directory_digest=self.lock_directory_digest,
                continuation_digest=continuation.receipt_digest,
                _capability=_TRANSITION_CAPABILITY_TOKEN,
            )
            self._replace_state_locked(resolved)
            return ready, resolved

    def worker_publish_continuation(
        self, *, active: SignedProcessAuthorityReceipt,
        continuation: SignedProcessAuthorityReceipt,
        prefix: EventStreamPrefixView,
        continuation_stream: SealedEventStream,
    ) -> None:
        self.factory.validate(active)
        with self._locked():
            current = self.read_state()
            if current.receipt_digest != active.receipt_digest:
                raise ValueError("worker continuation lost checkpoint CAS")
            self._publish_continuation_locked(
                continuation, prefix, continuation_stream
            )

    def supervisor_claim_timeout(
        self, *, active: SignedProcessAuthorityReceipt,
        prefix: EventStreamPrefixView, kill_disposition: str,
    ) -> SignedProcessAuthorityReceipt:
        self.factory.validate(active)
        prefix.validate()
        if active.payload["prefix_digest"] != prefix.prefix_authority_digest:
            raise ValueError("supervisor claim prefix differs from checkpoint")
        with self._locked():
            current = self.read_state()
            if current.receipt_digest != active.receipt_digest:
                raise ValueError("supervisor timeout lost checkpoint CAS")
            continuation = self.directory / "continuation.json"
            if continuation.exists():
                # Verification occurs under the same lock.  A valid continuation
                # always wins; a torn/invalid one makes the census invalid.
                durable = self.factory.decode(json.loads(
                    continuation.read_text(encoding="utf-8")
                ))
                durable_stream = self.codec.loads(
                    (self.directory / "continuation-stream.json").read_text(
                        encoding="utf-8"
                    )
                )
                self.factory.validate_worker_continuation(
                    durable, prefix, durable_stream,
                )
                recovery = self.factory.issue_recovery_resolution(
                    active=active, continuation=durable,
                    lock_directory_digest=self.lock_directory_digest,
                )
                self._atomic_write(
                    self.directory / "recovery-resolution.json",
                    self._bytes(recovery), identical_ok=True,
                )
                ready = self.factory._issue_transition(
                    prior=active, next_state=CheckpointState.COMPLETION_READY,
                    lock_directory_digest=self.lock_directory_digest,
                    continuation_digest=durable.receipt_digest,
                    recovery_resolution=recovery,
                    _capability=_TRANSITION_CAPABILITY_TOKEN,
                )
                self._atomic_write(
                    self.directory / "ready.json", self._bytes(ready),
                    identical_ok=True,
                )
                self._replace_state_locked(ready)
                resolved = self.factory._issue_transition(
                    prior=ready, next_state=CheckpointState.RESOLVED,
                    lock_directory_digest=self.lock_directory_digest,
                    continuation_digest=durable.receipt_digest,
                    recovery_resolution=recovery,
                    _capability=_TRANSITION_CAPABILITY_TOKEN,
                )
                self._replace_state_locked(resolved)
                return resolved
            claimed = self.factory._issue_transition(
                prior=active, next_state=CheckpointState.TIMED_OUT_CLAIMED,
                lock_directory_digest=self.lock_directory_digest,
                kill_disposition=kill_disposition,
                _capability=_TRANSITION_CAPABILITY_TOKEN,
            )
            self._atomic_write(
                self.directory / "claimed.json", self._bytes(claimed)
            )
            self._replace_state_locked(claimed)
            return claimed

    def recover_completion_ready(
        self, *, ready: SignedProcessAuthorityReceipt,
        prefix: EventStreamPrefixView,
    ) -> SignedProcessAuthorityReceipt:
        """Resolve the durable worker continuation after the READY crash window."""
        self.factory.validate(ready)
        prefix.validate()
        with self._locked():
            current = self.read_state()
            if (
                current.receipt_digest != ready.receipt_digest
                or ready.payload["state"] != CheckpointState.COMPLETION_READY.value
            ):
                raise ValueError("completion recovery lost READY-state CAS")
            try:
                checkpoint = self.factory.decode(json.loads(
                    (self.directory / "checkpoint.json").read_text(encoding="utf-8")
                ))
                continuation = self.factory.decode(json.loads(
                    (self.directory / "continuation.json").read_text(encoding="utf-8")
                ))
                continuation_stream = self.codec.loads(
                    (self.directory / "continuation-stream.json").read_text(
                        encoding="utf-8"
                    )
                )
            except Exception as exc:
                raise ValueError("READY recovery authority is missing or invalid") from exc
            self.factory.validate_worker_continuation(
                continuation, prefix, continuation_stream
            )
            if (
                checkpoint.payload["state"] != CheckpointState.ACTIVE.value
                or ready.payload["prior_state_receipt_digest"]
                != checkpoint.receipt_digest
                or ready.payload["continuation_digest"]
                != continuation.receipt_digest
            ):
                raise ValueError("READY recovery chain differs from durable authority")
            recovery = self.factory.issue_recovery_resolution(
                active=checkpoint, continuation=continuation,
                lock_directory_digest=self.lock_directory_digest,
            )
            self._atomic_write(
                self.directory / "recovery-resolution.json",
                self._bytes(recovery), identical_ok=True,
            )
            self._atomic_write(
                self.directory / "ready.json", self._bytes(ready),
                identical_ok=True,
            )
            resolved = self.factory._issue_transition(
                prior=ready, next_state=CheckpointState.RESOLVED,
                lock_directory_digest=self.lock_directory_digest,
                continuation_digest=continuation.receipt_digest,
                recovery_resolution=recovery,
                _capability=_TRANSITION_CAPABILITY_TOKEN,
            )
            self._replace_state_locked(resolved)
            return resolved

    def rematerialize_resolved_state(
        self, *, prefix: EventStreamPrefixView,
    ) -> SignedProcessAuthorityReceipt:
        """Verify the complete durable completion chain, not only final state."""
        prefix.validate()

        def read_receipt(name: str) -> SignedProcessAuthorityReceipt:
            try:
                return self.factory.decode(json.loads(
                    (self.directory / name).read_text(encoding="utf-8")
                ))
            except Exception as exc:
                raise ValueError(f"persisted {name} authority is invalid") from exc

        launch = read_receipt("launch.json")
        checkpoint = read_receipt("checkpoint.json")
        continuation, continuation_stream = self.rematerialize_worker_continuation(
            prefix=prefix
        )
        ready = read_receipt("ready.json")
        resolved = self.read_state()
        if (
            checkpoint.payload["state"] != CheckpointState.ACTIVE.value
            or checkpoint.payload["launch_receipt_digest"] != launch.receipt_digest
            or ready.payload["state"] != CheckpointState.COMPLETION_READY.value
            or ready.payload["prior_state_receipt_digest"]
            != checkpoint.receipt_digest
            or ready.payload["continuation_digest"] != continuation.receipt_digest
            or continuation.payload["operational_authority_root_digest"]
            != checkpoint.payload["operational_authority_root_digest"]
            or resolved.payload["state"] != CheckpointState.RESOLVED.value
            or resolved.payload["prior_state_receipt_digest"] != ready.receipt_digest
            or resolved.payload["continuation_digest"]
            != continuation.receipt_digest
        ):
            raise ValueError("durable RESOLVED chain is inconsistent")
        return resolved

    def rematerialize_worker_continuation(
        self, *, prefix: EventStreamPrefixView,
    ) -> tuple[SignedProcessAuthorityReceipt, SealedEventStream]:
        prefix.validate()
        try:
            continuation = self.factory.decode(json.loads(
                (self.directory / "continuation.json").read_text(encoding="utf-8")
            ))
            continuation_stream = self.codec.loads(
                (self.directory / "continuation-stream.json").read_text(
                    encoding="utf-8"
                )
            )
        except Exception as exc:
            raise ValueError("persisted worker continuation is invalid") from exc
        self.factory.validate_worker_continuation(
            continuation, prefix, continuation_stream
        )
        return continuation, continuation_stream

    def finalize_timeout(
        self, *, claimed: SignedProcessAuthorityReceipt,
        timeout: SignedProcessAuthorityReceipt,
        segment: SupervisorTerminalSegment,
        prefix: EventStreamPrefixView,
    ) -> SignedProcessAuthorityReceipt:
        self.factory.validate(claimed)
        self.factory.validate(timeout)
        segment.validate(prefix, timeout)
        with self._locked():
            current = self.read_state()
            if current.receipt_digest != claimed.receipt_digest:
                raise ValueError("timeout finalization lost claimed-state CAS")
            self._atomic_write(
                self.directory / "timeout.json", self._bytes(timeout),
                identical_ok=True,
            )
            segment_payload = json.dumps({
                "worker_prefix_digest": segment.worker_prefix_digest,
                "timeout_receipt_digest": segment.timeout_receipt_digest,
                "terminal_event_sequence": segment.terminal_event_sequence,
                "terminal_event_authority_digest": segment.terminal_event_authority_digest,
                "segment_digest": segment.segment_digest,
                "composite_stream_authority_digest": (
                    segment.composite_stream.envelope.authority_chain_digest
                ),
            }, sort_keys=True, separators=(",", ":")).encode("utf-8") + b"\n"
            self._atomic_write(
                self.directory / "terminal-segment.json", segment_payload,
                identical_ok=True,
            )
            self._atomic_write(
                self.directory / "terminal-stream.json",
                self.codec.dumps(segment.composite_stream).encode("utf-8"),
                identical_ok=True,
            )
            rematerialized = self.rematerialize_terminal_segment(prefix, timeout)
            if rematerialized.segment_digest != segment.segment_digest:
                raise ValueError("persisted terminal segment rematerialization differs")
            final = self.factory._issue_transition(
                prior=claimed, next_state=CheckpointState.TIMED_OUT,
                lock_directory_digest=self.lock_directory_digest,
                timeout_receipt_digest=timeout.receipt_digest,
                terminal_segment_digest=segment.segment_digest,
                _capability=_TRANSITION_CAPABILITY_TOKEN,
            )
            self._replace_state_locked(final)
            return final

    def rematerialize_terminal_segment(
        self, prefix: EventStreamPrefixView,
        timeout: SignedProcessAuthorityReceipt,
    ) -> SupervisorTerminalSegment:
        self.factory.validate(timeout)
        prefix.validate()
        try:
            metadata = json.loads(
                (self.directory / "terminal-segment.json").read_text(
                    encoding="utf-8"
                )
            )
            stream = self.codec.loads(
                (self.directory / "terminal-stream.json").read_text(
                    encoding="utf-8"
                )
            )
        except Exception as exc:
            raise ValueError("persisted terminal segment is missing or invalid") from exc
        required = {
            "worker_prefix_digest", "timeout_receipt_digest",
            "terminal_event_sequence", "terminal_event_authority_digest",
            "segment_digest", "composite_stream_authority_digest",
        }
        if set(metadata) != required:
            raise ValueError("persisted terminal segment schema mismatch")
        segment = SupervisorTerminalSegment(
            metadata["worker_prefix_digest"], metadata["timeout_receipt_digest"],
            metadata["terminal_event_sequence"],
            metadata["terminal_event_authority_digest"],
            metadata["segment_digest"], stream,
        )
        segment.validate(prefix, timeout)
        if (
            stream.envelope.authority_chain_digest
            != metadata["composite_stream_authority_digest"]
        ):
            raise ValueError("persisted composite stream digest mismatch")
        return segment

    def rematerialize_timeout_bundle(
        self, *, prefix: EventStreamPrefixView,
    ) -> DurableTimeoutFinalizationBundle:
        def read_receipt(name: str) -> SignedProcessAuthorityReceipt:
            try:
                return self.factory.decode(json.loads(
                    (self.directory / name).read_text(encoding="utf-8")
                ))
            except Exception as exc:
                raise ValueError(f"persisted {name} authority is invalid") from exc

        launch = read_receipt("launch.json")
        checkpoint = read_receipt("checkpoint.json")
        claimed = read_receipt("claimed.json")
        timeout = read_receipt("timeout.json")
        final = self.read_state()
        segment = self.rematerialize_terminal_segment(prefix, timeout)
        return self.factory.issue_timeout_bundle(
            launch=launch, checkpoint=checkpoint, claimed=claimed,
            timeout=timeout, segment=segment, final_transition=final,
            prefix=prefix,
        )

    def supervisor_finalize_operational_error(
        self, *, launch: SignedProcessAuthorityReceipt,
        error_kind: str, deadline_stage: str,
        child_exit_disposition: str,
        prefix: Optional[EventStreamPrefixView] = None,
    ) -> DurableErrorFinalizationBundle:
        self.factory.validate(launch)
        with self._locked():
            try:
                durable_launch = self.factory.decode(json.loads(
                    (self.directory / "launch.json").read_text(encoding="utf-8")
                ))
            except Exception as exc:
                raise ValueError(
                    "operational ERROR lacks durable launch authority"
                ) from exc
            if durable_launch.receipt_digest != launch.receipt_digest:
                raise ValueError("operational ERROR durable launch differs")
            if any(
                (self.directory / name).exists()
                for name in CHECKPOINT_AUTHORITY_FILENAMES
            ):
                raise ValueError(
                    "operational ERROR path cannot replace checkpoint authority"
                )
            error = self.factory._issue_operational_error(
                launch=launch, error_kind=error_kind,
                deadline_stage=deadline_stage,
                child_exit_disposition=child_exit_disposition,
                prefix=prefix,
                _capability=_OPERATIONAL_ERROR_CAPABILITY_TOKEN,
            )
            segment = self.factory._issue_operational_error_segment(
                launch=launch, error=error, prefix=prefix,
                _capability=_OPERATIONAL_ERROR_CAPABILITY_TOKEN,
            )
            bundle = self.factory._issue_operational_error_bundle(
                launch=launch, error=error, segment=segment, prefix=prefix,
                _capability=_OPERATIONAL_ERROR_CAPABILITY_TOKEN,
            )
            self._atomic_write(
                self.directory / "operational-error.json", self._bytes(error),
                identical_ok=True,
            )
            segment_payload = json.dumps({
                "worker_prefix_kind": segment.worker_prefix_kind,
                "worker_prefix_digest": segment.worker_prefix_digest,
                "error_receipt_digest": segment.error_receipt_digest,
                "terminal_event_sequence": segment.terminal_event_sequence,
                "terminal_event_authority_digest": (
                    segment.terminal_event_authority_digest
                ),
                "segment_digest": segment.segment_digest,
                "composite_stream_authority_digest": (
                    segment.composite_stream.envelope.authority_chain_digest
                ),
            }, sort_keys=True, separators=(",", ":")).encode("utf-8") + b"\n"
            self._atomic_write(
                self.directory / "operational-error-segment.json",
                segment_payload, identical_ok=True,
            )
            self._atomic_write(
                self.directory / "operational-error-stream.json",
                self.codec.dumps(segment.composite_stream).encode("utf-8"),
                identical_ok=True,
            )
            bundle_payload = json.dumps({
                name: getattr(bundle, name)
                for name in bundle.__dataclass_fields__
                if name not in {"terminal_segment", "_factory_token"}
            }, sort_keys=True, separators=(",", ":")).encode("utf-8") + b"\n"
            self._atomic_write(
                self.directory / "operational-error-bundle.json",
                bundle_payload, identical_ok=True,
            )
            rematerialized = self._rematerialize_operational_error_bundle_locked(
                prefix=prefix
            )
            if rematerialized.bundle_digest != bundle.bundle_digest:
                raise ValueError("persisted operational ERROR bundle differs")
            return bundle

    def _rematerialize_operational_error_bundle_locked(
        self, *, prefix: Optional[EventStreamPrefixView],
    ) -> DurableErrorFinalizationBundle:
        if any(
            (self.directory / name).exists()
            for name in CHECKPOINT_AUTHORITY_FILENAMES
        ):
            raise ValueError(
                "persisted operational ERROR conflicts with checkpoint authority"
            )
        try:
            launch = self.factory.decode(json.loads(
                (self.directory / "launch.json").read_text(encoding="utf-8")
            ))
            error = self.factory.decode(json.loads(
                (self.directory / "operational-error.json").read_text(
                    encoding="utf-8"
                )
            ))
            metadata = json.loads(
                (self.directory / "operational-error-segment.json").read_text(
                    encoding="utf-8"
                )
            )
            stream = self.codec.loads(
                (self.directory / "operational-error-stream.json").read_text(
                    encoding="utf-8"
                )
            )
            stored_bundle = json.loads(
                (self.directory / "operational-error-bundle.json").read_text(
                    encoding="utf-8"
                )
            )
        except Exception as exc:
            raise ValueError(
                "persisted operational ERROR authority is missing or invalid"
            ) from exc
        required_segment = {
            "worker_prefix_kind", "worker_prefix_digest", "error_receipt_digest",
            "terminal_event_sequence", "terminal_event_authority_digest",
            "segment_digest", "composite_stream_authority_digest",
        }
        if set(metadata) != required_segment:
            raise ValueError("persisted operational ERROR segment schema mismatch")
        segment = SupervisorErrorTerminalSegment(
            metadata["worker_prefix_kind"], metadata["worker_prefix_digest"],
            metadata["error_receipt_digest"],
            metadata["terminal_event_sequence"],
            metadata["terminal_event_authority_digest"],
            metadata["segment_digest"], stream,
        )
        bundle = self.factory._issue_operational_error_bundle(
            launch=launch, error=error, segment=segment, prefix=prefix,
            _capability=_OPERATIONAL_ERROR_CAPABILITY_TOKEN,
        )
        expected_bundle = {
            name: getattr(bundle, name)
            for name in bundle.__dataclass_fields__
            if name not in {"terminal_segment", "_factory_token"}
        }
        if (
            metadata["composite_stream_authority_digest"]
            != stream.envelope.authority_chain_digest
            or stored_bundle != json.loads(json.dumps(
                expected_bundle, sort_keys=True, separators=(",", ":")
            ))
        ):
            raise ValueError("persisted operational ERROR bundle integrity mismatch")
        return bundle

    def rematerialize_operational_error_bundle(
        self, *, prefix: Optional[EventStreamPrefixView] = None,
    ) -> DurableErrorFinalizationBundle:
        with self._locked():
            return self._rematerialize_operational_error_bundle_locked(prefix=prefix)
