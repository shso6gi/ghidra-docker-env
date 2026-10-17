"""Durable decompiler checkpoint, supervisor timeout, and process census authority."""

from __future__ import annotations

from contextlib import contextmanager
from dataclasses import dataclass, field
import fcntl
import hashlib
import hmac
import json
import os
from pathlib import Path
import tempfile
import threading
from typing import Any, Iterator, Mapping, Optional

from scripts.function_tracer_pcode.authority.process import store_layout as layout
from scripts.function_tracer_pcode.authority.process.canonical_envelope import (
    read_canonical_envelope,
)
from scripts.function_tracer_pcode.authority.contracts import (
    CauseOccurrence,
    CauseOccurrenceAuthority,
    IdentityScope,
    Outcome,
    ProofRequirement,
    ReasonDefinition,
    RecoveryAddressability,
    RequirementSlotDefinition,
    SatisfactionContractDefinition,
    VerifiedLifecyclePrefixProjection,
    authority_digest,
    requirement_slot,
)
from scripts.function_tracer_pcode.authority.lifecycle.stream import (
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
from scripts.function_tracer_pcode.authority.process.operational_extraction import (
    DecompilationDisposition,
    OPERATIONAL_REASON_REGISTRY,
    OPERATIONAL_RECOVERY_REGISTRY,
    OPERATIONAL_PRODUCER_STAGE_REGISTRY_DIGEST,
)
from scripts.function_tracer_pcode.authority.domains.analysis_limitation import (
    ANALYSIS_LIMITATION_REASON_REGISTRY,
    ANALYSIS_LIMITATION_RECOVERY_REGISTRY,
)
from scripts.function_tracer_pcode.authority.domains.call_effect import (
    CALL_EFFECT_REASON_REGISTRY,
    CALL_EFFECT_RECOVERY_REGISTRY,
)
from scripts.function_tracer_pcode.authority.domains.loop_recurrence import (
    LOOP_REASON_REGISTRY,
    LOOP_RECOVERY_REGISTRY,
)
from scripts.function_tracer_pcode.authority.domains.return_outcome import (
    RETURN_OUTCOME_REASON_REGISTRY,
    RETURN_OUTCOME_RECOVERY_REGISTRY,
)
from scripts.function_tracer_pcode.authority.domains.sat_safety import (
    SAT_SAFETY_REASON_REGISTRY,
    SAT_SAFETY_RECOVERY_REGISTRY,
)
from scripts.function_tracer_pcode.authority.domains.abi_width_readonly import (
    ABI_WIDTH_READONLY_REASON_REGISTRY,
    ABI_WIDTH_READONLY_RECOVERY_REGISTRY,
)
from scripts.function_tracer_pcode.authority.lifecycle.production_signals import (
    COMPARISON_CLOSURE_REASON_REGISTRY,
    COMPARISON_CLOSURE_RECOVERY_REGISTRY,
)
from scripts.function_tracer_pcode.authority.domains.cross_side_identity import (
    CROSS_SIDE_IDENTITY_REASON_REGISTRY,
    CROSS_SIDE_IDENTITY_RECOVERY_REGISTRY,
)
from scripts.function_tracer_pcode.authority.registry import (
    SatisfactionBindingFactory,
    SealedReasonRegistry,
    SealedRecoveryRegistry,
    SemanticCauseIdentityFactory,
)
from scripts.function_tracer_pcode.authority.process.subordinate_decompilation import (
    SubordinateProcessAssignmentFactory,
    SubordinateProcessAssignmentReceipt,
    SubordinateProcessExecutionReceipt,
)
from scripts.function_tracer_pcode.authority.codecs import StrictV2JsonCodec
from scripts.function_tracer_pcode.authority.process.checkpoint_archive import (
    CHAIN_MEMBER_NAMES,
    CHAIN_MEMBERS,
    directory_reader,
    fsync_directory,
    history_destination,
    history_directory,
    live_chain_members,
    move_member,
)
from scripts.function_tracer_pcode.authority.process.checkpoint_vocabulary import (
    ALLOWED_TRANSITIONS,
    BOOTSTRAP_CHECKPOINT_KIND,
    LAUNCH_RECEIPT_KIND,
    OPERATIONAL_ERROR_RECEIPT_KIND,
    CheckpointState,
    SUPERVISOR_DEADLINE_STAGES,
    SUPERVISOR_OPERATIONAL_ERROR_KINDS,
)
from scripts.function_tracer_pcode.authority.process import terminal_evidence
from scripts.function_tracer_pcode.authority.process.terminal_evidence import (
    TERMINAL_EVIDENCE_FILES,
)
from scripts.function_tracer_pcode.authority.lifecycle.stream import (
    RequirementCompletedEventAuthority,
)


PROCESS_SUPERVISOR_REGISTRY_ID = "operational-process-supervisor-v1"
PROCESS_SUPERVISOR_REGISTRY_VERSION = 1
PROCESS_SUPERVISOR_ISSUER_ID = "decompiler-process-supervisor-v1"
PROCESS_WORKER_ISSUER_ID = "decompiler-process-runner-v1"
PROCESS_POLICY_ID = "decompiler-deadline-policy-v1"
EMPTY_STREAM_ROOT = "0" * 64
ACTIVE_TRANSACTION_SCHEMA = "durable-active-checkpoint-transaction-v1"

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
    *CROSS_SIDE_IDENTITY_REASON_REGISTRY.snapshot(),
    *ANALYSIS_LIMITATION_REASON_REGISTRY.snapshot(),
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
    *CROSS_SIDE_IDENTITY_RECOVERY_REGISTRY.snapshot(),
    *ANALYSIS_LIMITATION_RECOVERY_REGISTRY.snapshot(),
    *PROCESS_COMPLETION_RECOVERY_REGISTRY.snapshot(),
))

SUPERVISOR_PREFIX_TERMINAL_EVENT_TYPES = frozenset({
    EventType.EQ_CLOSURE,
    EventType.COUNTEREXAMPLE,
    EventType.ERROR,
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
        # Issue #110: 検証の仕事は event 数に比例する: 契約の外の stream は検証を始めない
        from scripts.function_tracer_pcode.authority.event_contract import (
            require_events_within_contract,
        )

        require_events_within_contract(len(self.composite_stream.events))
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
        key_ids = (supervisor_signing_key_id, worker_signing_key_id)
        if (
            not all(type(value) is str and value for value in key_ids)
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
        return self._sign(kind, payload, signer_role=signer_role)

    def issue_terminal_evidence(
        self, kind: str, payload: Mapping[str, Any],
    ) -> SignedProcessAuthorityReceipt:
        """D / E / A（Issue #165）を supervisor role で署名する。

        schema と launch / D / E の join の検証は ``terminal_evidence`` が持つ
        （ここは kind の封と署名だけ）。
        """
        if kind not in TERMINAL_EVIDENCE_FILES:
            raise ValueError("terminal evidence kind is not sealed")
        return self._sign(kind, payload, signer_role="supervisor")

    def _sign(
        self, kind: str, payload: Mapping[str, Any], *, signer_role: str,
    ) -> SignedProcessAuthorityReceipt:
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
        key_id = self._role_key_ids()[signer_role]
        receipt = SignedProcessAuthorityReceipt(
            kind, dict(payload), digest, key_id, signature,
            _factory_token=_SIGNED_RECEIPT_TOKEN,
        )
        self._issued[id(receipt)] = receipt
        return receipt

    def _role_key_ids(self) -> dict[str, str]:
        return {
            "worker": self.worker_signing_key_id,
            "supervisor": self.supervisor_signing_key_id,
        }

    def validate(self, receipt: SignedProcessAuthorityReceipt) -> None:
        if (
            type(receipt) is not SignedProcessAuthorityReceipt
            or receipt._factory_token is not _SIGNED_RECEIPT_TOKEN
            or self._issued.get(id(receipt)) is not receipt
        ):
            raise TypeError("process authority receipt is not exact factory membership")
        role = next(
            (
                name for name, key_id in self._role_key_ids().items()
                if receipt.signing_key_id == key_id
            ),
            None,
        )
        if role is None:
            raise ValueError("process authority receipt signing key is untrusted")
        expected_roles = {
            LAUNCH_RECEIPT_KIND: "supervisor",
            "SupervisorTimeoutReceipt": "supervisor",
            OPERATIONAL_ERROR_RECEIPT_KIND: "supervisor",
            **{kind: "supervisor" for kind in TERMINAL_EVIDENCE_FILES},
            "RecoveryResolutionReceipt": "supervisor",
            "ProcessLiveRequirementAssignmentReceipt": "worker",
            "OperationalCheckpointReceipt": "worker",
            BOOTSTRAP_CHECKPOINT_KIND: "supervisor",
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

    def validate_supervisor_canonical_bundle(
        self, bundle: Mapping[str, Any], *, launch: SignedProcessAuthorityReceipt,
        outcome: Outcome, error_kind: Optional[str],
    ) -> Mapping[str, Any]:
        """supervisor が TIMEOUT / ERROR の終端として封をした canonical bundle。"""
        from scripts.function_tracer_pcode.authority.decision.canonical_result import (
            supervisor_canonical_result_payload_preimage,
        )

        self.validate(launch)
        return self.validate_child_canonical_bundle(
            bundle,
            result_payload_preimage=supervisor_canonical_result_payload_preimage(
                launch, outcome=outcome, error_kind=error_kind
            ),
        )

    def validate_child_canonical_bundle(
        self, bundle: Mapping[str, Any], *,
        result_payload_preimage: Mapping[str, Any],
    ) -> Mapping[str, Any]:
        """canonical bundle の封を supervisor 鍵で検証する（child の envelope にも使う）。

        封の検証そのものは canonical bundle の owner（``canonical_result``）が持ち、
        factory は鍵を渡すだけ。factory からその owner への依存は Issue #165 より
        前からある（owner を下層へ移す課題は #198）。
        """
        from scripts.function_tracer_pcode.authority.decision.canonical_result import (
            validate_canonical_result_finalization_bundle,
        )
        from scripts.function_tracer_pcode.authority.seal_work import SealWorkBudget

        return validate_canonical_result_finalization_bundle(
            bundle,
            work=SealWorkBudget.for_result(),
            result_payload_preimage=result_payload_preimage,
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
        return self._issue(LAUNCH_RECEIPT_KIND, payload, signer_role="supervisor")

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
        from scripts.function_tracer_pcode.authority.lifecycle.reducer import ShadowLifecycleReducer

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
        checkpoint = self._issue(BOOTSTRAP_CHECKPOINT_KIND, {
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
            launch.receipt_kind != LAUNCH_RECEIPT_KIND
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
            launch.receipt_kind != LAUNCH_RECEIPT_KIND
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
        if (prior_state, next_state) not in ALLOWED_TRANSITIONS:
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
        from scripts.function_tracer_pcode.authority.decision.canonical_result import (
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
            work=_supervisor_seal_work(),
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
        canonical = self.validate_supervisor_canonical_bundle(
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
        # Issue #110: 契約の外の stream は検証を始めない（O(1)）
        from scripts.function_tracer_pcode.authority.event_contract import (
            require_events_within_contract,
        )

        require_events_within_contract(len(segment.composite_stream.events))
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
            and receipt.receipt_kind == LAUNCH_RECEIPT_KIND
        }
        if set(launches_by_digest) != {bundle.launch_receipt_digest}:
            raise ValueError("timeout bundle launch authority is not unique")
        launch = launches_by_digest[bundle.launch_receipt_digest]
        canonical = self.validate_supervisor_canonical_bundle(
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
        if launch.receipt_kind != LAUNCH_RECEIPT_KIND:
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
            OPERATIONAL_ERROR_RECEIPT_KIND, payload,
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
            launch.receipt_kind != LAUNCH_RECEIPT_KIND
            or error.receipt_kind != OPERATIONAL_ERROR_RECEIPT_KIND
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
        # Issue #110: 契約の外の stream は検証を始めない（O(1)）
        from scripts.function_tracer_pcode.authority.event_contract import (
            require_events_within_contract,
        )

        require_events_within_contract(len(segment.composite_stream.events))
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
            error.receipt_kind != OPERATIONAL_ERROR_RECEIPT_KIND
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
        from scripts.function_tracer_pcode.authority.decision.canonical_result import (
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
            work=_supervisor_seal_work(),
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
        canonical = self.validate_supervisor_canonical_bundle(
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


@dataclass(frozen=True)
class ResolvedChain:
    """意味検証を通った閉じた checkpoint chain（``validate_resolved_chain_members``）。"""

    checkpoint: SignedProcessAuthorityReceipt
    prefix: EventStreamPrefixView
    resolved: SignedProcessAuthorityReceipt
    recovery: Optional[SignedProcessAuthorityReceipt]


#: Issue #165: この thread が今持っている flock（lock file の path）。flock は
#: open file description ごとなので、同じ thread が同じ file を別 fd でもう一度
#: 取ると自分を待って止まる。入れ子の取得は例外にする（``_exclusive_flock``）。
#: 別の thread は例外にせず、flock で待つ（thread ごとの記録）。
_HELD_LOCKS = threading.local()
_OWNERSHIP_TOKEN = object()


def _supervisor_seal_work() -> Any:
    """Issue #110: 1 回の terminal の封印（supervisor の固定の形の preimage）の有限の作業量。"""

    from scripts.function_tracer_pcode.authority.seal_work import SealWorkBudget

    return SealWorkBudget.for_supervisor()


def _held(kind: str) -> set[str]:
    held = getattr(_HELD_LOCKS, kind, None)
    if held is None:
        held = set()
        setattr(_HELD_LOCKS, kind, held)
    return held


class StoreLockReentry(RuntimeError):
    """同じ process が同じ lock を入れ子で取ろうとした（deadlock の代わりに落とす）。"""


def _lock_key(path: Path) -> str:
    return str(Path(path).resolve())


@contextmanager
def _exclusive_flock(path: Path, kind: str) -> Iterator[None]:
    held = _held(kind)
    key = _lock_key(path)
    if key in held:
        raise StoreLockReentry(f"{Path(path).name} is already held by this process")
    with Path(path).open("a+b") as lock_file:
        fcntl.flock(lock_file.fileno(), fcntl.LOCK_EX)
        held.add(key)
        try:
            yield
        finally:
            held.discard(key)
            fcntl.flock(lock_file.fileno(), fcntl.LOCK_UN)


@dataclass(frozen=True)
class SupervisorOwnership:
    """``DurableCheckpointStore.supervisor_ownership`` の中でだけ有効な証明。"""

    store: "DurableCheckpointStore" = field(repr=False)
    key: str
    _token: object = field(default=None, repr=False, compare=False)

    @property
    def held(self) -> bool:
        return self.key in _held("owner")


class DurableCheckpointStore:
    """Atomic, fsync-backed state/continuation store with a nonce-local lock."""

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
        self.lock_path = self.directory / ".checkpoint-transaction.lock"
        self.lock_directory_digest = authority_digest({
            "checkpoint_directory": str(self.directory.resolve())
        })
        self.codec = StrictV2JsonCodec(
            reason_registry=PROCESS_DURABLE_REASON_REGISTRY,
            recovery_registry=PROCESS_DURABLE_RECOVERY_REGISTRY,
        )

    @contextmanager
    def _locked(self) -> Iterator[None]:
        """store の flock を 1 回だけ取る（入れ子は例外。自分を待って止まらない）。"""
        self.root.mkdir(parents=True, exist_ok=True)
        with _exclusive_flock(self.lock_path, "store"):
            yield

    def _assert_locked(self) -> None:
        if _lock_key(self.lock_path) not in _held("store"):
            raise RuntimeError("store operation requires the store flock")

    @contextmanager
    def supervisor_ownership(self) -> Iterator["SupervisorOwnership"]:
        """Issue #165: この store を終端へ進める supervisor を 1 つに限る。

        store の flock（worker と共有・短時間）とは別の lock で、supervisor が
        起動から projection を書くまで持つ。2 つ目の supervisor（restart の
        重複起動）はここで先の supervisor の終了を待ち、その後で同じ durable
        evidence から同じ終端を導く。child は持たない（fd は継承されない）ので、
        kill / wait の間これを持っていても worker の store 操作は止まらない。
        """
        path = self.directory / ".supervisor-owner.lock"
        with _exclusive_flock(path, "owner"):
            ownership = SupervisorOwnership(self, _lock_key(path), _OWNERSHIP_TOKEN)
            yield ownership

    def _require_ownership(self, ownership: "SupervisorOwnership") -> None:
        if (
            type(ownership) is not SupervisorOwnership
            or ownership._token is not _OWNERSHIP_TOKEN
            or ownership.store is not self
            or ownership.key not in _held("owner")
        ):
            raise RuntimeError("supervisor-only store write requires held ownership")

    # -- Issue #165: supervisor の終了観測（D / E）と終端 transaction ----------

    def persist_deadline(
        self, ownership: "SupervisorOwnership", receipt: SignedProcessAuthorityReceipt,
    ) -> None:
        """D を signal より前に durable にする。**store の flock は取らない。**

        deadline に達した worker は store の transaction の中で止まっていることが
        ある（flock を持ったまま）。D の書込みがその flock を待つと kill が
        始まらない。D を書くのは owner の supervisor だけ（worker は書かない）
        なので、排他は ``ownership`` が持つ。
        """
        self._require_ownership(ownership)
        launch = self._read_launch()
        self.factory.validate(receipt)
        terminal_evidence.validate_deadline(receipt, launch)
        self._atomic_write(
            self.directory / layout.DEADLINE,
            self._bytes(receipt), identical_ok=True,
        )

    def record_child_exit(
        self, ownership: "SupervisorOwnership", build: Any,
    ) -> SignedProcessAuthorityReceipt:
        """E を書く。anchor と envelope の観測・署名・書込みを 1 回の flock で行う。

        ``build(launch=, deadline=, anchor=, envelope=)`` は署名済み E を返す
        （rc / signal / disposition は呼び出し側が wait で観測した値）。E は
        attempt ごとに 1 つで、既にあれば同じ bytes でない限り拒否する。
        """
        self._require_ownership(ownership)
        with self._locked():
            launch = self._read_launch()
            deadline = self._read_terminal_evidence_locked(
                terminal_evidence.DEADLINE_RECEIPT_KIND
            )
            if deadline is not None:
                terminal_evidence.validate_deadline(deadline, launch)
            receipt = build(
                launch=launch, deadline=deadline,
                anchor=self._observe_anchor_locked(),
                envelope=self._observe_envelope_locked(),
            )
            self.factory.validate(receipt)
            terminal_evidence.validate_child_exit(receipt, launch, deadline)
            self._atomic_write(
                self.directory / layout.CHILD_EXIT,
                self._bytes(receipt), identical_ok=True,
            )
            return receipt

    @contextmanager
    def owned_lock(self, ownership: "SupervisorOwnership") -> Iterator[None]:
        """owner の supervisor として store の flock を 1 回取る（終端処理の 1 手）。

        何をするか（snapshot の再読・判定・書込み）は ``terminal_transaction``
        が持つ。store は lock と ownership の検査だけを提供する。
        """
        self._require_ownership(ownership)
        with self._locked():
            yield

    def _read_terminal_evidence_locked(
        self, kind: str,
    ) -> Optional[SignedProcessAuthorityReceipt]:
        path = self.directory / terminal_evidence.TERMINAL_EVIDENCE_FILES[kind]
        if not path.exists():
            return None
        receipt = self.factory.decode(json.loads(path.read_text(encoding="utf-8")))
        if receipt.receipt_kind != kind:
            raise terminal_evidence.TerminalEvidenceInvalid(
                f"{path.name} does not hold {kind}"
            )
        return receipt

    def _observe_anchor_locked(self) -> "terminal_evidence.CheckpointAnchor":
        """child 終了の時点の live checkpoint（解釈はせず、読めたものを名指す）。"""
        anchor = terminal_evidence.CheckpointAnchor
        try:
            if self._pending_active_path.exists():
                checkpoint, _prefix, _stream, _bytes = (
                    self._decode_active_transaction_locked()
                )
                transaction = json.loads(
                    self._pending_active_path.read_text(encoding="utf-8")
                )["transaction_digest"]
                return anchor(
                    terminal_evidence.ANCHOR_PENDING_ACTIVE,
                    checkpoint_receipt_digest=checkpoint.receipt_digest,
                    transaction_digest=transaction,
                )
            if (self.directory / layout.STATE).exists():
                state = self.read_state()
                checkpoint = self.factory.decode(json.loads(
                    (self.directory / layout.CHECKPOINT).read_text(encoding="utf-8")
                ))
                return anchor(
                    terminal_evidence.ANCHOR_CHAIN,
                    checkpoint_receipt_digest=checkpoint.receipt_digest,
                    state_receipt_digest=state.receipt_digest,
                    state=state.payload["state"],
                )
        except (OSError, KeyError, TypeError, ValueError) as exc:
            return anchor(
                terminal_evidence.ANCHOR_UNREADABLE,
                detail=f"{type(exc).__name__}: {exc}"[:500],
            )
        residue = live_chain_members(self.directory)
        if residue:
            return anchor(
                terminal_evidence.ANCHOR_UNREADABLE,
                detail=f"chain members without state: {list(residue)}",
            )
        return anchor(terminal_evidence.ANCHOR_NONE)

    def _observe_envelope_locked(self) -> "terminal_evidence.EnvelopeObservation":
        path = self.directory / layout.RESULT_ENVELOPE
        if not path.exists():
            return terminal_evidence.EnvelopeObservation(False, None)
        # Issue #110: the same bounded read as the terminal snapshot (the digest
        # of at most the contract bound + 1 bytes; whole-file within bounds).
        return terminal_evidence.EnvelopeObservation(
            True, read_canonical_envelope(path).sha256,
        )

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

    def _write_json_locked(self, path: Path, payload: Mapping[str, Any]) -> None:
        """supervisor の durable JSON（同じ bytes の再書込みだけ許す）。"""
        self._assert_locked()
        self._atomic_write(
            path,
            json.dumps(dict(payload), sort_keys=True, separators=(",", ":")).encode("utf-8")
            + b"\n",
            identical_ok=True,
        )

    def _atomic_replace(self, path: Path, data: bytes) -> None:
        fd, temporary = tempfile.mkstemp(prefix=".replace-", dir=str(path.parent))
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

    @property
    def _pending_active_path(self) -> Path:
        return self.directory / layout.PENDING_ACTIVE_TRANSACTION

    def _active_transaction_bytes(
        self, receipt: SignedProcessAuthorityReceipt,
        prefix_stream: SealedEventStream,
    ) -> bytes:
        body = {
            "schema": ACTIVE_TRANSACTION_SCHEMA,
            "authority_kind": "DurableActiveCheckpointTransaction",
            "invocation_nonce": self.invocation_nonce,
            "checkpoint_receipt": receipt.to_dict(),
            "checkpoint_receipt_digest": receipt.receipt_digest,
            "launch_receipt_digest": receipt.payload["launch_receipt_digest"],
            "prefix_stream": json.loads(self.codec.dumps(prefix_stream)),
            "prefix_authority_digest": receipt.payload["prefix_digest"],
            "prior_resolved_receipt_digest": receipt.payload.get(
                "prior_resolved_receipt_digest"
            ),
        }
        payload = {**body, "transaction_digest": authority_digest(body)}
        return json.dumps(
            payload, sort_keys=True, separators=(",", ":")
        ).encode("utf-8") + b"\n"

    def _decode_active_transaction_locked(
        self,
    ) -> tuple[SignedProcessAuthorityReceipt, EventStreamPrefixView, bytes, bytes]:
        try:
            payload = json.loads(
                self._pending_active_path.read_text(encoding="utf-8")
            )
        except Exception as exc:
            raise ValueError("pending ACTIVE transaction is missing or invalid") from exc
        required = {
            "schema", "authority_kind", "invocation_nonce",
            "checkpoint_receipt", "checkpoint_receipt_digest",
            "launch_receipt_digest", "prefix_stream",
            "prefix_authority_digest", "prior_resolved_receipt_digest",
            "transaction_digest",
        }
        body = {
            key: value for key, value in payload.items()
            if key != "transaction_digest"
        }
        if (
            set(payload) != required
            or payload["schema"] != ACTIVE_TRANSACTION_SCHEMA
            or payload["authority_kind"]
            != "DurableActiveCheckpointTransaction"
            or payload["invocation_nonce"] != self.invocation_nonce
            or payload["transaction_digest"] != authority_digest(body)
        ):
            raise ValueError("pending ACTIVE transaction authority drifted")
        try:
            checkpoint = self.factory.decode(payload["checkpoint_receipt"])
            stream = self.codec.loads(json.dumps(
                payload["prefix_stream"], sort_keys=True, separators=(",", ":")
            ))
            prefix = EventStreamPrefixView.from_sealed_stream(stream)
            launch = self.factory.decode(json.loads(
                (self.directory / layout.LAUNCH).read_text(encoding="utf-8")
            ))
        except Exception as exc:
            raise ValueError("pending ACTIVE transaction members are invalid") from exc
        if (
            launch.receipt_kind != LAUNCH_RECEIPT_KIND
            or launch.payload["execution_nonce"] != self.invocation_nonce
            or payload["invocation_nonce"] != launch.payload["execution_nonce"]
        ):
            raise ValueError(
                "pending ACTIVE transaction launch authority differs"
            )
        prefix.validate()
        if (
            checkpoint.payload["state"] != CheckpointState.ACTIVE.value
            or checkpoint.receipt_digest
            != payload["checkpoint_receipt_digest"]
            or checkpoint.payload["launch_receipt_digest"]
            != payload["launch_receipt_digest"]
            or checkpoint.payload["launch_receipt_digest"]
            != launch.receipt_digest
            or checkpoint.payload["prefix_digest"]
            != payload["prefix_authority_digest"]
            or checkpoint.payload["prefix_digest"]
            != prefix.prefix_authority_digest
            or checkpoint.payload.get("prior_resolved_receipt_digest")
            != payload["prior_resolved_receipt_digest"]
        ):
            raise ValueError("pending ACTIVE transaction members do not join")
        return (
            checkpoint,
            prefix,
            self.codec.dumps(stream).encode("utf-8"),
            self._bytes(checkpoint),
        )

    def _remove_pending_active_locked(self) -> None:
        self._pending_active_path.unlink()
        directory_fd = os.open(self.directory, os.O_RDONLY)
        try:
            os.fsync(directory_fd)
        finally:
            os.close(directory_fd)

    def persist_launch(self, receipt: SignedProcessAuthorityReceipt) -> None:
        self.factory.validate(receipt)
        if receipt.receipt_kind != LAUNCH_RECEIPT_KIND:
            raise ValueError("launch store requires SupervisorLaunchReceipt")
        if receipt.payload["execution_nonce"] != self.invocation_nonce:
            raise ValueError("launch execution nonce differs from checkpoint directory")
        with self._locked():
            self._atomic_write(self.directory / layout.LAUNCH, self._bytes(receipt))

    def resolved_predecessor(self) -> Optional[SignedProcessAuthorityReceipt]:
        """Return the exact completed checkpoint that a new ACTIVE must extend."""

        with self._locked():
            state_path = self.directory / layout.STATE
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
        destination = history_destination(resolved.receipt_digest)
        history = self.directory / destination
        # Issue #165: chain の member は ``CHAIN_MEMBERS`` の 1 つの表で決め、移動は
        # ``checkpoint_archive`` の手順（os.replace と両側の directory fsync）で行う
        # （supervisor の recovery で閉じた chain は recovery-resolution も連れて行く）。
        for name in CHAIN_MEMBER_NAMES:
            source = self.directory / name
            if (history / name).exists():
                if source.exists():
                    if source.read_bytes() != (history / name).read_bytes():
                        raise ValueError(
                            "resolved checkpoint history member differs"
                        )
                    source.unlink()
                    fsync_directory(self.directory)
                continue
            if source.exists():
                move_member(self.directory, destination, name)
        try:
            archived = self.factory.decode(json.loads(
                (history / layout.STATE).read_text(encoding="utf-8")
            ))
        except (OSError, KeyError, TypeError, ValueError) as exc:
            raise ValueError(
                "resolved checkpoint history is incomplete or invalid"
            ) from exc
        if archived.receipt_digest != resolved.receipt_digest:
            raise ValueError("resolved checkpoint history authority differs")

    def _commit_pending_active_locked(
        self,
    ) -> tuple[SignedProcessAuthorityReceipt, EventStreamPrefixView]:
        checkpoint, prefix, prefix_bytes, checkpoint_bytes = (
            self._decode_active_transaction_locked()
        )
        state_path = self.directory / layout.STATE
        predecessor_digest = checkpoint.payload.get(
            "prior_resolved_receipt_digest"
        )
        already_committed = False
        if state_path.exists():
            current = self.factory.decode(json.loads(
                state_path.read_text(encoding="utf-8")
            ))
            if current.receipt_digest == checkpoint.receipt_digest:
                already_committed = True
            elif (
                current.payload.get("state") != CheckpointState.RESOLVED.value
                or current.receipt_digest != predecessor_digest
            ):
                raise ValueError(
                    "pending ACTIVE transaction does not extend committed state"
                )
            else:
                self._archive_resolved_checkpoint_locked(current)
        elif predecessor_digest is not None:
            history_state = (
                history_directory(self.directory, predecessor_digest) / layout.STATE
            )
            try:
                predecessor = self.factory.decode(json.loads(
                    history_state.read_text(encoding="utf-8")
                ))
            except Exception as exc:
                raise ValueError(
                    "pending ACTIVE transaction lost its resolved predecessor"
                ) from exc
            if (
                predecessor.receipt_digest != predecessor_digest
                or predecessor.payload.get("state")
                != CheckpointState.RESOLVED.value
            ):
                raise ValueError(
                    "pending ACTIVE transaction predecessor history differs"
                )

        members = (
            (self.directory / layout.PREFIX_STREAM, prefix_bytes),
            (self.directory / layout.CHECKPOINT, checkpoint_bytes),
        )
        for path, expected in members:
            if path.exists() and path.read_bytes() != expected:
                raise ValueError(
                    "pending ACTIVE transaction conflicts with durable member"
                )
        if already_committed and any(not path.exists() for path, _ in members):
            raise ValueError(
                "committed ACTIVE transaction lost a durable member"
            )
        for path, expected in members:
            if not path.exists():
                self._atomic_write(path, expected)
        if not already_committed:
            self._atomic_replace(state_path, checkpoint_bytes)
        self._remove_pending_active_locked()
        return checkpoint, prefix

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
            self._persist_active_locked(receipt, prefix)

    def _persist_active_locked(
        self, receipt: SignedProcessAuthorityReceipt,
        prefix: EventStreamPrefixView,
    ) -> None:
        self._assert_locked()
        self.factory.validate(receipt)
        prefix.validate()
        if (
            receipt.payload["state"] != CheckpointState.ACTIVE.value
            or receipt.payload["prefix_digest"] != prefix.prefix_authority_digest
        ):
            raise ValueError("ACTIVE checkpoint authority differs from its prefix")
        launch_path = self.directory / layout.LAUNCH
        try:
            launch = self.factory.decode(json.loads(
                launch_path.read_text(encoding="utf-8")
            ))
        except (OSError, KeyError, TypeError, ValueError) as exc:
            raise ValueError("ACTIVE checkpoint lacks durable launch authority") from exc
        if receipt.payload["launch_receipt_digest"] != launch.receipt_digest:
            raise ValueError("ACTIVE checkpoint launch binding differs")
        state_path = self.directory / layout.STATE
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
            self._pending_active_path,
            self._active_transaction_bytes(receipt, prefix_stream),
        )
        self._commit_pending_active_locked()

    def rollback_active(
        self, receipt: SignedProcessAuthorityReceipt,
        prefix: EventStreamPrefixView,
    ) -> None:
        """Remove one exact ACTIVE transaction that has no committed event."""

        self.factory.validate(receipt)
        prefix.validate()
        if (
            receipt.payload["state"] != CheckpointState.ACTIVE.value
            or receipt.payload["prefix_digest"] != prefix.prefix_authority_digest
        ):
            raise ValueError("ACTIVE rollback authority differs")
        with self._locked():
            if self._pending_active_path.exists():
                pending, pending_prefix, _prefix_bytes, _checkpoint_bytes = (
                    self._decode_active_transaction_locked()
                )
                if (
                    pending.receipt_digest != receipt.receipt_digest
                    or pending_prefix != prefix
                ):
                    raise ValueError(
                        "pending ACTIVE rollback authority differs"
                    )
                self._commit_pending_active_locked()

            state_path = self.directory / layout.STATE
            checkpoint_path = self.directory / layout.CHECKPOINT
            prefix_path = self.directory / layout.PREFIX_STREAM
            active_paths = (state_path, checkpoint_path, prefix_path)
            if not any(path.exists() for path in active_paths):
                return
            if not all(path.exists() for path in active_paths):
                raise ValueError("ACTIVE rollback found partial durable authority")
            try:
                current = self.factory.decode(json.loads(
                    state_path.read_text(encoding="utf-8")
                ))
                checkpoint = self.factory.decode(json.loads(
                    checkpoint_path.read_text(encoding="utf-8")
                ))
                stream = self.codec.loads(prefix_path.read_text(encoding="utf-8"))
                committed_prefix = EventStreamPrefixView.from_sealed_stream(stream)
            except Exception as exc:
                raise ValueError(
                    "ACTIVE rollback durable authority is invalid"
                ) from exc
            if (
                current.receipt_digest != receipt.receipt_digest
                or checkpoint.receipt_digest != receipt.receipt_digest
                or committed_prefix != prefix
            ):
                raise ValueError("committed ACTIVE rollback authority differs")
            if any(
                (self.directory / name).exists()
                for name in (
                    layout.CONTINUATION, layout.CONTINUATION_STREAM, layout.READY,
                    layout.RECOVERY_RESOLUTION, layout.CLAIMED, layout.TIMEOUT,
                    layout.TERMINAL_SEGMENT, layout.TERMINAL_STREAM,
                )
            ):
                raise ValueError(
                    "ACTIVE rollback cannot remove terminalized authority"
                )

            predecessor_digest = receipt.payload.get(
                "prior_resolved_receipt_digest"
            )
            history = None
            predecessor_names: tuple[str, ...] = ()
            if predecessor_digest is not None:
                history = history_directory(self.directory, predecessor_digest)
                predecessor_names = tuple(
                    spec.name for spec in CHAIN_MEMBERS
                    if spec.required or (history / spec.name).exists()
                )
                if any(
                    not (history / name).exists()
                    for name in predecessor_names
                ):
                    raise ValueError(
                        "ACTIVE rollback predecessor history is incomplete"
                    )

            for path in active_paths:
                path.unlink()

            if history is not None:
                for name in predecessor_names:
                    destination = self.directory / name
                    if destination.exists():
                        raise ValueError(
                            "ACTIVE rollback predecessor destination exists"
                        )
                    os.replace(history / name, destination)
                history.rmdir()

            directory_fd = os.open(self.directory, os.O_RDONLY)
            try:
                os.fsync(directory_fd)
            finally:
                os.close(directory_fd)

    def rematerialize_active_prefix(self) -> EventStreamPrefixView:
        try:
            checkpoint = self.factory.decode(json.loads(
                (self.directory / layout.CHECKPOINT).read_text(encoding="utf-8")
            ))
            stream = self.codec.loads(
                (self.directory / layout.PREFIX_STREAM).read_text(
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
        path = self.directory / layout.STATE
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
        stream_bytes = self.codec.dumps(continuation_stream).encode("utf-8")
        self._atomic_write(
            self.directory / layout.CONTINUATION_STREAM, stream_bytes,
            identical_ok=True,
        )
        self._atomic_write(
            self.directory / layout.CONTINUATION, self._bytes(receipt),
            identical_ok=True,
        )

    def _replace_state_locked(
        self, replacement: SignedProcessAuthorityReceipt,
    ) -> None:
        path = self.directory / layout.STATE
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
                self.directory / layout.READY, self._bytes(ready)
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

    def _close_continuation_locked(
        self, *, active: SignedProcessAuthorityReceipt,
        prefix: EventStreamPrefixView,
    ) -> SignedProcessAuthorityReceipt:
        """durable な worker continuation で ACTIVE chain を閉じる（RESOLVED まで）。

        worker が ``ready.json`` を公開した直後（``state.json`` を READY へ
        替える前）に止まった store では、その worker の READY をそのまま使う
        （supervisor の READY で書き替えない）。どちらの READY からも同じ
        recovery で RESOLVED にする。
        """
        self._assert_locked()
        self.factory.validate(active)
        prefix.validate()
        current = self.read_state()
        if (
            current.receipt_digest != active.receipt_digest
            or active.payload["state"] != CheckpointState.ACTIVE.value
            or active.payload["prefix_digest"] != prefix.prefix_authority_digest
        ):
            raise ValueError("continuation close lost ACTIVE-state CAS")
        durable, _stream = self.rematerialize_worker_continuation(prefix=prefix)
        if durable.payload["checkpoint_receipt_digest"] != active.receipt_digest:
            raise ValueError("durable continuation does not continue this checkpoint")
        ready_path = self.directory / layout.READY
        if ready_path.exists():
            ready = self.factory.decode(json.loads(ready_path.read_text(encoding="utf-8")))
            if (
                ready.receipt_kind != "CheckpointStateTransitionReceipt"
                or ready.payload["state"] != CheckpointState.COMPLETION_READY.value
                or ready.payload["prior_state_receipt_digest"] != active.receipt_digest
                or ready.payload["continuation_digest"] != durable.receipt_digest
            ):
                raise ValueError("durable READY does not close this continuation")
        else:
            recovery = self._write_recovery_resolution_locked(active, durable)
            ready = self.factory._issue_transition(
                prior=active, next_state=CheckpointState.COMPLETION_READY,
                lock_directory_digest=self.lock_directory_digest,
                continuation_digest=durable.receipt_digest,
                recovery_resolution=recovery,
                _capability=_TRANSITION_CAPABILITY_TOKEN,
            )
            self._atomic_write(ready_path, self._bytes(ready), identical_ok=True)
        self._replace_state_locked(ready)
        return self._recover_completion_ready_locked(ready=ready, prefix=prefix)

    def _write_recovery_resolution_locked(
        self, active: SignedProcessAuthorityReceipt,
        continuation: SignedProcessAuthorityReceipt,
    ) -> SignedProcessAuthorityReceipt:
        recovery = self.factory.issue_recovery_resolution(
            active=active, continuation=continuation,
            lock_directory_digest=self.lock_directory_digest,
        )
        self._atomic_write(
            self.directory / layout.RECOVERY_RESOLUTION,
            self._bytes(recovery), identical_ok=True,
        )
        return recovery

    def _claim_timeout_locked(
        self, *, active: SignedProcessAuthorityReceipt,
        prefix: EventStreamPrefixView, kill_disposition: str,
    ) -> SignedProcessAuthorityReceipt:
        """continuation の無い ACTIVE を supervisor の timeout として claim する。

        claim は ``kill_disposition``（E が観測したもの）から決定的に作るので、
        ``claimed.json`` の公開後・CAS 前に止まった store でも同じ bytes を
        書き直すだけになる（違う claim があれば既存の衝突検査で拒否）。
        """
        self._assert_locked()
        self.factory.validate(active)
        prefix.validate()
        if active.payload["prefix_digest"] != prefix.prefix_authority_digest:
            raise ValueError("supervisor claim prefix differs from checkpoint")
        current = self.read_state()
        if current.receipt_digest != active.receipt_digest:
            raise ValueError("supervisor timeout lost checkpoint CAS")
        if (self.directory / layout.CONTINUATION).exists():
            raise ValueError("a durable continuation exists; the checkpoint closes instead")
        claimed = self.factory._issue_transition(
            prior=active, next_state=CheckpointState.TIMED_OUT_CLAIMED,
            lock_directory_digest=self.lock_directory_digest,
            kill_disposition=kill_disposition,
            _capability=_TRANSITION_CAPABILITY_TOKEN,
        )
        self._atomic_write(
            self.directory / layout.CLAIMED, self._bytes(claimed), identical_ok=True,
        )
        self._replace_state_locked(claimed)
        return claimed

    def _recover_completion_ready_locked(
        self, *, ready: SignedProcessAuthorityReceipt,
        prefix: EventStreamPrefixView,
    ) -> SignedProcessAuthorityReceipt:
        """Resolve the durable worker continuation after the READY crash window."""
        self._assert_locked()
        self.factory.validate(ready)
        prefix.validate()
        current = self.read_state()
        if (
            current.receipt_digest != ready.receipt_digest
            or ready.payload["state"] != CheckpointState.COMPLETION_READY.value
        ):
            raise ValueError("completion recovery lost READY-state CAS")
        try:
            checkpoint = self.factory.decode(json.loads(
                (self.directory / layout.CHECKPOINT).read_text(encoding="utf-8")
            ))
        except (OSError, KeyError, TypeError, ValueError) as exc:
            raise ValueError("READY recovery authority is missing or invalid") from exc
        continuation, _stream = self.rematerialize_worker_continuation(prefix=prefix)
        if (
            checkpoint.payload["state"] != CheckpointState.ACTIVE.value
            or ready.payload["prior_state_receipt_digest"]
            != checkpoint.receipt_digest
            or ready.payload["continuation_digest"]
            != continuation.receipt_digest
        ):
            raise ValueError("READY recovery chain differs from durable authority")
        recovery = self._write_recovery_resolution_locked(checkpoint, continuation)
        self._atomic_write(
            self.directory / layout.READY, self._bytes(ready), identical_ok=True,
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
        chain = self.validate_resolved_chain_members(
            directory_reader(self.directory),
            present=live_chain_members(self.directory),
        )
        if chain.prefix != prefix:
            raise ValueError("durable RESOLVED chain prefix differs")
        return chain.resolved

    def validate_resolved_chain_members(
        self, read: Any, *, present: tuple[str, ...],
    ) -> "ResolvedChain":
        """1 つの閉じた chain を member の bytes から意味検証する（置き場所を問わない）。

        Issue #165: live の chain も、A archive の途中で live / history に
        分かれた chain も、同じ検証を通す。``read(name)`` は member の bytes を
        返し、``present`` はいま存在する member 名（任意 member の有無）。
        """
        missing = {
            spec.name for spec in CHAIN_MEMBERS if spec.required
        } - set(present)
        if missing:
            raise ValueError(f"resolved chain lacks members {sorted(missing)}")

        def receipt(name: str) -> SignedProcessAuthorityReceipt:
            try:
                return self.factory.decode(json.loads(read(name).decode("utf-8")))
            except (OSError, UnicodeDecodeError, KeyError, TypeError, ValueError) as exc:
                raise ValueError(f"persisted {name} authority is invalid") from exc

        def stream(name: str) -> SealedEventStream:
            try:
                return self.codec.loads(read(name).decode("utf-8"))
            except (OSError, UnicodeDecodeError, KeyError, TypeError, ValueError) as exc:
                raise ValueError(f"persisted {name} stream is invalid") from exc

        launch = self._read_launch()
        checkpoint = receipt(layout.CHECKPOINT)
        prefix = EventStreamPrefixView.from_sealed_stream(
            stream(layout.PREFIX_STREAM)
        )
        prefix.validate()
        continuation = receipt(layout.CONTINUATION)
        continuation_stream = stream(layout.CONTINUATION_STREAM)
        self.factory.validate_worker_continuation(
            continuation, prefix, continuation_stream
        )
        ready = receipt(layout.READY)
        resolved = receipt(layout.STATE)
        recovery = (
            receipt(layout.RECOVERY_RESOLUTION)
            if layout.RECOVERY_RESOLUTION in present else None
        )
        recovery_digest = None if recovery is None else recovery.receipt_digest
        if (
            checkpoint.payload["state"] != CheckpointState.ACTIVE.value
            or checkpoint.payload["prefix_digest"] != prefix.prefix_authority_digest
            or checkpoint.payload["launch_receipt_digest"] != launch.receipt_digest
            or ready.payload["state"] != CheckpointState.COMPLETION_READY.value
            or ready.payload["prior_state_receipt_digest"]
            != checkpoint.receipt_digest
            or ready.payload["continuation_digest"] != continuation.receipt_digest
            or continuation.payload["checkpoint_receipt_digest"]
            != checkpoint.receipt_digest
            or continuation.payload["operational_authority_root_digest"]
            != checkpoint.payload["operational_authority_root_digest"]
            or resolved.payload["state"] != CheckpointState.RESOLVED.value
            or resolved.payload["prior_state_receipt_digest"] != ready.receipt_digest
            or resolved.payload["continuation_digest"]
            != continuation.receipt_digest
            # 閉じたのが supervisor の recovery なら、その receipt もこの chain を
            # 名指す（別 chain の recovery を連れて行かない）。
            or resolved.payload["recovery_resolution_receipt_digest"] != recovery_digest
            or (
                recovery is not None
                and (
                    recovery.receipt_kind != "RecoveryResolutionReceipt"
                    or recovery.payload["checkpoint_receipt_digest"]
                    != checkpoint.receipt_digest
                    or recovery.payload["continuation_digest"]
                    != continuation.receipt_digest
                )
            )
        ):
            raise ValueError("durable RESOLVED chain is inconsistent")
        return ResolvedChain(checkpoint, prefix, resolved, recovery)

    def _read_launch(self) -> SignedProcessAuthorityReceipt:
        try:
            launch = self.factory.decode(json.loads(
                (self.directory / layout.LAUNCH).read_text(encoding="utf-8")
            ))
        except (OSError, KeyError, TypeError, ValueError) as exc:
            raise ValueError("durable launch authority is missing or invalid") from exc
        if (
            launch.receipt_kind != LAUNCH_RECEIPT_KIND
            or launch.payload["execution_nonce"] != self.invocation_nonce
        ):
            raise ValueError("durable launch authority differs from this store")
        return launch

    def rematerialize_worker_continuation(
        self, *, prefix: EventStreamPrefixView,
    ) -> tuple[SignedProcessAuthorityReceipt, SealedEventStream]:
        prefix.validate()
        try:
            continuation = self.factory.decode(json.loads(
                (self.directory / layout.CONTINUATION).read_text(encoding="utf-8")
            ))
            continuation_stream = self.codec.loads(
                (self.directory / layout.CONTINUATION_STREAM).read_text(
                    encoding="utf-8"
                )
            )
        except Exception as exc:
            raise ValueError("persisted worker continuation is invalid") from exc
        self.factory.validate_worker_continuation(
            continuation, prefix, continuation_stream
        )
        return continuation, continuation_stream

    def _finalize_timeout_locked(
        self, *, claimed: SignedProcessAuthorityReceipt,
        timeout: SignedProcessAuthorityReceipt,
        segment: SupervisorTerminalSegment,
        prefix: EventStreamPrefixView,
    ) -> SignedProcessAuthorityReceipt:
        self._assert_locked()
        self.factory.validate(claimed)
        self.factory.validate(timeout)
        segment.validate(prefix, timeout)
        current = self.read_state()
        if current.receipt_digest != claimed.receipt_digest:
            raise ValueError("timeout finalization lost claimed-state CAS")
        self._atomic_write(
            self.directory / layout.TIMEOUT, self._bytes(timeout),
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
            self.directory / layout.TERMINAL_SEGMENT, segment_payload,
            identical_ok=True,
        )
        self._atomic_write(
            self.directory / layout.TERMINAL_STREAM,
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
                (self.directory / layout.TERMINAL_SEGMENT).read_text(
                    encoding="utf-8"
                )
            )
            stream = self.codec.loads(
                (self.directory / layout.TERMINAL_STREAM).read_text(
                    encoding="utf-8"
                )
            )
        except (OSError, KeyError, TypeError, ValueError) as exc:
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
            except (OSError, KeyError, TypeError, ValueError) as exc:
                raise ValueError(f"persisted {name} authority is invalid") from exc

        launch = read_receipt(layout.LAUNCH)
        checkpoint = read_receipt(layout.CHECKPOINT)
        claimed = read_receipt(layout.CLAIMED)
        timeout = read_receipt(layout.TIMEOUT)
        final = self.read_state()
        segment = self.rematerialize_terminal_segment(prefix, timeout)
        return self.factory.issue_timeout_bundle(
            launch=launch, checkpoint=checkpoint, claimed=claimed,
            timeout=timeout, segment=segment, final_transition=final,
            prefix=prefix,
        )

    def _finalize_operational_error_locked(
        self, *, launch: SignedProcessAuthorityReceipt,
        error_kind: str, deadline_stage: str,
        child_exit_disposition: str,
        prefix: Optional[EventStreamPrefixView] = None,
    ) -> DurableErrorFinalizationBundle:
        self._assert_locked()
        self.factory.validate(launch)
        try:
            durable_launch = self.factory.decode(json.loads(
                (self.directory / layout.LAUNCH).read_text(encoding="utf-8")
            ))
        except (OSError, KeyError, TypeError, ValueError) as exc:
            raise ValueError(
                "operational ERROR lacks durable launch authority"
            ) from exc
        if durable_launch.receipt_digest != launch.receipt_digest:
            raise ValueError("operational ERROR durable launch differs")
        if any(
            (self.directory / name).exists()
            for name in layout.CHECKPOINT_AUTHORITY_FILENAMES
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
            self.directory / layout.OPERATIONAL_ERROR, self._bytes(error),
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
            self.directory / layout.OPERATIONAL_ERROR_SEGMENT,
            segment_payload, identical_ok=True,
        )
        self._atomic_write(
            self.directory / layout.OPERATIONAL_ERROR_STREAM,
            self.codec.dumps(segment.composite_stream).encode("utf-8"),
            identical_ok=True,
        )
        bundle_payload = json.dumps({
            name: getattr(bundle, name)
            for name in bundle.__dataclass_fields__
            if name not in {"terminal_segment", "_factory_token"}
        }, sort_keys=True, separators=(",", ":")).encode("utf-8") + b"\n"
        self._atomic_write(
            self.directory / layout.OPERATIONAL_ERROR_BUNDLE,
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
            for name in layout.CHECKPOINT_AUTHORITY_FILENAMES
        ):
            raise ValueError(
                "persisted operational ERROR conflicts with checkpoint authority"
            )
        try:
            launch = self.factory.decode(json.loads(
                (self.directory / layout.LAUNCH).read_text(encoding="utf-8")
            ))
            error = self.factory.decode(json.loads(
                (self.directory / layout.OPERATIONAL_ERROR).read_text(
                    encoding="utf-8"
                )
            ))
            metadata = json.loads(
                (self.directory / layout.OPERATIONAL_ERROR_SEGMENT).read_text(
                    encoding="utf-8"
                )
            )
            stream = self.codec.loads(
                (self.directory / layout.OPERATIONAL_ERROR_STREAM).read_text(
                    encoding="utf-8"
                )
            )
            stored_bundle = json.loads(
                (self.directory / layout.OPERATIONAL_ERROR_BUNDLE).read_text(
                    encoding="utf-8"
                )
            )
        except (OSError, KeyError, TypeError, ValueError) as exc:
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
