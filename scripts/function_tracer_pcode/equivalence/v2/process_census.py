"""Complete process-attempt census and deterministic terminal-timeout selection."""

from __future__ import annotations

from dataclasses import dataclass, field
import json
from typing import Any, Mapping, Optional

from .contracts import VerifiedLifecyclePrefixProjection, VerifiedLifecycleProjection, authority_digest
from .operational_extraction import (
    DecompilationDisposition,
    SealedDecompilationInvocationCensus,
)
from .reducer import CauseLifecycleSnapshot
from .process_supervisor import (
    DurableCheckpointStore,
    DurableTimeoutFinalizationBundle,
    ProcessSupervisorAuthorityFactory,
    SignedProcessAuthorityReceipt,
)
from .process_worker_runtime import require_canonical_supervisor_projection
from .stream import (
    EventType,
    ProcessExecutionEventAuthority,
    ErrorEventAuthority,
    RecordedEvent,
    EventStreamPrefixView,
    SealedEventStream,
)


PROCESS_CENSUS_REGISTRY_ID = "operational-process-attempt-census-v1"
PROCESS_CENSUS_REGISTRY_VERSION = 1
PROCESS_CENSUS_REGISTRY_DIGEST = authority_digest({
    "registry_id": PROCESS_CENSUS_REGISTRY_ID,
    "registry_version": PROCESS_CENSUS_REGISTRY_VERSION,
    "dispositions": tuple(item.value for item in DecompilationDisposition),
    "extra_dispositions": ("ERROR", "RECEIPTLESS", "SUPERVISOR_TIMED_OUT"),
    "latest_per_requirement_order": ("invocation_ordinal", "event_sequence"),
    "candidate_order": (
        "terminal_priority", "proof_requirement_id", "event_sequence",
        "entry_digest",
    ),
})


_MEMBERSHIP_TOKEN = object()
_ENTRY_TOKEN = object()
_CENSUS_TOKEN = object()
_SELECTION_TOKEN = object()
_CONSUMPTION_TOKEN = object()


@dataclass(frozen=True)
class ProcessInvocationMembership:
    result_occurrence_id: str
    proof_requirement_id: str
    assignment_receipt_digest: str
    invocation_receipt_digest: str
    invocation_identity: str
    invocation_ordinal: int
    terminal_priority: int
    ownership_kind: str
    membership_digest: str
    _factory_token: object = field(default=None, repr=False, compare=False)


@dataclass(frozen=True)
class ProcessAttemptCensusEntry:
    membership_digest: str
    result_occurrence_id: str
    proof_requirement_id: str
    invocation_receipt_digest: str
    invocation_identity: str
    invocation_ordinal: int
    terminal_priority: int
    disposition: str
    attempt_receipt_digest: Optional[str]
    process_event_authority_digest: Optional[str]
    process_event_sequence: Optional[int]
    process_event_stream_digest: Optional[str]
    operational_error_artifact_digest: Optional[str]
    operational_error_kind: Optional[str]
    error_event_authority_digest: Optional[str]
    error_event_sequence: Optional[int]
    error_event_stream_digest: Optional[str]
    supervisor_timeout_bundle_digest: Optional[str]
    receiptless_reason: Optional[str]
    entry_digest: str
    _factory_token: object = field(default=None, repr=False, compare=False)


@dataclass(frozen=True)
class SealedProcessAttemptCensus:
    result_occurrence_id: str
    membership_digests: tuple[str, ...]
    issuer_invocation_census_digests: tuple[str, ...]
    entries: tuple[ProcessAttemptCensusEntry, ...]
    registry_digest: str
    census_digest: str
    _factory_token: object = field(default=None, repr=False, compare=False)


@dataclass(frozen=True)
class TerminalProcessTimeoutSelectionReceipt:
    result_occurrence_id: str
    process_census_digest: str
    process_census_registry_digest: str
    final_lifecycle_projection_digest: str
    final_q_open_base_digest: str
    final_event_stream_authority_digest: str
    candidate_set_digest: str
    selected_entry_digest: str
    selected_proof_requirement_id: str
    selected_invocation_identity: str
    selected_terminal_priority: int
    selected_event_or_bundle_digest: str
    selection_digest: str
    _factory_token: object = field(default=None, repr=False, compare=False)


class ProcessAttemptCensusFactory:
    def __init__(self, result_occurrence_id: str) -> None:
        if type(result_occurrence_id) is not str or not result_occurrence_id:
            raise TypeError("process census result occurrence is incomplete")
        self.result_occurrence_id = result_occurrence_id
        self._memberships: dict[int, ProcessInvocationMembership] = {}
        self._operational_factories: dict[int, Any] = {}
        self._membership_factories: dict[str, Any] = {}
        self._entries: dict[int, ProcessAttemptCensusEntry] = {}
        self._entry_by_membership: dict[str, ProcessAttemptCensusEntry] = {}
        self._censuses: dict[int, SealedProcessAttemptCensus] = {}
        self._census_issuer_pairs: dict[
            int, tuple[tuple[Any, SealedDecompilationInvocationCensus], ...]
        ] = {}
        self._selections: dict[int, TerminalProcessTimeoutSelectionReceipt] = {}

    def _validate_membership(self, membership: ProcessInvocationMembership) -> None:
        if (
            type(membership) is not ProcessInvocationMembership
            or membership._factory_token is not _MEMBERSHIP_TOKEN
            or self._memberships.get(id(membership)) is not membership
        ):
            raise TypeError("process membership is not exact census-factory membership")
        payload = {
            name: value for name, value in vars(membership).items()
            if name not in {"membership_digest", "_factory_token"}
        }
        if membership.membership_digest != authority_digest(payload):
            raise ValueError("process membership digest mismatch")
        operational_factory = self._membership_factories.get(
            membership.membership_digest
        )
        if operational_factory is None:
            raise ValueError("process membership lacks operational issuer")

    def _validate_membership_operational_factory(
        self, membership: ProcessInvocationMembership, operational_factory: Any,
    ) -> None:
        self._validate_membership(membership)
        if (
            self._membership_factories.get(membership.membership_digest)
            is not operational_factory
        ):
            raise ValueError("record evidence differs from membership operational issuer")

    def _record(
        self, membership: ProcessInvocationMembership, *, disposition: str,
        attempt_receipt_digest: Optional[str] = None,
        process_event: Optional[RecordedEvent] = None,
        process_event_stream: Optional[SealedEventStream] = None,
        error_digest: Optional[str] = None,
        error_kind: Optional[str] = None,
        error_event: Optional[RecordedEvent] = None,
        error_event_stream: Optional[SealedEventStream] = None,
        bundle_digest: Optional[str] = None,
        receiptless_reason: Optional[str] = None,
    ) -> ProcessAttemptCensusEntry:
        self._validate_membership(membership)
        if membership.membership_digest in self._entry_by_membership:
            raise ValueError("process membership already has a census entry")
        event_digest = None
        event_sequence = None
        event_stream_digest = None
        if process_event is not None:
            if type(process_event_stream) is not SealedEventStream:
                raise TypeError("process timeout event requires sealed stream authority")
            process_event_stream.validate()
            if (
                type(process_event) is not RecordedEvent
                or process_event.header.event_type is not EventType.PROCESS_TIMEOUT
                or type(process_event.authority_payload)
                is not ProcessExecutionEventAuthority
                or process_event.authority_payload.proof_requirement_id
                != membership.proof_requirement_id
                or process_event.authority_payload.process_invocation_id
                != membership.invocation_identity
                or not any(item is process_event for item in process_event_stream.events)
                or process_event_stream.envelope.result_occurrence_id
                != membership.result_occurrence_id
            ):
                raise ValueError("process timeout event differs from membership")
            event_digest = process_event.authority_digest
            event_sequence = process_event.header.sequence_number
            event_stream_digest = process_event_stream.envelope.authority_chain_digest
        elif process_event_stream is not None:
            raise ValueError("process event stream cannot exist without timeout event")
        error_event_digest = None
        error_event_sequence = None
        error_stream_digest = None
        if error_event is not None:
            if type(error_event_stream) is not SealedEventStream:
                raise TypeError("operational error event requires sealed stream authority")
            error_event_stream.validate()
            if (
                type(error_event) is not RecordedEvent
                or error_event.header.event_type is not EventType.ERROR
                or type(error_event.authority_payload) is not ErrorEventAuthority
                or error_event.authority_payload.error_artifact_digest != error_digest
                or error_event.authority_payload.error_kind != error_kind
                or not any(item is error_event for item in error_event_stream.events)
                or error_event_stream.envelope.result_occurrence_id
                != membership.result_occurrence_id
            ):
                raise ValueError("operational error event differs from membership")
            error_event_digest = error_event.authority_digest
            error_event_sequence = error_event.header.sequence_number
            error_stream_digest = error_event_stream.envelope.authority_chain_digest
        elif error_event_stream is not None:
            raise ValueError("error event stream cannot exist without error event")
        payload = {
            "membership_digest": membership.membership_digest,
            "result_occurrence_id": membership.result_occurrence_id,
            "proof_requirement_id": membership.proof_requirement_id,
            "invocation_receipt_digest": membership.invocation_receipt_digest,
            "invocation_identity": membership.invocation_identity,
            "invocation_ordinal": membership.invocation_ordinal,
            "terminal_priority": membership.terminal_priority,
            "disposition": disposition,
            "attempt_receipt_digest": attempt_receipt_digest,
            "process_event_authority_digest": event_digest,
            "process_event_sequence": event_sequence,
            "process_event_stream_digest": event_stream_digest,
            "operational_error_artifact_digest": error_digest,
            "operational_error_kind": error_kind,
            "error_event_authority_digest": error_event_digest,
            "error_event_sequence": error_event_sequence,
            "error_event_stream_digest": error_stream_digest,
            "supervisor_timeout_bundle_digest": bundle_digest,
            "receiptless_reason": receiptless_reason,
        }
        entry = ProcessAttemptCensusEntry(
            **payload, entry_digest=authority_digest(payload),
            _factory_token=_ENTRY_TOKEN,
        )
        self._entries[id(entry)] = entry
        self._entry_by_membership[membership.membership_digest] = entry
        return entry

    def record_attempt(
        self, membership: ProcessInvocationMembership, *, attempt: Any,
        operational_factory: Any, process_timeout_event: Optional[RecordedEvent] = None,
        process_timeout_stream: Optional[SealedEventStream] = None,
    ) -> ProcessAttemptCensusEntry:
        self._validate_membership_operational_factory(
            membership, operational_factory
        )
        operational_factory.validate_attempt_membership(attempt)
        if (
            attempt.invocation_receipt_digest != membership.invocation_receipt_digest
            or attempt.proof_requirement_id != membership.proof_requirement_id
        ):
            raise ValueError("process attempt differs from invocation membership")
        if (
            process_timeout_event is not None
            and attempt.disposition is not DecompilationDisposition.TIMED_OUT
        ):
            raise ValueError("only structured timed-out attempt accepts timeout event")
        return self._record(
            membership, disposition=attempt.disposition.value,
            attempt_receipt_digest=attempt.receipt_digest,
            process_event=process_timeout_event,
            process_event_stream=process_timeout_stream,
        )

    def seal(self) -> SealedProcessAttemptCensus:
        if len(self._entry_by_membership) != len(self._memberships):
            raise ValueError("process census is missing registered invocation entries")
        for membership in self._memberships.values():
            self._validate_membership(membership)
        issuer_pairs = tuple(sorted((
            (factory, factory.seal_invocation_census())
            for factory in self._operational_factories.values()
        ), key=lambda item: item[1].census_digest))
        issued_invocations = {
            digest for _factory, issuer_census in issuer_pairs
            for digest in issuer_census.invocation_receipt_digests
        }
        registered_invocations = {
            item.invocation_receipt_digest for item in self._memberships.values()
        }
        if issued_invocations != registered_invocations:
            raise ValueError(
                "process census membership differs from issuer invocation census"
            )
        memberships = tuple(sorted(
            item.membership_digest for item in self._memberships.values()
        ))
        issuer_digests = tuple(
            issuer_census.census_digest for _factory, issuer_census in issuer_pairs
        )
        entries = tuple(sorted(
            self._entries.values(), key=lambda item: (
                item.invocation_ordinal, item.entry_digest
            )
        ))
        payload = {
            "result_occurrence_id": self.result_occurrence_id,
            "membership_digests": memberships,
            "issuer_invocation_census_digests": issuer_digests,
            "entry_digests": tuple(item.entry_digest for item in entries),
            "registry_digest": PROCESS_CENSUS_REGISTRY_DIGEST,
        }
        census = SealedProcessAttemptCensus(
            self.result_occurrence_id, memberships, issuer_digests, entries,
            PROCESS_CENSUS_REGISTRY_DIGEST, authority_digest(payload),
            _factory_token=_CENSUS_TOKEN,
        )
        self._censuses[id(census)] = census
        self._census_issuer_pairs[id(census)] = issuer_pairs
        return census
