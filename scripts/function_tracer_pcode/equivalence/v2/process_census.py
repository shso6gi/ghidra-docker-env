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


@dataclass(frozen=True)
class DurableSupervisorProjectionConsumption:
    status: str
    continuation_kind: Optional[str]
    durable_authority_digest: str
    process_census_entry_digest: Optional[str]
    consumption_digest: str
    _factory_token: object = field(default=None, repr=False, compare=False)

    def __post_init__(self) -> None:
        if self._factory_token is not _CONSUMPTION_TOKEN:
            raise TypeError("supervisor projection consumption must be factory-issued")


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

    def _register(
        self, invocation: Any, operational_factory: Any, *,
        assignment_receipt_digest: str, terminal_priority: int,
        ownership_kind: str,
    ) -> ProcessInvocationMembership:
        operational_factory.validate_invocation_membership(invocation)
        if (
            self._operational_factories
            and id(operational_factory) not in self._operational_factories
        ):
            raise ValueError("process census cannot mix operational issuer factories")
        if invocation.result_occurrence_id != self.result_occurrence_id:
            raise ValueError("process invocation belongs to another result")
        if type(terminal_priority) is not int or terminal_priority <= 0:
            raise TypeError("process terminal priority is invalid")
        if any(
            item.invocation_ordinal == invocation.invocation_ordinal
            for item in self._memberships.values()
        ):
            raise ValueError("process invocation ordinal is not globally unique")
        payload = {
            "result_occurrence_id": self.result_occurrence_id,
            "proof_requirement_id": invocation.proof_requirement_id,
            "assignment_receipt_digest": assignment_receipt_digest,
            "invocation_receipt_digest": invocation.receipt_digest,
            "invocation_identity": invocation.invocation_identity,
            "invocation_ordinal": invocation.invocation_ordinal,
            "terminal_priority": terminal_priority,
            "ownership_kind": ownership_kind,
        }
        membership = ProcessInvocationMembership(
            **payload, membership_digest=authority_digest(payload),
            _factory_token=_MEMBERSHIP_TOKEN,
        )
        self._memberships[id(membership)] = membership
        self._operational_factories[id(operational_factory)] = operational_factory
        self._membership_factories[membership.membership_digest] = operational_factory
        return membership

    def register_operational(
        self, invocation: Any, operational_factory: Any, *,
        assignment: SignedProcessAuthorityReceipt,
        process_authority_factory: ProcessSupervisorAuthorityFactory,
    ) -> ProcessInvocationMembership:
        process_authority_factory.validate(assignment)
        if (
            assignment.receipt_kind != "ProcessLiveRequirementAssignmentReceipt"
            or assignment.payload["result_occurrence_id"] != self.result_occurrence_id
            or assignment.payload["proof_requirement_id"]
            != invocation.proof_requirement_id
        ):
            raise ValueError("operational process assignment differs from invocation")
        return self._register(
            invocation, operational_factory,
            assignment_receipt_digest=assignment.receipt_digest,
            terminal_priority=assignment.payload["terminal_priority"],
            ownership_kind="OPERATIONAL",
        )

    def register_subordinate(
        self, invocation: Any, operational_factory: Any, *,
        assignment: Any, assignment_factory: Any,
        projection: VerifiedLifecyclePrefixProjection,
        prefix: EventStreamPrefixView,
    ) -> ProcessInvocationMembership:
        assignment_factory.validate(assignment, projection, prefix)
        if assignment.proof_requirement_id != invocation.proof_requirement_id:
            raise ValueError("subordinate assignment differs from invocation")
        return self._register(
            invocation, operational_factory,
            assignment_receipt_digest=assignment.assignment_receipt_digest,
            terminal_priority=assignment.terminal_priority,
            ownership_kind="SUBORDINATE",
        )

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

    def record_error(
        self, membership: ProcessInvocationMembership, *, error: Any,
        attempt: Any,
        operational_factory: Any,
        error_event: RecordedEvent,
        error_event_stream: SealedEventStream,
    ) -> ProcessAttemptCensusEntry:
        self._validate_membership_operational_factory(
            membership, operational_factory
        )
        operational_factory.validate_error_membership(error)
        operational_factory.validate_attempt_membership(attempt)
        if (
            error.result_occurrence_id != membership.result_occurrence_id
            or error.attempt_receipt_digest != attempt.receipt_digest
            or attempt.invocation_receipt_digest
            != membership.invocation_receipt_digest
            or type(error_event) is not RecordedEvent
            or type(error_event.authority_payload) is not ErrorEventAuthority
            or error_event.authority_payload.error_kind != error.error_kind
        ):
            raise ValueError("operational error differs from process membership")
        return self._record(
            membership, disposition="ERROR",
            error_digest=error.artifact_digest,
            error_kind=error.error_kind,
            error_event=error_event,
            error_event_stream=error_event_stream,
        )

    def record_supervisor_timeout(
        self, membership: ProcessInvocationMembership, *,
        checkpoint: SignedProcessAuthorityReceipt,
        bundle: DurableTimeoutFinalizationBundle,
        process_authority_factory: ProcessSupervisorAuthorityFactory,
    ) -> ProcessAttemptCensusEntry:
        self._validate_membership(membership)
        process_authority_factory.validate(checkpoint)
        process_authority_factory.validate_timeout_bundle_membership(bundle)
        if (
            checkpoint.receipt_kind != "OperationalCheckpointReceipt"
            or bundle.checkpoint_receipt_digest != checkpoint.receipt_digest
            or bundle.result_occurrence_id != membership.result_occurrence_id
            or bundle.proof_requirement_id != membership.proof_requirement_id
            or bundle.invocation_identity != membership.invocation_identity
            or checkpoint.payload["invocation_receipt_digest"]
            != membership.invocation_receipt_digest
            or checkpoint.payload["assignment_receipt_digest"]
            != membership.assignment_receipt_digest
            or checkpoint.payload["assignment_kind"]
            != membership.ownership_kind
            or checkpoint.payload["operational_authority_root_digest"]
            != self._membership_factories[
                membership.membership_digest
            ].authority_root_digest
        ):
            raise ValueError("supervisor timeout bundle differs from membership")
        terminal_event = process_authority_factory.validated_timeout_terminal_event(
            bundle
        )
        return self._record(
            membership, disposition="SUPERVISOR_TIMED_OUT",
            process_event=terminal_event,
            process_event_stream=bundle.terminal_segment.composite_stream,
            bundle_digest=bundle.bundle_digest,
        )

    def record_worker_continuation(
        self, membership: ProcessInvocationMembership, *,
        checkpoint: SignedProcessAuthorityReceipt,
        continuation: SignedProcessAuthorityReceipt,
        continuation_stream: SealedEventStream,
        prefix: EventStreamPrefixView,
        process_authority_factory: ProcessSupervisorAuthorityFactory,
    ) -> ProcessAttemptCensusEntry:
        self._validate_membership(membership)
        process_authority_factory.validate(checkpoint)
        process_authority_factory.validate_worker_continuation(
            continuation, prefix, continuation_stream
        )
        if (
            checkpoint.receipt_kind != "OperationalCheckpointReceipt"
            or continuation.receipt_kind != "WorkerContinuationReceipt"
            or continuation.payload["checkpoint_receipt_digest"]
            != checkpoint.receipt_digest
            or checkpoint.payload["invocation_receipt_digest"]
            != membership.invocation_receipt_digest
            or checkpoint.payload["assignment_receipt_digest"]
            != membership.assignment_receipt_digest
            or checkpoint.payload["assignment_kind"]
            != membership.ownership_kind
            or continuation.payload["invocation_identity"]
            != membership.invocation_identity
            or continuation.payload["proof_requirement_id"]
            != membership.proof_requirement_id
            or continuation.payload["operational_authority_root_digest"]
            != checkpoint.payload["operational_authority_root_digest"]
            or checkpoint.payload["operational_authority_root_digest"]
            != self._membership_factories[
                membership.membership_digest
            ].authority_root_digest
        ):
            raise ValueError("worker continuation differs from process membership")
        terminal = continuation_stream.events[-1]
        kind = continuation.payload["continuation_kind"]
        if kind in {"COMPLETED", "SUBORDINATE_COMPLETED"}:
            return self._record(
                membership, disposition=DecompilationDisposition.COMPLETED.value,
                attempt_receipt_digest=continuation.payload[
                    "attempt_receipt_digest"
                ],
            )
        if kind == "TIMED_OUT_ATTEMPT":
            return self._record(
                membership, disposition=DecompilationDisposition.TIMED_OUT.value,
                attempt_receipt_digest=continuation.payload[
                    "attempt_receipt_digest"
                ],
                process_event=terminal,
                process_event_stream=continuation_stream,
            )
        if kind == "ERROR":
            return self._record(
                membership, disposition="ERROR",
                attempt_receipt_digest=continuation.payload[
                    "attempt_receipt_digest"
                ],
                error_digest=continuation.payload["terminal_artifact_digest"],
                error_kind=continuation.payload["terminal_error_kind"],
                error_event=terminal,
                error_event_stream=continuation_stream,
            )
        raise ValueError("worker continuation kind is not sealed")

    def record_receiptless(
        self, membership: ProcessInvocationMembership, *, reason: str,
    ) -> ProcessAttemptCensusEntry:
        if type(reason) is not str or not reason:
            raise TypeError("receiptless process attempt requires typed reason")
        return self._record(
            membership, disposition="RECEIPTLESS", receiptless_reason=reason,
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

    def _validate_entry(self, entry: ProcessAttemptCensusEntry) -> None:
        if (
            type(entry) is not ProcessAttemptCensusEntry
            or entry._factory_token is not _ENTRY_TOKEN
            or self._entries.get(id(entry)) is not entry
            or self._entry_by_membership.get(entry.membership_digest) is not entry
        ):
            raise TypeError("process census entry is not exact factory membership")
        payload = {
            name: value for name, value in vars(entry).items()
            if name not in {"entry_digest", "_factory_token"}
        }
        if entry.entry_digest != authority_digest(payload):
            raise ValueError("process census entry digest mismatch")

    def _validate_census(self, census: SealedProcessAttemptCensus) -> None:
        if (
            type(census) is not SealedProcessAttemptCensus
            or census._factory_token is not _CENSUS_TOKEN
            or self._censuses.get(id(census)) is not census
        ):
            raise TypeError("terminal selection requires exact sealed census")
        if census.registry_digest != PROCESS_CENSUS_REGISTRY_DIGEST:
            raise ValueError("process census registry digest mismatch")
        issuer_pairs = self._census_issuer_pairs.get(id(census))
        if issuer_pairs is None:
            raise TypeError("sealed process census lacks exact issuer closure")
        for factory, issuer_census in issuer_pairs:
            factory.validate_invocation_census(issuer_census)
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
        for membership in self._memberships.values():
            self._validate_membership(membership)
        for entry in census.entries:
            self._validate_entry(entry)
        expected_memberships = tuple(sorted(
            item.membership_digest for item in self._memberships.values()
        ))
        expected_entries = tuple(sorted(
            self._entries.values(), key=lambda item: (
                item.invocation_ordinal, item.entry_digest
            )
        ))
        payload = {
            "result_occurrence_id": self.result_occurrence_id,
            "membership_digests": expected_memberships,
            "issuer_invocation_census_digests": tuple(
                issuer_census.census_digest
                for _factory, issuer_census in issuer_pairs
            ),
            "entry_digests": tuple(item.entry_digest for item in expected_entries),
            "registry_digest": PROCESS_CENSUS_REGISTRY_DIGEST,
        }
        if (
            census.result_occurrence_id != self.result_occurrence_id
            or census.membership_digests != expected_memberships
            or census.issuer_invocation_census_digests
            != payload["issuer_invocation_census_digests"]
            or census.entries != expected_entries
            or census.census_digest != authority_digest(payload)
        ):
            raise ValueError("sealed process census content or digest mismatch")

    def _terminal_candidates(
        self, census: SealedProcessAttemptCensus,
        final_snapshot: CauseLifecycleSnapshot,
        final_projection: VerifiedLifecycleProjection,
    ) -> tuple[ProcessAttemptCensusEntry, ...]:
        live_q = {row.proof_requirement_id for row in final_projection.q_open_base}
        satisfaction = dict(final_projection.satisfaction_projection)
        final_execution_events = frozenset(satisfaction["execution_event_digests"])
        latest: dict[str, ProcessAttemptCensusEntry] = {}
        for entry in census.entries:
            if entry.proof_requirement_id not in live_q:
                continue
            current = latest.get(entry.proof_requirement_id)
            order = (entry.invocation_ordinal, entry.process_event_sequence or 0)
            if current is None or order > (
                current.invocation_ordinal, current.process_event_sequence or 0
            ):
                latest[entry.proof_requirement_id] = entry
        eligible_dispositions = {
            DecompilationDisposition.TIMED_OUT.value,
            "SUPERVISOR_TIMED_OUT",
        }
        return tuple(sorted((
            entry for entry in latest.values()
            if (
                entry.disposition in eligible_dispositions
                and entry.process_event_authority_digest is not None
                and entry.process_event_authority_digest in final_execution_events
                and entry.process_event_stream_digest
                == final_snapshot.event_stream_authority_digest
                and (
                    entry.disposition != "SUPERVISOR_TIMED_OUT"
                    or entry.supervisor_timeout_bundle_digest is not None
                )
            )
        ), key=lambda item: (
            item.terminal_priority, item.proof_requirement_id,
            item.process_event_sequence or 0, item.entry_digest,
        )))

    def _validate_final_authority(
        self, final_snapshot: CauseLifecycleSnapshot,
        final_projection: VerifiedLifecycleProjection,
    ) -> None:
        if type(final_snapshot) is not CauseLifecycleSnapshot:
            raise TypeError("process terminal selection requires final lifecycle snapshot")
        final_snapshot.validate()
        final_projection.validate()
        if (
            final_snapshot.result_occurrence_id != self.result_occurrence_id
            or final_projection.result_occurrence_id != self.result_occurrence_id
            or final_projection.snapshot_digest != final_snapshot.snapshot_digest
        ):
            raise ValueError("process census/final lifecycle authority differs")
        error_bindings = set(final_snapshot.error_event_bindings)
        for entry in self._entries.values():
            if entry.error_event_authority_digest is not None and (
                entry.error_event_stream_digest
                != final_snapshot.event_stream_authority_digest
                or (
                    entry.operational_error_kind,
                    entry.operational_error_artifact_digest,
                ) not in error_bindings
            ):
                raise ValueError("process ERROR entry lacks exact FINAL event binding")
            if entry.process_event_authority_digest is not None and (
                entry.process_event_stream_digest
                != final_snapshot.event_stream_authority_digest
                or entry.process_event_authority_digest
                not in final_snapshot.execution_event_digests
            ):
                raise ValueError("process timeout entry lacks exact FINAL event binding")

    def select_terminal_timeout(
        self, census: SealedProcessAttemptCensus,
        final_snapshot: CauseLifecycleSnapshot,
        final_projection: VerifiedLifecycleProjection,
    ) -> Optional[TerminalProcessTimeoutSelectionReceipt]:
        self._validate_census(census)
        self._validate_final_authority(final_snapshot, final_projection)
        if census.result_occurrence_id != self.result_occurrence_id:
            raise ValueError("process census/final lifecycle result differs")
        candidates = self._terminal_candidates(
            census, final_snapshot, final_projection
        )
        if not candidates:
            return None
        selected = candidates[0]
        selected_authority = (
            selected.supervisor_timeout_bundle_digest
            if selected.disposition == "SUPERVISOR_TIMED_OUT"
            else selected.process_event_authority_digest
        )
        payload = {
            "result_occurrence_id": self.result_occurrence_id,
            "process_census_digest": census.census_digest,
            "process_census_registry_digest": census.registry_digest,
            "final_lifecycle_projection_digest": (
                final_projection.lifecycle_projection_digest
            ),
            "final_q_open_base_digest": final_projection.q_open_base_digest,
            "final_event_stream_authority_digest": (
                final_snapshot.event_stream_authority_digest
            ),
            "candidate_set_digest": authority_digest(tuple(
                item.entry_digest for item in candidates
            )),
            "selected_entry_digest": selected.entry_digest,
            "selected_proof_requirement_id": selected.proof_requirement_id,
            "selected_invocation_identity": selected.invocation_identity,
            "selected_terminal_priority": selected.terminal_priority,
            "selected_event_or_bundle_digest": selected_authority,
        }
        receipt = TerminalProcessTimeoutSelectionReceipt(
            **payload, selection_digest=authority_digest(payload),
            _factory_token=_SELECTION_TOKEN,
        )
        self._selections[id(receipt)] = receipt
        return receipt

    def validate_selection(
        self, receipt: TerminalProcessTimeoutSelectionReceipt,
        census: SealedProcessAttemptCensus,
        final_snapshot: CauseLifecycleSnapshot,
        final_projection: VerifiedLifecycleProjection,
    ) -> None:
        if (
            type(receipt) is not TerminalProcessTimeoutSelectionReceipt
            or receipt._factory_token is not _SELECTION_TOKEN
            or self._selections.get(id(receipt)) is not receipt
        ):
            raise TypeError("terminal selection is not exact factory membership")
        self._validate_census(census)
        self._validate_final_authority(final_snapshot, final_projection)
        if census.result_occurrence_id != self.result_occurrence_id:
            raise ValueError("process census/final lifecycle result differs")
        candidates = self._terminal_candidates(
            census, final_snapshot, final_projection
        )
        if not candidates:
            raise ValueError("terminal selection has no eligible candidate")
        selected = candidates[0]
        selected_authority = (
            selected.supervisor_timeout_bundle_digest
            if selected.disposition == "SUPERVISOR_TIMED_OUT"
            else selected.process_event_authority_digest
        )
        payload = {
            "result_occurrence_id": self.result_occurrence_id,
            "process_census_digest": census.census_digest,
            "process_census_registry_digest": census.registry_digest,
            "final_lifecycle_projection_digest": (
                final_projection.lifecycle_projection_digest
            ),
            "final_q_open_base_digest": final_projection.q_open_base_digest,
            "final_event_stream_authority_digest": (
                final_snapshot.event_stream_authority_digest
            ),
            "candidate_set_digest": authority_digest(tuple(
                item.entry_digest for item in candidates
            )),
            "selected_entry_digest": selected.entry_digest,
            "selected_proof_requirement_id": selected.proof_requirement_id,
            "selected_invocation_identity": selected.invocation_identity,
            "selected_terminal_priority": selected.terminal_priority,
            "selected_event_or_bundle_digest": selected_authority,
        }
        actual_payload = {
            name: value for name, value in vars(receipt).items()
            if name not in {"selection_digest", "_factory_token"}
        }
        if actual_payload != payload or receipt.selection_digest != authority_digest(payload):
            raise ValueError("terminal selection content or digest mismatch")


def consume_durable_supervisor_projection(
    payload: Mapping[str, Any], *, store: DurableCheckpointStore,
    process_authority_factory: ProcessSupervisorAuthorityFactory,
    census_factory: Optional[ProcessAttemptCensusFactory] = None,
    membership: Optional[ProcessInvocationMembership] = None,
) -> DurableSupervisorProjectionConsumption:
    """Join a command projection back to durable authority before census use."""
    projection = require_canonical_supervisor_projection(payload)
    if store.factory is not process_authority_factory:
        raise ValueError("supervisor projection store/factory authority differs")
    status = projection["status"]
    continuation_kind = None
    entry = None
    if status == "ERROR":
        if census_factory is not None or membership is not None:
            raise ValueError("pre-checkpoint supervisor ERROR cannot claim invocation")
        bundle = store.rematerialize_operational_error_bundle()
        if (
            projection["launch_receipt_digest"]
            != bundle.launch_receipt_digest
            or projection["finalization_bundle_digest"] != bundle.bundle_digest
            or projection["event_stream_authority_digest"]
            != bundle.composite_stream_authority_digest
        ):
            raise ValueError("ERROR projection differs from durable bundle")
        durable_digest = bundle.bundle_digest
    elif status == "TIMEOUT":
        if census_factory is None or membership is None:
            raise ValueError("TIMEOUT projection lacks process census membership")
        prefix = store.rematerialize_active_prefix()
        bundle = store.rematerialize_timeout_bundle(prefix=prefix)
        try:
            checkpoint = process_authority_factory.decode(json.loads(
                (store.directory / "checkpoint.json").read_text(encoding="utf-8")
            ))
        except Exception as exc:
            raise ValueError("TIMEOUT durable checkpoint is invalid") from exc
        if (
            projection["launch_receipt_digest"] != bundle.launch_receipt_digest
            or projection["finalization_bundle_digest"] != bundle.bundle_digest
            or projection["event_stream_authority_digest"]
            != bundle.composite_stream_authority_digest
            or projection["proof_requirement_id"] != bundle.proof_requirement_id
        ):
            raise ValueError("TIMEOUT projection differs from durable bundle")
        entry = census_factory.record_supervisor_timeout(
            membership, checkpoint=checkpoint, bundle=bundle,
            process_authority_factory=process_authority_factory,
        )
        durable_digest = bundle.bundle_digest
    else:
        if census_factory is None or membership is None:
            raise ValueError("RESOLVED projection lacks process census membership")
        prefix = store.rematerialize_active_prefix()
        state = store.rematerialize_resolved_state(prefix=prefix)
        continuation, stream = store.rematerialize_worker_continuation(
            prefix=prefix
        )
        try:
            checkpoint = process_authority_factory.decode(json.loads(
                (store.directory / "checkpoint.json").read_text(encoding="utf-8")
            ))
            launch = process_authority_factory.decode(json.loads(
                (store.directory / "launch.json").read_text(encoding="utf-8")
            ))
        except Exception as exc:
            raise ValueError("RESOLVED durable launch/checkpoint is invalid") from exc
        if (
            projection["launch_receipt_digest"] != launch.receipt_digest
            or projection["finalization_bundle_digest"] != state.receipt_digest
        ):
            raise ValueError("RESOLVED projection differs from durable state")
        entry = census_factory.record_worker_continuation(
            membership, checkpoint=checkpoint, continuation=continuation,
            continuation_stream=stream, prefix=prefix,
            process_authority_factory=process_authority_factory,
        )
        continuation_kind = continuation.payload["continuation_kind"]
        durable_digest = continuation.receipt_digest
    authority = {
        "status": status,
        "continuation_kind": continuation_kind,
        "durable_authority_digest": durable_digest,
        "process_census_entry_digest": (
            entry.entry_digest if entry is not None else None
        ),
        "projection_digest": projection["projection_digest"],
    }
    return DurableSupervisorProjectionConsumption(
        status, continuation_kind, durable_digest,
        entry.entry_digest if entry is not None else None,
        authority_digest(authority), _factory_token=_CONSUMPTION_TOKEN,
    )
