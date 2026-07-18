"""Runtime-owned Phase 7 activation, finalization, and projection join."""

from __future__ import annotations

from dataclasses import dataclass, replace
from typing import Any, Mapping, Sequence

from .contracts import authority_digest
from .decision import (
    FinalizationAuthority,
    TerminalTimeoutReceipt,
    finalize_decision,
)
from .phase7_cutover import (
    ActivationDisposition,
    ExpectedActivationContract,
    ExpectedActivationAuthority,
    ExpectedActivationLedgerFactory,
    ExpectedCauseSlotContract,
    ProducerSiteContract,
    SealedProducerSiteRegistry,
    TypedResultProjectionReceipt,
    VerifiedFinalizationBundle,
    VerifiedFinalizationBundleFactory,
    typed_cause_coverage,
)
from .process_supervisor import (
    PROCESS_DURABLE_REASON_REGISTRY,
    PROCESS_DURABLE_RECOVERY_REGISTRY,
)
from .stream import CauseObservedEventAuthority, EventIntent, EventType


@dataclass(frozen=True)
class Phase7RuntimeResult:
    finalization_bundle: VerifiedFinalizationBundle
    projection_receipts: tuple[TypedResultProjectionReceipt, ...]
    coverage: Mapping[str, object]
    runtime_activation_ledger_digest: str
    projection_factory: Any
    decision_receipt: Any
    terminal_timeout_assignment_receipt: Any = None
    expected_activation_ledger_digest: str = ""
    expected_activation_count: int = 0
    runtime_activation_count: int = 0
    not_reached_activation_count: int = 0
    static_producer_site_count: int = 0
    discovered_activation_count: int = 0


class Phase7ProductionRuntime:
    """Consume independently expected activations from real producer signals."""

    def __init__(
        self,
        expected_factory: ExpectedActivationLedgerFactory,
        signal_authorities: Mapping[str, ExpectedActivationAuthority],
    ) -> None:
        if not signal_authorities:
            raise ValueError("Phase 7 runtime requires expected producer signals")
        if any(
            type(key) is not str
            or not key
            for key in signal_authorities
        ):
            raise ValueError("Phase 7 signal plan lacks expected-ledger authority")
        self._expected_factory = expected_factory
        self._activation_factory = expected_factory.open_runtime_ledger()
        normalized_authorities: dict[str, list[ExpectedActivationAuthority]] = {}
        for key, value in signal_authorities.items():
            values = (
                tuple(value)
                if type(value) in {tuple, list}
                else (value,)
            )
            if not values or any(
                not expected_factory.owns(item) for item in values
            ):
                raise ValueError("Phase 7 signal plan lacks expected-ledger authority")
            normalized_authorities[key] = list(values)
        flattened = tuple(
            item for values in normalized_authorities.values() for item in values
        )
        if len({id(item) for item in flattened}) != len(flattened):
            raise ValueError("one expected activation cannot cover multiple signals")
        self._signal_authorities = normalized_authorities
        self._pending_by_signal: dict[str, list[str]] = {}
        self._buffered: list[tuple[str | None, EventIntent]] = []
        self._recorded: set[str] = set()
        self._finalized = False

    @staticmethod
    def signal_digest(producer_site_manifest_id: str, signal: Any) -> str:
        if type(producer_site_manifest_id) is not str or not producer_site_manifest_id:
            raise TypeError("production signal requires audited producer site identity")
        if (
            hasattr(signal, "target")
            and type(getattr(signal.target, "target_digest", None)) is str
        ):
            signal_authority = {
                "reason_id": getattr(signal, "reason_id", None),
                "target_digest": signal.target.target_digest,
                "evidence_refs": tuple(getattr(signal, "evidence_refs", ())),
                "producer_id": getattr(signal, "producer_id", None),
            }
        else:
            signal_authority = signal
        return authority_digest({
            "producer_site_manifest_id": producer_site_manifest_id,
            "phase7_production_signal_type": type(signal).__qualname__,
            "signal": signal_authority,
        })

    def record_pre_emission_activation(
        self, producer_site_manifest_id: str, signal: Any,
    ) -> None:
        if self._finalized:
            raise ValueError("Phase 7 runtime is finalized")
        digest = self.signal_digest(producer_site_manifest_id, signal)
        authorities = self._signal_authorities.get(digest)
        if not authorities:
            authorities = self._signal_authorities.get(
                "audited-site:" + producer_site_manifest_id
            )
        if not authorities:
            raise ValueError("production signal is absent from expected activation plan")
        authority = authorities.pop(0)
        expected_id = authority.contract.expected_activation_id
        if expected_id in self._recorded:
            raise ValueError("production signal activation is duplicated")
        self._activation_factory.record(authority)
        self._recorded.add(expected_id)
        self._pending_by_signal.setdefault(digest, []).append(expected_id)

    def buffer_signal_intents(
        self, producer_site_manifest_id: str, signal: Any,
        intents: Sequence[EventIntent],
    ) -> None:
        digest = self.signal_digest(producer_site_manifest_id, signal)
        pending = self._pending_by_signal.get(digest, [])
        if not pending:
            raise ValueError("cause emission lacks pre-emission activation")
        activation_id = pending.pop(0)
        for intent in intents:
            if type(intent) is not EventIntent:
                raise TypeError("Phase 7 runtime requires exact event intents")
            if intent.event_type is EventType.CAUSE_OBSERVED:
                self._buffered.append((activation_id, intent))

    def buffer_execution_intent(self, intent: EventIntent) -> None:
        if type(intent) is not EventIntent:
            raise TypeError("Phase 7 runtime requires exact event intent")
        if intent.event_type is EventType.CAUSE_OBSERVED:
            raise ValueError("cause events require producer activation")
        self._buffered.append((None, intent))

    def finalize(self, *, stream_id: str, result_occurrence_id: str,
                 source_snapshot_fingerprint: str) -> Phase7RuntimeResult:
        if self._finalized:
            raise ValueError("Phase 7 runtime is already finalized")
        self._finalized = True
        ledger = self._activation_factory.seal()
        activations = {row.activation_id: row for row in ledger.receipts}
        finalization_factory = VerifiedFinalizationBundleFactory(
            PROCESS_DURABLE_REASON_REGISTRY, PROCESS_DURABLE_RECOVERY_REGISTRY,
        )
        recorder = finalization_factory.open_recorder(
            stream_id=stream_id,
            result_occurrence_id=result_occurrence_id,
            source_snapshot_fingerprint=source_snapshot_fingerprint,
        )
        joined = []
        for activation_id, intent in self._buffered:
            if intent.event_type is not EventType.CAUSE_OBSERVED:
                recorder.append(intent)
                continue
            if type(intent.authority_payload) is not CauseObservedEventAuthority:
                raise TypeError("Phase 7 cause intent authority is not exact")
            activation = activations[activation_id]
            occurrence_authority = intent.authority_payload.occurrence_authority
            matching_slots = tuple(
                slot_id for slot_id in activation.expected_cause_slot_ids
                if (
                    occurrence_authority.occurrence.reason_id
                    in self._activation_factory.cause_slot_contract(
                        activation, slot_id
                    ).allowed_reason_ids
                )
            )
            if len(matching_slots) != 1:
                raise ValueError("production occurrence does not select one expected slot")
            slot_id = matching_slots[0]
            binding = self._activation_factory.bind_emission(
                activation=activation,
                expected_cause_slot_id=slot_id,
                occurrence_authority=occurrence_authority,
            )
            emitted = finalization_factory.append_cause_observed(
                recorder=recorder,
                emission_binding=binding,
                activation_factory=self._activation_factory,
            )
            joined.append((activation, slot_id, binding, emitted))
        bundle = finalization_factory.issue(recorder)
        projection_factory = self._activation_factory.open_projection_factory(
            finalization_factory
        )
        projections = tuple(
            projection_factory.issue(
                activation=activation,
                expected_cause_slot_id=slot_id,
                bundle=bundle,
                emission_binding=binding,
                emitted_cause=emitted,
            )
            for activation, slot_id, binding, emitted in joined
            if activation.expected_disposition is ActivationDisposition.ELIGIBLE
        )
        coverage = typed_cause_coverage(
            ledger, self._activation_factory, projection_factory, projections,
        )
        terminal_assignment = None
        terminal_receipts = ()
        terminal_candidates = tuple(
            event for event in bundle.sealed_event_stream.events
            if event.header.event_type in {
                EventType.SOLVER_TIMEOUT, EventType.PROCESS_TIMEOUT,
            }
            and getattr(event.authority_payload, "terminal_candidate", False) is True
        )
        if terminal_candidates:
            terminal_assignment = (
                finalization_factory.open_timeout_assignment_factory().issue(bundle)
            )
            terminal_receipts = (TerminalTimeoutReceipt.create(
                result_occurrence_id=result_occurrence_id,
                lifecycle_projection_digest=(
                    bundle.lifecycle_projection.lifecycle_projection_digest
                ),
                proof_requirement_id=(
                    terminal_assignment.assignment_requirement_ids[0]
                ),
                execution_event_digest=(
                    terminal_assignment.execution_event_digests[0]
                ),
            ),)
        decision = finalize_decision(FinalizationAuthority(
            result_occurrence_id=result_occurrence_id,
            lifecycle_projection=bundle.lifecycle_projection,
            terminal_timeout_receipts=terminal_receipts,
        ))
        return Phase7RuntimeResult(
            bundle, projections, coverage, ledger.ledger_digest,
            projection_factory, decision, terminal_assignment,
            self._expected_factory.ledger.ledger_digest,
            len(self._expected_factory.ledger.authorities),
            len(ledger.receipts),
            0,
        )


_DISCOVERY_AUTHORITY_TOKEN = object()


@dataclass(frozen=True, init=False)
class DiscoveredActivationAuthority:
    result_occurrence_id: str
    producer_manifest_digest: str
    producer_site_manifest_id: str
    producer_source_fingerprint: str
    signal_digest: str
    invocation_ordinal: int
    authority_digest: str

    def __init__(self, *values: Any, _factory_token: Any = None) -> None:
        if _factory_token is not _DISCOVERY_AUTHORITY_TOKEN:
            raise ValueError("discovered activation authority is factory-issued")
        for name, value in zip(tuple(self.__dataclass_fields__), values):
            object.__setattr__(self, name, value)


class DiscoveredActivationAuthorityFactory:
    """Issue branch-entry authority independently of lifecycle cause emission."""

    def __init__(
        self, *, result_occurrence_id: str, producer_manifest_digest: str,
        sites: Mapping[str, Mapping[str, Any]],
    ) -> None:
        self._result_occurrence_id = result_occurrence_id
        self._producer_manifest_digest = producer_manifest_digest
        self._sites = dict(sites)
        self._issued: dict[int, DiscoveredActivationAuthority] = {}
        self._ordinals: dict[str, int] = {}

    def issue(
        self, producer_site_manifest_id: str, signal_digest: str,
    ) -> DiscoveredActivationAuthority:
        site = self._sites.get(producer_site_manifest_id)
        if site is None:
            raise ValueError("branch entry is absent from static producer manifest")
        ordinal = self._ordinals.get(producer_site_manifest_id, 0) + 1
        self._ordinals[producer_site_manifest_id] = ordinal
        body = {
            "result_occurrence_id": self._result_occurrence_id,
            "producer_manifest_digest": self._producer_manifest_digest,
            "producer_site_manifest_id": producer_site_manifest_id,
            "producer_source_fingerprint": site["source_sha256"],
            "signal_digest": signal_digest,
            "invocation_ordinal": ordinal,
        }
        authority = DiscoveredActivationAuthority(
            body["result_occurrence_id"], body["producer_manifest_digest"],
            body["producer_site_manifest_id"],
            body["producer_source_fingerprint"], body["signal_digest"],
            body["invocation_ordinal"], authority_digest(body),
            _factory_token=_DISCOVERY_AUTHORITY_TOKEN,
        )
        self._issued[id(authority)] = authority
        return authority

    def owns(self, authority: DiscoveredActivationAuthority) -> bool:
        return self._issued.get(id(authority)) is authority


class AuditedManifestPhase7Runtime:
    """Discover dynamic activations at wrapper entry; never accept a caller census."""

    def __init__(
        self, producer_manifest: Mapping[str, Any], identity: Any,
        registry: SealedProducerSiteRegistry,
    ) -> None:
        self._manifest = producer_manifest
        self._identity = identity
        self._registry = registry
        self._sites = {
            row["producer_site_manifest_id"]: row
            for row in producer_manifest["sites"]
        }
        self._discovery_factory = DiscoveredActivationAuthorityFactory(
            result_occurrence_id=identity.result_occurrence_id,
            producer_manifest_digest=producer_manifest["manifest_digest"],
            sites=self._sites,
        )
        self._pending: dict[str, list[tuple[DiscoveredActivationAuthority, Any]]] = {}
        self._materialized: list[tuple[
            DiscoveredActivationAuthority, Any, tuple[EventIntent, ...],
            ExpectedActivationContract,
        ]] = []
        self._execution_intents: list[EventIntent] = []
        self._finalized = False

    def record_pre_emission_activation(
        self, producer_site_manifest_id: str, signal: Any,
    ) -> None:
        if self._finalized:
            raise ValueError("Phase 7 discovered runtime is finalized")
        digest = Phase7ProductionRuntime.signal_digest(
            producer_site_manifest_id, signal
        )
        authority = self._discovery_factory.issue(
            producer_site_manifest_id, digest
        )
        self._pending.setdefault(digest, []).append((authority, signal))

    def _select_slot(
        self, site_id: str, occurrence_authority: Any,
    ) -> str:
        occurrence = occurrence_authority.occurrence
        matches = tuple(
            slot.slot_id
            for slot in self._registry.get(site_id).eligible_cause_slots
            if occurrence.reason_id in slot.allowed_reason_ids
            and occurrence.target_kind == slot.expected_target_kind
            and occurrence.identity_scope.value == slot.expected_identity_scope
        )
        if len(matches) != 1:
            raise ValueError(
                "production occurrence does not match one site-exact alternative slot"
            )
        return matches[0]

    def buffer_signal_intents(
        self, producer_site_manifest_id: str, signal: Any,
        intents: Sequence[EventIntent],
    ) -> None:
        digest = Phase7ProductionRuntime.signal_digest(
            producer_site_manifest_id, signal
        )
        pending = self._pending.get(digest, [])
        if not pending:
            raise ValueError("signal intents lack wrapper-entry discovery authority")
        discovery, discovered_signal = pending.pop(0)
        if discovered_signal is not signal or not self._discovery_factory.owns(discovery):
            raise ValueError("signal intents differ from discovered branch entry")
        exact_intents = tuple(intents)
        if any(type(intent) is not EventIntent for intent in exact_intents):
            raise TypeError("Phase 7 discovered runtime requires exact event intents")
        cause_intents = tuple(
            intent for intent in exact_intents
            if intent.event_type is EventType.CAUSE_OBSERVED
        )
        if len(cause_intents) > 1:
            raise ValueError("one discovered wrapper activation emitted multiple causes")
        site = self._sites[producer_site_manifest_id]
        if cause_intents:
            payload = cause_intents[0].authority_payload
            if type(payload) is not CauseObservedEventAuthority:
                raise TypeError("discovered cause intent lacks exact occurrence authority")
            occurrence = payload.occurrence_authority.occurrence
            producer_id = occurrence.producer_id
            branch_or_attempt_id = occurrence.attempt_id
            disposition = ActivationDisposition.ELIGIBLE
            selected_slots = (
                self._select_slot(
                    producer_site_manifest_id, payload.occurrence_authority
                ),
            )
        else:
            allowed = tuple(site["allowed_producer_ids"])
            signal_producer = getattr(signal, "producer_id", None)
            if signal_producer is None:
                signal_producer = getattr(
                    getattr(signal, "blocker", None), "producer_id", None
                )
            producer_id = signal_producer if signal_producer in allowed else (
                allowed[0] if len(allowed) == 1 else None
            )
            if producer_id is None:
                raise ValueError("decisive activation producer is ambiguous")
            branch_or_attempt_id = getattr(
                signal, "producer_attempt_identity",
                self._identity.execution_identity_digest,
            )
            disposition = (
                ActivationDisposition.OPERATIONAL_ERROR_NO_SEMANTIC_CAUSE
                if any(intent.event_type is EventType.ERROR for intent in exact_intents)
                else ActivationDisposition.DECISIVE
            )
            selected_slots = ()
        if producer_id not in site["allowed_producer_ids"]:
            raise ValueError("discovered activation producer is not site-sealed")
        if disposition.value not in site["allowed_dispositions"]:
            raise ValueError("discovered activation disposition is not site-sealed")
        contract = ExpectedActivationContract(
            expected_activation_id="discovered-" + discovery.authority_digest,
            producer_site_manifest_id=producer_site_manifest_id,
            branch_or_attempt_id=branch_or_attempt_id,
            producer_id=producer_id,
            disposition=disposition,
            invocation_ordinal=discovery.invocation_ordinal,
            selected_cause_slot_ids=selected_slots,
        )
        self._materialized.append((discovery, signal, exact_intents, contract))

    def buffer_execution_intent(self, intent: EventIntent) -> None:
        if type(intent) is not EventIntent:
            raise TypeError("Phase 7 discovered runtime requires exact event intent")
        if intent.event_type is EventType.CAUSE_OBSERVED:
            raise ValueError("cause events require discovered producer activation")
        self._execution_intents.append(intent)

    def finalize(
        self, *, stream_id: str, result_occurrence_id: str,
        source_snapshot_fingerprint: str,
    ) -> Phase7RuntimeResult:
        if self._finalized:
            raise ValueError("Phase 7 discovered runtime is already finalized")
        self._finalized = True
        if any(self._pending.values()):
            raise ValueError("discovered branch entry lacks signal materialization")
        if not self._materialized:
            raise ValueError("Phase 7 run has no discovered producer activations")
        expected_factory = ExpectedActivationLedgerFactory(
            self._registry,
            ledger_id="discovered:" + self._identity.result_occurrence_id,
            result_occurrence_id=self._identity.result_occurrence_id,
            expected=tuple(item[3] for item in self._materialized),
        )
        authorities = {
            row.contract.expected_activation_id: row
            for row in expected_factory.ledger.authorities
        }
        by_digest: dict[str, list[ExpectedActivationAuthority]] = {}
        for discovery, _signal, _intents, contract in self._materialized:
            by_digest.setdefault(discovery.signal_digest, []).append(
                authorities[contract.expected_activation_id]
            )
        runtime = Phase7ProductionRuntime(expected_factory, by_digest)
        for discovery, signal, intents, _contract in self._materialized:
            runtime.record_pre_emission_activation(
                discovery.producer_site_manifest_id, signal
            )
            runtime.buffer_signal_intents(
                discovery.producer_site_manifest_id, signal, intents
            )
        for intent in self._execution_intents:
            runtime.buffer_execution_intent(intent)
        result = runtime.finalize(
            stream_id=stream_id,
            result_occurrence_id=result_occurrence_id,
            source_snapshot_fingerprint=source_snapshot_fingerprint,
        )
        return replace(
            result,
            static_producer_site_count=self._manifest["site_count"],
            discovered_activation_count=len(self._materialized),
        )


def runtime_from_audited_manifest(
    producer_manifest: Mapping[str, Any],
    identity: Any,
) -> AuditedManifestPhase7Runtime:
    """Bind the static site census; wrappers discover the dynamic census."""

    body = {
        key: value for key, value in producer_manifest.items()
        if key != "manifest_digest"
    }
    if (
        producer_manifest.get("manifest_kind")
        != "unknown-taxonomy-v2-phase7-producer-sites-v2"
        or producer_manifest.get("manifest_digest") != authority_digest(body)
    ):
        raise ValueError("Phase 7 producer manifest authority is invalid")
    sites = tuple(producer_manifest.get("sites", ()))
    if len(sites) != producer_manifest.get("site_count"):
        raise ValueError("Phase 7 producer manifest census is incomplete")
    registry = SealedProducerSiteRegistry(tuple(
        ProducerSiteContract(
            row["producer_site_manifest_id"], row["source_sha256"], row["domain"],
            frozenset(ActivationDisposition(item) for item in row["allowed_dispositions"]),
            tuple(ExpectedCauseSlotContract(
                slot["slot_id"], frozenset(slot["allowed_reason_ids"]),
                slot["expected_domain"], slot["expected_target_kind"],
                slot["expected_identity_scope"], slot["slot_semantics"],
            ) for slot in row["expected_cause_slots"]),
        ) for row in sites
    ))
    return AuditedManifestPhase7Runtime(producer_manifest, identity, registry)
