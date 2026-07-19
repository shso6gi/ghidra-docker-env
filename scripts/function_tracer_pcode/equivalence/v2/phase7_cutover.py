"""Phase 7 umbrella-retirement authority and coverage contracts.

This module deliberately owns no legacy reason aliases.  It turns audited
producer activation, verified lifecycle replay, and typed result projection
into separately sealed authorities so coverage cannot select its own denominator.
"""

from __future__ import annotations

from dataclasses import dataclass, replace
from enum import Enum
from typing import Iterable, Mapping, Sequence

from .contracts import CActiveBaseRow, QOpenBaseRow, authority_digest
from .reducer import CauseLifecycleSnapshot, ShadowLifecycleReducer
from .registry import SealedReasonRegistry, SealedRecoveryRegistry
from .stream import (
    CauseObservedEventAuthority,
    EventIntent,
    EventRecorder,
    EventType,
    GenericReceiptBoundSolverExecutionEventAuthority,
    ReceiptBoundSolverExecutionEventAuthority,
    SealedEventStream,
)


RETIRED_UMBRELLA_REASON_IDS = frozenset({
    "unknown",
    "solver_unknown_timeout",
    "unresolved_expression",
    "equivalence_blocking_unsafety",
    "sat_unsafety",
    "loop_summary_proof_missing",
    "outcome_partition_unknown",
    "method_b_closure_blocked",
})


class ActivationDisposition(str, Enum):
    ELIGIBLE = "ELIGIBLE"
    DECISIVE = "DECISIVE"
    OPERATIONAL_ERROR_NO_SEMANTIC_CAUSE = "OPERATIONAL_ERROR_NO_SEMANTIC_CAUSE"
    LEGACY = "LEGACY"


@dataclass(frozen=True)
class ExpectedCauseSlotContract:
    slot_id: str
    allowed_reason_ids: frozenset[str]
    expected_domain: str
    expected_target_kind: str
    expected_identity_scope: str
    slot_semantics: str = "MANDATORY_CAUSE"

    def __post_init__(self) -> None:
        object.__setattr__(self, "allowed_reason_ids", frozenset(self.allowed_reason_ids))
        if not all(type(value) is str and value for value in (
            self.slot_id, self.expected_domain, self.expected_target_kind,
            self.expected_identity_scope, self.slot_semantics,
        )):
            raise TypeError("expected cause-slot contract identity is incomplete")
        if not self.allowed_reason_ids or any(
            type(item) is not str or not item or item in RETIRED_UMBRELLA_REASON_IDS
            for item in self.allowed_reason_ids
        ):
            raise ValueError("expected cause slot must allow only typed reason IDs")
        if self.slot_semantics not in {
            "MANDATORY_CAUSE", "ALTERNATIVE_REASON_CHOICE",
        }:
            raise ValueError("Phase 7 cause-slot semantics are not sealed")


@dataclass(frozen=True)
class ProducerSiteContract:
    manifest_site_id: str
    source_fingerprint: str
    domain: str
    allowed_dispositions: frozenset[ActivationDisposition]
    eligible_cause_slots: tuple[ExpectedCauseSlotContract, ...]

    def __post_init__(self) -> None:
        if not all(type(value) is str and value for value in (
            self.manifest_site_id, self.source_fingerprint, self.domain,
        )):
            raise TypeError("producer-site identity is incomplete")
        object.__setattr__(self, "allowed_dispositions", frozenset(
            ActivationDisposition(item) for item in self.allowed_dispositions
        ))
        object.__setattr__(self, "eligible_cause_slots", tuple(self.eligible_cause_slots))
        if not self.allowed_dispositions:
            raise ValueError("producer site must seal at least one disposition")
        if any(type(item) is not ExpectedCauseSlotContract for item in self.eligible_cause_slots):
            raise TypeError("producer cause slots require exact typed contracts")
        slot_ids = tuple(item.slot_id for item in self.eligible_cause_slots)
        if len(slot_ids) != len(set(slot_ids)):
            raise ValueError("producer cause-slot IDs must be unique")
        if any(item.expected_domain != self.domain for item in self.eligible_cause_slots):
            raise ValueError("producer cause-slot domain differs from site domain")
        if (
            ActivationDisposition.ELIGIBLE in self.allowed_dispositions
            and not self.eligible_cause_slots
        ):
            raise ValueError("eligible producer site lacks expected cause slots")
        if (
            ActivationDisposition.ELIGIBLE not in self.allowed_dispositions
            and self.eligible_cause_slots
        ):
            raise ValueError("ineligible producer site declares cause slots")


class SealedProducerSiteRegistry:
    def __init__(self, rows: Sequence[ProducerSiteContract]) -> None:
        indexed: dict[str, ProducerSiteContract] = {}
        for row in rows:
            if type(row) is not ProducerSiteContract:
                raise TypeError("producer registry requires exact site contracts")
            if row.manifest_site_id in indexed:
                raise ValueError("duplicate producer manifest site ID")
            indexed[row.manifest_site_id] = row
        if not indexed:
            raise ValueError("producer site registry cannot be empty")
        self._rows = tuple(indexed[key] for key in sorted(indexed))
        self.registry_digest = authority_digest(self._rows)

    def get(self, manifest_site_id: str) -> ProducerSiteContract:
        matches = [row for row in self._rows if row.manifest_site_id == manifest_site_id]
        if len(matches) != 1:
            raise KeyError("producer manifest site is not sealed")
        return matches[0]

    def snapshot(self) -> tuple[ProducerSiteContract, ...]:
        return self._rows

    def cause_slot(
        self, manifest_site_id: str, slot_id: str,
    ) -> ExpectedCauseSlotContract:
        matches = [
            row for row in self.get(manifest_site_id).eligible_cause_slots
            if row.slot_id == slot_id
        ]
        if len(matches) != 1:
            raise KeyError("expected cause slot is not sealed")
        return matches[0]


_ACTIVATION_TOKEN = object()
_EXPECTED_ACTIVATION_TOKEN = object()
_EXPECTED_LEDGER_TOKEN = object()
_RUNTIME_LEDGER_FACTORY_TOKEN = object()


@dataclass(frozen=True)
class ExpectedActivationContract:
    expected_activation_id: str
    producer_site_manifest_id: str
    branch_or_attempt_id: str
    producer_id: str
    disposition: ActivationDisposition
    invocation_ordinal: int = 1
    selected_cause_slot_ids: tuple[str, ...] = ()

    def __post_init__(self) -> None:
        object.__setattr__(self, "disposition", ActivationDisposition(self.disposition))
        object.__setattr__(
            self, "selected_cause_slot_ids", tuple(self.selected_cause_slot_ids)
        )
        if not all(type(value) is str and value for value in (
            self.expected_activation_id, self.producer_site_manifest_id,
            self.branch_or_attempt_id, self.producer_id,
        )):
            raise TypeError("expected activation contract identity is incomplete")
        if type(self.invocation_ordinal) is not int or self.invocation_ordinal < 1:
            raise TypeError("expected activation invocation ordinal is invalid")
        if any(
            type(item) is not str or not item
            for item in self.selected_cause_slot_ids
        ) or len(self.selected_cause_slot_ids) != len(
            set(self.selected_cause_slot_ids)
        ):
            raise TypeError("selected cause-slot IDs are invalid")
        if (
            self.disposition is not ActivationDisposition.ELIGIBLE
            and self.selected_cause_slot_ids
        ):
            raise ValueError("non-eligible activation cannot select cause slots")


@dataclass(frozen=True, init=False)
class ExpectedActivationAuthority:
    contract: ExpectedActivationContract
    result_occurrence_id: str
    expected_ledger_id: str
    expected_ledger_digest: str
    authority_digest: str

    def __init__(self, *values, _factory_token=None) -> None:
        if _factory_token is not _EXPECTED_ACTIVATION_TOKEN:
            raise ValueError("expected activation authorities are factory-issued")
        for name, value in zip(tuple(self.__dataclass_fields__), values):
            object.__setattr__(self, name, value)


@dataclass(frozen=True, init=False)
class SealedExpectedActivationLedger:
    ledger_id: str
    result_occurrence_id: str
    site_registry_digest: str
    authorities: tuple[ExpectedActivationAuthority, ...]
    ledger_digest: str

    def __init__(self, *values, _factory_token=None) -> None:
        if _factory_token is not _EXPECTED_LEDGER_TOKEN:
            raise ValueError("expected activation ledgers are factory-issued")
        for name, value in zip(tuple(self.__dataclass_fields__), values):
            object.__setattr__(self, name, value)


class ExpectedActivationLedgerFactory:
    def __init__(
        self, registry: SealedProducerSiteRegistry, *, ledger_id: str,
        result_occurrence_id: str, expected: Sequence[ExpectedActivationContract],
    ) -> None:
        if not expected:
            raise ValueError("expected activation census cannot be empty")
        rows = tuple(expected)
        if any(type(row) is not ExpectedActivationContract for row in rows):
            raise TypeError("expected activation census requires exact contracts")
        ids = tuple(row.expected_activation_id for row in rows)
        if len(ids) != len(set(ids)):
            raise ValueError("duplicate expected activation identity")
        semantic_keys = tuple((
            row.producer_site_manifest_id, row.branch_or_attempt_id,
            row.producer_id, row.invocation_ordinal,
        ) for row in rows)
        if len(semantic_keys) != len(set(semantic_keys)):
            raise ValueError("duplicate expected semantic activation key")
        if not all(type(value) is str and value for value in (
            ledger_id, result_occurrence_id,
        )):
            raise TypeError("expected activation ledger identity is incomplete")
        normalized = []
        for row in rows:
            site = registry.get(row.producer_site_manifest_id)
            if row.disposition not in site.allowed_dispositions:
                raise ValueError("expected disposition differs from sealed producer site")
            declared_slot_ids = {
                item.slot_id for item in site.eligible_cause_slots
            }
            if row.disposition is ActivationDisposition.ELIGIBLE:
                mandatory_slot_ids = {
                    item.slot_id for item in site.eligible_cause_slots
                    if item.slot_semantics == "MANDATORY_CAUSE"
                }
                alternative_slot_ids = declared_slot_ids - mandatory_slot_ids
                if not row.selected_cause_slot_ids:
                    if alternative_slot_ids:
                        raise ValueError(
                            "eligible activation must select exact alternative cause slots"
                        )
                    row = replace(
                        row, selected_cause_slot_ids=tuple(sorted(mandatory_slot_ids))
                    )
                if not set(row.selected_cause_slot_ids).issubset(
                    declared_slot_ids
                ):
                    raise ValueError(
                        "selected cause slot differs from sealed producer site"
                    )
                if not mandatory_slot_ids.issubset(row.selected_cause_slot_ids):
                    raise ValueError("eligible activation omitted a mandatory cause slot")
                if alternative_slot_ids and len(
                    alternative_slot_ids.intersection(row.selected_cause_slot_ids)
                ) != 1:
                    raise ValueError(
                        "eligible activation must choose one alternative cause slot"
                    )
            normalized.append(row)
        normalized = tuple(sorted(normalized, key=lambda row: row.expected_activation_id))
        digest = authority_digest({
            "ledger_id": ledger_id,
            "result_occurrence_id": result_occurrence_id,
            "site_registry_digest": registry.registry_digest,
            "expected": normalized,
        })
        authorities = tuple(ExpectedActivationAuthority(
            row, result_occurrence_id, ledger_id, digest,
            authority_digest({
                "contract": row,
                "result_occurrence_id": result_occurrence_id,
                "expected_ledger_id": ledger_id,
                "expected_ledger_digest": digest,
            }),
            _factory_token=_EXPECTED_ACTIVATION_TOKEN,
        ) for row in normalized)
        self._registry = registry
        self._authorities = {id(row): row for row in authorities}
        self._ledger = SealedExpectedActivationLedger(
            ledger_id, result_occurrence_id, registry.registry_digest,
            authorities, digest, _factory_token=_EXPECTED_LEDGER_TOKEN,
        )
        self._runtime_opened = False

    @property
    def ledger(self) -> SealedExpectedActivationLedger:
        return self._ledger

    def owns(self, authority: ExpectedActivationAuthority) -> bool:
        return self._authorities.get(id(authority)) is authority

    def owns_ledger(self, ledger: SealedExpectedActivationLedger) -> bool:
        return ledger is self._ledger

    def open_runtime_ledger(self) -> "ProducerActivationLedgerFactory":
        if self._runtime_opened:
            raise ValueError("expected activation ledger already has a runtime census")
        self._runtime_opened = True
        return ProducerActivationLedgerFactory(
            self, self._ledger, self._registry,
            _factory_token=_RUNTIME_LEDGER_FACTORY_TOKEN,
        )


@dataclass(frozen=True, init=False)
class ProducerActivationReceipt:
    activation_id: str
    result_occurrence_id: str
    domain: str
    producer_site_manifest_id: str
    producer_source_fingerprint: str
    branch_or_attempt_id: str
    activation_ledger_id: str
    activation_ledger_digest: str
    expected_disposition: ActivationDisposition
    expected_cause_slot_ids: tuple[str, ...]
    activation_authority_digest: str

    def __init__(self, *values, _factory_token=None) -> None:
        if _factory_token is not _ACTIVATION_TOKEN:
            raise ValueError("activation receipts are factory-issued")
        names = tuple(self.__dataclass_fields__)
        for name, value in zip(names, values):
            object.__setattr__(self, name, value)


_ACTIVATION_LEDGER_TOKEN = object()


@dataclass(frozen=True, init=False)
class SealedProducerActivationLedger:
    ledger_id: str
    site_registry_digest: str
    receipts: tuple[ProducerActivationReceipt, ...]
    ledger_digest: str

    def __init__(self, *values, _factory_token=None) -> None:
        if _factory_token is not _ACTIVATION_LEDGER_TOKEN:
            raise ValueError("activation ledgers are factory-issued")
        names = tuple(self.__dataclass_fields__)
        for name, value in zip(names, values):
            object.__setattr__(self, name, value)


class ProducerActivationLedgerFactory:
    def __init__(
        self, expected_factory: ExpectedActivationLedgerFactory,
        expected_ledger: SealedExpectedActivationLedger,
        registry: SealedProducerSiteRegistry,
        *, _factory_token=None,
    ) -> None:
        if _factory_token is not _RUNTIME_LEDGER_FACTORY_TOKEN:
            raise ValueError("runtime activation ledgers require expected-ledger authority")
        if not expected_factory.owns_ledger(expected_ledger):
            raise ValueError("runtime census expected ledger is not factory-owned")
        self._registry = registry
        self._expected_factory = expected_factory
        self._expected_ledger = expected_ledger
        self._ledger_id = "runtime-" + expected_ledger.ledger_id
        self._result_occurrence_id = expected_ledger.result_occurrence_id
        self._pending: dict[str, ExpectedActivationAuthority] = {}
        self._issued: dict[int, ProducerActivationReceipt] = {}
        self._issued_ledgers: dict[int, SealedProducerActivationLedger] = {}
        self._emission_bindings: dict[int, object] = {}
        self._consumed_emission_bindings: dict[int, object] = {}
        self._bound_occurrences: set[tuple[str, str]] = set()
        self._projection_factory_opened = False
        self._sealed = False

    def record(self, authority: ExpectedActivationAuthority) -> None:
        if self._sealed:
            raise ValueError("activation ledger is already sealed")
        if not self._expected_factory.owns(authority):
            raise ValueError("runtime activation is not expected-ledger authority")
        expected_id = authority.contract.expected_activation_id
        if expected_id in self._pending:
            raise ValueError("duplicate activation identity")
        self._pending[expected_id] = authority

    def seal(self) -> SealedProducerActivationLedger:
        if self._sealed:
            raise ValueError("activation ledger is empty or already sealed")
        expected_ids = {
            row.contract.expected_activation_id
            for row in self._expected_ledger.authorities
        }
        if set(self._pending) != expected_ids:
            raise ValueError("runtime activation census differs from expected ledger")
        provisional = tuple(sorted((
            {
                "activation_id": authority.contract.expected_activation_id,
                "result_occurrence_id": self._result_occurrence_id,
                "domain": self._registry.get(
                    authority.contract.producer_site_manifest_id
                ).domain,
                "producer_site_manifest_id": authority.contract.producer_site_manifest_id,
                "producer_source_fingerprint": self._registry.get(
                    authority.contract.producer_site_manifest_id
                ).source_fingerprint,
                "branch_or_attempt_id": authority.contract.branch_or_attempt_id,
                "expected_disposition": authority.contract.disposition.value,
                "expected_cause_slot_ids": (
                    authority.contract.selected_cause_slot_ids
                    if authority.contract.disposition is ActivationDisposition.ELIGIBLE else ()
                ),
            }
            for authority in self._pending.values()
        ), key=lambda item: item["activation_id"]))
        ledger_digest = authority_digest({
            "ledger_id": self._ledger_id,
            "site_registry_digest": self._registry.registry_digest,
            "activations": provisional,
        })
        receipts = []
        for row in provisional:
            digest = authority_digest({
                **row,
                "activation_ledger_id": self._ledger_id,
                "activation_ledger_digest": ledger_digest,
            })
            receipt = ProducerActivationReceipt(
                row["activation_id"], row["result_occurrence_id"], row["domain"],
                row["producer_site_manifest_id"], row["producer_source_fingerprint"],
                row["branch_or_attempt_id"], self._ledger_id, ledger_digest,
                ActivationDisposition(row["expected_disposition"]),
                tuple(row["expected_cause_slot_ids"]), digest,
                _factory_token=_ACTIVATION_TOKEN,
            )
            receipts.append(receipt)
            self._issued[id(receipt)] = receipt
        self._sealed = True
        ledger = SealedProducerActivationLedger(
            self._ledger_id, self._registry.registry_digest, tuple(receipts), ledger_digest,
            _factory_token=_ACTIVATION_LEDGER_TOKEN,
        )
        self._issued_ledgers[id(ledger)] = ledger
        return ledger

    def owns(self, receipt: ProducerActivationReceipt) -> bool:
        return self._issued.get(id(receipt)) is receipt

    def owns_ledger(self, ledger: SealedProducerActivationLedger) -> bool:
        return (
            type(ledger) is SealedProducerActivationLedger
            and self._issued_ledgers.get(id(ledger)) is ledger
        )

    def cause_slot_contract(
        self, activation: ProducerActivationReceipt, slot_id: str,
    ) -> ExpectedCauseSlotContract:
        if not self.owns(activation):
            raise ValueError("cause-slot lookup requires an owned activation")
        return self._registry.cause_slot(
            activation.producer_site_manifest_id, slot_id
        )

    def expected_contract(
        self, activation: ProducerActivationReceipt,
    ) -> ExpectedActivationContract:
        if not self.owns(activation):
            raise ValueError("expected-contract lookup requires an owned activation")
        matches = [
            row.contract for row in self._expected_ledger.authorities
            if row.contract.expected_activation_id == activation.activation_id
        ]
        if len(matches) != 1:
            raise ValueError("activation does not exactly join expected census")
        return matches[0]

    def bind_emission(
        self, *, activation: ProducerActivationReceipt,
        expected_cause_slot_id: str, occurrence_authority: object,
    ) -> "CauseEmissionBindingReceipt":
        from .contracts import CauseOccurrenceAuthority

        if not self._sealed:
            raise ValueError("emission binding requires a sealed activation census")
        if not self.owns(activation):
            raise ValueError("emission binding activation is not factory-owned")
        if type(occurrence_authority) is not CauseOccurrenceAuthority:
            raise TypeError("emission binding requires exact occurrence data")
        slot = self.cause_slot_contract(activation, expected_cause_slot_id)
        expected = self.expected_contract(activation)
        occurrence = occurrence_authority.occurrence
        site = self._registry.get(activation.producer_site_manifest_id)
        if (
            occurrence.producer_id != expected.producer_id
            or occurrence.attempt_id != expected.branch_or_attempt_id
            or occurrence.reason_id not in slot.allowed_reason_ids
            or occurrence.target_kind != slot.expected_target_kind
            or occurrence.identity_scope.value != slot.expected_identity_scope
            or site.domain != slot.expected_domain
        ):
            raise ValueError(
                "emission does not join expected producer/attempt/slot: "
                f"producer={occurrence.producer_id!r}/{expected.producer_id!r}, "
                f"attempt={occurrence.attempt_id!r}/{expected.branch_or_attempt_id!r}, "
                f"reason={occurrence.reason_id!r}, "
                f"target={occurrence.target_kind!r}/{slot.expected_target_kind!r}, "
                f"scope={occurrence.identity_scope.value!r}/{slot.expected_identity_scope!r}, "
                f"domain={site.domain!r}/{slot.expected_domain!r}"
            )
        occurrence_key = (activation.result_occurrence_id, occurrence.occurrence_id)
        if occurrence_key in self._bound_occurrences:
            raise ValueError("one occurrence cannot cover multiple activation slots")
        payload = {
            "activation_id": activation.activation_id,
            "expected_cause_slot_id": expected_cause_slot_id,
            "result_occurrence_id": activation.result_occurrence_id,
            "producer_site_manifest_id": activation.producer_site_manifest_id,
            "producer_source_fingerprint": activation.producer_source_fingerprint,
            "branch_or_attempt_id": activation.branch_or_attempt_id,
            "producer_id": expected.producer_id,
            "invocation_ordinal": expected.invocation_ordinal,
            "occurrence_id": occurrence.occurrence_id,
            "cause_id": occurrence.cause_id.value,
            "reason_id": occurrence.reason_id,
            "occurrence_authority_digest": authority_digest(occurrence_authority),
        }
        receipt = CauseEmissionBindingReceipt(
            *payload.values(), authority_digest(payload),
            occurrence_authority=occurrence_authority,
            _factory_token=_EMISSION_BINDING_TOKEN,
        )
        self._bound_occurrences.add(occurrence_key)
        self._emission_bindings[id(receipt)] = receipt
        return receipt

    def owns_emission_binding(self, receipt: "CauseEmissionBindingReceipt") -> bool:
        return self._emission_bindings.get(id(receipt)) is receipt

    def consume_emission_binding(
        self, receipt: "CauseEmissionBindingReceipt", consumer: object,
    ) -> None:
        if not self.owns_emission_binding(receipt):
            raise ValueError("cause emission binding is not factory-owned")
        if id(receipt) in self._consumed_emission_bindings:
            raise ValueError("cause emission binding is already consumed")
        self._consumed_emission_bindings[id(receipt)] = consumer

    def open_projection_factory(
        self, finalization_factory: "VerifiedFinalizationBundleFactory",
    ) -> "TypedResultProjectionFactory":
        if not self._sealed:
            raise ValueError("projection factory requires a sealed activation census")
        if self._projection_factory_opened:
            raise ValueError("activation census already has a projection issuer")
        self._projection_factory_opened = True
        return TypedResultProjectionFactory(
            self, finalization_factory, _factory_token=_PROJECTION_FACTORY_TOKEN,
        )


_EMISSION_BINDING_TOKEN = object()


@dataclass(frozen=True, init=False)
class CauseEmissionBindingReceipt:
    activation_id: str
    expected_cause_slot_id: str
    result_occurrence_id: str
    producer_site_manifest_id: str
    producer_source_fingerprint: str
    branch_or_attempt_id: str
    producer_id: str
    invocation_ordinal: int
    occurrence_id: str
    cause_id: str
    reason_id: str
    occurrence_authority_digest: str
    receipt_digest: str
    occurrence_authority: object

    def __init__(
        self, *values, occurrence_authority=None, _factory_token=None,
    ) -> None:
        if _factory_token is not _EMISSION_BINDING_TOKEN:
            raise ValueError("cause-emission bindings are factory-issued")
        field_names = tuple(self.__dataclass_fields__)
        for name, value in zip(field_names[:-1], values):
            object.__setattr__(self, name, value)
        object.__setattr__(self, "occurrence_authority", occurrence_authority)


_EMITTED_CAUSE_TOKEN = object()


@dataclass(frozen=True, init=False)
class EmittedCauseBindingReceipt:
    emission_binding_receipt_digest: str
    result_occurrence_id: str
    stream_id: str
    recorder_authority_id: str
    source_snapshot_fingerprint: str
    event_sequence_number: int
    event_digest: str
    occurrence_id: str
    receipt_digest: str

    def __init__(self, *values, _factory_token=None) -> None:
        if _factory_token is not _EMITTED_CAUSE_TOKEN:
            raise ValueError("emitted-cause bindings are finalization-factory-issued")
        for name, value in zip(tuple(self.__dataclass_fields__), values):
            object.__setattr__(self, name, value)


_FINAL_BUNDLE_TOKEN = object()
_FINAL_RECORDER_TOKEN = object()


class VerifiedFinalizationRecorder:
    def __init__(
        self, recorder: EventRecorder, recorder_authority_id: str,
        *, _factory_token=None,
    ) -> None:
        if _factory_token is not _FINAL_RECORDER_TOKEN:
            raise ValueError("finalization recorders are verifier-factory-issued")
        self._recorder = recorder
        self._recorder_authority_id = recorder_authority_id

    def append(self, intent: EventIntent):
        if type(intent) is not EventIntent:
            raise TypeError("finalization recorder requires exact event intent")
        if intent.event_type == EventType.CAUSE_OBSERVED:
            raise ValueError("CAUSE_OBSERVED requires pre-emission binding consumption")
        return self._recorder.append(intent)


@dataclass(frozen=True, init=False)
class VerifiedFinalizationBundle:
    sealed_event_stream: SealedEventStream
    lifecycle_snapshot: CauseLifecycleSnapshot
    lifecycle_projection: object
    reason_registry_digest: str
    recovery_registry_digest: str
    bundle_digest: str

    def __init__(self, *values, _factory_token=None) -> None:
        if _factory_token is not _FINAL_BUNDLE_TOKEN:
            raise ValueError("finalization bundles are verifier-issued")
        names = tuple(self.__dataclass_fields__)
        for name, value in zip(names, values):
            object.__setattr__(self, name, value)


class VerifiedFinalizationBundleFactory:
    def __init__(
        self, reason_registry: SealedReasonRegistry,
        recovery_registry: SealedRecoveryRegistry,
    ) -> None:
        self._reason_registry = reason_registry
        self._recovery_registry = recovery_registry
        self._reason_digest = authority_digest(reason_registry.snapshot())
        self._recovery_digest = authority_digest(recovery_registry.snapshot())
        self._recorders: dict[int, VerifiedFinalizationRecorder] = {}
        self._issued: dict[int, VerifiedFinalizationBundle] = {}
        self._emitted_causes: dict[int, EmittedCauseBindingReceipt] = {}
        self._consumed_emission_bindings: set[int] = set()
        self._timeout_factory_opened = False
        self._recorder_ordinal = 0

    def open_recorder(
        self, *, stream_id: str, result_occurrence_id: str,
        source_snapshot_fingerprint: str,
    ) -> VerifiedFinalizationRecorder:
        self._recorder_ordinal += 1
        recorder_authority_id = "finalization-recorder-" + authority_digest({
            "stream_id": stream_id,
            "result_occurrence_id": result_occurrence_id,
            "source_snapshot_fingerprint": source_snapshot_fingerprint,
            "ordinal": self._recorder_ordinal,
            "reason_registry_digest": self._reason_digest,
            "recovery_registry_digest": self._recovery_digest,
        })
        wrapper = VerifiedFinalizationRecorder(
            EventRecorder(
                stream_id=stream_id,
                result_occurrence_id=result_occurrence_id,
                source_snapshot_fingerprint=source_snapshot_fingerprint,
            ),
            recorder_authority_id,
            _factory_token=_FINAL_RECORDER_TOKEN,
        )
        self._recorders[id(wrapper)] = wrapper
        return wrapper

    def append_cause_observed(
        self, *, recorder: VerifiedFinalizationRecorder,
        emission_binding: CauseEmissionBindingReceipt,
        activation_factory: ProducerActivationLedgerFactory,
    ) -> EmittedCauseBindingReceipt:
        if self._recorders.get(id(recorder)) is not recorder:
            raise ValueError("cause emission recorder is not open/factory-owned")
        if not activation_factory.owns_emission_binding(emission_binding):
            raise ValueError("cause emission binding is not activation-factory-owned")
        occurrence = emission_binding.occurrence_authority.occurrence
        if occurrence.source_snapshot_fingerprint != recorder._recorder._source_snapshot_fingerprint:
            raise ValueError("cause emission source snapshot differs from recorder")
        if emission_binding.result_occurrence_id != recorder._recorder._result_occurrence_id:
            raise ValueError("cause emission result differs from recorder")
        activation_factory.consume_emission_binding(emission_binding, self)
        event = recorder._recorder.append(EventIntent(
            EventType.CAUSE_OBSERVED,
            CauseObservedEventAuthority(emission_binding.occurrence_authority),
        ))
        payload = {
            "emission_binding_receipt_digest": emission_binding.receipt_digest,
            "result_occurrence_id": emission_binding.result_occurrence_id,
            "stream_id": event.header.stream_id,
            "recorder_authority_id": recorder._recorder_authority_id,
            "source_snapshot_fingerprint": event.header.source_snapshot_fingerprint,
            "event_sequence_number": event.header.sequence_number,
            "event_digest": event.authority_digest,
            "occurrence_id": occurrence.occurrence_id,
        }
        emitted = EmittedCauseBindingReceipt(
            *payload.values(), authority_digest(payload),
            _factory_token=_EMITTED_CAUSE_TOKEN,
        )
        self._consumed_emission_bindings.add(id(emission_binding))
        self._emitted_causes[id(emitted)] = emitted
        return emitted

    def owns_emitted_cause(self, receipt: EmittedCauseBindingReceipt) -> bool:
        return self._emitted_causes.get(id(receipt)) is receipt

    def emitted_for(
        self, emission_binding: CauseEmissionBindingReceipt,
    ) -> EmittedCauseBindingReceipt:
        matches = [
            row for row in self._emitted_causes.values()
            if row.emission_binding_receipt_digest == emission_binding.receipt_digest
        ]
        if len(matches) != 1:
            raise ValueError("pre-emission binding has no unique emitted-cause row")
        return matches[0]

    def issue(self, recorder: VerifiedFinalizationRecorder) -> VerifiedFinalizationBundle:
        if (
            type(recorder) is not VerifiedFinalizationRecorder
            or self._recorders.get(id(recorder)) is not recorder
        ):
            raise ValueError("finalization input stream is not verifier-factory-owned")
        del self._recorders[id(recorder)]
        stream = recorder._recorder.seal()
        stream.validate()
        cause_events = {
            (
                event.header.stream_id,
                event.header.result_occurrence_id,
                event.header.source_snapshot_fingerprint,
                event.header.sequence_number,
                event.authority_digest,
                event.authority_payload.occurrence_authority.occurrence.occurrence_id,
            )
            for event in stream.events
            if event.header.event_type == EventType.CAUSE_OBSERVED
        }
        emitted_rows = {
            (
                row.stream_id,
                row.result_occurrence_id,
                row.source_snapshot_fingerprint,
                row.event_sequence_number,
                row.event_digest,
                row.occurrence_id,
            )
            for row in self._emitted_causes.values()
            if row.recorder_authority_id == recorder._recorder_authority_id
        }
        if cause_events != emitted_rows:
            raise ValueError("CAUSE_OBSERVED stream and emitted-binding census differ")
        reduction = ShadowLifecycleReducer(
            reason_registry=self._reason_registry,
            recovery_registry=self._recovery_registry,
        ).replay(stream)
        payload = {
            "result_occurrence_id": stream.envelope.result_occurrence_id,
            "source_snapshot_fingerprint": stream.envelope.source_snapshot_fingerprint,
            "event_stream_digest": stream.envelope.authority_chain_digest,
            "snapshot_digest": reduction.snapshot.snapshot_digest,
            "lifecycle_projection_digest": reduction.projection.lifecycle_projection_digest,
            "semantic_projection_digest": reduction.projection.semantic_cause_projection_digest,
            "reason_registry_digest": self._reason_digest,
            "recovery_registry_digest": self._recovery_digest,
        }
        bundle = VerifiedFinalizationBundle(
            stream, reduction.snapshot, reduction.projection,
            self._reason_digest, self._recovery_digest, authority_digest(payload),
            _factory_token=_FINAL_BUNDLE_TOKEN,
        )
        self._issued[id(bundle)] = bundle
        return bundle

    def owns(self, bundle: VerifiedFinalizationBundle) -> bool:
        return self._issued.get(id(bundle)) is bundle

    def open_timeout_assignment_factory(self) -> "TerminalTimeoutAssignmentFactory":
        if self._timeout_factory_opened:
            raise ValueError("finalization authority already has a timeout issuer")
        self._timeout_factory_opened = True
        return TerminalTimeoutAssignmentFactory(
            self, _factory_token=_TIMEOUT_FACTORY_TOKEN,
        )


_PROJECTION_TOKEN = object()


@dataclass(frozen=True, init=False)
class TypedResultProjectionReceipt:
    activation_id: str
    expected_cause_slot_id: str
    result_occurrence_id: str
    occurrence_id: str
    cause_id: str
    reason_id: str
    source_snapshot_fingerprint: str
    event_digest: str
    event_stream_digest: str
    semantic_projection_digest: str
    lifecycle_projection_digest: str
    reason_registry_digest: str
    recovery_registry_digest: str
    projection_schema: str
    receipt_digest: str

    def __init__(self, *values, _factory_token=None) -> None:
        if _factory_token is not _PROJECTION_TOKEN:
            raise ValueError("typed result projections are factory-issued")
        names = tuple(self.__dataclass_fields__)
        for name, value in zip(names, values):
            object.__setattr__(self, name, value)


class TypedResultProjectionFactory:
    SCHEMA = "typed-result-projection-v1"

    def __init__(
        self, activation_factory: ProducerActivationLedgerFactory,
        finalization_factory: VerifiedFinalizationBundleFactory,
        *, _factory_token=None,
    ) -> None:
        if _factory_token is not _PROJECTION_FACTORY_TOKEN:
            raise ValueError("typed projection factory is activation-ledger-issued")
        self._activation_factory = activation_factory
        self._finalization_factory = finalization_factory
        self._issued: dict[int, TypedResultProjectionReceipt] = {}
        self._covered_slots: set[tuple[str, str]] = set()
        self._covered_occurrences: set[tuple[str, str]] = set()

    def issue(
        self, *, activation: ProducerActivationReceipt,
        expected_cause_slot_id: str, bundle: VerifiedFinalizationBundle,
        emission_binding: CauseEmissionBindingReceipt,
        emitted_cause: EmittedCauseBindingReceipt,
    ) -> TypedResultProjectionReceipt:
        if not self._activation_factory.owns(activation):
            raise ValueError("projection activation is not factory-owned")
        if not self._finalization_factory.owns(bundle):
            raise ValueError("projection finalization bundle is not verifier-owned")
        if activation.expected_disposition is not ActivationDisposition.ELIGIBLE:
            raise ValueError("ineligible activation cannot issue a typed projection")
        if expected_cause_slot_id not in activation.expected_cause_slot_ids:
            raise ValueError("projection cause slot is not declared by activation")
        slot_contract = self._activation_factory.cause_slot_contract(
            activation, expected_cause_slot_id
        )
        if not self._activation_factory.owns_emission_binding(emission_binding):
            raise ValueError("projection emission binding is not factory-owned")
        if not self._finalization_factory.owns_emitted_cause(emitted_cause):
            raise ValueError("projection emitted-cause binding is not factory-owned")
        if (
            emission_binding.activation_id != activation.activation_id
            or emission_binding.expected_cause_slot_id != expected_cause_slot_id
            or emission_binding.result_occurrence_id != activation.result_occurrence_id
        ):
            raise ValueError("projection emission binding differs from activation slot")
        if (
            emitted_cause.emission_binding_receipt_digest
            != emission_binding.receipt_digest
            or emitted_cause.result_occurrence_id != activation.result_occurrence_id
            or emitted_cause.occurrence_id != emission_binding.occurrence_id
        ):
            raise ValueError("projection emitted-cause row differs from pre-emission binding")
        occurrence_id = emission_binding.occurrence_id
        if activation.result_occurrence_id != bundle.lifecycle_projection.result_occurrence_id:
            raise ValueError("projection activation and bundle results differ")
        bundle.sealed_event_stream.validate()
        bundle.lifecycle_snapshot.validate()
        bundle.lifecycle_projection.validate()
        active = [row for row in bundle.lifecycle_projection.c_active_base
                  if row.occurrence_id == occurrence_id]
        events = [event for event in bundle.sealed_event_stream.events
                  if event.header.event_type == EventType.CAUSE_OBSERVED
                  and type(event.authority_payload) is CauseObservedEventAuthority
                  and event.authority_payload.occurrence_authority.occurrence.occurrence_id
                  == occurrence_id]
        snapshots = [authority for authority in bundle.lifecycle_snapshot.occurrence_authorities
                     if authority.occurrence.occurrence_id == occurrence_id]
        if len(active) > 1 or len(events) != 1 or len(snapshots) != 1:
            raise ValueError("projection requires one exact observed occurrence")
        event = events[0]
        occurrence = snapshots[0].occurrence
        reason_definition = self._finalization_factory._reason_registry.get(
            occurrence.reason_id
        )
        if active:
            row: CActiveBaseRow = active[0]
            projected_identity = (
                row.result_occurrence_id,
                row.occurrence_id,
                row.cause_id,
                row.reason_id,
            )
        else:
            # Producer coverage includes a cause that was observed and then
            # discharged in the same verified lifecycle.  It must not re-enter
            # C_active or the compatibility UNKNOWN projection.
            projected_identity = (
                activation.result_occurrence_id,
                occurrence.occurrence_id,
                occurrence.cause_id.value,
                occurrence.reason_id,
            )
        if (
            projected_identity != (
                activation.result_occurrence_id,
                occurrence.occurrence_id,
                occurrence.cause_id.value,
                occurrence.reason_id,
            )
            or event.authority_payload.occurrence_authority
            is not emission_binding.occurrence_authority
            or event.authority_digest != emitted_cause.event_digest
            or event.header.sequence_number != emitted_cause.event_sequence_number
            or event.header.stream_id != emitted_cause.stream_id
            or authority_digest(event.authority_payload.occurrence_authority)
            != emission_binding.occurrence_authority_digest
            or occurrence.reason_id in RETIRED_UMBRELLA_REASON_IDS
            or occurrence.reason_id not in slot_contract.allowed_reason_ids
            or reason_definition.domain != slot_contract.expected_domain
            or occurrence.target_kind != slot_contract.expected_target_kind
            or occurrence.identity_scope.value != slot_contract.expected_identity_scope
            or occurrence.source_snapshot_fingerprint
            != bundle.sealed_event_stream.envelope.source_snapshot_fingerprint
        ):
            raise ValueError("projection occurrence join is not exact typed authority")
        slot_key = (activation.activation_id, expected_cause_slot_id)
        occurrence_key = (activation.result_occurrence_id, occurrence_id)
        if slot_key in self._covered_slots or occurrence_key in self._covered_occurrences:
            raise ValueError("projection slot/occurrence coverage is not one-to-one")
        payload = {
            "activation_id": activation.activation_id,
            "expected_cause_slot_id": expected_cause_slot_id,
            "result_occurrence_id": activation.result_occurrence_id,
            "occurrence_id": occurrence.occurrence_id,
            "cause_id": occurrence.cause_id.value,
            "reason_id": occurrence.reason_id,
            "source_snapshot_fingerprint": occurrence.source_snapshot_fingerprint,
            "event_digest": event.authority_digest,
            "event_stream_digest": bundle.sealed_event_stream.envelope.authority_chain_digest,
            "semantic_projection_digest": bundle.lifecycle_projection.semantic_cause_projection_digest,
            "lifecycle_projection_digest": bundle.lifecycle_projection.lifecycle_projection_digest,
            "reason_registry_digest": bundle.reason_registry_digest,
            "recovery_registry_digest": bundle.recovery_registry_digest,
            "projection_schema": self.SCHEMA,
        }
        receipt = TypedResultProjectionReceipt(
            *payload.values(), authority_digest(payload), _factory_token=_PROJECTION_TOKEN
        )
        self._covered_slots.add(slot_key)
        self._covered_occurrences.add(occurrence_key)
        self._issued[id(receipt)] = receipt
        return receipt

    def owns(self, receipt: TypedResultProjectionReceipt) -> bool:
        return self._issued.get(id(receipt)) is receipt

    def reason_definition_for(
        self, receipt: TypedResultProjectionReceipt,
    ) -> ReasonDefinition:
        if not self.owns(receipt):
            raise ValueError("production compatibility projection is not issuer-owned")
        return self._finalization_factory._reason_registry.get(receipt.reason_id)


def typed_cause_coverage(
    ledger: SealedProducerActivationLedger,
    activation_factory: ProducerActivationLedgerFactory,
    projection_factory: TypedResultProjectionFactory,
    projections: Iterable[TypedResultProjectionReceipt],
) -> Mapping[str, object]:
    if not activation_factory.owns_ledger(ledger):
        raise ValueError("coverage ledger is not factory-owned")
    if any(not activation_factory.owns(receipt) for receipt in ledger.receipts):
        raise ValueError("coverage ledger contains a non-factory activation")
    eligible = {
        (receipt.activation_id, slot)
        for receipt in ledger.receipts
        for slot in receipt.expected_cause_slot_ids
        if receipt.expected_disposition is ActivationDisposition.ELIGIBLE
    }
    covered = set()
    for projection in projections:
        if not projection_factory.owns(projection):
            raise ValueError("coverage contains a non-factory projection")
        key = (projection.activation_id, projection.expected_cause_slot_id)
        if key not in eligible or key in covered:
            raise ValueError("coverage projection is extra or duplicated")
        covered.add(key)
    missing = tuple(sorted(eligible - covered))
    return {
        "eligible_cause_slot_count": len(eligible),
        "covered_cause_slot_count": len(covered),
        "v2_native_typed_cause_coverage": (
            None if not eligible else len(covered) / len(eligible)
        ),
        "missing_cause_slots": missing,
    }


_PROJECTION_FACTORY_TOKEN = object()
_TIMEOUT_SELECTION_TOKEN = object()
_TIMEOUT_FACTORY_TOKEN = object()


@dataclass(frozen=True, init=False)
class TerminalTimeoutAssignmentReceipt:
    result_occurrence_id: str
    source_snapshot_fingerprint: str
    event_stream_digest: str
    lifecycle_projection_digest: str
    solver_invocation_id: str
    query_digest: str
    execution_identity_digest: str
    assignment_requirement_ids: tuple[str, ...]
    execution_event_digests: tuple[str, ...]
    execution_receipt_digests: tuple[str, ...]
    receipt_digest: str

    def __init__(self, *values, _factory_token=None) -> None:
        if _factory_token is not _TIMEOUT_SELECTION_TOKEN:
            raise ValueError("terminal timeout assignments are factory-issued")
        for name, value in zip(tuple(self.__dataclass_fields__), values):
            object.__setattr__(self, name, value)


class TerminalTimeoutAssignmentFactory:
    """Derive one terminal assignment set from receipt-bound timeout events."""

    def __init__(
        self, finalization_factory: VerifiedFinalizationBundleFactory,
        *, _factory_token=None,
    ) -> None:
        if _factory_token is not _TIMEOUT_FACTORY_TOKEN:
            raise ValueError("timeout assignment factory is finalization-authority-issued")
        self._finalization_factory = finalization_factory
        self._issued: dict[int, TerminalTimeoutAssignmentReceipt] = {}
        self._selected_bundles: dict[int, VerifiedFinalizationBundle] = {}

    def issue(
        self, bundle: VerifiedFinalizationBundle,
    ) -> TerminalTimeoutAssignmentReceipt:
        if not self._finalization_factory.owns(bundle):
            raise ValueError("timeout selection bundle is not verifier-owned")
        if self._selected_bundles.get(id(bundle)) is bundle:
            raise ValueError("finalization bundle already has a timeout selection")
        solver_timeouts = tuple(
            event for event in bundle.sealed_event_stream.events
            if event.header.event_type == EventType.SOLVER_TIMEOUT
        )
        if any(
            not hasattr(event.authority_payload, "terminal_candidate")
            for event in solver_timeouts
        ):
            raise ValueError("SOLVER_TIMEOUT authority lacks terminal-candidate binding")
        all_terminal_candidates = tuple(
            event for event in solver_timeouts
            if event.authority_payload.terminal_candidate is True
        )
        if any(
            type(event.authority_payload)
            is not GenericReceiptBoundSolverExecutionEventAuthority
            for event in all_terminal_candidates
        ):
            raise ValueError("terminal timeout candidate lacks result-bound generic receipt")
        events = all_terminal_candidates
        if any(
            event.header.event_type == EventType.PROCESS_TIMEOUT
            for event in bundle.sealed_event_stream.events
        ):
            raise ValueError("process timeout requires its durable result-bound selector")
        if not events:
            raise ValueError("terminal timeout set must contain every exact receipt-bound candidate")
        invocation_ids = {event.authority_payload.solver_invocation_id for event in events}
        query_digests = {event.authority_payload.query_digest for event in events}
        execution_identities = {
            event.authority_payload.execution_receipt_authority[
                "execution_identity_digest"
            ] for event in events
        }
        if (
            len(invocation_ids) != 1
            or len(query_digests) != 1
            or len(execution_identities) != 1
        ):
            raise ValueError("terminal timeout assignment events are not one execution")
        for event in events:
            authority = event.authority_payload.execution_receipt_authority
            if authority["result_occurrence_id"] != (
                bundle.lifecycle_projection.result_occurrence_id
            ):
                raise ValueError("timeout execution receipt belongs to another result")
        assignments = tuple(sorted(
            event.authority_payload.proof_requirement_id for event in events
        ))
        if len(assignments) != len(set(assignments)):
            raise ValueError("terminal timeout assignment set contains duplicates")
        projection = bundle.lifecycle_projection
        q_by_id = {row.proof_requirement_id: row for row in projection.q_open_base}
        if any(item not in q_by_id for item in assignments):
            raise ValueError("timeout assignment is absent from final live frontier")
        c_keys = {
            (row.result_occurrence_id, row.occurrence_id, row.cause_id)
            for row in projection.c_active_base
        }
        q_rows = tuple(q_by_id[item] for item in assignments)
        if any(
            row.result_occurrence_id != projection.result_occurrence_id
            or (row.result_occurrence_id, row.occurrence_id, row.cause_id) not in c_keys
            for row in q_rows
        ):
            raise ValueError("timeout assignment lacks exact active semantic cause")
        payload = {
            "result_occurrence_id": projection.result_occurrence_id,
            "source_snapshot_fingerprint": (
                bundle.sealed_event_stream.envelope.source_snapshot_fingerprint
            ),
            "event_stream_digest": bundle.sealed_event_stream.envelope.authority_chain_digest,
            "lifecycle_projection_digest": projection.lifecycle_projection_digest,
            "solver_invocation_id": next(iter(invocation_ids)),
            "query_digest": next(iter(query_digests)),
            "execution_identity_digest": next(iter(execution_identities)),
            "assignment_requirement_ids": assignments,
            "execution_event_digests": tuple(event.authority_digest for event in events),
            "execution_receipt_digests": tuple(
                event.authority_payload.execution_receipt_digest for event in events
            ),
        }
        receipt = TerminalTimeoutAssignmentReceipt(
            *payload.values(), authority_digest(payload),
            _factory_token=_TIMEOUT_SELECTION_TOKEN,
        )
        self._selected_bundles[id(bundle)] = bundle
        self._issued[id(receipt)] = receipt
        return receipt

    def owns(self, receipt: TerminalTimeoutAssignmentReceipt) -> bool:
        return self._issued.get(id(receipt)) is receipt
