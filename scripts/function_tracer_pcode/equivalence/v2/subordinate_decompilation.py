"""Typed authority joining secondary decompilation to an existing parent Q."""

from __future__ import annotations

from dataclasses import dataclass, field
from types import MappingProxyType
from typing import Any, Mapping

from .call_effect import CALL_EFFECT_REASON_REGISTRY, CALL_EFFECT_RECOVERY_REGISTRY
from .contracts import VerifiedLifecyclePrefixProjection, authority_digest
from .loop_recurrence import LOOP_REASON_REGISTRY, LOOP_RECOVERY_REGISTRY
from .stream import CauseObservedEventAuthority, EventStreamPrefixView, EventType


SUBORDINATE_ADAPTER_REGISTRY_ID = "subordinate-decompilation-adapter-v1"
SUBORDINATE_ADAPTER_REGISTRY_VERSION = 1
SUBORDINATE_ASSIGNMENT_ISSUER = "subordinate-decompilation-assignment-factory-v1"
SUBORDINATE_PROCESS_ISSUER = "decompiler-process-runner-v1"
SUBORDINATE_PROCESS_STAGE = "function_decompilation_artifact"

CALL_EFFECT_PARENT_REGISTRY_ID = "call-effect-memory-v2"
CALL_EFFECT_PARENT_REGISTRY_VERSION = 1
CALL_EFFECT_PARENT_REGISTRY_DIGEST = (
    "9c078cca2afef7b82c16f0795f160e80f0c5d42779e1022cdf3e63853e2e2c0d"
)
LOOP_PARENT_REGISTRY_ID = "loop-recurrence-summary-v2"
LOOP_PARENT_REGISTRY_VERSION = 1
LOOP_PARENT_REGISTRY_DIGEST = (
    "3feffdc5a2d8dc432b6042aefa5367a8816a9d3cf3d38237eec5e907be44561c"
)


@dataclass(frozen=True)
class SubordinateDecompilationAdapterRow:
    adapter_id: str
    source_contract_id: str
    parent_reason_id: str
    parent_proof_kind: str
    parent_registry_id: str
    parent_registry_version: int
    parent_registry_digest: str
    parent_producer_contract_ids: tuple[str, ...]
    assignment_issuer_id: str
    process_stage: str
    process_issuer_id: str
    allowed_status: str
    terminal_eligible: bool
    terminal_priority: int

    def __post_init__(self) -> None:
        strings = tuple(
            getattr(self, name) for name in self.__dataclass_fields__
            if name not in {
                "parent_registry_version", "terminal_eligible", "terminal_priority",
                "parent_producer_contract_ids",
            }
        )
        if not all(type(value) is str and value for value in strings):
            raise TypeError("subordinate adapter row string identity is incomplete")
        if type(self.parent_registry_version) is not int or self.parent_registry_version <= 0:
            raise TypeError("subordinate parent registry version is invalid")
        if type(self.terminal_eligible) is not bool or self.terminal_eligible is not True:
            raise TypeError("subordinate adapter must be terminal eligible")
        if type(self.terminal_priority) is not int or self.terminal_priority <= 0:
            raise TypeError("subordinate adapter priority is invalid")
        if (
            type(self.parent_producer_contract_ids) is not tuple
            or not self.parent_producer_contract_ids
            or any(type(value) is not str or not value for value in self.parent_producer_contract_ids)
            or len(set(self.parent_producer_contract_ids)) != len(self.parent_producer_contract_ids)
        ):
            raise TypeError("subordinate parent producer contracts are invalid")
        if (
            self.assignment_issuer_id != SUBORDINATE_ASSIGNMENT_ISSUER
            or self.process_stage != SUBORDINATE_PROCESS_STAGE
            or self.process_issuer_id != SUBORDINATE_PROCESS_ISSUER
            or self.allowed_status != "attempted"
        ):
            raise ValueError("subordinate adapter execution contract is not sealed")

    def authority_tuple(self) -> tuple[Any, ...]:
        return tuple(getattr(self, name) for name in self.__dataclass_fields__)


@dataclass(frozen=True)
class SubordinateParentBinding:
    """Exact parent identity supplied by the producer owning the refresh."""

    result_occurrence_id: str
    occurrence_id: str
    cause_id: str
    proof_requirement_id: str
    semantic_target_digest: str

    def __post_init__(self) -> None:
        if not all(type(value) is str and value for value in (
            self.result_occurrence_id,
            self.occurrence_id,
            self.cause_id,
            self.proof_requirement_id,
            self.semantic_target_digest,
        )):
            raise TypeError("subordinate parent binding identity is incomplete")

    def to_authority_dict(self) -> Mapping[str, str]:
        return {
            "result_occurrence_id": self.result_occurrence_id,
            "occurrence_id": self.occurrence_id,
            "cause_id": self.cause_id,
            "proof_requirement_id": self.proof_requirement_id,
            "semantic_target_digest": self.semantic_target_digest,
        }


@dataclass(frozen=True)
class SubordinateParentBindingRequiredDiagnostic:
    """Typed fail-closed diagnostic when refresh has multiple proposals."""

    source_contract_id: str
    proposal_digests: tuple[str, ...]
    result_occurrence_id: str | None = None
    diagnostic_kind: str = "PARENT_BINDING_REQUIRED"

    def __post_init__(self) -> None:
        if type(self.source_contract_id) is not str or not self.source_contract_id:
            raise TypeError("subordinate binding diagnostic source is incomplete")
        if type(self.proposal_digests) is not tuple or not self.proposal_digests:
            raise TypeError("subordinate binding diagnostic proposals are incomplete")
        if any(
            type(value) is not str or not value for value in self.proposal_digests
        ) or len(set(self.proposal_digests)) != len(self.proposal_digests):
            raise TypeError("subordinate binding diagnostic proposals are invalid")
        if self.result_occurrence_id is not None and (
            type(self.result_occurrence_id) is not str
            or not self.result_occurrence_id
        ):
            raise TypeError("subordinate binding diagnostic result is invalid")
        if self.diagnostic_kind != "PARENT_BINDING_REQUIRED":
            raise ValueError("subordinate binding diagnostic kind is not sealed")

    def to_authority_dict(self) -> Mapping[str, Any]:
        return {
            "diagnostic_kind": self.diagnostic_kind,
            "source_contract_id": self.source_contract_id,
            "proposal_digests": self.proposal_digests,
            "result_occurrence_id": self.result_occurrence_id,
        }

    @property
    def diagnostic_digest(self) -> str:
        return authority_digest(self.to_authority_dict())

    def to_signed_authority_dict(self) -> Mapping[str, Any]:
        return {
            **self.to_authority_dict(),
            "diagnostic_digest": self.diagnostic_digest,
        }


def _row(
    adapter_id: str, source: str, reason: str, proof_kind: str,
    registry_id: str, version: int, digest: str,
    producer_contract_ids: tuple[str, ...], priority: int,
) -> SubordinateDecompilationAdapterRow:
    return SubordinateDecompilationAdapterRow(
        adapter_id, source, reason, proof_kind,
        registry_id, version, digest, producer_contract_ids,
        SUBORDINATE_ASSIGNMENT_ISSUER, SUBORDINATE_PROCESS_STAGE,
        SUBORDINATE_PROCESS_ISSUER, "attempted", True, priority,
    )


SUBORDINATE_DECOMPILATION_ADAPTER_ROWS = (
    _row(
        "fresh-callee-parameter-decomp-v1",
        "return-analyzer-lifecycle-helper-decompile-v2",
        "call_argument_extraction_incomplete", "call_argument_extraction",
        CALL_EFFECT_PARENT_REGISTRY_ID, CALL_EFFECT_PARENT_REGISTRY_VERSION,
        CALL_EFFECT_PARENT_REGISTRY_DIGEST,
        ("internal_typed_pure_direct_call_stage_producer",), 191,
    ),
    _row(
        "callee-effect-summary-decomp-v1", "callee-effect-summary-decompile-v2",
        "callee_effect_summary_incomplete", "callee_effect_summary",
        CALL_EFFECT_PARENT_REGISTRY_ID, CALL_EFFECT_PARENT_REGISTRY_VERSION,
        CALL_EFFECT_PARENT_REGISTRY_DIGEST,
        (
            "internal_typed_pure_direct_call_stage_producer",
            "typed-summary-effect-prerequisite-v2",
        ), 192,
    ),
    _row(
        "inline-region-state-decomp-v1", "inline-region-state-decompile-v2",
        "inline_region_semantics_incomplete", "inline_region_state_transformer",
        CALL_EFFECT_PARENT_REGISTRY_ID, CALL_EFFECT_PARENT_REGISTRY_VERSION,
        CALL_EFFECT_PARENT_REGISTRY_DIGEST,
        ("internal_typed_pure_direct_call_stage_producer",), 193,
    ),
    _row(
        "recurrence-proposal-refresh-decomp-v1",
        "structural-recurrence-refresh-decompile-v2",
        "recurrence_proposal_validation_unproven",
        "recurrence_transition_termination_validation",
        LOOP_PARENT_REGISTRY_ID, LOOP_PARENT_REGISTRY_VERSION,
        LOOP_PARENT_REGISTRY_DIGEST, ("typed-recurrence-proposal-signal-v2",), 194,
    ),
    _row(
        "summary-return-refresh-decomp-v1",
        "structural-recurrence-refresh-decompile-v2",
        "summary_return_extraction_incomplete", "summary_return_extraction",
        LOOP_PARENT_REGISTRY_ID, LOOP_PARENT_REGISTRY_VERSION,
        LOOP_PARENT_REGISTRY_DIGEST, ("typed-summary-acceptance-signal-v2",), 195,
    ),
    _row(
        "summary-transition-refresh-decomp-v1",
        "structural-recurrence-refresh-decompile-v2",
        "summary_recurrence_transition_validation_incomplete",
        "summary_recurrence_transition_validation",
        LOOP_PARENT_REGISTRY_ID, LOOP_PARENT_REGISTRY_VERSION,
        LOOP_PARENT_REGISTRY_DIGEST, ("typed-summary-acceptance-signal-v2",), 196,
    ),
)

SUBORDINATE_DECOMPILATION_ADAPTER_REGISTRY: Mapping[str, SubordinateDecompilationAdapterRow] = MappingProxyType(
    {row.adapter_id: row for row in SUBORDINATE_DECOMPILATION_ADAPTER_ROWS}
)
SUBORDINATE_DECOMPILATION_ADAPTER_REGISTRY_DIGEST = authority_digest({
    "registry_id": SUBORDINATE_ADAPTER_REGISTRY_ID,
    "registry_version": SUBORDINATE_ADAPTER_REGISTRY_VERSION,
    "rows": tuple(row.authority_tuple() for row in SUBORDINATE_DECOMPILATION_ADAPTER_ROWS),
})


@dataclass(frozen=True)
class SubordinateParentAuthorityDiagnostic:
    """Signed, lossless diagnostics for subordinate parent resolution."""

    diagnostic_kind: str
    source_contract_id: str
    adapter_row_count: int
    parent_proof_kind_match_q_count: int
    binding_match_q_count: int
    c_q_candidate_count: int
    occurrence_ids: tuple[str, ...]
    parent_reason_ids: tuple[str, ...]
    parent_domains: tuple[str, ...]
    parent_producers: tuple[str, ...]
    prefix_chain_digest: str
    projection_digest: str
    q_open_base_digest: str
    adapter_ids: tuple[str, ...]
    parent_observations: tuple[Mapping[str, Any], ...]
    mismatch_reasons: tuple[str, ...]
    requested_parent_binding: Mapping[str, str] | None = None

    def __post_init__(self) -> None:
        if not all(type(value) is str and value for value in (
            self.diagnostic_kind,
            self.source_contract_id,
            self.prefix_chain_digest,
            self.projection_digest,
            self.q_open_base_digest,
        )):
            raise TypeError("subordinate authority diagnostic identity is incomplete")
        if any(
            type(value) is not int or value < 0
            for value in (
                self.adapter_row_count,
                self.parent_proof_kind_match_q_count,
                self.binding_match_q_count,
                self.c_q_candidate_count,
            )
        ):
            raise TypeError("subordinate authority diagnostic counts are invalid")
        for values in (
            self.occurrence_ids,
            self.parent_reason_ids,
            self.parent_domains,
            self.parent_producers,
            self.adapter_ids,
            self.mismatch_reasons,
        ):
            if type(values) is not tuple or any(
                type(value) is not str or not value for value in values
            ):
                raise TypeError("subordinate authority diagnostic rows are invalid")
        if type(self.parent_observations) is not tuple or any(
            not isinstance(value, Mapping) for value in self.parent_observations
        ):
            raise TypeError("subordinate authority diagnostic observations are invalid")
        if self.requested_parent_binding is not None and not isinstance(
            self.requested_parent_binding, Mapping
        ):
            raise TypeError("subordinate requested parent binding is invalid")

    def to_authority_dict(self) -> Mapping[str, Any]:
        return {
            "diagnostic_kind": self.diagnostic_kind,
            "source_contract_id": self.source_contract_id,
            "adapter_row_count": self.adapter_row_count,
            "parent_proof_kind_match_q_count": self.parent_proof_kind_match_q_count,
            "binding_match_q_count": self.binding_match_q_count,
            "c_q_candidate_count": self.c_q_candidate_count,
            "occurrence_ids": self.occurrence_ids,
            "parent_reason_ids": self.parent_reason_ids,
            "parent_domains": self.parent_domains,
            "parent_producers": self.parent_producers,
            "prefix_chain_digest": self.prefix_chain_digest,
            "projection_digest": self.projection_digest,
            "q_open_base_digest": self.q_open_base_digest,
            "adapter_ids": self.adapter_ids,
            "parent_observations": self.parent_observations,
            "mismatch_reasons": self.mismatch_reasons,
            "requested_parent_binding": self.requested_parent_binding,
        }

    @property
    def diagnostic_digest(self) -> str:
        return authority_digest(self.to_authority_dict())

    def to_signed_authority_dict(self) -> Mapping[str, Any]:
        return {
            **self.to_authority_dict(),
            "diagnostic_digest": self.diagnostic_digest,
        }


class SubordinateParentAuthorityError(ValueError):
    """A typed fail-closed parent-resolution authority failure."""

    def __init__(self, diagnostic: SubordinateParentAuthorityDiagnostic, message: str):
        if type(diagnostic) is not SubordinateParentAuthorityDiagnostic:
            raise TypeError("subordinate authority failure lacks exact diagnostic")
        self.diagnostic = diagnostic
        super().__init__(
            f"{message}; signed_diagnostic="
            f"{diagnostic.to_signed_authority_dict()!r}"
        )


class SubordinateParentNotLive(SubordinateParentAuthorityError):
    """The source has no live recovery parent and needs standalone ownership."""
EXPECTED_SUBORDINATE_DECOMPILATION_ADAPTER_REGISTRY_DIGEST = (
    "e1d8bb3c21a4985e84020afd7974a9f0342cd93b112c0e9f5fdaa76f5fae576c"
)

_PARENT_DOMAIN_BY_REGISTRY = MappingProxyType({
    CALL_EFFECT_PARENT_REGISTRY_ID: "expression_call_effect_memory",
    LOOP_PARENT_REGISTRY_ID: "loop_recurrence_summary",
})


def _authority_for_occurrence(
    prefix: EventStreamPrefixView, occurrence_id: str,
) -> Any:
    prefix.validate()
    rows = tuple(
        event.authority_payload.occurrence_authority
        for event in prefix.events
        if (
            event.header.event_type is EventType.CAUSE_OBSERVED
            and type(event.authority_payload) is CauseObservedEventAuthority
            and event.authority_payload.occurrence_authority.occurrence.occurrence_id
            == occurrence_id
        )
    )
    if len(rows) != 1:
        raise ValueError("subordinate parent occurrence producer is not unique")
    return rows[0]


def _validate_parent_occurrence_authority(row: Any, authority: Any) -> str:
    registry = (
        CALL_EFFECT_REASON_REGISTRY
        if row.parent_registry_id == CALL_EFFECT_PARENT_REGISTRY_ID
        else LOOP_REASON_REGISTRY
    )
    recovery = (
        CALL_EFFECT_RECOVERY_REGISTRY
        if row.parent_registry_id == CALL_EFFECT_PARENT_REGISTRY_ID
        else LOOP_RECOVERY_REGISTRY
    )
    definition = registry.get(row.parent_reason_id)
    authority.occurrence.validate_against(definition, authority.bound_contract)
    bound = authority.bound_contract
    expected_contract = recovery.get(
        bound.contract_definition_id, bound.contract_version
    )
    if bound.normalized_expression_digest != expected_contract.normalized_expression_digest:
        raise ValueError("subordinate parent recovery contract is not exact registry membership")
    producer = authority.occurrence.producer_id
    if type(producer) is not str or not producer:
        raise ValueError("subordinate parent occurrence producer is incomplete")
    return producer


def validate_subordinate_adapter_registry() -> None:
    if len(SUBORDINATE_DECOMPILATION_ADAPTER_REGISTRY) != 6:
        raise ValueError("subordinate adapter registry must contain exactly six rows")
    if len({row.terminal_priority for row in SUBORDINATE_DECOMPILATION_ADAPTER_ROWS}) != 6:
        raise ValueError("subordinate terminal priorities must form a total order")
    actual_parent_digests = {
        CALL_EFFECT_PARENT_REGISTRY_ID: authority_digest({
            "reason_registry": CALL_EFFECT_REASON_REGISTRY.snapshot()
        }),
        LOOP_PARENT_REGISTRY_ID: authority_digest({
            "reason_registry": LOOP_REASON_REGISTRY.snapshot()
        }),
    }
    registries = {
        CALL_EFFECT_PARENT_REGISTRY_ID: CALL_EFFECT_REASON_REGISTRY,
        LOOP_PARENT_REGISTRY_ID: LOOP_REASON_REGISTRY,
    }
    for row in SUBORDINATE_DECOMPILATION_ADAPTER_ROWS:
        definition = registries[row.parent_registry_id].get(row.parent_reason_id)
        if (
            actual_parent_digests[row.parent_registry_id] != row.parent_registry_digest
            or definition.canonicalization_policy_id != row.parent_registry_id
            or row.parent_proof_kind not in definition.allowed_proof_kinds
        ):
            raise ValueError("subordinate adapter parent registry membership is invalid")
    if (
        SUBORDINATE_DECOMPILATION_ADAPTER_REGISTRY_DIGEST
        != EXPECTED_SUBORDINATE_DECOMPILATION_ADAPTER_REGISTRY_DIGEST
    ):
        raise ValueError("subordinate adapter registry digest drift")


_SUBORDINATE_ASSIGNMENT_TOKEN = object()
_SUBORDINATE_INVOCATION_TOKEN = object()
_SUBORDINATE_EXECUTION_TOKEN = object()


@dataclass(frozen=True)
class SubordinateProcessAssignmentReceipt:
    result_occurrence_id: str
    adapter_id: str
    source_contract_id: str
    parent_reason_id: str
    parent_proof_kind: str
    parent_registry_id: str
    parent_registry_version: int
    parent_registry_digest: str
    parent_producer_contract_id: str
    lifecycle_prefix_projection_digest: str
    q_open_base_digest: str
    occurrence_id: str
    cause_id: str
    proof_requirement_id: str
    semantic_target_digest: str
    process_stage: str
    process_issuer_id: str
    terminal_priority: int
    adapter_registry_digest: str
    assignment_receipt_digest: str
    _factory_token: object = field(default=None, repr=False, compare=False)

    def validate_against(
        self, projection: VerifiedLifecyclePrefixProjection, *,
        prefix: EventStreamPrefixView,
        factory: "SubordinateProcessAssignmentFactory",
    ) -> None:
        factory.validate(self, projection, prefix)


@dataclass(frozen=True)
class SubordinateProcessInvocationReceipt:
    result_occurrence_id: str
    adapter_id: str
    proof_requirement_id: str
    assignment_receipt_digest: str
    operational_invocation_receipt_digest: str
    target_digest: str
    input_surface_digest: str
    invocation_ordinal: int
    invocation_binding_digest: str
    _factory_token: object = field(default=None, repr=False, compare=False)


@dataclass(frozen=True)
class SubordinateProcessExecutionReceipt:
    result_occurrence_id: str
    adapter_id: str
    proof_requirement_id: str
    invocation_binding_digest: str
    operational_attempt_receipt_digest: str
    observation_digest: str
    disposition: str
    completed_artifact_digest: str | None
    allowed_status: str
    terminal_priority: int
    execution_receipt_digest: str
    _factory_token: object = field(default=None, repr=False, compare=False)


class SubordinateProcessAssignmentFactory:
    def __init__(self, result_occurrence_id: str) -> None:
        if type(result_occurrence_id) is not str or not result_occurrence_id:
            raise TypeError("subordinate factory result occurrence is incomplete")
        self.result_occurrence_id = result_occurrence_id
        self._issued: dict[int, SubordinateProcessAssignmentReceipt] = {}
        self._invocations: dict[int, SubordinateProcessInvocationReceipt] = {}
        self._executions: dict[int, SubordinateProcessExecutionReceipt] = {}

    def validate(
        self, receipt: SubordinateProcessAssignmentReceipt,
        projection: VerifiedLifecyclePrefixProjection,
        prefix: EventStreamPrefixView,
    ) -> None:
        if (
            type(receipt) is not SubordinateProcessAssignmentReceipt
            or receipt._factory_token is not _SUBORDINATE_ASSIGNMENT_TOKEN
            or self._issued.get(id(receipt)) is not receipt
        ):
            raise TypeError("subordinate process assignment is not exact factory membership")
        projection.validate()
        prefix.validate()
        if projection.event_stream_prefix_digest != prefix.prefix_chain_digest:
            raise ValueError("subordinate projection does not bind the supplied prefix")
        row = SUBORDINATE_DECOMPILATION_ADAPTER_REGISTRY.get(receipt.adapter_id)
        if row is None:
            raise ValueError("subordinate assignment adapter is not registered")
        q_matches = tuple(q for q in projection.q_open_base if (
            q.occurrence_id == receipt.occurrence_id
            and q.cause_id == receipt.cause_id
            and q.proof_requirement_id == receipt.proof_requirement_id
            and q.proof_kind == receipt.parent_proof_kind
            and q.semantic_target_digest == receipt.semantic_target_digest
        ))
        c_matches = tuple(c for c in projection.c_active_base if (
            c.occurrence_id == receipt.occurrence_id
            and c.cause_id == receipt.cause_id
            and c.reason_id == receipt.parent_reason_id
            and c.domain == _PARENT_DOMAIN_BY_REGISTRY[row.parent_registry_id]
        ))
        producer = _validate_parent_occurrence_authority(
            row, _authority_for_occurrence(prefix, receipt.occurrence_id)
        )
        payload = {
            name: getattr(receipt, name) for name in receipt.__dataclass_fields__
            if name not in {"assignment_receipt_digest", "_factory_token"}
        }
        if (
            receipt.result_occurrence_id != projection.result_occurrence_id
            or receipt.lifecycle_prefix_projection_digest != projection.prefix_projection_digest
            or receipt.q_open_base_digest != projection.q_open_base_digest
            or len(q_matches) != 1 or len(c_matches) != 1
            or producer != receipt.parent_producer_contract_id
            or producer not in row.parent_producer_contract_ids
            or receipt.adapter_registry_digest != SUBORDINATE_DECOMPILATION_ADAPTER_REGISTRY_DIGEST
            or receipt.assignment_receipt_digest != authority_digest(payload)
            or (
                receipt.adapter_id, receipt.source_contract_id,
                receipt.parent_reason_id, receipt.parent_proof_kind,
                receipt.parent_registry_id, receipt.parent_registry_version,
                receipt.parent_registry_digest, receipt.process_stage,
                receipt.process_issuer_id, receipt.terminal_priority,
            ) != (
                row.adapter_id, row.source_contract_id,
                row.parent_reason_id, row.parent_proof_kind,
                row.parent_registry_id, row.parent_registry_version,
                row.parent_registry_digest, row.process_stage,
                row.process_issuer_id, row.terminal_priority,
            )
        ):
            raise ValueError("subordinate process assignment integrity mismatch")

    def issue_for_source(
        self, projection: VerifiedLifecyclePrefixProjection,
        prefix: EventStreamPrefixView, source_contract_id: str, *,
        parent_binding: SubordinateParentBinding | None = None,
    ) -> SubordinateProcessAssignmentReceipt:
        projection.validate()
        prefix.validate()
        if projection.event_stream_prefix_digest != prefix.prefix_chain_digest:
            raise ValueError("subordinate projection does not bind the supplied prefix")
        if projection.result_occurrence_id != self.result_occurrence_id:
            raise ValueError("subordinate projection belongs to another result")
        if parent_binding is not None:
            if type(parent_binding) is not SubordinateParentBinding:
                raise TypeError("subordinate parent binding is not exact")
            if parent_binding.result_occurrence_id != self.result_occurrence_id:
                raise ValueError("subordinate parent binding belongs to another result")
        rows = tuple(
            row for row in SUBORDINATE_DECOMPILATION_ADAPTER_ROWS
            if row.source_contract_id == source_contract_id
        )
        candidates = []
        observations = []
        mismatch_reasons = set()
        occurrence_ids = set()
        parent_reason_ids = {row.parent_reason_id for row in rows}
        parent_domains = {
            _PARENT_DOMAIN_BY_REGISTRY[row.parent_registry_id] for row in rows
        }
        parent_producers = set()
        parent_proof_kind_match_q_count = 0
        binding_match_q_count = 0
        for row in rows:
            proof_kind_q_rows = tuple(
                q_row for q_row in projection.q_open_base
                if q_row.proof_kind == row.parent_proof_kind
            )
            parent_proof_kind_match_q_count += len(proof_kind_q_rows)
            q_rows = (
                proof_kind_q_rows
                if parent_binding is None
                else tuple(
                    q_row for q_row in proof_kind_q_rows
                    if (
                        q_row.occurrence_id == parent_binding.occurrence_id
                        and q_row.cause_id == parent_binding.cause_id
                        and q_row.proof_requirement_id
                        == parent_binding.proof_requirement_id
                        and q_row.semantic_target_digest
                        == parent_binding.semantic_target_digest
                    )
                )
            )
            binding_match_q_count += len(q_rows)
            for q_row in q_rows:
                occurrence_ids.add(q_row.occurrence_id)
                observation = {
                    "adapter_id": row.adapter_id,
                    "parent_proof_kind": row.parent_proof_kind,
                    "occurrence_id": q_row.occurrence_id,
                    "cause_id": q_row.cause_id,
                    "proof_requirement_id": q_row.proof_requirement_id,
                    "semantic_target_digest": q_row.semantic_target_digest,
                    "parent_reason_id": row.parent_reason_id,
                    "parent_domain": _PARENT_DOMAIN_BY_REGISTRY[
                        row.parent_registry_id
                    ],
                    "expected_parent_producer_contract_ids": (
                        row.parent_producer_contract_ids
                    ),
                    "proof_kind_q_count_before_binding": len(proof_kind_q_rows),
                    "binding_match_q_count": len(q_rows),
                }
                c_rows = tuple(
                    c_row for c_row in projection.c_active_base
                    if (
                        c_row.occurrence_id == q_row.occurrence_id
                        and c_row.cause_id == q_row.cause_id
                    )
                )
                observation["matching_occurrence_c_count"] = len(c_rows)
                try:
                    producer = _validate_parent_occurrence_authority(
                        row, _authority_for_occurrence(prefix, q_row.occurrence_id)
                    )
                except (KeyError, TypeError, ValueError) as exc:
                    mismatch_reasons.add(
                        "parent_authority_invalid:" + type(exc).__name__
                    )
                    observation["parent_authority_error"] = (
                        f"{type(exc).__name__}: {exc}"
                    )
                    observations.append(observation)
                    continue
                parent_producers.add(producer)
                observation["parent_producer"] = producer
                exact_c_rows = tuple(
                    c_row for c_row in c_rows
                    if (
                        c_row.reason_id == row.parent_reason_id
                        and c_row.domain == _PARENT_DOMAIN_BY_REGISTRY[
                            row.parent_registry_id
                        ]
                        and producer in row.parent_producer_contract_ids
                    )
                )
                observation["c_rows"] = tuple({
                    "reason_id": c_row.reason_id,
                    "domain": c_row.domain,
                } for c_row in c_rows)
                observation["exact_c_row_count"] = len(exact_c_rows)
                if not exact_c_rows:
                    if not any(
                        c_row.reason_id == row.parent_reason_id
                        for c_row in c_rows
                    ):
                        mismatch_reasons.add("parent_reason_mismatch")
                    if not any(
                        c_row.domain == _PARENT_DOMAIN_BY_REGISTRY[
                            row.parent_registry_id
                        ]
                        for c_row in c_rows
                    ):
                        mismatch_reasons.add("parent_domain_mismatch")
                    if producer not in row.parent_producer_contract_ids:
                        mismatch_reasons.add("parent_producer_mismatch")
                for c_row in exact_c_rows:
                    candidates.append((row, c_row, q_row, producer))
                observations.append(observation)
        if parent_binding is not None and not candidates:
            mismatch_reasons.add("requested_parent_binding_not_found")
        diagnostic_kind = "SUBORDINATE_ADAPTER_ROW_MISSING"
        diagnostic_message = (
            "subordinate source has no adapter row for source_contract_id"
        )
        if rows:
            if not parent_proof_kind_match_q_count:
                diagnostic_kind = "PARENT_C_Q_NOT_LIVE"
                diagnostic_message = "subordinate source has no live parent C/Q"
            elif parent_binding is not None and not binding_match_q_count:
                diagnostic_kind = "PARENT_C_Q_BINDING_MISMATCH"
                diagnostic_message = (
                    "subordinate source parent binding does not match live parent Q"
                )
            elif not candidates:
                diagnostic_kind = "PARENT_C_Q_CONTRACT_MISMATCH"
                diagnostic_message = "subordinate source parent C/Q contract mismatch"
            elif len(candidates) != 1:
                diagnostic_kind = "PARENT_C_Q_AMBIGUOUS"
                diagnostic_message = (
                    "subordinate source requires exactly one live parent C/Q"
                )
            else:
                diagnostic_kind = "PARENT_C_Q_RESOLVED"
                diagnostic_message = "subordinate source parent C/Q resolved"
        diagnostic = SubordinateParentAuthorityDiagnostic(
            diagnostic_kind,
            source_contract_id,
            len(rows),
            parent_proof_kind_match_q_count,
            binding_match_q_count,
            len(candidates),
            tuple(sorted(occurrence_ids)),
            tuple(sorted(parent_reason_ids)),
            tuple(sorted(parent_domains)),
            tuple(sorted(parent_producers)),
            prefix.prefix_chain_digest,
            projection.prefix_projection_digest,
            projection.q_open_base_digest,
            tuple(row.adapter_id for row in rows),
            tuple(observations),
            tuple(sorted(mismatch_reasons)),
            (
                parent_binding.to_authority_dict()
                if parent_binding is not None else None
            ),
        )
        if diagnostic_kind == "SUBORDINATE_ADAPTER_ROW_MISSING":
            raise SubordinateParentAuthorityError(diagnostic, diagnostic_message)
        if diagnostic_kind == "PARENT_C_Q_NOT_LIVE":
            raise SubordinateParentNotLive(diagnostic, diagnostic_message)
        if diagnostic_kind == "PARENT_C_Q_BINDING_MISMATCH":
            raise SubordinateParentAuthorityError(diagnostic, diagnostic_message)
        if diagnostic_kind == "PARENT_C_Q_CONTRACT_MISMATCH":
            raise SubordinateParentAuthorityError(diagnostic, diagnostic_message)
        if diagnostic_kind == "PARENT_C_Q_AMBIGUOUS":
            raise SubordinateParentAuthorityError(diagnostic, diagnostic_message)
        row, c_row, q_row, producer = candidates[0]
        payload = {
            "result_occurrence_id": self.result_occurrence_id,
            "adapter_id": row.adapter_id,
            "source_contract_id": row.source_contract_id,
            "parent_reason_id": row.parent_reason_id,
            "parent_proof_kind": row.parent_proof_kind,
            "parent_registry_id": row.parent_registry_id,
            "parent_registry_version": row.parent_registry_version,
            "parent_registry_digest": row.parent_registry_digest,
            "parent_producer_contract_id": producer,
            "lifecycle_prefix_projection_digest": projection.prefix_projection_digest,
            "q_open_base_digest": projection.q_open_base_digest,
            "occurrence_id": q_row.occurrence_id,
            "cause_id": q_row.cause_id,
            "proof_requirement_id": q_row.proof_requirement_id,
            "semantic_target_digest": q_row.semantic_target_digest,
            "process_stage": row.process_stage,
            "process_issuer_id": row.process_issuer_id,
            "terminal_priority": row.terminal_priority,
            "adapter_registry_digest": SUBORDINATE_DECOMPILATION_ADAPTER_REGISTRY_DIGEST,
        }
        receipt = SubordinateProcessAssignmentReceipt(
            **payload, assignment_receipt_digest=authority_digest(payload),
            _factory_token=_SUBORDINATE_ASSIGNMENT_TOKEN,
        )
        if any(
            existing.assignment_receipt_digest == receipt.assignment_receipt_digest
            for existing in self._issued.values()
        ):
            raise ValueError("duplicate subordinate process assignment")
        self._issued[id(receipt)] = receipt
        self.validate(receipt, projection, prefix)
        return receipt

    def bind_invocation(
        self, assignment: SubordinateProcessAssignmentReceipt, *,
        projection: VerifiedLifecyclePrefixProjection,
        prefix: EventStreamPrefixView, invocation: Any,
        operational_factory: Any,
    ) -> SubordinateProcessInvocationReceipt:
        self.validate(assignment, projection, prefix)
        operational_factory.validate_invocation_membership(invocation)
        if (
            invocation.result_occurrence_id != self.result_occurrence_id
            or invocation.proof_requirement_id != assignment.proof_requirement_id
        ):
            raise ValueError("subordinate invocation differs from parent assignment")
        payload = {
            "result_occurrence_id": self.result_occurrence_id,
            "adapter_id": assignment.adapter_id,
            "proof_requirement_id": assignment.proof_requirement_id,
            "assignment_receipt_digest": assignment.assignment_receipt_digest,
            "operational_invocation_receipt_digest": invocation.receipt_digest,
            "target_digest": invocation.target_digest,
            "input_surface_digest": invocation.input_surface_digest,
            "invocation_ordinal": invocation.invocation_ordinal,
        }
        receipt = SubordinateProcessInvocationReceipt(
            **payload, invocation_binding_digest=authority_digest(payload),
            _factory_token=_SUBORDINATE_INVOCATION_TOKEN,
        )
        self._invocations[id(receipt)] = receipt
        self.validate_invocation_binding(receipt)
        return receipt

    def validate_invocation_binding(
        self, receipt: SubordinateProcessInvocationReceipt,
    ) -> None:
        if (
            type(receipt) is not SubordinateProcessInvocationReceipt
            or receipt._factory_token is not _SUBORDINATE_INVOCATION_TOKEN
            or self._invocations.get(id(receipt)) is not receipt
        ):
            raise TypeError("subordinate invocation binding is not exact factory membership")
        payload = {
            name: getattr(receipt, name) for name in receipt.__dataclass_fields__
            if name not in {"invocation_binding_digest", "_factory_token"}
        }
        if receipt.invocation_binding_digest != authority_digest(payload):
            raise ValueError("subordinate invocation binding digest mismatch")

    def bind_execution(
        self, invocation_binding: SubordinateProcessInvocationReceipt, *,
        assignment: SubordinateProcessAssignmentReceipt,
        projection: VerifiedLifecyclePrefixProjection,
        prefix: EventStreamPrefixView, attempt: Any,
        completed_artifact: Any = None, operational_factory: Any,
    ) -> SubordinateProcessExecutionReceipt:
        self.validate(assignment, projection, prefix)
        self.validate_invocation_binding(invocation_binding)
        if (
            invocation_binding.assignment_receipt_digest
            != assignment.assignment_receipt_digest
        ):
            raise TypeError("subordinate invocation binding is not exact factory membership")
        operational_factory.validate_attempt_membership(attempt)
        if (
            attempt.invocation_receipt_digest
            != invocation_binding.operational_invocation_receipt_digest
            or attempt.proof_requirement_id != assignment.proof_requirement_id
            or attempt.result_occurrence_id != self.result_occurrence_id
        ):
            raise ValueError("subordinate attempt differs from bound invocation")
        artifact_digest = None
        if completed_artifact is not None:
            operational_factory.validate_artifact_membership(completed_artifact)
            if completed_artifact.attempt_receipt_digest != attempt.receipt_digest:
                raise ValueError("subordinate completed artifact belongs to another attempt")
            artifact_digest = completed_artifact.artifact_digest
        if (attempt.disposition.value == "COMPLETED") != (artifact_digest is not None):
            raise ValueError("subordinate completion artifact/disposition mismatch")
        row = SUBORDINATE_DECOMPILATION_ADAPTER_REGISTRY[assignment.adapter_id]
        payload = {
            "result_occurrence_id": self.result_occurrence_id,
            "adapter_id": assignment.adapter_id,
            "proof_requirement_id": assignment.proof_requirement_id,
            "invocation_binding_digest": invocation_binding.invocation_binding_digest,
            "operational_attempt_receipt_digest": attempt.receipt_digest,
            "observation_digest": attempt.observation_digest,
            "disposition": attempt.disposition.value,
            "completed_artifact_digest": artifact_digest,
            "allowed_status": row.allowed_status,
            "terminal_priority": row.terminal_priority,
        }
        receipt = SubordinateProcessExecutionReceipt(
            **payload, execution_receipt_digest=authority_digest(payload),
            _factory_token=_SUBORDINATE_EXECUTION_TOKEN,
        )
        self._executions[id(receipt)] = receipt
        self.validate_execution(receipt)
        return receipt

    def validate_execution(
        self, receipt: SubordinateProcessExecutionReceipt,
    ) -> None:
        if (
            type(receipt) is not SubordinateProcessExecutionReceipt
            or receipt._factory_token is not _SUBORDINATE_EXECUTION_TOKEN
            or self._executions.get(id(receipt)) is not receipt
        ):
            raise TypeError("subordinate execution is not exact factory membership")
        payload = {
            name: getattr(receipt, name) for name in receipt.__dataclass_fields__
            if name not in {"execution_receipt_digest", "_factory_token"}
        }
        if receipt.execution_receipt_digest != authority_digest(payload):
            raise ValueError("subordinate execution receipt digest mismatch")

    def validate_runtime_execution(
        self, execution: SubordinateProcessExecutionReceipt, *,
        assignment: SubordinateProcessAssignmentReceipt,
        projection: VerifiedLifecyclePrefixProjection,
        prefix: EventStreamPrefixView, invocation: Any, attempt: Any,
        completed_artifact: Any, operational_factory: Any,
    ) -> None:
        """Revalidate the complete subordinate chain before durable publication."""
        self.validate(assignment, projection, prefix)
        self.validate_execution(execution)
        operational_factory.validate_invocation_membership(invocation)
        operational_factory.validate_attempt_membership(attempt)
        operational_factory.validate_artifact_membership(completed_artifact)
        bindings = tuple(
            item for item in self._invocations.values()
            if item.invocation_binding_digest
            == execution.invocation_binding_digest
        )
        if len(bindings) != 1:
            raise ValueError("subordinate execution lacks one exact invocation binding")
        binding = bindings[0]
        self.validate_invocation_binding(binding)
        if (
            binding.assignment_receipt_digest
            != assignment.assignment_receipt_digest
            or binding.operational_invocation_receipt_digest
            != invocation.receipt_digest
            or execution.proof_requirement_id != assignment.proof_requirement_id
            or execution.operational_attempt_receipt_digest != attempt.receipt_digest
            or execution.disposition != "COMPLETED"
            or execution.completed_artifact_digest
            != completed_artifact.artifact_digest
            or attempt.invocation_receipt_digest != invocation.receipt_digest
            or completed_artifact.attempt_receipt_digest != attempt.receipt_digest
        ):
            raise ValueError("subordinate runtime execution chain does not join")


validate_subordinate_adapter_registry()
