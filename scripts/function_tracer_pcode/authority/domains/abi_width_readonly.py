"""Sealed Phase 6.5 ABI, return-width, and readonly authority model.

This module owns semantic cause identity and proof-work identity only.  It does
not infer final outcomes and it never turns solver status into a ReasonId.
"""

from __future__ import annotations

from dataclasses import dataclass
from enum import Enum
import threading
from types import MappingProxyType
from typing import Any, Iterable, Mapping, Optional

from scripts.function_tracer_pcode.authority.domains.sat_safety_ledger import SAT_SAFETY_LEDGER_KEYS
from scripts.function_tracer_pcode.authority.contracts import (
    CauseOccurrence,
    CauseOccurrenceAuthority,
    CauseTransformationEvent,
    CauseTransformationProofReceipt,
    IdentityScope,
    ProofRequirement,
    ReasonDefinition,
    RecoveryAddressability,
    RequirementCompletionReceipt,
    RequirementSlotDefinition,
    SatisfactionContractDefinition,
    TransformationKind,
    authority_digest,
    canonical_value,
    requirement_slot,
)
from scripts.function_tracer_pcode.authority.lifecycle.execution_authority import (
    ProducerStageContract,
    ProducerStageRegistry,
)
from scripts.function_tracer_pcode.authority.registry import (
    SatisfactionBindingFactory,
    SealedReasonRegistry,
    SealedRecoveryRegistry,
    SemanticCauseIdentityFactory,
)
from scripts.function_tracer_pcode.authority.lifecycle.stream import (
    CauseObservedEventAuthority,
    CauseTransformedEventAuthority,
    EventIntent,
    EventType,
    GenericReceiptBoundSolverExecutionEventAuthority,
    RequirementCompletedEventAuthority,
)


ABI_WIDTH_READONLY_DOMAIN_ID = "abi-return-width-readonly-v2"
ABI_WIDTH_READONLY_REGISTRY_VERSION = 1



#: commit を終えた取引の、取引の前の台帳の写し（取引の終わりまで残す）。
_ABI_COMMITTED_ROLLBACK_SNAPSHOTS_KEY = "abi_width_committed_rollback_snapshots"


def _restore_abi_transaction_snapshots(state: dict, snapshots: dict) -> None:
    for key, (existed, snapshot) in snapshots.items():
        if existed:
            state[key] = snapshot
        else:
            state.pop(key, None)

class AbiWidthReadonlyCapability(str, Enum):
    STRUCTURAL_ONLY = "STRUCTURAL_ONLY"
    STRUCTURAL_OR_SOLVER_UNSAT = "STRUCTURAL_OR_SOLVER_UNSAT"


class AbiWidthReadonlyDisposition(str, Enum):
    TYPED_SLICE5_CAUSE = "TYPED_SLICE5_CAUSE"
    LEGACY_DIAGNOSTIC = "LEGACY_DIAGNOSTIC"
    REFINED_TO_SLICE3 = "REFINED_TO_SLICE3"
    REFINED_TO_SLICE4 = "REFINED_TO_SLICE4"
    INFRASTRUCTURE_INVALID = "INFRASTRUCTURE_INVALID"


class ReturnAbiFactStatus(str, Enum):
    PRESENT = "PRESENT"
    MISSING = "MISSING"
    MALFORMED = "MALFORMED"


class ReturnAbiRelationStatus(str, Enum):
    PROVED = "PROVED"
    UNPROVEN = "UNPROVEN"
    INVALID = "INVALID"


class ReturnAbiAuthorityInvalid(ValueError):
    """Typed fail-closed error for malformed or invalid ABI authority."""

    canonical_error_kind = "return_abi_authority_invalid"

    def __init__(self, reason_code: str, *, malformed_slots=(), detail: str = ""):
        self.reason_code = str(reason_code)
        self.malformed_slots = tuple(str(slot) for slot in malformed_slots)
        self.detail = str(detail or "")
        super().__init__(
            "return ABI authority invalid: "
            + self.reason_code
            + (f" malformed_slots={self.malformed_slots!r}" if self.malformed_slots else "")
            + (f" detail={self.detail}" if self.detail else "")
        )


@dataclass(frozen=True)
class AbiWidthReadonlyReasonSpec:
    reason_id: str
    identity_scope: IdentityScope
    target_kind: str
    proof_kind: str
    category: str

    @property
    def contract_definition_id(self) -> str:
        return self.reason_id + "-recovery"


_REASON_ROWS = (
    ("return_width_provenance_unavailable", IdentityScope.UNARY, "return_site_slot", "return_width_provenance", "return_width"),
    ("return_width_relation_unproven", IdentityScope.UNARY, "same_function_return_pair", "same_function_return_width_relation", "return_width"),
    ("return_abi_provenance_unavailable", IdentityScope.UNARY, "return_site_slot", "return_abi_provenance", "abi"),
    ("return_observation_contract_unproven", IdentityScope.RELATIONAL, "return_observation_pair", "return_observation_contract", "return_width"),
    ("return_abi_relation_unproven", IdentityScope.RELATIONAL, "return_observation_pair", "return_abi_relation", "abi"),
    ("return_high_bit_relation_unproven", IdentityScope.RELATIONAL, "return_observation_pair", "return_high_bit_relation", "return_width"),
    ("readonly_storage_identity_unproven", IdentityScope.UNARY, "readonly_load_site", "readonly_storage_identity", "readonly_identity"),
    ("readonly_object_correspondence_unproven", IdentityScope.RELATIONAL, "readonly_reduction_object_sets", "readonly_object_correspondence", "readonly_identity"),
)


ABI_WIDTH_READONLY_REASON_SPECS: Mapping[str, AbiWidthReadonlyReasonSpec] = (
    MappingProxyType({
        row[0]: AbiWidthReadonlyReasonSpec(*row)
        for row in _REASON_ROWS
    })
)
if len(ABI_WIDTH_READONLY_REASON_SPECS) != len(_REASON_ROWS):
    raise ValueError("duplicate Phase 6.5 reason specification")


def _reason_definition(spec: AbiWidthReadonlyReasonSpec) -> ReasonDefinition:
    return ReasonDefinition(
        spec.reason_id,
        spec.category,
        "proof_obligation",
        "blocks_decision",
        frozenset((spec.target_kind,)),
        ("stable_site_identity", "source_snapshot", "missing_proposition"),
        frozenset((spec.proof_kind,)),
        True,
        ABI_WIDTH_READONLY_DOMAIN_ID,
        RecoveryAddressability.REQUIREMENT_REQUIRED,
    )


def _satisfaction_contract(spec: AbiWidthReadonlyReasonSpec) -> SatisfactionContractDefinition:
    return SatisfactionContractDefinition(
        spec.contract_definition_id,
        1,
        (RequirementSlotDefinition("proof", frozenset((spec.proof_kind,))),),
        requirement_slot("proof"),
    )


ABI_WIDTH_READONLY_REASON_REGISTRY = SealedReasonRegistry.build(
    _reason_definition(spec) for spec in ABI_WIDTH_READONLY_REASON_SPECS.values()
)
ABI_WIDTH_READONLY_RECOVERY_REGISTRY = SealedRecoveryRegistry.build(
    _satisfaction_contract(spec)
    for spec in ABI_WIDTH_READONLY_REASON_SPECS.values()
)


@dataclass(frozen=True)
class AbiWidthReadonlyProducerStageSpec:
    producer_contract_id: str
    producer_version: str
    proof_stage: str
    proof_kind: str
    capability: AbiWidthReadonlyCapability
    execution_issuer_id: str
    allowed_statuses: tuple[str, ...]
    terminal_eligible_statuses: tuple[str, ...]
    terminal_priority: int

    def __post_init__(self) -> None:
        if type(self.capability) is not AbiWidthReadonlyCapability:
            if type(self.capability) is not str:
                raise TypeError(
                    "Phase 6.5 producer capability must be an exact Enum or string"
                )
            try:
                capability = AbiWidthReadonlyCapability(self.capability)
            except ValueError as exc:
                raise ValueError(
                    "Phase 6.5 producer capability is not sealed"
                ) from exc
            object.__setattr__(self, "capability", capability)
        object.__setattr__(self, "allowed_statuses", tuple(sorted(self.allowed_statuses)))
        object.__setattr__(
            self,
            "terminal_eligible_statuses",
            tuple(sorted(self.terminal_eligible_statuses)),
        )
        if not self.allowed_statuses:
            raise ValueError("Phase 6.5 producer statuses cannot be empty")
        if not set(self.terminal_eligible_statuses).issubset(self.allowed_statuses):
            raise ValueError("Phase 6.5 terminal statuses differ from allowed statuses")

    def to_authority_tuple(self) -> tuple[Any, ...]:
        return (
            self.producer_contract_id,
            self.producer_version,
            self.proof_stage,
            self.proof_kind,
            self.capability.value,
            self.execution_issuer_id,
            self.allowed_statuses,
            self.terminal_eligible_statuses,
            self.terminal_priority,
        )

    def to_common_contract(self) -> ProducerStageContract:
        return ProducerStageContract(
            ABI_WIDTH_READONLY_DOMAIN_ID,
            self.producer_contract_id,
            self.producer_version,
            self.proof_stage,
            self.execution_issuer_id,
            frozenset(self.allowed_statuses),
            frozenset(self.terminal_eligible_statuses),
            self.terminal_priority,
        )


_STAGE_ROWS = (
    ("return-width-provenance-validator-v2", "2", "return_width_provenance", "return_width_provenance", AbiWidthReadonlyCapability.STRUCTURAL_ONLY, "abi-width-structural-proof-factory-v1", ("structural_proof",), (), 110),
    ("same-function-return-width-relation-validator-v2", "2", "same_function_return_width_relation", "same_function_return_width_relation", AbiWidthReadonlyCapability.STRUCTURAL_ONLY, "abi-width-structural-proof-factory-v1", ("structural_proof",), (), 120),
    ("return-abi-provenance-validator-v2", "2", "return_abi_provenance", "return_abi_provenance", AbiWidthReadonlyCapability.STRUCTURAL_ONLY, "abi-width-structural-proof-factory-v1", ("structural_proof",), (), 130),
    ("return-observation-contract-validator-v2", "2", "return_observation_contract", "return_observation_contract", AbiWidthReadonlyCapability.STRUCTURAL_ONLY, "abi-width-structural-proof-factory-v1", ("structural_proof",), (), 140),
    ("return-abi-relation-validator-v2", "2", "return_abi_relation", "return_abi_relation", AbiWidthReadonlyCapability.STRUCTURAL_ONLY, "abi-width-structural-proof-factory-v1", ("structural_proof",), (), 150),
    ("return-high-bit-relation-solver-v2", "2", "return_high_bit_relation", "return_high_bit_relation", AbiWidthReadonlyCapability.STRUCTURAL_OR_SOLVER_UNSAT, "parallel-solver-runner-v1", ("attempted",), ("attempted",), 160),
    ("readonly-storage-identity-validator-v2", "2", "readonly_storage_identity", "readonly_storage_identity", AbiWidthReadonlyCapability.STRUCTURAL_ONLY, "abi-width-structural-proof-factory-v1", ("structural_proof",), (), 170),
    ("readonly-object-correspondence-validator-v2", "2", "readonly_object_correspondence", "readonly_object_correspondence", AbiWidthReadonlyCapability.STRUCTURAL_OR_SOLVER_UNSAT, "parallel-solver-runner-v1", ("attempted",), ("attempted",), 180),
)


ABI_WIDTH_READONLY_PRODUCER_STAGE_SPECS = tuple(
    AbiWidthReadonlyProducerStageSpec(*row) for row in _STAGE_ROWS
)


def abi_width_readonly_registry_authority_dict() -> dict[str, Any]:
    return {
        "registry_id": ABI_WIDTH_READONLY_DOMAIN_ID,
        "registry_version": ABI_WIDTH_READONLY_REGISTRY_VERSION,
        "rows": tuple(
            item.to_authority_tuple()
            for item in ABI_WIDTH_READONLY_PRODUCER_STAGE_SPECS
        ),
    }


ABI_WIDTH_READONLY_PRODUCER_STAGE_REGISTRY_DIGEST = authority_digest(
    abi_width_readonly_registry_authority_dict()
)
ABI_WIDTH_READONLY_COMMON_EXECUTION_STAGE_REGISTRY = ProducerStageRegistry(
    ABI_WIDTH_READONLY_REGISTRY_VERSION,
    tuple(
        item.to_common_contract()
        for item in ABI_WIDTH_READONLY_PRODUCER_STAGE_SPECS
    ),
)
EXPECTED_ABI_WIDTH_READONLY_PRODUCER_STAGE_REGISTRY_DIGEST = (
    "2161081892ca7a9faca9c60c6e93d82e14c008ca219b2d5f33c920d63c5722ab"
)
EXPECTED_ABI_WIDTH_READONLY_COMMON_REGISTRY_DIGEST = (
    "551027e8142ff34fe691aa34351dc3d784cc81a617c748caa57cfcf650495465"
)
if ABI_WIDTH_READONLY_PRODUCER_STAGE_REGISTRY_DIGEST != (
    EXPECTED_ABI_WIDTH_READONLY_PRODUCER_STAGE_REGISTRY_DIGEST
):
    raise ValueError("Phase 6.5 producer registry authority digest drift")
if ABI_WIDTH_READONLY_COMMON_EXECUTION_STAGE_REGISTRY.normalized_registry_digest != (
    EXPECTED_ABI_WIDTH_READONLY_COMMON_REGISTRY_DIGEST
):
    raise ValueError("Phase 6.5 common registry authority digest drift")


_WIDTH_SLOTS = frozenset({
    "return_storage_fact", "payload_width_fact", "extension_evidence_fact",
})
_ABI_SLOTS = frozenset({
    "calling_convention", "declared_or_effective_return_type",
    "return_storage_descriptor",
})
_READONLY_RELATION_CODES = frozenset({
    "semantic_key_mismatch", "readonly_contract_mismatch",
    "readonly_contract_missing_term_sequence",
    "readonly_contract_term_sequence_mismatch",
})
_READONLY_UNARY_CODES = frozenset({
    "semantic_key_missing", "semantic_key_unavailable", "semantic_key_none",
})

# Exhaustive production ownership census.  These are semantic source families,
# not call-site strings: every sealed reason must have at least one typed source
# and a new reason cannot enter the registry without declaring its producer.
ABI_WIDTH_READONLY_PRODUCTION_SOURCE_REASON_IDS = {
    "return_width_surface.unary_seed": ("return_width_provenance_unavailable",),
    "summary_return_acceptance.same_function_pair": ("return_width_relation_unproven",),
    "return_abi_facts.missing_slot": ("return_abi_provenance_unavailable",),
    "return_abi_compatibility.unproven": ("return_abi_relation_unproven",),
    "return_observation.need_or_projection": ("return_observation_contract_unproven",),
    "return_observation.projection_high_bits": ("return_high_bit_relation_unproven",),
    "readonly_reduction.member_identity": ("readonly_storage_identity_unproven",),
    "readonly_reduction.object_correspondence": ("readonly_object_correspondence_unproven",),
}


def validate_abi_width_readonly_production_source_conservation() -> None:
    owned = []
    for source, reason_ids in ABI_WIDTH_READONLY_PRODUCTION_SOURCE_REASON_IDS.items():
        if type(source) is not str or not source or not reason_ids:
            raise ValueError("Phase 6.5 production source ownership is incomplete")
        if len(reason_ids) != len(set(reason_ids)) or any(
            reason_id not in ABI_WIDTH_READONLY_REASON_SPECS
            for reason_id in reason_ids
        ):
            raise ValueError("Phase 6.5 production source owns an invalid reason set")
        owned.extend(reason_ids)
    if set(owned) != set(ABI_WIDTH_READONLY_REASON_SPECS):
        raise ValueError("Phase 6.5 production sources do not cover the sealed registry")


@dataclass(frozen=True)
class AbiWidthReadonlySourceClassification:
    disposition: AbiWidthReadonlyDisposition
    reason_ids: tuple[str, ...]
    source_contract: str
    source_code: str

    def __post_init__(self) -> None:
        if self.disposition is AbiWidthReadonlyDisposition.TYPED_SLICE5_CAUSE:
            if not self.reason_ids or any(
                item not in ABI_WIDTH_READONLY_REASON_SPECS
                for item in self.reason_ids
            ):
                raise ValueError("typed Phase 6.5 source lacks sealed reason ownership")
        elif self.reason_ids:
            raise ValueError("non-typed Phase 6.5 disposition cannot own reasons")


def classify_summary_width_source(source_code: str) -> AbiWidthReadonlySourceClassification:
    if source_code == "summary_return_candidate_invalid:return_width_missing":
        reasons = ("return_width_provenance_unavailable",)
    elif source_code == "summary_return_overlap_unproven:return_width_mismatch":
        reasons = ("return_width_relation_unproven",)
    else:
        return AbiWidthReadonlySourceClassification(
            AbiWidthReadonlyDisposition.INFRASTRUCTURE_INVALID,
            (), "summary_return_acceptance", source_code,
        )
    return AbiWidthReadonlySourceClassification(
        AbiWidthReadonlyDisposition.TYPED_SLICE5_CAUSE,
        reasons, "summary_return_acceptance", source_code,
    )


def classify_readonly_source(source_code: str) -> AbiWidthReadonlySourceClassification:
    if source_code in _READONLY_UNARY_CODES:
        disposition = AbiWidthReadonlyDisposition.TYPED_SLICE5_CAUSE
        reasons = ("readonly_storage_identity_unproven",)
    elif source_code in _READONLY_RELATION_CODES:
        disposition = AbiWidthReadonlyDisposition.TYPED_SLICE5_CAUSE
        reasons = ("readonly_object_correspondence_unproven",)
    elif source_code == "readonly_contract_result_width_mismatch":
        disposition = AbiWidthReadonlyDisposition.TYPED_SLICE5_CAUSE
        reasons = (
            "return_observation_contract_unproven",
            "return_high_bit_relation_unproven",
        )
    elif source_code in {"readonly_contract_missing_effect_profile", "readonly_contract_effects_unproven"}:
        disposition = AbiWidthReadonlyDisposition.REFINED_TO_SLICE3
        reasons = ()
    elif source_code == "readonly_contract_missing_loop":
        disposition = AbiWidthReadonlyDisposition.REFINED_TO_SLICE4
        reasons = ()
    else:
        disposition = AbiWidthReadonlyDisposition.INFRASTRUCTURE_INVALID
        reasons = ()
    return AbiWidthReadonlySourceClassification(
        disposition, reasons, "readonly_loop_fallback", source_code,
    )


_RETURN_ABI_SEED_TOKEN = object()


def _sealed_return_abi_present_value(slot: str, value: Any) -> tuple[Any, ...]:
    """Validate and return one canonical immutable PRESENT ABI fact."""

    if type(value) is not tuple:
        raise ValueError("PRESENT return ABI fact is not an immutable tuple")
    if slot == "calling_convention":
        if len(value) != 2 or value[0] != "ghidra_calling_convention_v1" or (
            type(value[1]) is not str or not value[1].strip()
        ):
            raise ValueError("calling-convention fact schema is malformed")
        return (value[0], value[1].strip())
    if slot == "declared_or_effective_return_type":
        if len(value) != 3 or value[0] != "ghidra_return_type_v1" or (
            type(value[1]) is not str or not value[1].strip()
        ) or type(value[2]) is not int or type(value[2]) is bool or value[2] < 0:
            raise ValueError("return-type fact schema is malformed")
        return (value[0], value[1].strip(), value[2])
    if slot == "return_storage_descriptor":
        if len(value) != 2 or value[0] != "ghidra_return_storage_v1" or (
            type(value[1]) is not tuple or not value[1]
        ):
            raise ValueError("return-storage fact schema is malformed")
        members = []
        for member in value[1]:
            if type(member) is not tuple or len(member) != 4 or (
                member[0] != "ghidra_return_storage_member_v1"
                or type(member[1]) is not str or not member[1].strip()
                or type(member[2]) is not int or type(member[2]) is bool or member[2] < 0
                or type(member[3]) is not int or type(member[3]) is bool or member[3] <= 0
            ):
                raise ValueError("return-storage member schema is malformed")
            members.append((member[0], member[1].strip(), member[2], member[3]))
        canonical = tuple(sorted(members, key=lambda item: (item[1], item[2], item[3])))
        if len(canonical) != len(set(canonical)) or tuple(members) != canonical:
            raise ValueError("return-storage members are duplicated or noncanonical")
        return (value[0], canonical)
    raise ValueError("return ABI fact slot is not sealed")


_VOID_EFFECT_SURFACE_FACT_SCHEMA = "void_effect_surface_fact_v1"


_VOID_EFFECT_SURFACE_FACT_MALFORMED = (_VOID_EFFECT_SURFACE_FACT_SCHEMA, "malformed")
# Surface kinds this authority knows how to compare.  A kind outside this set
# (new, unknown, or malformed evidence) is never compatible with anything.
_SEALED_OBSERVATION_SURFACE_KINDS = frozenset({"memory_effect", "return_value"})


def _exact_int(value: Any) -> Optional[int]:
    return value if type(value) is int else None


def _sealed_void_effect_surface_fact(analysis: Any, slot_rows: tuple) -> tuple[Any, ...]:
    """Seal the observation-surface facts that decide the ABI observation contract.

    Read from the analysis exactly once at seed construction (Issue #104,
    Gap 6) and carried inside the seed digest; the ABI assessment never
    re-reads the analysis.  The surface is taken from the canonical accessor
    ``FunctionReturnAnalysis.get_comparison_surface()`` - the same authority
    the width/solver path uses - so the ABI relation can never disagree with
    the surface the query is actually built on.  Every component must already
    have its exact type (``str`` kind out of the sealed kind set, ``int``
    widths and counts, ``tuple`` of non-empty ``str`` reasons, ``bool``
    flags): authority evidence is never coerced, a malformed value seals the
    fact as MALFORMED, which is never eligible and never compatible.
    """

    getter = getattr(analysis, "get_comparison_surface", None)
    if not callable(getter):
        return _VOID_EFFECT_SURFACE_FACT_MALFORMED + ("comparison_surface_api",)
    try:
        surface = getter()
    except Exception:
        return _VOID_EFFECT_SURFACE_FACT_MALFORMED + ("comparison_surface_error",)
    if surface is None:
        return _VOID_EFFECT_SURFACE_FACT_MALFORMED + ("comparison_surface_absent",)
    surface_kind = getattr(surface, "kind", None)
    surface_bits = getattr(surface, "explicit_bit_width", None)
    if type(surface_kind) is not str or surface_kind not in _SEALED_OBSERVATION_SURFACE_KINDS:
        return _VOID_EFFECT_SURFACE_FACT_MALFORMED + ("surface_kind",)
    if _exact_int(surface_bits) is None or type(surface_bits) is bool:
        return _VOID_EFFECT_SURFACE_FACT_MALFORMED + ("surface_bits",)
    return_type_is_void = False
    for slot, status, value, _source in slot_rows:
        if slot == "declared_or_effective_return_type" and status is ReturnAbiFactStatus.PRESENT:
            name = str(value[1]).rsplit("/", 1)[-1].strip().lower()
            return_type_is_void = name == "void" and int(value[2]) == 0
    effect_summary = getattr(analysis, "effect_summary", None)
    if effect_summary is None:
        # No effect evidence at all.  The surface kind is still authoritative
        # (a plain return-value observation); the eligibility facts below are
        # simply empty, which can never satisfy the void effect-only shape.
        return (
            _VOID_EFFECT_SURFACE_FACT_SCHEMA,
            surface_kind,
            surface_bits,
            0,
            (),
            True,
            return_type_is_void,
            False,
        )
    effects = getattr(effect_summary, "effects", None)
    reasons = getattr(effect_summary, "incomplete_reasons", None)
    unsupported = getattr(effect_summary, "has_unsupported_call", None)
    if type(effects) not in (list, tuple):
        return _VOID_EFFECT_SURFACE_FACT_MALFORMED + ("effects",)
    if type(reasons) not in (list, tuple) or any(type(item) is not str or not item for item in reasons):
        return _VOID_EFFECT_SURFACE_FACT_MALFORMED + ("incomplete_reasons",)
    if type(unsupported) is not bool:
        return _VOID_EFFECT_SURFACE_FACT_MALFORMED + ("has_unsupported_call",)
    return (
        _VOID_EFFECT_SURFACE_FACT_SCHEMA,
        surface_kind,
        surface_bits,
        len(effects),
        tuple(sorted(reasons)),
        unsupported,
        return_type_is_void,
        True,
    )


@dataclass(frozen=True, init=False)
class FunctionReturnAbiSeed:
    return_site_target_key: Any
    function_snapshot: Any
    width_seed_digest: str
    slot_facts: tuple[tuple[str, ReturnAbiFactStatus, Any, str], ...]
    prepared_snapshot_digest: str
    surface_fact: tuple[Any, ...]
    seed_digest: str

    def __init__(self, **values: Any) -> None:
        if values.pop("_factory_token", None) is not _RETURN_ABI_SEED_TOKEN:
            raise TypeError("return ABI seed must be factory issued")
        supplied = values.pop("seed_digest", None)
        for name, value in values.items():
            object.__setattr__(self, name, value)
        if tuple(name for name, *_ in self.slot_facts) != tuple(sorted(_ABI_SLOTS)):
            raise ValueError("return ABI seed slot set differs from sealed registry")
        digest = authority_digest(values)
        if supplied is not None and supplied != digest:
            raise ValueError("return ABI seed digest mismatch")
        object.__setattr__(self, "seed_digest", digest)

    @property
    def missing_slots(self) -> tuple[str, ...]:
        return tuple(name for name, status, _value, _source in self.slot_facts if status is ReturnAbiFactStatus.MISSING)

    @property
    def malformed_slots(self) -> tuple[str, ...]:
        return tuple(name for name, status, _value, _source in self.slot_facts if status is ReturnAbiFactStatus.MALFORMED)

    @property
    def complete(self) -> bool:
        return all(status is ReturnAbiFactStatus.PRESENT for _name, status, _value, _source in self.slot_facts)

    @property
    def void_effect_only_surface(self) -> bool:
        """True when the return storage slot is semantically absent.

        A ``void`` function whose observable behaviour is a complete,
        non-empty memory-effect surface (no incomplete effect reasons, no
        unsupported call) has no return value to observe: its comparison
        surface *is* the effect surface.  Exactly one ABI slot may then be
        missing, ``return_storage_descriptor``; every other slot must be
        PRESENT.  All inputs come from the sealed ``surface_fact``.
        """

        fact = self.surface_fact
        if (
            type(fact) is not tuple
            or len(fact) != 8
            or fact[0] != _VOID_EFFECT_SURFACE_FACT_SCHEMA
        ):
            return False
        _schema, kind, bits, effect_count, reasons, unsupported, is_void, has_summary = fact
        return (
            has_summary is True
            and kind == "memory_effect"
            and type(bits) is int and bits > 0
            and type(effect_count) is int and effect_count > 0
            and reasons == ()
            and unsupported is False
            and is_void is True
            and not self.malformed_slots
            and self.missing_slots == ("return_storage_descriptor",)
        )

    @property
    def observation_complete(self) -> bool:
        """ABI facts suffice for the observation contract (complete, or void effect-only)."""
        return self.complete or self.void_effect_only_surface

    @property
    def effective_surface_kind(self) -> Optional[str]:
        """Kind of the surface this function is observed on.

        ``"memory_effect"`` when the analysis compares stores (void effect-only
        or non-void stores ⊕ return), ``"return_value"`` for a plain return
        value, and ``None`` for anything else (malformed evidence or a kind
        outside the sealed set), which is never compatible.
        """

        fact = self.surface_fact
        if (
            type(fact) is not tuple
            or len(fact) != 8
            or fact[0] != _VOID_EFFECT_SURFACE_FACT_SCHEMA
        ):
            return None
        kind = fact[1]
        if type(kind) is not str or kind not in _SEALED_OBSERVATION_SURFACE_KINDS:
            return None
        return kind

    def fact(self, slot: str) -> Any:
        for name, status, value, source in self.slot_facts:
            if name == slot:
                return status, value, source
        raise KeyError(slot)

    @classmethod
    def from_analysis_and_width_seed(cls, analysis: Any, width_seed: Any):
        from scripts.function_tracer_pcode.core import FunctionReturnAnalysis
        from scripts.function_tracer_pcode.proof.return_width.surface import FunctionReturnWidthSeed

        if type(analysis) is not FunctionReturnAnalysis or type(
            width_seed
        ) is not FunctionReturnWidthSeed:
            raise TypeError("return ABI seed requires exact analysis and width seed")
        if analysis.outcome_function_identity() != width_seed.target_id.function_identity:
            raise ValueError("return ABI analysis and return site differ")
        raw = analysis.return_abi_facts
        if type(raw) is not dict:
            rows = tuple(
                (slot, ReturnAbiFactStatus.MALFORMED, None, "return_abi_facts")
                for slot in sorted(_ABI_SLOTS)
            )
        elif not raw:
            # Older and synthetic analysis producers may not have populated the
            # schema-versioned ABI envelope.  Absence is not malformed evidence:
            # publish exact MISSING slots so production V2 remains UNKNOWN while
            # non-authoritative legacy/unit paths can continue their analysis.
            rows = tuple(
                (
                    slot,
                    ReturnAbiFactStatus.MISSING,
                    None,
                    "return_abi_facts_absent",
                )
                for slot in sorted(_ABI_SLOTS)
            )
        elif raw.get("schema_version") != 1:
            rows = tuple(
                (slot, ReturnAbiFactStatus.MALFORMED, None, "return_abi_facts")
                for slot in sorted(_ABI_SLOTS)
            )
        else:
            rows = []
            for slot in sorted(_ABI_SLOTS):
                fact = raw.get(slot)
                if type(fact) is not dict or set(fact) != {"status", "value", "source"}:
                    rows.append((slot, ReturnAbiFactStatus.MALFORMED, None, "return_abi_facts"))
                    continue
                try:
                    status = ReturnAbiFactStatus(fact["status"])
                except (TypeError, ValueError):
                    status = ReturnAbiFactStatus.MALFORMED
                source = fact.get("source")
                value = fact.get("value")
                if type(source) is not str or not source or (
                    status is not ReturnAbiFactStatus.PRESENT and value is not None
                ):
                    status = ReturnAbiFactStatus.MALFORMED
                    value = None
                    source = "return_abi_facts"
                elif status is ReturnAbiFactStatus.PRESENT:
                    try:
                        value = _sealed_return_abi_present_value(slot, value)
                    except (TypeError, ValueError):
                        status = ReturnAbiFactStatus.MALFORMED
                        value = None
                        source = "return_abi_facts"
                authority_digest(value)
                rows.append((slot, status, value, source))
            rows = tuple(rows)
        target = (
            "return_site_slot_v2", width_seed.target_id.stable_key(),
            width_seed.normalization_policy_digest,
        )
        surface_fact = _sealed_void_effect_surface_fact(analysis, rows)
        authority_digest(surface_fact)
        prepared = authority_digest({
            "analysis_function": analysis.outcome_function_identity(),
            "width_seed": width_seed.stable_key(),
            "slot_facts": rows,
            "surface_fact": surface_fact,
        })
        return cls(
            return_site_target_key=target,
            function_snapshot=analysis.outcome_function_identity(),
            width_seed_digest=width_seed.digest,
            slot_facts=rows,
            prepared_snapshot_digest=prepared,
            surface_fact=surface_fact,
            _factory_token=_RETURN_ABI_SEED_TOKEN,
        )


@dataclass(frozen=True)
class ReturnAbiCompatibilityAssessment:
    status: ReturnAbiRelationStatus
    projection_seed_digest: str
    left_abi_seed_digest: str
    right_abi_seed_digest: str
    predicate_body: tuple[Any, ...]
    assessment_digest: str

    @classmethod
    def assess(cls, projection_seed: Any, left: FunctionReturnAbiSeed, right: FunctionReturnAbiSeed):
        if type(projection_seed) is not ReturnObservationProjectionSeed or type(
            left
        ) is not FunctionReturnAbiSeed or type(right) is not FunctionReturnAbiSeed:
            raise TypeError("ABI compatibility requires exact projection and ABI seeds")
        if (
            left.malformed_slots or right.malformed_slots
            or not left.observation_complete or not right.observation_complete
        ):
            status = ReturnAbiRelationStatus.INVALID
            body = ("abi_relation_invalid_v2", left.malformed_slots, right.malformed_slots,
                    left.missing_slots, right.missing_slots)
        else:
            left_cc = left.fact("calling_convention")[1]
            right_cc = right.fact("calling_convention")[1]
            # Binary equivalence intentionally spans architectures and ABIs.
            # Physical calling-convention names and return registers therefore
            # must not be compared for literal equality.  Each unary seed has
            # already validated its own ABI facts; the relational question is
            # whether both physical surfaces project to the same semantic
            # payload observed by the comparison query.
            calling_conventions_individually_valid = bool(left_cc) and bool(right_cc)
            storage_projection_related = (
                projection_seed.candidate_observation_width
                == projection_seed.left_payload_width
                == projection_seed.right_payload_width
                and projection_seed.candidate_observation_width
                <= projection_seed.left_storage_width
                and projection_seed.candidate_observation_width
                <= projection_seed.right_storage_width
            )
            observation_applicable = (
                projection_seed.candidate_observation_width
                <= projection_seed.left_storage_width
                and projection_seed.candidate_observation_width
                <= projection_seed.right_storage_width
            )
            # A memory-effect surface (stores, or stores ⊕ return) and a
            # return-value surface are different observations even when they
            # render to the same bit vector: a function that writes a global is
            # never compared as a value against one that returns that value.
            # Both sides must observe the same effective surface kind; a
            # malformed / unavailable kind is never compatible (Issue #104).
            left_kind = left.effective_surface_kind
            right_kind = right.effective_surface_kind
            observation_surface_kinds_compatible = (
                left_kind is not None and right_kind is not None and left_kind == right_kind
            )
            body = (
                "return_abi_semantic_projection_predicates_v5",
                (
                    "calling_conventions_individually_valid",
                    calling_conventions_individually_valid,
                ),
                ("storage_projection_related", storage_projection_related),
                ("observation_contract_applicable", observation_applicable),
                (
                    "observation_surface_kinds_compatible",
                    observation_surface_kinds_compatible,
                ),
            )
            status = (
                ReturnAbiRelationStatus.PROVED
                if all((
                    calling_conventions_individually_valid,
                    storage_projection_related,
                    observation_applicable,
                    observation_surface_kinds_compatible,
                ))
                else ReturnAbiRelationStatus.UNPROVEN
            )
        payload = {
            "status": status.value,
            "projection_seed_digest": projection_seed.seed_digest,
            "left_abi_seed_digest": left.seed_digest,
            "right_abi_seed_digest": right.seed_digest,
            "predicate_body": body,
        }
        return cls(status, projection_seed.seed_digest, left.seed_digest,
                   right.seed_digest, body, authority_digest(payload))


_PROJECTION_SEED_TOKEN = object()
_OBSERVATION_NEED_SEED_TOKEN = object()


@dataclass(frozen=True, init=False)
class ReturnObservationNeedSeed:
    """Exact pair authority when complete unary surfaces lack a common width."""

    pair_target_key: Any
    left_seed_digest: str
    right_seed_digest: str
    left_target_key: Any
    right_target_key: Any
    left_widths: tuple[int, int]
    right_widths: tuple[int, int]
    guard_contract: Any
    source_snapshot_pair: Any
    prepared_snapshot_digest: str
    seed_digest: str

    def __init__(self, **values: Any) -> None:
        if values.pop("_factory_token", None) is not _OBSERVATION_NEED_SEED_TOKEN:
            raise TypeError("observation-need seed must be factory issued")
        supplied = values.pop("seed_digest", None)
        for name, value in values.items():
            object.__setattr__(self, name, value)
        digest = authority_digest(values)
        if supplied is not None and supplied != digest:
            raise ValueError("observation-need seed digest mismatch")
        object.__setattr__(self, "seed_digest", digest)

    @classmethod
    def from_pair_seed(cls, left_seed: Any, right_seed: Any, pair_seed: Any):
        from scripts.function_tracer_pcode.proof.return_width.surface import (
            FunctionReturnWidthSeed,
            PairReturnObservationSeed,
        )

        if type(left_seed) is not FunctionReturnWidthSeed or type(right_seed) is not FunctionReturnWidthSeed:
            raise TypeError("observation-need seed requires exact unary seeds")
        if type(pair_seed) is not PairReturnObservationSeed:
            raise TypeError("observation-need seed requires exact pair seed")
        if not left_seed.complete or not right_seed.complete:
            raise ValueError("observation-need seed requires complete unary width surfaces")
        if pair_seed.left_seed_digest != left_seed.digest or pair_seed.right_seed_digest != right_seed.digest:
            raise ValueError("observation-need pair/unary authority differs")
        prepared = authority_digest({
            "left_width_seed": left_seed.stable_key(),
            "right_width_seed": right_seed.stable_key(),
            "pair_width_seed": pair_seed.stable_key(),
        })
        return cls(
            pair_target_key=pair_seed.target_id.stable_key(),
            left_seed_digest=left_seed.digest,
            right_seed_digest=right_seed.digest,
            left_target_key=left_seed.target_id.stable_key(),
            right_target_key=right_seed.target_id.stable_key(),
            left_widths=(int(left_seed.storage_width), int(left_seed.payload_width)),
            right_widths=(int(right_seed.storage_width), int(right_seed.payload_width)),
            guard_contract=("ordered_guard_contract_v2", left_seed.guard_region_fact.stable_key(), right_seed.guard_region_fact.stable_key()),
            source_snapshot_pair=("ordered_function_pair_v2", left_seed.target_id.function_identity, right_seed.target_id.function_identity),
            prepared_snapshot_digest=prepared,
            _factory_token=_OBSERVATION_NEED_SEED_TOKEN,
        )


class ProjectionNotFormable(ValueError):
    """Complete, matching width authority has no common observation width."""


@dataclass(frozen=True, init=False)
class ReturnObservationProjectionSeed:
    pair_target_key: Any
    left_seed_digest: str
    right_seed_digest: str
    left_return_site_target_digest: str
    right_return_site_target_digest: str
    candidate_observation_width: int
    derivation: str
    left_storage_width: int
    right_storage_width: int
    left_payload_width: int
    right_payload_width: int
    left_extension_kind: str
    right_extension_kind: str
    guard_contract: Any
    source_snapshot_pair: Any
    prepared_snapshot_digest: str
    seed_digest: str

    def __init__(self, **values: Any) -> None:
        token = values.pop("_factory_token", None)
        if token is not _PROJECTION_SEED_TOKEN:
            raise TypeError("return observation projection seed must be factory issued")
        payload = dict(values)
        supplied = payload.pop("seed_digest", None)
        for name, value in payload.items():
            object.__setattr__(self, name, value)
        digest = authority_digest(payload)
        if supplied is not None and supplied != digest:
            raise ValueError("return observation projection seed digest mismatch")
        object.__setattr__(self, "seed_digest", digest)
        self.validate()

    @classmethod
    def from_pair_seed(
        cls,
        left_seed: Any,
        right_seed: Any,
        pair_seed: Any,
    ) -> "ReturnObservationProjectionSeed":
        from scripts.function_tracer_pcode.proof.return_width.surface import (
            FunctionReturnWidthSeed,
            PairReturnObservationSeed,
        )

        if type(left_seed) is not FunctionReturnWidthSeed or type(
            right_seed
        ) is not FunctionReturnWidthSeed:
            raise TypeError("projection seed requires exact unary width seeds")
        if type(pair_seed) is not PairReturnObservationSeed:
            raise TypeError("projection seed requires an exact pair seed")
        if (
            pair_seed.left_seed_digest != left_seed.digest
            or pair_seed.right_seed_digest != right_seed.digest
            or pair_seed.target_id.left_target_id != left_seed.target_id
            or pair_seed.target_id.right_target_id != right_seed.target_id
        ):
            raise ValueError("projection seed pair/unary authority differs")
        if not left_seed.complete or not right_seed.complete:
            raise ValueError("projection seed requires complete unary width facts")
        left_payload = int(left_seed.payload_width or 0)
        right_payload = int(right_seed.payload_width or 0)
        if left_payload <= 0 or left_payload != right_payload:
            raise ProjectionNotFormable(
                "projection seed lacks one candidate observation width"
            )
        source_pair = (
            "ordered_function_pair_v2",
            left_seed.target_id.function_identity,
            right_seed.target_id.function_identity,
        )
        guard_contract = (
            "ordered_guard_contract_v2",
            left_seed.guard_region_fact.stable_key(),
            right_seed.guard_region_fact.stable_key(),
        )
        return cls(
            pair_target_key=pair_seed.target_id.stable_key(),
            left_seed_digest=left_seed.digest,
            right_seed_digest=right_seed.digest,
            left_return_site_target_digest=authority_digest((
                "return_site_slot_v2", left_seed.target_id.stable_key(),
                left_seed.normalization_policy_digest,
            )),
            right_return_site_target_digest=authority_digest((
                "return_site_slot_v2", right_seed.target_id.stable_key(),
                right_seed.normalization_policy_digest,
            )),
            candidate_observation_width=left_payload,
            derivation="common_validated_semantic_payload_width",
            left_storage_width=int(left_seed.storage_width or 0),
            right_storage_width=int(right_seed.storage_width or 0),
            left_payload_width=left_payload,
            right_payload_width=right_payload,
            left_extension_kind=left_seed.extension_evidence_source.kind,
            right_extension_kind=right_seed.extension_evidence_source.kind,
            guard_contract=guard_contract,
            source_snapshot_pair=source_pair,
            prepared_snapshot_digest=authority_digest({
                "left_width_seed": left_seed.stable_key(),
                "right_width_seed": right_seed.stable_key(),
                "pair_width_seed": pair_seed.stable_key(),
            }),
            _factory_token=_PROJECTION_SEED_TOKEN,
        )

    def validate(self) -> None:
        for value in (
            self.left_seed_digest, self.right_seed_digest,
            self.left_return_site_target_digest, self.right_return_site_target_digest,
            self.derivation,
            self.left_extension_kind, self.right_extension_kind,
            self.prepared_snapshot_digest, self.seed_digest,
        ):
            if type(value) is not str or not value:
                raise TypeError("projection seed string authority is incomplete")
        for value in (
            self.candidate_observation_width, self.left_storage_width,
            self.right_storage_width, self.left_payload_width,
            self.right_payload_width,
        ):
            if type(value) is not int or value <= 0:
                raise TypeError("projection seed widths must be positive exact integers")
        authority_digest(self.pair_target_key)
        authority_digest(self.guard_contract)
        authority_digest(self.source_snapshot_pair)


_READONLY_SEED_TOKEN = object()
PINNED_SHARED_PARAMETER_MEMORY_CONTRACT_ID = (
    "binary-equivalence-shared-parameter-memory-v1"
)


@dataclass(frozen=True, init=False)
class ReadonlyReductionObjectSetSeed:
    """Ordered, object-derived readonly member authority; never a proof."""

    ordered_pair_target_key: Any
    left_function_snapshot: Any
    right_function_snapshot: Any
    left_case_key: Any
    right_case_key: Any
    left_reduction_key: Any
    right_reduction_key: Any
    left_member_keys: tuple[Any, ...]
    right_member_keys: tuple[Any, ...]
    left_unresolved_member_indices: tuple[int, ...]
    right_unresolved_member_indices: tuple[int, ...]
    left_object_set_complete: bool
    right_object_set_complete: bool
    guard_contract: Any
    observation_contract: Any
    shared_input_memory_contract: Any
    prepared_snapshot_digest: str
    seed_digest: str

    def __init__(self, **values: Any) -> None:
        if values.pop("_factory_token", None) is not _READONLY_SEED_TOKEN:
            raise TypeError("readonly object-set seed must be factory issued")
        supplied = values.pop("seed_digest", None)
        for name, value in values.items():
            object.__setattr__(self, name, value)
        digest = authority_digest(values)
        if supplied is not None and supplied != digest:
            raise ValueError("readonly object-set seed digest mismatch")
        object.__setattr__(self, "seed_digest", digest)
        if not self.left_member_keys or not self.right_member_keys:
            raise ValueError("readonly object-set seed requires both ordered member sets")
        if len(set(map(authority_digest, self.left_member_keys))) != len(self.left_member_keys):
            raise ValueError("left readonly object set contains duplicate member identity")
        if len(set(map(authority_digest, self.right_member_keys))) != len(self.right_member_keys):
            raise ValueError("right readonly object set contains duplicate member identity")
        for indices, members in (
            (self.left_unresolved_member_indices, self.left_member_keys),
            (self.right_unresolved_member_indices, self.right_member_keys),
        ):
            if (
                type(indices) is not tuple
                or tuple(sorted(indices)) != indices
                or len(indices) != len(set(indices))
                or any(type(index) is not int or index < 0 or index >= len(members)
                       for index in indices)
            ):
                raise ValueError("readonly unresolved-member set is invalid")

    @staticmethod
    def _case_key(case: Any) -> Any:
        conditions = tuple(condition._safe_structural_key() for condition in case.conditions)
        if any(item is None for item in conditions):
            raise ValueError("readonly case contains an unstable guard identity")
        return (
            "readonly_return_case_v2",
            int(case.index),
            tuple(int(item) for item in case.source_indices),
            authority_digest(conditions),
        )

    @staticmethod
    def _member_keys(readonly_ref: Any) -> tuple[Any, ...]:
        members = []
        for witness_index, witness in enumerate(readonly_ref.semantic_witnesses):
            for member_index, term in enumerate(witness.terms):
                members.append((
                    "readonly_reduction_member_v2",
                    readonly_ref.pointer_base_ref.stable_key(),
                    readonly_ref.reduction_kind,
                    witness_index,
                    witness.exact_count,
                    member_index,
                    term.stable_key(),
                    readonly_ref.result_size,
                ))
        if not members:
            members.append((
                "readonly_reduction_member_v2",
                readonly_ref.pointer_base_ref.stable_key(),
                readonly_ref.reduction_kind,
                "symbolic_sequence",
                readonly_ref.start_offset,
                readonly_ref.stride,
                readonly_ref.element_size,
                readonly_ref.result_size,
            ))
        return tuple(members)

    @staticmethod
    def _unresolved_member_indices(readonly_ref: Any, member_count: int) -> tuple[int, ...]:
        semantic_key = getattr(readonly_ref, "pairwise_semantic_key", None)
        if not callable(semantic_key):
            return tuple(range(member_count))
        try:
            value = semantic_key()
        except (AttributeError, TypeError, ValueError):
            return tuple(range(member_count))
        return () if value is not None else tuple(range(member_count))

    @classmethod
    def from_analyses_and_cases(
        cls, left_analysis: Any, right_analysis: Any, left_case: Any, right_case: Any
    ) -> "ReadonlyReductionObjectSetSeed":
        from scripts.function_tracer_pcode.core import FunctionReturnAnalysis, ReadonlyReductionRef
        from scripts.function_tracer_pcode.proof.strategies.pairwise_models import ReturnCase

        if type(left_analysis) is not FunctionReturnAnalysis or type(
            right_analysis
        ) is not FunctionReturnAnalysis:
            raise TypeError("readonly seed requires exact function analyses")
        if type(left_case) is not ReturnCase or type(right_case) is not ReturnCase:
            raise TypeError("readonly seed requires exact return cases")
        left_ref = getattr(left_case.value_expr, "runtime_ref", None)
        right_ref = getattr(right_case.value_expr, "runtime_ref", None)
        if type(left_ref) is not ReadonlyReductionRef or type(
            right_ref
        ) is not ReadonlyReductionRef:
            raise TypeError("readonly seed requires exact readonly reduction refs")
        left_snapshot = left_analysis.outcome_function_identity()
        right_snapshot = right_analysis.outcome_function_identity()
        left_case_key = cls._case_key(left_case)
        right_case_key = cls._case_key(right_case)
        left_guards = tuple(item._safe_structural_key() for item in left_case.conditions)
        right_guards = tuple(item._safe_structural_key() for item in right_case.conditions)
        if any(item is None for item in left_guards + right_guards):
            raise ValueError("readonly seed contains an unstable guard identity")
        guard = (
            "ordered_readonly_guard_v2",
            left_guards,
            right_guards,
        )
        observation = (
            "readonly_reduction_observation_v2",
            left_ref.reduction_kind,
            right_ref.reduction_kind,
            left_ref.result_size,
            right_ref.result_size,
            left_case.program_is_big_endian,
            right_case.program_is_big_endian,
        )
        left_pointer = left_ref.pointer_base_ref.stable_key()
        right_pointer = right_ref.pointer_base_ref.stable_key()
        shared_input_memory_contract = None
        if (
            type(left_pointer) is tuple
            and type(right_pointer) is tuple
            and len(left_pointer) == 2
            and len(right_pointer) == 2
            and left_pointer[0] == right_pointer[0] == "parameter"
            and type(left_pointer[1]) is int
            and left_pointer[1] == right_pointer[1]
        ):
            shared_input_memory_contract = (
                PINNED_SHARED_PARAMETER_MEMORY_CONTRACT_ID,
                ("ordered_function_pair_v2", left_snapshot, right_snapshot),
                ("corresponding_parameter_index", left_pointer[1]),
                ("shared_initial_byte_memory", "all_reachable_read_offsets"),
            )
        left_members = cls._member_keys(left_ref)
        right_members = cls._member_keys(right_ref)
        left_unresolved = cls._unresolved_member_indices(left_ref, len(left_members))
        right_unresolved = cls._unresolved_member_indices(right_ref, len(right_members))
        body = dict(
            ordered_pair_target_key=("ordered_function_pair_v2", left_snapshot, right_snapshot),
            left_function_snapshot=left_snapshot,
            right_function_snapshot=right_snapshot,
            left_case_key=left_case_key,
            right_case_key=right_case_key,
            left_reduction_key=left_ref.stable_key(),
            right_reduction_key=right_ref.stable_key(),
            left_member_keys=left_members,
            right_member_keys=right_members,
            left_unresolved_member_indices=left_unresolved,
            right_unresolved_member_indices=right_unresolved,
            left_object_set_complete=bool(left_ref.semantic_witnesses),
            right_object_set_complete=bool(right_ref.semantic_witnesses),
            guard_contract=guard,
            observation_contract=observation,
            shared_input_memory_contract=shared_input_memory_contract,
            prepared_snapshot_digest=authority_digest((
                left_snapshot, right_snapshot, left_case_key, right_case_key,
                left_ref.stable_key(), right_ref.stable_key(), guard, observation,
                shared_input_memory_contract,
                left_unresolved, right_unresolved,
                bool(left_ref.semantic_witnesses), bool(right_ref.semantic_witnesses),
            )),
        )
        return cls(**body, _factory_token=_READONLY_SEED_TOKEN)


_RESOLVED_READONLY_SEED_TOKEN = object()


@dataclass(frozen=True, init=False)
class ResolvedReadonlyObjectSetSeed:
    base_seed_digest: str
    ordered_pair_target_key: Any
    left_reduction_key: Any
    right_reduction_key: Any
    left_member_keys: tuple[Any, ...]
    right_member_keys: tuple[Any, ...]
    left_object_set_complete: bool
    right_object_set_complete: bool
    guard_contract: Any
    observation_contract: Any
    shared_input_memory_contract: Any
    dependency_artifact_digests: tuple[str, ...]
    dependency_completion_receipt_digests: tuple[str, ...]
    prepared_snapshot_digest: str
    seed_digest: str

    def __init__(self, **values: Any) -> None:
        if values.pop("_factory_token", None) is not _RESOLVED_READONLY_SEED_TOKEN:
            raise TypeError("resolved readonly object-set seed must be factory issued")
        supplied = values.pop("seed_digest", None)
        for name, value in values.items():
            object.__setattr__(self, name, value)
        digest = authority_digest(values)
        if supplied is not None and supplied != digest:
            raise ValueError("resolved readonly object-set seed digest mismatch")
        object.__setattr__(self, "seed_digest", digest)

    @classmethod
    def from_live_completion_closure(
        cls,
        session: Any,
        base_seed: ReadonlyReductionObjectSetSeed,
        dependencies: Iterable[tuple[Any, Any, Any]],
    ) -> "ResolvedReadonlyObjectSetSeed":
        if type(base_seed) is not ReadonlyReductionObjectSetSeed:
            raise TypeError("readonly resolution requires exact base seed")
        if not base_seed.left_object_set_complete or not base_seed.right_object_set_complete:
            raise ValueError("readonly resolution requires complete ordered object sets")
        rows = tuple(dependencies)
        expected = {
            ("left", index) for index in base_seed.left_unresolved_member_indices
        } | {
            ("right", index) for index in base_seed.right_unresolved_member_indices
        }
        if len(rows) != len(expected):
            raise ValueError("readonly resolution dependency cardinality differs")
        resolved: dict[tuple[str, int], ReadonlyStorageIdentityArtifact] = {}
        receipt_digests = []
        for blocker, artifact, receipt in rows:
            if (
                type(blocker) is not AbiWidthReadonlyBlockerSignal
                or type(artifact) is not ReadonlyStorageIdentityArtifact
                or type(receipt) is not RequirementCompletionReceipt
                or artifact.reason_id != "readonly_storage_identity_unproven"
                or receipt.proof_artifact_digest != artifact.artifact_digest
                or artifact.source_seed_digest != base_seed.seed_digest
                or artifact.source_snapshot_digest
                != session.identity.source_snapshot_fingerprint
            ):
                raise ValueError("readonly resolution dependency authority differs")
            applicability = artifact.applicability_body
            if len(applicability) != 4 or applicability[0] != "member_guard":
                raise ValueError("readonly resolution artifact lacks member selector")
            selector = (applicability[2], applicability[3])
            if selector not in expected or selector in resolved:
                raise ValueError("readonly resolution dependency is extra or duplicated")
            authority = session.domain_signal_encoder.authority_for_signal(
                session, blocker
            )
            requirement = authority.bound_contract.slot_bindings[0][1]
            if (
                receipt.occurrence_id != authority.occurrence.occurrence_id
                or receipt.cause_id != authority.occurrence.cause_id.value
                or receipt.proof_requirement_id != requirement.requirement_id
            ):
                raise ValueError("readonly resolution receipt differs from unary Q")
            completed = tuple(
                event.authority_payload.completion_receipt
                for event in session.recorder.prefix_view().events
                if event.header.event_type is EventType.REQUIREMENT_COMPLETED
                and event.authority_payload.completion_receipt == receipt
            )
            if len(completed) != 1:
                raise ValueError("readonly resolution dependency is not live-session completed")
            resolved[selector] = artifact
            receipt_digests.append(authority_digest(receipt))
        if set(resolved) != expected:
            raise ValueError("readonly resolution dependency closure is incomplete")

        def members(side: str, source: tuple[Any, ...]) -> tuple[Any, ...]:
            return tuple(
                (
                    "validated_readonly_storage_identity_v2",
                    member,
                    resolved[(side, index)].semantic_target_digest,
                    resolved[(side, index)].artifact_digest,
                    resolved[(side, index)].proof_body,
                    resolved[(side, index)].applicability_body,
                )
                if (side, index) in resolved else member
                for index, member in enumerate(source)
            )

        left = members("left", base_seed.left_member_keys)
        right = members("right", base_seed.right_member_keys)
        body = {
            "base_seed_digest": base_seed.seed_digest,
            "ordered_pair_target_key": base_seed.ordered_pair_target_key,
            "left_reduction_key": base_seed.left_reduction_key,
            "right_reduction_key": base_seed.right_reduction_key,
            "left_member_keys": left,
            "right_member_keys": right,
            "left_object_set_complete": base_seed.left_object_set_complete,
            "right_object_set_complete": base_seed.right_object_set_complete,
            "guard_contract": base_seed.guard_contract,
            "observation_contract": base_seed.observation_contract,
            "shared_input_memory_contract": base_seed.shared_input_memory_contract,
            "dependency_artifact_digests": tuple(sorted(
                artifact.artifact_digest for artifact in resolved.values()
            )),
            "dependency_completion_receipt_digests": tuple(sorted(receipt_digests)),
            "prepared_snapshot_digest": authority_digest((
                base_seed.prepared_snapshot_digest, left, right,
                tuple(sorted(receipt_digests)),
            )),
        }
        return cls(**body, _factory_token=_RESOLVED_READONLY_SEED_TOKEN)


_READONLY_CORRESPONDENCE_FACT_TOKEN = object()


@dataclass(frozen=True, init=False)
class ReadonlyCorrespondenceFactSet:
    """Independent structural premises plus the factory-owned value goal."""

    resolved_seed_digest: str
    mapping: tuple[tuple[str, str], ...]
    left_value_symbols: tuple[str, ...]
    right_value_symbols: tuple[str, ...]
    value_width_bits: int
    premise_fact_rows: tuple[Any, ...]
    shared_value_authority_rows: tuple[Any, ...]
    goal_fact_row: Any
    fact_digest: str

    def __init__(self, **values: Any) -> None:
        if values.pop("_factory_token", None) is not _READONLY_CORRESPONDENCE_FACT_TOKEN:
            raise TypeError("readonly correspondence facts must be factory issued")
        supplied = values.pop("fact_digest", None)
        for name, value in values.items():
            object.__setattr__(self, name, value)
        payload = {
            name: getattr(self, name)
            for name in self.__dataclass_fields__ if name != "fact_digest"
        }
        digest = authority_digest(payload)
        if supplied is not None and supplied != digest:
            raise ValueError("readonly correspondence fact digest mismatch")
        object.__setattr__(self, "fact_digest", digest)

    @staticmethod
    def _raw_member_parts(member: Any) -> tuple[Any, ...]:
        if (
            type(member) is tuple
            and len(member) == 6
            and member[0] == "validated_readonly_storage_identity_v2"
        ):
            original = member[1]
            proof_body = member[4]
            applicability = member[5]
            if (
                type(member[2]) is not str
                or type(member[3]) is not str
                or type(proof_body) is not tuple
                or len(proof_body) != 7
                or proof_body[0] != "readonly_storage_identity_v2"
                or proof_body[4] is not True
                or type(applicability) is not tuple
                or len(applicability) != 4
                or applicability[0] != "member_guard"
            ):
                raise ProjectionNotFormable(
                    "resolved readonly member lacks typed storage authority"
                )
            member = original
        if (
            type(member) is not tuple
            or len(member) != 8
            or member[0] != "readonly_reduction_member_v2"
            or type(member[3]) is not int
            or type(member[4]) is not int
            or type(member[5]) is not int
            or type(member[7]) is not int
            or member[4] <= 0
            or member[7] <= 0
        ):
            raise ProjectionNotFormable(
                "readonly correspondence lacks raw typed member value authority"
            )
        return member

    @staticmethod
    def _resolved_storage_descriptor(member: Any) -> Any:
        if (
            type(member) is tuple
            and len(member) == 6
            and member[0] == "validated_readonly_storage_identity_v2"
        ):
            proof_body = member[4]
            return (
                "validated_storage_descriptor_v2",
                proof_body[1], proof_body[2], proof_body[3],
                member[2], member[3], proof_body[5], proof_body[6],
            )
        return None

    @classmethod
    def from_resolved_seed(
        cls, seed: ResolvedReadonlyObjectSetSeed
    ) -> "ReadonlyCorrespondenceFactSet":
        if type(seed) is not ResolvedReadonlyObjectSetSeed:
            raise TypeError("readonly correspondence facts require exact resolved seed")
        if (
            not seed.left_object_set_complete
            or not seed.right_object_set_complete
            or len(seed.left_member_keys) != len(seed.right_member_keys)
        ):
            raise ProjectionNotFormable(
                "readonly correspondence lacks complete equal-cardinality object sets"
            )
        left = tuple(map(cls._raw_member_parts, seed.left_member_keys))
        right = tuple(map(cls._raw_member_parts, seed.right_member_keys))
        left_descriptors = tuple(map(
            cls._resolved_storage_descriptor, seed.left_member_keys
        ))
        right_descriptors = tuple(map(
            cls._resolved_storage_descriptor, seed.right_member_keys
        ))
        observation = seed.observation_contract
        if (
            type(observation) is not tuple
            or len(observation) != 7
            or observation[0] != "readonly_reduction_observation_v2"
            or observation[1] != observation[2]
            or observation[3] != observation[4]
            or observation[5] != observation[6]
            or type(observation[3]) is not int
            or observation[3] <= 0
        ):
            raise ProjectionNotFormable(
                "readonly correspondence observation operator/width/endian differs"
            )
        guard = seed.guard_contract
        if (
            type(guard) is not tuple
            or len(guard) != 3
            or guard[0] != "ordered_readonly_guard_v2"
            or guard[1] != guard[2]
        ):
            raise ProjectionNotFormable(
                "readonly correspondence lacks an exact guard relation"
            )
        left_reduction = seed.left_reduction_key
        right_reduction = seed.right_reduction_key
        if (
            type(left_reduction) is not tuple
            or type(right_reduction) is not tuple
            or len(left_reduction) != len(right_reduction)
            or left_reduction[0] != "readonly_reduction"
            or right_reduction[0] != "readonly_reduction"
            or left_reduction[1] != right_reduction[1]
            or left_reduction[4:12] != right_reduction[4:12]
            or left_reduction[14:] != right_reduction[14:]
        ):
            raise ProjectionNotFormable(
                "readonly correspondence reduction/count/iteration facts differ"
            )

        def role(member: tuple[Any, ...]) -> Any:
            return (member[2], member[3], member[4], member[5], member[6], member[7])

        if tuple(map(role, left)) != tuple(map(role, right)):
            raise ProjectionNotFormable(
                "readonly correspondence role/order/load-shape facts differ"
            )
        for members in (left, right):
            witness_counts: dict[int, tuple[int, int]] = {}
            for member in members:
                witness_index = member[3]
                exact_count = member[4]
                seen, prior_count = witness_counts.get(
                    witness_index, (0, exact_count)
                )
                if prior_count != exact_count:
                    raise ProjectionNotFormable(
                        "readonly witness cardinality authority is inconsistent"
                    )
                witness_counts[witness_index] = (seen + 1, exact_count)
            if any(
                seen != exact_count
                for seen, exact_count in witness_counts.values()
            ):
                raise ProjectionNotFormable(
                    "readonly finite witness set is incomplete"
                )

        expected_endian = "big" if observation[5] is True else "little"
        for members, descriptors in (
            (left, left_descriptors), (right, right_descriptors)
        ):
            for member, descriptor in zip(members, descriptors):
                if descriptor is None:
                    continue
                term = member[6]
                if (
                    descriptor[2] != term[2]
                    or descriptor[3] != expected_endian
                    or type(descriptor[1]) is not str
                    or not descriptor[1]
                ):
                    raise ProjectionNotFormable(
                        "resolved storage descriptor differs from load semantics"
                    )

        symbols_by_value_key: dict[str, str] = {}
        shared_authority_rows: dict[str, Any] = {}
        shared_contract = seed.shared_input_memory_contract

        def value_key(
            member: tuple[Any, ...], descriptor: Any, side: str
        ) -> tuple[Any, bool]:
            pointer = member[1]
            if type(pointer) is tuple and pointer and pointer[0] == "parameter":
                if len(pointer) != 2 or type(pointer[1]) is not int:
                    raise ProjectionNotFormable(
                        "parameter readonly value lacks program-independent identity"
                    )
                if (
                    type(shared_contract) is not tuple
                    or len(shared_contract) != 4
                    or shared_contract[0]
                    != PINNED_SHARED_PARAMETER_MEMORY_CONTRACT_ID
                    or shared_contract[1] != seed.ordered_pair_target_key
                    or shared_contract[2]
                    != ("corresponding_parameter_index", pointer[1])
                    or shared_contract[3]
                    != (
                        "shared_initial_byte_memory",
                        "all_reachable_read_offsets",
                    )
                ):
                    raise ProjectionNotFormable(
                        "parameter readonly value lacks pinned shared-input authority"
                    )
                return (
                    (
                        "shared_parameter_memory_value_v2",
                        authority_digest(shared_contract), pointer[1], member[6],
                        observation[5], member[7], descriptor,
                    ),
                    True,
                )
            return (
                (
                    "side_local_readonly_value_v2", side, pointer, member[6],
                    observation[5], member[7], descriptor,
                ),
                False,
            )

        def symbols(
            members: tuple[tuple[Any, ...], ...], descriptors: tuple[Any, ...],
            side: str,
        ) -> tuple[str, ...]:
            values = []
            for member, descriptor in zip(members, descriptors):
                key_body, is_shared = value_key(member, descriptor, side)
                value_key_digest = authority_digest(key_body)
                symbol = symbols_by_value_key.setdefault(
                    value_key_digest,
                    f"readonly_value_{len(symbols_by_value_key)}",
                )
                if is_shared:
                    shared_authority_rows.setdefault(
                        value_key_digest,
                        (
                            "shared_parameter_value_authority_v2",
                            symbol, key_body, shared_contract,
                        ),
                    )
                values.append(symbol)
            return tuple(values)

        left_value_descriptors = list(left_descriptors)
        right_value_descriptors = list(right_descriptors)
        for index, (
            left_member, right_member, left_descriptor, right_descriptor
        ) in enumerate(zip(
            left, right, left_descriptors, right_descriptors
        )):
            if left_member[1][0] == right_member[1][0] == "parameter":
                if (left_descriptor is None) != (right_descriptor is None) or (
                    left_descriptor is not None
                    and left_descriptor[1:4] != right_descriptor[1:4]
                ):
                    raise ProjectionNotFormable(
                        "shared parameter loads have different storage descriptors"
                    )
                if left_descriptor is not None:
                    paired = (
                        "paired_parameter_storage_descriptor_v2",
                        left_descriptor, right_descriptor,
                    )
                    left_value_descriptors[index] = paired
                    right_value_descriptors[index] = paired
        left_symbols = symbols(
            left, tuple(left_value_descriptors), "left"
        )
        right_symbols = symbols(
            right, tuple(right_value_descriptors), "right"
        )
        mapping = tuple(zip(
            map(authority_digest, seed.left_member_keys),
            map(authority_digest, seed.right_member_keys),
        ))
        premise_rows = (
            ("operator_preserved_fact_v2", observation[1]),
            ("roles_order_multiplicity_fact_v2", tuple(map(role, left))),
            ("count_identity_fact_v2", left_reduction[4:6]),
            ("guard_iteration_fact_v2", guard),
            ("load_shape_fact_v2", tuple(member[6:] for member in left)),
            ("finite_witness_complete_fact_v2", tuple(
                (member[3], member[4]) for member in left
            )),
            ("resolved_storage_identity_authority_v2", tuple(
                member for member in (
                    *seed.left_member_keys, *seed.right_member_keys
                )
                if type(member) is tuple
                and member
                and member[0] == "validated_readonly_storage_identity_v2"
            )),
            ("resolved_storage_descriptor_rows_v2", (
                left_descriptors, right_descriptors
            )),
        )
        goal = (
            "value_observation_correspondence_goal_v2",
            left_symbols, right_symbols, mapping,
        )
        return cls(
            resolved_seed_digest=seed.seed_digest,
            mapping=mapping,
            left_value_symbols=left_symbols,
            right_value_symbols=right_symbols,
            value_width_bits=8 * observation[3],
            premise_fact_rows=premise_rows,
            shared_value_authority_rows=tuple(
                shared_authority_rows[key]
                for key in sorted(shared_authority_rows)
            ),
            goal_fact_row=goal,
            _factory_token=_READONLY_CORRESPONDENCE_FACT_TOKEN,
        )


_BLOCKER_SIGNAL_TOKEN = object()


@dataclass(frozen=True, init=False)
class AbiWidthReadonlyBlockerSignal:
    reason_id: str
    identity_scope: IdentityScope
    target_kind: str
    canonical_target_key: Any
    missing_semantic_fact: Any
    semantic_proposition: Any
    observation_surface: Any
    active_semantic_precondition: Any
    correspondence_contract: Any
    evidence_refs: tuple[str, ...]
    producer_id: str

    def __init__(self, **values: Any) -> None:
        token = values.pop("_factory_token", None)
        if token is not _BLOCKER_SIGNAL_TOKEN:
            raise TypeError("Phase 6.5 blocker signal must be factory issued")
        for name, value in values.items():
            object.__setattr__(self, name, value)
        spec = ABI_WIDTH_READONLY_REASON_SPECS.get(self.reason_id)
        if spec is None:
            raise ValueError("Phase 6.5 blocker reason is not sealed")
        if self.identity_scope is not spec.identity_scope or self.target_kind != spec.target_kind:
            raise ValueError("Phase 6.5 blocker scope/target differs from registry")
        if any(type(item) is not str or not item for item in self.evidence_refs):
            raise TypeError("Phase 6.5 evidence references must be exact strings")
        for value in (
            self.canonical_target_key, self.missing_semantic_fact,
            self.semantic_proposition, self.observation_surface,
            self.active_semantic_precondition, self.correspondence_contract,
        ):
            authority_digest(value)

    @classmethod
    def from_projection_seed(
        cls,
        reason_id: str,
        seed: ReturnObservationProjectionSeed,
        *,
        producer_id: str = "typed-return-observation-signal-v2",
    ) -> "AbiWidthReadonlyBlockerSignal":
        if type(seed) is not ReturnObservationProjectionSeed:
            raise TypeError("pair blocker requires exact projection-seed authority")
        seed.validate()
        if reason_id not in {
            "return_observation_contract_unproven",
            "return_abi_relation_unproven",
            "return_high_bit_relation_unproven",
        }:
            raise ValueError("projection seed cannot own a non-pair reason")
        missing_by_reason = {
            "return_observation_contract_unproven": (
                "return_observation_contract_applicable", False,
            ),
            "return_abi_relation_unproven": ("return_abi_relation_proved", False),
            "return_high_bit_relation_unproven": (
                "return_high_bit_relation_proved", False,
            ),
        }
        spec = ABI_WIDTH_READONLY_REASON_SPECS[reason_id]
        return cls(
            reason_id=reason_id,
            identity_scope=spec.identity_scope,
            target_kind=spec.target_kind,
            canonical_target_key=(
                "return_observation_pair_v2",
                seed.pair_target_key,
                seed.source_snapshot_pair,
                seed.prepared_snapshot_digest,
            ),
            missing_semantic_fact=missing_by_reason[reason_id],
            semantic_proposition=("return_observation_proposition", reason_id),
            observation_surface=(
                "return_projection_seed",
                seed.seed_digest,
                seed.candidate_observation_width,
            ),
            active_semantic_precondition=seed.guard_contract,
            correspondence_contract=(
                "ordered_return_pair",
                seed.left_seed_digest,
                seed.right_seed_digest,
            ),
            evidence_refs=(seed.seed_digest,),
            producer_id=producer_id,
            _factory_token=_BLOCKER_SIGNAL_TOKEN,
        )

    @classmethod
    def from_observation_need_seed(
        cls, seed: ReturnObservationNeedSeed,
    ) -> "AbiWidthReadonlyBlockerSignal":
        if type(seed) is not ReturnObservationNeedSeed:
            raise TypeError("observation blocker requires exact need-seed authority")
        reason_id = "return_observation_contract_unproven"
        spec = ABI_WIDTH_READONLY_REASON_SPECS[reason_id]
        return cls(
            reason_id=reason_id,
            identity_scope=spec.identity_scope,
            target_kind=spec.target_kind,
            canonical_target_key=(
                "return_observation_pair_v2",
                seed.pair_target_key,
                seed.source_snapshot_pair,
                seed.prepared_snapshot_digest,
            ),
            missing_semantic_fact=("common_observation_width", False),
            semantic_proposition=("return_observation_proposition", reason_id),
            observation_surface=("unjoined_widths", seed.left_widths, seed.right_widths),
            active_semantic_precondition=seed.guard_contract,
            correspondence_contract=("ordered_return_pair", seed.left_seed_digest, seed.right_seed_digest),
            evidence_refs=(seed.seed_digest,),
            producer_id="typed-return-observation-need-signal-v2",
            _factory_token=_BLOCKER_SIGNAL_TOKEN,
        )

    @classmethod
    def from_width_seed(
        cls,
        seed: Any,
        missing_slot: str,
    ) -> "AbiWidthReadonlyBlockerSignal":
        from scripts.function_tracer_pcode.proof.return_width.surface import FunctionReturnWidthSeed

        if type(seed) is not FunctionReturnWidthSeed:
            raise TypeError("width blocker requires an exact unary width seed")
        if missing_slot not in seed.unresolved_fact_slots or missing_slot not in _WIDTH_SLOTS:
            raise ValueError("width blocker slot is not unresolved in the exact seed")
        reason_id = "return_width_provenance_unavailable"
        spec = ABI_WIDTH_READONLY_REASON_SPECS[reason_id]
        return cls(
            reason_id=reason_id,
            identity_scope=spec.identity_scope,
            target_kind=spec.target_kind,
            canonical_target_key=(
                "return_site_slot_v2",
                seed.target_id.stable_key(),
                seed.normalization_policy_digest,
            ),
            missing_semantic_fact=("missing_slot", missing_slot),
            semantic_proposition=("return_width_fact_available", missing_slot),
            observation_surface=seed.storage_identity,
            active_semantic_precondition=seed.guard_region_fact.stable_key(),
            correspondence_contract=("one_function_width_seed", seed.digest),
            evidence_refs=(seed.digest, missing_slot),
            producer_id="typed-return-width-seed-signal-v2",
            _factory_token=_BLOCKER_SIGNAL_TOKEN,
        )

    @classmethod
    def from_return_abi_seed(
        cls, seed: FunctionReturnAbiSeed, missing_slot: str
    ) -> "AbiWidthReadonlyBlockerSignal":
        if type(seed) is not FunctionReturnAbiSeed:
            raise TypeError("ABI blocker requires exact typed ABI seed")
        if missing_slot not in seed.missing_slots:
            raise ValueError("ABI blocker slot is not MISSING in the exact ABI seed")
        spec = ABI_WIDTH_READONLY_REASON_SPECS["return_abi_provenance_unavailable"]
        return cls(
            reason_id=spec.reason_id,
            identity_scope=spec.identity_scope,
            target_kind=spec.target_kind,
            canonical_target_key=seed.return_site_target_key,
            missing_semantic_fact=("missing_abi_slot", missing_slot),
            semantic_proposition=("return_abi_fact_available", missing_slot),
            observation_surface=("typed_return_abi_seed", seed.width_seed_digest),
            active_semantic_precondition=("return_site_function", seed.function_snapshot),
            correspondence_contract=("one_function_abi_seed", seed.seed_digest),
            evidence_refs=(seed.seed_digest, missing_slot),
            producer_id="typed-return-abi-fact-seed-v2",
            _factory_token=_BLOCKER_SIGNAL_TOKEN,
        )

    @classmethod
    def from_same_function_width_seeds(
        cls, first_seed: Any, second_seed: Any
    ) -> "AbiWidthReadonlyBlockerSignal":
        from scripts.function_tracer_pcode.proof.return_width.surface import FunctionReturnWidthSeed

        if type(first_seed) is not FunctionReturnWidthSeed or type(
            second_seed
        ) is not FunctionReturnWidthSeed:
            raise TypeError("same-function width relation requires exact seeds")
        if first_seed.target_id.function_identity != second_seed.target_id.function_identity:
            raise ValueError("same-function width relation crossed function identity")
        if first_seed.target_id == second_seed.target_id:
            raise ValueError("same-function width relation requires two distinct members")
        ordered = tuple(sorted(
            (first_seed.target_id.stable_key(), second_seed.target_id.stable_key()),
            key=authority_digest,
        ))
        spec = ABI_WIDTH_READONLY_REASON_SPECS["return_width_relation_unproven"]
        return cls(
            reason_id=spec.reason_id,
            identity_scope=spec.identity_scope,
            target_kind=spec.target_kind,
            canonical_target_key=("same_function_return_pair_v2", first_seed.target_id.function_identity, ordered),
            missing_semantic_fact=("observation_preserving_width_join", False),
            semantic_proposition=("same_function_return_width_relation", "lossless_total"),
            observation_surface=(first_seed.storage_width, first_seed.payload_width, second_seed.storage_width, second_seed.payload_width),
            active_semantic_precondition=(first_seed.guard_region_fact.stable_key(), second_seed.guard_region_fact.stable_key()),
            correspondence_contract=("same_function_member_pair", tuple(sorted((first_seed.digest, second_seed.digest)))),
            evidence_refs=tuple(sorted((first_seed.digest, second_seed.digest))),
            producer_id="typed-same-function-width-signal-v2",
            _factory_token=_BLOCKER_SIGNAL_TOKEN,
        )

    @classmethod
    def from_summary_occurrence(
        cls, analysis: Any, acceptance_result: Any, occurrence: Any
    ) -> "AbiWidthReadonlyBlockerSignal":
        from scripts.function_tracer_pcode.analysis.returns.summary_returns import (
            SummaryReturnAcceptanceResult,
            SummaryReturnBlockerOccurrence,
        )
        from scripts.function_tracer_pcode.core import FunctionReturnAnalysis

        if type(analysis) is not FunctionReturnAnalysis:
            raise TypeError("summary width blocker requires exact function analysis")
        if type(acceptance_result) is not SummaryReturnAcceptanceResult or type(
            occurrence
        ) is not SummaryReturnBlockerOccurrence:
            raise TypeError("summary width blocker requires exact acceptance authority")
        classification = classify_summary_width_source(occurrence.source_code)
        if classification.disposition is not AbiWidthReadonlyDisposition.TYPED_SLICE5_CAUSE:
            raise ValueError("summary occurrence is not owned by slice5")
        if occurrence.function_identity != analysis.outcome_function_identity():
            raise ValueError("summary occurrence function authority differs")
        if occurrence.candidate_id is None or occurrence.candidate_identity is None:
            raise ValueError("summary width occurrence lacks stable candidate identity")
        reason_id = classification.reason_ids[0]
        spec = ABI_WIDTH_READONLY_REASON_SPECS[reason_id]
        if reason_id == "return_width_provenance_unavailable":
            target = (
                "return_site_slot_v2", occurrence.function_identity,
                occurrence.candidate_id, occurrence.candidate_identity,
            )
            missing = ("missing_slot", "summary_return_width_fact")
            proposition = ("summary_return_width_fact_available", True)
            correspondence = ("one_summary_candidate", occurrence.candidate_id)
        else:
            if occurrence.peer_return_identity is None:
                raise ValueError("summary width relation lacks exact peer return identity")
            target = (
                "same_function_return_pair_v2", occurrence.function_identity,
                occurrence.candidate_identity, occurrence.peer_return_identity,
            )
            missing = ("observation_preserving_width_join", False)
            proposition = ("same_function_return_width_relation", "lossless_total")
            correspondence = (
                "summary_candidate_exact_return_pair", occurrence.candidate_id,
            )
        return cls(
            reason_id=reason_id,
            identity_scope=spec.identity_scope,
            target_kind=spec.target_kind,
            canonical_target_key=target,
            missing_semantic_fact=missing,
            semantic_proposition=proposition,
            observation_surface=occurrence.observation_surface_key,
            active_semantic_precondition=occurrence.active_precondition_key,
            correspondence_contract=correspondence,
            evidence_refs=(occurrence.occurrence_digest,),
            producer_id="typed-summary-width-occurrence-v2",
            _factory_token=_BLOCKER_SIGNAL_TOKEN,
        )

    @classmethod
    def from_readonly_member(
        cls, seed: ReadonlyReductionObjectSetSeed, side: str, member_index: int
    ) -> "AbiWidthReadonlyBlockerSignal":
        if type(seed) is not ReadonlyReductionObjectSetSeed:
            raise TypeError("readonly member blocker requires exact object-set seed")
        if side not in {"left", "right"} or type(member_index) is not int:
            raise TypeError("readonly member selector is invalid")
        members = seed.left_member_keys if side == "left" else seed.right_member_keys
        snapshot = seed.left_function_snapshot if side == "left" else seed.right_function_snapshot
        case_key = seed.left_case_key if side == "left" else seed.right_case_key
        if member_index < 0 or member_index >= len(members):
            raise ValueError("readonly member selector is outside the sealed object set")
        member = members[member_index]
        spec = ABI_WIDTH_READONLY_REASON_SPECS["readonly_storage_identity_unproven"]
        return cls(
            reason_id=spec.reason_id,
            identity_scope=spec.identity_scope,
            target_kind=spec.target_kind,
            canonical_target_key=("readonly_load_site_v2", snapshot, case_key, member),
            missing_semantic_fact=("stable_immutable_storage_identity", False),
            semantic_proposition=("readonly_storage_identity", "unique_for_all_reachable_uses"),
            observation_surface=seed.observation_contract,
            active_semantic_precondition=seed.guard_contract,
            correspondence_contract=("readonly_member_of_ordered_set", side, member_index, seed.seed_digest),
            evidence_refs=(seed.seed_digest, authority_digest(member)),
            producer_id="typed-readonly-member-signal-v2",
            _factory_token=_BLOCKER_SIGNAL_TOKEN,
        )

    @classmethod
    def from_readonly_object_sets(
        cls, seed: ResolvedReadonlyObjectSetSeed
    ) -> "AbiWidthReadonlyBlockerSignal":
        if type(seed) is not ResolvedReadonlyObjectSetSeed:
            raise TypeError("readonly correspondence requires exact resolved object-set seed")
        spec = ABI_WIDTH_READONLY_REASON_SPECS["readonly_object_correspondence_unproven"]
        return cls(
            reason_id=spec.reason_id,
            identity_scope=spec.identity_scope,
            target_kind=spec.target_kind,
            canonical_target_key=(
                "readonly_reduction_object_sets_v2",
                seed.ordered_pair_target_key,
                tuple(map(authority_digest, seed.left_member_keys)),
                tuple(map(authority_digest, seed.right_member_keys)),
            ),
            missing_semantic_fact=("unique_total_readonly_correspondence", False),
            semantic_proposition=("readonly_object_correspondence", "unique_total_order_preserving"),
            observation_surface=seed.observation_contract,
            active_semantic_precondition=seed.guard_contract,
            correspondence_contract=("ordered_object_set_pair", seed.seed_digest),
            evidence_refs=(seed.seed_digest, seed.prepared_snapshot_digest),
            producer_id="typed-readonly-object-set-signal-v2",
            _factory_token=_BLOCKER_SIGNAL_TOKEN,
        )


_COMPLETION_ARTIFACT_TOKEN = object()
_STRUCTURAL_HIGH_BIT_THEOREMS = frozenset({
    "same_width_identity_v1",
    "validated_zero_extend_projection_v1",
    "validated_sign_extend_projection_v1",
    "member_local_high_bits_irrelevant_v1",
})


@dataclass(frozen=True, init=False)
class _AbiWidthReadonlyCompletionArtifact:
    reason_id: str
    proof_kind: str
    semantic_target_digest: str
    source_seed_digest: str
    source_snapshot_digest: str
    prepared_snapshot_digest: str
    proof_body: tuple[Any, ...]
    applicability_body: tuple[Any, ...]
    dependency_artifact_digests: tuple[str, ...]
    producer_contract_id: str
    producer_contract_version: str
    encoding_version: str
    registry_digest: str
    common_registry_digest: str
    artifact_digest: str

    REASON_ID = ""
    ENCODING_VERSION = ""

    def __init__(self, **values: Any) -> None:
        if values.pop("_factory_token", None) is not _COMPLETION_ARTIFACT_TOKEN:
            raise TypeError("Phase 6.5 completion artifact must be exact-factory issued")
        supplied = values.pop("artifact_digest", None)
        for name, value in values.items():
            object.__setattr__(self, name, value)
        if self.reason_id != self.REASON_ID:
            raise ValueError("completion artifact reason/class mismatch")
        spec = ABI_WIDTH_READONLY_REASON_SPECS[self.reason_id]
        if self.proof_kind != spec.proof_kind:
            raise ValueError("completion artifact proof kind differs from registry")
        stage = next(item for item in ABI_WIDTH_READONLY_PRODUCER_STAGE_SPECS if item.proof_kind == self.proof_kind)
        if (self.producer_contract_id, self.producer_contract_version) != (
            stage.producer_contract_id, stage.producer_version
        ):
            raise ValueError("completion artifact producer contract differs from registry")
        if self.encoding_version != self.ENCODING_VERSION:
            raise ValueError("completion artifact encoding version mismatch")
        if self.registry_digest != ABI_WIDTH_READONLY_PRODUCER_STAGE_REGISTRY_DIGEST or (
            self.common_registry_digest
            != ABI_WIDTH_READONLY_COMMON_EXECUTION_STAGE_REGISTRY.normalized_registry_digest
        ):
            raise ValueError("completion artifact registry binding mismatch")
        if any(type(item) is not str or not item for item in (
            self.semantic_target_digest, self.source_seed_digest,
            self.source_snapshot_digest, self.prepared_snapshot_digest,
            *self.dependency_artifact_digests,
        )):
            raise TypeError("completion artifact identity is incomplete")
        payload = {name: getattr(self, name) for name in self.__dataclass_fields__ if name != "artifact_digest"}
        digest = authority_digest(payload)
        if supplied is not None and supplied != digest:
            raise ValueError("completion artifact digest mismatch")
        object.__setattr__(self, "artifact_digest", digest)


def _artifact_values(
    artifact_type: type[_AbiWidthReadonlyCompletionArtifact],
    blocker: AbiWidthReadonlyBlockerSignal,
    *,
    source_seed_digest: str,
    source_snapshot_digest: str,
    prepared_snapshot_digest: str,
    proof_body: tuple[Any, ...],
    applicability_body: tuple[Any, ...],
    dependency_artifact_digests: Iterable[str] = (),
) -> _AbiWidthReadonlyCompletionArtifact:
    if type(blocker) is not AbiWidthReadonlyBlockerSignal or blocker.reason_id != artifact_type.REASON_ID:
        raise TypeError("completion factory requires its exact blocker reason")
    spec = ABI_WIDTH_READONLY_REASON_SPECS[blocker.reason_id]
    stage = next(item for item in ABI_WIDTH_READONLY_PRODUCER_STAGE_SPECS if item.proof_kind == spec.proof_kind)
    return artifact_type(
        reason_id=blocker.reason_id,
        proof_kind=spec.proof_kind,
        semantic_target_digest=authority_digest(blocker.canonical_target_key),
        source_seed_digest=source_seed_digest,
        source_snapshot_digest=source_snapshot_digest,
        prepared_snapshot_digest=prepared_snapshot_digest,
        proof_body=proof_body,
        applicability_body=applicability_body,
        dependency_artifact_digests=tuple(sorted(dependency_artifact_digests)),
        producer_contract_id=stage.producer_contract_id,
        producer_contract_version=stage.producer_version,
        encoding_version=artifact_type.ENCODING_VERSION,
        registry_digest=ABI_WIDTH_READONLY_PRODUCER_STAGE_REGISTRY_DIGEST,
        common_registry_digest=ABI_WIDTH_READONLY_COMMON_EXECUTION_STAGE_REGISTRY.normalized_registry_digest,
        _factory_token=_COMPLETION_ARTIFACT_TOKEN,
    )


def _validate_solver_query_receipt_binding(
    query_authority: Any, membership: Any, execution_receipt: Any
) -> None:
    """Recheck the renderer/assignment/attempt join at artifact issuance."""

    expected_query_binding_digest = authority_digest({
        "renderer_query_authority_digest": query_authority.authority_digest,
        "result_occurrence_id": execution_receipt.result_occurrence_id,
        "proof_requirement_id": membership.proof_requirement_id,
        "obligation_id": membership.obligation_id,
        "observation_contract_id": membership.observation_contract_id,
        "producer_stage": membership.proof_stage,
        "execution_identity_digest": membership.execution_identity_digest,
    })
    if (
        execution_receipt.query_authority_digest
        != expected_query_binding_digest
        or execution_receipt.normalized_query != query_authority.query_text
        or membership.proof_stage != query_authority.proof_stage
        or membership.obligation_id != query_authority.obligation_id
        or membership.observation_contract_id
        != query_authority.observation_contract_id
        or membership.execution_identity_digest
        != query_authority.execution_identity_digest
    ):
        raise ValueError("solver artifact receipt differs from semantic query authority")


class ReturnWidthProvenanceArtifact(_AbiWidthReadonlyCompletionArtifact):
    REASON_ID = "return_width_provenance_unavailable"
    ENCODING_VERSION = "return-width-provenance-encoding-v2"

class SameFunctionReturnWidthRelationArtifact(_AbiWidthReadonlyCompletionArtifact):
    REASON_ID = "return_width_relation_unproven"
    ENCODING_VERSION = "same-function-return-width-relation-encoding-v2"

class ReturnAbiProvenanceArtifact(_AbiWidthReadonlyCompletionArtifact):
    REASON_ID = "return_abi_provenance_unavailable"
    ENCODING_VERSION = "return-abi-provenance-encoding-v2"

    @classmethod
    def from_void_effect_surface(cls, blocker, seed, *, source_snapshot_fingerprint):
        """Structural proof that the return storage slot is not observable.

        For a ``void`` function with a complete, non-empty memory-effect
        comparison surface the return storage descriptor is semantically
        absent: the observation contract is the effect surface, whose width
        the unary width artifacts already establish.  The proof replays the
        sealed surface fact of the exact seed and covers only the
        ``return_storage_descriptor`` slot (Issue #104, Gap 6).
        """

        if type(seed) is not FunctionReturnAbiSeed:
            raise TypeError("void effect-only ABI proof requires the exact ABI seed")
        if not seed.void_effect_only_surface:
            raise ValueError("ABI seed is not a void effect-only surface")
        expected = AbiWidthReadonlyBlockerSignal.from_return_abi_seed(
            seed, "return_storage_descriptor"
        )
        if blocker != expected:
            raise ValueError("void effect-only ABI proof differs from its blocker")
        return _artifact_values(
            cls,
            blocker,
            source_seed_digest=seed.seed_digest,
            source_snapshot_digest=source_snapshot_fingerprint,
            prepared_snapshot_digest=seed.prepared_snapshot_digest,
            proof_body=(
                "void_effect_only_return_abi_v1",
                "return_storage_semantically_absent",
                seed.surface_fact,
                seed.slot_facts,
            ),
            applicability_body=(
                "void_effect_surface",
                seed.function_snapshot,
                ("missing_abi_slot", "return_storage_descriptor"),
            ),
            dependency_artifact_digests=(),
        )

class ReturnObservationContractArtifact(_AbiWidthReadonlyCompletionArtifact):
    REASON_ID = "return_observation_contract_unproven"
    ENCODING_VERSION = "return-observation-contract-encoding-v2"

    @classmethod
    def from_projection_seed(cls, blocker, seed, *, derivation, projection_policy,
                             source_snapshot_fingerprint, high_bit_dependency=None):
        if type(seed) is not ReturnObservationProjectionSeed or blocker.evidence_refs[0] != seed.seed_digest:
            raise ValueError("observation artifact differs from projection seed authority")
        if derivation not in {"common_validated_semantic_payload_width"}:
            raise ValueError("observation width derivation is not sealed")
        if not projection_policy:
            raise ValueError("observation contract lacks a projection policy")
        if high_bit_dependency is not None and (
            type(high_bit_dependency) is not ReturnHighBitRelationProofArtifact
            or high_bit_dependency.source_seed_digest != seed.seed_digest
            or high_bit_dependency.semantic_target_digest != authority_digest(
                AbiWidthReadonlyBlockerSignal.from_projection_seed(
                    "return_high_bit_relation_unproven", seed
                ).canonical_target_key
            )
        ):
            raise ValueError("observation contract high-bit dependency targets another seed")
        dependencies = () if high_bit_dependency is None else (high_bit_dependency.artifact_digest,)
        if projection_policy != "identity" and high_bit_dependency is None:
            raise ValueError("non-identity observation projection lacks high-bit proof")
        return _artifact_values(cls, blocker, source_seed_digest=seed.seed_digest,
            source_snapshot_digest=source_snapshot_fingerprint,
            prepared_snapshot_digest=seed.prepared_snapshot_digest,
            proof_body=("return_observation_contract_v2", seed.candidate_observation_width,
                        derivation, projection_policy),
            applicability_body=("both_complete_unary_surfaces", seed.left_seed_digest, seed.right_seed_digest),
            dependency_artifact_digests=dependencies)


class ReturnAbiRelationArtifact(_AbiWidthReadonlyCompletionArtifact):
    REASON_ID = "return_abi_relation_unproven"
    ENCODING_VERSION = "return-abi-relation-encoding-v2"

    @classmethod
    def from_assessment(
        cls,
        blocker,
        seed,
        assessment,
        left_abi_seed,
        right_abi_seed,
        *,
        source_snapshot_fingerprint,
    ):
        if (
            type(seed) is not ReturnObservationProjectionSeed
            or type(assessment) is not ReturnAbiCompatibilityAssessment
            or type(left_abi_seed) is not FunctionReturnAbiSeed
            or type(right_abi_seed) is not FunctionReturnAbiSeed
            or assessment.status is not ReturnAbiRelationStatus.PROVED
            or assessment.projection_seed_digest != seed.seed_digest
            or assessment.left_abi_seed_digest != left_abi_seed.seed_digest
            or assessment.right_abi_seed_digest != right_abi_seed.seed_digest
            or not left_abi_seed.observation_complete
            or not right_abi_seed.observation_complete
        ):
            raise ValueError("ABI relation assessment authority is incomplete")
        expected = ReturnAbiCompatibilityAssessment.assess(
            seed, left_abi_seed, right_abi_seed
        )
        if expected != assessment:
            raise ValueError("ABI relation assessment does not replay")
        return _artifact_values(
            cls,
            blocker,
            source_seed_digest=seed.seed_digest,
            source_snapshot_digest=source_snapshot_fingerprint,
            prepared_snapshot_digest=seed.prepared_snapshot_digest,
            proof_body=(
                "return_abi_relation_assessment_v1",
                assessment.assessment_digest,
                assessment.predicate_body,
                left_abi_seed.slot_facts,
                right_abi_seed.slot_facts,
            ),
            applicability_body=("active_guard", seed.guard_contract),
            dependency_artifact_digests=(),
        )

    @classmethod
    def from_projection_seed(cls, blocker, seed, *, left_abi_artifact,
                             right_abi_artifact, source_snapshot_fingerprint,
                             calling_conventions_individually_valid,
                             storage_projection_related, observation_applicable):
        if type(seed) is not ReturnObservationProjectionSeed or not all(
            value is True for value in (
                calling_conventions_individually_valid,
                storage_projection_related,
                observation_applicable,
            )
        ):
            raise ValueError("ABI relation lacks its three-predicate conjunction")
        if type(left_abi_artifact) is not ReturnAbiProvenanceArtifact or type(
            right_abi_artifact
        ) is not ReturnAbiProvenanceArtifact:
            raise TypeError("ABI relation requires exact unary ABI artifacts")
        if (
            left_abi_artifact.semantic_target_digest
            != seed.left_return_site_target_digest
            or right_abi_artifact.semantic_target_digest
            != seed.right_return_site_target_digest
        ):
            raise ValueError("ABI relation unary target dependencies differ from pair seed")
        return _artifact_values(cls, blocker, source_seed_digest=seed.seed_digest,
            source_snapshot_digest=source_snapshot_fingerprint,
            prepared_snapshot_digest=seed.prepared_snapshot_digest,
            proof_body=(
                "return_abi_semantic_projection_v3",
                calling_conventions_individually_valid,
                storage_projection_related,
                observation_applicable,
            ),
            applicability_body=("active_guard", seed.guard_contract),
            dependency_artifact_digests=(left_abi_artifact.artifact_digest, right_abi_artifact.artifact_digest))


class ReturnHighBitRelationProofArtifact(_AbiWidthReadonlyCompletionArtifact):
    REASON_ID = "return_high_bit_relation_unproven"
    ENCODING_VERSION = "return-high-bit-relation-encoding-v2"

    @classmethod
    def from_solver_unsat(
        cls, blocker, seed, abi_relation_artifact, *, query_authority,
        membership, execution_receipt, lifecycle_projection,
        source_snapshot_fingerprint,
    ):
        from scripts.function_tracer_pcode.authority.contracts import (
            VerifiedLifecyclePrefixProjection,
        )
        from scripts.function_tracer_pcode.authority.lifecycle.execution_authority import (
            GenericSolverExecutionReceipt,
            ProducerAttemptMembership,
        )

        if (
            type(seed) is not ReturnObservationProjectionSeed
            or type(abi_relation_artifact) is not ReturnAbiRelationArtifact
            or type(query_authority) is not AbiWidthReadonlySolverQueryAuthority
            or type(membership) is not ProducerAttemptMembership
            or type(execution_receipt) is not GenericSolverExecutionReceipt
            or type(lifecycle_projection) is not VerifiedLifecyclePrefixProjection
            or query_authority.proof_kind != "return_high_bit_relation"
            or query_authority.semantic_target_digest
            != membership.requirement_assignment.semantic_target_digest
            or query_authority.prepared_surface_digest
            != seed.prepared_snapshot_digest
            or query_authority.dependency_artifact_digests
            != (abi_relation_artifact.artifact_digest,)
            or execution_receipt.observed_status != "unsat"
        ):
            raise ValueError("high-bit solver UNSAT authority is incomplete")
        membership.validate_against(ABI_WIDTH_READONLY_COMMON_EXECUTION_STAGE_REGISTRY)
        membership.requirement_assignment.validate_against(lifecycle_projection)
        execution_receipt.validate_join(
            ABI_WIDTH_READONLY_COMMON_EXECUTION_STAGE_REGISTRY, membership
        )
        _validate_solver_query_receipt_binding(
            query_authority, membership, execution_receipt
        )
        return _artifact_values(
            cls, blocker, source_seed_digest=seed.seed_digest,
            source_snapshot_digest=source_snapshot_fingerprint,
            prepared_snapshot_digest=seed.prepared_snapshot_digest,
            proof_body=(
                "return_high_bit_solver_unsat_v2",
                query_authority.authority_digest,
                execution_receipt.receipt_digest,
                query_authority.theorem_body,
            ),
            applicability_body=(
                "exact_projection_guard_and_live_assignment",
                seed.guard_contract,
                membership.requirement_assignment.assignment_digest,
            ),
            dependency_artifact_digests=(abi_relation_artifact.artifact_digest,),
        )


class ReadonlyStorageIdentityArtifact(_AbiWidthReadonlyCompletionArtifact):
    REASON_ID = "readonly_storage_identity_unproven"
    ENCODING_VERSION = "readonly-storage-identity-encoding-v2"

class ReadonlyObjectCorrespondenceArtifact(_AbiWidthReadonlyCompletionArtifact):
    REASON_ID = "readonly_object_correspondence_unproven"
    ENCODING_VERSION = "readonly-object-correspondence-encoding-v2"

    @classmethod
    def from_solver_unsat(
        cls, blocker, seed, *, query_authority, membership,
        execution_receipt, lifecycle_projection, source_snapshot_fingerprint,
    ):
        from scripts.function_tracer_pcode.authority.contracts import (
            VerifiedLifecyclePrefixProjection,
        )
        from scripts.function_tracer_pcode.authority.lifecycle.execution_authority import (
            GenericSolverExecutionReceipt,
            ProducerAttemptMembership,
        )

        if (
            type(seed) is not ResolvedReadonlyObjectSetSeed
            or type(query_authority) is not AbiWidthReadonlySolverQueryAuthority
            or type(membership) is not ProducerAttemptMembership
            or type(execution_receipt) is not GenericSolverExecutionReceipt
            or type(lifecycle_projection) is not VerifiedLifecyclePrefixProjection
            or query_authority.proof_kind != "readonly_object_correspondence"
            or query_authority.semantic_target_digest
            != membership.requirement_assignment.semantic_target_digest
            or query_authority.prepared_surface_digest
            != seed.prepared_snapshot_digest
            or query_authority.dependency_artifact_digests
            != seed.dependency_artifact_digests
            or execution_receipt.observed_status != "unsat"
        ):
            raise ValueError("readonly solver UNSAT authority is incomplete")
        membership.validate_against(ABI_WIDTH_READONLY_COMMON_EXECUTION_STAGE_REGISTRY)
        membership.requirement_assignment.validate_against(lifecycle_projection)
        execution_receipt.validate_join(
            ABI_WIDTH_READONLY_COMMON_EXECUTION_STAGE_REGISTRY, membership
        )
        _validate_solver_query_receipt_binding(
            query_authority, membership, execution_receipt
        )
        return _artifact_values(
            cls, blocker, source_seed_digest=seed.seed_digest,
            source_snapshot_digest=source_snapshot_fingerprint,
            prepared_snapshot_digest=seed.prepared_snapshot_digest,
            proof_body=(
                "readonly_correspondence_solver_unsat_v2",
                query_authority.authority_digest,
                execution_receipt.receipt_digest,
                query_authority.theorem_body,
            ),
            applicability_body=(
                "resolved_guard_iteration_live_assignment",
                seed.guard_contract,
                seed.observation_contract,
                membership.requirement_assignment.assignment_digest,
            ),
            dependency_artifact_digests=seed.dependency_artifact_digests,
        )


_ABI_WIDTH_SOLVER_QUERY_TOKEN = object()


def _live_completion_receipt_for(
    session: Any,
    blocker: AbiWidthReadonlyBlockerSignal,
    artifact: _AbiWidthReadonlyCompletionArtifact,
    receipt: RequirementCompletionReceipt,
) -> None:
    if (
        type(blocker) is not AbiWidthReadonlyBlockerSignal
        or not isinstance(artifact, _AbiWidthReadonlyCompletionArtifact)
        or type(receipt) is not RequirementCompletionReceipt
        or receipt.proof_artifact_digest != artifact.artifact_digest
        or artifact.source_snapshot_digest
        != session.identity.source_snapshot_fingerprint
    ):
        raise ValueError("solver dependency object authority differs")
    authority = session.domain_signal_encoder.authority_for_signal(session, blocker)
    requirement = authority.bound_contract.slot_bindings[0][1]
    if (
        receipt.occurrence_id != authority.occurrence.occurrence_id
        or receipt.cause_id != authority.occurrence.cause_id.value
        or receipt.proof_requirement_id != requirement.requirement_id
    ):
        raise ValueError("solver dependency receipt differs from exact source Q")
    matches = tuple(
        event for event in session.recorder.prefix_view().events
        if event.header.event_type is EventType.REQUIREMENT_COMPLETED
        and event.authority_payload.completion_receipt == receipt
    )
    if len(matches) != 1:
        raise ValueError("solver dependency is not completed in the current prefix")


@dataclass(frozen=True, init=False)
class AbiWidthReadonlySolverQueryAuthority:
    proof_stage: str
    proof_kind: str
    obligation_id: str
    observation_contract_id: str
    semantic_target_digest: str
    query_text: str
    normalized_assertion_text: str
    declaration_rows: tuple[str, ...]
    premise_assertions: tuple[str, ...]
    theorem_body: Any
    source_snapshot_digests: tuple[str, ...]
    prepared_surface_digest: str
    dependency_artifact_digests: tuple[str, ...]
    dependency_completion_receipt_digests: tuple[str, ...]
    execution_identity_digest: str
    authority_digest: str

    def __init__(self, **values: Any) -> None:
        if values.pop("_factory_token", None) is not _ABI_WIDTH_SOLVER_QUERY_TOKEN:
            raise TypeError("ABI/width solver query must be renderer issued")
        supplied = values.pop("authority_digest", None)
        for name, value in values.items():
            object.__setattr__(self, name, value)
        digest = authority_digest(values)
        if supplied is not None and supplied != digest:
            raise ValueError("ABI/width solver query authority digest mismatch")
        object.__setattr__(self, "authority_digest", digest)
        self.validate()

    def validate(self) -> None:
        if self.proof_kind not in {
            "return_high_bit_relation", "readonly_object_correspondence"
        } or self.proof_stage != self.proof_kind:
            raise ValueError("ABI/width solver query stage is not sealed")
        for value in (
            self.obligation_id, self.observation_contract_id,
            self.semantic_target_digest, self.query_text,
            self.normalized_assertion_text, self.prepared_surface_digest,
            self.execution_identity_digest, self.authority_digest,
        ):
            if type(value) is not str or not value:
                raise TypeError("ABI/width solver query string authority is incomplete")
        if not self.query_text.endswith("(check-sat)"):
            raise ValueError("ABI/width solver query is not a complete SMT query")
        expected_query = "\n".join((
            *self.declaration_rows,
            *self.premise_assertions,
            f"(assert {self.normalized_assertion_text})",
            "(check-sat)",
        ))
        if self.query_text != expected_query:
            raise ValueError("ABI/width query does not match its sealed replay surface")
        if self.dependency_artifact_digests != tuple(sorted(
            self.dependency_artifact_digests
        )) or self.dependency_completion_receipt_digests != tuple(sorted(
            self.dependency_completion_receipt_digests
        )):
            raise ValueError("ABI/width solver dependency digests are noncanonical")

    @property
    def stage(self) -> str:
        return self.proof_stage

    @staticmethod
    def _extended_payload(
        name: str, payload_width: int, storage_width: int, kind: str
    ) -> str:
        if storage_width == payload_width and kind == "same_width":
            return name
        extension = storage_width - payload_width
        if extension <= 0:
            raise ValueError("high-bit renderer lacks a sealed extension relation")
        if kind in {"zero_extend", "sign_extend"}:
            op = "zero_extend" if kind == "zero_extend" else "sign_extend"
            return f"((_ {op} {extension}) {name})"
        prefix = "zero_extend_or_mask:"
        if kind.startswith(prefix):
            mask_text = kind[len(prefix):]
            if not mask_text or any(
                character < "0" or character > "9"
                for character in mask_text
            ):
                raise ValueError("high-bit renderer mask is not canonical")
            mask = int(mask_text)
            if mask_text != str(mask):
                raise ValueError("high-bit renderer mask is not canonical")
            if not (
                0 < mask < (1 << storage_width)
                and mask & ((1 << payload_width) - 1) == 0
            ):
                raise ValueError("high-bit renderer mask overlaps payload")
            widened = f"((_ zero_extend {extension}) {name})"
            return f"(bvor {widened} (_ bv{mask} {storage_width}))"
        raise ValueError("high-bit renderer lacks a sealed extension relation")

    @classmethod
    def from_high_bit_theorem(
        cls,
        session: Any,
        blocker: AbiWidthReadonlyBlockerSignal,
        seed: ReturnObservationProjectionSeed,
        abi_dependency: tuple[Any, Any, Any],
    ) -> "AbiWidthReadonlySolverQueryAuthority":
        dependency_blocker, artifact, receipt = abi_dependency
        if (
            type(seed) is not ReturnObservationProjectionSeed
            or type(artifact) is not ReturnAbiRelationArtifact
            or blocker != AbiWidthReadonlyBlockerSignal.from_projection_seed(
                "return_high_bit_relation_unproven", seed
            )
            or artifact.source_seed_digest != seed.seed_digest
        ):
            raise ValueError("high-bit query seed/dependency authority differs")
        _live_completion_receipt_for(
            session, dependency_blocker, artifact, receipt
        )
        target_authority = session.domain_signal_encoder.authority_for_signal(
            session, blocker
        )
        target_requirement = target_authority.bound_contract.slot_bindings[0][1]
        width = seed.candidate_observation_width
        if seed.left_storage_width != seed.right_storage_width:
            raise ValueError("high-bit renderer requires ABI-related storage widths")
        left = cls._extended_payload(
            "left_payload", width, seed.left_storage_width,
            seed.left_extension_kind,
        )
        right = cls._extended_payload(
            "right_payload", width, seed.right_storage_width,
            seed.right_extension_kind,
        )
        declarations = (
            f"(declare-const left_payload (_ BitVec {width}))",
            f"(declare-const right_payload (_ BitVec {width}))",
        )
        premise_assertions = (
            "(assert (= left_payload right_payload))",
        )
        normalized_assertion = f"(not (= {left} {right}))"
        query = "\n".join((
            *declarations, *premise_assertions,
            f"(assert {normalized_assertion})", "(check-sat)",
        ))
        theorem = (
            "negated_return_high_bit_relation_v2", seed.seed_digest,
            seed.guard_contract, width, seed.left_extension_kind,
            seed.right_extension_kind, artifact.artifact_digest,
        )
        return cls(
            proof_stage="return_high_bit_relation",
            proof_kind="return_high_bit_relation",
            obligation_id="abi-width-obligation-" + authority_digest(theorem)[:32],
            observation_contract_id="return-high-bit-observation-" + seed.seed_digest[:24],
            semantic_target_digest=authority_digest({
                "semantic_target": canonical_value(
                    target_requirement.semantic_target_key
                )
            }),
            query_text=query,
            normalized_assertion_text=normalized_assertion,
            declaration_rows=declarations,
            premise_assertions=premise_assertions,
            theorem_body=theorem,
            source_snapshot_digests=tuple(
                authority_digest(item) for item in seed.source_snapshot_pair[1:]
            ),
            prepared_surface_digest=seed.prepared_snapshot_digest,
            dependency_artifact_digests=(artifact.artifact_digest,),
            dependency_completion_receipt_digests=(authority_digest(receipt),),
            execution_identity_digest=session.identity.execution_identity_digest,
            _factory_token=_ABI_WIDTH_SOLVER_QUERY_TOKEN,
        )

    @classmethod
    def from_readonly_correspondence_theorem(
        cls,
        session: Any,
        blocker: AbiWidthReadonlyBlockerSignal,
        seed: ResolvedReadonlyObjectSetSeed,
    ) -> "AbiWidthReadonlySolverQueryAuthority":
        if (
            type(seed) is not ResolvedReadonlyObjectSetSeed
            or blocker != AbiWidthReadonlyBlockerSignal.from_readonly_object_sets(seed)
            or len(seed.left_member_keys) != len(seed.right_member_keys)
        ):
            raise ValueError("readonly query requires one exact resolved ordered set pair")
        completion_receipts = {
            authority_digest(event.authority_payload.completion_receipt)
            for event in session.recorder.prefix_view().events
            if event.header.event_type is EventType.REQUIREMENT_COMPLETED
        }
        if not set(seed.dependency_completion_receipt_digests).issubset(
            completion_receipts
        ):
            raise ValueError("readonly query dependency closure is stale")
        target_authority = session.domain_signal_encoder.authority_for_signal(
            session, blocker
        )
        target_requirement = target_authority.bound_contract.slot_bindings[0][1]
        facts = ReadonlyCorrespondenceFactSet.from_resolved_seed(seed)
        declarations = tuple(
            f"(declare-const {name} (_ BitVec {facts.value_width_bits}))"
            for name in sorted(set((
                *facts.left_value_symbols, *facts.right_value_symbols
            )))
        )
        premise_assertions: tuple[str, ...] = ()

        def total(values: tuple[str, ...]) -> str:
            values = list(values)
            expression = values[0]
            for value in values[1:]:
                expression = f"(bvadd {expression} {value})"
            return expression

        normalized_assertion = (
            f"(not (= {total(facts.left_value_symbols)} "
            f"{total(facts.right_value_symbols)}))"
        )
        theorem = (
            "negated_readonly_unique_total_correspondence_v2",
            seed.seed_digest,
            facts.fact_digest,
            facts.mapping,
            facts.premise_fact_rows,
            facts.shared_value_authority_rows,
            facts.goal_fact_row,
        )
        query = "\n".join((
            *declarations, *premise_assertions,
            f"(assert {normalized_assertion})", "(check-sat)"
        ))
        return cls(
            proof_stage="readonly_object_correspondence",
            proof_kind="readonly_object_correspondence",
            obligation_id="abi-width-obligation-" + authority_digest(theorem)[:32],
            observation_contract_id="readonly-observation-" + seed.seed_digest[:24],
            semantic_target_digest=authority_digest({
                "semantic_target": canonical_value(
                    target_requirement.semantic_target_key
                )
            }),
            query_text=query,
            normalized_assertion_text=normalized_assertion,
            declaration_rows=declarations,
            premise_assertions=premise_assertions,
            theorem_body=theorem,
            source_snapshot_digests=(
                authority_digest(seed.ordered_pair_target_key[1]),
                authority_digest(seed.ordered_pair_target_key[2]),
            ),
            prepared_surface_digest=seed.prepared_snapshot_digest,
            dependency_artifact_digests=seed.dependency_artifact_digests,
            dependency_completion_receipt_digests=(
                seed.dependency_completion_receipt_digests
            ),
            execution_identity_digest=session.identity.execution_identity_digest,
            _factory_token=_ABI_WIDTH_SOLVER_QUERY_TOKEN,
        )


@dataclass
class AbiWidthReadonlySolverExecutionContext:
    lifecycle_projection: Any
    result_occurrence_id: str
    q_open_row: Any
    attempt_ordinals: dict[tuple[str, str], int]
    _attempt_lock: Any

    def __init__(self, lifecycle_projection: Any, q_open_row: Any) -> None:
        from scripts.function_tracer_pcode.authority.contracts import (
            QOpenBaseRow,
            VerifiedLifecyclePrefixProjection,
        )

        if type(lifecycle_projection) is not VerifiedLifecyclePrefixProjection:
            raise TypeError("ABI/width execution context requires PREFIX authority")
        lifecycle_projection.validate()
        if type(q_open_row) is not QOpenBaseRow or q_open_row not in (
            lifecycle_projection.q_open_base
        ):
            raise ValueError("ABI/width execution context lacks one live Q")
        self.lifecycle_projection = lifecycle_projection
        self.result_occurrence_id = lifecycle_projection.result_occurrence_id
        self.q_open_row = q_open_row
        self.attempt_ordinals = {}
        self._attempt_lock = threading.RLock()

    def membership_for(self, query: AbiWidthReadonlySolverQueryAuthority) -> Any:
        from scripts.function_tracer_pcode.authority.lifecycle.execution_authority import (
            ProducerAttemptMembership,
            issue_abi_width_readonly_requirement_assignment,
        )

        if type(query) is not AbiWidthReadonlySolverQueryAuthority:
            raise TypeError("ABI/width membership requires exact query")
        assignment = issue_abi_width_readonly_requirement_assignment(
            projection=self.lifecycle_projection,
            q_open_row=self.q_open_row,
            query_authority=query,
        )
        spec = next(
            item for item in ABI_WIDTH_READONLY_PRODUCER_STAGE_SPECS
            if item.proof_stage == query.proof_stage
            and item.proof_kind == query.proof_kind
        )
        key = (query.obligation_id, query.proof_stage)
        with self._attempt_lock:
            ordinal = self.attempt_ordinals.get(key, 0) + 1
            self.attempt_ordinals[key] = ordinal
        return ProducerAttemptMembership(
            ABI_WIDTH_READONLY_DOMAIN_ID,
            spec.producer_contract_id,
            spec.producer_version,
            spec.proof_stage,
            self.q_open_row.proof_requirement_id,
            query.obligation_id,
            query.observation_contract_id,
            "attempted",
            f"{self.result_occurrence_id}:{query.obligation_id}:{query.proof_stage}",
            ordinal,
            query.execution_identity_digest,
            assignment,
        )


_ABI_WIDTH_SOLVER_BATCH_TOKEN = object()


@dataclass(frozen=True, init=False)
class AbiWidthReadonlySolverExecutionBatchSignal:
    blocker: AbiWidthReadonlyBlockerSignal
    query_authority: AbiWidthReadonlySolverQueryAuthority
    proof_seed: Any
    dependency_artifacts: tuple[Any, ...]
    membership: Any
    execution_receipts: tuple[Any, ...]
    lifecycle_projection: Any

    def __init__(
        self, blocker: Any, query_authority: Any, proof_seed: Any,
        dependency_artifacts: Iterable[Any], membership: Any,
        execution_receipts: Iterable[Any], lifecycle_projection: Any,
        *, _factory_token: object = None,
    ) -> None:
        from scripts.function_tracer_pcode.authority.contracts import (
            VerifiedLifecyclePrefixProjection,
        )
        from scripts.function_tracer_pcode.authority.lifecycle.execution_authority import (
            GenericSolverExecutionReceipt,
            ProducerAttemptMembership,
        )

        if _factory_token is not _ABI_WIDTH_SOLVER_BATCH_TOKEN:
            raise TypeError("ABI/width solver batch must be issuer joined")
        receipts = tuple(execution_receipts)
        dependencies = tuple(dependency_artifacts)
        if (
            type(blocker) is not AbiWidthReadonlyBlockerSignal
            or type(query_authority) is not AbiWidthReadonlySolverQueryAuthority
            or type(membership) is not ProducerAttemptMembership
            or type(lifecycle_projection) is not VerifiedLifecyclePrefixProjection
            or not receipts
            or any(type(item) is not GenericSolverExecutionReceipt for item in receipts)
        ):
            raise TypeError("ABI/width solver batch authority is incomplete")
        if query_authority.proof_kind == "return_high_bit_relation":
            if type(proof_seed) is not ReturnObservationProjectionSeed or (
                len(dependencies) != 1
                or type(dependencies[0]) is not ReturnAbiRelationArtifact
            ):
                raise TypeError("high-bit solver batch dependencies are incomplete")
        elif query_authority.proof_kind == "readonly_object_correspondence":
            if type(proof_seed) is not ResolvedReadonlyObjectSetSeed or tuple(
                sorted(item.artifact_digest for item in dependencies)
            ) != query_authority.dependency_artifact_digests:
                raise TypeError("readonly solver batch dependencies are incomplete")
        if tuple(sorted(item.artifact_digest for item in dependencies)) != (
            query_authority.dependency_artifact_digests
        ):
            raise ValueError("ABI/width batch dependency artifacts differ from query")
        lifecycle_projection.validate()
        membership.validate_against(ABI_WIDTH_READONLY_COMMON_EXECUTION_STAGE_REGISTRY)
        membership.requirement_assignment.validate_against(lifecycle_projection)
        expected_query_binding_digest = authority_digest({
            "renderer_query_authority_digest": query_authority.authority_digest,
            "result_occurrence_id": receipts[0].result_occurrence_id,
            "proof_requirement_id": membership.proof_requirement_id,
            "obligation_id": membership.obligation_id,
            "observation_contract_id": membership.observation_contract_id,
            "producer_stage": membership.proof_stage,
            "execution_identity_digest": membership.execution_identity_digest,
        })
        for receipt in receipts:
            receipt.validate_join(
                ABI_WIDTH_READONLY_COMMON_EXECUTION_STAGE_REGISTRY, membership
            )
            if receipt.query_authority_digest != expected_query_binding_digest:
                raise ValueError("ABI/width receipt differs from semantic query")
        if (
            membership.proof_stage != query_authority.proof_stage
            or membership.obligation_id != query_authority.obligation_id
            or membership.observation_contract_id
            != query_authority.observation_contract_id
        ):
            raise ValueError("ABI/width query and membership differ")
        object.__setattr__(self, "blocker", blocker)
        object.__setattr__(self, "query_authority", query_authority)
        object.__setattr__(self, "proof_seed", proof_seed)
        object.__setattr__(self, "dependency_artifacts", dependencies)
        object.__setattr__(self, "membership", membership)
        object.__setattr__(self, "lifecycle_projection", lifecycle_projection)
        object.__setattr__(self, "execution_receipts", tuple(sorted(
            receipts, key=lambda item: item.invocation_ordinal
        )))

    @classmethod
    def from_issuer_results(
        cls, blocker: Any, query_authority: Any, proof_seed: Any,
        dependency_artifacts: Iterable[Any], membership: Any,
        execution_receipts: Iterable[Any], lifecycle_projection: Any,
    ) -> "AbiWidthReadonlySolverExecutionBatchSignal":
        return cls(
            blocker, query_authority, proof_seed, dependency_artifacts,
            membership, execution_receipts,
            lifecycle_projection, _factory_token=_ABI_WIDTH_SOLVER_BATCH_TOKEN,
        )

class AbiWidthReadonlyPilotEncoder:
    """Encode exact Phase 6.5 blocker signals into independent C/Q authority."""

    def __init__(
        self, *, enable_solver_execution: bool = False,
        solver_timeout_ms: int = 1000,
    ) -> None:
        if type(enable_solver_execution) is not bool:
            raise TypeError("ABI/width solver activation must be exact boolean")
        if type(solver_timeout_ms) is not int or solver_timeout_ms <= 0:
            raise TypeError("ABI/width solver timeout must be a positive integer")
        self._enable_solver_execution = enable_solver_execution
        self._solver_timeout_ms = solver_timeout_ms
        self._cause_factory = SemanticCauseIdentityFactory(
            ABI_WIDTH_READONLY_REASON_REGISTRY
        )
        self._binding_factory = SatisfactionBindingFactory(
            ABI_WIDTH_READONLY_RECOVERY_REGISTRY
        )

    def validate_startup(self) -> Any:
        from scripts.function_tracer_pcode.authority.lifecycle.execution_authority import (
            validate_execution_authority_deployment,
        )

        return (
            validate_execution_authority_deployment()
            if self._enable_solver_execution else None
        )

    def authority_for_signal(
        self, session: Any, signal: AbiWidthReadonlyBlockerSignal
    ) -> CauseOccurrenceAuthority:
        if type(signal) is not AbiWidthReadonlyBlockerSignal:
            raise TypeError("Phase 6.5 encoder requires an exact blocker signal")
        spec = ABI_WIDTH_READONLY_REASON_SPECS[signal.reason_id]
        cause = self._cause_factory.create(
            reason_id=signal.reason_id,
            identity_scope=signal.identity_scope,
            target_kind=signal.target_kind,
            canonical_target_key=signal.canonical_target_key,
            missing_semantic_fact=signal.missing_semantic_fact,
            semantic_proposition=signal.semantic_proposition,
            observation_surface=signal.observation_surface,
            active_semantic_precondition=signal.active_semantic_precondition,
            correspondence_contract=signal.correspondence_contract,
        )
        requirement = ProofRequirement(
            "abi-width-q-" + authority_digest({
                "cause_id": cause.value,
                "proof_kind": spec.proof_kind,
            })[:32],
            spec.proof_kind,
            (
                "abi_width_readonly_semantic_target_v2",
                signal.canonical_target_key,
                signal.missing_semantic_fact,
                spec.proof_kind,
            ),
        )
        bound = self._binding_factory.bind(
            contract_definition_id=spec.contract_definition_id,
            contract_version=1,
            bindings={"proof": requirement},
        )
        occurrence = CauseOccurrence(
            "abi-width-occ-" + authority_digest({
                "cause_id": cause.value,
                "result_occurrence_id": session.identity.result_occurrence_id,
            })[:32],
            cause,
            signal.reason_id,
            authority_digest(signal.canonical_target_key),
            signal.target_kind,
            signal.identity_scope,
            bound.contract_definition_id,
            bound.contract_version,
            bound.normalized_expression_digest,
            bound.bound_expression_digest,
            (requirement.requirement_id,),
            signal.evidence_refs,
            "abi_width_readonly_producer_signal",
            session.identity.source_snapshot_fingerprint,
            signal.producer_id,
            session.identity.execution_identity_digest,
        )
        return CauseOccurrenceAuthority(occurrence, bound)

    def __call__(
        self, session: Any, signal: Any
    ) -> tuple[EventIntent, ...]:
        if type(signal) is AbiWidthReadonlySolverExecutionBatchSignal:
            return self._solver_batch_intents(session, signal)
        if self.has_observed(session, signal):
            return ()
        authority = self.authority_for_signal(session, signal)
        return (EventIntent(
            EventType.CAUSE_OBSERVED,
            CauseObservedEventAuthority(authority),
        ),)

    def has_observed(
        self, session: Any, signal: AbiWidthReadonlyBlockerSignal,
    ) -> bool:
        """Accept only byte-identical retransmission of one occurrence."""

        authority = self.authority_for_signal(session, signal)
        recorder = getattr(session, "recorder", None)
        if recorder is None or int(getattr(recorder, "event_count", 0)) == 0:
            return False
        occurrence_id = authority.occurrence.occurrence_id
        for event in recorder.prefix_view().events:
            if event.header.event_type is not EventType.CAUSE_OBSERVED:
                continue
            payload = event.authority_payload
            if (
                type(payload) is not CauseObservedEventAuthority
                or payload.occurrence_authority.occurrence.occurrence_id
                != occurrence_id
            ):
                continue
            if payload.occurrence_authority != authority:
                raise ValueError(
                    "ABI/width occurrence retransmission authority conflicts"
                )
            return True
        return False

    def build_execution_context(
        self, session: Any, blocker: AbiWidthReadonlyBlockerSignal,
        query: AbiWidthReadonlySolverQueryAuthority,
    ) -> AbiWidthReadonlySolverExecutionContext:
        if not self._enable_solver_execution:
            raise ValueError("ABI/width solver execution is not activated")
        authority = self.authority_for_signal(session, blocker)
        projection = session.preview_lifecycle_projection()
        rows = tuple(row for row in projection.q_open_base if (
            row.occurrence_id == authority.occurrence.occurrence_id
            and row.cause_id == authority.occurrence.cause_id.value
            and row.proof_kind == query.proof_kind
            and row.semantic_target_digest == query.semantic_target_digest
        ))
        if len(rows) != 1:
            raise ValueError("ABI/width query does not bind exactly one live Q")
        context = AbiWidthReadonlySolverExecutionContext(projection, rows[0])
        context.attempt_ordinals = session.domain_signal_state.setdefault(
            "abi_width_solver_attempt_ordinals", {}
        )
        context._attempt_lock = session.domain_signal_state.setdefault(
            "abi_width_solver_attempt_lock", threading.RLock()
        )
        return context

    def _solver_batch_intents(
        self, session: Any, batch: AbiWidthReadonlySolverExecutionBatchSignal
    ) -> tuple[EventIntent, ...]:
        if type(batch) is not AbiWidthReadonlySolverExecutionBatchSignal:
            raise TypeError("ABI/width solver encoder requires exact batch")
        authority = self.authority_for_signal(session, batch.blocker)
        requirement = authority.bound_contract.slot_bindings[0][1]
        assignment = batch.membership.requirement_assignment
        if (
            assignment.occurrence_id != authority.occurrence.occurrence_id
            or assignment.cause_id != authority.occurrence.cause_id.value
            or assignment.proof_requirement_id != requirement.requirement_id
        ):
            raise ValueError("ABI/width solver assignment differs from blocker")
        transaction_key = self._solver_batch_transaction_key(session, batch)
        transaction_digest = self._solver_batch_transaction_digest(session, batch)
        committed_entry = self._committed_solver_batch_entry(session, batch)
        if committed_entry is not None:
            committed_digest, _committed_intents_digest, committed_intents = (
                committed_entry
            )
            if committed_digest != transaction_digest:
                raise ValueError("ABI/width committed transaction identity conflicts")
            return committed_intents
        pending = session.domain_signal_state.get(
            "abi_width_pending_emission_transactions", {}
        )
        if type(pending) is not dict:
            raise TypeError("ABI/width pending emission ledger is not exact")
        existing = pending.get(transaction_key)
        if existing is not None:
            expected_digest, expected_intents, _expected_payload = existing
            if expected_digest != transaction_digest:
                raise ValueError(
                    "ABI/width emission transaction identity conflicts"
                )
            return expected_intents
        observations = []
        completions = []
        seen = session.domain_signal_state.setdefault(
            "abi_width_solver_execution_receipts", set()
        )
        fresh = tuple(
            receipt for receipt in batch.execution_receipts
            if receipt.receipt_digest not in seen
        )
        commit_payload = {
            "fresh_receipt_digests": tuple(
                receipt.receipt_digest for receipt in fresh
            ),
            "decisive_conflict": None,
            "model_artifacts": [],
            "sat_transformations": [],
        }
        sat_receipts = tuple(
            receipt for receipt in fresh if receipt.observed_status == "sat"
        )
        unsat_receipts = tuple(
            receipt for receipt in fresh if receipt.observed_status == "unsat"
        )
        decisive_conflict = bool(sat_receipts and unsat_receipts)
        if decisive_conflict:
            commit_payload["decisive_conflict"] = {
                "query_authority_digest": batch.query_authority.authority_digest,
                "sat_receipt_digests": tuple(sorted(
                    item.receipt_digest for item in sat_receipts
                )),
                "unsat_receipt_digests": tuple(sorted(
                    item.receipt_digest for item in unsat_receipts
                )),
            }
        selected_decisive_digest = None
        if not decisive_conflict:
            decisive = unsat_receipts or sat_receipts
            if decisive:
                selected_decisive_digest = min(
                    item.receipt_digest for item in decisive
                )
        for receipt in fresh:
            if receipt.observed_status in {"sat", "unsat"} and (
                receipt.receipt_digest != selected_decisive_digest
            ):
                continue
            if receipt.observed_status in {"unknown", "timeout", "error"}:
                observations.append(EventIntent(
                    {
                        "unknown": EventType.SOLVER_UNKNOWN,
                        "timeout": EventType.SOLVER_TIMEOUT,
                        "error": EventType.SOLVER_ERROR,
                    }[receipt.observed_status],
                    GenericReceiptBoundSolverExecutionEventAuthority(
                        requirement.requirement_id,
                        receipt.to_authority_dict(),
                        receipt.observed_status == "timeout",
                    ),
                ))
                continue
            if receipt.observed_status == "sat":
                if receipt.model_digest is None or receipt.model_authority is None:
                    raise ValueError("ABI/width SAT result lacks model authority")
                from scripts.function_tracer_pcode.authority.lifecycle.execution_authority import (
                    ModelBoundRelationalRefutationArtifact,
                    PINNED_RELATIONAL_WITNESS_VERIFIER,
                )
                from scripts.function_tracer_pcode.authority.lifecycle.production_signals import (
                    SatSafetyBlockerProductionSignal,
                )

                premise = {"assertions": batch.query_authority.premise_assertions}
                stage_input = {"declarations": batch.query_authority.declaration_rows}
                replay = PINNED_RELATIONAL_WITNESS_VERIFIER.issue(
                    receipt,
                    registry=ABI_WIDTH_READONLY_COMMON_EXECUTION_STAGE_REGISTRY,
                    membership=batch.membership,
                    obligation_id=batch.query_authority.obligation_id,
                    prepared_surface_digest=batch.query_authority.prepared_surface_digest,
                    observation_contract_id=batch.query_authority.observation_contract_id,
                    normalized_assertion=batch.query_authority.normalized_assertion_text,
                    premise=premise,
                    stage_input=stage_input,
                    model=receipt.model_authority,
                    configured_timeout_ms=receipt.configured_timeout_ms or 1000,
                    lifecycle_projection=batch.lifecycle_projection,
                )
                artifact = ModelBoundRelationalRefutationArtifact.create(
                    obligation_id=batch.query_authority.obligation_id,
                    source_snapshot_digests=batch.query_authority.source_snapshot_digests,
                    prepared_surface_digest=batch.query_authority.prepared_surface_digest,
                    observation_contract_id=batch.query_authority.observation_contract_id,
                    normalized_assertion=batch.query_authority.normalized_assertion_text,
                    premise=premise,
                    stage_input=stage_input,
                    applicability=replay.applicability_authority,
                    producer_version="abi-width-model-bound-refutation-v1",
                    encoding_version="abi-width-pair-value-replay-v1",
                    dependency_proof_ids=(receipt.receipt_digest,),
                    sat_execution_receipt=receipt,
                    replay_receipt=replay,
                    registry=ABI_WIDTH_READONLY_COMMON_EXECUTION_STAGE_REGISTRY,
                    membership=batch.membership,
                )
                artifact.validate(
                    PINNED_RELATIONAL_WITNESS_VERIFIER,
                    ABI_WIDTH_READONLY_COMMON_EXECUTION_STAGE_REGISTRY,
                    batch.membership,
                )
                commit_payload["model_artifacts"].append(artifact)
                handoff = SatSafetyBlockerProductionSignal(
                    "OBSERVED",
                    "counterexample_analysis_safety_unproven",
                    (
                        "abi_width_model_bound_refutation",
                        artifact.obligation_id,
                        artifact.source_snapshot_digests,
                        artifact.prepared_surface_digest,
                    ),
                    (
                        "model_bound_refutation_requires_counterexample_safety",
                        artifact.artifact_digest,
                    ),
                    (
                        artifact.artifact_digest,
                        receipt.receipt_digest,
                        replay.replay_receipt_digest,
                    ),
                    "abi-width-model-bound-refutation-handoff-v1",
                )
                prepare = getattr(
                    session.domain_signal_encoder,
                    "prepare_sat_safety_transformation",
                    None,
                )
                commit = getattr(
                    session.domain_signal_encoder,
                    "commit_sat_safety_transformed_observation",
                    None,
                )
                if not callable(prepare) or not callable(commit):
                    raise ValueError(
                        "ABI/width SAT lacks atomic counterexample-safety route"
                    )
                replacement_authority = prepare(session, handoff)
                if type(replacement_authority) is not CauseOccurrenceAuthority:
                    raise TypeError("SAT safety replacement authority is not exact")
                old_occurrence = authority.occurrence
                new_occurrence = replacement_authority.occurrence
                transformation_receipt_id = authority_digest({
                    "transformation_kind": "high_bit_sat_to_counterexample_safety_v1",
                    "result_occurrence_id": session.identity.result_occurrence_id,
                    "old_occurrence_id": old_occurrence.occurrence_id,
                    "old_requirement_id": requirement.requirement_id,
                    "new_occurrence_id": new_occurrence.occurrence_id,
                    "new_requirement_ids": new_occurrence.proof_requirement_ids,
                    "query_authority_digest": batch.query_authority.authority_digest,
                    "execution_receipt_digest": receipt.receipt_digest,
                    "model_refutation_artifact_digest": artifact.artifact_digest,
                    "replay_receipt_digest": replay.replay_receipt_digest,
                })
                transformation = CauseTransformationEvent(
                    TransformationKind.REPLACEMENT,
                    (old_occurrence.occurrence_id,),
                    (new_occurrence.occurrence_id,),
                    transformation_receipt_id,
                    "abi-width-high-bit-sat-safety-v1",
                    session.identity.source_snapshot_fingerprint,
                )
                proof = CauseTransformationProofReceipt(
                    transformation_receipt_id,
                    ((old_occurrence.occurrence_id, old_occurrence.cause_id.value),),
                    ((new_occurrence.occurrence_id, new_occurrence.cause_id.value),),
                    (),
                    session.identity.source_snapshot_fingerprint,
                    False,
                )
                transformed_intents = (
                    EventIntent(
                        EventType.CAUSE_OBSERVED,
                        CauseObservedEventAuthority(replacement_authority),
                    ),
                    EventIntent(
                        EventType.CAUSE_TRANSFORMED,
                        CauseTransformedEventAuthority(transformation, proof),
                    ),
                )
                commit_payload["sat_transformations"].append(
                    (transformation, proof, artifact, handoff)
                )
                observations.extend(transformed_intents)
                continue
            if receipt.observed_status != "unsat":
                raise ValueError("ABI/width solver status is not sealed")
            if batch.query_authority.proof_kind == "return_high_bit_relation":
                artifact = ReturnHighBitRelationProofArtifact.from_solver_unsat(
                    batch.blocker,
                    batch.proof_seed,
                    batch.dependency_artifacts[0],
                    query_authority=batch.query_authority,
                    membership=batch.membership,
                    execution_receipt=receipt,
                    lifecycle_projection=batch.lifecycle_projection,
                    source_snapshot_fingerprint=(
                        session.identity.source_snapshot_fingerprint
                    ),
                )
                completions.append(self.complete_return_high_bit_relation(
                    session, batch.blocker, artifact
                ))
            else:
                artifact = ReadonlyObjectCorrespondenceArtifact.from_solver_unsat(
                    batch.blocker,
                    batch.proof_seed,
                    query_authority=batch.query_authority,
                    membership=batch.membership,
                    execution_receipt=receipt,
                    lifecycle_projection=batch.lifecycle_projection,
                    source_snapshot_fingerprint=(
                        session.identity.source_snapshot_fingerprint
                    ),
                )
                completions.append(self.complete_readonly_object_correspondence(
                    session, batch.blocker, artifact
                ))
        intents = tuple((*observations, *completions))
        return self._register_solver_batch_transaction(
            session, batch, intents, commit_payload
        )

    @staticmethod
    def _solver_batch_transaction_key(
        session: Any, batch: AbiWidthReadonlySolverExecutionBatchSignal,
    ) -> tuple[str, tuple[str, int], str]:
        membership = batch.membership
        return (
            session.identity.result_occurrence_id,
            (
                membership.attempt_group_identity,
                membership.attempt_ordinal,
            ),
            batch.query_authority.authority_digest,
        )

    @classmethod
    def _solver_batch_transaction_digest(
        cls, session: Any, batch: AbiWidthReadonlySolverExecutionBatchSignal,
    ) -> str:
        membership = batch.membership
        return authority_digest({
            "transaction_key": cls._solver_batch_transaction_key(session, batch),
            "attempt_group_identity": membership.attempt_group_identity,
            "attempt_ordinal": membership.attempt_ordinal,
            "proof_requirement_id": membership.proof_requirement_id,
            "receipt_digests": tuple(
                receipt.receipt_digest for receipt in batch.execution_receipts
            ),
        })

    @classmethod
    def _register_solver_batch_transaction(
        cls, session: Any,
        batch: AbiWidthReadonlySolverExecutionBatchSignal,
        intents: tuple[EventIntent, ...],
        payload: Mapping[str, Any],
    ) -> tuple[EventIntent, ...]:
        """Register one semantic batch, returning the existing plan on replay."""

        transaction_key = cls._solver_batch_transaction_key(session, batch)
        transaction_digest = cls._solver_batch_transaction_digest(session, batch)
        pending = session.domain_signal_state.setdefault(
            "abi_width_pending_emission_transactions", {}
        )
        if type(pending) is not dict:
            raise TypeError("ABI/width pending emission ledger is not exact")
        existing = pending.get(transaction_key)
        if existing is not None:
            expected_digest, expected_intents, _expected_payload = existing
            if expected_digest != transaction_digest:
                raise ValueError(
                    "ABI/width emission transaction identity conflicts"
                )
            if tuple(intents) != expected_intents:
                raise ValueError(
                    "ABI/width emission transaction intents changed"
                )
            return expected_intents
        pending[transaction_key] = (
            transaction_digest, tuple(intents), dict(payload)
        )
        return tuple(intents)

    @classmethod
    def _committed_solver_batch_entry(
        cls, session: Any,
        batch: AbiWidthReadonlySolverExecutionBatchSignal,
    ) -> tuple[str, str, tuple[EventIntent, ...]] | None:
        committed = session.domain_signal_state.get(
            "abi_width_committed_emission_transactions", {}
        )
        if type(committed) is not dict:
            raise TypeError("ABI/width committed emission ledger is not exact")
        entry = committed.get(cls._solver_batch_transaction_key(session, batch))
        if entry is None:
            return None
        if type(entry) is not tuple or len(entry) != 3:
            raise TypeError("ABI/width committed emission transaction is not exact")
        if type(entry[2]) is not tuple or any(
            type(intent) is not EventIntent for intent in entry[2]
        ):
            raise TypeError("ABI/width committed transaction intents are not exact")
        return entry

    def is_committed_signal_replay(
        self, session: Any, signal: Any,
        intents: tuple[EventIntent, ...] = (),
    ) -> bool:
        """Return true only for the exact already-committed solver batch."""

        if type(signal) is not AbiWidthReadonlySolverExecutionBatchSignal:
            return False
        committed_entry = self._committed_solver_batch_entry(session, signal)
        if committed_entry is None:
            return False
        committed_digest, committed_intents_digest, _committed_intents = committed_entry
        if committed_digest != self._solver_batch_transaction_digest(session, signal):
            raise ValueError("ABI/width committed transaction identity conflicts")
        if authority_digest(tuple(intents)) != committed_intents_digest:
            raise ValueError("ABI/width committed transaction intents changed")
        return True

    def commit_emitted_signal(
        self, session: Any, signal: Any, intents: tuple[EventIntent, ...]
    ) -> None:
        if type(signal) is not AbiWidthReadonlySolverExecutionBatchSignal:
            return
        pending = session.domain_signal_state.setdefault(
            "abi_width_pending_emission_transactions", {}
        )
        transaction_key = self._solver_batch_transaction_key(session, signal)
        transaction_digest = self._solver_batch_transaction_digest(session, signal)
        try:
            expected_digest, expected_intents, payload = pending[transaction_key]
        except KeyError as exc:
            committed_entry = self._committed_solver_batch_entry(session, signal)
            if committed_entry is not None:
                committed_digest, committed_intents_digest, _committed_intents = (
                    committed_entry
                )
                if committed_digest != transaction_digest:
                    raise ValueError(
                        "ABI/width committed transaction identity conflicts"
                    )
                if authority_digest(tuple(intents)) != committed_intents_digest:
                    raise ValueError(
                        "ABI/width committed transaction intents changed"
                    )
                return
            raise ValueError("ABI/width emission transaction is missing") from exc
        if expected_digest != transaction_digest:
            raise ValueError("ABI/width emission transaction identity changed")
        if tuple(intents) != expected_intents:
            raise ValueError("ABI/width emission transaction intents changed")
        state = session.domain_signal_state
        rollbacks = state.setdefault(_ABI_COMMITTED_ROLLBACK_SNAPSHOTS_KEY, {})
        if type(rollbacks) is not dict:
            raise TypeError("ABI/width committed rollback ledger is not exact")
        if transaction_key in rollbacks:
            # 同じ取引の前の commit がまだ終わっていない（写しを上書きすれば戻せなくなる）。
            raise ValueError("ABI/width transaction already owns a committed rollback")
        mutated_keys = (
            "abi_width_solver_execution_receipts",
            "abi_width_solver_decisive_conflicts",
            "abi_width_model_bound_refutation_artifacts",
            # 変換した SAT-safety の観測の公開は、SAT-safety の台帳の全ての key を変え得る。
            *SAT_SAFETY_LEDGER_KEYS,
            "sat_safety_pending_emission_transactions",
            "abi_width_high_bit_sat_transformations",
            "abi_width_committed_emission_transactions",
        )
        snapshots = {}
        for key in mutated_keys:
            if key not in state:
                snapshots[key] = (False, None)
            elif type(state[key]) is set:
                snapshots[key] = (True, set(state[key]))
            elif type(state[key]) is list:
                snapshots[key] = (True, list(state[key]))
            elif type(state[key]) is dict:
                snapshots[key] = (True, dict(state[key]))
            else:
                raise TypeError(
                    f"ABI/width transaction ledger has invalid type: {key}"
                )
        try:
            state.setdefault(
                "abi_width_solver_execution_receipts", set()
            ).update(payload["fresh_receipt_digests"])
            conflict = payload["decisive_conflict"]
            if conflict is not None:
                state.setdefault(
                    "abi_width_solver_decisive_conflicts", []
                ).append(conflict)
            if payload["model_artifacts"]:
                state.setdefault(
                    "abi_width_model_bound_refutation_artifacts", []
                ).extend(payload["model_artifacts"])
            commit = getattr(
                session.domain_signal_encoder,
                "commit_sat_safety_transformed_observation", None,
            )
            if payload["sat_transformations"] and not callable(commit):
                raise ValueError("ABI/width SAT safety commit route disappeared")
            for transformation, proof, artifact, handoff in payload[
                "sat_transformations"
            ]:
                commit(session, handoff)
                state.setdefault(
                    "abi_width_high_bit_sat_transformations", []
                ).append((transformation, proof, artifact, handoff))
            committed = state.setdefault(
                "abi_width_committed_emission_transactions", {}
            )
            if type(committed) is not dict:
                raise TypeError("ABI/width committed emission ledger is not exact")
            committed[transaction_key] = (
                transaction_digest,
                authority_digest(tuple(intents)),
                tuple(intents),
            )
        except Exception:
            _restore_abi_transaction_snapshots(state, snapshots)
            raise
        # この commit の後で同じ取引の別の commit（Phase 7 など）が失敗すると、呼び手は
        # ``rollback_emitted_signal`` を呼ぶ。そのとき ABI と SAT-safety の全ての台帳を
        # 取引の前へ戻せるよう、写しをこの取引の分として取引の終わりまで残す。写しを
        # 捨てるのはこの取引の終わり（``rollback_emitted_signal`` か
        # ``finish_emitted_signal``）だけ。取引は session の取引の境界の中で始まって終わり、
        # 取引が生きている間は別の取引が始まらない（producer の取引の境界）ので、写しの
        # 時点からの変化はこの取引のものだけ。
        rollbacks[transaction_key] = snapshots
        pending.pop(transaction_key)

    def finish_emitted_signal(self, session: Any, signal: Any) -> None:
        """この取引の公開は確定した: この取引の巻き戻し用の写しを捨てる。"""
        if type(signal) is not AbiWidthReadonlySolverExecutionBatchSignal:
            return
        self._pop_committed_rollback(session, signal)

    def _pop_committed_rollback(self, session: Any, signal: Any) -> Any:
        rollbacks = session.domain_signal_state.get(_ABI_COMMITTED_ROLLBACK_SNAPSHOTS_KEY)
        if rollbacks is None:
            return None
        if type(rollbacks) is not dict:
            raise TypeError("ABI/width committed rollback ledger is not exact")
        snapshots = rollbacks.pop(self._solver_batch_transaction_key(session, signal), None)
        if not rollbacks:
            session.domain_signal_state.pop(_ABI_COMMITTED_ROLLBACK_SNAPSHOTS_KEY, None)
        return snapshots

    def rollback_emitted_signal(self, session: Any, signal: Any) -> None:
        if type(signal) is AbiWidthReadonlySolverExecutionBatchSignal:
            pending = session.domain_signal_state.setdefault(
                "abi_width_pending_emission_transactions", {}
            )
            transaction_key = self._solver_batch_transaction_key(session, signal)
            pending.pop(transaction_key, None)
            snapshots = self._pop_committed_rollback(session, signal)
            if snapshots is not None:
                # commit の後でこの取引が失敗した: ABI と SAT-safety の台帳を取引の前へ戻す。
                _restore_abi_transaction_snapshots(session.domain_signal_state, snapshots)
                return
            committed = session.domain_signal_state.get(
                "abi_width_committed_emission_transactions", {}
            )
            if type(committed) is not dict:
                raise TypeError("ABI/width committed emission ledger is not exact")
            committed_entry = committed.get(transaction_key)
            if committed_entry is not None:
                if committed_entry[0] != self._solver_batch_transaction_digest(
                    session, signal
                ):
                    raise ValueError(
                        "ABI/width committed transaction identity conflicts during rollback"
                    )
                committed.pop(transaction_key, None)

    def _completion_intent(
        self,
        session: Any,
        blocker: AbiWidthReadonlyBlockerSignal,
        artifact: _AbiWidthReadonlyCompletionArtifact,
        expected_type: type[_AbiWidthReadonlyCompletionArtifact],
    ) -> EventIntent:
        if type(artifact) is not expected_type or artifact.reason_id != blocker.reason_id:
            raise TypeError("completion entrypoint requires its exact artifact and blocker")
        authority = self.authority_for_signal(session, blocker)
        occurrence = authority.occurrence
        if artifact.semantic_target_digest != authority_digest(blocker.canonical_target_key):
            raise ValueError("completion artifact semantic target differs from C authority")
        if artifact.source_snapshot_digest != session.identity.source_snapshot_fingerprint:
            raise ValueError("completion artifact source snapshot differs from live result")
        if artifact.registry_digest != ABI_WIDTH_READONLY_PRODUCER_STAGE_REGISTRY_DIGEST:
            raise ValueError("completion artifact uses another sealed registry")
        if int(getattr(session.recorder, "event_count", 0)) == 0:
            raise ValueError(
                "completion artifact does not bind one live C_active row: "
                f"reason={blocker.reason_id}, occurrence={occurrence.occurrence_id}, "
                "event_count=0"
            )
        projection = session.preview_lifecycle_projection()
        active_rows = tuple(row for row in projection.c_active_base if (
            row.occurrence_id == occurrence.occurrence_id
            and row.cause_id == occurrence.cause_id.value
            and row.reason_id == blocker.reason_id
        ))
        if len(active_rows) != 1:
            raise ValueError(
                "completion artifact does not bind one live C_active row: "
                f"reason={blocker.reason_id}, occurrence={occurrence.occurrence_id}, "
                f"matching_rows={len(active_rows)}"
            )
        if authority.bound_contract is None or len(authority.bound_contract.slot_bindings) != 1:
            raise ValueError("completion authority does not own one atomic Q")
        requirement = authority.bound_contract.slot_bindings[0][1]
        q_rows = tuple(row for row in projection.q_open_base if (
            row.occurrence_id == occurrence.occurrence_id
            and row.cause_id == occurrence.cause_id.value
            and row.proof_requirement_id == requirement.requirement_id
            and row.proof_kind == artifact.proof_kind
        ))
        if len(q_rows) != 1:
            raise ValueError("completion artifact does not bind one live Q_open row")
        applicability = authority_digest({
            "result_occurrence_id": session.identity.result_occurrence_id,
            "occurrence_id": occurrence.occurrence_id,
            "cause_id": occurrence.cause_id.value,
            "reason_id": blocker.reason_id,
            "proof_requirement_id": requirement.requirement_id,
            "proof_kind": artifact.proof_kind,
            "semantic_target_digest": artifact.semantic_target_digest,
            "source_seed_digest": artifact.source_seed_digest,
            "source_snapshot_digest": artifact.source_snapshot_digest,
            "prepared_snapshot_digest": artifact.prepared_snapshot_digest,
            "c_active_base_digest": authority_digest(projection.c_active_base),
            "q_open_base_digest": projection.q_open_base_digest,
            "lifecycle_prefix_projection_digest": projection.prefix_projection_digest,
            "registry_digest": artifact.registry_digest,
            "common_registry_digest": artifact.common_registry_digest,
            "artifact_digest": artifact.artifact_digest,
        })
        receipt = RequirementCompletionReceipt(
            occurrence.cause_id.value,
            occurrence.occurrence_id,
            requirement.requirement_id,
            authority.bound_contract.contract_definition_id,
            authority.bound_contract.contract_version,
            authority.bound_contract.bound_expression_digest,
            artifact.artifact_digest,
            applicability,
        )
        receipt.validate_against(
            occurrence, authority.bound_contract, (requirement.requirement_id,)
        )
        session.domain_signal_state.setdefault(
            "abi_width_readonly_completion_candidates", []
        ).append((blocker, artifact, receipt))
        return EventIntent(
            EventType.REQUIREMENT_COMPLETED,
            RequirementCompletedEventAuthority(receipt),
        )

    def complete_return_abi_provenance(self, session, blocker, artifact):
        return self._completion_intent(session, blocker, artifact, ReturnAbiProvenanceArtifact)

    def register_void_effect_only_return_abi_seed(self, session: Any, seed: Any) -> None:
        """Remember an exact void effect-only ABI seed for structural closure."""
        if type(seed) is not FunctionReturnAbiSeed or not seed.void_effect_only_surface:
            raise TypeError("void effect-only ABI plan requires an eligible exact seed")
        pending = session.domain_signal_state.setdefault(
            "void_effect_only_return_abi_seeds", {}
        )
        existing = pending.setdefault(seed.seed_digest, seed)
        if existing != seed:
            raise ValueError("void effect-only ABI plan drifted")

    def _complete_registered_void_effect_only_return_abi(self, session: Any) -> None:
        plans = session.domain_signal_state.get("void_effect_only_return_abi_seeds", {})
        completed = session.domain_signal_state.setdefault(
            "void_effect_only_return_abi_completed", set()
        )
        for seed_digest, seed in tuple(sorted(plans.items())):
            if seed_digest in completed:
                continue
            blocker = AbiWidthReadonlyBlockerSignal.from_return_abi_seed(
                seed, "return_storage_descriptor"
            )
            artifact = ReturnAbiProvenanceArtifact.from_void_effect_surface(
                blocker,
                seed,
                source_snapshot_fingerprint=session.identity.source_snapshot_fingerprint,
            )
            session.emit(self.complete_return_abi_provenance(session, blocker, artifact))
            completed.add(seed_digest)

    def complete_return_observation_contract(self, session, blocker, artifact):
        return self._completion_intent(session, blocker, artifact, ReturnObservationContractArtifact)

    def complete_return_abi_relation(self, session, blocker, artifact):
        return self._completion_intent(session, blocker, artifact, ReturnAbiRelationArtifact)

    def complete_return_high_bit_relation(self, session, blocker, artifact):
        return self._completion_intent(session, blocker, artifact, ReturnHighBitRelationProofArtifact)

    def complete_readonly_object_correspondence(self, session, blocker, artifact):
        return self._completion_intent(session, blocker, artifact, ReadonlyObjectCorrespondenceArtifact)

    def register_readonly_promotion(
        self, session: Any, seed: ReadonlyReductionObjectSetSeed
    ) -> None:
        if type(seed) is not ReadonlyReductionObjectSetSeed:
            raise TypeError("readonly promotion requires exact base seed")
        pending = session.domain_signal_state.setdefault(
            "abi_width_readonly_pending_promotions", {}
        )
        pending.setdefault(seed.seed_digest, seed)

    def register_solver_candidate(
        self, session: Any, blocker: AbiWidthReadonlyBlockerSignal, seed: Any
    ) -> None:
        if blocker.reason_id == "return_high_bit_relation_unproven":
            if (
                type(seed) is not ReturnObservationProjectionSeed
                or blocker != AbiWidthReadonlyBlockerSignal.from_projection_seed(
                    blocker.reason_id, seed
                )
            ):
                raise TypeError("high-bit scheduler requires exact projection seed")
        elif blocker.reason_id == "readonly_object_correspondence_unproven":
            if (
                type(seed) is not ResolvedReadonlyObjectSetSeed
                or blocker != AbiWidthReadonlyBlockerSignal.from_readonly_object_sets(
                    seed
                )
            ):
                raise TypeError("readonly scheduler requires exact resolved seed")
        else:
            raise ValueError("ABI/width scheduler candidate proof kind is not solver-capable")
        session.domain_signal_state.setdefault(
            "abi_width_pending_solver_candidates", {}
        ).setdefault((blocker.reason_id, seed.seed_digest), (blocker, seed))

    def register_return_observation_proof_plan(
        self,
        session: Any,
        projection_seed: ReturnObservationProjectionSeed,
        assessment: "ReturnAbiProductionAssessment",
    ) -> None:
        if (
            type(projection_seed) is not ReturnObservationProjectionSeed
            or type(assessment) is not ReturnAbiProductionAssessment
            or assessment.relation_assessment is None
            or assessment.relation_assessment.projection_seed_digest
            != projection_seed.seed_digest
        ):
            raise TypeError("return-observation proof plan authority is invalid")
        pending = session.domain_signal_state.setdefault(
            "return_observation_proof_plans", {}
        )
        existing = pending.setdefault(
            projection_seed.seed_digest, (projection_seed, assessment)
        )
        if existing != (projection_seed, assessment):
            raise ValueError("return-observation proof plan drifted")

    def _complete_registered_return_abi_relations(self, session: Any) -> None:
        plans = session.domain_signal_state.get("return_observation_proof_plans", {})
        completed = session.domain_signal_state.setdefault(
            "return_observation_abi_relation_completed", set()
        )
        for seed_digest, (seed, assessment) in tuple(sorted(plans.items())):
            if seed_digest in completed:
                continue
            relation = assessment.relation_assessment
            if relation.status is not ReturnAbiRelationStatus.PROVED:
                continue
            blocker = AbiWidthReadonlyBlockerSignal.from_projection_seed(
                "return_abi_relation_unproven", seed
            )
            artifact = ReturnAbiRelationArtifact.from_assessment(
                blocker,
                seed,
                relation,
                assessment.left_seed,
                assessment.right_seed,
                source_snapshot_fingerprint=(
                    session.identity.source_snapshot_fingerprint
                ),
            )
            session.emit(self.complete_return_abi_relation(
                session, blocker, artifact
            ))
            completed.add(seed_digest)

    def _complete_registered_observation_contracts(self, session: Any) -> None:
        plans = session.domain_signal_state.get("return_observation_proof_plans", {})
        candidates = tuple(session.domain_signal_state.get(
            "abi_width_readonly_completion_candidates", ()
        ))
        completed = session.domain_signal_state.setdefault(
            "return_observation_contract_completed", set()
        )
        for seed_digest, (seed, _assessment) in tuple(sorted(plans.items())):
            if seed_digest in completed:
                continue
            high_bit_rows = tuple(
                row for row in candidates
                if type(row[1]) is ReturnHighBitRelationProofArtifact
                and row[1].source_seed_digest == seed.seed_digest
            )
            if len(high_bit_rows) != 1:
                continue
            high_bit_artifact = high_bit_rows[0][1]
            blocker = AbiWidthReadonlyBlockerSignal.from_projection_seed(
                "return_observation_contract_unproven", seed
            )
            artifact = ReturnObservationContractArtifact.from_projection_seed(
                blocker,
                seed,
                derivation=seed.derivation,
                projection_policy="abi_extension",
                source_snapshot_fingerprint=(
                    session.identity.source_snapshot_fingerprint
                ),
                high_bit_dependency=high_bit_artifact,
            )
            session.emit(self.complete_return_observation_contract(
                session, blocker, artifact
            ))
            completed.add(seed_digest)

    def finalize_derived_promotions(self, session: Any) -> None:
        pending = session.domain_signal_state.get(
            "abi_width_readonly_pending_promotions", {}
        )
        completed = session.domain_signal_state.get(
            "abi_width_readonly_completed_promotions", set()
        )
        candidates = tuple(session.domain_signal_state.get(
            "abi_width_readonly_completion_candidates", ()
        ))
        changed = True
        while changed:
            changed = False
            for digest, seed in tuple(sorted(pending.items())):
                if digest in completed:
                    continue
                dependencies = tuple(
                    row for row in candidates
                    if type(row[1]) is ReadonlyStorageIdentityArtifact
                    and row[1].source_seed_digest == seed.seed_digest
                )
                expected_count = (
                    len(seed.left_unresolved_member_indices)
                    + len(seed.right_unresolved_member_indices)
                )
                if len(dependencies) != expected_count:
                    continue
                resolved = ResolvedReadonlyObjectSetSeed.from_live_completion_closure(
                    session, seed, dependencies
                )
                signal = AbiWidthReadonlyBlockerSignal.from_readonly_object_sets(
                    resolved
                )
                session.emit_domain_signal(signal)
                session.domain_signal_state.setdefault(
                    "abi_width_readonly_resolved_readonly_seeds", {}
                )[resolved.seed_digest] = resolved
                self.register_solver_candidate(session, signal, resolved)
                completed.add(digest)
                changed = True
        session.domain_signal_state[
            "abi_width_readonly_completed_promotions"
        ] = completed

    def _execute_pending_solver_queries(self, session: Any) -> None:
        if not self._enable_solver_execution:
            return
        from scripts.function_tracer_pcode.authority.lifecycle.execution_authority import (
            PINNED_SOLVER_EXECUTION_ISSUER,
        )
        from scripts.function_tracer_pcode.authority.lifecycle.production_signals import (
            SatSafetyBlockerProductionSignal,
        )

        pending = session.domain_signal_state.get(
            "abi_width_pending_solver_candidates", {}
        )
        attempted = session.domain_signal_state.setdefault(
            "abi_width_scheduled_semantic_queries", set()
        )
        completions = tuple(session.domain_signal_state.get(
            "abi_width_readonly_completion_candidates", ()
        ))
        for _key, (blocker, seed) in tuple(sorted(pending.items())):
            if blocker.reason_id == "return_high_bit_relation_unproven":
                dependencies = tuple(
                    row for row in completions
                    if type(row[1]) is ReturnAbiRelationArtifact
                    and row[1].source_seed_digest == seed.seed_digest
                )
                if len(dependencies) != 1:
                    continue
                dependency_blocker, dependency_artifact, dependency_receipt = (
                    dependencies[0]
                )
                try:
                    query = AbiWidthReadonlySolverQueryAuthority.from_high_bit_theorem(
                        session, blocker, seed,
                        (
                            dependency_blocker, dependency_artifact,
                            dependency_receipt,
                        ),
                    )
                except ValueError:
                    continue
                dependency_artifacts = (dependency_artifact,)
            else:
                try:
                    query = (
                        AbiWidthReadonlySolverQueryAuthority
                        .from_readonly_correspondence_theorem(
                            session, blocker, seed
                        )
                    )
                except ProjectionNotFormable:
                    continue
                dependency_artifacts = ()
            if query.authority_digest in attempted:
                continue
            first_invocation_ordinal = int(session.domain_signal_state.get(
                "abi_width_next_invocation_ordinal", 1
            ))
            receipts = None
            membership = None
            context = None
            for scheduler_retry in range(2):
                context = self.build_execution_context(session, blocker, query)
                membership = context.membership_for(query)
                try:
                    receipts = PINNED_SOLVER_EXECUTION_ISSUER.execute(
                        registry=ABI_WIDTH_READONLY_COMMON_EXECUTION_STAGE_REGISTRY,
                        result_occurrence_id=session.identity.result_occurrence_id,
                        membership=membership,
                        invocation_identity=(
                            session.identity.result_occurrence_id + ":"
                            + query.obligation_id + ":" + query.proof_stage
                        ),
                        first_invocation_ordinal=first_invocation_ordinal,
                        query=query.query_text,
                        configured_timeout_ms=self._solver_timeout_ms,
                        query_authority=query,
                        lifecycle_projection=context.lifecycle_projection,
                    )
                except Exception as exc:
                    session.domain_signal_state.setdefault(
                        "abi_width_solver_scheduler_failures", []
                    ).append((
                        query.authority_digest, scheduler_retry + 1,
                        type(exc).__name__, str(exc),
                    ))
                    first_invocation_ordinal += 1
                    session.domain_signal_state[
                        "abi_width_next_invocation_ordinal"
                    ] = first_invocation_ordinal
                    continue
                break
            attempted.add(query.authority_digest)
            if receipts is None:
                continue
            session.domain_signal_state["abi_width_next_invocation_ordinal"] = (
                max(receipt.invocation_ordinal for receipt in receipts) + 1
            )
            batch = AbiWidthReadonlySolverExecutionBatchSignal.from_issuer_results(
                blocker, query, seed, dependency_artifacts,
                membership, receipts, context.lifecycle_projection,
            )
            # This is an issuer-derived execution receipt batch, not a fresh
            # source producer activation.  Encode it at the owning domain
            # boundary so Phase 7 does not require a fabricated source site,
            # while preserving the same atomic producer-state transaction as
            # ProductionDualWritePilotSession.emit_domain_signal().
            self._emit_solver_batch_transaction(session, batch)
            handoffs = tuple(session.domain_signal_state.pop(
                "abi_width_sat_safety_handoffs", ()
            ))
            if handoffs:
                accepts = getattr(
                    session.domain_signal_encoder, "accepts_signal_type", None
                )
                if not callable(accepts) or not accepts(
                    SatSafetyBlockerProductionSignal
                ):
                    raise ValueError(
                        "ABI/width scheduled SAT lacks counterexample-safety route"
                    )
                for handoff in handoffs:
                    session.emit_domain_signal(handoff)

    def _emit_solver_batch_transaction(self, session: Any, batch: Any) -> None:
        """solver の batch を 1 つの producer の取引（attempt）として encode し公開する。

        境界は session の ``run_signal_transaction``: encoding が予約した取引、commit の後で
        同じ取引の Phase 7 の commit などが失敗したら ``rollback_emitted_signal`` が commit の
        写しから全ての台帳を戻し、公開できたら ``finish_emitted_signal`` がこの取引の写しを
        捨てる。例外はそのまま上げる。
        """
        session.run_signal_transaction(
            batch,
            lambda: self._solver_batch_intents(session, batch),
            lambda intents: self.commit_emitted_signal(session, batch, intents),
            lambda: self.rollback_emitted_signal(session, batch),
            finish=lambda: self.finish_emitted_signal(session, batch),
            replay_aware=True,
        )

    def finalize_open_execution_history(self, session: Any) -> None:
        from scripts.function_tracer_pcode.authority.lifecycle.execution_authority import (
            PINNED_SOLVER_EXECUTION_ISSUER,
        )

        self.finalize_derived_promotions(session)
        self._complete_registered_void_effect_only_return_abi(session)
        self._complete_registered_return_abi_relations(session)
        self._execute_pending_solver_queries(session)
        self._complete_registered_observation_contracts(session)
        result_id = session.identity.result_occurrence_id
        if PINNED_SOLVER_EXECUTION_ISSUER.has_open_result_ledger(
            ABI_WIDTH_READONLY_COMMON_EXECUTION_STAGE_REGISTRY, result_id
        ):
            census = PINNED_SOLVER_EXECUTION_ISSUER.seal_result_census(
                ABI_WIDTH_READONLY_COMMON_EXECUTION_STAGE_REGISTRY, result_id
            )
            seen = session.domain_signal_state.setdefault(
                "abi_width_solver_execution_receipts", set()
            )
            for event in census.events:
                receipt = event.execution_receipt
                if receipt is None:
                    continue
                if receipt.observed_status not in {"unknown", "timeout", "error"}:
                    continue
                if receipt.receipt_digest in seen:
                    continue
                session.emit(EventIntent(
                    {
                        "unknown": EventType.SOLVER_UNKNOWN,
                        "timeout": EventType.SOLVER_TIMEOUT,
                        "error": EventType.SOLVER_ERROR,
                    }[receipt.observed_status],
                    GenericReceiptBoundSolverExecutionEventAuthority(
                        receipt.proof_requirement_id,
                        receipt.to_authority_dict(),
                        receipt.observed_status == "timeout",
                    ),
                ))
                seen.add(receipt.receipt_digest)
            session.domain_signal_state["abi_width_solver_census"] = census

    def finalize_terminal_timeout_bindings(
        self, session: Any, stream: Any
    ) -> tuple[tuple[int, str], ...]:
        from scripts.function_tracer_pcode.authority.lifecycle.execution_authority import (
            ExecutionAuthorityStartupReceipt,
            SolverExecutionEvidenceBundle,
            TerminalLifecycleProjectionAuthority,
            TerminalTimeoutSelectionReceipt,
        )

        census = session.domain_signal_state.get("abi_width_solver_census")
        if census is None:
            return ()
        projection = session.reducer.replay(stream).projection
        terminal_projection = TerminalLifecycleProjectionAuthority.create(
            session.identity.result_occurrence_id,
            (row.proof_requirement_id for row in projection.q_open_base),
        )
        selection = TerminalTimeoutSelectionReceipt.select(
            ABI_WIDTH_READONLY_COMMON_EXECUTION_STAGE_REGISTRY,
            census,
            terminal_projection,
        )
        startup = tuple(getattr(session, "startup_receipts", ()))
        if len(startup) != 1 or type(startup[0]) is not ExecutionAuthorityStartupReceipt:
            raise ValueError("ABI/width solver evidence lacks one startup receipt")
        observed = tuple(
            event.authority_payload.execution_receipt_digest
            for event in stream.events
            if type(event.authority_payload)
            is GenericReceiptBoundSolverExecutionEventAuthority
        )
        bundle = SolverExecutionEvidenceBundle.seal(
            registry=ABI_WIDTH_READONLY_COMMON_EXECUTION_STAGE_REGISTRY,
            startup_receipt=startup[0],
            census=census,
            terminal_projection=terminal_projection,
            terminal_selection=selection,
            final_lifecycle_projection_digest=projection.lifecycle_projection_digest,
            observed_stream_receipt_digests=observed,
        )
        session.domain_signal_state["abi_width_terminal_timeout_selection"] = selection
        session.execution_authority_evidence_bundles.append((
            ABI_WIDTH_READONLY_COMMON_EXECUTION_STAGE_REGISTRY, bundle
        ))
        if selection is None:
            return ()
        matches = tuple(
            event for event in stream.events
            if type(event.authority_payload)
            is GenericReceiptBoundSolverExecutionEventAuthority
            and event.authority_payload.execution_receipt_digest
            == selection.execution_receipt_digest
            and event.authority_payload.proof_requirement_id
            == selection.proof_requirement_id
        )
        if len(matches) != 1:
            raise ValueError("ABI/width terminal timeout lacks one stream event")
        return ((matches[0].header.sequence_number, selection.proof_requirement_id),)


def summary_abi_width_signals_from_acceptance(
    analysis: Any, acceptance_result: Any
) -> tuple[AbiWidthReadonlyBlockerSignal, ...]:
    """Expand only the exact summary occurrences deferred from slice4."""

    from scripts.function_tracer_pcode.analysis.returns.summary_returns import (
        SummaryReturnAcceptanceResult,
    )

    if type(acceptance_result) is not SummaryReturnAcceptanceResult:
        raise TypeError("slice5 summary expansion requires exact acceptance result")
    signals = []
    for occurrence in acceptance_result.blocker_occurrences:
        classification = classify_summary_width_source(occurrence.source_code)
        if classification.disposition is AbiWidthReadonlyDisposition.TYPED_SLICE5_CAUSE:
            signals.append(AbiWidthReadonlyBlockerSignal.from_summary_occurrence(
                analysis, acceptance_result, occurrence
            ))
    return tuple(signals)


@dataclass(frozen=True)
class ReturnAbiProductionAssessment:
    left_seed: FunctionReturnAbiSeed
    right_seed: FunctionReturnAbiSeed
    relation_assessment: Optional[ReturnAbiCompatibilityAssessment]
    signals: tuple[AbiWidthReadonlyBlockerSignal, ...]


def assess_return_abi_pair(
    left_analysis: Any,
    right_analysis: Any,
    left_width_seed: Any,
    right_width_seed: Any,
    pair_width_seed: Any,
) -> ReturnAbiProductionAssessment:
    """Produce exact ABI blockers without reading legacy reason/detail strings."""

    left = FunctionReturnAbiSeed.from_analysis_and_width_seed(
        left_analysis, left_width_seed
    )
    right = FunctionReturnAbiSeed.from_analysis_and_width_seed(
        right_analysis, right_width_seed
    )
    if left.malformed_slots or right.malformed_slots:
        raise ReturnAbiAuthorityInvalid(
            "return_abi_source_malformed",
            malformed_slots=(
                tuple(f"left:{slot}" for slot in left.malformed_slots)
                + tuple(f"right:{slot}" for slot in right.malformed_slots)
            ),
            detail="return ABI source is MALFORMED and must make the shadow entry INVALID",
        )
    signals = [
        AbiWidthReadonlyBlockerSignal.from_return_abi_seed(seed, slot)
        for seed in (left, right)
        for slot in seed.missing_slots
    ]
    relation = None
    if left.observation_complete and right.observation_complete:
        if not left_width_seed.complete or not right_width_seed.complete:
            projection = None
        else:
            try:
                projection = ReturnObservationProjectionSeed.from_pair_seed(
                    left_width_seed, right_width_seed, pair_width_seed
                )
            except ProjectionNotFormable:
                projection = None
        if projection is not None:
            relation = ReturnAbiCompatibilityAssessment.assess(
                projection, left, right
            )
            if relation.status in {
                ReturnAbiRelationStatus.PROVED,
                ReturnAbiRelationStatus.UNPROVEN,
            }:
                signals.append(
                    AbiWidthReadonlyBlockerSignal.from_projection_seed(
                        "return_abi_relation_unproven", projection
                    )
                )
            elif relation.status is ReturnAbiRelationStatus.INVALID:
                raise ReturnAbiAuthorityInvalid(
                    "return_abi_compatibility_invalid",
                    detail="return ABI compatibility assessment is INVALID",
                )
    return ReturnAbiProductionAssessment(left, right, relation, tuple(signals))
