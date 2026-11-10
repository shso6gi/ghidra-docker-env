"""Sealed Phase 6.4 loop, recurrence, and summary authority contracts."""

from __future__ import annotations

from dataclasses import dataclass
from enum import Enum
from types import MappingProxyType
from types import MethodType
from typing import Any, Iterable, Mapping, Optional
import threading

from scripts.function_tracer_pcode.authority.contracts import (
    CauseOccurrence,
    CauseOccurrenceAuthority,
    IdentityScope,
    ProofRequirement,
    ReasonDefinition,
    RecoveryAddressability,
    RequirementSlotDefinition,
    SatisfactionContractDefinition,
    RequirementCompletionReceipt,
    all_of,
    authority_digest,
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
    EventIntent,
    EventType,
    RequirementCompletedEventAuthority,
    GenericReceiptBoundSolverExecutionEventAuthority,
)


LOOP_DOMAIN_CONTRACT_ID = "loop-recurrence-summary-v2"
LOOP_REGISTRY_VERSION = 1


class LoopSourceDisposition(str, Enum):
    TYPED_SLICE4_CAUSE = "TYPED_SLICE4_CAUSE"
    REFINED_TO_SLICE3 = "REFINED_TO_SLICE3"
    INFRASTRUCTURE_INVALID = "INFRASTRUCTURE_INVALID"
    DEFERRED_SLICE5 = "DEFERRED_SLICE5"


class LoopStageCapability(str, Enum):
    STRUCTURAL_ONLY = "STRUCTURAL_ONLY"
    STRUCTURAL_OR_SOLVER_UNSAT = "STRUCTURAL_OR_SOLVER_UNSAT"
    SOLVER_UNSAT_ONLY = "SOLVER_UNSAT_ONLY"


@dataclass(frozen=True)
class LoopReasonSpec:
    reason_id: str
    identity_scope: IdentityScope
    target_kind: str
    contract_definition_id: str
    proof_kinds: tuple[str, ...]


def _single_contract(reason_id: str, proof_kind: str) -> SatisfactionContractDefinition:
    return SatisfactionContractDefinition(
        reason_id + "-recovery",
        1,
        (RequirementSlotDefinition("proof", frozenset((proof_kind,))),),
        requirement_slot("proof"),
    )


LOOP_EXACT_SUMMARY_CONTRACT = SatisfactionContractDefinition(
    "loop-exact-summary-recovery",
    1,
    (
        RequirementSlotDefinition(
            "loop_exact_term_relation", frozenset(("loop_exact_term_relation",))
        ),
        RequirementSlotDefinition(
            "loop_exact_guard_partition", frozenset(("loop_exact_guard_partition",))
        ),
    ),
    all_of(
        requirement_slot("loop_exact_term_relation"),
        requirement_slot("loop_exact_guard_partition"),
    ),
)


_SINGLE_REASON_ROWS = (
    (
        "recurrence_proposal_validation_unproven",
        IdentityScope.UNARY,
        "recurrence_proposal",
        "recurrence_transition_termination_validation",
    ),
    (
        "loop_summary_guard_correspondence_unproven",
        IdentityScope.RELATIONAL,
        "loop_summary_pair",
        "loop_summary_guard_correspondence",
    ),
    (
        "loop_summary_structure_correspondence_unproven",
        IdentityScope.RELATIONAL,
        "loop_summary_pair",
        "loop_summary_structure_correspondence",
    ),
    (
        "loop_summary_semantic_equality_unproven",
        IdentityScope.RELATIONAL,
        "loop_summary_pair",
        "loop_summary_semantic_equality",
    ),
    (
        "summary_return_extraction_incomplete",
        IdentityScope.UNARY,
        "summary_return_extraction",
        "summary_return_extraction",
    ),
    (
        "summary_return_value_extraction_incomplete",
        IdentityScope.UNARY,
        "summary_return_candidate",
        "summary_return_value_extraction",
    ),
    (
        "summary_recurrence_transition_validation_incomplete",
        IdentityScope.UNARY,
        "summary_return_candidate",
        "summary_recurrence_transition_validation",
    ),
    (
        "summary_return_precondition_incomplete",
        IdentityScope.UNARY,
        "summary_return_candidate",
        "summary_return_active_precondition",
    ),
    (
        "summary_effect_model_incomplete",
        IdentityScope.UNARY,
        "summary_effect_surface",
        "summary_effect_model",
    ),
    (
        "phi_cycle_lowering_unproven",
        IdentityScope.UNARY,
        "phi_scc",
        "phi_cycle_structural_lowering",
    ),
    (
        "summary_return_overlap_feasibility_unproven",
        IdentityScope.UNARY,
        "same_function_return_pair",
        "summary_return_overlap_feasibility",
    ),
    (
        "summary_return_overlap_input_incomplete",
        IdentityScope.UNARY,
        "same_function_return_pair",
        "summary_return_overlap_value_inputs",
    ),
    (
        "summary_return_overlap_value_equality_unproven",
        IdentityScope.UNARY,
        "same_function_return_pair",
        "summary_return_overlap_value_equality",
    ),
    (
        "summary_return_memory_observation_mismatch",
        IdentityScope.UNARY,
        "same_function_return_pair",
        "summary_return_memory_observation_relation",
    ),
    (
        "summary_return_partition_totality_unproven",
        IdentityScope.UNARY,
        "summary_return_partition",
        "summary_return_partition_totality",
    ),
)


_contracts: list[SatisfactionContractDefinition] = [LOOP_EXACT_SUMMARY_CONTRACT]
_specs: list[LoopReasonSpec] = [
    LoopReasonSpec(
        "loop_exact_summary_relation_unproven",
        IdentityScope.RELATIONAL,
        "exact_summary_pair",
        LOOP_EXACT_SUMMARY_CONTRACT.contract_definition_id,
        ("loop_exact_term_relation", "loop_exact_guard_partition"),
    )
]
for _reason_id, _scope, _target_kind, _proof_kind in _SINGLE_REASON_ROWS:
    _contract = _single_contract(_reason_id, _proof_kind)
    _contracts.append(_contract)
    _specs.append(
        LoopReasonSpec(
            _reason_id,
            _scope,
            _target_kind,
            _contract.contract_definition_id,
            (_proof_kind,),
        )
    )


LOOP_REASON_SPECS: Mapping[str, LoopReasonSpec] = MappingProxyType(
    {item.reason_id: item for item in sorted(_specs, key=lambda item: item.reason_id)}
)
if len(LOOP_REASON_SPECS) != len(_specs):
    raise ValueError("duplicate Phase 6.4 reason specification")


def _reason_definition(spec: LoopReasonSpec) -> ReasonDefinition:
    return ReasonDefinition(
        spec.reason_id,
        "loop_recurrence_summary",
        "proof_obligation",
        "blocks_decision",
        frozenset((spec.target_kind,)),
        ("object_derived_identity", "source_snapshot", "missing_proposition"),
        frozenset(spec.proof_kinds),
        True,
        LOOP_DOMAIN_CONTRACT_ID,
        RecoveryAddressability.REQUIREMENT_REQUIRED,
    )


LOOP_REASON_REGISTRY = SealedReasonRegistry.build(
    _reason_definition(spec) for spec in LOOP_REASON_SPECS.values()
)
LOOP_RECOVERY_REGISTRY = SealedRecoveryRegistry.build(_contracts)


@dataclass(frozen=True)
class LoopSourceClassification:
    disposition: LoopSourceDisposition
    reason_ids: tuple[str, ...]
    source_contract: str
    source_code: Any

    def __post_init__(self) -> None:
        object.__setattr__(self, "reason_ids", tuple(self.reason_ids))
        if self.disposition is LoopSourceDisposition.TYPED_SLICE4_CAUSE:
            if len(self.reason_ids) != 1 or self.reason_ids[0] not in LOOP_REASON_SPECS:
                raise ValueError("slice4 classification lacks one sealed reason")
        elif self.disposition is LoopSourceDisposition.REFINED_TO_SLICE3:
            if not self.reason_ids:
                raise ValueError("slice3 refinement lacks exact reason owners")
        elif self.reason_ids:
            raise ValueError("invalid/deferred classifications cannot own reasons")


_LOOP_FALLBACK_REASONS = MappingProxyType({
    "counted_loop_summary_expression_proof_missing": "loop_exact_summary_relation_unproven",
    "loop_summary_guard_mismatch": "loop_summary_guard_correspondence_unproven",
    "loop_summary_shape_mismatch": "loop_summary_structure_correspondence_unproven",
    "loop_summary_incompatible": "loop_summary_structure_correspondence_unproven",
    "loop_summary_intrinsic_mismatch": "loop_summary_structure_correspondence_unproven",
    "loop_summary_operand_mismatch": "loop_summary_structure_correspondence_unproven",
    "exact_key_unavailable": "loop_summary_structure_correspondence_unproven",
    "exact_key_mismatch": "loop_summary_structure_correspondence_unproven",
    "loop_summary_unproven": "loop_summary_semantic_equality_unproven",
    "loop_summary_unknown": "loop_summary_semantic_equality_unproven",
})


_SUMMARY_BLOCKER_REASONS = MappingProxyType({
    "summary_return_candidate_invalid:no_proposed_returns": "summary_return_extraction_incomplete",
    "summary_return_candidate_invalid:no_new_summary_returns": "summary_return_extraction_incomplete",
    "summary_return_candidate_invalid:no_valid_candidates": "summary_return_extraction_incomplete",
    "summary_return_candidate_invalid:value_missing": "summary_return_value_extraction_incomplete",
    "summary_return_candidate_invalid:transition_evidence_missing": "summary_recurrence_transition_validation_incomplete",
    "summary_return_candidate_invalid:transition_evidence_incomplete": "summary_recurrence_transition_validation_incomplete",
    "summary_precondition_incomplete:summary_applicability_guard_missing": "summary_return_precondition_incomplete",
    "summary_effect_unmodeled:side_effect_provenance_incomplete": "summary_effect_model_incomplete",
    "summary_effect_unmodeled:effect_region_incomplete": "summary_effect_model_incomplete",
    "summary_effect_unmodeled:memory_read_unmodeled": "summary_effect_model_incomplete",
    "summary_effect_unmodeled:memory_write_effects_present": "summary_effect_model_incomplete",
    "phi_circular_replacement_unproven:replacement_obligation_missing": "phi_cycle_lowering_unproven",
    "summary_return_overlap_unproven:overlap_feasibility_unknown": "summary_return_overlap_feasibility_unproven",
    "summary_return_overlap_unproven:value_comparison_unavailable": "summary_return_overlap_input_incomplete",
    "summary_return_overlap_unproven:value_equality_not_proved": "summary_return_overlap_value_equality_unproven",
    "summary_return_overlap_unproven:memory_read_model_mismatch": "summary_return_memory_observation_mismatch",
    "summary_partition_not_total:active_precondition_not_covered": "summary_return_partition_totality_unproven",
    "return_coverage_gap:summary_partition_not_total:active_precondition_not_covered": "summary_return_partition_totality_unproven",
})


_INVALID_SUMMARY_BLOCKERS = frozenset({
    "summary_return_candidate_invalid:unstable_guard_key",
    "summary_return_candidate_invalid:unstable_value_key",
    "summary_return_candidate_invalid:opaque_guard_key",
    "summary_return_candidate_invalid:opaque_value_key",
    "summary_return_candidate_invalid:loop_summary_identity_missing",
    "summary_return_candidate_invalid:unstable_loop_summary_identity",
    "summary_return_candidate_invalid:unstable_transition_evidence",
})


_DEFERRED_SUMMARY_BLOCKERS = frozenset({
    "summary_return_candidate_invalid:return_width_missing",
    "summary_return_overlap_unproven:return_width_mismatch",
})


_SLICE3_DIRECT_SUMMARY_BLOCKERS = MappingProxyType({
    "summary_effect_unmodeled:effect_summary_missing": ("effect_observation_coverage_incomplete",),
    "summary_effect_unmodeled:unsupported_call_effect": ("unsupported_call_effect_semantics",),
})


_EFFECT_INCOMPLETE_REASON_OWNERS = MappingProxyType({
    "callee_effect_summary_missing": "callee_effect_summary_incomplete",
    "effect_order_unavailable": "memory_effect_order_extraction_incomplete",
    "effect_summary_path_coverage_incomplete": "effect_observation_coverage_incomplete",
    # Issue #104: observable memory writes / effect surface that could not be
    # modelled; the function's effect census is not fully observed.
    "effect_store_location_unmodeled": "effect_observation_coverage_incomplete",
    "effect_global_read_identity_unavailable": "effect_observation_coverage_incomplete",
    "effect_surface_composition_incomplete": "effect_observation_coverage_incomplete",
    # Issue #131: 効果面の展開が上限で切り捨てられた要約。観測できた効果集合が
    # 全体である保証がないので、既存の効果不完全性へ写像する。
    "effect_expansion_case_budget_exceeded": "effect_observation_coverage_incomplete",
})


def classify_loop_fallback(source_code: str) -> LoopSourceClassification:
    if type(source_code) is not str or not source_code:
        raise TypeError("loop fallback source code must be an exact string")
    reason_id = _LOOP_FALLBACK_REASONS.get(source_code)
    if reason_id is None:
        return LoopSourceClassification(
            LoopSourceDisposition.INFRASTRUCTURE_INVALID,
            (),
            "loop_summary_fallback",
            source_code,
        )
    return LoopSourceClassification(
        LoopSourceDisposition.TYPED_SLICE4_CAUSE,
        (reason_id,),
        "loop_summary_fallback",
        source_code,
    )


def classify_recurrence_proposal(proposal: Any) -> LoopSourceClassification:
    from scripts.function_tracer_pcode.core.recurrence_contracts import (
        QuarantinedRecurrenceProposal,
    )

    if type(proposal) is not QuarantinedRecurrenceProposal:
        raise TypeError("recurrence classification requires an exact quarantined proposal")
    return LoopSourceClassification(
        LoopSourceDisposition.TYPED_SLICE4_CAUSE,
        ("recurrence_proposal_validation_unproven",),
        "quarantined_recurrence_proposal",
        proposal.digest,
    )


def classify_summary_blocker(source_code: str) -> LoopSourceClassification:
    if type(source_code) is not str or not source_code:
        raise TypeError("summary blocker source code must be an exact string")
    reason_id = _SUMMARY_BLOCKER_REASONS.get(source_code)
    if reason_id is not None:
        return LoopSourceClassification(
            LoopSourceDisposition.TYPED_SLICE4_CAUSE,
            (reason_id,),
            "summary_return_acceptance",
            source_code,
        )
    owners = _SLICE3_DIRECT_SUMMARY_BLOCKERS.get(source_code)
    if owners is not None:
        return LoopSourceClassification(
            LoopSourceDisposition.REFINED_TO_SLICE3,
            owners,
            "summary_return_acceptance",
            source_code,
        )
    if source_code in _INVALID_SUMMARY_BLOCKERS:
        disposition = LoopSourceDisposition.INFRASTRUCTURE_INVALID
    elif source_code in _DEFERRED_SUMMARY_BLOCKERS:
        disposition = LoopSourceDisposition.DEFERRED_SLICE5
    else:
        disposition = LoopSourceDisposition.INFRASTRUCTURE_INVALID
    return LoopSourceClassification(
        disposition, (), "summary_return_acceptance", source_code
    )


def classify_effect_incomplete_reasons(
    reasons: Iterable[str],
) -> LoopSourceClassification:
    materialized = tuple(reasons)
    if (
        not materialized
        or any(type(item) is not str or not item for item in materialized)
        or materialized != tuple(sorted(materialized))
        or len(materialized) != len(set(materialized))
        or any(item not in _EFFECT_INCOMPLETE_REASON_OWNERS for item in materialized)
    ):
        return LoopSourceClassification(
            LoopSourceDisposition.INFRASTRUCTURE_INVALID,
            (),
            "summary_effect_incomplete_reasons",
            materialized,
        )
    return LoopSourceClassification(
        LoopSourceDisposition.REFINED_TO_SLICE3,
        tuple(_EFFECT_INCOMPLETE_REASON_OWNERS[item] for item in materialized),
        "summary_effect_incomplete_reasons",
        materialized,
    )


@dataclass(frozen=True)
class LoopProducerStageSpec:
    producer_contract_id: str
    producer_version: str
    proof_stage: str
    proof_kind: str
    capability: LoopStageCapability
    execution_issuer_id: str
    allowed_statuses: tuple[str, ...]
    terminal_eligible_statuses: tuple[str, ...]
    terminal_priority: int

    def __post_init__(self) -> None:
        if type(self.capability) is not LoopStageCapability:
            if type(self.capability) is not str:
                raise TypeError(
                    "loop producer capability must be an exact Enum or string"
                )
            try:
                capability = LoopStageCapability(self.capability)
            except ValueError as exc:
                raise ValueError("loop producer capability is not sealed") from exc
            object.__setattr__(self, "capability", capability)
        object.__setattr__(self, "allowed_statuses", tuple(sorted(self.allowed_statuses)))
        object.__setattr__(
            self,
            "terminal_eligible_statuses",
            tuple(sorted(self.terminal_eligible_statuses)),
        )
        if not self.allowed_statuses or not set(self.terminal_eligible_statuses).issubset(
            self.allowed_statuses
        ):
            raise ValueError("loop producer statuses are invalid")

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
            LOOP_DOMAIN_CONTRACT_ID,
            self.producer_contract_id,
            self.producer_version,
            self.proof_stage,
            self.execution_issuer_id,
            frozenset(self.allowed_statuses),
            frozenset(self.terminal_eligible_statuses),
            self.terminal_priority,
        )


_STAGE_ROWS = (
    ("typed-recurrence-transition-validator-v2", "2", "recurrence_transition_termination_validation", "recurrence_transition_termination_validation", LoopStageCapability.STRUCTURAL_ONLY, "loop-structural-proof-factory-v1", ("structural_proof",), (), 10),
    ("loop-exact-term-relation-validator-v2", "2", "loop_exact_term_relation", "loop_exact_term_relation", LoopStageCapability.STRUCTURAL_OR_SOLVER_UNSAT, "parallel-solver-runner-v1", ("attempted",), ("attempted",), 20),
    ("loop-exact-guard-partition-validator-v2", "2", "loop_exact_guard_partition", "loop_exact_guard_partition", LoopStageCapability.STRUCTURAL_OR_SOLVER_UNSAT, "parallel-solver-runner-v1", ("attempted",), ("attempted",), 30),
    ("loop-summary-guard-correspondence-solver-v2", "2", "loop_summary_guard_correspondence", "loop_summary_guard_correspondence", LoopStageCapability.SOLVER_UNSAT_ONLY, "parallel-solver-runner-v1", ("attempted",), ("attempted",), 40),
    ("loop-summary-structure-correspondence-validator-v2", "2", "loop_summary_structure_correspondence", "loop_summary_structure_correspondence", LoopStageCapability.STRUCTURAL_OR_SOLVER_UNSAT, "parallel-solver-runner-v1", ("attempted",), ("attempted",), 50),
    ("loop-summary-semantic-equality-solver-v2", "2", "loop_summary_semantic_equality", "loop_summary_semantic_equality", LoopStageCapability.SOLVER_UNSAT_ONLY, "parallel-solver-runner-v1", ("attempted",), ("attempted",), 60),
    ("summary-return-overlap-feasibility-solver-v2", "2", "summary_return_overlap_feasibility", "summary_return_overlap_feasibility", LoopStageCapability.SOLVER_UNSAT_ONLY, "parallel-solver-runner-v1", ("attempted",), ("attempted",), 70),
    ("summary-return-overlap-value-equality-solver-v2", "2", "summary_return_overlap_value_equality", "summary_return_overlap_value_equality", LoopStageCapability.SOLVER_UNSAT_ONLY, "parallel-solver-runner-v1", ("attempted",), ("attempted",), 80),
    ("summary-return-partition-totality-solver-v2", "2", "summary_return_partition_totality", "summary_return_partition_totality", LoopStageCapability.SOLVER_UNSAT_ONLY, "parallel-solver-runner-v1", ("attempted",), ("attempted",), 90),
)


LOOP_PRODUCER_STAGE_SPECS = tuple(LoopProducerStageSpec(*row) for row in _STAGE_ROWS)
if tuple(item.terminal_priority for item in LOOP_PRODUCER_STAGE_SPECS) != tuple(
    sorted(item.terminal_priority for item in LOOP_PRODUCER_STAGE_SPECS)
):
    raise ValueError("loop producer rows are not priority ordered")


def loop_producer_registry_authority_dict() -> dict[str, Any]:
    return {
        "registry_id": LOOP_DOMAIN_CONTRACT_ID,
        "registry_version": LOOP_REGISTRY_VERSION,
        "rows": tuple(item.to_authority_tuple() for item in LOOP_PRODUCER_STAGE_SPECS),
    }


LOOP_PRODUCER_STAGE_REGISTRY_DIGEST = authority_digest(
    loop_producer_registry_authority_dict()
)
LOOP_COMMON_EXECUTION_STAGE_REGISTRY = ProducerStageRegistry(
    LOOP_REGISTRY_VERSION,
    tuple(item.to_common_contract() for item in LOOP_PRODUCER_STAGE_SPECS),
)


EXPECTED_LOOP_PRODUCER_STAGE_REGISTRY_DIGEST = (
    "59e3fbedc98851c45400a9618c7814f09c2e372d4f9d912e47a4e52921d84654"
)
EXPECTED_LOOP_COMMON_REGISTRY_DIGEST = (
    "aed45d8bb14646686eefcace9ba0f59856ea48a2b7305d067e875916683c8eb3"
)
if LOOP_PRODUCER_STAGE_REGISTRY_DIGEST != EXPECTED_LOOP_PRODUCER_STAGE_REGISTRY_DIGEST:
    raise ValueError("loop producer registry authority digest drift")
if (
    LOOP_COMMON_EXECUTION_STAGE_REGISTRY.normalized_registry_digest
    != EXPECTED_LOOP_COMMON_REGISTRY_DIGEST
):
    raise ValueError("loop common execution registry digest drift")


_LOOP_BLOCKER_SIGNAL_TOKEN = object()
_RECURRENCE_COMPLETION_SIGNAL_TOKEN = object()
_RECURRENCE_BINDING_TOKEN = object()
_RECURRENCE_COMPLETION_AUTHORITY_TOKEN = object()


@dataclass(frozen=True, init=False)
class LoopBlockerProductionSignal:
    """Factory-issued object-derived input for one exact slice4 cause."""

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

    def __init__(
        self,
        reason_id: str,
        identity_scope: IdentityScope,
        target_kind: str,
        canonical_target_key: Any,
        missing_semantic_fact: Any,
        semantic_proposition: Any,
        observation_surface: Any,
        active_semantic_precondition: Any,
        correspondence_contract: Any,
        evidence_refs: Iterable[str],
        producer_id: str,
        *,
        _factory_token: object = None,
    ) -> None:
        if _factory_token is not _LOOP_BLOCKER_SIGNAL_TOKEN:
            raise TypeError("loop blocker signal must be object-factory issued")
        values = {
            "reason_id": reason_id,
            "identity_scope": identity_scope,
            "target_kind": target_kind,
            "canonical_target_key": canonical_target_key,
            "missing_semantic_fact": missing_semantic_fact,
            "semantic_proposition": semantic_proposition,
            "observation_surface": observation_surface,
            "active_semantic_precondition": active_semantic_precondition,
            "correspondence_contract": correspondence_contract,
            "evidence_refs": tuple(evidence_refs),
            "producer_id": producer_id,
        }
        for name, value in values.items():
            object.__setattr__(self, name, value)
        spec = LOOP_REASON_SPECS.get(reason_id)
        if spec is None:
            raise ValueError("loop blocker reason is not sealed")
        if identity_scope is not spec.identity_scope or target_kind != spec.target_kind:
            raise ValueError("loop blocker scope/target differs from registry")
        if type(producer_id) is not str or not producer_id:
            raise TypeError("loop blocker producer identity is incomplete")
        if any(type(item) is not str or not item for item in self.evidence_refs):
            raise TypeError("loop blocker evidence references must be exact strings")
        # authority_digest is also the canonical-value validation boundary.
        for value in (
            canonical_target_key,
            missing_semantic_fact,
            semantic_proposition,
            observation_surface,
            active_semantic_precondition,
            correspondence_contract,
        ):
            authority_digest(value)

    def _phase7_signal_authority(self) -> Mapping[str, Any]:
        """Project only the sealed semantic blocker fields into Phase 7 identity."""

        return {
            name: getattr(self, name)
            for name in self.__dataclass_fields__
        }

    @classmethod
    def from_recurrence_proposal(
        cls, analysis: Any, proposal: Any
    ) -> "LoopBlockerProductionSignal":
        from scripts.function_tracer_pcode.core.analysis import FunctionReturnAnalysis
        from scripts.function_tracer_pcode.core.recurrence_contracts import (
            QuarantinedRecurrenceProposal,
        )

        if type(analysis) is not FunctionReturnAnalysis:
            raise TypeError("recurrence blocker requires exact function analysis")
        classification = classify_recurrence_proposal(proposal)
        if type(proposal) is not QuarantinedRecurrenceProposal:
            raise TypeError("recurrence blocker requires exact quarantined proposal")
        function_identity = analysis.outcome_function_identity()
        target = (
            "recurrence_proposal_target_v2",
            function_identity,
            proposal.seed_core_digest,
            proposal.digest,
            "recurrence-successor-derivation-v2",
        )
        return cls(
            classification.reason_ids[0],
            IdentityScope.UNARY,
            "recurrence_proposal",
            target,
            ("recurrence_proposal_validated", False),
            ("recurrence_transition_and_termination_preserve_function_semantics", proposal.digest),
            ("function_recurrence_proposal", function_identity),
            ("proposal_is_quarantined", proposal.digest),
            ("one_function_snapshot",),
            (proposal.digest, proposal.seed_core_digest),
            "typed-recurrence-proposal-signal-v2",
            _factory_token=_LOOP_BLOCKER_SIGNAL_TOKEN,
        )

    @classmethod
    def from_summary_occurrence(
        cls,
        analysis: Any,
        acceptance_result: Any,
        blocker_occurrence: Any,
        *,
        semantic_object_identity: Any = None,
    ) -> "LoopBlockerProductionSignal":
        from scripts.function_tracer_pcode.analysis.returns.summary_returns import (
            SummaryReturnAcceptanceResult,
            SummaryReturnBlockerOccurrence,
        )
        from scripts.function_tracer_pcode.core.analysis import FunctionReturnAnalysis

        if type(analysis) is not FunctionReturnAnalysis:
            raise TypeError("summary occurrence signal requires exact analysis")
        if type(acceptance_result) is not SummaryReturnAcceptanceResult:
            raise TypeError("summary occurrence signal requires exact acceptance result")
        if type(blocker_occurrence) is not SummaryReturnBlockerOccurrence:
            raise TypeError("summary occurrence signal requires exact blocker occurrence")
        if blocker_occurrence not in acceptance_result.blocker_occurrences:
            raise ValueError("summary blocker occurrence is not in the acceptance result")
        if blocker_occurrence.function_identity != analysis.outcome_function_identity():
            raise ValueError("summary blocker occurrence belongs to another function")
        classification = classify_summary_blocker(blocker_occurrence.source_code)
        if classification.disposition is not LoopSourceDisposition.TYPED_SLICE4_CAUSE:
            raise ValueError("summary occurrence does not own a slice4 cause")
        reason_id = classification.reason_ids[0]
        spec = LOOP_REASON_SPECS[reason_id]
        if spec.target_kind == "same_function_return_pair":
            if (
                blocker_occurrence.candidate_identity is None
                or blocker_occurrence.peer_return_identity is None
            ):
                raise ValueError("summary overlap occurrence lacks an exact same-function pair")
            target = (
                "same_function_summary_return_pair_v2",
                blocker_occurrence.function_identity,
                blocker_occurrence.candidate_identity,
                blocker_occurrence.peer_return_identity,
                blocker_occurrence.active_precondition_key,
                blocker_occurrence.observation_surface_key,
            )
        elif spec.target_kind == "phi_scc":
            if semantic_object_identity is None:
                raise ValueError("phi-cycle cause lacks an exact SCC object identity")
            target = (
                "phi_scc_v2",
                blocker_occurrence.function_identity,
                semantic_object_identity,
            )
        elif blocker_occurrence.candidate_identity is None:
            target = (
                spec.target_kind + "_v2",
                blocker_occurrence.function_identity,
                blocker_occurrence.active_precondition_key,
                blocker_occurrence.observation_surface_key,
            )
        else:
            target = (
                spec.target_kind + "_v2",
                blocker_occurrence.function_identity,
                blocker_occurrence.candidate_identity,
                blocker_occurrence.active_precondition_key,
                blocker_occurrence.observation_surface_key,
            )
        return cls(
            reason_id,
            spec.identity_scope,
            spec.target_kind,
            target,
            ("missing_summary_proposition", blocker_occurrence.source_code),
            ("summary_acceptance_proposition", reason_id),
            blocker_occurrence.observation_surface_key,
            (
                "summary_acceptance_blocked",
                blocker_occurrence.active_precondition_key,
            ),
            ("one_function_snapshot",),
            (blocker_occurrence.occurrence_digest, blocker_occurrence.source_code),
            "typed-summary-acceptance-signal-v2",
            _factory_token=_LOOP_BLOCKER_SIGNAL_TOKEN,
        )

    @classmethod
    def from_loop_fallback(
        cls,
        analysis1: Any,
        analysis2: Any,
        case1: Any,
        case2: Any,
        source_code: str,
        *,
        observation_contract_id: str,
    ) -> "LoopBlockerProductionSignal":
        from scripts.function_tracer_pcode.core.analysis import FunctionReturnAnalysis
        from scripts.function_tracer_pcode.proof.obligations.snapshot import AnalysisSnapshot
        from scripts.function_tracer_pcode.proof.strategies.pairwise_models import ReturnCase

        if type(analysis1) is not FunctionReturnAnalysis or type(
            analysis2
        ) is not FunctionReturnAnalysis:
            raise TypeError("loop fallback signal requires exact function analyses")
        if type(case1) is not ReturnCase or type(case2) is not ReturnCase:
            raise TypeError("loop fallback signal requires exact return cases")
        if type(observation_contract_id) is not str or not observation_contract_id:
            raise TypeError("loop fallback observation contract is incomplete")
        classification = classify_loop_fallback(source_code)
        if classification.disposition is not LoopSourceDisposition.TYPED_SLICE4_CAUSE:
            raise ValueError("loop fallback cannot form a typed semantic cause")
        reason_id = classification.reason_ids[0]
        spec = LOOP_REASON_SPECS[reason_id]
        left_snapshot = AnalysisSnapshot.from_function_analysis(
            analysis1
        ).semantic_fingerprint
        right_snapshot = AnalysisSnapshot.from_function_analysis(
            analysis2
        ).semantic_fingerprint
        left_case = _loop_case_object_identity(case1)
        right_case = _loop_case_object_identity(case2)
        target = (
            spec.target_kind + "_v2",
            ("left_source_snapshot", left_snapshot),
            ("right_source_snapshot", right_snapshot),
            ("left_case", left_case),
            ("right_case", right_case),
            ("observation_contract", observation_contract_id),
        )
        return cls(
            reason_id,
            IdentityScope.RELATIONAL,
            spec.target_kind,
            target,
            ("missing_loop_correspondence", source_code),
            ("loop_return_semantics_correspond", reason_id),
            (
                observation_contract_id,
                _loop_case_observation_surface(case1),
                _loop_case_observation_surface(case2),
            ),
            ("pairwise_loop_fallback_active", True),
            ("ordered_function_pair", left_snapshot, right_snapshot),
            (source_code, authority_digest(left_case), authority_digest(right_case)),
            "typed-loop-pair-fallback-signal-v2",
            _factory_token=_LOOP_BLOCKER_SIGNAL_TOKEN,
        )

def _loop_case_object_identity(case: Any) -> Any:
    return_info = getattr(case, "return_info", None)
    if return_info is None or not callable(getattr(return_info, "to_dict", None)):
        raise TypeError("loop return case lacks immutable return authority")
    conditions = []
    for condition in tuple(getattr(case, "conditions", ()) or ()):
        structural_key = getattr(condition, "structural_key", None)
        if not callable(structural_key):
            raise TypeError("loop return condition lacks structural object identity")
        conditions.append(structural_key(budget=512))
    value_key = getattr(case.value_expr, "structural_key", None)
    if not callable(value_key):
        raise TypeError("loop return value lacks structural object identity")
    value = value_key(budget=512)
    return (
        "loop_return_case_v2",
        authority_digest(return_info.to_dict()),
        tuple(conditions),
        value,
    )


def _loop_case_observation_surface(case: Any) -> Any:
    surface = getattr(case, "comparison_surface", None)
    stable_key = getattr(surface, "stable_key", None)
    surface_key = stable_key() if callable(stable_key) else None
    effect_summary = getattr(case, "effect_summary", None)
    effect_key_fn = getattr(effect_summary, "stable_key", None)
    effect_key = effect_key_fn() if callable(effect_key_fn) else None
    return (
        "loop_case_observation_surface_v2",
        surface_key,
        effect_key,
        getattr(case, "return_type", None),
        getattr(case, "program_is_big_endian", None),
    )


def summary_signals_from_acceptance(
    analysis: Any, acceptance_result: Any
) -> tuple[LoopBlockerProductionSignal, ...]:
    from scripts.function_tracer_pcode.analysis.returns.summary_returns import (
        SummaryReturnAcceptanceResult,
    )

    if type(acceptance_result) is not SummaryReturnAcceptanceResult:
        raise TypeError("summary signal expansion requires exact acceptance result")
    candidates = {
        tuple(item.candidate_id): item for item in acceptance_result.candidates
    }
    classified_occurrences = tuple(
        (
            occurrence,
            _classify_summary_occurrence(analysis, occurrence),
        )
        for occurrence in acceptance_result.blocker_occurrences
    )
    slice3_blocked_candidates = {
        tuple(occurrence.candidate_id or ())
        for occurrence, classification in classified_occurrences
        if classification.disposition is LoopSourceDisposition.REFINED_TO_SLICE3
    }
    signals: list[LoopBlockerProductionSignal] = []
    for occurrence, classification in classified_occurrences:
        if classification.disposition in {
            LoopSourceDisposition.DEFERRED_SLICE5,
            LoopSourceDisposition.REFINED_TO_SLICE3,
        }:
            continue
        if classification.disposition is LoopSourceDisposition.INFRASTRUCTURE_INVALID:
            raise ValueError(
                "summary acceptance source cannot form canonical slice4 evidence: "
                + occurrence.source_code
            )
        if (
            classification.reason_ids == ("summary_effect_model_incomplete",)
            and tuple(occurrence.candidate_id or ()) in slice3_blocked_candidates
        ):
            # Slice3 general effect authority owns the missing prerequisite.
            continue
        if classification.reason_ids == ("phi_cycle_lowering_unproven",):
            candidate = candidates.get(tuple(occurrence.candidate_id or ()))
            if candidate is None:
                raise ValueError("phi-cycle blocker has no exact candidate")
            phi_keys = _phi_cycle_object_keys(candidate.return_info)
            if not phi_keys:
                raise ValueError("phi-cycle blocker has no stable SCC object identity")
            signals.extend(
                LoopBlockerProductionSignal.from_summary_occurrence(
                    analysis,
                    acceptance_result,
                    occurrence,
                    semantic_object_identity=phi_key,
                )
                for phi_key in phi_keys
            )
            continue
        signals.append(
            LoopBlockerProductionSignal.from_summary_occurrence(
                analysis, acceptance_result, occurrence
            )
        )
    return tuple(signals)


def _classify_summary_occurrence(
    analysis: Any, occurrence: Any
) -> LoopSourceClassification:
    classified = classify_summary_blocker(occurrence.source_code)
    prefix = "summary_effect_unmodeled:"
    if (
        classified.disposition is LoopSourceDisposition.INFRASTRUCTURE_INVALID
        and occurrence.source_code.startswith(prefix)
    ):
        suffix = occurrence.source_code[len(prefix):]
        members = tuple(suffix.split(",")) if suffix else ()
        effect_summary = getattr(analysis, "effect_summary", None)
        actual = tuple(getattr(effect_summary, "incomplete_reasons", ()) or ())
        if members == actual:
            return classify_effect_incomplete_reasons(members)
    return classified


def _phi_cycle_object_keys(return_info: Any) -> tuple[Any, ...]:
    from scripts.function_tracer_pcode.core import ExpressionType
    from scripts.function_tracer_pcode.core.recurrence_contracts import (
        ImmutableRecurrenceExpression,
    )

    keys = []

    def walk(expression: Any) -> None:
        if expression is None:
            return
        runtime_ref = getattr(expression, "runtime_ref", None)
        is_phi_cycle = (
            getattr(runtime_ref, "reason", None) == "phi_circular"
            or getattr(runtime_ref, "kind", None) == "phi_circular"
            or (
                getattr(expression, "expr_type", None) == ExpressionType.UNKNOWN
                and "phi_circular" in str(getattr(expression, "name", ""))
            )
        )
        if is_phi_cycle:
            immutable = ImmutableRecurrenceExpression.from_expression(expression)
            keys.append(("phi_cycle_object_v2", immutable.stable_key()))
        if getattr(expression, "expr_type", None) == ExpressionType.PHI:
            for condition, value in getattr(expression, "value", None) or ():
                if condition is not None:
                    walk(getattr(condition, "expression", None))
                walk(value)
            return
        for operand in getattr(expression, "operands", None) or ():
            walk(operand)

    walk(getattr(return_info, "value", None))
    for condition in getattr(return_info, "conditions", ()) or ():
        walk(getattr(condition, "expression", None))
    return tuple(sorted(set(keys), key=lambda item: authority_digest(item)))


_LOOP_EXACT_TERM_SIGNAL_TOKEN = object()
_LOOP_EXACT_GUARD_SIGNAL_TOKEN = object()
_LOOP_EXACT_TERM_AUTHORITY_TOKEN = object()
_LOOP_EXACT_GUARD_AUTHORITY_TOKEN = object()
_LOOP_SOLVER_QUERY_AUTHORITY_TOKEN = object()


def _capture_pairwise_structural_implementations() -> Mapping[str, Any]:
    """Pin service function objects before producer class/instance mutation."""

    from scripts.function_tracer_pcode.proof.strategies.pairwise_services import (
        snapshot_implementations,
    )

    captured = snapshot_implementations()
    if any(value is None for value in captured.values()):
        raise RuntimeError("pairwise structural implementation registry is incomplete")
    return MappingProxyType(captured)


_SEALED_PAIRWISE_STRUCTURAL_IMPLEMENTATIONS = (
    _capture_pairwise_structural_implementations()
)


@dataclass(frozen=True, init=False)
class LoopSolverQueryAuthority:
    stage: str
    proof_kind: str
    obligation_id: str
    observation_contract_id: str
    semantic_target_digest: str
    query_text: str
    normalized_assertion_text: str
    premise_assertions: tuple[str, ...]
    declaration_rows: tuple[str, ...]
    source_snapshot_digests: tuple[str, str]
    prepared_surface_digest: str
    execution_identity_digest: str
    authority_digest: str

    def __init__(self, *, _factory_token: object = None, **payload: Any) -> None:
        if _factory_token is not _LOOP_SOLVER_QUERY_AUTHORITY_TOKEN:
            raise TypeError("loop solver query authority must be typed-renderer issued")
        if set(payload) != set(self.__dataclass_fields__):
            raise TypeError("loop solver query authority fields are not exact")
        for name, value in payload.items():
            object.__setattr__(self, name, value)
        self.validate()

    def _payload(self) -> dict[str, Any]:
        return {
            name: getattr(self, name)
            for name in self.__dataclass_fields__
            if name != "authority_digest"
        }

    def validate(self) -> None:
        matching = tuple(
            row for row in LOOP_PRODUCER_STAGE_SPECS
            if row.proof_stage == self.stage and row.proof_kind == self.proof_kind
        )
        if len(matching) != 1 or matching[0].capability is LoopStageCapability.STRUCTURAL_ONLY:
            raise ValueError("loop solver query stage/proof kind is not solver-capable")
        for value in (
            self.obligation_id,
            self.observation_contract_id,
            self.semantic_target_digest,
            self.query_text,
            self.normalized_assertion_text,
            self.prepared_surface_digest,
            self.execution_identity_digest,
        ):
            if type(value) is not str or not value:
                raise TypeError("loop solver query identity is incomplete")
        if (
            type(self.premise_assertions) is not tuple
            or type(self.declaration_rows) is not tuple
            or any(type(item) is not str or not item for item in (
                *self.premise_assertions, *self.declaration_rows
            ))
            or type(self.source_snapshot_digests) is not tuple
            or len(self.source_snapshot_digests) != 2
            or any(type(item) is not str or not item for item in self.source_snapshot_digests)
        ):
            raise TypeError("loop solver replay surface is incomplete")
        expected_query = "\n".join((
            *self.declaration_rows,
            *self.premise_assertions,
            f"(assert {self.normalized_assertion_text})",
            "(check-sat)",
        ))
        if self.query_text != expected_query:
            raise ValueError("loop solver query differs from replay surface")
        if self.authority_digest != authority_digest(self._payload()):
            raise ValueError("loop solver query authority digest mismatch")


def _issue_loop_solver_query_authority(
    rendered: Any,
) -> LoopSolverQueryAuthority:
    """Typed-renderer boundary used by loop producers after exact query rendering."""

    from scripts.function_tracer_pcode.proof.strategies.pairwise_query_executor import (
        RenderedLoopV2SolverQuery,
    )

    if type(rendered) is not RenderedLoopV2SolverQuery:
        raise TypeError("loop query authority requires exact typed renderer receipt")
    rendered.validate()
    payload = {
        "stage": rendered.proof_stage,
        "proof_kind": rendered.proof_kind,
        "obligation_id": rendered.obligation_id,
        "observation_contract_id": rendered.observation_contract_id,
        "semantic_target_digest": rendered.semantic_target_digest,
        "query_text": rendered.query_text,
        "normalized_assertion_text": rendered.normalized_assertion_text,
        "premise_assertions": rendered.premise_assertions,
        "declaration_rows": rendered.declaration_rows,
        "source_snapshot_digests": rendered.source_snapshot_digests,
        "prepared_surface_digest": rendered.prepared_surface_digest,
        "execution_identity_digest": rendered.execution_identity_digest,
    }
    return LoopSolverQueryAuthority(
        **payload,
        authority_digest=authority_digest(payload),
        _factory_token=_LOOP_SOLVER_QUERY_AUTHORITY_TOKEN,
    )


@dataclass
class LoopSolverExecutionContext:
    lifecycle_projection: Any
    result_occurrence_id: str
    q_open_rows_by_proof_kind: Mapping[str, Any]
    attempt_ordinals: dict[tuple[str, str], int]
    _attempt_lock: Any

    def __init__(
        self,
        lifecycle_projection: Any,
        result_occurrence_id: str,
        q_open_rows_by_proof_kind: Mapping[str, Any],
    ) -> None:
        from scripts.function_tracer_pcode.authority.contracts import (
            VerifiedLifecyclePrefixProjection,
        )

        if type(lifecycle_projection) is not VerifiedLifecyclePrefixProjection:
            raise TypeError("loop execution context requires PREFIX lifecycle authority")
        lifecycle_projection.validate()
        if result_occurrence_id != lifecycle_projection.result_occurrence_id:
            raise ValueError("loop execution context result differs from projection")
        rows = dict(q_open_rows_by_proof_kind)
        if (
            not rows
            or len(rows) != len(q_open_rows_by_proof_kind)
            or any(
                type(kind) is not str
                or not kind
                or row not in lifecycle_projection.q_open_base
                or row.proof_kind != kind
                for kind, row in rows.items()
            )
        ):
            raise ValueError("loop execution context Q_open mapping is invalid")
        self.lifecycle_projection = lifecycle_projection
        self.result_occurrence_id = result_occurrence_id
        self.q_open_rows_by_proof_kind = MappingProxyType(rows)
        self.attempt_ordinals = {}
        self._attempt_lock = threading.RLock()

    def membership_for(self, query: LoopSolverQueryAuthority) -> Any:
        from scripts.function_tracer_pcode.authority.lifecycle.execution_authority import (
            ProducerAttemptMembership,
            issue_loop_requirement_assignment,
        )

        if type(query) is not LoopSolverQueryAuthority:
            raise TypeError("loop execution membership requires exact query authority")
        query.validate()
        try:
            row = self.q_open_rows_by_proof_kind[query.proof_kind]
        except KeyError as exc:
            raise ValueError("loop solver stage lacks exact live Q_open assignment") from exc
        assignment = issue_loop_requirement_assignment(
            projection=self.lifecycle_projection,
            q_open_row=row,
            query_authority=query,
        )
        spec = next(
            item for item in LOOP_PRODUCER_STAGE_SPECS
            if item.proof_stage == query.stage and item.proof_kind == query.proof_kind
        )
        key = (query.obligation_id, query.stage)
        with self._attempt_lock:
            ordinal = self.attempt_ordinals.get(key, 0) + 1
            self.attempt_ordinals[key] = ordinal
        return ProducerAttemptMembership(
            LOOP_DOMAIN_CONTRACT_ID,
            spec.producer_contract_id,
            spec.producer_version,
            spec.proof_stage,
            row.proof_requirement_id,
            query.obligation_id,
            query.observation_contract_id,
            "attempted",
            f"{self.result_occurrence_id}:{query.obligation_id}:{query.stage}",
            ordinal,
            query.execution_identity_digest,
            assignment,
        )


_LOOP_SOLVER_BATCH_TOKEN = object()


@dataclass(frozen=True, init=False)
class LoopSolverExecutionBatchSignal:
    blocker: "LoopBlockerProductionSignal"
    query_authority: LoopSolverQueryAuthority
    membership: Any
    execution_receipts: tuple[Any, ...]
    lifecycle_projection: Any

    def __init__(
        self,
        blocker: "LoopBlockerProductionSignal",
        query_authority: LoopSolverQueryAuthority,
        membership: Any,
        execution_receipts: Iterable[Any],
        lifecycle_projection: Any,
        *,
        _factory_token: object = None,
    ) -> None:
        from scripts.function_tracer_pcode.authority.lifecycle.execution_authority import (
            GenericSolverExecutionReceipt,
            ProducerAttemptMembership,
        )
        from scripts.function_tracer_pcode.authority.contracts import (
            VerifiedLifecyclePrefixProjection,
        )

        if _factory_token is not _LOOP_SOLVER_BATCH_TOKEN:
            raise TypeError("loop solver batch must be issuer joined")
        receipts = tuple(execution_receipts)
        if type(blocker) is not LoopBlockerProductionSignal:
            raise TypeError("loop solver batch lacks exact blocker")
        if type(query_authority) is not LoopSolverQueryAuthority:
            raise TypeError("loop solver batch lacks exact query authority")
        if type(membership) is not ProducerAttemptMembership:
            raise TypeError("loop solver batch lacks exact membership")
        if type(lifecycle_projection) is not VerifiedLifecyclePrefixProjection:
            raise TypeError("loop solver batch lacks exact PREFIX lifecycle authority")
        lifecycle_projection.validate()
        if not receipts or any(
            type(item) is not GenericSolverExecutionReceipt for item in receipts
        ):
            raise TypeError("loop solver batch lacks exact execution receipts")
        membership.validate_against(LOOP_COMMON_EXECUTION_STAGE_REGISTRY)
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
            receipt.validate_join(LOOP_COMMON_EXECUTION_STAGE_REGISTRY, membership)
            if receipt.query_authority_digest != expected_query_binding_digest:
                raise ValueError(
                    "loop solver receipt differs from supplied query authority"
                )
        if (
            membership.proof_stage != query_authority.stage
            or membership.obligation_id != query_authority.obligation_id
            or membership.observation_contract_id
            != query_authority.observation_contract_id
        ):
            raise ValueError("loop solver batch query and membership differ")
        object.__setattr__(self, "blocker", blocker)
        object.__setattr__(self, "query_authority", query_authority)
        object.__setattr__(self, "membership", membership)
        object.__setattr__(self, "lifecycle_projection", lifecycle_projection)
        object.__setattr__(
            self,
            "execution_receipts",
            tuple(sorted(receipts, key=lambda item: item.invocation_ordinal)),
        )

    @classmethod
    def from_issuer_results(
        cls,
        blocker: "LoopBlockerProductionSignal",
        query_authority: LoopSolverQueryAuthority,
        membership: Any,
        execution_receipts: Iterable[Any],
        lifecycle_projection: Any,
    ) -> "LoopSolverExecutionBatchSignal":
        return cls(
            blocker,
            query_authority,
            membership,
            execution_receipts,
            lifecycle_projection,
            _factory_token=_LOOP_SOLVER_BATCH_TOKEN,
        )

class _SealedPairwiseStructuralValidatorMeta(type):
    def __setattr__(cls, name: str, value: Any) -> None:
        raise TypeError("sealed pairwise structural validator class is immutable")

    def __delattr__(cls, name: str) -> None:
        raise TypeError("sealed pairwise structural validator class is immutable")


class _SealedPairwiseStructuralValidator(
    metaclass=_SealedPairwiseStructuralValidatorMeta
):
    """Narrow immutable-dispatch receiver for object-derived Method-B proofs."""

    __slots__ = ()

    def __getattribute__(self, name: str) -> Any:
        implementation = _SEALED_PAIRWISE_STRUCTURAL_IMPLEMENTATIONS.get(name)
        if implementation is not None:
            return MethodType(implementation, self)
        return object.__getattribute__(self, name)


def _method_b_structural_proof_body(covering: Any) -> tuple[Any, ...]:
    """Canonicalize the exact object proof without admitting legacy evidence dicts."""

    from scripts.function_tracer_pcode.proof.strategies.pairwise_services._shared import (
        _MethodBCoveringCaseProof,
    )

    if type(covering) is not _MethodBCoveringCaseProof:
        raise TypeError("loop exact completion requires exact covering proof object")
    proof = covering.exact_proof
    count_values = tuple(
        sorted({
            int(value)
            for value in tuple(proof.count_values or (proof.count_value,))
            if int(value) > 0
        })
    )
    if not count_values:
        raise ValueError("loop exact covering proof has no positive count value")
    return (
        "loop_exact_term_structural_proof_v2",
        ("exact_side", covering.exact_side),
        ("summary_side", covering.summary_side),
        ("exact_case", _loop_case_object_identity(covering.exact_case)),
        ("summary_case", _loop_case_object_identity(covering.summary_case)),
        ("count_values", count_values),
        ("exact_terms", tuple(term.stable_key() for term in proof.exact_terms)),
        ("expected_terms", tuple(term.stable_key() for term in proof.expected_terms)),
        ("constant_bias", int(proof.constant_bias)),
        ("result_size", int(proof.result_size)),
        ("covering_evidence", proof.evidence),
    )


def _sealed_pairwise_structural_validator() -> Any:
    """Return a receiver backed only by module-load-pinned service functions."""

    return _SealedPairwiseStructuralValidator()


@dataclass(frozen=True, init=False)
class LoopExactTermRelationCompletionSignal:
    blocker: LoopBlockerProductionSignal
    structural_proof_body: tuple[Any, ...]
    dependency_proof_ids: tuple[str, ...]
    producer_contract_id: str
    producer_contract_version: int
    encoding_version: str

    def __init__(
        self,
        blocker: LoopBlockerProductionSignal,
        structural_proof_body: tuple[Any, ...],
        dependency_proof_ids: Iterable[str],
        producer_contract_id: str,
        producer_contract_version: int,
        encoding_version: str,
        *,
        _factory_token: object = None,
    ) -> None:
        if _factory_token is not _LOOP_EXACT_TERM_SIGNAL_TOKEN:
            raise TypeError("loop exact term completion signal must be factory issued")
        for name, value in (
            ("blocker", blocker),
            ("structural_proof_body", structural_proof_body),
            ("dependency_proof_ids", tuple(dependency_proof_ids)),
            ("producer_contract_id", producer_contract_id),
            ("producer_contract_version", producer_contract_version),
            ("encoding_version", encoding_version),
        ):
            object.__setattr__(self, name, value)
        if type(blocker) is not LoopBlockerProductionSignal or blocker.reason_id != (
            "loop_exact_summary_relation_unproven"
        ):
            raise TypeError("loop exact term completion requires exact blocker")
        if producer_contract_id != "loop-exact-term-relation-validator-v2" or (
            producer_contract_version != 2
        ):
            raise ValueError("loop exact term producer contract mismatch")
        if encoding_version != "loop-exact-term-relation-encoding-v2":
            raise ValueError("loop exact term encoding version mismatch")
        authority_digest(structural_proof_body)
        if any(type(item) is not str or not item for item in self.dependency_proof_ids):
            raise TypeError("loop exact term dependency identity is incomplete")

    @classmethod
    def from_pairwise_cases(
        cls,
        blocker: LoopBlockerProductionSignal,
        case1: Any,
        case2: Any,
        *,
        dependency_proof_ids: Iterable[str] = (),
    ) -> "LoopExactTermRelationCompletionSignal":
        from scripts.function_tracer_pcode.proof.strategies.pairwise_models import ReturnCase

        if type(case1) is not ReturnCase or type(case2) is not ReturnCase:
            raise TypeError("loop exact term factory requires exact return cases")
        validator = _sealed_pairwise_structural_validator()
        covering = validator._method_b_covering_case_proof(case1, case2)
        if covering is None:
            raise ValueError("pairwise strategy did not derive an exact covering proof")
        body = _method_b_structural_proof_body(covering)
        exact_key = _loop_case_object_identity(covering.exact_case)
        summary_key = _loop_case_object_identity(covering.summary_case)
        target_cases = {
            blocker.canonical_target_key[3][1],
            blocker.canonical_target_key[4][1],
        }
        if {exact_key, summary_key} != target_cases:
            raise ValueError(
                "loop exact covering proof cases differ from blocker semantic target"
            )
        return cls(
            blocker,
            body,
            dependency_proof_ids,
            "loop-exact-term-relation-validator-v2",
            2,
            "loop-exact-term-relation-encoding-v2",
            _factory_token=_LOOP_EXACT_TERM_SIGNAL_TOKEN,
        )


@dataclass(frozen=True, init=False)
class LoopExactGuardPartitionCompletionSignal:
    blocker: LoopBlockerProductionSignal
    term_completion_signal: Optional[LoopExactTermRelationCompletionSignal]
    term_completion_authority_digest: Optional[str]
    structural_coverage_body: tuple[Any, ...]
    producer_contract_id: str
    producer_contract_version: int
    encoding_version: str

    def __init__(
        self,
        blocker: LoopBlockerProductionSignal,
        term_completion_signal: Optional[LoopExactTermRelationCompletionSignal],
        term_completion_authority_digest: Optional[str],
        structural_coverage_body: tuple[Any, ...],
        producer_contract_id: str,
        producer_contract_version: int,
        encoding_version: str,
        *,
        _factory_token: object = None,
    ) -> None:
        if _factory_token is not _LOOP_EXACT_GUARD_SIGNAL_TOKEN:
            raise TypeError("loop exact guard completion signal must be factory issued")
        for name, value in (
            ("blocker", blocker),
            ("term_completion_signal", term_completion_signal),
            ("term_completion_authority_digest", term_completion_authority_digest),
            ("structural_coverage_body", structural_coverage_body),
            ("producer_contract_id", producer_contract_id),
            ("producer_contract_version", producer_contract_version),
            ("encoding_version", encoding_version),
        ):
            object.__setattr__(self, name, value)
        if (term_completion_signal is None) == (term_completion_authority_digest is None):
            raise TypeError("loop exact guard requires one exact term dependency mode")
        if term_completion_signal is not None and type(
            term_completion_signal
        ) is not LoopExactTermRelationCompletionSignal:
            raise TypeError("loop exact guard completion lacks exact term signal")
        if (
            term_completion_signal is not None
            and blocker != term_completion_signal.blocker
        ):
            raise ValueError("loop exact guard and term blockers differ")
        if term_completion_authority_digest is not None and (
            type(term_completion_authority_digest) is not str
            or not term_completion_authority_digest
        ):
            raise TypeError("loop exact guard term authority digest is incomplete")
        if producer_contract_id != "loop-exact-guard-partition-validator-v2" or (
            producer_contract_version != 2
        ):
            raise ValueError("loop exact guard producer contract mismatch")
        if encoding_version != "loop-exact-guard-partition-encoding-v2":
            raise ValueError("loop exact guard encoding version mismatch")
        authority_digest(structural_coverage_body)

    @classmethod
    def from_pairwise_cases(
        cls,
        term_completion_signal: LoopExactTermRelationCompletionSignal,
        case1: Any,
        case2: Any,
    ) -> "LoopExactGuardPartitionCompletionSignal":
        from scripts.function_tracer_pcode.proof.strategies.pairwise_models import ReturnCase

        if type(case1) is not ReturnCase or type(case2) is not ReturnCase:
            raise TypeError("loop exact guard factory requires exact return cases")
        validator = _sealed_pairwise_structural_validator()
        covering = validator._method_b_covering_case_proof(case1, case2)
        if covering is None:
            raise ValueError("pairwise strategy did not derive an exact covering proof")
        term_body = _method_b_structural_proof_body(covering)
        if term_body != term_completion_signal.structural_proof_body:
            raise ValueError("loop exact guard proof differs from term proof")
        proved_counts = tuple(term_body[5][1])
        if not validator._cases_admit_reduction_count_values(
            covering.exact_case,
            covering.summary_case,
            covering.accumulator_proof,
            proved_counts,
        ):
            raise ValueError("pairwise strategy did not prove exact guard coverage")
        admitted = proved_counts
        coverage_body = (
            "loop_exact_guard_partition_structural_proof_v2",
            ("case_pair_target_digest", authority_digest(
                term_completion_signal.blocker.canonical_target_key
            )),
            ("term_proof_digest", authority_digest(term_body)),
            ("admitted_count_values", admitted),
            ("coverage_proposition", "all_proved_counts_imply_case_partition"),
        )
        return cls(
            term_completion_signal.blocker,
            term_completion_signal,
            None,
            coverage_body,
            "loop-exact-guard-partition-validator-v2",
            2,
            "loop-exact-guard-partition-encoding-v2",
            _factory_token=_LOOP_EXACT_GUARD_SIGNAL_TOKEN,
        )

@dataclass(frozen=True, init=False)
class _LoopExactCompletionAuthorityBase:
    completion_receipt: RequirementCompletionReceipt
    semantic_target_digest: str
    proof_body: tuple[Any, ...]
    dependency_proof_ids: tuple[str, ...]
    producer_contract_id: str
    producer_contract_version: int
    encoding_version: str
    artifact_digest: str

    def _validate(self, expected_proof_kind: str, expected_contract_id: str) -> None:
        if type(self.completion_receipt) is not RequirementCompletionReceipt:
            raise TypeError("loop exact completion lacks exact completion receipt")
        if self.producer_contract_id != expected_contract_id or (
            self.producer_contract_version != 2
        ):
            raise ValueError("loop exact completion producer contract mismatch")
        if expected_proof_kind.replace("_", "-") not in self.encoding_version:
            raise ValueError("loop exact completion encoding/proof mismatch")
        payload = {
            "completion_receipt": self.completion_receipt,
            "semantic_target_digest": self.semantic_target_digest,
            "proof_body": self.proof_body,
            "dependency_proof_ids": self.dependency_proof_ids,
            "producer_contract_id": self.producer_contract_id,
            "producer_contract_version": self.producer_contract_version,
            "encoding_version": self.encoding_version,
        }
        if self.artifact_digest != authority_digest(payload):
            raise ValueError("loop exact completion artifact digest mismatch")


@dataclass(frozen=True, init=False)
class LoopExactTermRelationCompletionAuthority(_LoopExactCompletionAuthorityBase):
    def __init__(self, **values: Any) -> None:
        token = values.pop("_factory_token", None)
        if token is not _LOOP_EXACT_TERM_AUTHORITY_TOKEN:
            raise TypeError("loop exact term authority must be factory issued")
        for name in self.__dataclass_fields__:
            object.__setattr__(self, name, values[name])
        self._validate(
            "loop_exact_term_relation", "loop-exact-term-relation-validator-v2"
        )


@dataclass(frozen=True, init=False)
class LoopExactGuardPartitionCompletionAuthority(_LoopExactCompletionAuthorityBase):
    term_completion_artifact_digest: str

    def __init__(self, **values: Any) -> None:
        token = values.pop("_factory_token", None)
        if token is not _LOOP_EXACT_GUARD_AUTHORITY_TOKEN:
            raise TypeError("loop exact guard authority must be factory issued")
        for name in self.__dataclass_fields__:
            object.__setattr__(self, name, values[name])
        self._validate(
            "loop_exact_guard_partition", "loop-exact-guard-partition-validator-v2"
        )
        if self.term_completion_artifact_digest not in self.dependency_proof_ids:
            raise ValueError("loop exact guard authority lacks exact term dependency")


@dataclass(frozen=True, init=False)
class RecurrenceValidationCompletionSignal:
    blocker: LoopBlockerProductionSignal
    source_analysis: Any
    successor_analysis: Any
    proposal: Any
    seed_core: Any
    validated_entry: Any
    producer_id: str

    def __init__(
        self,
        blocker: LoopBlockerProductionSignal,
        source_analysis: Any,
        successor_analysis: Any,
        proposal: Any,
        seed_core: Any,
        validated_entry: Any,
        *,
        _factory_token: object = None,
    ) -> None:
        if _factory_token is not _RECURRENCE_COMPLETION_SIGNAL_TOKEN:
            raise TypeError("recurrence completion signal must be promotion-factory issued")
        for name, value in (
            ("blocker", blocker),
            ("source_analysis", source_analysis),
            ("successor_analysis", successor_analysis),
            ("proposal", proposal),
            ("seed_core", seed_core),
            ("validated_entry", validated_entry),
            ("producer_id", "equivalence_recurrence_validator"),
        ):
            object.__setattr__(self, name, value)
        _validate_recurrence_completion_inputs(self)

    @classmethod
    def from_side_promotion(cls, side_promotion: Any) -> "RecurrenceValidationCompletionSignal":
        from scripts.function_tracer_pcode.proof.recurrence_promotion import RecurrenceSidePromotion

        if type(side_promotion) is not RecurrenceSidePromotion:
            raise TypeError("recurrence completion requires exact side promotion")
        if (
            side_promotion.proposal is None
            or side_promotion.seed_core is None
            or side_promotion.entry is None
        ):
            raise ValueError("recurrence completion requires a validated promoted side")
        blocker = LoopBlockerProductionSignal.from_recurrence_proposal(
            side_promotion.source_analysis, side_promotion.proposal
        )
        return cls(
            blocker,
            side_promotion.source_analysis,
            side_promotion.successor_analysis,
            side_promotion.proposal,
            side_promotion.seed_core,
            side_promotion.entry,
            _factory_token=_RECURRENCE_COMPLETION_SIGNAL_TOKEN,
        )

    def _phase7_signal_authority(self) -> Mapping[str, Any]:
        """Bind completion identity without serializing live Ghidra objects."""

        from scripts.function_tracer_pcode.proof.obligations.snapshot import AnalysisSnapshot

        artifact = self.validated_entry.artifact
        artifact_authority = {
            "artifact_id": artifact.artifact_id,
            "requirement_key": artifact.requirement_id.to_key(),
            "produced_from_view_id": artifact.produced_from_view_id,
            "premise_digest": artifact.premise_digest,
            "dependency_artifact_ids": artifact.dependency_artifact_ids,
            "producer_id": artifact.producer_id,
            "producer_version": artifact.producer_version,
            "encoding_version": artifact.encoding_version,
            "artifact_validation_status": artifact.artifact_validation_status,
            "payload": artifact.payload,
        }
        return {
            "blocker": self.blocker._phase7_signal_authority(),
            "source_snapshot_fingerprint": AnalysisSnapshot.from_function_analysis(
                self.source_analysis
            ).semantic_fingerprint,
            "successor_snapshot_fingerprint": AnalysisSnapshot.from_function_analysis(
                self.successor_analysis
            ).semantic_fingerprint,
            "successor_analysis_view_identity": (
                self.successor_analysis.analysis_view_identity
            ),
            "successor_partition_revision": int(
                self.successor_analysis.partition_revision
            ),
            "proposal_digest": self.proposal.digest,
            "seed_core_digest": self.seed_core.digest,
            "validated_entry": {
                "domain": self.validated_entry.domain,
                "function_premise_digest": (
                    self.validated_entry.function_premise_digest
                ),
                "function_snapshot_fingerprint": (
                    self.validated_entry.function_snapshot_fingerprint
                ),
                "semantic_seed_digest": self.validated_entry.semantic_seed_digest,
                "normalization_policy_digest": (
                    self.validated_entry.normalization_policy_digest
                ),
                "attempt_candidate_independent": (
                    self.validated_entry.attempt_candidate_independent
                ),
                "pair_independent": self.validated_entry.pair_independent,
                "premise_schema_id": self.validated_entry.premise_schema_id,
                "premise_codec_id": self.validated_entry.premise_codec_id,
                "proposal_digest": self.validated_entry.proposal_digest,
                "function_recurrence_binding_digest": (
                    self.validated_entry.function_recurrence_binding_digest
                ),
                "artifact_digest": authority_digest(artifact_authority),
            },
        }

def _validate_recurrence_completion_inputs(
    signal: RecurrenceValidationCompletionSignal,
) -> None:
    from scripts.function_tracer_pcode.core.analysis import FunctionReturnAnalysis
    from scripts.function_tracer_pcode.core.recurrence_contracts import (
        QuarantinedRecurrenceProposal,
        RecurrenceSeedCore,
    )
    from scripts.function_tracer_pcode.proof.obligations.cache import ValidatedUnaryArtifactEntry
    from scripts.function_tracer_pcode.proof.obligations.recurrence import (
        validate_recurrence_artifact_content,
        validate_recurrence_requirement_binding,
    )
    from scripts.function_tracer_pcode.proof.obligations.snapshot import AnalysisSnapshot

    if type(signal.blocker) is not LoopBlockerProductionSignal:
        raise TypeError("recurrence completion blocker is not exact")
    if signal.blocker.reason_id != "recurrence_proposal_validation_unproven":
        raise ValueError("recurrence completion targets the wrong reason")
    if type(signal.source_analysis) is not FunctionReturnAnalysis or type(
        signal.successor_analysis
    ) is not FunctionReturnAnalysis:
        raise TypeError("recurrence completion analyses are not exact")
    if type(signal.proposal) is not QuarantinedRecurrenceProposal or type(
        signal.seed_core
    ) is not RecurrenceSeedCore:
        raise TypeError("recurrence completion proposal/seed is not exact")
    if type(signal.validated_entry) is not ValidatedUnaryArtifactEntry:
        raise TypeError("recurrence completion entry is not exact")
    entry = signal.validated_entry
    artifact = entry.artifact
    if not artifact.is_validated:
        raise ValueError("recurrence completion artifact is not validated")
    source_snapshot = AnalysisSnapshot.from_function_analysis(signal.source_analysis)
    if (
        entry.function_snapshot_fingerprint != source_snapshot.semantic_fingerprint
        or entry.semantic_seed_digest != signal.seed_core.digest
        or entry.proposal_digest != signal.proposal.digest
        or artifact.producer_id != "equivalence_recurrence_validator"
        or artifact.producer_version != "1"
        or artifact.encoding_version != "recurrence_digest_codec_v1"
    ):
        raise ValueError("recurrence completion entry authority mismatch")
    binding = entry.function_recurrence_binding_digest
    if type(binding) is not str or not binding:
        raise ValueError("recurrence completion binding digest is missing")
    validate_recurrence_requirement_binding(
        artifact.requirement_id,
        seed_core_digest=signal.seed_core.digest,
        proposal_digest=signal.proposal.digest,
        function_recurrence_binding_digest=binding,
    )
    validate_recurrence_artifact_content(
        artifact,
        seed_core_digest=signal.seed_core.digest,
        proposal_digest=signal.proposal.digest,
        function_recurrence_binding_digest=binding,
        proposal=signal.proposal,
    )
    if signal.successor_analysis.analysis_view_identity is None:
        raise ValueError("recurrence successor lineage is missing")
    if int(signal.successor_analysis.partition_revision) <= int(
        signal.source_analysis.partition_revision
    ):
        raise ValueError("recurrence successor revision did not advance")


@dataclass(frozen=True, init=False)
class RecurrenceRequirementBindingReceipt:
    v2_proof_requirement_id: str
    v2_semantic_target_digest: str
    legacy_requirement_key: Any
    original_function_snapshot: str
    successor_analysis_view_identity: Any
    successor_partition_revision: int
    accepted_candidate_digest: str
    function_recurrence_binding_digest: str
    semantic_closure_digest: str
    receipt_digest: str

    def __init__(
        self,
        v2_proof_requirement_id: str,
        v2_semantic_target_digest: str,
        legacy_requirement_key: Any,
        original_function_snapshot: str,
        successor_analysis_view_identity: Any,
        successor_partition_revision: int,
        accepted_candidate_digest: str,
        function_recurrence_binding_digest: str,
        semantic_closure_digest: str,
        receipt_digest: str,
        *,
        _factory_token: object = None,
    ) -> None:
        if _factory_token is not _RECURRENCE_BINDING_TOKEN:
            raise TypeError("recurrence requirement binding must be factory issued")
        for name, value in (
            ("v2_proof_requirement_id", v2_proof_requirement_id),
            ("v2_semantic_target_digest", v2_semantic_target_digest),
            ("legacy_requirement_key", legacy_requirement_key),
            ("original_function_snapshot", original_function_snapshot),
            ("successor_analysis_view_identity", successor_analysis_view_identity),
            ("successor_partition_revision", successor_partition_revision),
            ("accepted_candidate_digest", accepted_candidate_digest),
            ("function_recurrence_binding_digest", function_recurrence_binding_digest),
            ("semantic_closure_digest", semantic_closure_digest),
            ("receipt_digest", receipt_digest),
        ):
            object.__setattr__(self, name, value)
        self.validate()

    def _payload(self) -> dict[str, Any]:
        return {
            name: getattr(self, name)
            for name in self.__dataclass_fields__
            if name not in {"receipt_digest"}
        }

    def validate(self) -> None:
        for value in (
            self.v2_proof_requirement_id,
            self.v2_semantic_target_digest,
            self.original_function_snapshot,
            self.accepted_candidate_digest,
            self.function_recurrence_binding_digest,
            self.semantic_closure_digest,
        ):
            if type(value) is not str or not value:
                raise TypeError("recurrence binding receipt identity is incomplete")
        if type(self.successor_partition_revision) is not int or (
            self.successor_partition_revision <= 0
        ):
            raise TypeError("recurrence binding successor revision is invalid")
        if self.receipt_digest != authority_digest(self._payload()):
            raise ValueError("recurrence binding receipt digest mismatch")


@dataclass(frozen=True, init=False)
class RecurrenceValidationCompletionAuthority:
    binding_receipt: RecurrenceRequirementBindingReceipt
    proof_artifact_id: Any
    proof_artifact_digest: str
    completion_receipt: RequirementCompletionReceipt
    authority_digest_value: str

    def __init__(
        self,
        binding_receipt: RecurrenceRequirementBindingReceipt,
        proof_artifact_id: Any,
        proof_artifact_digest: str,
        completion_receipt: RequirementCompletionReceipt,
        authority_digest_value: str,
        *,
        _factory_token: object = None,
    ) -> None:
        if _factory_token is not _RECURRENCE_COMPLETION_AUTHORITY_TOKEN:
            raise TypeError("recurrence completion authority must be factory issued")
        for name, value in (
            ("binding_receipt", binding_receipt),
            ("proof_artifact_id", proof_artifact_id),
            ("proof_artifact_digest", proof_artifact_digest),
            ("completion_receipt", completion_receipt),
            ("authority_digest_value", authority_digest_value),
        ):
            object.__setattr__(self, name, value)
        self.validate()

    def _payload(self) -> dict[str, Any]:
        return {
            "binding_receipt_digest": self.binding_receipt.receipt_digest,
            "proof_artifact_id": self.proof_artifact_id,
            "proof_artifact_digest": self.proof_artifact_digest,
            "completion_receipt": self.completion_receipt,
        }

    def validate(self) -> None:
        if type(self.binding_receipt) is not RecurrenceRequirementBindingReceipt:
            raise TypeError("recurrence completion lacks exact binding receipt")
        self.binding_receipt.validate()
        if type(self.completion_receipt) is not RequirementCompletionReceipt:
            raise TypeError("recurrence completion lacks exact completion receipt")
        if (
            self.completion_receipt.proof_requirement_id
            != self.binding_receipt.v2_proof_requirement_id
            or self.completion_receipt.proof_artifact_digest
            != self.proof_artifact_digest
        ):
            raise ValueError("recurrence completion receipt does not join binding/artifact")
        if self.authority_digest_value != authority_digest(self._payload()):
            raise ValueError("recurrence completion authority digest mismatch")


class LoopRecurrencePilotEncoder:
    """Creates C_active/Q_open authority from exact slice4 producer signals."""

    def __init__(self) -> None:
        self._cause_factory = SemanticCauseIdentityFactory(LOOP_REASON_REGISTRY)
        self._binding_factory = SatisfactionBindingFactory(LOOP_RECOVERY_REGISTRY)

    def validate_startup(self) -> Any:
        from scripts.function_tracer_pcode.authority.lifecycle.execution_authority import (
            validate_execution_authority_deployment,
        )

        return validate_execution_authority_deployment()

    @staticmethod
    def _committed_ledger(session: Any, key: str) -> set[str]:
        ledger = session.domain_signal_state.get(key)
        if ledger is None:
            return set()
        if type(ledger) is not set:
            raise TypeError(f"loop committed ledger is not an exact set: {key}")
        return ledger

    @classmethod
    def _observed(cls, session: Any) -> set[str]:
        return cls._committed_ledger(session, "loop_recurrence_observed")

    @classmethod
    def _completed(cls, session: Any) -> set[str]:
        return cls._committed_ledger(session, "loop_recurrence_completed")

    @classmethod
    def _completed_requirements(cls, session: Any) -> set[str]:
        return cls._committed_ledger(
            session, "loop_recurrence_completed_requirements"
        )

    @staticmethod
    def _register_emission_plan(
        session: Any,
        signal: Any,
        intents: tuple[EventIntent, ...],
        action: str,
        payload: Mapping[str, Any],
    ) -> None:
        pending_key = "loop_recurrence_pending_emission_transactions"
        pending = session.domain_signal_state.setdefault(pending_key, {})
        if type(pending) is not dict:
            raise TypeError("loop pending emission ledger is not exact")
        if id(signal) in pending:
            raise ValueError("loop signal already owns an emission transaction")
        pending[id(signal)] = (intents, action, dict(payload))

    def authority_for_signal(
        self, session: Any, signal: LoopBlockerProductionSignal
    ) -> CauseOccurrenceAuthority:
        if type(signal) is not LoopBlockerProductionSignal:
            raise TypeError("loop encoder requires an exact blocker signal")
        spec = LOOP_REASON_SPECS[signal.reason_id]
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
        bindings: dict[str, ProofRequirement] = {}
        if signal.reason_id == "loop_exact_summary_relation_unproven":
            slot_names = ("loop_exact_term_relation", "loop_exact_guard_partition")
        else:
            slot_names = ("proof",)
        for slot_name, proof_kind in zip(slot_names, spec.proof_kinds):
            requirement_id = "loop-q-" + authority_digest({
                "cause_id": cause.value,
                "slot": slot_name,
                "proof_kind": proof_kind,
            })[:32]
            bindings[slot_name] = ProofRequirement(
                requirement_id,
                proof_kind,
                (
                    "loop_semantic_target_v2",
                    signal.canonical_target_key,
                    signal.missing_semantic_fact,
                    proof_kind,
                ),
            )
        bound = self._binding_factory.bind(
            contract_definition_id=spec.contract_definition_id,
            contract_version=1,
            bindings=bindings,
        )
        occurrence_id = "loop-occ-" + authority_digest({
            "cause_id": cause.value,
            "result_occurrence_id": session.identity.result_occurrence_id,
        })[:32]
        occurrence = CauseOccurrence(
            occurrence_id,
            cause,
            signal.reason_id,
            authority_digest(signal.canonical_target_key),
            signal.target_kind,
            signal.identity_scope,
            bound.contract_definition_id,
            bound.contract_version,
            bound.normalized_expression_digest,
            bound.bound_expression_digest,
            tuple(item.requirement_id for item in bindings.values()),
            signal.evidence_refs,
            "loop_recurrence_producer_signal",
            session.identity.source_snapshot_fingerprint,
            signal.producer_id,
            session.identity.execution_identity_digest,
        )
        return CauseOccurrenceAuthority(occurrence, bound)

    def requirement_for_signal(
        self,
        session: Any,
        blocker: LoopBlockerProductionSignal,
        proof_kind: str,
    ) -> ProofRequirement:
        authority = self.authority_for_signal(session, blocker)
        return self._requirement_for_kind(authority, proof_kind)

    def _issue_recurrence_completion(
        self,
        session: Any,
        signal: RecurrenceValidationCompletionSignal,
    ) -> RecurrenceValidationCompletionAuthority:
        from scripts.function_tracer_pcode.proof.obligations.snapshot import AnalysisSnapshot

        _validate_recurrence_completion_inputs(signal)
        occurrence_authority = self.authority_for_signal(session, signal.blocker)
        occurrence = occurrence_authority.occurrence
        slot_bindings = occurrence_authority.bound_contract.slot_bindings
        if len(slot_bindings) != 1:
            raise ValueError("recurrence proposal completion requires one exact Q row")
        requirement = slot_bindings[0][1]
        artifact = signal.validated_entry.artifact
        source_snapshot = AnalysisSnapshot.from_function_analysis(signal.source_analysis)
        candidate_digest = authority_digest(tuple(
            item.to_dict()
            for item in tuple(signal.successor_analysis.summary_return_candidates or ())
        ))
        closure = str(artifact.payload.get("semantic_closure_digest") or "")
        binding_payload = {
            "v2_proof_requirement_id": requirement.requirement_id,
            "v2_semantic_target_digest": authority_digest(requirement.semantic_target_key),
            "legacy_requirement_key": artifact.requirement_id.to_key(),
            "original_function_snapshot": source_snapshot.semantic_fingerprint,
            "successor_analysis_view_identity": signal.successor_analysis.analysis_view_identity,
            "successor_partition_revision": int(signal.successor_analysis.partition_revision),
            "accepted_candidate_digest": candidate_digest,
            "function_recurrence_binding_digest": str(
                signal.validated_entry.function_recurrence_binding_digest or ""
            ),
            "semantic_closure_digest": closure,
        }
        binding = RecurrenceRequirementBindingReceipt(
            **binding_payload,
            receipt_digest=authority_digest(binding_payload),
            _factory_token=_RECURRENCE_BINDING_TOKEN,
        )
        proof_artifact_digest = authority_digest({
            "artifact_id": artifact.artifact_id,
            "requirement_key": artifact.requirement_id.to_key(),
            "produced_from_view_id": artifact.produced_from_view_id,
            "premise_digest": artifact.premise_digest,
            "producer_id": artifact.producer_id,
            "producer_version": artifact.producer_version,
            "encoding_version": artifact.encoding_version,
            "artifact_validation_status": artifact.artifact_validation_status,
            "payload": artifact.payload,
        })
        completion = RequirementCompletionReceipt(
            occurrence.cause_id.value,
            occurrence.occurrence_id,
            requirement.requirement_id,
            occurrence_authority.bound_contract.contract_definition_id,
            occurrence_authority.bound_contract.contract_version,
            occurrence_authority.bound_contract.bound_expression_digest,
            proof_artifact_digest,
            binding.receipt_digest,
        )
        completion.validate_against(
            occurrence,
            occurrence_authority.bound_contract,
            (requirement.requirement_id,),
        )
        payload = {
            "binding_receipt_digest": binding.receipt_digest,
            "proof_artifact_id": artifact.artifact_id,
            "proof_artifact_digest": proof_artifact_digest,
            "completion_receipt": completion,
        }
        return RecurrenceValidationCompletionAuthority(
            binding,
            artifact.artifact_id,
            proof_artifact_digest,
            completion,
            authority_digest(payload),
            _factory_token=_RECURRENCE_COMPLETION_AUTHORITY_TOKEN,
        )

    def build_execution_context(
        self,
        session: Any,
        blocker: LoopBlockerProductionSignal,
        queries: Iterable[LoopSolverQueryAuthority],
    ) -> LoopSolverExecutionContext:
        if type(blocker) is not LoopBlockerProductionSignal:
            raise TypeError("loop execution context requires exact blocker")
        authority = self.authority_for_signal(session, blocker)
        if authority.occurrence.occurrence_id not in self._observed(session):
            raise ValueError("loop blocker was not observed before solver execution")
        typed_queries = tuple(queries)
        if not typed_queries or any(
            type(item) is not LoopSolverQueryAuthority for item in typed_queries
        ):
            raise TypeError("loop execution context requires exact typed queries")
        if len({item.proof_kind for item in typed_queries}) != len(typed_queries):
            raise ValueError("loop execution context repeats a proof kind")
        projection = session.preview_lifecycle_projection()
        owned_ids = frozenset(authority.occurrence.proof_requirement_ids)
        rows = {
            row.proof_kind: row
            for row in projection.q_open_base
            if row.proof_requirement_id in owned_ids
            and row.proof_kind in {item.proof_kind for item in typed_queries}
        }
        if len(rows) != len(typed_queries):
            raise ValueError("loop execution context lacks exact live stage frontier")
        return LoopSolverExecutionContext(
            projection,
            session.identity.result_occurrence_id,
            rows,
        )

    @staticmethod
    def _requirement_for_kind(
        occurrence_authority: CauseOccurrenceAuthority, proof_kind: str
    ) -> ProofRequirement:
        matches = tuple(
            requirement
            for _, requirement in occurrence_authority.bound_contract.slot_bindings
            if requirement.proof_kind == proof_kind
        )
        if len(matches) != 1:
            raise ValueError("loop exact completion lacks one exact live Q binding")
        return matches[0]

    def _issue_loop_exact_completion(
        self, session: Any, signal: Any
    ) -> Any:
        if type(signal) is LoopExactTermRelationCompletionSignal:
            proof_kind = "loop_exact_term_relation"
            proof_body = signal.structural_proof_body
            dependency_ids = signal.dependency_proof_ids
            producer_id = signal.producer_contract_id
            producer_version = signal.producer_contract_version
            encoding_version = signal.encoding_version
            authority_type = LoopExactTermRelationCompletionAuthority
            authority_token = _LOOP_EXACT_TERM_AUTHORITY_TOKEN
        elif type(signal) is LoopExactGuardPartitionCompletionSignal:
            proof_kind = "loop_exact_guard_partition"
            proof_body = signal.structural_coverage_body
            producer_id = signal.producer_contract_id
            producer_version = signal.producer_contract_version
            encoding_version = signal.encoding_version
            term_authorities = tuple(
                item
                for item in session.domain_signal_state.get(
                    "loop_exact_completion_authorities", ()
                )
                if type(item) is LoopExactTermRelationCompletionAuthority
                and item.completion_receipt.occurrence_id
                == self.authority_for_signal(session, signal.blocker).occurrence.occurrence_id
            )
            if len(term_authorities) != 1:
                raise ValueError(
                    "loop exact guard completion requires prior exact term authority"
                )
            term_signal = signal.term_completion_signal
            if term_signal is not None:
                expected_term_proof_digest = authority_digest({
                    "semantic_target_digest": authority_digest(
                        term_signal.blocker.canonical_target_key
                    ),
                    "proof_body": term_signal.structural_proof_body,
                    "dependency_proof_ids": term_signal.dependency_proof_ids,
                    "producer_contract_id": term_signal.producer_contract_id,
                    "producer_contract_version": term_signal.producer_contract_version,
                    "encoding_version": term_signal.encoding_version,
                })
                if (
                    term_authorities[0].proof_body
                    != term_signal.structural_proof_body
                    or term_authorities[0].semantic_target_digest
                    != authority_digest(term_signal.blocker.canonical_target_key)
                    or term_authorities[0].completion_receipt.proof_artifact_digest
                    != expected_term_proof_digest
                ):
                    raise ValueError(
                        "loop exact guard signal does not join prior term authority"
                    )
            elif signal.term_completion_authority_digest != (
                term_authorities[0].artifact_digest
            ):
                raise ValueError(
                    "loop exact guard signal differs from prior term authority"
                )
            dependency_ids = (
                *(
                    signal.term_completion_signal.dependency_proof_ids
                    if signal.term_completion_signal is not None
                    else ()
                ),
                term_authorities[0].artifact_digest,
            )
            authority_type = LoopExactGuardPartitionCompletionAuthority
            authority_token = _LOOP_EXACT_GUARD_AUTHORITY_TOKEN
        else:
            raise TypeError("loop exact completion signal type is not registered")

        occurrence_authority = self.authority_for_signal(session, signal.blocker)
        occurrence = occurrence_authority.occurrence
        if occurrence.occurrence_id not in self._observed(session):
            raise ValueError("loop exact completion has no observed live occurrence")
        requirement = self._requirement_for_kind(occurrence_authority, proof_kind)
        completed_requirements = self._completed_requirements(session)
        if requirement.requirement_id in completed_requirements:
            return None
        semantic_target_digest = authority_digest(signal.blocker.canonical_target_key)
        applicability_receipt = authority_digest({
            "occurrence_id": occurrence.occurrence_id,
            "requirement_id": requirement.requirement_id,
            "semantic_target_digest": semantic_target_digest,
            "source_snapshot": session.identity.source_snapshot_fingerprint,
            "observation_surface": signal.blocker.observation_surface,
            "active_precondition": signal.blocker.active_semantic_precondition,
        })
        artifact_payload = {
            "semantic_target_digest": semantic_target_digest,
            "proof_body": proof_body,
            "dependency_proof_ids": tuple(dependency_ids),
            "producer_contract_id": producer_id,
            "producer_contract_version": producer_version,
            "encoding_version": encoding_version,
        }
        proof_artifact_digest = authority_digest(artifact_payload)
        completion = RequirementCompletionReceipt(
            occurrence.cause_id.value,
            occurrence.occurrence_id,
            requirement.requirement_id,
            occurrence_authority.bound_contract.contract_definition_id,
            occurrence_authority.bound_contract.contract_version,
            occurrence_authority.bound_contract.bound_expression_digest,
            proof_artifact_digest,
            applicability_receipt,
        )
        completion.validate_against(
            occurrence,
            occurrence_authority.bound_contract,
            (requirement.requirement_id,),
        )
        authority_payload = {
            "completion_receipt": completion,
            **artifact_payload,
        }
        authority_values = {
            **authority_payload,
            "artifact_digest": authority_digest(authority_payload),
            "_factory_token": authority_token,
        }
        if authority_type is LoopExactGuardPartitionCompletionAuthority:
            authority_values["term_completion_artifact_digest"] = dependency_ids[-1]
        authority = authority_type(**authority_values)
        return authority

    def _solver_batch_intents(
        self, session: Any, batch: LoopSolverExecutionBatchSignal
    ) -> tuple[EventIntent, ...]:
        if type(batch) is not LoopSolverExecutionBatchSignal:
            raise TypeError("loop solver encoder requires exact batch signal")
        occurrence_authority = self.authority_for_signal(session, batch.blocker)
        occurrence = occurrence_authority.occurrence
        if occurrence.occurrence_id not in self._observed(session):
            raise ValueError("loop solver batch has no observed live occurrence")
        requirement = self._requirement_for_kind(
            occurrence_authority, batch.query_authority.proof_kind
        )
        assignment = batch.membership.requirement_assignment
        if (
            assignment.occurrence_id != occurrence.occurrence_id
            or assignment.cause_id != occurrence.cause_id.value
            or assignment.proof_requirement_id != requirement.requirement_id
        ):
            raise ValueError("loop solver assignment differs from blocker authority")
        observation_intents: list[EventIntent] = []
        completion_intents: list[EventIntent] = []
        state = session.domain_signal_state
        completed = state.get("loop_recurrence_completed_requirements", set())
        seen = state.get("loop_solver_execution_receipts", set())
        if type(completed) is not set or type(seen) is not set:
            raise TypeError("loop solver transaction ledgers are not exact sets")
        fresh_receipts = tuple(
            receipt for receipt in batch.execution_receipts
            if receipt.receipt_digest not in seen
        )
        projected_completed = set(completed)
        commit_payload = {
            "fresh_receipt_digests": tuple(
                receipt.receipt_digest for receipt in fresh_receipts
            ),
            "completed_requirement_ids": [],
            "model_artifacts": [],
            "sat_safety_handoffs": [],
            "exact_completion_authorities": [],
            "unsat_completion_receipts": [],
        }
        for receipt in fresh_receipts:
            if receipt.observed_status in {"unknown", "timeout", "error"}:
                event_type = {
                    "unknown": EventType.SOLVER_UNKNOWN,
                    "timeout": EventType.SOLVER_TIMEOUT,
                    "error": EventType.SOLVER_ERROR,
                }[receipt.observed_status]
                observation_intents.append(EventIntent(
                    event_type,
                    GenericReceiptBoundSolverExecutionEventAuthority(
                        requirement.requirement_id,
                        receipt.to_authority_dict(),
                        receipt.observed_status == "timeout",
                    ),
                ))
                continue
            if receipt.observed_status == "sat":
                if receipt.model_digest is None or receipt.model_authority is None:
                    raise ValueError("loop SAT result lacks model-bound handoff authority")
                from scripts.function_tracer_pcode.authority.lifecycle.execution_authority import (
                    ModelBoundRelationalRefutationArtifact,
                    PINNED_RELATIONAL_WITNESS_VERIFIER,
                )
                from scripts.function_tracer_pcode.authority.lifecycle.production_signals import (
                    SatSafetyBlockerProductionSignal,
                )

                premise = {"assertions": batch.query_authority.premise_assertions}
                stage_input = {
                    "declarations": batch.query_authority.declaration_rows
                }
                replay = PINNED_RELATIONAL_WITNESS_VERIFIER.issue(
                    receipt,
                    registry=LOOP_COMMON_EXECUTION_STAGE_REGISTRY,
                    membership=batch.membership,
                    obligation_id=batch.query_authority.obligation_id,
                    prepared_surface_digest=(
                        batch.query_authority.prepared_surface_digest
                    ),
                    observation_contract_id=(
                        batch.query_authority.observation_contract_id
                    ),
                    normalized_assertion=(
                        batch.query_authority.normalized_assertion_text
                    ),
                    premise=premise,
                    stage_input=stage_input,
                    model=receipt.model_authority,
                    configured_timeout_ms=receipt.configured_timeout_ms or 1000,
                    lifecycle_projection=batch.lifecycle_projection,
                )
                artifact = ModelBoundRelationalRefutationArtifact.create(
                    obligation_id=batch.query_authority.obligation_id,
                    source_snapshot_digests=(
                        batch.query_authority.source_snapshot_digests
                    ),
                    prepared_surface_digest=(
                        batch.query_authority.prepared_surface_digest
                    ),
                    observation_contract_id=(
                        batch.query_authority.observation_contract_id
                    ),
                    normalized_assertion=(
                        batch.query_authority.normalized_assertion_text
                    ),
                    premise=premise,
                    stage_input=stage_input,
                    applicability=replay.applicability_authority,
                    producer_version="loop-model-bound-refutation-v1",
                    encoding_version="loop-pair-value-replay-v1",
                    dependency_proof_ids=(receipt.receipt_digest,),
                    sat_execution_receipt=receipt,
                    replay_receipt=replay,
                    registry=LOOP_COMMON_EXECUTION_STAGE_REGISTRY,
                    membership=batch.membership,
                )
                artifact.validate(
                    PINNED_RELATIONAL_WITNESS_VERIFIER,
                    LOOP_COMMON_EXECUTION_STAGE_REGISTRY,
                    batch.membership,
                )
                commit_payload["model_artifacts"].append(artifact)
                commit_payload["sat_safety_handoffs"].append(
                    SatSafetyBlockerProductionSignal(
                    "OBSERVED",
                    "counterexample_analysis_safety_unproven",
                    (
                        "loop_model_bound_refutation",
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
                    "loop-model-bound-refutation-handoff-v1",
                    )
                )
                continue
            if receipt.observed_status != "unsat":
                raise ValueError("loop solver receipt status is not sealed")
            if requirement.requirement_id in projected_completed:
                continue
            if batch.query_authority.proof_kind == "loop_exact_guard_partition":
                term = self._requirement_for_kind(
                    occurrence_authority, "loop_exact_term_relation"
                )
                if term.requirement_id not in projected_completed:
                    raise ValueError(
                        "loop solver guard UNSAT requires prior exact term completion"
                    )
            proof_artifact_digest = authority_digest({
                "proof_kind": requirement.proof_kind,
                "query_authority_digest": batch.query_authority.authority_digest,
                "execution_receipt_digest": receipt.receipt_digest,
                "validated_status": "unsat",
            })
            completion = RequirementCompletionReceipt(
                occurrence.cause_id.value,
                occurrence.occurrence_id,
                requirement.requirement_id,
                occurrence_authority.bound_contract.contract_definition_id,
                occurrence_authority.bound_contract.contract_version,
                occurrence_authority.bound_contract.bound_expression_digest,
                proof_artifact_digest,
                authority_digest({
                    "assignment_digest": assignment.assignment_digest,
                    "query_authority_digest": batch.query_authority.authority_digest,
                    "execution_receipt_digest": receipt.receipt_digest,
                }),
            )
            completion.validate_against(
                occurrence,
                occurrence_authority.bound_contract,
                (requirement.requirement_id,),
            )
            projected_completed.add(requirement.requirement_id)
            commit_payload["completed_requirement_ids"].append(
                requirement.requirement_id
            )
            if requirement.proof_kind == "loop_exact_term_relation":
                proof_body = (
                    "loop_exact_term_solver_unsat_proof_v2",
                    ("query_authority_digest", batch.query_authority.authority_digest),
                    ("execution_receipt_digest", receipt.receipt_digest),
                    ("validated_status", "unsat"),
                )
                authority_payload = {
                    "completion_receipt": completion,
                    "semantic_target_digest": authority_digest(
                        batch.blocker.canonical_target_key
                    ),
                    "proof_body": proof_body,
                    "dependency_proof_ids": (receipt.receipt_digest,),
                    "producer_contract_id": (
                        "loop-exact-term-relation-validator-v2"
                    ),
                    "producer_contract_version": 2,
                    "encoding_version": "loop-exact-term-relation-encoding-v2",
                }
                commit_payload["exact_completion_authorities"].append(
                    LoopExactTermRelationCompletionAuthority(
                        **authority_payload,
                        artifact_digest=authority_digest(authority_payload),
                        _factory_token=_LOOP_EXACT_TERM_AUTHORITY_TOKEN,
                    )
                )
            commit_payload["unsat_completion_receipts"].append(completion)
            completion_intents.append(EventIntent(
                EventType.REQUIREMENT_COMPLETED,
                RequirementCompletedEventAuthority(completion),
            ))
        intents = tuple((*observation_intents, *completion_intents))
        pending_key = "loop_solver_pending_emission_transactions"
        pending = state.setdefault(pending_key, {})
        if type(pending) is not dict:
            raise TypeError("loop solver pending transaction ledger is not exact")
        if id(batch) in pending:
            raise ValueError("loop solver signal already owns an emission transaction")
        pending[id(batch)] = (intents, commit_payload)
        return intents

    def commit_emitted_signal(
        self, session: Any, signal: Any, intents: tuple[EventIntent, ...]
    ) -> None:
        if type(signal) is not LoopSolverExecutionBatchSignal:
            self._commit_recurrence_emission_plan(session, signal, intents)
            return
        state = session.domain_signal_state
        pending_key = "loop_solver_pending_emission_transactions"
        pending = state.get(pending_key)
        if type(pending) is not dict:
            raise ValueError("loop solver emission transaction is missing")
        try:
            expected_intents, payload = pending[id(signal)]
        except KeyError as exc:
            raise ValueError("loop solver emission transaction is missing") from exc
        if tuple(intents) != expected_intents:
            raise ValueError("loop solver emission transaction intents changed")
        mutated_keys = (
            "loop_solver_execution_receipts",
            "loop_recurrence_completed_requirements",
            "loop_model_bound_refutation_artifacts",
            "loop_sat_safety_handoffs",
            "loop_exact_completion_authorities",
            "loop_solver_unsat_completion_receipts",
        )
        snapshots = {}
        for key in mutated_keys:
            if key not in state:
                snapshots[key] = (False, None)
            elif type(state[key]) is set:
                snapshots[key] = (True, set(state[key]))
            elif type(state[key]) is list:
                snapshots[key] = (True, list(state[key]))
            else:
                raise TypeError(
                    f"loop solver transaction ledger has invalid type: {key}"
                )
        try:
            self._apply_solver_batch_commit_payload(state, payload)
        except Exception:
            for key, (existed, snapshot) in snapshots.items():
                if existed:
                    state[key] = snapshot
                else:
                    state.pop(key, None)
            raise
        pending.pop(id(signal))
        if not pending:
            state.pop(pending_key, None)

    def _commit_recurrence_emission_plan(
        self, session: Any, signal: Any, intents: tuple[EventIntent, ...]
    ) -> None:
        state = session.domain_signal_state
        pending_key = "loop_recurrence_pending_emission_transactions"
        pending = state.get(pending_key)
        if pending is None:
            if intents:
                raise ValueError("loop emission transaction is missing")
            return
        if type(pending) is not dict:
            raise TypeError("loop pending emission ledger is not exact")
        try:
            expected_intents, action, payload = pending[id(signal)]
        except KeyError as exc:
            if intents:
                raise ValueError(
                    "loop emission transaction is missing"
                ) from exc
            return
        if tuple(intents) != expected_intents:
            raise ValueError("loop emission transaction intents changed")
        mutated_keys = (
            "loop_recurrence_observed",
            "loop_recurrence_completed",
            "loop_recurrence_completed_requirements",
            "recurrence_completion_authorities",
            "loop_exact_completion_authorities",
        )
        snapshots = {}
        for key in mutated_keys:
            if key not in state:
                snapshots[key] = (False, None)
            elif type(state[key]) is set:
                snapshots[key] = (True, set(state[key]))
            elif type(state[key]) is list:
                snapshots[key] = (True, list(state[key]))
            else:
                raise TypeError(
                    f"loop emission transaction ledger has invalid type: {key}"
                )
        try:
            if action == "OBSERVED":
                ledger = state.setdefault("loop_recurrence_observed", set())
                occurrence_id = payload["occurrence_id"]
                if occurrence_id in ledger:
                    raise ValueError("loop observation duplicates committed state")
                ledger.add(occurrence_id)
            elif action == "RECURRENCE_COMPLETED":
                ledger = state.setdefault("loop_recurrence_completed", set())
                occurrence_id = payload["occurrence_id"]
                if occurrence_id in ledger:
                    raise ValueError("recurrence completion duplicates committed state")
                ledger.add(occurrence_id)
                state.setdefault(
                    "recurrence_completion_authorities", []
                ).append(payload["authority"])
            elif action == "EXACT_COMPLETED":
                ledger = state.setdefault(
                    "loop_recurrence_completed_requirements", set()
                )
                requirement_id = payload["requirement_id"]
                if requirement_id in ledger:
                    raise ValueError("loop exact completion duplicates committed state")
                ledger.add(requirement_id)
                state.setdefault(
                    "loop_exact_completion_authorities", []
                ).append(payload["authority"])
            else:
                raise ValueError("loop emission transaction action is invalid")
        except Exception:
            for key, (existed, snapshot) in snapshots.items():
                if existed:
                    state[key] = snapshot
                else:
                    state.pop(key, None)
            raise
        pending.pop(id(signal))
        if not pending:
            state.pop(pending_key, None)

    @staticmethod
    def _apply_solver_batch_commit_payload(
        state: dict[str, Any], payload: Mapping[str, Any]
    ) -> None:
        """Apply one prevalidated loop batch plan inside recorder transaction."""

        state.setdefault("loop_solver_execution_receipts", set()).update(
            payload["fresh_receipt_digests"]
        )
        state.setdefault(
            "loop_recurrence_completed_requirements", set()
        ).update(payload["completed_requirement_ids"])
        for key, payload_key in (
            (
                "loop_model_bound_refutation_artifacts",
                "model_artifacts",
            ),
            ("loop_sat_safety_handoffs", "sat_safety_handoffs"),
            (
                "loop_exact_completion_authorities",
                "exact_completion_authorities",
            ),
            (
                "loop_solver_unsat_completion_receipts",
                "unsat_completion_receipts",
            ),
        ):
            if payload[payload_key]:
                state.setdefault(key, []).extend(payload[payload_key])

    def rollback_emitted_signal(self, session: Any, signal: Any) -> None:
        if type(signal) is not LoopSolverExecutionBatchSignal:
            pending_key = "loop_recurrence_pending_emission_transactions"
            pending = session.domain_signal_state.get(pending_key)
            if pending is None:
                return
            if type(pending) is not dict:
                raise TypeError("loop pending emission ledger is not exact")
            pending.pop(id(signal), None)
            if not pending:
                session.domain_signal_state.pop(pending_key, None)
            return
        state = session.domain_signal_state
        pending_key = "loop_solver_pending_emission_transactions"
        pending = state.get(pending_key)
        if pending is None:
            return
        if type(pending) is not dict:
            raise TypeError("loop solver pending transaction ledger is not exact")
        pending.pop(id(signal), None)
        if not pending:
            state.pop(pending_key, None)

    def finalize_open_execution_history(self, session: Any) -> None:
        from scripts.function_tracer_pcode.authority.lifecycle.execution_authority import (
            PINNED_SOLVER_EXECUTION_ISSUER,
        )

        result_id = session.identity.result_occurrence_id
        if not PINNED_SOLVER_EXECUTION_ISSUER.has_open_result_ledger(
            LOOP_COMMON_EXECUTION_STAGE_REGISTRY, result_id
        ):
            return
        census = PINNED_SOLVER_EXECUTION_ISSUER.seal_result_census(
            LOOP_COMMON_EXECUTION_STAGE_REGISTRY, result_id
        )
        seen = session.domain_signal_state.setdefault(
            "loop_solver_execution_receipts", set()
        )
        for event in census.events:
            receipt = event.execution_receipt
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
        session.domain_signal_state["loop_solver_census"] = census

    def finalize_terminal_timeout_bindings(
        self, session: Any, stream: Any
    ) -> tuple[tuple[int, str], ...]:
        from scripts.function_tracer_pcode.authority.lifecycle.execution_authority import (
            ExecutionAuthorityStartupReceipt,
            SolverExecutionEvidenceBundle,
            TerminalLifecycleProjectionAuthority,
            TerminalTimeoutSelectionReceipt,
        )

        census = session.domain_signal_state.get("loop_solver_census")
        if census is None:
            return ()
        projection = session.reducer.replay(stream).projection
        terminal_projection = TerminalLifecycleProjectionAuthority.create(
            session.identity.result_occurrence_id,
            (row.proof_requirement_id for row in projection.q_open_base),
        )
        selection = TerminalTimeoutSelectionReceipt.select(
            LOOP_COMMON_EXECUTION_STAGE_REGISTRY,
            census,
            terminal_projection,
        )
        startup = tuple(getattr(session, "startup_receipts", ()))
        if len(startup) != 1 or type(startup[0]) is not ExecutionAuthorityStartupReceipt:
            raise ValueError("loop solver evidence lacks one startup receipt")
        observed = tuple(
            event.authority_payload.execution_receipt_digest
            for event in stream.events
            if type(event.authority_payload)
            is GenericReceiptBoundSolverExecutionEventAuthority
        )
        bundle = SolverExecutionEvidenceBundle.seal(
            registry=LOOP_COMMON_EXECUTION_STAGE_REGISTRY,
            startup_receipt=startup[0],
            census=census,
            terminal_projection=terminal_projection,
            terminal_selection=selection,
            final_lifecycle_projection_digest=projection.lifecycle_projection_digest,
            observed_stream_receipt_digests=observed,
        )
        session.domain_signal_state["loop_terminal_timeout_selection"] = selection
        session.domain_signal_state["loop_solver_execution_evidence_bundle"] = bundle
        session.execution_authority_evidence_bundles.append((
            LOOP_COMMON_EXECUTION_STAGE_REGISTRY, bundle
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
            raise ValueError("loop terminal timeout selection lacks one stream event")
        return ((matches[0].header.sequence_number, selection.proof_requirement_id),)

    def __call__(self, session: Any, signal: Any) -> tuple[EventIntent, ...]:
        if type(signal) is LoopSolverExecutionBatchSignal:
            return self._solver_batch_intents(session, signal)
        if type(signal) in {
            LoopExactTermRelationCompletionSignal,
            LoopExactGuardPartitionCompletionSignal,
        }:
            authority = self._issue_loop_exact_completion(session, signal)
            if authority is None:
                return ()
            intents = (
                EventIntent(
                    EventType.REQUIREMENT_COMPLETED,
                    RequirementCompletedEventAuthority(
                        authority.completion_receipt
                    ),
                ),
            )
            self._register_emission_plan(
                session,
                signal,
                intents,
                "EXACT_COMPLETED",
                {
                    "requirement_id": (
                        authority.completion_receipt.proof_requirement_id
                    ),
                    "authority": authority,
                },
            )
            return intents
        if type(signal) is RecurrenceValidationCompletionSignal:
            completion_authority = self._issue_recurrence_completion(session, signal)
            occurrence_id = (
                completion_authority.completion_receipt.occurrence_id
            )
            if occurrence_id not in self._observed(session):
                raise ValueError("recurrence completion has no observed live occurrence")
            completed = self._completed(session)
            if occurrence_id in completed:
                return ()
            intents = (
                EventIntent(
                    EventType.REQUIREMENT_COMPLETED,
                    RequirementCompletedEventAuthority(
                        completion_authority.completion_receipt
                    ),
                ),
            )
            self._register_emission_plan(
                session,
                signal,
                intents,
                "RECURRENCE_COMPLETED",
                {
                    "occurrence_id": occurrence_id,
                    "authority": completion_authority,
                },
            )
            return intents
        if type(signal) is not LoopBlockerProductionSignal:
            raise TypeError("loop encoder signal type is not registered")
        authority = self.authority_for_signal(session, signal)
        occurrence_id = authority.occurrence.occurrence_id
        observed = self._observed(session)
        if occurrence_id in observed:
            return ()
        intents = (
            EventIntent(
                EventType.CAUSE_OBSERVED,
                CauseObservedEventAuthority(authority),
            ),
        )
        self._register_emission_plan(
            session,
            signal,
            intents,
            "OBSERVED",
            {"occurrence_id": occurrence_id},
        )
        return intents

    def has_observed(self, session: Any, signal: Any) -> bool:
        if type(signal) is not LoopBlockerProductionSignal:
            return False
        authority = self.authority_for_signal(session, signal)
        return authority.occurrence.occurrence_id in self._observed(session)
