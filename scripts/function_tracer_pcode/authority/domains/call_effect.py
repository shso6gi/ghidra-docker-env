"""Sealed Phase 6.3 expression/call/effect/memory authority model."""

from __future__ import annotations

from dataclasses import dataclass
from enum import Enum
from types import MappingProxyType
from typing import Any, Callable, Iterable, Mapping, Optional

from scripts.function_tracer_pcode.proof.call_effect.obligations import (
    InternalSolverProofArtifact,
    StructuralCoverageCertificate,
    UseDomainCoverageMapping,
)
from scripts.function_tracer_pcode.proof.call_effect.preflight import (
    CallResolutionProjection,
    PreparedAnalysisPair,
)
from scripts.function_tracer_pcode.authority.lifecycle.execution_authority import (
    CallEffectExecutionRefusalReceipt,
    ExecutionAuthorityStartupReceipt,
    GenericSolverExecutionReceipt,
    ModelBoundRelationalRefutationArtifact,
    ProducerAttemptMembership,
    ProducerStageContract,
    ProducerStageRegistry,
    PINNED_SOLVER_EXECUTION_ISSUER,
    SolverExecutionEvidenceBundle,
    TerminalLifecycleProjectionAuthority,
    TerminalTimeoutSelectionReceipt,
    validate_execution_authority_deployment,
)

from scripts.function_tracer_pcode.authority.contracts import (
    CauseOccurrence,
    CauseOccurrenceAuthority,
    IdentityScope,
    ProofRequirement,
    ReasonDefinition,
    RecoveryAddressability,
    RequirementCompletionReceipt,
    RequirementSlotDefinition,
    SatisfactionContractDefinition,
    all_of,
    authority_digest,
    authority_identity_key,
    any_of,
    requirement_slot,
)
from scripts.function_tracer_pcode.authority.lifecycle.production_signals import (
    CallEffectBlockerProductionSignal,
    CallEffectPrerequisiteProductionSignal,
    CallEffectProofBatchProductionSignal,
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
    GenericReceiptBoundSolverExecutionEventAuthority,
    RequirementCompletedEventAuthority,
)


class FailureDisposition(str, Enum):
    TYPED_SEMANTIC_CAUSE = "TYPED_SEMANTIC_CAUSE"
    INFRASTRUCTURE_INVALID = "INFRASTRUCTURE_INVALID"
    DIAGNOSTIC_ONLY = "DIAGNOSTIC_ONLY"


_SUMMARY_EFFECT_SIGNAL_TOKEN = object()


@dataclass(frozen=True, init=False)
class SummaryEffectPrerequisiteProductionSignal:
    """Factory-issued slice3 owner for summary-discovered effect prerequisites."""

    reason_id: str
    identity_scope: IdentityScope
    target_kind: str
    canonical_target_key: Any
    function_snapshot_fingerprint: str
    missing_semantic_fact: Any
    observation_surface: Any
    evidence_refs: tuple[str, ...]
    producer_id: str

    def __init__(
        self,
        reason_id: str,
        identity_scope: IdentityScope,
        target_kind: str,
        canonical_target_key: Any,
        function_snapshot_fingerprint: str,
        missing_semantic_fact: Any,
        observation_surface: Any,
        evidence_refs: Iterable[str],
        producer_id: str,
        *,
        _factory_token: object = None,
    ) -> None:
        if _factory_token is not _SUMMARY_EFFECT_SIGNAL_TOKEN:
            raise TypeError("summary effect prerequisite signal must be factory issued")
        for name, value in (
            ("reason_id", reason_id),
            ("identity_scope", identity_scope),
            ("target_kind", target_kind),
            ("canonical_target_key", canonical_target_key),
            ("function_snapshot_fingerprint", function_snapshot_fingerprint),
            ("missing_semantic_fact", missing_semantic_fact),
            ("observation_surface", observation_surface),
            ("evidence_refs", tuple(evidence_refs)),
            ("producer_id", producer_id),
        ):
            object.__setattr__(self, name, value)
        spec = CALL_EFFECT_REASON_SPECS.get(reason_id)
        if (
            spec is None
            or identity_scope is not spec.identity_scope
            or target_kind != spec.target_kind
        ):
            raise ValueError("summary effect prerequisite differs from slice3 registry")
        if identity_scope is not IdentityScope.UNARY:
            raise ValueError("summary effect prerequisite must be unary")
        if type(function_snapshot_fingerprint) is not str or not function_snapshot_fingerprint:
            raise TypeError("summary effect prerequisite snapshot is incomplete")
        if type(producer_id) is not str or not producer_id:
            raise TypeError("summary effect prerequisite producer is incomplete")
        if any(type(item) is not str or not item for item in self.evidence_refs):
            raise TypeError("summary effect prerequisite evidence is incomplete")
        authority_digest(canonical_target_key)
        authority_digest(missing_semantic_fact)
        authority_digest(observation_surface)


@dataclass(frozen=True)
class CallEffectReasonSpec:
    reason_id: str
    identity_scope: IdentityScope
    target_kind: str
    contract_definition_id: Optional[str]
    proof_kinds: tuple[str, ...]

    @property
    def recovery_addressability(self) -> RecoveryAddressability:
        return (
            RecoveryAddressability.NO_PROOF_RECOVERY
            if self.contract_definition_id is None
            else RecoveryAddressability.REQUIREMENT_REQUIRED
        )


def _single_contract(reason_id: str, proof_kind: str) -> SatisfactionContractDefinition:
    return SatisfactionContractDefinition(
        reason_id + "-recovery",
        1,
        (RequirementSlotDefinition("proof", frozenset((proof_kind,))),),
        requirement_slot("proof"),
    )


def _all_contract(reason_id: str, slots: tuple[str, ...]) -> SatisfactionContractDefinition:
    definitions = tuple(
        RequirementSlotDefinition(name, frozenset((name,))) for name in slots
    )
    return SatisfactionContractDefinition(
        reason_id + "-recovery",
        1,
        definitions,
        all_of(*(requirement_slot(name) for name in slots)),
    )


PURE_CALL_CONTRACT = SatisfactionContractDefinition(
    "pure-call-semantics-recovery",
    1,
    tuple(
        RequirementSlotDefinition(name, frozenset((name,)))
        for name in (
            "inline_region_semantic_proof",
            "callee_summary_semantic_proof",
            "call_guard_relation",
            "call_argument_relation",
            "call_return_relation",
        )
    ),
    all_of(
        any_of(
            requirement_slot("inline_region_semantic_proof"),
            requirement_slot("callee_summary_semantic_proof"),
        ),
        requirement_slot("call_guard_relation"),
        requirement_slot("call_argument_relation"),
        requirement_slot("call_return_relation"),
    ),
)


_SINGLE_PROOF_SPECS = (
    ("expression_translation_incomplete", IdentityScope.UNARY, "expression_object", "expression_translation"),
    ("callsite_identity_extraction_missing", IdentityScope.UNARY, "call_site", "callsite_object_identity"),
    ("call_target_resolution_unproven", IdentityScope.UNARY, "call_site", "call_target_resolution"),
    ("call_argument_extraction_incomplete", IdentityScope.UNARY, "call_site", "call_argument_extraction"),
    ("call_invocation_multiplicity_unproven", IdentityScope.UNARY, "call_site", "call_invocation_multiplicity"),
    ("call_output_reaching_definition_unproven", IdentityScope.UNARY, "call_output_use", "call_output_reaching_definition"),
    ("recursive_call_scc_unproven", IdentityScope.UNARY, "callee_scc", "recursive_call_scc_summary"),
    ("callee_dependency_closure_missing", IdentityScope.UNARY, "callee_dependency", "callee_dependency_closure"),
    ("callee_return_summary_incomplete", IdentityScope.UNARY, "callee_summary", "callee_return_partition"),
    ("effect_observation_coverage_incomplete", IdentityScope.UNARY, "function_effect_census", "effect_observation_coverage"),
    ("callsite_correspondence_unproven", IdentityScope.RELATIONAL, "call_correspondence", "callsite_correspondence"),
    ("effect_endpoint_correspondence_unproven", IdentityScope.RELATIONAL, "effect_endpoint_coupling", "effect_endpoint_correspondence"),
    ("call_to_region_input_relation_unproven", IdentityScope.RELATIONAL, "call_region_obligation", "call_to_region_input_relation"),
    ("abi_argument_relation_unproven", IdentityScope.RELATIONAL, "call_obligation", "abi_argument_relation"),
    ("call_effect_correspondence_unproven", IdentityScope.RELATIONAL, "effect_coupling", "call_effect_correspondence"),
    ("external_call_coupling_unproven", IdentityScope.RELATIONAL, "external_call_obligation", "external_call_semantic_coupling"),
    ("memory_object_identity_unproven", IdentityScope.RELATIONAL, "memory_coupling", "memory_object_identity"),
    ("memory_alias_relation_unproven", IdentityScope.RELATIONAL, "memory_coupling", "memory_alias_relation"),
    ("memory_effect_order_extraction_incomplete", IdentityScope.UNARY, "memory_effect_set", "memory_effect_order_extraction"),
    ("memory_effect_order_unproven", IdentityScope.RELATIONAL, "memory_coupling", "memory_effect_order_correspondence"),
    ("memory_final_state_correspondence_unproven", IdentityScope.RELATIONAL, "memory_coupling", "memory_final_state_correspondence"),
    ("call_projection_partition_unproven", IdentityScope.RELATIONAL, "prepared_call_projection", "call_projection_partition"),
)

_COMPOSITE_SPECS = (
    (
        "callee_effect_summary_incomplete",
        IdentityScope.UNARY,
        "callee_summary",
        ("callee_control_effect_profile", "callee_effect_summary", "callee_nested_call_closure"),
    ),
    (
        "inline_region_boundary_incomplete",
        IdentityScope.UNARY,
        "inline_region",
        ("inline_region_single_entry", "inline_region_exit_coverage", "inline_region_cross_edge_coverage"),
    ),
    (
        "inline_region_semantics_incomplete",
        IdentityScope.UNARY,
        "inline_region",
        (
            "inline_region_guard_partition",
            "inline_region_state_transformer",
            "inline_region_return_partition",
            "inline_region_control_profile",
        ),
    ),
)

_NO_PROOF_SPECS = (
    ("expression_semantics_unsupported", IdentityScope.UNARY, "expression_object"),
    ("unsupported_call_operation", IdentityScope.UNARY, "call_site"),
    ("unsupported_call_effect_semantics", IdentityScope.UNARY, "call_effect_object"),
)


_contracts = []
_specs = []
for reason_id, scope, target_kind, proof_kind in _SINGLE_PROOF_SPECS:
    contract = _single_contract(reason_id, proof_kind)
    _contracts.append(contract)
    _specs.append(CallEffectReasonSpec(
        reason_id, scope, target_kind, contract.contract_definition_id, (proof_kind,)
    ))
for reason_id, scope, target_kind, slots in _COMPOSITE_SPECS:
    contract = _all_contract(reason_id, slots)
    _contracts.append(contract)
    _specs.append(CallEffectReasonSpec(
        reason_id, scope, target_kind, contract.contract_definition_id, slots
    ))
_contracts.append(PURE_CALL_CONTRACT)
_specs.append(CallEffectReasonSpec(
    "pure_call_semantics_unproven",
    IdentityScope.RELATIONAL,
    "call_semantic_obligation",
    PURE_CALL_CONTRACT.contract_definition_id,
    tuple(slot.name for slot in PURE_CALL_CONTRACT.requirement_slots),
))
for reason_id, scope, target_kind in _NO_PROOF_SPECS:
    _specs.append(CallEffectReasonSpec(reason_id, scope, target_kind, None, ()))

CALL_EFFECT_REASON_SPECS: Mapping[str, CallEffectReasonSpec] = MappingProxyType({
    item.reason_id: item for item in sorted(_specs, key=lambda item: item.reason_id)
})
if len(CALL_EFFECT_REASON_SPECS) != len(_specs):
    raise ValueError("duplicate Phase 6.3 reason specification")


def _reason_definition(spec: CallEffectReasonSpec) -> ReasonDefinition:
    return ReasonDefinition(
        spec.reason_id,
        "expression_call_effect_memory",
        "unsupported_semantics" if not spec.proof_kinds else "proof_obligation",
        "blocks_decision",
        frozenset((spec.target_kind,)),
        ("object_derived_identity", "source_snapshot", "producer_predicate"),
        frozenset(spec.proof_kinds),
        True,
        "call-effect-memory-v2",
        spec.recovery_addressability,
    )


CALL_EFFECT_REASON_REGISTRY = SealedReasonRegistry.build(
    _reason_definition(spec) for spec in CALL_EFFECT_REASON_SPECS.values()
)
CALL_EFFECT_RECOVERY_REGISTRY = SealedRecoveryRegistry.build(_contracts)


@dataclass(frozen=True)
class FailureSourceKey:
    source_contract: str
    failure_code: str

    def __post_init__(self) -> None:
        if type(self.source_contract) is not str or not self.source_contract:
            raise TypeError("failure source contract is incomplete")
        if type(self.failure_code) is not str or not self.failure_code:
            raise TypeError("failure source code is incomplete")


@dataclass(frozen=True)
class FailureClassification:
    disposition: FailureDisposition
    reason_id: Optional[str]
    expected_scope: Optional[IdentityScope]

    def __post_init__(self) -> None:
        object.__setattr__(self, "disposition", FailureDisposition(self.disposition))
        if self.disposition == FailureDisposition.TYPED_SEMANTIC_CAUSE:
            if self.reason_id not in CALL_EFFECT_REASON_SPECS or self.expected_scope is None:
                raise ValueError("typed failure classification lacks sealed reason/scope")
            object.__setattr__(self, "expected_scope", IdentityScope(self.expected_scope))
        elif self.reason_id is not None or self.expected_scope is not None:
            raise ValueError("nonsemantic failure classification cannot carry reason authority")


def _semantic(reason_id: str) -> FailureClassification:
    spec = CALL_EFFECT_REASON_SPECS[reason_id]
    return FailureClassification(
        FailureDisposition.TYPED_SEMANTIC_CAUSE,
        reason_id,
        spec.identity_scope,
    )


def _build_failure_rules() -> Mapping[FailureSourceKey, FailureClassification]:
    rows: list[tuple[str, str, FailureClassification]] = []

    def add(source: str, codes: Iterable[str], classification: FailureClassification) -> None:
        rows.extend((source, code, classification) for code in codes)

    add("expression_translator", ("semantic_class_unsupported",), _semantic("expression_semantics_unsupported"))
    add("expression_translator", ("translation_incomplete",), _semantic("expression_translation_incomplete"))
    add("call_fact_extraction", ("pcode_op_identity_missing",), _semantic("callsite_identity_extraction_missing"))
    add("call_fact_extraction", ("call_operation_kind_unsupported",), _semantic("unsupported_call_operation"))
    add("call_fact_extraction", ("call_target_ambiguous", "call_target_evidence_missing"), _semantic("call_target_resolution_unproven"))
    add("call_fact_extraction", (
        "argument_evidence_missing", "argument_coverage_incomplete",
        "argument_group_missing", "argument_groups_ambiguous",
    ), _semantic("call_argument_extraction_incomplete"))
    add("call_fact_extraction", ("unsupported_call_effect",), _semantic("unsupported_call_effect_semantics"))

    add("primary_proof_stage", ("recursive_call_scc_unproven",), _semantic("recursive_call_scc_unproven"))
    add("primary_proof_stage", ("callsite_identity_extraction_missing",), _semantic("callsite_identity_extraction_missing"))
    add("primary_proof_stage", ("call_target_relation_missing",), _semantic("call_target_resolution_unproven"))
    add("primary_proof_stage", ("callsite_argument_evidence_incomplete",), _semantic("call_argument_extraction_incomplete"))
    add("primary_proof_stage", ("abi_argument_relation_missing",), _semantic("abi_argument_relation_unproven"))
    add("primary_proof_stage", ("callee_effect_summary_incomplete",), _semantic("callee_effect_summary_incomplete"))
    add("primary_proof_stage", ("callee_dependency_closure_missing",), _semantic("callee_dependency_closure_missing"))
    add("primary_proof_stage", ("inline_region_single_entry_missing", "inline_region_boundary_coverage_missing"), _semantic("inline_region_boundary_incomplete"))
    add("primary_proof_stage", ("inline_region_guard_partition_missing", "inline_region_state_transformer_missing"), _semantic("inline_region_semantics_incomplete"))
    add("primary_proof_stage", ("call_to_region_input_relation_missing",), _semantic("call_to_region_input_relation_unproven"))
    add("primary_proof_stage", ("unsupported_call_operation",), _semantic("unsupported_call_operation"))
    add("primary_proof_stage", ("callsite_correspondence_missing",), _semantic("callsite_correspondence_unproven"))
    add("primary_proof_stage", ("memory_effect_relation_missing",), _semantic("memory_final_state_correspondence_unproven"))
    add("primary_proof_stage", ("callee_return_relation_missing",), _semantic("callee_return_summary_incomplete"))
    add("primary_proof_stage", ("relational_call_effect_stage_proofs_missing",), _semantic("pure_call_semantics_unproven"))
    add("primary_proof_stage", ("relational_call_effect_input_incomplete",), FailureClassification(
        FailureDisposition.INFRASTRUCTURE_INVALID, None, None
    ))

    for side in ("left", "right"):
        add("structural_coverage", (
            f"{side}_pcode_census_incomplete",
            f"{side}_pcode_census_fact_key_mismatch",
            f"{side}_missing_call_facts_present",
            f"{side}_orphan_call_facts_present",
        ), _semantic("effect_observation_coverage_incomplete"))
    add("structural_coverage", (
        "structural_endpoint_coverage_incomplete",
        "duplicate_left_fact_ids_present", "duplicate_right_fact_ids_present",
        "uncovered_left_fact_ids_present", "uncovered_right_fact_ids_present",
    ), _semantic("effect_endpoint_correspondence_unproven"))
    add("structural_coverage", (
        "legacy_blocker_mapping_incomplete", "orphan_legacy_blockers_present",
    ), FailureClassification(FailureDisposition.INFRASTRUCTURE_INVALID, None, None))

    add("preflight_semantic", ("non_call_effect_unsafety_present",), _semantic("effect_observation_coverage_incomplete"))
    add("preflight_semantic", ("unsupported_call_effect_present",), _semantic("unsupported_call_effect_semantics"))
    add("preflight_semantic", ("caller_memory_relation_not_proven",), _semantic("memory_final_state_correspondence_unproven"))
    add("preflight_semantic", ("call_semantic_projection_incomplete",), _semantic("pure_call_semantics_unproven"))
    add("preflight_semantic", ("call_projection_no_active_pair_proof_missing",), _semantic("call_projection_partition_unproven"))

    add("infrastructure", (
        "prepared_use_domain_coverage_mapping_mismatch",
        "untrusted_use_domain_mapping_issuer",
        "use_domain_mapping_builder_version_mismatch",
        "use_domain_mapping_digest_mismatch",
        "use_domain_mapping_count_mismatch",
        "use_domain_mapping_invocation_contract_unproven",
        "structural_coverage_certificate_incomplete",
        "call_effect_stage_proofs_incomplete",
        "certificate_payload_status_mismatch",
        "certificate_digest_mismatch",
        "producer_kind_mismatch",
        "query_authority_invalid", "query_authority_membership_mismatch",
        "query_authority_missing",
        "normalized_assertion_digest_mismatch",
        "stage_input_digest_mismatch",
        "precondition_digest_mismatch",
        "source_analysis_mutated", "prepared_surface_invalid",
        "projection_binding_consumption_incomplete", "decision_owner_conflict",
        "comparison_receipt_missing", "comparison_receipt_invalid",
        "dispatch_cleanup_incomplete", "untrusted_producer_token",
        "query_digest_mismatch", "proof_id_mismatch", "unknown_failure_string",
        "call_effect_preflight_incomplete", "relational_call_effect_input_incomplete",
    ), FailureClassification(FailureDisposition.INFRASTRUCTURE_INVALID, None, None))
    add("migration_diagnostic", (
        "legacy_blocker_replacement_not_ready", "legacy_projection_only",
    ), FailureClassification(FailureDisposition.DIAGNOSTIC_ONLY, None, None))

    indexed: dict[FailureSourceKey, FailureClassification] = {}
    for source, code, classification in rows:
        key = FailureSourceKey(source, code)
        if key in indexed:
            raise ValueError(f"multiply classified failure input: {key!r}")
        indexed[key] = classification
    return MappingProxyType(dict(sorted(indexed.items(), key=lambda item: (
        item[0].source_contract, item[0].failure_code
    ))))


CALL_EFFECT_FAILURE_RULES = _build_failure_rules()

# Exact AST-normalized output surface of call_effect_producer.py.  Braces denote
# a typed runtime field (obligation/side/stage status), never a wildcard match.
CALL_EFFECT_PRODUCER_OUTPUT_PATTERNS = frozenset((
    "argument_relation_{}", "call_region_argument_evidence_incomplete",
    "call_region_callee_summary_incomplete", "call_region_endpoint_kind_mismatch",
    "call_region_memory_effect_coverage_incomplete", "call_region_pcode_identity_missing",
    "caller_memory_relation_{}", "complete_return_partition_missing",
    "guard_relation_{}", "inline_region_control_profile_missing",
    "inline_region_effect_summary_incomplete", "inline_region_nonexact_return_present",
    "inline_region_not_total_trap_free_scalar", "inline_region_return_partition_missing",
    "inline_region_return_validation_blocked", "inline_region_unsupported_call_present",
    "memory_relation_{}", "pcode_identity_missing", "pure_effect_summary_incomplete",
    "pure_producer_requires_resolved_calls", "return_partition_key_coverage_mismatch",
    "return_relation_{}", "typed_argument_evidence_incomplete",
    "typed_argument_evidence_missing", "typed_effect_evidence_missing",
    "typed_fact_missing", "typed_memory_effect_coverage_incomplete",
    "typed_return_partition_missing", "structural_coverage_certificate_missing",
    "structural_coverage_certificate_incomplete",
    "structural_coverage_certificate_id_missing", "{}",
))
CALL_EFFECT_PRODUCER_EXCEPTION_PATTERNS = frozenset((
    "argument_abi_width_relation_missing", "argument_arity_relation_missing",
    "call-effect query authority must be typed-renderer issued",
    "call-effect typed query authority digest mismatch",
    "call-effect typed query authority is incomplete",
    "call_region_argument_abi_width_relation_missing", "call_region_argument_arity_relation_missing",
    "call_region_parameter_width_missing", "call_region_return_partition_missing",
    "call_region_return_signedness_missing", "call_region_return_width_missing",
    "call_region_return_width_relation_direction_unsupported",
    "call_region_return_width_relation_semantic_width_missing",
    "call_region_return_width_relation_signedness_missing",
    "caller_memory_call_return_expression_unsupported",
    "caller_memory_call_return_signedness_missing", "caller_memory_call_return_width_missing",
    "caller_observation_exceeds_callee_return_width", "caller_parameter_relation_incomplete",
    "caller_parameter_relation_missing", "caller_return_observation_width_relation_missing",
    "inline_region_parameter_wider_than_declaration", "inline_region_parameter_width_missing",
    "inline_region_parameter_width_relation_ambiguous", "left_parameter_names_ambiguous",
    "memory_effect_call_target_relation_missing", "memory_effect_callsite_identity_missing",
    "memory_effect_location_relation_missing", "memory_effect_substitution_coverage_missing",
    "memory_effect_substitution_provenance_incomplete", "memory_effect_width_missing",
    "return_extension_signedness_missing", "return_partition_missing",
    "return_semantic_width_evidence_incomplete", "return_semantic_width_invalid",
    "return_semantic_width_relation_missing", "return_width_relation_missing",
    "right_parameter_names_ambiguous", "typed_stage_dependency_mismatch",
    "typed_stage_payload_mismatch", "unsupported_argument_expression",
    "unsupported_call_region_argument_expression", "unsupported_call_region_return_expression",
    "unsupported_guard_expression", "unsupported_return_expression",
    "unsupported_typed_proof_stage", "untrusted_typed_stage_renderer",
    "solver query authority requires the sealed typed renderer output",
    "v2 execution context requires PREFIX lifecycle authority",
    "v2 execution context result differs from lifecycle projection",
    "Q_open assignment must be a duplicate-preserving key/row pair",
    "Q_open assignment key must be obligation/stage strings",
    "Q_open assignment row is not live in lifecycle projection",
    "suppressed call/effect obligation IDs must be strings",
    "suppressed call/effect obligation IDs repeat",
    "v2 solver stage lacks live Q_open assignment",
    "v2 solver stage has ambiguous live Q_open assignments",
    "{}_alias_relation_missing", "{}_caller_call_effect_census_mismatch",
    "{}_caller_call_effect_identity_incomplete", "{}_caller_call_effect_summary_incomplete",
    "{}_caller_call_result_declaration_incomplete", "{}_caller_call_result_identity_incomplete",
    "{}_caller_call_result_summary_incomplete", "{}_caller_call_result_summary_missing",
    "{}_caller_call_result_symbol_collision", "{}_caller_derived_store_census_mismatch",
    "{}_caller_derived_store_identity_mismatch", "{}_caller_derived_store_target_mismatch",
    "{}_caller_effect_census_incomplete", "{}_caller_effect_order_not_acyclic",
    "{}_caller_effect_profile_missing", "{}_caller_local_store_census_mismatch",
    "{}_caller_local_store_identity_mismatch", "{}_caller_store_provenance_incomplete",
    "{}_count_relation_missing", "{}_event_location_relation_missing",
    "{}_event_order_relation_missing", "{}_execution_provenance_incomplete",
    "{}_location_relation_missing", "{}_order_relation_missing",
    "{}_partial_overlap_unsupported", "{}_value_relation_unsupported",
    "{}_value_width_relation_missing",
))
_PRODUCER_INFRASTRUCTURE_PATTERNS = frozenset((
    "{}", "typed_stage_dependency_mismatch", "typed_stage_payload_mismatch",
    "unsupported_typed_proof_stage", "untrusted_typed_stage_renderer",
    "call-effect query authority must be typed-renderer issued",
    "call-effect typed query authority digest mismatch",
    "call-effect typed query authority is incomplete",
    "solver query authority requires the sealed typed renderer output",
    "v2 execution context result differs from lifecycle projection",
    "Q_open assignment must be a duplicate-preserving key/row pair",
    "Q_open assignment key must be obligation/stage strings",
    "Q_open assignment row is not live in lifecycle projection",
    "suppressed call/effect obligation IDs must be strings",
    "suppressed call/effect obligation IDs repeat",
    "v2 solver stage lacks live Q_open assignment",
    "v2 solver stage has ambiguous live Q_open assignments",
    "structural_coverage_certificate_missing",
    "structural_coverage_certificate_incomplete",
    "structural_coverage_certificate_id_missing",
))
_PRODUCER_SOLVER_OUTCOME_PATTERNS = frozenset((
    "guard_relation_{}", "argument_relation_{}", "return_relation_{}",
    "memory_relation_{}", "caller_memory_relation_{}",
))
CALL_EFFECT_PRODUCER_PATTERN_DISPOSITIONS: Mapping[str, str] = MappingProxyType({
    pattern: (
        "INFRASTRUCTURE_INVALID" if pattern in _PRODUCER_INFRASTRUCTURE_PATTERNS
        else "TYPED_SOLVER_OUTCOME" if pattern in _PRODUCER_SOLVER_OUTCOME_PATTERNS
        else "TYPED_SEMANTIC_INPUT_GAP"
    )
    for pattern in (
        CALL_EFFECT_PRODUCER_OUTPUT_PATTERNS | CALL_EFFECT_PRODUCER_EXCEPTION_PATTERNS
    )
})


def classify_failure(
    source_contract: str,
    failure_code: str,
    *,
    identity_scope: Optional[IdentityScope] = None,
) -> FailureClassification:
    try:
        classification = CALL_EFFECT_FAILURE_RULES[FailureSourceKey(
            source_contract, failure_code
        )]
    except KeyError as exc:
        raise ValueError("unclassified Phase 6.3 failure input") from exc
    if classification.expected_scope is not None:
        if identity_scope is None or IdentityScope(identity_scope) != classification.expected_scope:
            raise ValueError("failure input scope differs from sealed reason owner")
    elif identity_scope is not None:
        raise ValueError("infrastructure/diagnostic input cannot claim semantic scope")
    return classification


_CALL_ELIGIBILITY_BLOCKER_BASE_CODES = frozenset({
    "argument_arity_relation_missing",
    "argument_relation_missing",
    "call_callee_memory_effect_summary_ambiguous",
    "call_callee_not_total_trap_free_scalar",
    "call_callee_return_shape_missing",
    "call_callee_return_summary_missing",
    "call_dependency_closure_missing",
    "call_invocation_multiplicity_unproven",
    "call_output_reaching_definition_unproven",
    "call_parameter_alignment_incomplete",
    "call_recursive_scc_unproven",
    "call_to_region_call_target_incomplete",
    "call_unsupported_effect",
    "callee_control_profile_missing",
    "callee_dependency_closure_missing",
    "callee_effect_summary_incomplete",
    "callee_memory_effect_summary_ambiguous",
    "callee_nested_call_incomplete",
    "callee_not_total_trap_free_scalar_effect",
    "callee_parameter_alignment_incomplete",
    "callee_return_shape_missing",
    "callee_return_summary_missing",
    "noninternal_call_target",
    "not_resolved_internal_call_candidate",
    "recursive_callee_summary_unproven",
    "target_relation_input_incomplete",
    "unsupported_call_effect",
    "inline_region_cross_edge_coverage_missing",
    "inline_region_exit_coverage_missing",
    "inline_region_not_total_trap_free_scalar",
    "inline_region_return_partition_missing",
    "inline_region_single_entry_unproven",
    "inline_region_state_transformer_missing",
    "phase2_requires_paired_call_sites",
})
_CALL_ELIGIBILITY_EXTRACTION_CODES = frozenset({
    "argument_coverage_incomplete",
    "argument_evidence_missing",
    "argument_group_missing",
    "argument_groups_ambiguous",
    "call_operation_kind_unsupported",
    "call_target_ambiguous",
    "call_target_evidence_missing",
    "pcode_op_identity_missing",
    "unsupported_call_effect",
})


def classify_call_eligibility_blocker(
    blocker: str,
) -> FailureClassification:
    """Classify one Phase 2 ineligibility code into relational authority."""

    if type(blocker) is not str or not blocker:
        raise TypeError("call eligibility blocker code is invalid")
    normalized = blocker
    for prefix in ("left_", "right_"):
        if normalized.startswith(prefix):
            normalized = normalized[len(prefix):]
            break
    extraction = False
    for prefix in ("call_extraction_", "extraction_"):
        if normalized.startswith(prefix):
            normalized = normalized[len(prefix):]
            extraction = True
            break
    if extraction:
        known = normalized in _CALL_ELIGIBILITY_EXTRACTION_CODES
    else:
        known = normalized in _CALL_ELIGIBILITY_BLOCKER_BASE_CODES
    if not known:
        return FailureClassification(
            FailureDisposition.INFRASTRUCTURE_INVALID, None, None
        )
    if normalized == "phase2_requires_paired_call_sites":
        return _semantic("callsite_correspondence_unproven")
    if "argument" in normalized or "parameter_alignment" in normalized:
        return _semantic("abi_argument_relation_unproven")
    if "memory" in normalized:
        return _semantic("memory_final_state_correspondence_unproven")
    return _semantic("pure_call_semantics_unproven")


@dataclass(frozen=True)
class ArtifactCapabilityRule:
    artifact_type: type
    allowed_scopes: frozenset[IdentityScope]
    observable_reason_ids: frozenset[str]
    completable_proof_kinds: frozenset[str]
    issuer_id: str
    validator: Callable[[Any, Mapping[str, Any]], bool]


def _verification_failure_absent(artifact: Any, _context: Mapping[str, Any]) -> bool:
    return callable(getattr(artifact, "verification_failure", None)) and (
        artifact.verification_failure() is None
    )


def _solver_v2_execution_valid(
    artifact: InternalSolverProofArtifact, context: Mapping[str, Any]
) -> bool:
    if not _verification_failure_absent(artifact, context):
        return False
    receipt = artifact.v2_execution_receipt
    receipts = tuple(artifact.v2_execution_receipts)
    membership = artifact.v2_producer_membership
    if (
        type(receipt) is not GenericSolverExecutionReceipt
        or not receipts
        or any(type(item) is not GenericSolverExecutionReceipt for item in receipts)
        or receipt not in receipts
        or type(membership) is not ProducerAttemptMembership
        or artifact.query_authority is None
    ):
        return False
    try:
        registry = context["producer_stage_registry"]
        projection = context["lifecycle_projection"]
        membership.requirement_assignment.validate_against(projection)
        for item in receipts:
            item.validate_join(registry, membership)
    except (TypeError, ValueError):
        return False
    except KeyError:
        return False
    expected_assignment = authority_digest({
        "renderer_query_authority_digest": artifact.query_authority.authority_digest,
        "result_occurrence_id": receipt.result_occurrence_id,
        "proof_requirement_id": membership.proof_requirement_id,
        "obligation_id": membership.obligation_id,
        "observation_contract_id": membership.observation_contract_id,
        "producer_stage": membership.proof_stage,
        "execution_identity_digest": membership.execution_identity_digest,
    })
    return bool(
        receipt.query_authority_digest == expected_assignment
        and all(item.query_authority_digest == expected_assignment for item in receipts)
        and receipt.proof_requirement_id == membership.proof_requirement_id
        and receipt.obligation_id == artifact.record.obligation_id
        and receipt.observation_contract_id == artifact.record.observation_contract_id
        and receipt.observed_status == artifact.record.solver_result
    )


def _prepared_valid(artifact: Any, context: Mapping[str, Any]) -> bool:
    source = context.get("source_pair")
    return source is not None and artifact.is_valid_for(source) and artifact.is_unchanged()


def _projection_valid(artifact: Any, context: Mapping[str, Any]) -> bool:
    return bool(
        artifact.prepared_surface_digest == context.get("prepared_surface_digest")
        and artifact.generation == context.get("generation")
    )


def _refutation_valid(artifact: Any, _context: Mapping[str, Any]) -> bool:
    try:
        artifact.validate()
    except (TypeError, ValueError):
        return False
    return bool(
        artifact.sat_execution_receipt.runner_issuer_id == "parallel-solver-runner-v1"
        and artifact.replay_receipt.replay_execution_receipt.runner_issuer_id
        == "parallel-solver-runner-v1"
    )


_unary_reasons = frozenset(
    spec.reason_id
    for spec in CALL_EFFECT_REASON_SPECS.values()
    if spec.identity_scope == IdentityScope.UNARY
)
_relational_reasons = frozenset(CALL_EFFECT_REASON_SPECS) - _unary_reasons
_solver_stage_proof_kinds = frozenset((
    "call_guard_relation", "call_argument_relation", "call_return_relation",
    "call_effect_correspondence", "memory_final_state_correspondence",
))


class ArtifactCapabilityRegistry:
    def __init__(self, rules: Iterable[ArtifactCapabilityRule]) -> None:
        indexed = {}
        for rule in rules:
            if type(rule) is not ArtifactCapabilityRule:
                raise TypeError("artifact capability rules must be exact typed values")
            if rule.artifact_type in indexed:
                raise ValueError("duplicate artifact capability type")
            indexed[rule.artifact_type] = rule
        self._rules = MappingProxyType(indexed)

    def _rule(self, artifact: Any) -> ArtifactCapabilityRule:
        try:
            return self._rules[type(artifact)]
        except KeyError as exc:
            raise TypeError("artifact exact type has no sealed capability") from exc

    def authorize_observe(
        self,
        artifact: Any,
        *,
        reason_id: str,
        identity_scope: IdentityScope,
        validation_context: Mapping[str, Any] = MappingProxyType({}),
    ) -> str:
        rule = self._rule(artifact)
        scope = IdentityScope(identity_scope)
        if scope not in rule.allowed_scopes or reason_id not in rule.observable_reason_ids:
            raise ValueError("artifact is not authorized to observe this reason/scope")
        if not rule.validator(artifact, validation_context):
            raise ValueError("artifact issuer/semantic validation failed")
        return rule.issuer_id

    def authorize_completion(
        self,
        artifact: Any,
        *,
        reason_id: str,
        identity_scope: IdentityScope,
        proof_kind: str,
        validation_context: Mapping[str, Any] = MappingProxyType({}),
    ) -> str:
        rule = self._rule(artifact)
        self.authorize_observe(
            artifact,
            reason_id=reason_id,
            identity_scope=identity_scope,
            validation_context=validation_context,
        )
        if proof_kind not in rule.completable_proof_kinds:
            raise ValueError("artifact cannot complete this proof kind")
        if type(artifact) is InternalSolverProofArtifact:
            stage_to_kind = {
                "guard_relation": "call_guard_relation",
                "argument_relation": "call_argument_relation",
                "return_relation": "call_return_relation",
                "memory_relation": "memory_final_state_correspondence",
                "caller_memory_relation": "memory_final_state_correspondence",
            }
            if (
                artifact.record.status != "proven"
                or artifact.record.solver_result != "unsat"
                or stage_to_kind.get(artifact.record.proof_stage) != proof_kind
            ):
                raise ValueError("solver artifact stage/status does not authorize completion")
            assignment = artifact.v2_producer_membership.requirement_assignment
            projection = validation_context.get("lifecycle_projection")
            if projection is None or not any(
                row.occurrence_id == assignment.occurrence_id
                and row.cause_id == assignment.cause_id
                and row.reason_id == reason_id
                for row in projection.c_active_base
            ):
                raise ValueError("solver completion reason does not join active cause owner")
        return rule.issuer_id


CALL_EFFECT_ARTIFACT_CAPABILITY_REGISTRY = ArtifactCapabilityRegistry((
    ArtifactCapabilityRule(
        StructuralCoverageCertificate,
        frozenset((IdentityScope.UNARY, IdentityScope.RELATIONAL)),
        frozenset(("effect_observation_coverage_incomplete", "effect_endpoint_correspondence_unproven")),
        frozenset(),
        "structural-coverage-certificate-v1",
        _verification_failure_absent,
    ),
    ArtifactCapabilityRule(
        UseDomainCoverageMapping,
        frozenset((IdentityScope.RELATIONAL,)),
        _relational_reasons,
        frozenset(),
        "use-domain-coverage-mapping-v1",
        _verification_failure_absent,
    ),
    ArtifactCapabilityRule(
        PreparedAnalysisPair,
        frozenset((IdentityScope.RELATIONAL,)),
        _relational_reasons,
        frozenset(),
        "prepared-analysis-pair-v1",
        _prepared_valid,
    ),
    ArtifactCapabilityRule(
        CallResolutionProjection,
        frozenset((IdentityScope.RELATIONAL,)),
        _relational_reasons,
        frozenset(),
        "call-resolution-projection-v1",
        _projection_valid,
    ),
    ArtifactCapabilityRule(
        InternalSolverProofArtifact,
        frozenset((IdentityScope.RELATIONAL,)),
        _relational_reasons,
        _solver_stage_proof_kinds,
        "internal-parallel-solver-runner",
        _solver_v2_execution_valid,
    ),
    ArtifactCapabilityRule(
        ModelBoundRelationalRefutationArtifact,
        frozenset((IdentityScope.RELATIONAL,)),
        _relational_reasons,
        frozenset(),
        "pinned-relational-witness-replay-v1",
        _refutation_valid,
    ),
))


def summary_effect_prerequisite_signals_from_acceptance(
    analysis: Any, acceptance_result: Any
) -> tuple[SummaryEffectPrerequisiteProductionSignal, ...]:
    """Refine summary effect blockers into their slice3 semantic owners."""

    from scripts.function_tracer_pcode.analysis.returns.summary_returns import (
        SummaryReturnAcceptanceResult,
    )
    from scripts.function_tracer_pcode.proof.obligations.snapshot import AnalysisSnapshot
    from scripts.function_tracer_pcode.authority.domains.loop_recurrence import (
        LoopSourceDisposition,
        _classify_summary_occurrence,
    )

    if type(acceptance_result) is not SummaryReturnAcceptanceResult:
        raise TypeError("summary effect refinement requires exact acceptance result")
    function_identity = analysis.outcome_function_identity()
    function_snapshot = AnalysisSnapshot.from_function_analysis(
        analysis
    ).semantic_fingerprint
    effect_summary = getattr(analysis, "effect_summary", None)
    effect_summary_key = (
        effect_summary.stable_key()
        if effect_summary is not None and callable(getattr(effect_summary, "stable_key", None))
        else None
    )
    results: list[SummaryEffectPrerequisiteProductionSignal] = []

    def issue(
        reason_id: str,
        target_kind: str,
        target: Any,
        missing_fact: Any,
        observation_surface: Any,
        evidence_refs: tuple[str, ...],
    ) -> None:
        results.append(SummaryEffectPrerequisiteProductionSignal(
            reason_id,
            IdentityScope.UNARY,
            target_kind,
            target,
            function_snapshot,
            missing_fact,
            observation_surface,
            evidence_refs,
            "typed-summary-effect-prerequisite-v2",
            _factory_token=_SUMMARY_EFFECT_SIGNAL_TOKEN,
        ))

    for occurrence in acceptance_result.blocker_occurrences:
        classification = _classify_summary_occurrence(analysis, occurrence)
        if classification.disposition is not LoopSourceDisposition.REFINED_TO_SLICE3:
            continue
        source_members = _summary_effect_source_members(
            analysis, occurrence.source_code, classification.reason_ids
        )
        for reason_id, source_member in zip(classification.reason_ids, source_members):
            spec = CALL_EFFECT_REASON_SPECS[reason_id]
            base_evidence = (occurrence.occurrence_digest, source_member)
            if reason_id == "callee_effect_summary_incomplete":
                matching = tuple(
                    item
                    for item in tuple(
                        getattr(effect_summary, "call_site_effect_summary_evidence", ()) or ()
                    )
                    if source_member in tuple(getattr(item, "incomplete_reasons", ()) or ())
                    or (
                        source_member == "callee_effect_summary_missing"
                        and getattr(item, "summary_status", None) == "missing"
                    )
                )
                if not matching:
                    raise ValueError("callee effect summary cause lacks exact callsite evidence")
                for item in matching:
                    item_key = item.stable_key()
                    issue(
                        reason_id,
                        spec.target_kind,
                        (
                            "callee_summary_v2",
                            function_identity,
                            function_snapshot,
                            item_key,
                        ),
                        ("callee_effect_summary_complete", False, source_member),
                        ("summary_candidate_effect_prerequisite", item_key),
                        base_evidence + (authority_digest(item_key),),
                    )
            elif reason_id == "memory_effect_order_extraction_incomplete":
                effect_keys = tuple(
                    item.stable_key()
                    for item in tuple(getattr(effect_summary, "effects", ()) or ())
                )
                issue(
                    reason_id,
                    spec.target_kind,
                    (
                        "memory_effect_set_v2",
                        function_identity,
                        function_snapshot,
                        effect_keys,
                    ),
                    ("memory_effect_order_extracted", False, source_member),
                    ("summary_candidate_effect_prerequisite", effect_summary_key),
                    base_evidence + (authority_digest(effect_keys),),
                )
            elif reason_id == "unsupported_call_effect_semantics":
                unsupported = tuple(
                    getattr(effect_summary, "unsupported_call_sites", ()) or ()
                )
                if not unsupported:
                    raise ValueError("unsupported call effect cause lacks exact callsite object")
                for item in unsupported:
                    item_key = item.stable_key()
                    issue(
                        reason_id,
                        spec.target_kind,
                        (
                            "call_effect_object_v2",
                            function_identity,
                            function_snapshot,
                            item_key,
                        ),
                        ("call_effect_semantics_supported", False, source_member),
                        ("summary_candidate_effect_prerequisite", item_key),
                        base_evidence + (authority_digest(item_key),),
                    )
            else:
                issue(
                    reason_id,
                    spec.target_kind,
                    (
                        "function_effect_census_v2",
                        function_identity,
                        function_snapshot,
                        effect_summary_key,
                    ),
                    ("effect_observation_coverage_complete", False, source_member),
                    ("summary_candidate_effect_prerequisite", effect_summary_key),
                    base_evidence + (authority_digest(effect_summary_key),),
                )
    return _dedupe_prerequisite_signals(results)


def _dedupe_prerequisite_signals(
    results: Iterable["SummaryEffectPrerequisiteProductionSignal"],
) -> tuple["SummaryEffectPrerequisiteProductionSignal", ...]:
    """同じ (reason, target, missing) の signal を 1 つにする。

    同じかは authority の厳密な identity（`authority_identity_key`）で決める（target は値・対象の
    identity を含む。digest の一致・型を落とす preimage の一致で別の target の signal を落とさない:
    #218 PR-D）。並びは従来どおり digest の順。
    """

    deduped: dict[Any, SummaryEffectPrerequisiteProductionSignal] = {}
    order: dict[Any, tuple] = {}
    for signal in results:
        payload = {
            "reason_id": signal.reason_id,
            "target": signal.canonical_target_key,
            "missing": signal.missing_semantic_fact,
        }
        key = authority_identity_key(payload)
        if key not in deduped:
            deduped[key] = signal
            order[key] = (authority_digest(payload), len(order))
    return tuple(deduped[key] for key in sorted(deduped, key=order.__getitem__))


def _summary_effect_source_members(
    analysis: Any, source_code: str, reason_ids: tuple[str, ...]
) -> tuple[str, ...]:
    direct = {
        "summary_effect_unmodeled:effect_summary_missing": (
            "effect_summary_missing",
        ),
        "summary_effect_unmodeled:unsupported_call_effect": (
            "unsupported_call_effect",
        ),
    }
    if source_code in direct:
        members = direct[source_code]
    else:
        prefix = "summary_effect_unmodeled:"
        if not source_code.startswith(prefix):
            raise ValueError("slice3 summary refinement has an unknown source contract")
        members = tuple(source_code[len(prefix):].split(","))
        actual = tuple(
            getattr(getattr(analysis, "effect_summary", None), "incomplete_reasons", ())
            or ()
        )
        if members != actual:
            raise ValueError("summary effect source tuple differs from object authority")
    if len(members) != len(reason_ids):
        raise ValueError("summary effect source/refinement cardinality differs")
    return members


CALL_EFFECT_PRODUCTION_STAGE_REGISTRY = ProducerStageRegistry(1, tuple(
    ProducerStageContract(
        "call-effect-domain-v1",
        "typed-call-effect-solver-v1",
        "1",
        stage,
        "parallel-solver-runner-v1",
        frozenset(("attempted",)),
        frozenset(("attempted",)),
        priority,
    )
    for priority, stage in enumerate((
        "guard_relation",
        "argument_relation",
        "return_relation",
        "memory_relation",
        "caller_memory_relation",
    ), 1)
))


_PURE_CALL_STAGE_BY_PROOF_KIND = MappingProxyType({
    "call_guard_relation": "guard_relation",
    "call_argument_relation": "argument_relation",
    "call_return_relation": "return_relation",
})


class CallEffectPilotEncoder:
    """Production encoder for exact call/effect causes and pinned proof assignments."""

    def __init__(self) -> None:
        self._cause_factory = SemanticCauseIdentityFactory(CALL_EFFECT_REASON_REGISTRY)
        self._binding_factory = SatisfactionBindingFactory(CALL_EFFECT_RECOVERY_REGISTRY)

    @staticmethod
    def _state(session: Any) -> dict[str, Any]:
        return session.domain_signal_state.setdefault(
            "call_effect_v2",
            {
                "authorities": {},
                "signals": {},
                "execution_projections": {},
                "completed_requirements": set(),
                "execution_receipts": set(),
                "execution_started": False,
                "execution_refusals": [],
                "startup_receipt": None,
            },
        )

    def validate_startup(self) -> ExecutionAuthorityStartupReceipt:
        return validate_execution_authority_deployment()

    @staticmethod
    def _signal_key(signal: CallEffectBlockerProductionSignal) -> str:
        return authority_digest({
            "source_contract": signal.source_contract,
            "failure_code": signal.failure_code,
            "obligation_id": signal.obligation_id,
            "observation_contract_id": signal.observation_contract_id,
            "left_fact_id": signal.left_fact_id,
            "right_fact_id": signal.right_fact_id,
            "semantic_arm": signal.semantic_arm,
            "structural_certificate_id": signal.structural_certificate_id,
            "producer_id": signal.producer_id,
            "effect_stage_required": signal.effect_stage_required,
        })

    @staticmethod
    def _summary_effect_signal_key(
        signal: SummaryEffectPrerequisiteProductionSignal,
    ) -> str:
        return authority_digest({
            "reason_id": signal.reason_id,
            "target_kind": signal.target_kind,
            "canonical_target_key": signal.canonical_target_key,
            "function_snapshot_fingerprint": signal.function_snapshot_fingerprint,
            "missing_semantic_fact": signal.missing_semantic_fact,
            "observation_surface": signal.observation_surface,
            "producer_id": signal.producer_id,
        })

    @staticmethod
    def _prerequisite_signal_key(
        signal: CallEffectPrerequisiteProductionSignal,
    ) -> str:
        return authority_digest(signal._phase7_signal_authority())

    def _prerequisite_authority(
        self, session: Any, signal: CallEffectPrerequisiteProductionSignal,
    ) -> CauseOccurrenceAuthority:
        reason_id = signal.reason_id
        for blocker in signal.eligibility_blockers:
            classification = classify_call_eligibility_blocker(blocker)
            if (
                classification.disposition
                != FailureDisposition.TYPED_SEMANTIC_CAUSE
                or classification.reason_id != reason_id
                or classification.expected_scope != IdentityScope.RELATIONAL
            ):
                raise ValueError(
                    "call/effect prerequisite blocker routing is not sealed"
                )
        spec = CALL_EFFECT_REASON_SPECS[reason_id]
        target = (
            spec.target_kind,
            "call_effect_prerequisite",
            signal.obligation_id,
            signal.observation_contract_id,
            signal.left_fact_id,
            signal.right_fact_id,
            signal.structural_certificate_id,
        )
        cause = self._cause_factory.create(
            reason_id=reason_id,
            identity_scope=IdentityScope.RELATIONAL,
            target_kind=spec.target_kind,
            canonical_target_key=target,
            missing_semantic_fact=(
                "phase2_call_eligibility_blockers",
                signal.eligibility_blockers,
            ),
            semantic_proposition=(
                "call_effect_prerequisite_is_proven", reason_id, target
            ),
            observation_surface=(
                signal.observation_contract_id,
                signal.structural_certificate_id,
            ),
            active_semantic_precondition=(
                "phase2_eligibility_blockers", signal.eligibility_blockers
            ),
            correspondence_contract=(
                "relational_call_effect_obligation",
                signal.left_fact_id,
                signal.right_fact_id,
            ),
        )
        semantic_target_kind = "typed_call_effect_prerequisite_v2"
        requirements = {}
        for proof_kind in spec.proof_kinds:
            semantic_target = (
                semantic_target_kind, proof_kind, target
            )
            requirement_id = "call-effect-prereq-" + authority_digest({
                "cause_id": cause.value,
                "proof_kind": proof_kind,
                "semantic_target": semantic_target,
            })[:32]
            requirements[proof_kind] = ProofRequirement(
                requirement_id, proof_kind, semantic_target
            )
        bound = self._binding_factory.bind(
            contract_definition_id=spec.contract_definition_id,
            contract_version=1,
            bindings=(
                {"proof": next(iter(requirements.values()))}
                if len(requirements) == 1
                else requirements
            ),
        )
        occurrence = CauseOccurrence(
            "call-effect-prereq-occ-" + authority_digest({
                "cause_id": cause.value,
                "result_occurrence_id": session.identity.result_occurrence_id,
            })[:32],
            cause,
            reason_id,
            authority_digest({"canonical_target": target}),
            spec.target_kind,
            IdentityScope.RELATIONAL,
            bound.contract_definition_id,
            bound.contract_version,
            bound.normalized_expression_digest,
            bound.bound_expression_digest,
            tuple(
                requirement.requirement_id
                for requirement in requirements.values()
            ),
            (
                signal.structural_certificate_id,
                *signal.eligibility_blockers,
            ),
            "typed_call_effect_prerequisite",
            session.identity.source_snapshot_fingerprint,
            signal.producer_id,
            session.identity.execution_identity_digest,
        )
        return CauseOccurrenceAuthority(occurrence, bound)

    def _summary_effect_authority(
        self,
        session: Any,
        signal: SummaryEffectPrerequisiteProductionSignal,
    ) -> CauseOccurrenceAuthority:
        spec = CALL_EFFECT_REASON_SPECS[signal.reason_id]
        cause = self._cause_factory.create(
            reason_id=signal.reason_id,
            identity_scope=IdentityScope.UNARY,
            target_kind=signal.target_kind,
            canonical_target_key=(
                signal.canonical_target_key,
                ("function_snapshot", signal.function_snapshot_fingerprint),
            ),
            missing_semantic_fact=signal.missing_semantic_fact,
            semantic_proposition=("slice3_effect_prerequisite_complete", signal.reason_id),
            observation_surface=signal.observation_surface,
            active_semantic_precondition=("summary_candidate_requires_effect_fact", True),
            correspondence_contract=("one_function_snapshot",),
        )
        bindings: dict[str, ProofRequirement] = {}
        slot_names = spec.proof_kinds if len(spec.proof_kinds) > 1 else ("proof",)
        for slot_name, proof_kind in zip(slot_names, spec.proof_kinds):
            semantic_target = (
                "summary_effect_prerequisite_target_v2",
                signal.canonical_target_key,
                signal.function_snapshot_fingerprint,
                proof_kind,
            )
            requirement_id = "summary-effect-q-" + authority_digest({
                "cause_id": cause.value,
                "proof_kind": proof_kind,
                "semantic_target": semantic_target,
            })[:32]
            bindings[slot_name] = ProofRequirement(
                requirement_id, proof_kind, semantic_target
            )
        bound = self._binding_factory.bind(
            contract_definition_id=spec.contract_definition_id,
            contract_version=1,
            bindings=bindings,
        )
        occurrence_id = "summary-effect-occ-" + authority_digest({
            "cause_id": cause.value,
            "result_occurrence_id": session.identity.result_occurrence_id,
        })[:32]
        occurrence = CauseOccurrence(
            occurrence_id,
            cause,
            signal.reason_id,
            authority_digest(signal.canonical_target_key),
            signal.target_kind,
            IdentityScope.UNARY,
            bound.contract_definition_id,
            bound.contract_version,
            bound.normalized_expression_digest,
            bound.bound_expression_digest,
            tuple(item.requirement_id for item in bindings.values()),
            signal.evidence_refs,
            "typed_summary_effect_prerequisite",
            session.identity.source_snapshot_fingerprint,
            signal.producer_id,
            session.identity.execution_identity_digest,
        )
        return CauseOccurrenceAuthority(occurrence, bound)

    def _authority(
        self, session: Any, signal: CallEffectBlockerProductionSignal
    ) -> CauseOccurrenceAuthority:
        classification = classify_failure(
            signal.source_contract,
            signal.failure_code,
            identity_scope=IdentityScope.RELATIONAL,
        )
        if (
            classification.disposition != FailureDisposition.TYPED_SEMANTIC_CAUSE
            or classification.reason_id != "pure_call_semantics_unproven"
        ):
            raise ValueError("call/effect production signal is outside pure-call cause lane")
        spec = CALL_EFFECT_REASON_SPECS[classification.reason_id]
        target = (
            "call_semantic_obligation",
            signal.obligation_id,
            signal.observation_contract_id,
            signal.left_fact_id,
            signal.right_fact_id,
        )
        cause = self._cause_factory.create(
            reason_id=classification.reason_id,
            identity_scope=IdentityScope.RELATIONAL,
            target_kind=spec.target_kind,
            canonical_target_key=target,
            missing_semantic_fact=("pure_call_relational_proof_incomplete",),
            semantic_proposition=("pure_call_semantics_equivalent", target),
            observation_surface=(
                signal.observation_contract_id,
                signal.structural_certificate_id,
            ),
            active_semantic_precondition=("eligible_relational_obligation", True),
            correspondence_contract=(
                "ordered_call_or_region_facts",
                signal.left_fact_id,
                signal.right_fact_id,
            ),
        )
        bindings = {}
        for proof_kind in spec.proof_kinds:
            stage = _PURE_CALL_STAGE_BY_PROOF_KIND.get(proof_kind)
            semantic_target = (
                (
                    "call_effect_solver_stage",
                    signal.obligation_id,
                    signal.observation_contract_id,
                    stage,
                )
                if stage is not None
                else (
                    "call_effect_semantic_arm",
                    signal.obligation_id,
                    signal.observation_contract_id,
                    proof_kind,
                )
            )
            requirement_id = "call-effect-req-" + authority_digest({
                "cause_id": cause.value,
                "proof_kind": proof_kind,
                "semantic_target": semantic_target,
            })[:32]
            bindings[proof_kind] = ProofRequirement(
                requirement_id, proof_kind, semantic_target
            )
        bound = self._binding_factory.bind(
            contract_definition_id=spec.contract_definition_id,
            contract_version=1,
            bindings=bindings,
        )
        occurrence_id = "call-effect-occ-" + authority_digest({
            "cause_id": cause.value,
            "result_occurrence_id": session.identity.result_occurrence_id,
        })[:32]
        occurrence = CauseOccurrence(
            occurrence_id,
            cause,
            classification.reason_id,
            authority_digest({"canonical_target": target}),
            spec.target_kind,
            IdentityScope.RELATIONAL,
            bound.contract_definition_id,
            bound.contract_version,
            bound.normalized_expression_digest,
            bound.bound_expression_digest,
            tuple(sorted(item.requirement_id for item in bindings.values())),
            (
                signal.structural_certificate_id,
                signal.left_fact_id,
                signal.right_fact_id,
            ),
            "typed_call_effect_proof_input",
            session.identity.source_snapshot_fingerprint,
            signal.producer_id,
            session.identity.execution_identity_digest,
        )
        return CauseOccurrenceAuthority(occurrence, bound)

    def __call__(self, session: Any, signal: Any) -> tuple[EventIntent, ...]:
        if type(signal) is CallEffectProofBatchProductionSignal:
            return self._proof_batch_intents(session, signal)
        if type(signal) is CallEffectPrerequisiteProductionSignal:
            state = self._state(session)
            key = self._prerequisite_signal_key(signal)
            if key in state["authorities"]:
                return ()
            authority = self._prerequisite_authority(session, signal)
            state["authorities"][key] = authority
            state["signals"][key] = signal
            return (EventIntent(
                EventType.CAUSE_OBSERVED,
                CauseObservedEventAuthority(authority),
            ),)
        if type(signal) is SummaryEffectPrerequisiteProductionSignal:
            state = self._state(session)
            key = self._summary_effect_signal_key(signal)
            if key in state["authorities"]:
                return ()
            authority = self._summary_effect_authority(session, signal)
            state["authorities"][key] = authority
            state["signals"][key] = signal
            return (EventIntent(
                EventType.CAUSE_OBSERVED,
                CauseObservedEventAuthority(authority),
            ),)
        if type(signal) is not CallEffectBlockerProductionSignal:
            raise TypeError("call/effect encoder requires an exact production signal")
        state = self._state(session)
        key = self._signal_key(signal)
        if key in state["authorities"]:
            return ()
        authority = self._authority(session, signal)
        state["authorities"][key] = authority
        state["signals"][key] = signal
        return (EventIntent(
            EventType.CAUSE_OBSERVED,
            CauseObservedEventAuthority(authority),
        ),)

    @staticmethod
    def _completion_intent(
        authority: CauseOccurrenceAuthority,
        requirement_id: str,
        artifact_digest: str,
        applicability_digest: str,
    ) -> EventIntent:
        return EventIntent(
            EventType.REQUIREMENT_COMPLETED,
            RequirementCompletedEventAuthority(RequirementCompletionReceipt(
                authority.occurrence.cause_id.value,
                authority.occurrence.occurrence_id,
                requirement_id,
                authority.bound_contract.contract_definition_id,
                authority.bound_contract.contract_version,
                authority.bound_contract.bound_expression_digest,
                artifact_digest,
                applicability_digest,
            )),
        )

    def _proof_batch_intents(
        self, session: Any, batch: CallEffectProofBatchProductionSignal
    ) -> tuple[EventIntent, ...]:
        state = self._state(session)
        key = self._signal_key(batch.blocker)
        try:
            authority = state["authorities"][key]
            projection = state["execution_projections"][
                authority.occurrence.occurrence_id
            ]
        except KeyError as exc:
            raise ValueError("call/effect proof batch lacks observed prefix authority") from exc
        artifacts = tuple(batch.artifacts)
        if any(
            type(artifact) is not InternalSolverProofArtifact
            or artifact.record.obligation_id != batch.blocker.obligation_id
            or artifact.record.observation_contract_id
            != batch.blocker.observation_contract_id
            or artifact.record.left_object_id != batch.blocker.left_fact_id
            or artifact.record.right_object_id != batch.blocker.right_fact_id
            for artifact in artifacts
        ):
            raise ValueError("call/effect proof batch differs from blocker authority")
        state["execution_started"] = True
        by_stage = {}
        for artifact in artifacts:
            if artifact.record.proof_stage in by_stage:
                raise ValueError("call/effect proof batch repeats a proof stage")
            by_stage[artifact.record.proof_stage] = artifact
        intents = []
        validation_context = {
            "producer_stage_registry": CALL_EFFECT_PRODUCTION_STAGE_REGISTRY,
            "lifecycle_projection": projection,
        }
        for proof_kind, stage in _PURE_CALL_STAGE_BY_PROOF_KIND.items():
            artifact = by_stage.get(stage)
            if artifact is None:
                continue
            for receipt in artifact.v2_execution_receipts:
                if receipt.observed_status not in {"unknown", "timeout", "error"}:
                    continue
                if receipt.receipt_digest in state["execution_receipts"]:
                    continue
                event_type = {
                    "unknown": EventType.SOLVER_UNKNOWN,
                    "timeout": EventType.SOLVER_TIMEOUT,
                    "error": EventType.SOLVER_ERROR,
                }[receipt.observed_status]
                intents.append(EventIntent(
                    event_type,
                    GenericReceiptBoundSolverExecutionEventAuthority(
                        receipt.proof_requirement_id,
                        receipt.to_authority_dict(),
                        receipt.observed_status == "timeout",
                    ),
                ))
                state["execution_receipts"].add(receipt.receipt_digest)
            if artifact.record.status != "proven":
                continue
            CALL_EFFECT_ARTIFACT_CAPABILITY_REGISTRY.authorize_completion(
                artifact,
                reason_id="pure_call_semantics_unproven",
                identity_scope=IdentityScope.RELATIONAL,
                proof_kind=proof_kind,
                validation_context=validation_context,
            )
            assignment = artifact.v2_producer_membership.requirement_assignment
            if assignment.occurrence_id != authority.occurrence.occurrence_id:
                raise ValueError("solver completion assignment differs from blocker occurrence")
            requirement_id = assignment.proof_requirement_id
            if requirement_id not in state["completed_requirements"]:
                artifact_digest = authority_digest({
                    "proof_id": artifact.record.proof_id,
                    "execution_receipt_digest": artifact.v2_execution_receipt.receipt_digest,
                    "query_authority_digest": artifact.query_authority.authority_digest,
                })
                intents.append(self._completion_intent(
                    authority,
                    requirement_id,
                    artifact_digest,
                    authority_digest({
                        "artifact_digest": artifact_digest,
                        "assignment_digest": assignment.assignment_digest,
                        "lifecycle_prefix_projection_digest": (
                            projection.prefix_projection_digest
                        ),
                    }),
                ))
                state["completed_requirements"].add(requirement_id)
        return tuple(intents)

    def build_execution_context(
        self,
        session: Any,
        signals: tuple[CallEffectBlockerProductionSignal, ...],
        registry: ProducerStageRegistry,
    ) -> Any:
        if registry != CALL_EFFECT_PRODUCTION_STAGE_REGISTRY:
            raise ValueError("call/effect execution registry differs from production authority")
        state = self._state(session)
        authorities = []
        for signal in signals:
            if type(signal) is not CallEffectBlockerProductionSignal:
                raise TypeError("execution context requires exact blocker signals")
            try:
                authorities.append(state["authorities"][self._signal_key(signal)])
            except KeyError as exc:
                raise ValueError("call/effect blocker was not observed before execution") from exc
        projection = session.preview_lifecycle_projection()
        requirement_to_key = {}
        for signal, authority in zip(signals, authorities):
            for proof_kind, stage in _PURE_CALL_STAGE_BY_PROOF_KIND.items():
                requirement = next(
                    requirement
                    for slot_name, requirement
                    in authority.bound_contract.slot_bindings
                    if slot_name == proof_kind
                )
                requirement_to_key[requirement.requirement_id] = (
                    signal.obligation_id, stage
                )
        completed_stage_requirements = (
            set(requirement_to_key) & state["completed_requirements"]
        )
        if completed_stage_requirements == set(requirement_to_key):
            # The checker may revisit the same shadow manifest in one result
            # occurrence after the exact stage batch has already been
            # materialized.  Its semantic-arm requirement intentionally stays
            # open, but the solver stages must not be executed a second time.
            return None
        requirements_by_obligation = {}
        for requirement_id, (obligation_id, _stage) in requirement_to_key.items():
            requirements_by_obligation.setdefault(obligation_id, []).append(
                requirement_id
            )
        suppressed_obligation_ids = []
        for obligation_id, requirement_ids in requirements_by_obligation.items():
            completed = [
                requirement_id
                for requirement_id in requirement_ids
                if requirement_id in completed_stage_requirements
            ]
            if not completed:
                continue
            if completed != requirement_ids[:len(completed)]:
                raise ValueError(
                    "call/effect completed stage frontier is not an ordered prefix"
                )
            # A later visit cannot reconstruct the dependency proof IDs for
            # the unfinished suffix without replaying completed solver stages.
            # Keep the suffix open and suppress this obligation for the
            # remainder of the result occurrence.
            suppressed_obligation_ids.append(obligation_id)
        active_requirement_ids = {
            requirement_id
            for requirement_id, (obligation_id, _stage) in requirement_to_key.items()
            if obligation_id not in suppressed_obligation_ids
        }
        if not active_requirement_ids:
            return None
        assignments = tuple(
            (requirement_to_key[row.proof_requirement_id], row)
            for row in projection.q_open_base
            if row.proof_requirement_id in active_requirement_ids
        )
        if len(assignments) != len(active_requirement_ids):
            live_requirement_ids = {
                row.proof_requirement_id for row in projection.q_open_base
            }
            missing_requirement_ids = tuple(sorted(
                active_requirement_ids - live_requirement_ids
            ))
            raise ValueError(
                "call/effect execution context lacks exact live stage frontier: "
                f"expected={len(active_requirement_ids)} assigned={len(assignments)} "
                f"missing={missing_requirement_ids!r} "
                f"live_count={len(live_requirement_ids)} "
                f"completed_stage_count={len(completed_stage_requirements)} "
                f"recorder_event_count={session.recorder.event_count}"
            )
        for authority in authorities:
            state["execution_projections"][authority.occurrence.occurrence_id] = projection
        from scripts.function_tracer_pcode.proof.call_effect.producer import (
            V2CallEffectExecutionContext,
        )

        def record_refusal(query_authority: Any, candidates: Any) -> None:
            receipt = CallEffectExecutionRefusalReceipt.ambiguous_q_open(
                projection=projection,
                query_authority=query_authority,
                candidates=candidates,
            )
            if receipt.refusal_receipt_digest not in {
                item.refusal_receipt_digest for item in state["execution_refusals"]
            }:
                state["execution_refusals"].append(receipt)
                session.execution_refusal_receipts.append(receipt)

        return V2CallEffectExecutionContext(
            registry,
            projection,
            session.identity.result_occurrence_id,
            assignments,
            record_refusal,
            tuple(suppressed_obligation_ids),
        )

    def finalize_terminal_timeout_bindings(
        self, session: Any, stream: Any
    ) -> tuple[tuple[int, str], ...]:
        state = self._state(session)
        census = state.get("solver_census")
        if census is None:
            return ()
        projection = session.reducer.replay(stream).projection
        terminal_projection = TerminalLifecycleProjectionAuthority.create(
            session.identity.result_occurrence_id,
            (row.proof_requirement_id for row in projection.q_open_base),
        )
        selection = TerminalTimeoutSelectionReceipt.select(
            CALL_EFFECT_PRODUCTION_STAGE_REGISTRY,
            census,
            terminal_projection,
        )
        startup_receipts = tuple(getattr(session, "startup_receipts", ()))
        if len(startup_receipts) != 1 or type(startup_receipts[0]) is not ExecutionAuthorityStartupReceipt:
            raise ValueError("call/effect solver evidence lacks one startup receipt")
        observed_stream_receipt_digests = tuple(
            event.authority_payload.execution_receipt_digest
            for event in stream.events
            if type(event.authority_payload)
            is GenericReceiptBoundSolverExecutionEventAuthority
        )
        bundle = SolverExecutionEvidenceBundle.seal(
            registry=CALL_EFFECT_PRODUCTION_STAGE_REGISTRY,
            startup_receipt=startup_receipts[0],
            census=census,
            terminal_projection=terminal_projection,
            terminal_selection=selection,
            final_lifecycle_projection_digest=projection.lifecycle_projection_digest,
            observed_stream_receipt_digests=observed_stream_receipt_digests,
        )
        state["solver_census"] = census
        state["terminal_timeout_selection"] = selection
        state["solver_execution_evidence_bundle"] = bundle
        session.execution_authority_evidence_bundles.append((
            CALL_EFFECT_PRODUCTION_STAGE_REGISTRY, bundle
        ))
        if selection is None:
            return ()
        matches = tuple(
            event
            for event in stream.events
            if type(event.authority_payload)
            is GenericReceiptBoundSolverExecutionEventAuthority
            and event.authority_payload.execution_receipt_digest
            == selection.execution_receipt_digest
            and event.authority_payload.proof_requirement_id
            == selection.proof_requirement_id
        )
        if len(matches) != 1:
            raise ValueError("terminal timeout selection lacks one stream event")
        return ((
            matches[0].header.sequence_number,
            selection.proof_requirement_id,
        ),)

    def finalize_open_execution_history(self, session: Any) -> None:
        """Seal every issuer-created ledger before the recorder is closed."""

        state = self._state(session)
        result_id = session.identity.result_occurrence_id
        if not PINNED_SOLVER_EXECUTION_ISSUER.has_open_result_ledger(
            CALL_EFFECT_PRODUCTION_STAGE_REGISTRY, result_id
        ):
            return
        census = PINNED_SOLVER_EXECUTION_ISSUER.seal_result_census(
            CALL_EFFECT_PRODUCTION_STAGE_REGISTRY, result_id
        )
        for event in census.events:
            receipt = event.execution_receipt
            if receipt.observed_status not in {"unknown", "timeout", "error"}:
                continue
            if receipt.receipt_digest in state["execution_receipts"]:
                continue
            event_type = {
                "unknown": EventType.SOLVER_UNKNOWN,
                "timeout": EventType.SOLVER_TIMEOUT,
                "error": EventType.SOLVER_ERROR,
            }[receipt.observed_status]
            session.emit(EventIntent(
                event_type,
                GenericReceiptBoundSolverExecutionEventAuthority(
                    receipt.proof_requirement_id,
                    receipt.to_authority_dict(),
                    receipt.observed_status == "timeout",
                ),
            ))
            state["execution_receipts"].add(receipt.receipt_digest)
        state["solver_census"] = census
