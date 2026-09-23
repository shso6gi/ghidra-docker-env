"""Certified call/effect preflight and prepared pairwise dispatch.

The public strategy API continues to receive the source analyses.  Built-in
pairwise executors consume a single-use frame and compare only the certified
solver-normalized pair carried by that frame.
"""

from __future__ import annotations

from contextvars import ContextVar, Token
from dataclasses import dataclass, field
from enum import Enum
import hashlib
import inspect
import marshal
import re
from threading import Lock
from typing import Any, Dict, Iterable, Mapping, Optional, Tuple
from uuid import uuid4

from scripts.function_tracer_pcode.proof.call_effect.obligations import (
    USE_DOMAIN_COVERAGE_MAPPING_BUILDER_VERSION,
    build_structural_coverage_certificate,
    build_use_domain_coverage_mapping,
    call_use_mapping_payload_from_manifest,
    call_use_obligation_edges_from_manifest,
)
from scripts.function_tracer_pcode.proof.cause_identity import (
    ProofRequirementContract,
    ProofRequirementId,
)
from scripts.function_tracer_pcode.proof.obligations.snapshot import (
    AnalysisSnapshot,
    SnapshotFingerprintCodec,
)
from scripts.function_tracer_pcode.core import expression_provenance_key
from scripts.function_tracer_pcode.proof.formula.input_correspondence import (
    LEFT as _INPUT_LEFT,
    RIGHT as _INPUT_RIGHT,
    InputCorrespondenceSet,
    build_input_correspondence_set,
)
from scripts.function_tracer_pcode.semantics.semantic_width import (
    align_return_value_extension_surfaces as _trusted_align_return_surfaces,
    normalize_analysis_semantic_width as _trusted_normalize_semantic_width,
)
from scripts.function_tracer_pcode.proof.monolithic_authority import (
    verify_monolithic_proof_bundle as _PINNED_MONOLITHIC_PROOF_VERIFIER,
    verify_terminal_decision_receipt as _PINNED_MONOLITHIC_TERMINAL_VERIFIER,
)


class CallProofDecisionMode(str, Enum):
    LEGACY_POST_PAIRWISE = "legacy_post_pairwise"
    PREFLIGHT_PROJECTION = "preflight_projection"


@dataclass(frozen=True)
class CallProofDecisionLease:
    comparison_session_id: str
    branch_id: str
    prepared_surface_digest: str
    mode: CallProofDecisionMode
    generation: int
    decision_owner_id: str
    configuration_digest: str


_DECISION_LEASE_LOCK = Lock()
_ACTIVE_DECISION_LEASES: Dict[Tuple[str, str, int], str] = {}


def _acquire_decision_lease(
    comparison_session_id: str,
    branch_id: str,
    generation: int,
    prepared_surface_digest: str,
    mode: CallProofDecisionMode,
) -> CallProofDecisionLease:
    owner = uuid4().hex
    key = (comparison_session_id, branch_id, generation)
    with _DECISION_LEASE_LOCK:
        if key in _ACTIVE_DECISION_LEASES:
            raise RuntimeError("call_proof_decision_owner_conflict")
        _ACTIVE_DECISION_LEASES[key] = owner
    return CallProofDecisionLease(
        comparison_session_id,
        branch_id,
        prepared_surface_digest,
        mode,
        generation,
        owner,
        _digest(("call_proof_decision_configuration_v1", mode.value, branch_id)),
    )


def _release_decision_lease(lease: CallProofDecisionLease) -> None:
    key = (lease.comparison_session_id, lease.branch_id, lease.generation)
    with _DECISION_LEASE_LOCK:
        if _ACTIVE_DECISION_LEASES.get(key) == lease.decision_owner_id:
            _ACTIVE_DECISION_LEASES.pop(key, None)


def _digest(value: Any) -> str:
    return SnapshotFingerprintCodec.digest(value)


_NORMALIZATION_RULE_VERSIONS = (
    # v2 (Issue #167): 条件付き規則は最終 InputCorrespondence の authorization
    # の下でだけ効く。
    "semantic_width_normalizer_v2",
    "return_extension_surface_alignment_v1",
)
_NORMALIZATION_ALLOWED_ROOTS = (
    "comparison_surface",
    "effect_summary",
    "parameters",
    "outcomes",
    "return_type",
    "return_type_obj",
    "return_type_provenance",
    "returns",
    "signature_hypotheses",
    "signedness_result",
    "summary_return_candidates",
)
_NORMALIZATION_OBSERVATION_ROOTS = (
    "parameters",
    "returns",
    "outcomes",
    "summary_return_candidates",
    "effect_summary",
    "comparison_surface",
)


def _analysis_digest(analysis: Any) -> str:
    return AnalysisSnapshot.from_function_analysis(analysis).semantic_fingerprint


def _pair_digest(pair: Tuple[Any, Any]) -> str:
    return _digest(tuple(_analysis_digest(item) for item in pair))


def _normalize_source_pair(source_pair: "StrategySourceAnalysisPair") -> Tuple[Any, Any]:
    """raw source を、その raw から決めた最終 relation の authorization で書き換える。

    prepared surface の構築と certificate の独立再構築はどちらもここを通るので、
    二重 normalize が同じ authorization を使うことが構造で保証される。
    """

    correspondence = source_pair.input_correspondence()
    return (
        _trusted_normalize_semantic_width(
            source_pair.analysis1,
            authorization=correspondence.authorization(_INPUT_LEFT),
        ),
        _trusted_normalize_semantic_width(
            source_pair.analysis2,
            authorization=correspondence.authorization(_INPUT_RIGHT),
        ),
    )


def _changed_semantic_roots(source: Any, candidate: Any) -> Tuple[str, ...]:
    before = AnalysisSnapshot.from_function_analysis(source).semantic_fields
    after = AnalysisSnapshot.from_function_analysis(candidate).semantic_fields
    return tuple(
        sorted(
            key for key in set(before) | set(after)
            if before.get(key) != after.get(key)
        )
    )


@dataclass(frozen=True)
class SurfaceDeltaAuditCertificate:
    audit_id: str
    status: str
    rule_steps: Tuple[Tuple[str, str, str], ...]
    changed_roots: Tuple[Tuple[str, Tuple[str, ...]], ...]
    allowed_roots: Tuple[str, ...]
    audit_kind: str = "rule_level_surface_delta_audit_v1"

    def validate(
        self,
        source_pair: "StrategySourceAnalysisPair",
        candidate_pair: Tuple[Any, Any],
    ) -> bool:
        if (
            self.status != "proven"
            or self.audit_kind != "rule_level_surface_delta_audit_v1"
            or self.allowed_roots != _NORMALIZATION_ALLOWED_ROOTS
        ):
            return False
        source_items = (source_pair.analysis1, source_pair.analysis2)
        normalized = _normalize_source_pair(source_pair)
        aligned = _trusted_align_return_surfaces(*normalized)
        expected_steps = (
            (
                _NORMALIZATION_RULE_VERSIONS[0],
                _pair_digest(source_items),
                _pair_digest(normalized),
            ),
            (
                _NORMALIZATION_RULE_VERSIONS[1],
                _pair_digest(normalized),
                _pair_digest(aligned),
            ),
        )
        expected_roots = tuple(
            (side, _changed_semantic_roots(source, candidate))
            for side, source, candidate in zip(
                ("left", "right"), source_items, candidate_pair
            )
        )
        if any(
            not set(roots).issubset(self.allowed_roots)
            for _side, roots in expected_roots
        ):
            return False
        expected_id = _digest(
            (
                self.audit_kind,
                expected_steps,
                expected_roots,
                self.allowed_roots,
            )
        )
        return (
            self.rule_steps == expected_steps
            and self.changed_roots == expected_roots
            and tuple(_analysis_digest(item) for item in aligned)
            == tuple(_analysis_digest(item) for item in candidate_pair)
            and self.audit_id == expected_id
        )


@dataclass(frozen=True)
class SemanticTransformationCertificate:
    certificate_id: str
    status: str
    surface_delta_audit_id: str
    trust_basis: str
    observation_roots: Tuple[str, ...]
    permitted_rewrite_kinds: Tuple[str, ...]
    return_alignment_premise_digest: str

    def validate(
        self,
        source_pair: "StrategySourceAnalysisPair",
        candidate_pair: Tuple[Any, Any],
        audit: SurfaceDeltaAuditCertificate,
        observation_contract_digest: str,
    ) -> bool:
        normalized = _normalize_source_pair(source_pair)
        premise = _digest(
            (
                "return_alignment_premise_v1",
                _pair_digest(normalized),
                observation_contract_digest,
                self.observation_roots,
            )
        )
        expected_id = _digest(
            (
                "semantic_transformation_certificate_v1",
                audit.audit_id,
                self.trust_basis,
                self.observation_roots,
                self.permitted_rewrite_kinds,
                premise,
                tuple(_analysis_digest(item) for item in candidate_pair),
            )
        )
        return (
            self.status == "proven"
            and audit.validate(source_pair, candidate_pair)
            and self.surface_delta_audit_id == audit.audit_id
            and self.trust_basis == "trusted_solver_semantic_width_tcb_v1"
            and self.observation_roots == _NORMALIZATION_OBSERVATION_ROOTS
            and self.permitted_rewrite_kinds == _NORMALIZATION_RULE_VERSIONS
            and self.return_alignment_premise_digest == premise
            and self.certificate_id == expected_id
        )


@dataclass(frozen=True)
class NormalizationCertificate:
    semantic_id: str
    instance_id: str
    source_pair_digest: str
    candidate_pair_digest: str
    left_source_digest: str
    right_source_digest: str
    left_candidate_digest: str
    right_candidate_digest: str
    observation_contract_digest: str
    status: str
    rule_versions: Tuple[str, ...]
    transformation_kind: str
    semantic_delta: Tuple[Tuple[str, str, str], ...]
    surface_delta_audit: SurfaceDeltaAuditCertificate
    semantic_transformation: SemanticTransformationCertificate
    #: 書き換えの前提を決めた最終 InputCorrespondence の digest（Issue #167）。
    #: authorization digest の決定性の証拠であり、意味保存の証明ではない
    #: （意味保存は規則ごとの SMT certificate test が担う）。
    input_correspondence_digest: str = ""

    @staticmethod
    def _rebuild_candidate(source_pair: "StrategySourceAnalysisPair") -> Tuple[Any, Any]:
        return _trusted_align_return_surfaces(*_normalize_source_pair(source_pair))

    def validate(self, source_pair: "StrategySourceAnalysisPair", candidate_pair: Tuple[Any, Any]) -> bool:
        if self.status != "proven":
            return False
        source_digests = source_pair.current_side_digests()
        candidate_digests = tuple(
            AnalysisSnapshot.from_function_analysis(item).semantic_fingerprint
            for item in candidate_pair
        )
        if source_digests != (self.left_source_digest, self.right_source_digest):
            return False
        if candidate_digests != (self.left_candidate_digest, self.right_candidate_digest):
            return False
        if self.transformation_kind != "trusted_semantic_width_normalization":
            return False
        if source_pair.input_correspondence().digest != self.input_correspondence_digest:
            return False
        if not self.surface_delta_audit.validate(source_pair, candidate_pair):
            return False
        if not self.semantic_transformation.validate(
            source_pair,
            candidate_pair,
            self.surface_delta_audit,
            self.observation_contract_digest,
        ):
            return False
        rebuilt = self._rebuild_candidate(source_pair)
        rebuilt_digests = tuple(
            AnalysisSnapshot.from_function_analysis(item).semantic_fingerprint
            for item in rebuilt
        )
        if rebuilt_digests != candidate_digests:
            return False
        expected_delta = tuple(
            (
                side,
                source_digest,
                candidate_digest,
            )
            for side, source_digest, candidate_digest in zip(
                ("left", "right"), source_digests, candidate_digests
            )
            if source_digest != candidate_digest
        )
        if self.semantic_delta != expected_delta:
            return False
        if _digest(source_digests) != self.source_pair_digest:
            return False
        if _digest(candidate_digests) != self.candidate_pair_digest:
            return False
        expected_semantic_id = _digest(
            (
                "normalization_certificate_v1",
                source_digests,
                candidate_digests,
                self.rule_versions,
                self.observation_contract_digest,
                self.transformation_kind,
                self.semantic_delta,
                self.surface_delta_audit.audit_id,
                self.semantic_transformation.certificate_id,
                self.input_correspondence_digest,
            )
        )
        return expected_semantic_id == self.semantic_id


@dataclass(frozen=True)
class StrategySourceAnalysisPair:
    """semantic-width 書き換え前の raw pair（Issue #167 の健全性保証の起点）。"""

    analysis1: Any = field(compare=False)
    analysis2: Any = field(compare=False)
    left_digest: str
    right_digest: str
    pair_digest: str
    #: validator を通った InputExtensionEvidence。production provider は現在
    #: 何も発行しない（信頼済み signature の経路が無い、v5 §4.4）。
    input_extension_evidence: Tuple[Any, ...] = field(default=(), compare=False)
    _input_correspondence_cache: Any = field(default=None, compare=False, repr=False)

    @classmethod
    def create(
        cls,
        analysis1: Any,
        analysis2: Any,
        *,
        input_extension_evidence: Tuple[Any, ...] = (),
    ) -> "StrategySourceAnalysisPair":
        left = AnalysisSnapshot.from_function_analysis(analysis1).semantic_fingerprint
        right = AnalysisSnapshot.from_function_analysis(analysis2).semantic_fingerprint
        return cls(
            analysis1,
            analysis2,
            left,
            right,
            _digest((left, right)),
            tuple(input_extension_evidence or ()),
        )

    def input_correspondence(self) -> InputCorrespondenceSet:
        """この raw pair の最終 InputCorrespondence（raw は不変なので 1 回だけ作る）。"""

        if not self.is_unchanged():
            raise ValueError("prepared_analysis_mutated")
        cached = self._input_correspondence_cache
        if cached is None:
            cached = build_input_correspondence_set(
                self.analysis1,
                self.analysis2,
                input_extension_evidence=self.input_extension_evidence,
            )
            object.__setattr__(self, "_input_correspondence_cache", cached)
        return cached

    def current_side_digests(self) -> Tuple[str, str]:
        return (
            AnalysisSnapshot.from_function_analysis(self.analysis1).semantic_fingerprint,
            AnalysisSnapshot.from_function_analysis(self.analysis2).semantic_fingerprint,
        )

    def is_unchanged(self) -> bool:
        return self.current_side_digests() == (self.left_digest, self.right_digest)


@dataclass(frozen=True)
class PreparedAnalysisPair:
    analysis1: Any = field(compare=False)
    analysis2: Any = field(compare=False)
    left_digest: str
    right_digest: str
    surface_digest: str
    certificate: NormalizationCertificate
    surface_kind: str = "certified_normalized_surface"
    #: この surface の parameter premise / authorization / decisive 十分性の唯一の出所。
    input_correspondence: Any = field(default=None, compare=False)

    def is_valid_for(self, source: StrategySourceAnalysisPair) -> bool:
        return (
            self.surface_kind == "certified_normalized_surface"
            and self.certificate.validate(source, (self.analysis1, self.analysis2))
            and self.surface_digest == self.certificate.candidate_pair_digest
            and type(self.input_correspondence) is InputCorrespondenceSet
            and self.input_correspondence.digest == self.certificate.input_correspondence_digest
        )

    def is_unchanged(self) -> bool:
        current = tuple(
            AnalysisSnapshot.from_function_analysis(item).semantic_fingerprint
            for item in (self.analysis1, self.analysis2)
        )
        return current == (self.left_digest, self.right_digest)


def prepare_solver_surface(
    source: StrategySourceAnalysisPair,
    *,
    observation_contract_digest: str,
    comparison_session_id: str,
    branch_id: str,
    generation: int,
    decision_mode: CallProofDecisionMode,
) -> PreparedAnalysisPair:
    """Build the certified child consumed by proof and comparison stages."""

    if not source.is_unchanged():
        raise ValueError("prepared_analysis_mutated")
    source_items = (source.analysis1, source.analysis2)
    # 順序が本質（v5 §4.3）: raw → 最終 relation → authorization → normalize。
    input_correspondence = source.input_correspondence()
    normalized = _normalize_source_pair(source)
    candidate1, candidate2 = _trusted_align_return_surfaces(*normalized)
    left = AnalysisSnapshot.from_function_analysis(candidate1).semantic_fingerprint
    right = AnalysisSnapshot.from_function_analysis(candidate2).semantic_fingerprint
    candidate_digest = _digest((left, right))
    transformation_kind = "trusted_semantic_width_normalization"
    semantic_delta = tuple(
        (side, source_digest, candidate_digest)
        for side, source_digest, candidate_digest in zip(
            ("left", "right"),
            (source.left_digest, source.right_digest),
            (left, right),
        )
        if source_digest != candidate_digest
    )
    rule_versions = (*_NORMALIZATION_RULE_VERSIONS, "independent_candidate_rebuild_v1")
    rule_steps = (
        (_NORMALIZATION_RULE_VERSIONS[0], _pair_digest(source_items), _pair_digest(normalized)),
        (
            _NORMALIZATION_RULE_VERSIONS[1],
            _pair_digest(normalized),
            _pair_digest((candidate1, candidate2)),
        ),
    )
    changed_roots = tuple(
        (side, _changed_semantic_roots(before, after))
        for side, before, after in zip(
            ("left", "right"), source_items, (candidate1, candidate2)
        )
    )
    if any(
        not set(roots).issubset(_NORMALIZATION_ALLOWED_ROOTS)
        for _side, roots in changed_roots
    ):
        raise ValueError(
            "surface_delta_outside_trusted_normalization_roots:"
            + repr(changed_roots)
        )
    audit_id = _digest(
        (
            "rule_level_surface_delta_audit_v1",
            rule_steps,
            changed_roots,
            _NORMALIZATION_ALLOWED_ROOTS,
        )
    )
    surface_delta_audit = SurfaceDeltaAuditCertificate(
        audit_id=audit_id,
        status="proven",
        rule_steps=rule_steps,
        changed_roots=changed_roots,
        allowed_roots=_NORMALIZATION_ALLOWED_ROOTS,
    )
    alignment_premise = _digest(
        (
            "return_alignment_premise_v1",
            _pair_digest(normalized),
            observation_contract_digest,
            _NORMALIZATION_OBSERVATION_ROOTS,
        )
    )
    semantic_transformation_id = _digest(
        (
            "semantic_transformation_certificate_v1",
            audit_id,
            "trusted_solver_semantic_width_tcb_v1",
            _NORMALIZATION_OBSERVATION_ROOTS,
            _NORMALIZATION_RULE_VERSIONS,
            alignment_premise,
            (left, right),
        )
    )
    semantic_transformation = SemanticTransformationCertificate(
        certificate_id=semantic_transformation_id,
        status="proven",
        surface_delta_audit_id=audit_id,
        trust_basis="trusted_solver_semantic_width_tcb_v1",
        observation_roots=_NORMALIZATION_OBSERVATION_ROOTS,
        permitted_rewrite_kinds=_NORMALIZATION_RULE_VERSIONS,
        return_alignment_premise_digest=alignment_premise,
    )
    semantic_id = _digest(
        (
            "normalization_certificate_v1",
            (source.left_digest, source.right_digest),
            (left, right),
            rule_versions,
            observation_contract_digest,
            transformation_kind,
            semantic_delta,
            audit_id,
            semantic_transformation_id,
            input_correspondence.digest,
        )
    )
    instance_id = _digest(
        (
            semantic_id,
            comparison_session_id,
            branch_id,
            generation,
            decision_mode.value,
            uuid4().hex,
        )
    )
    certificate = NormalizationCertificate(
        semantic_id=semantic_id,
        instance_id=instance_id,
        source_pair_digest=source.pair_digest,
        candidate_pair_digest=candidate_digest,
        left_source_digest=source.left_digest,
        right_source_digest=source.right_digest,
        left_candidate_digest=left,
        right_candidate_digest=right,
        observation_contract_digest=observation_contract_digest,
        status="proven",
        rule_versions=rule_versions,
        transformation_kind=transformation_kind,
        semantic_delta=semantic_delta,
        surface_delta_audit=surface_delta_audit,
        semantic_transformation=semantic_transformation,
        input_correspondence_digest=input_correspondence.digest,
    )
    prepared = PreparedAnalysisPair(
        candidate1,
        candidate2,
        left,
        right,
        candidate_digest,
        certificate,
        input_correspondence=input_correspondence,
    )
    if not prepared.is_valid_for(source):
        raise ValueError("surface_transformation_certificate_invalid")
    return prepared


@dataclass(frozen=True)
class BlockerResolutionRecord:
    occurrence_id: str
    blocker: str
    obligation_id: str
    requirement_id: ProofRequirementId
    mapping_basis: str
    status: str

    def to_dict(self) -> Dict[str, Any]:
        return {
            "occurrence_id": self.occurrence_id,
            "blocker": self.blocker,
            "obligation_id": self.obligation_id,
            "requirement_id": self.requirement_id.to_dict(),
            "mapping_basis": self.mapping_basis,
            "status": self.status,
        }


@dataclass(frozen=True)
class CallSemanticProjectionBinding:
    binding_id: str
    obligation_id: str
    requirement_id: ProofRequirementId
    observation_contract_id: str
    left_fact_id: Optional[str]
    right_fact_id: Optional[str]
    left_pcode_op_key: Optional[Tuple[Any, ...]]
    right_pcode_op_key: Optional[Tuple[Any, ...]]
    left_use_bindings: Tuple[Tuple[Any, ...], ...]
    right_use_bindings: Tuple[Tuple[Any, ...], ...]
    proof_stage_records: Tuple[Tuple[str, str, str], ...]
    relation_kind: str
    call_on_left: Optional[bool]
    region_return_members: Tuple[Tuple[Any, ...], ...]
    consumer_domains: Tuple[str, ...]
    status: str
    return_width_relation_contract: Tuple[Any, ...] = ()

    def to_dict(self) -> Dict[str, Any]:
        return {
            "binding_id": self.binding_id,
            "obligation_id": self.obligation_id,
            "requirement_id": self.requirement_id.to_dict(),
            "observation_contract_id": self.observation_contract_id,
            "left_fact_id": self.left_fact_id,
            "right_fact_id": self.right_fact_id,
            "left_pcode_op_key": self.left_pcode_op_key,
            "right_pcode_op_key": self.right_pcode_op_key,
            "left_use_bindings": self.left_use_bindings,
            "right_use_bindings": self.right_use_bindings,
            "proof_stage_records": self.proof_stage_records,
            "relation_kind": self.relation_kind,
            "call_on_left": self.call_on_left,
            "region_return_members": self.region_return_members,
            "consumer_domains": self.consumer_domains,
            "status": self.status,
            "return_width_relation_contract": self.return_width_relation_contract,
        }


@dataclass(frozen=True)
class CallResolutionProjection:
    projection_id: str
    prepared_surface_digest: str
    generation: int
    status: str
    required: bool
    covered_blockers: Tuple[str, ...]
    root_blockers: Tuple[str, ...]
    completed_obligation_ids: Tuple[str, ...]
    completed_requirement_keys: Tuple[Tuple[Any, ...], ...]
    blocker_resolutions: Tuple[BlockerResolutionRecord, ...]
    semantic_bindings: Tuple[CallSemanticProjectionBinding, ...]
    use_mapping_builder_version: str
    use_census_digest: str
    coverage_mapping_digest: str
    expected_pairwise_consumers: Tuple[str, ...] = ("return_cases", "base_context", "blocking_gate")

    @property
    def proven(self) -> bool:
        return self.status in {"proven", "not_required"}


def validate_call_resolution_projection(
    manifest: Mapping[str, Any],
    prepared: PreparedAnalysisPair,
    *,
    generation: int,
    trusted_proof_artifacts: Iterable[Any] = (),
) -> CallResolutionProjection:
    rebuilt_use_mapping = build_use_domain_coverage_mapping(
        prepared.analysis1,
        prepared.analysis2,
        # Fallback labels affect artifact-local fact ids only.  The trusted
        # mapping payload is keyed by object-derived p-code identity and never
        # accepts a binary label from the persisted manifest.
        binary1_name="prepared-left",
        binary2_name="prepared-right",
    )
    persisted_use_mapping = call_use_mapping_payload_from_manifest(manifest)
    persisted_use_edges = call_use_obligation_edges_from_manifest(manifest)
    use_mapping_failure = rebuilt_use_mapping.verification_failure()
    use_mapping_valid = bool(
        use_mapping_failure is None
        and rebuilt_use_mapping.builder_version
        == USE_DOMAIN_COVERAGE_MAPPING_BUILDER_VERSION
        and persisted_use_mapping == rebuilt_use_mapping.payload
        and persisted_use_edges == rebuilt_use_mapping.obligation_edges
    )
    summary = manifest.get("summary") if isinstance(manifest.get("summary"), Mapping) else {}
    obligations = tuple(
        item for item in manifest.get("relational_obligations", ()) or ()
        if isinstance(item, Mapping)
    )
    mappings = tuple(
        item for item in manifest.get("legacy_blocker_mapping", ()) or ()
        if isinstance(item, Mapping)
    )
    artifacts = tuple(trusted_proof_artifacts or ())
    orphan_blockers = tuple(str(item) for item in manifest.get("orphan_legacy_blockers", ()) or ())
    required = bool(
        any(records for _side, records in rebuilt_use_mapping.payload)
        or
        obligations
        or mappings
        or orphan_blockers
        or manifest.get("failure_cause")
        or int(summary.get("left_fact_count", 0) or 0)
        or int(summary.get("right_fact_count", 0) or 0)
    )
    if not required:
        status = "not_required"
        covered: Tuple[str, ...] = ()
        roots: Tuple[str, ...] = ()
        completed: Tuple[str, ...] = ()
    else:
        certificate = manifest.get("structural_coverage_certificate")
        rebuilt = build_structural_coverage_certificate(manifest)
        readiness = tuple(
            item for item in manifest.get("proof_readiness", ()) or ()
            if isinstance(item, Mapping)
        )
        completed = tuple(sorted(
            str(item.get("obligation_id")) for item in readiness
            if item.get("decision_eligible") is True and item.get("obligation_id")
        ))
        completed_set = set(completed)
        covered_items = []
        invalid_items = []
        resolution_records = []
        for mapping_index, mapping in enumerate(mappings):
            blocker = str(mapping.get("legacy_blocker") or "")
            requirement_ids = tuple(str(item) for item in mapping.get("obligation_ids", ()) or ())
            exact = (
                bool(blocker)
                and mapping.get("mapping_basis") == "callsite_pcode_ref"
                and mapping.get("mapping_status") == "mapped"
                and len(requirement_ids) == 1
                and requirement_ids[0] in completed_set
            )
            (covered_items if exact else invalid_items).append(blocker or "missing_blocker_identity")
            if exact:
                obligation_id = requirement_ids[0]
                requirement = ProofRequirementId.create(
                    "call_effect_summary_proof",
                    (
                        "prepared_call_effect_obligation",
                        prepared.surface_digest,
                        obligation_id,
                    ),
                    ProofRequirementContract(
                        proposition="prove deferred call return/effect relation before comparison",
                        relation_direction="ordered",
                        observation_surface=(
                            prepared.certificate.observation_contract_digest,
                            prepared.certificate.semantic_id,
                        ),
                        active_precondition=("obligation_id", obligation_id),
                    ),
                )
                resolution_records.append(
                    BlockerResolutionRecord(
                        occurrence_id=_digest(
                            (
                                "call_blocker_occurrence_v1",
                                prepared.surface_digest,
                                mapping_index,
                                blocker,
                                obligation_id,
                            )
                        ),
                        blocker=blocker,
                        obligation_id=obligation_id,
                        requirement_id=requirement,
                        mapping_basis="callsite_pcode_ref",
                        status="proven",
                    )
                )
        certificate_valid = (
            isinstance(certificate, Mapping)
            and certificate.get("status") == "complete"
            and certificate.get("verification_status") == "verified"
            and certificate.get("certificate_id") == rebuilt.certificate_id
            and rebuilt.verification_failure() is None
        )
        readiness_valid = bool(obligations) and len(readiness) == len(obligations) and all(
            item.get("decision_eligible") is True for item in readiness
        )
        replacement = manifest.get("legacy_replacement_readiness")
        replacement_valid = isinstance(replacement, Mapping) and replacement.get("status") == "ready"
        facts_by_id = {
            str(item.get("fact_id")): item
            for side in ("left", "right")
            for item in (
                tuple(manifest.get(f"{side}_facts", ()) or ())
                + tuple(manifest.get(f"{side}_regions", ()) or ())
            )
            if isinstance(item, Mapping) and item.get("fact_id")
        }
        artifacts_by_obligation: Dict[str, list[Any]] = {}
        for artifact in artifacts:
            verification_failure = getattr(artifact, "verification_failure", None)
            record = getattr(artifact, "record", None)
            if (
                not callable(verification_failure)
                or verification_failure() is not None
                or record is None
                or getattr(record, "status", None) not in {"proven", "inactive_proven"}
            ):
                continue
            artifacts_by_obligation.setdefault(
                str(getattr(record, "obligation_id", "")),
                [],
            ).append(artifact)
        semantic_bindings = []
        obligation_by_id = {
            str(item.get("obligation_id")): item for item in obligations
        }
        readiness_by_id = {
            str(item.get("obligation_id")): item for item in readiness
        }

        def use_consumer_domain(item: Any) -> str:
            try:
                payload = item if isinstance(item, Mapping) else dict(item)
                location = payload.get("semantic_location") or ("unknown",)
                if not isinstance(location, (tuple, list)):
                    return "unknown"
                tokens = {str(token) for token in location if isinstance(token, str)}
                if tokens.intersection({"condition", "guard", "phi_condition"}):
                    return "guard"
                root = str(location[0]) if location else "unknown"
                if root == "effects":
                    return "effect"
                if root in {
                    "returns", "return_outcomes", "summary_return_candidates",
                    "call_argument_evidence", "unsupported_call_sites",
                    "deferred_calls",
                }:
                    return "value"
                return "unknown"
            except (TypeError, ValueError, IndexError):
                return "unknown"

        for obligation_id in completed:
            obligation = obligation_by_id.get(obligation_id) or {}
            ready = readiness_by_id.get(obligation_id) or {}
            left_fact = facts_by_id.get(str(obligation.get("left_fact_id") or "")) or {}
            right_fact = facts_by_id.get(str(obligation.get("right_fact_id") or "")) or {}
            stage_artifacts = artifacts_by_obligation.get(obligation_id, [])
            stage_records = tuple(sorted(
                (
                    str(getattr(item.record, "proof_stage", "")),
                    str(getattr(item.record, "proof_id", "")),
                    str(getattr(item.record, "query_digest", "")),
                )
                for item in stage_artifacts
            ))
            completed_stages = tuple(ready.get("completed_stages", ()) or ())
            stage_names = {item[0] for item in stage_records}
            artifact_coverage = bool(completed_stages) and set(completed_stages).issubset(stage_names)
            return_artifacts = tuple(
                item
                for item in stage_artifacts
                if getattr(item.record, "proof_stage", None) == "return_relation"
            )
            width_relation_contract: Tuple[Any, ...] = ()
            if len(return_artifacts) == 1:
                preconditions = getattr(return_artifacts[0], "precondition_payload", {})
                if isinstance(preconditions, Mapping) and isinstance(
                    preconditions.get("return_width_relation"), Mapping
                ):
                    width_relation_contract = SnapshotFingerprintCodec.freeze(
                        preconditions["return_width_relation"]
                    )
            relation_kind = str(obligation.get("relation_kind") or "")
            call_on_left = None
            region_return_members: Tuple[Tuple[Any, ...], ...] = ()
            if relation_kind == "call_to_region" and len(return_artifacts) == 1:
                stage_payload = getattr(return_artifacts[0], "stage_input_payload", {})
                if isinstance(stage_payload, Mapping):
                    call_on_left = bool(stage_payload.get("call_on_left"))
                    region_return_members = tuple(
                        SnapshotFingerprintCodec.freeze(item)
                        for item in tuple(stage_payload.get("region_returns", ()) or ())
                    )
            fact_census_closed = all(
                fact.get("fact_kind") != "call_site"
                or fact.get("output_use_census_status") == "closed"
                for fact in (left_fact, right_fact)
                if fact
            )
            requirement = ProofRequirementId.create(
                "call_effect_summary_proof",
                ("prepared_call_effect_obligation", prepared.surface_digest, obligation_id),
                ProofRequirementContract(
                    proposition="lower proven deferred call relation into comparison queries",
                    relation_direction="ordered",
                    observation_surface=(
                        prepared.certificate.observation_contract_digest,
                        prepared.certificate.semantic_id,
                    ),
                    active_precondition=("obligation_id", obligation_id),
                ),
            )
            consumer_domains = tuple(sorted({
                use_consumer_domain(item)
                for item in (
                    *tuple(left_fact.get("output_use_bindings", ()) or ()),
                    *tuple(right_fact.get("output_use_bindings", ()) or ()),
                )
            }))
            binding_payload = (
                obligation_id,
                obligation.get("observation_contract_id"),
                left_fact.get("identity", {}).get("pcode_op_key"),
                right_fact.get("identity", {}).get("pcode_op_key"),
                tuple(left_fact.get("output_use_bindings", ()) or ()),
                tuple(right_fact.get("output_use_bindings", ()) or ()),
                stage_records,
                relation_kind,
                call_on_left,
                region_return_members,
                consumer_domains,
                width_relation_contract,
                requirement.to_key(),
            )
            semantic_bindings.append(
                CallSemanticProjectionBinding(
                    binding_id=_digest(("call_semantic_projection_binding_v1", binding_payload)),
                    obligation_id=obligation_id,
                    requirement_id=requirement,
                    observation_contract_id=str(obligation.get("observation_contract_id") or ""),
                    left_fact_id=obligation.get("left_fact_id"),
                    right_fact_id=obligation.get("right_fact_id"),
                    left_pcode_op_key=(
                        tuple(left_fact.get("identity", {}).get("pcode_op_key"))
                        if left_fact.get("identity", {}).get("pcode_op_key")
                        else None
                    ),
                    right_pcode_op_key=(
                        tuple(right_fact.get("identity", {}).get("pcode_op_key"))
                        if right_fact.get("identity", {}).get("pcode_op_key")
                        else None
                    ),
                    left_use_bindings=tuple(
                        SnapshotFingerprintCodec.freeze(item)
                        for item in tuple(left_fact.get("output_use_bindings", ()) or ())
                    ),
                    right_use_bindings=tuple(
                        SnapshotFingerprintCodec.freeze(item)
                        for item in tuple(right_fact.get("output_use_bindings", ()) or ())
                    ),
                    proof_stage_records=stage_records,
                    relation_kind=relation_kind,
                    call_on_left=call_on_left,
                    region_return_members=region_return_members,
                    consumer_domains=consumer_domains,
                    status=(
                        "proven"
                        if (
                            artifact_coverage
                            and fact_census_closed
                            and set(consumer_domains).issubset({
                                "value", "guard", "effect",
                            })
                            and (
                                relation_kind != "call_to_region"
                                or (
                                    call_on_left is not None
                                    and bool(region_return_members)
                                )
                            )
                        )
                        else "inconclusive"
                    ),
                    return_width_relation_contract=width_relation_contract,
                )
            )
        semantic_safety_failures = []
        if not use_mapping_valid:
            semantic_safety_failures.append(
                use_mapping_failure or "prepared_use_domain_coverage_mapping_mismatch"
            )
        caller_memory_present = False
        for analysis in (prepared.analysis1, prepared.analysis2):
            effect_summary = getattr(analysis, "effect_summary", None)
            incomplete_reasons = tuple(
                getattr(effect_summary, "incomplete_reasons", ()) or ()
            )
            if incomplete_reasons:
                semantic_safety_failures.append("non_call_effect_unsafety_present")
            if bool(getattr(effect_summary, "has_unsupported_call", False)):
                semantic_safety_failures.append("unsupported_call_effect_present")
            if "effect_summary_path_coverage_incomplete" in tuple(
                getattr(analysis, "analysis_notes", ()) or ()
            ):
                semantic_safety_failures.append("non_call_effect_unsafety_present")
            profile = getattr(effect_summary, "function_control_effect_profile", None)
            caller_memory_present = caller_memory_present or bool(
                tuple(getattr(effect_summary, "effects", ()) or ())
                or int(getattr(profile, "store_count", 0) or 0)
                or sum(
                    int(getattr(item, "memory_effect_count", 0) or 0)
                    for item in tuple(
                        getattr(effect_summary, "call_site_effect_summary_evidence", ()) or ()
                    )
                )
            )
        caller_memory_proven = bool(readiness) and all(
            "caller_memory_relation" in tuple(item.get("completed_stages", ()) or ())
            for item in readiness
        )
        if caller_memory_present and not caller_memory_proven:
            semantic_safety_failures.append("caller_memory_relation_not_proven")
        semantic_bindings_valid = (
            len(semantic_bindings) == len(completed)
            and all(item.status == "proven" for item in semantic_bindings)
        )
        if not semantic_bindings_valid:
            semantic_safety_failures.append("call_semantic_projection_incomplete")
        covered = tuple(sorted(covered_items))
        roots = tuple(sorted(set(
            orphan_blockers + tuple(invalid_items) + tuple(semantic_safety_failures)
        )))
        status = (
            "proven"
            if certificate_valid and readiness_valid and replacement_valid and not roots
            else "inconclusive"
        )
        if status != "proven" and not roots:
            failures = []
            if manifest.get("failure_cause"):
                failures.append(str(manifest.get("failure_cause")))
            if not certificate_valid:
                failures.append("structural_coverage_certificate_incomplete")
            if not readiness_valid:
                failures.append("call_effect_stage_proofs_incomplete")
            if not replacement_valid:
                failures.append("legacy_blocker_replacement_not_ready")
            roots = tuple(failures or ("call_effect_preflight_incomplete",))
    if not required:
        resolution_records = []
        semantic_bindings = []
    completed_requirement_keys = tuple(
        record.requirement_id.to_key() for record in resolution_records
    )
    projection_id = _digest(
        (
            "call_resolution_projection_v1",
            prepared.surface_digest,
            generation,
            status,
            required,
            covered,
            roots,
            completed,
            completed_requirement_keys,
            tuple(semantic_bindings),
            rebuilt_use_mapping.builder_version,
            rebuilt_use_mapping.mapping_digest,
            tuple(
                (
                    side,
                    item.get("fact_id"),
                    item.get("observed_output_use_count"),
                    item.get("output_use_reaching_definition_status"),
                    item.get("output_use_census_status"),
                    item.get("output_use_census_digest"),
                    item.get("output_use_bindings"),
                    item.get("guard_keys"),
                )
                for side in ("left", "right")
                for item in tuple(manifest.get(f"{side}_facts", ()) or ())
                if isinstance(item, Mapping)
            ),
        )
    )
    use_census = tuple(
        (
            side,
            item.get("fact_id"),
            item.get("observed_output_use_count"),
            item.get("output_use_reaching_definition_status"),
            item.get("output_use_census_status"),
            item.get("output_use_census_digest"),
            item.get("output_use_bindings"),
            item.get("guard_keys"),
        )
        for side in ("left", "right")
        for item in tuple(manifest.get(f"{side}_facts", ()) or ())
        if isinstance(item, Mapping)
    )
    mapping_payload = tuple(
        (
            item.get("legacy_blocker"),
            item.get("mapping_basis"),
            item.get("mapping_status"),
            tuple(item.get("obligation_ids", ()) or ()),
        )
        for item in mappings
    )
    return CallResolutionProjection(
        projection_id,
        prepared.surface_digest,
        generation,
        status,
        required,
        covered,
        roots,
        completed,
        completed_requirement_keys,
        tuple(resolution_records),
        tuple(semantic_bindings),
        rebuilt_use_mapping.builder_version,
        _digest(("prepared_call_use_census_v2", rebuilt_use_mapping.payload)),
        _digest(
            (
                "call_use_coverage_mapping_v2",
                rebuilt_use_mapping.builder_version,
                rebuilt_use_mapping.mapping_digest,
                mapping_payload,
                tuple(resolution_records),
                tuple(semantic_bindings),
                use_census,
            )
        ),
    )


@dataclass(frozen=True)
class QueryExecutionRecord:
    query_label: str
    premise_digest: str
    formula_digest: str
    disposition: str
    proof_kind: str
    projection_binding_ids: Tuple[str, ...] = ()
    formula_text: str = field(default="", repr=False, compare=False)
    return_width_observation_view_digest: str = ""
    return_width_binding_receipt_digest: str = ""
    call_site_return_width_receipt_digests: Tuple[str, ...] = ()
    call_site_return_width_receipt_assertion_digests: Tuple[Tuple[str, str], ...] = ()
    canonical_return_width_receipt_digests: Tuple[str, ...] = ()

    def validate(self) -> bool:
        scalar_strings = (
            self.query_label,
            self.premise_digest,
            self.formula_digest,
            self.disposition,
            self.proof_kind,
            self.formula_text,
            self.return_width_observation_view_digest,
            self.return_width_binding_receipt_digest,
        )
        string_tuples = (
            self.projection_binding_ids,
            self.call_site_return_width_receipt_digests,
            self.canonical_return_width_receipt_digests,
        )
        if (
            any(type(value) is not str for value in scalar_strings)
            or any(type(values) is not tuple for values in string_tuples)
            or any(
                type(value) is not str
                for values in string_tuples
                for value in values
            )
            or type(
                self.call_site_return_width_receipt_assertion_digests
            ) is not tuple
            or any(
                type(item) is not tuple
                or len(item) != 2
                or any(type(value) is not str for value in item)
                for item in (
                    self.call_site_return_width_receipt_assertion_digests
                )
            )
        ):
            return False
        evidence = projection_binding_evidence_from_query(self.formula_text)
        call_width_receipts = call_site_return_width_evidence_from_query(
            self.formula_text
        )
        canonical_width_receipts = tuple(sorted(set(
            re.findall(
                r"^; canonical_return_width_binding_receipt ([0-9a-f]{64})$",
                self.formula_text,
                flags=re.MULTILINE,
            )
            + re.findall(
                r"^; binding-receipt ([0-9a-f]{64})$",
                self.formula_text,
                flags=re.MULTILINE,
            )
        )))
        return (
            bool(self.query_label)
            and len(self.premise_digest) == 64
            and len(self.formula_digest) == 64
            and bool(self.formula_text)
            and hashlib.sha256(self.formula_text.encode("utf-8")).hexdigest()
            == self.formula_digest
            and tuple(sorted(evidence)) == tuple(sorted(self.projection_binding_ids))
            and self.disposition in {"unsat", "sat", "unknown", "error"}
            and bool(self.proof_kind)
            and (
                not self.return_width_observation_view_digest
                or len(self.return_width_observation_view_digest) == 64
            )
            and (
                not self.return_width_binding_receipt_digest
                or len(self.return_width_binding_receipt_digest) == 64
            )
            and bool(self.return_width_observation_view_digest)
            == bool(self.return_width_binding_receipt_digest)
            and tuple(sorted(call_width_receipts))
            == tuple(sorted(set(self.call_site_return_width_receipt_digests)))
            and tuple(sorted(call_width_receipts.items()))
            == tuple(sorted(set(
                self.call_site_return_width_receipt_assertion_digests
            )))
            and canonical_width_receipts
            == tuple(sorted(set(self.canonical_return_width_receipt_digests)))
            and (
                not self.return_width_binding_receipt_digest
                or bool(canonical_width_receipts)
            )
        )


_CALL_SITE_RETURN_WIDTH_MARKER = re.compile(
    r"^; call_site_return_width_receipt ([0-9a-f]{64}) "
    r"assertion_sha256=([0-9a-f]{64})$"
)


def call_site_return_width_evidence_from_query(query_text: str) -> Dict[str, str]:
    """Validate that every receipt marker binds the immediately asserted term."""

    lines = str(query_text or "").splitlines()
    evidence: Dict[str, str] = {}
    for index, line in enumerate(lines):
        match = _CALL_SITE_RETURN_WIDTH_MARKER.fullmatch(line)
        if match is None:
            continue
        if index + 1 >= len(lines) or not lines[index + 1].startswith("(assert "):
            return {}
        receipt_digest, expected_assertion_digest = match.groups()
        actual_assertion_digest = hashlib.sha256(
            lines[index + 1].encode("utf-8")
        ).hexdigest()
        if actual_assertion_digest != expected_assertion_digest:
            return {}
        if receipt_digest in evidence and evidence[receipt_digest] != actual_assertion_digest:
            return {}
        evidence[receipt_digest] = actual_assertion_digest
    return evidence


_PROJECTION_BINDING_START = re.compile(
    r"^; call_projection_binding ([0-9a-f]{64}) assertion_sha256=([0-9a-f]{64})$"
)
_PROJECTION_BINDING_END = re.compile(
    r"^; call_projection_binding_end ([0-9a-f]{64})$"
)


def projection_binding_evidence_from_query(query_text: str) -> Dict[str, str]:
    """Recompute binding consumption from exact assertion blocks in a query."""

    lines = str(query_text or "").splitlines()
    evidence: Dict[str, str] = {}
    index = 0
    while index < len(lines):
        match = _PROJECTION_BINDING_START.fullmatch(lines[index])
        if match is None:
            index += 1
            continue
        binding_id, expected_digest = match.groups()
        if binding_id in evidence:
            return {}
        end_index = index + 1
        while end_index < len(lines):
            end_match = _PROJECTION_BINDING_END.fullmatch(lines[end_index])
            if end_match is not None:
                break
            if _PROJECTION_BINDING_START.fullmatch(lines[end_index]) is not None:
                return {}
            end_index += 1
        if end_index >= len(lines) or end_match.group(1) != binding_id:
            return {}
        assertion_text = "\n".join(lines[index + 1 : end_index])
        if (
            not assertion_text.strip()
            or hashlib.sha256(assertion_text.encode("utf-8")).hexdigest()
            != expected_digest
        ):
            return {}
        evidence[binding_id] = expected_digest
        index = end_index + 1
    return evidence


def _no_active_pair_certificate_proven(
    frame: "PreparedDispatchFrame",
    records: Tuple[QueryExecutionRecord, ...],
) -> bool:
    """Fail closed until a relational partition and termination proof exists."""

    # Empty local outcome lists plus terminal census flags are not a relational
    # proof.  A future issuer must validate paired return/divergence partitions
    # and a left/right termination relation before changing this result.
    del frame, records
    return False


@dataclass(frozen=True)
class ComparisonExecutionReceipt:
    receipt_id: str
    comparison_session_id: str
    branch_id: str
    prepared_surface_digest: str
    projection_id: str
    generation: int
    dispatch_nonce: str
    query_records: Tuple[QueryExecutionRecord, ...]
    consumed_projection_binding_ids: Tuple[str, ...]
    disposition_counts: Tuple[Tuple[str, int], ...]
    issuer_kind: str
    status: str
    schema_version: str = "comparison_execution_receipt_v3"
    branch_payload_kind: str = "query_execution_records"
    ledger_binding_digest: str = ""
    quiescence_certificate_digest: str = ""
    closure_snapshot: Tuple[Tuple[Any, ...], ...] = ()
    closure_snapshot_digest: str = ""
    required_projection_binding_ids: Tuple[str, ...] = ()
    excluded_projection_binding_ids: Tuple[str, ...] = ()

    def is_trusted_for(self, frame: "PreparedDispatchFrame") -> bool:
        from scripts.function_tracer_pcode.authority.lifecycle.production_context import (
            comparison_receipt_authority,
        )

        authority = comparison_receipt_authority(self, frame)
        count_map = dict(self.disposition_counts)
        runtime = frame.obligation_runtime
        ledger = frame.pair_disposition_ledger
        runtime_binding_valid = bool(
            self.branch_payload_kind != "pairwise_ledger"
            or (
                runtime is not None
                and ledger is not None
                and runtime.pair_ledger_manager.current is ledger
                and runtime.current_view.view_id == ledger.binding.derived_view_id
                and runtime.premise_digest == ledger.binding.premise_digest
            )
        )
        successor_plan = frame.replan_successor_plan
        successor_binding_valid = bool(
            successor_plan is None
            or (
                ledger is not None
                and frame.successor_ledger_reused
                and frame.replan_successor_ledger is ledger
                and successor_plan.accepts(
                    ledger.binding, ledger.expected_pairs
                )
            )
        )
        return (
            authority is not None
            and authority[0] is frame
            and authority[1] is self
            and frame.authoritative_receipt is self
            and frame.receipt is self
            and
            self.status == "complete"
            and self.comparison_session_id == frame.comparison_session_id
            and self.branch_id == frame.branch_id
            and self.prepared_surface_digest == frame.prepared.surface_digest
            and self.projection_id == frame.projection.projection_id
            and self.generation == frame.generation
            and self.dispatch_nonce == frame.dispatch_nonce
            and self.issuer_kind == "builtin_query_executor_v1"
            and self.schema_version == "comparison_execution_receipt_v3"
            and self.branch_payload_kind in {"pairwise_ledger", "monolithic_query", "query_execution_records"}
            and runtime_binding_valid
            and successor_binding_valid
            and (
                self.branch_payload_kind != "pairwise_ledger"
                or (
                    frame.pair_disposition_ledger is not None
                    and getattr(getattr(frame.pair_disposition_ledger, "lifecycle", None), "value", None) == "sealed"
                    and frame.pair_disposition_ledger.validates_complete_snapshot()
                    and frame.pair_disposition_ledger.closure_snapshot() == self.closure_snapshot
                    and _digest(self.closure_snapshot) == self.closure_snapshot_digest
                )
            )
            and all(record.validate() for record in self.query_records)
            and tuple(sorted(self.consumed_projection_binding_ids))
            == self.consumed_projection_binding_ids
            and tuple(sorted(self.required_projection_binding_ids))
            == self.required_projection_binding_ids
            and tuple(sorted(self.excluded_projection_binding_ids))
            == self.excluded_projection_binding_ids
            and not (
                set(self.consumed_projection_binding_ids)
                & set(self.excluded_projection_binding_ids)
            )
            and (
                set(self.consumed_projection_binding_ids)
                | set(self.excluded_projection_binding_ids)
            ).issubset(set(self.required_projection_binding_ids))
            and count_map.get("projection_no_active_pair_proven")
            == int(_no_active_pair_certificate_proven(frame, self.query_records))
        )

@dataclass
class PreparedDispatchFrame:
    comparison_session_id: str
    branch_id: str
    generation: int
    source: StrategySourceAnalysisPair
    prepared: PreparedAnalysisPair
    projection: CallResolutionProjection
    preflight_manifest: Mapping[str, Any]
    trusted_proof_artifacts: Tuple[Any, ...]
    decision_mode: CallProofDecisionMode
    dispatch_nonce: str = field(default_factory=lambda: uuid4().hex)
    lifecycle_state: str = field(default="unclaimed", init=False)
    receipt: Optional[ComparisonExecutionReceipt] = field(default=None, init=False)
    authoritative_receipt: Optional[ComparisonExecutionReceipt] = field(default=None, init=False)
    shadow_receipt: Optional[ComparisonExecutionReceipt] = field(default=None, init=False)
    receipt_authority_policy: str = field(default="v3_authoritative_v2_shadow", init=False)
    pair_disposition_ledger: Any = field(default=None, init=False, repr=False)
    pair_quiescence_certificate: Any = field(default=None, init=False, repr=False)
    obligation_runtime: Any = field(default=None, init=False, repr=False)
    replan_successor_ledger: Any = field(default=None, init=False, repr=False)
    replan_successor_plan: Any = field(default=None, init=False, repr=False)
    successor_ledger_reused: bool = field(default=False, init=False)
    pending_query_records: Tuple[QueryExecutionRecord, ...] = field(
        default=(), init=False, repr=False
    )
    pending_consumed_projection_binding_ids: Tuple[str, ...] = field(
        default=(), init=False, repr=False
    )
    pending_disposition_counts: Mapping[str, int] = field(
        default_factory=dict, init=False, repr=False
    )
    cleanup_complete: bool = field(default=False, init=False)
    production_branch_authority_lease: Any = field(default=None, repr=False, compare=False)
    monolithic_execution_authority_lease: Any = field(default=None, init=False, repr=False, compare=False)
    monolithic_terminal_receipt: Any = field(default=None, init=False, repr=False, compare=False)
    monolithic_proof_bundle: Any = field(default=None, init=False, repr=False, compare=False)
    monolithic_counterexample_safety_receipt: Any = field(
        default=None, init=False, repr=False, compare=False
    )
    decision_lease: CallProofDecisionLease = field(init=False)
    _lock: Lock = field(default_factory=Lock, init=False, repr=False, compare=False)

    def __post_init__(self) -> None:
        lease = _acquire_decision_lease(
            self.comparison_session_id, self.branch_id, self.generation,
            self.prepared.surface_digest, self.decision_mode,
        )
        self.decision_lease = lease
        try:
            if "MONOLITHIC" in self.branch_id.upper():
                if self.production_branch_authority_lease is None:
                    raise RuntimeError("production_branch_authority_missing")
                from scripts.function_tracer_pcode.proof.monolithic_authority import (
                    derive_monolithic_execution_authority,
                )
                self.monolithic_execution_authority_lease = (
                    derive_monolithic_execution_authority(
                        self.production_branch_authority_lease,
                        prepared_surface_digest=self.prepared.surface_digest,
                        projection_id=self.projection.projection_id,
                        dispatch_nonce=self.dispatch_nonce,
                    )
                )
        except Exception:
            _release_decision_lease(lease)
            raise

    def consume(self, analysis1: Any, analysis2: Any) -> "PreparedDispatchFrame":
        with self._lock:
            if self.lifecycle_state != "unclaimed":
                raise RuntimeError("prepared_dispatch_context_double_consumed")
            if analysis1 is not self.source.analysis1 or analysis2 is not self.source.analysis2:
                raise RuntimeError("projection_context_untrusted")
            if not self.source.is_unchanged():
                raise RuntimeError("prepared_analysis_mutated")
            if not self.prepared.is_valid_for(self.source):
                raise RuntimeError("projection_surface_mismatch")
            self.lifecycle_state = "claimed"
            return self

    def _complete_from_builtin_executor(
        self,
        query_records: Iterable[QueryExecutionRecord],
        consumed_projection_binding_ids: Iterable[str],
        disposition_counts: Mapping[str, int],
        *,
        authority_token: Any,
    ) -> ComparisonExecutionReceipt:
        with self._lock:
            if authority_token is not _BUILTIN_RECEIPT_AUTHORITY_TOKEN:
                raise RuntimeError("comparison_receipt_untrusted_issuer")
            if self.lifecycle_state != "claimed":
                raise RuntimeError("prepared_dispatch_context_scope_closed")
            records = tuple(query_records)
            if not all(isinstance(item, QueryExecutionRecord) and item.validate() for item in records):
                raise RuntimeError("comparison_receipt_query_evidence_invalid")
            consumed_set = {
                str(item) for item in consumed_projection_binding_ids
            }
            required_set = {
                str(binding.binding_id)
                for binding in self.projection.semantic_bindings
            }
            excluded_set = set()
            count_map = {
                str(name): int(count) for name, count in disposition_counts.items()
            }
            count_map["projection_active_total"] = sum(
                1 for record in records if record.projection_binding_ids
            )
            count_map["projection_inactive_total"] = sum(
                1 for record in records if not record.projection_binding_ids
            )
            count_map["projection_no_active_pair_proven"] = int(
                _no_active_pair_certificate_proven(self, records)
            )
            counts = tuple(sorted(count_map.items()))
            ledger = self.pair_disposition_ledger
            branch_payload_kind = (
                "monolithic_query" if "MONOLITHIC" in self.branch_id.upper()
                else "pairwise_ledger" if ledger is not None
                else "query_execution_records"
            )
            if (
                branch_payload_kind == "query_execution_records"
                and int(count_map.get("total", 0) or 0) > 0
            ):
                raise RuntimeError("comparison_receipt_pair_ledger_missing")
            closure_snapshot = ()
            closure_snapshot_digest = ""
            if ledger is not None:
                lifecycle = getattr(getattr(ledger, "lifecycle", None), "value", None)
                if lifecycle != "sealed":
                    raise RuntimeError("comparison_receipt_pair_ledger_unsealed")
                ledger_counts = dict(ledger.counts())
                for name in ("total", "unsat", "sat", "unknown", "error"):
                    if int(ledger_counts.get(name, 0)) != int(count_map.get(name, 0)):
                        raise RuntimeError("comparison_receipt_pair_ledger_count_mismatch")
                binding_key = ledger.binding.stable_key()
                certificate = self.pair_quiescence_certificate
                if certificate is None:
                    raise RuntimeError("comparison_receipt_quiescence_certificate_missing")
                if not certificate.is_quiescent:
                    raise RuntimeError("comparison_receipt_runtime_not_quiescent")
                ledger_binding_digest = _digest(binding_key)
                quiescence_certificate_digest = _digest((
                    "runtime_quiescence_certificate_v1",
                    certificate.binding_key,
                    certificate.expected_pairs,
                    certificate.closed_pairs,
                    certificate.pending_work_items,
                    certificate.provisional_pairs,
                    certificate.pending_work,
                    certificate.active_owner_work,
                ))
                if not ledger.validates_complete_snapshot():
                    raise RuntimeError("comparison_receipt_pair_closure_snapshot_invalid")
                (
                    closure_required,
                    closure_consumed,
                    closure_excluded,
                ) = ledger.binding_use_partitions()
                closure_required_set = set(closure_required)
                if not closure_required_set.issubset(required_set):
                    raise RuntimeError(
                        "comparison_receipt_closure_binding_requirement_invalid"
                    )
                consumed_set.update(closure_consumed)
                excluded_set.update(closure_excluded)
                closure_snapshot = ledger.closure_snapshot()
                closure_snapshot_digest = _digest(closure_snapshot)
            else:
                if branch_payload_kind == "pairwise_ledger" and count_map.get("total", 0) > 0:
                    raise RuntimeError("comparison_receipt_pair_ledger_missing")
                ledger_binding_digest = _digest((
                    "pair_ledger_binding_compatibility_v1",
                    self.comparison_session_id,
                    self.branch_id,
                    self.prepared.surface_digest,
                    self.projection.projection_id,
                    self.generation,
                    self.dispatch_nonce,
                ))
                quiescence_certificate_digest = _digest((
                    "runtime_quiescence_certificate_compatibility_v1",
                    ledger_binding_digest,
                    counts,
                ))
            consumed = tuple(sorted(consumed_set))
            excluded = tuple(sorted(excluded_set - consumed_set))
            required = tuple(sorted(required_set))
            if not (set(consumed) | set(excluded)).issubset(required_set):
                raise RuntimeError("comparison_receipt_binding_partition_invalid")
            receipt_id = _digest(
                (
                    "comparison_execution_receipt_v3",
                    self.comparison_session_id,
                    self.branch_id,
                    self.prepared.surface_digest,
                    self.projection.projection_id,
                    self.generation,
                    self.dispatch_nonce,
                    records,
                    consumed,
                    counts,
                    "builtin_query_executor_v1",
                    branch_payload_kind,
                    ledger_binding_digest,
                    quiescence_certificate_digest,
                    closure_snapshot_digest,
                    required,
                    excluded,
                )
            )
            receipt = ComparisonExecutionReceipt(
                receipt_id,
                self.comparison_session_id,
                self.branch_id,
                self.prepared.surface_digest,
                self.projection.projection_id,
                self.generation,
                self.dispatch_nonce,
                records,
                consumed,
                counts,
                "builtin_query_executor_v1",
                "complete",
                "comparison_execution_receipt_v3",
                branch_payload_kind,
                ledger_binding_digest,
                quiescence_certificate_digest,
                closure_snapshot,
                closure_snapshot_digest,
                required,
                excluded,
            )
            self.authoritative_receipt = receipt
            self.receipt = receipt
            from scripts.function_tracer_pcode.authority.lifecycle.production_context import (
                active_production_pilot_session,
                register_comparison_receipt_authority,
            )

            register_comparison_receipt_authority(
                receipt.receipt_id, self, receipt,
                active_production_pilot_session(),
            )
            return receipt

    def close(self) -> None:
        """No-fail, idempotent capability revocation."""
        with self._lock:
            self.lifecycle_state = "closed"
        from scripts.function_tracer_pcode.proof.monolithic_authority import (
            revoke_monolithic_execution_authority,
        )
        revoke_monolithic_execution_authority(self.monolithic_execution_authority_lease)
        _release_decision_lease(self.decision_lease)


_DISPATCH_STACK: ContextVar[Tuple[PreparedDispatchFrame, ...]] = ContextVar(
    "prepared_pairwise_dispatch_stack", default=()
)


def push_prepared_dispatch_frame(frame: PreparedDispatchFrame) -> Token:
    stack = _DISPATCH_STACK.get()
    if stack and stack[-1].lifecycle_state == "unclaimed":
        raise RuntimeError("prepared_dispatch_context_nested_without_child_lease")
    return _DISPATCH_STACK.set(stack + (frame,))


def consume_prepared_dispatch_frame(analysis1: Any, analysis2: Any) -> PreparedDispatchFrame:
    stack = _DISPATCH_STACK.get()
    if not stack:
        raise RuntimeError("prepared_dispatch_context_missing")
    return stack[-1].consume(analysis1, analysis2)


def close_prepared_dispatch_frame(frame: PreparedDispatchFrame, token: Token) -> bool:
    frame.close()
    try:
        _DISPATCH_STACK.reset(token)
    except Exception:
        frame.cleanup_complete = False
        return False
    frame.cleanup_complete = True
    return True


def current_dispatch_depth() -> int:
    return len(_DISPATCH_STACK.get())


_BUILTIN_RECEIPT_AUTHORITY_TOKEN = object()
_TRUSTED_BUILTIN_EXECUTOR_CODES: Dict[str, Any] = {}
def verify_monolithic_terminal_receipt(frame: PreparedDispatchFrame) -> bool:
    terminal = frame.monolithic_terminal_receipt
    return bool(
        terminal is not None
        and _PINNED_MONOLITHIC_TERMINAL_VERIFIER(terminal)
    )


def verify_monolithic_proof_receipt(frame: PreparedDispatchFrame) -> bool:
    bundle = frame.monolithic_proof_bundle
    return bool(
        bundle is not None
        and _PINNED_MONOLITHIC_PROOF_VERIFIER(bundle)
    )


def register_builtin_receipt_executor(role: str, executor: Any) -> None:
    """Pin one import-time code object per built-in executor role.

    The registry deliberately stores the code object rather than resolving a
    module symbol at receipt-issuance time.  Later monkeypatches therefore
    cannot replace the receipt authority allowlist.
    """

    expected = {
        "pairwise": (
            "function_tracer_pcode.proof.strategies."
            "pairwise_services.orchestration",
            "_impl_check",
        ),
        "monolithic": (
            "function_tracer_pcode.proof.strategies.monolithic",
            "MonolithicStrategy.check",
        ),
    }.get(role)
    if expected is None:
        raise RuntimeError("comparison_receipt_executor_role_invalid")
    executor_module = str(getattr(executor, "__module__", "") or "")
    if (
        not executor_module.endswith(expected[0])
        or getattr(executor, "__qualname__", None) != expected[1]
    ):
        raise RuntimeError("comparison_receipt_executor_identity_invalid")
    code = getattr(executor, "__code__", None)
    if code is None:
        raise RuntimeError("comparison_receipt_executor_code_missing")
    existing = _TRUSTED_BUILTIN_EXECUTOR_CODES.get(role)
    if existing is not None and existing is not code:
        bytecode_equal = marshal.dumps(existing) == marshal.dumps(code)
        try:
            source_equal = (
                existing.co_filename == code.co_filename
                and existing.co_name == code.co_name
                and inspect.getsource(existing) == inspect.getsource(code)
            )
        except (OSError, TypeError):
            source_equal = False
        if not bytecode_equal and not source_equal:
            raise RuntimeError("comparison_receipt_executor_replacement_rejected")
    _TRUSTED_BUILTIN_EXECUTOR_CODES[role] = code


# Compatibility for callers outside the production registration path.
_register_builtin_receipt_executor = register_builtin_receipt_executor


def issue_builtin_comparison_receipt(
    frame: PreparedDispatchFrame,
    *,
    query_records: Iterable[QueryExecutionRecord],
    consumed_projection_binding_ids: Iterable[str],
    disposition_counts: Mapping[str, int],
) -> ComparisonExecutionReceipt:
    """Issue a receipt only from the exact built-in executor code objects."""

    current = inspect.currentframe()
    caller = current.f_back if current is not None else None
    try:
        trusted_codes = set(_TRUSTED_BUILTIN_EXECUTOR_CODES.values())
        if caller is None or caller.f_code not in trusted_codes:
            raise RuntimeError("comparison_receipt_untrusted_issuer")
        return frame._complete_from_builtin_executor(
            query_records,
            consumed_projection_binding_ids,
            disposition_counts,
            authority_token=_BUILTIN_RECEIPT_AUTHORITY_TOKEN,
        )
    finally:
        del caller
        del current


def finalize_pairwise_comparison_receipt(
    frame: PreparedDispatchFrame,
) -> ComparisonExecutionReceipt:
    """Seal and receipt the pair ledger against the final runtime generation."""

    runtime = frame.obligation_runtime
    ledger = frame.pair_disposition_ledger
    if runtime is None or ledger is None:
        raise RuntimeError("pairwise_receipt_runtime_or_ledger_missing")
    if runtime.pair_ledger_manager.current is not ledger:
        raise RuntimeError("pairwise_receipt_ledger_not_current")
    if (
        runtime.current_view.view_id != ledger.binding.derived_view_id
        or runtime.premise_digest != ledger.binding.premise_digest
    ):
        raise RuntimeError("pairwise_receipt_runtime_generation_changed")
    lifecycle = getattr(getattr(ledger, "lifecycle", None), "value", None)
    if lifecycle == "open":
        certificate = runtime.pair_quiescence_certificate(ledger)
        ledger.seal(certificate)
        frame.pair_quiescence_certificate = certificate
    elif lifecycle != "sealed":
        raise RuntimeError("pairwise_receipt_ledger_not_sealable")
    if frame.receipt is None:
        frame._complete_from_builtin_executor(
            frame.pending_query_records,
            frame.pending_consumed_projection_binding_ids,
            frame.pending_disposition_counts,
            authority_token=_BUILTIN_RECEIPT_AUTHORITY_TOKEN,
        )
    if frame.receipt is None or not frame.receipt.is_trusted_for(frame):
        raise RuntimeError("pairwise_receipt_final_runtime_validation_failed")
    return frame.receipt


def finalize_monolithic_comparison_receipt(
    frame: PreparedDispatchFrame,
) -> ComparisonExecutionReceipt:
    """Validate a receipt sealed by the strategy before frame close.

    This function intentionally has no issuance path.  Post-close issuance was
    the authority gap fixed by the monolithic split cutover.
    """

    if frame.lifecycle_state != "closed" or not frame.cleanup_complete:
        raise RuntimeError("monolithic_receipt_dispatch_cleanup_incomplete")
    if frame.receipt is None or not frame.receipt.is_trusted_for(frame):
        raise RuntimeError("monolithic_receipt_final_validation_failed")
    terminal = frame.monolithic_terminal_receipt
    if terminal is None or not verify_monolithic_terminal_receipt(frame):
        raise RuntimeError("monolithic_terminal_receipt_invalid")
    if terminal.comparison_receipt_id != frame.receipt.receipt_id:
        raise RuntimeError("monolithic_terminal_comparison_receipt_mismatch")
    if (
        frame.monolithic_proof_bundle is not None
        and terminal.outcome_kind in {"eq_closure", "decisive_counterexample"}
        and not verify_monolithic_proof_receipt(frame)
    ):
        raise RuntimeError("monolithic_proof_bundle_invalid")
    return frame.receipt


def issue_inconclusive_monolithic_receipts(
    frame: PreparedDispatchFrame,
    frozen_surface: Any,
    canonical_census: Any,
    reason: str,
) -> ComparisonExecutionReceipt:
    """Seal diagnostic-only authority while the frame is active.

    This path cannot authorize EQ or NOT_EQ and is therefore safe for
    fail-closed exception/unsupported-surface exits.
    """
    if frame.lifecycle_state != "claimed":
        raise RuntimeError("prepared_dispatch_context_scope_closed")
    if frame.receipt is None:
        frame._complete_from_builtin_executor(
            (), (), {"total": 0, "unsat": 0, "sat": 0, "unknown": 1, "error": 0},
            authority_token=_BUILTIN_RECEIPT_AUTHORITY_TOKEN,
        )
    from scripts.function_tracer_pcode.proof.monolithic_authority import (
        reconstruct_fallback_census,
        seal_terminal_decision,
    )
    census = canonical_census or reconstruct_fallback_census(frozen_surface)
    reason_digest = hashlib.sha256(str(reason).encode("utf-8")).hexdigest()
    frame.monolithic_terminal_receipt = seal_terminal_decision(
        frame.production_branch_authority_lease,
        frame.monolithic_execution_authority_lease,
        frozen_surface,
        census,
        outcome_kind="inconclusive_diagnostic",
        comparison_receipt_id=frame.receipt.receipt_id,
        region_receipt_digests=(),
        diagnostic_reason_digests=(reason_digest,),
    )
    return frame.receipt


@dataclass(frozen=True)
class TypedProjectionAssertionBundle:
    binding_id: str
    consumer_domains: Tuple[str, ...]
    assertions: Tuple[str, ...]
    assertion_digest: str

    def validates(self) -> bool:
        return (
            bool(self.binding_id)
            and bool(self.assertions)
            and self.assertion_digest
            == hashlib.sha256("\n".join(self.assertions).encode("utf-8")).hexdigest()
        )

    def is_guard_bound(self) -> bool:
        return self.validates() and "guard" in self.consumer_domains


@dataclass(frozen=True)
class LoweredCallProjection:
    assertions: Tuple[str, ...]
    binding_ids: Tuple[str, ...]
    evidence_digest: str
    status: str
    failure_cause: Optional[str] = None
    binding_assertion_digests: Tuple[Tuple[str, str], ...] = ()
    return_width_receipt_digests: Tuple[str, ...] = ()
    return_width_receipt_assertion_digests: Tuple[Tuple[str, str], ...] = ()
    guard_binding_ids: Tuple[str, ...] = ()
    assertion_bundles: Tuple[TypedProjectionAssertionBundle, ...] = ()


def lower_call_projection_for_case_pair(
    frame: PreparedDispatchFrame,
    case1: Any,
    case2: Any,
    *,
    pair_id: str,
    render_fn1: Any = None,
    render_fn2: Any = None,
) -> LoweredCallProjection:
    """Lower exact call-result relations for one pairwise case pair."""

    def normalized(value: Any) -> Any:
        if isinstance(value, (tuple, list)):
            return tuple(normalized(item) for item in value)
        if isinstance(value, Mapping):
            return tuple(
                (str(key), normalized(item))
                for key, item in sorted(value.items(), key=lambda pair: str(pair[0]))
            )
        return value

    def expressions_for_pcode(case: Any, pcode_key: Optional[Tuple[Any, ...]]) -> Tuple[Any, ...]:
        if pcode_key is None:
            return ()
        matches = []
        seen = set()

        def visit(expr: Any) -> None:
            if expr is None or id(expr) in seen:
                return
            seen.add(id(expr))
            runtime_ref = getattr(expr, "runtime_ref", None)
            deferred_ref = getattr(runtime_ref, "deferred_call_ref", None)
            op_ref = getattr(deferred_ref, "pcode_op_ref", None)
            stable_key = getattr(op_ref, "stable_key", None)
            if callable(stable_key) and normalized(stable_key()) == normalized(pcode_key):
                matches.append(expr)
            for operand in tuple(getattr(expr, "operands", ()) or ()):
                visit(operand)
            value = getattr(expr, "value", None)
            if isinstance(value, (tuple, list)):
                for item in value:
                    if isinstance(item, (tuple, list)) and len(item) == 2:
                        visit(getattr(item[0], "expression", None))
                        visit(item[1])

        if hasattr(case, "returns"):
            for ret in tuple(getattr(case, "returns", ()) or ()):
                visit(getattr(ret, "value", None))
                for condition in tuple(getattr(ret, "conditions", ()) or ()):
                    visit(getattr(condition, "expression", None))
            for outcome in tuple(getattr(case, "return_outcomes", ()) or ()):
                visit(getattr(outcome, "value", None))
                for condition in tuple(getattr(outcome, "guard", ()) or ()):
                    visit(getattr(condition, "expression", None))
            for candidate in tuple(getattr(case, "summary_return_candidates", ()) or ()):
                ret = getattr(candidate, "return_info", None)
                visit(getattr(ret, "value", None))
                for condition in tuple(getattr(ret, "conditions", ()) or ()):
                    visit(getattr(condition, "expression", None))
        else:
            visit(getattr(case, "value_expr", None))
            for condition in tuple(getattr(case, "conditions", ()) or ()):
                visit(getattr(condition, "expression", None))
        return tuple(matches)

    def unresolved_pcode_keys(case: Any) -> Tuple[Any, ...]:
        keys = []
        seen = set()

        def visit(expr: Any) -> None:
            if expr is None or id(expr) in seen:
                return
            seen.add(id(expr))
            if getattr(getattr(expr, "expr_type", None), "name", None) == "UNKNOWN":
                runtime_ref = getattr(expr, "runtime_ref", None)
                deferred_ref = getattr(runtime_ref, "deferred_call_ref", None)
                op_ref = getattr(deferred_ref, "pcode_op_ref", None)
                stable_key = getattr(op_ref, "stable_key", None)
                keys.append(
                    normalized(stable_key())
                    if callable(stable_key)
                    else ("unresolved_without_deferred_call_identity",)
                )
            for operand in tuple(getattr(expr, "operands", ()) or ()):
                visit(operand)
            value = getattr(expr, "value", None)
            if isinstance(value, (tuple, list)):
                for item in value:
                    if isinstance(item, (tuple, list)) and len(item) == 2:
                        visit(getattr(item[0], "expression", None))
                        visit(item[1])

        if hasattr(case, "returns"):
            for ret in tuple(getattr(case, "returns", ()) or ()):
                visit(getattr(ret, "value", None))
                for condition in tuple(getattr(ret, "conditions", ()) or ()):
                    visit(getattr(condition, "expression", None))
            for outcome in tuple(getattr(case, "return_outcomes", ()) or ()):
                visit(getattr(outcome, "value", None))
                for condition in tuple(getattr(outcome, "guard", ()) or ()):
                    visit(getattr(condition, "expression", None))
        else:
            visit(getattr(case, "value_expr", None))
            for condition in tuple(getattr(case, "conditions", ()) or ()):
                visit(getattr(condition, "expression", None))
        return tuple(keys)

    def frozen_field(item: Any, name: str) -> Any:
        if isinstance(item, Mapping):
            return item.get(name)
        for pair in tuple(item or ()):
            if isinstance(pair, (tuple, list)) and len(pair) == 2 and pair[0] == name:
                return pair[1]
        return None

    def condition_member(condition: Any) -> Tuple[Any, ...]:
        structural_key = getattr(condition, "structural_key", None)
        return (
            "condition",
            bool(getattr(condition, "negated", False)),
            structural_key() if callable(structural_key) else None,
        )

    def active_uses(
        case: Any,
        uses: Tuple[Tuple[Any, ...], ...],
        pcode_key: Optional[Tuple[Any, ...]],
    ) -> Tuple[Tuple[Any, ...], bool]:
        if hasattr(case, "returns"):
            return tuple(uses), True
        source_indices = {
            int(item) for item in tuple(getattr(case, "source_indices", ()) or ())
        }
        case_guard_keys = set(
            condition_member(item)
            for item in tuple(
                getattr(getattr(case, "return_info", None), "conditions", ()) or ()
            )
        )
        active = []
        mapping_closed = True
        for use in uses:
            location = frozen_field(use, "semantic_location")
            domain = location[0] if isinstance(location, (tuple, list)) and location else None
            if domain == "effects":
                # Effects are function-level observations.  Their exact value
                # relation is discharged by caller_memory_relation rather than
                # by a return-case expression.
                active.append(use)
                continue
            if domain in {"return_outcomes", "summary_return_candidates"}:
                # These are function-level return observations validated by the
                # typed return-relation stage; they are not indexed by the
                # legacy ReturnCase.source_indices array.
                active.append(use)
                continue
            if not (
                isinstance(location, (tuple, list))
                and len(location) >= 2
                and location[0] == "returns"
                and int(location[1]) in source_indices
            ):
                continue
            use_guard_keys = set(frozen_field(use, "use_guard_keys") or ())
            if not use_guard_keys.issubset(case_guard_keys):
                mapping_closed = False
                continue
            active.append(use)
        return tuple(active), mapping_closed

    def case_region_member(case: Any) -> Any:
        ret = getattr(case, "return_info", None)
        if ret is None:
            return None
        return SnapshotFingerprintCodec.freeze(
            {
                "address": getattr(ret, "address", None),
                "conditions": tuple(
                    condition_member(item)
                    for item in tuple(getattr(ret, "conditions", ()) or ())
                ),
                "value": expression_provenance_key(getattr(ret, "value", None)),
                "return_kind": getattr(ret, "return_kind", None),
                "acceptance_status": getattr(ret, "acceptance_status", None),
                "validation_blockers": tuple(
                    getattr(ret, "validation_blockers", ()) or ()
                ),
            }
        )

    def rendered(expr: Any, render_fn: Any) -> str:
        if callable(render_fn):
            return str(render_fn(expr))
        return str(expr.to_smt(float_mode="fp"))

    assertions = [
        f"; certified call projection for pair {pair_id}",
        f"; projection_id {frame.projection.projection_id}",
    ]
    consumed = []
    evidence = []
    binding_assertion_digests = []
    guard_binding_ids = []
    assertion_bundles = []
    return_width_receipt_digests = []
    return_width_receipt_assertion_digests = []
    expected_left_unresolved_keys = []
    expected_right_unresolved_keys = []
    known_uncovered_left_keys = []
    known_uncovered_right_keys = []
    for binding in frame.projection.semantic_bindings:
        assertion_start = len(assertions)
        left_exprs = expressions_for_pcode(case1, binding.left_pcode_op_key)
        right_exprs = expressions_for_pcode(case2, binding.right_pcode_op_key)
        left_active_uses, left_mapping_closed = active_uses(
            case1, binding.left_use_bindings, binding.left_pcode_op_key
        )
        right_active_uses, right_mapping_closed = active_uses(
            case2, binding.right_use_bindings, binding.right_pcode_op_key
        )
        if not left_mapping_closed or not right_mapping_closed:
            return LoweredCallProjection(
                (),
                (),
                _digest((
                    "call_projection_lowering_v2",
                    pair_id,
                    binding.binding_id,
                    "case_guard_mapping",
                )),
                "inconclusive",
                "call_projection_case_guard_mapping_incomplete",
            )
        left_effect_uses = tuple(
            use for use in left_active_uses
            if (frozen_field(use, "semantic_location") or (None,))[0] == "effects"
        )
        right_effect_uses = tuple(
            use for use in right_active_uses
            if (frozen_field(use, "semantic_location") or (None,))[0] == "effects"
        )
        effect_proof_consumed = bool(left_effect_uses or right_effect_uses)
        if effect_proof_consumed:
            stage_names = {item[0] for item in binding.proof_stage_records}
            if "caller_memory_relation" not in stage_names:
                return LoweredCallProjection(
                    (),
                    (),
                    _digest(("call_projection_lowering_v3", pair_id, binding.binding_id, "effect_proof")),
                    "inconclusive",
                    "call_projection_effect_proof_missing",
                )
            effect_use_ids = tuple(
                frozen_field(use, "use_id")
                for use in (*left_effect_uses, *right_effect_uses)
            )
            assertions.append(
                f"; effect consumer caller_memory_relation use_ids={_digest(effect_use_ids)}"
            )
            assertions.append("(assert true)")
        proof_return_domains = {"return_outcomes", "summary_return_candidates"}
        left_return_proof_uses = tuple(
            use for use in left_active_uses
            if (frozen_field(use, "semantic_location") or (None,))[0]
            in proof_return_domains
        )
        right_return_proof_uses = tuple(
            use for use in right_active_uses
            if (frozen_field(use, "semantic_location") or (None,))[0]
            in proof_return_domains
        )
        return_proof_consumed = bool(
            left_return_proof_uses or right_return_proof_uses
        )
        if return_proof_consumed:
            stage_names = {item[0] for item in binding.proof_stage_records}
            if "return_relation" not in stage_names:
                return LoweredCallProjection(
                    (),
                    (),
                    _digest(("call_projection_lowering_v3", pair_id, binding.binding_id, "return_surface_proof")),
                    "inconclusive",
                    "call_projection_return_surface_proof_missing",
                )
            return_use_ids = tuple(
                frozen_field(use, "use_id")
                for use in (*left_return_proof_uses, *right_return_proof_uses)
            )
            assertions.append(
                f"; return surface consumer return_relation use_ids={_digest(return_use_ids)}"
            )
            assertions.append("(assert true)")
        left_value_uses = tuple(
            use for use in left_active_uses if use not in left_effect_uses
            and use not in left_return_proof_uses
        )
        right_value_uses = tuple(
            use for use in right_active_uses if use not in right_effect_uses
            and use not in right_return_proof_uses
        )
        expected_left = len(left_value_uses)
        expected_right = len(right_value_uses)
        globally_unobserved = (
            not binding.left_use_bindings and not binding.right_use_bindings
        )
        if expected_left == 0 and expected_right == 0 and (
            effect_proof_consumed or return_proof_consumed
        ):
            pass
        elif expected_left == 0 and expected_right == 0 and globally_unobserved:
            assertions.append(
                f"; binding {binding.binding_id}: return unobserved, effect/termination proof consumed"
            )
            assertions.append("(assert true)")
        elif expected_left == 0 and expected_right == 0:
            if left_exprs or right_exprs:
                return LoweredCallProjection(
                    (),
                    (),
                    _digest(("call_projection_lowering_v2", pair_id, binding.binding_id, "inactive")),
                    "inconclusive",
                    "call_projection_case_use_mapping_mismatch",
                )
            continue
        elif (
            expected_left > 0
            and expected_right > 0
            and len(left_exprs) == expected_left
            and len(right_exprs) == expected_right
        ):
            expected_left_unresolved_keys.append(normalized(binding.left_pcode_op_key))
            expected_right_unresolved_keys.append(normalized(binding.right_pcode_op_key))
            expression_pairs = tuple(
                (left_expr, right_exprs[0]) for left_expr in left_exprs
            ) + tuple(
                (left_exprs[0], right_expr) for right_expr in right_exprs[1:]
            )
            for left_expr, right_expr in expression_pairs:
                int(getattr(left_expr, "get_bit_width", lambda: 0)() or 0)
                int(getattr(right_expr, "get_bit_width", lambda: 0)() or 0)
                from scripts.function_tracer_pcode.proof.return_width.surface import (
                    BlockedObservation,
                    build_call_site_return_width_receipt,
                )
                left_term = rendered(left_expr, render_fn1)
                right_term = rendered(right_expr, render_fn2)
                receipt = build_call_site_return_width_receipt(
                    binding=binding,
                    pair_id=pair_id,
                    left_expr=left_expr,
                    right_expr=right_expr,
                    lowered_left_term=left_term,
                    lowered_right_term=right_term,
                )
                if isinstance(receipt, BlockedObservation):
                    return LoweredCallProjection(
                        (),
                        (),
                        _digest(("call_projection_lowering_v1", pair_id, binding.binding_id, "width")),
                        "inconclusive",
                        "call_projection_width_mismatch",
                    )
                assertions.append(
                    f"; call_site_return_width_receipt {receipt.binding_digest} "
                    f"assertion_sha256={receipt.assertion_digest}"
                )
                assertions.append(receipt.assertion_text)
                return_width_receipt_digests.append(receipt.binding_digest)
                return_width_receipt_assertion_digests.append(
                    (receipt.binding_digest, receipt.assertion_digest)
                )
        elif (
            binding.relation_kind == "call_to_region"
            and ((expected_left > 0) != (expected_right > 0))
            and len(left_exprs) == expected_left
            and len(right_exprs) == expected_right
        ):
            call_is_left = expected_left > 0
            if call_is_left:
                expected_left_unresolved_keys.append(normalized(binding.left_pcode_op_key))
            else:
                expected_right_unresolved_keys.append(normalized(binding.right_pcode_op_key))
            if binding.call_on_left is not call_is_left:
                return LoweredCallProjection(
                    (),
                    (),
                    _digest(("call_projection_lowering_v2", pair_id, binding.binding_id, "direction")),
                    "inconclusive",
                    "call_projection_region_direction_mismatch",
                )
            region_case = case2 if call_is_left else case1
            if case_region_member(region_case) not in binding.region_return_members:
                return LoweredCallProjection(
                    (),
                    (),
                    _digest(("call_projection_lowering_v2", pair_id, binding.binding_id, "region_member")),
                    "inconclusive",
                    "call_projection_region_member_mismatch",
                )
            call_exprs = left_exprs if call_is_left else right_exprs
            call_render_fn = render_fn1 if call_is_left else render_fn2
            region_render_fn = render_fn2 if call_is_left else render_fn1
            region_value = getattr(region_case, "value_expr", None)
            if region_value is None:
                return LoweredCallProjection(
                    (),
                    (),
                    _digest(("call_projection_lowering_v2", pair_id, binding.binding_id, "region_value")),
                    "inconclusive",
                    "call_projection_region_value_missing",
                )
            call_bits = int(getattr(call_exprs[0], "get_bit_width", lambda: 0)() or 0)
            region_bits = int(getattr(region_value, "get_bit_width", lambda: 0)() or 0)
            for call_expr in call_exprs:
                left_expr = call_expr if call_is_left else region_value
                right_expr = region_value if call_is_left else call_expr
                left_render = call_render_fn if call_is_left else region_render_fn
                right_render = region_render_fn if call_is_left else call_render_fn
                from scripts.function_tracer_pcode.proof.return_width.surface import (
                    BlockedObservation,
                    build_call_site_return_width_receipt,
                )
                left_term = rendered(left_expr, left_render)
                right_term = rendered(right_expr, right_render)
                receipt = build_call_site_return_width_receipt(
                    binding=binding,
                    pair_id=pair_id,
                    left_expr=left_expr,
                    right_expr=right_expr,
                    lowered_left_term=left_term,
                    lowered_right_term=right_term,
                )
                if isinstance(receipt, BlockedObservation):
                    return LoweredCallProjection(
                        (),
                        (),
                        _digest(("call_projection_lowering_v2", pair_id, binding.binding_id, call_bits, region_bits)),
                        "inconclusive",
                        "call_projection_width_mismatch",
                    )
                assertions.append(
                    f"; call_site_return_width_receipt {receipt.binding_digest} "
                    f"assertion_sha256={receipt.assertion_digest}"
                )
                assertions.append(receipt.assertion_text)
                return_width_receipt_digests.append(receipt.binding_digest)
                return_width_receipt_assertion_digests.append(
                    (receipt.binding_digest, receipt.assertion_digest)
                )
        elif (
            binding.relation_kind == "call_to_call"
            and ((expected_left > 0) != (expected_right > 0))
            and len(left_exprs) == expected_left
            and len(right_exprs) == expected_right
        ):
            # Do not force a value relation across mutually exclusive call
            # regions.  The guard-only query runs first.  If the regions do
            # overlap, the still-uncovered UNKNOWN makes the value stage
            # conservatively return UNKNOWN.
            if expected_left:
                known_uncovered_left_keys.append(normalized(binding.left_pcode_op_key))
            if expected_right:
                known_uncovered_right_keys.append(normalized(binding.right_pcode_op_key))
            continue
        else:
            return LoweredCallProjection(
                (),
                (),
                _digest(
                    (
                        "call_projection_lowering_v1",
                        pair_id,
                        binding.binding_id,
                        expected_left,
                        expected_right,
                        len(left_exprs),
                        len(right_exprs),
                    )
                ),
                "inconclusive",
                "call_projection_use_binding_mismatch",
            )
        consumed.append(binding.binding_id)
        if "guard" in set(binding.consumer_domains):
            guard_binding_ids.append(binding.binding_id)
        binding_assertions = tuple(assertions[assertion_start:])
        assertion_text = "\n".join(binding_assertions)
        assertion_digest = hashlib.sha256(
            assertion_text.encode("utf-8")
        ).hexdigest()
        assertions.insert(
            assertion_start,
            f"; call_projection_binding {binding.binding_id} assertion_sha256={assertion_digest}",
        )
        assertions.append(f"; call_projection_binding_end {binding.binding_id}")
        binding_assertion_digests.append((binding.binding_id, assertion_digest))
        assertion_bundles.append(TypedProjectionAssertionBundle(
            binding.binding_id,
            tuple(sorted(binding.consumer_domains)),
            binding_assertions,
            assertion_digest,
        ))
        evidence.append(
            (
                binding.binding_id,
                tuple(item[0] for item in binding.proof_stage_records),
                len(left_exprs),
                len(right_exprs),
                len(left_active_uses),
                len(right_active_uses),
            )
        )
    actual_left_unresolved_keys = unresolved_pcode_keys(case1)
    actual_right_unresolved_keys = unresolved_pcode_keys(case2)
    if (
        set(actual_left_unresolved_keys)
        != set(expected_left_unresolved_keys + known_uncovered_left_keys)
        or set(actual_right_unresolved_keys)
        != set(expected_right_unresolved_keys + known_uncovered_right_keys)
    ):
        return LoweredCallProjection(
            (),
            (),
            _digest(
                (
                    "call_projection_lowering_v1",
                    pair_id,
                    actual_left_unresolved_keys,
                    actual_right_unresolved_keys,
                    tuple(expected_left_unresolved_keys),
                    tuple(expected_right_unresolved_keys),
                )
            ),
            "inconclusive",
            "call_projection_unresolved_census_mismatch",
        )
    return LoweredCallProjection(
        tuple(assertions),
        tuple(sorted(consumed)),
        _digest(("call_projection_lowering_v1", pair_id, tuple(evidence), tuple(assertions))),
        "proven",
        binding_assertion_digests=tuple(sorted(binding_assertion_digests)),
        return_width_receipt_digests=tuple(sorted(set(return_width_receipt_digests))),
        return_width_receipt_assertion_digests=tuple(sorted(set(
            return_width_receipt_assertion_digests
        ))),
        guard_binding_ids=tuple(sorted(set(guard_binding_ids))),
        assertion_bundles=tuple(sorted(assertion_bundles, key=lambda item: item.binding_id)),
    )


def diagnostic_projection(
    manifest: Mapping[str, Any],
    frame: PreparedDispatchFrame,
) -> Dict[str, Any]:
    """Project validated preflight state without producing proofs or decisions."""
    projected = dict(manifest)
    projected["decision_mode"] = "preflight_projection"
    projected["preflight_projection"] = {
        "status": frame.projection.status,
        "required": frame.projection.required,
        "projection_id": frame.projection.projection_id,
        "prepared_surface_digest": frame.prepared.surface_digest,
        "normalization_certificate_semantic_id": frame.prepared.certificate.semantic_id,
        "normalization_certificate_instance_id": frame.prepared.certificate.instance_id,
        "surface_delta_audit_id": (
            frame.prepared.certificate.surface_delta_audit.audit_id
        ),
        "semantic_transformation_certificate_id": (
            frame.prepared.certificate.semantic_transformation.certificate_id
        ),
        "normalization_trust_basis": (
            frame.prepared.certificate.semantic_transformation.trust_basis
        ),
        "normalization_changed_roots": dict(
            frame.prepared.certificate.surface_delta_audit.changed_roots
        ),
        "covered_blockers": list(frame.projection.covered_blockers),
        "root_blockers": list(frame.projection.root_blockers),
        "completed_obligation_ids": list(frame.projection.completed_obligation_ids),
        "completed_requirement_ids": [
            record.requirement_id.to_dict()
            for record in frame.projection.blocker_resolutions
        ],
        "blocker_resolutions": [
            record.to_dict() for record in frame.projection.blocker_resolutions
        ],
        "semantic_bindings": [
            binding.to_dict() for binding in frame.projection.semantic_bindings
        ],
        "use_mapping_builder_version": frame.projection.use_mapping_builder_version,
        "use_census_digest": frame.projection.use_census_digest,
        "coverage_mapping_digest": frame.projection.coverage_mapping_digest,
        "comparison_receipt_id": frame.receipt.receipt_id if frame.receipt else None,
        "comparison_receipt_schema_version": (
            frame.receipt.schema_version if frame.receipt else None
        ),
        "comparison_receipt_branch_payload_kind": (
            frame.receipt.branch_payload_kind if frame.receipt else None
        ),
        "comparison_receipt_ledger_binding_digest": (
            frame.receipt.ledger_binding_digest if frame.receipt else None
        ),
        "comparison_receipt_quiescence_certificate_digest": (
            frame.receipt.quiescence_certificate_digest if frame.receipt else None
        ),
        "comparison_receipt_closure_snapshot_digest": (
            frame.receipt.closure_snapshot_digest if frame.receipt else None
        ),
        "comparison_receipt_required_projection_binding_ids": (
            list(frame.receipt.required_projection_binding_ids)
            if frame.receipt else None
        ),
        "comparison_receipt_consumed_projection_binding_ids": (
            list(frame.receipt.consumed_projection_binding_ids)
            if frame.receipt else None
        ),
        "comparison_receipt_excluded_projection_binding_ids": (
            list(frame.receipt.excluded_projection_binding_ids)
            if frame.receipt else None
        ),
        "comparison_receipt_disposition_counts": (
            dict(frame.receipt.disposition_counts) if frame.receipt else None
        ),
        "dispatch_cleanup_complete": frame.cleanup_complete,
        "comparison_receipt_successor_ledger_reused": (
            frame.successor_ledger_reused
            if frame.replan_successor_plan is not None else None
        ),
        "decision_effect": "diagnostic_projection_only",
    }
    disabled = "completed_recovery_proofs_disabled" in frame.projection.root_blockers
    if disabled:
        projected["phase2_discharge_gate"] = {
            "status": "disabled",
            "decision_effect": "diagnostic_only",
            "failure_cause": "completed_recovery_proofs_disabled",
        }
    else:
        priority = (
            "non_call_effect_unsafety_present",
            "unsupported_call_effect_present",
            "caller_memory_relation_not_proven",
            "structural_coverage_certificate_incomplete",
            "call_effect_stage_proofs_incomplete",
            "legacy_blocker_replacement_not_ready",
        )
        failure_cause = next(
            (item for item in priority if item in frame.projection.root_blockers),
            frame.projection.root_blockers[0]
            if frame.projection.root_blockers
            else "call_effect_preflight_incomplete",
        )
        projected["phase2_discharge_gate"] = {
            "status": "proven" if frame.projection.proven else "blocked",
            "decision_effect": (
                "preflight_veto_only" if frame.projection.proven else "blocks_equivalence"
            ),
            "failure_cause": (
                None if frame.projection.proven else failure_cause
            ),
        }
        if frame.projection.proven:
            projected["phase2_discharge_gate"]["proof_kind"] = (
                "typed_pure_direct_call_relational_preflight"
            )
        elif failure_cause == "non_call_effect_unsafety_present":
            projected["phase2_discharge_gate"]["non_call_effect_unsafety"] = list(
                dict.fromkeys(
                    str(reason)
                    for analysis in (frame.prepared.analysis1, frame.prepared.analysis2)
                    for reason in tuple(
                        getattr(getattr(analysis, "effect_summary", None), "incomplete_reasons", ()) or ()
                    )
                )
            )
        elif failure_cause == "caller_memory_relation_not_proven":
            caller_memory_effects = []
            for side, analysis in (
                ("function1", frame.prepared.analysis1),
                ("function2", frame.prepared.analysis2),
            ):
                effect_summary = getattr(analysis, "effect_summary", None)
                profile = getattr(effect_summary, "function_control_effect_profile", None)
                effect_count = len(tuple(getattr(effect_summary, "effects", ()) or ()))
                explicit_store_count = int(getattr(profile, "store_count", 0) or 0)
                call_derived_store_count = sum(
                    int(getattr(item, "memory_effect_count", 0) or 0)
                    for item in tuple(
                        getattr(effect_summary, "call_site_effect_summary_evidence", ()) or ()
                    )
                )
                if effect_count or explicit_store_count or call_derived_store_count:
                    caller_memory_effects.append({
                        "side": side,
                        "effect_count": effect_count,
                        "explicit_store_count": explicit_store_count,
                        "call_derived_store_count": call_derived_store_count,
                    })
            projected["phase2_discharge_gate"]["caller_memory_effects"] = caller_memory_effects
    if frame.projection.proven:
        summary = projected.get("summary")
        if isinstance(summary, dict):
            summary["semantic_proof_status"] = "proven"
    return projected


__all__ = [
    "CallProofDecisionMode",
    "CallProofDecisionLease",
    "CallResolutionProjection",
    "ComparisonExecutionReceipt",
    "NormalizationCertificate",
    "PreparedAnalysisPair",
    "PreparedDispatchFrame",
    "StrategySourceAnalysisPair",
    "close_prepared_dispatch_frame",
    "consume_prepared_dispatch_frame",
    "current_dispatch_depth",
    "diagnostic_projection",
    "prepare_solver_surface",
    "push_prepared_dispatch_frame",
    "validate_call_resolution_projection",
]
