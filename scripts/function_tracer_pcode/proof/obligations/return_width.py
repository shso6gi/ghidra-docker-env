"""Function-local return-width proof production and cache reuse."""

from __future__ import annotations

from dataclasses import dataclass
from typing import Any, Optional, Tuple

from scripts.function_tracer_pcode.proof.cause_identity import (
    ProofRequirementContract,
    ProofRequirementId,
)
from scripts.function_tracer_pcode.proof.return_width.surface import (
    ExtensionKind,
    FunctionReturnWidthSeed,
    RETURN_WIDTH_NORMALIZATION_POLICY,
    ValidatedUnaryWidthArtifact,
)
from scripts.function_tracer_pcode.proof.obligations.cache import ValidatedUnaryArtifactEntry
from scripts.function_tracer_pcode.proof.obligations.model import (
    FunctionProofOutcome,
    ProofArtifact,
    UnaryArtifactDomain,
)
from scripts.function_tracer_pcode.proof.obligations.runtime import ObligationRuntimeSession


RETURN_WIDTH_PRODUCER_VERSION = "function-return-width-producer-v1"
RETURN_WIDTH_ENCODING_VERSION = "function-return-width-structural-v1"


@dataclass(frozen=True)
class UnaryWidthProofResult:
    status: str
    blocker_kind: Optional[str] = None
    validated_artifact: Optional[ValidatedUnaryWidthArtifact] = None
    cache_entry: Optional[ValidatedUnaryArtifactEntry] = None
    cache_hit: bool = False

    @property
    def complete(self) -> bool:
        return self.status == "proved" and self.validated_artifact is not None


def return_width_requirement(seed: FunctionReturnWidthSeed) -> ProofRequirementId:
    return ProofRequirementId.create(
        "unary_return_width_relation",
        seed.target_id.stable_key(),
        ProofRequirementContract(
            proposition="return storage equals the declared semantic payload relation",
            relation_direction="unary",
            observation_surface=(
                seed.storage_width,
                seed.payload_width,
                seed.extension_evidence_source.kind,
                seed.normalization_policy_digest,
            ),
            active_precondition=(seed.digest,),
        ),
    )


def _validate_structural_relation(seed: FunctionReturnWidthSeed) -> Tuple[bool, str]:
    if not seed.complete:
        return False, "return_width_seed_incomplete"
    storage = int(seed.storage_width or 0)
    payload = int(seed.payload_width or 0)
    if storage <= 0 or payload <= 0:
        return False, "return_width_nonpositive"
    evidence = seed.extension_evidence_source
    if evidence.kind == ExtensionKind.SAME_WIDTH.value:
        if storage != payload or evidence.storage_value_ref != evidence.payload_value_ref:
            return False, "same_width_identity_flow_invalid"
        if evidence.identity_flow_kind != "same_expression":
            return False, "same_width_identity_flow_missing"
        return True, "same_width_identity_flow"
    if evidence.kind in {
        ExtensionKind.ZERO_EXTEND.value,
        ExtensionKind.SIGN_EXTEND.value,
    }:
        if storage <= payload:
            return False, "extension_width_relation_invalid"
        if evidence.storage_value_ref == evidence.payload_value_ref:
            return False, "extension_payload_identity_missing"
        if evidence.identity_flow_kind != "certified_return_input_def_chain":
            return False, "extension_return_input_flow_missing"
        if not evidence.data_flow_certificate_key:
            return False, "extension_data_flow_certificate_missing"
        if not evidence.producer_refs or not evidence.detail:
            return False, "extension_producer_provenance_missing"
        return True, evidence.kind
    return False, "unsupported_extension_relation"


def prove_function_return_width(
    analysis: Any,
    seed: FunctionReturnWidthSeed,
    *,
    normalization_policy_digest: str = RETURN_WIDTH_NORMALIZATION_POLICY,
) -> UnaryWidthProofResult:
    """Prove or reuse one function-local return-member width relation.

    This producer intentionally has no peer function, side label, pair id, or
    counterexample in its premise.  Unsupported relations remain blocked.
    """

    if seed.normalization_policy_digest != str(normalization_policy_digest):
        return UnaryWidthProofResult("blocked", "normalization_policy_mismatch")
    valid, basis = _validate_structural_relation(seed)
    if not valid:
        return UnaryWidthProofResult("blocked", basis)

    runtime = ObligationRuntimeSession.create_unary(
        analysis,
        domain=UnaryArtifactDomain.RETURN_WIDTH_V1,
        semantic_seed=seed,
        domain_contract=("function_return_width", seed.target_id.stable_key()),
        normalization_policy_digest=normalization_policy_digest,
    )
    requirement = return_width_requirement(seed)
    snapshot_fingerprint = str(runtime.current_view.semantic_surface["function_snapshot"])
    function_premise_digest = runtime.premise_digest
    cached = runtime.unary_artifact_cache.get(
        requirement.to_key(),
        function_premise_digest,
        domain=UnaryArtifactDomain.RETURN_WIDTH_V1,
        function_snapshot_fingerprint=snapshot_fingerprint,
        semantic_seed_digest=seed.digest,
        normalization_policy_digest=normalization_policy_digest,
        producer_version=RETURN_WIDTH_PRODUCER_VERSION,
        encoding_version=RETURN_WIDTH_ENCODING_VERSION,
    )
    if cached is not None:
        validated = ValidatedUnaryWidthArtifact(
            seed=seed,
            proof_artifact=cached.artifact,
            relation=seed.extension_evidence_source.kind,
            validation_basis=("validated_unary_cache", basis),
        )
        return UnaryWidthProofResult(
            "proved", validated_artifact=validated, cache_entry=cached, cache_hit=True
        )

    runtime.proof_outcomes[requirement.to_key()] = FunctionProofOutcome.EQUIVALENT
    runtime._apply_artifact(requirement, {
        "proof_requirement_id": requirement.to_dict(),
        "proof_status": "complete",
        "proof_source": "function_return_width_structural_relation",
        "semantic_seed_digest": seed.digest,
        "normalization_policy_digest": normalization_policy_digest,
        "validation_basis": basis,
    })
    raw = runtime.artifacts[-1]
    artifact = ProofArtifact(
        artifact_id=raw.artifact_id,
        requirement_id=raw.requirement_id,
        produced_from_view_id=raw.produced_from_view_id,
        premise_digest=raw.premise_digest,
        dependency_artifact_ids=raw.dependency_artifact_ids,
        producer_id="function_return_width",
        producer_version=RETURN_WIDTH_PRODUCER_VERSION,
        encoding_version=RETURN_WIDTH_ENCODING_VERSION,
        artifact_validation_status=raw.artifact_validation_status,
        payload=raw.payload,
    )
    runtime.artifacts[-1] = artifact
    runtime.publish_unary_artifact(
        artifact,
        domain=UnaryArtifactDomain.RETURN_WIDTH_V1,
        semantic_seed_digest=seed.digest,
        function_snapshot_fingerprint=snapshot_fingerprint,
        function_premise_digest=function_premise_digest,
        normalization_policy_digest=normalization_policy_digest,
        attempt_candidate_independent=True,
        pair_independent=True,
    )
    entry = runtime.unary_artifact_cache.get(
        requirement.to_key(),
        function_premise_digest,
        domain=UnaryArtifactDomain.RETURN_WIDTH_V1,
        function_snapshot_fingerprint=snapshot_fingerprint,
        semantic_seed_digest=seed.digest,
        normalization_policy_digest=normalization_policy_digest,
        producer_version=RETURN_WIDTH_PRODUCER_VERSION,
        encoding_version=RETURN_WIDTH_ENCODING_VERSION,
    )
    validated = ValidatedUnaryWidthArtifact(
        seed=seed,
        proof_artifact=artifact,
        relation=seed.extension_evidence_source.kind,
        validation_basis=("structural_relation", basis),
    )
    return UnaryWidthProofResult(
        "proved", validated_artifact=validated, cache_entry=entry, cache_hit=False
    )
