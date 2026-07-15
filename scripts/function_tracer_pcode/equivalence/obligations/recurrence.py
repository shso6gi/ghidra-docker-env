"""Proposal-specific recurrence proof identities."""

from __future__ import annotations

from typing import Any, Mapping, Tuple

from ...model.recurrence_contracts import (
    RECURRENCE_UNARY_DOMAIN,
    RecurrenceValidationEvidence,
    semantic_recurrence_closure_digest,
)
from .model import ProofArtifact
from ..cause_identity import ProofRequirementContract, ProofRequirementId


def recurrence_proof_requirement(
    seed_core_digest: str,
    proposal_digest: str,
    function_recurrence_binding_digest: str,
    proof_stage: str,
    proof_target_semantic_key: Tuple[Any, ...],
) -> ProofRequirementId:
    values = (
        seed_core_digest, proposal_digest, function_recurrence_binding_digest,
        proof_stage,
    )
    if not all(isinstance(value, str) and value for value in values):
        raise ValueError("recurrence proof identity is incomplete")
    if not isinstance(proof_target_semantic_key, tuple) or not proof_target_semantic_key:
        raise ValueError("recurrence proof target is required")
    target = (
        "recurrence_proof_target_v1",
        ("domain", RECURRENCE_UNARY_DOMAIN),
        ("seed_core_digest", seed_core_digest),
        ("proposal_digest", proposal_digest),
        ("function_recurrence_binding_digest", function_recurrence_binding_digest),
        ("proof_stage", proof_stage),
        ("proof_target", proof_target_semantic_key),
    )
    return ProofRequirementId.create(
        "loop_recurrence_proof",
        target,
        ProofRequirementContract(
            proposition="validated recurrence proposal preserves function semantics",
            observation_surface=("return", "termination", "effects"),
            active_precondition=("proposal_bound",),
        ),
    )


def validate_recurrence_requirement_target(
    requirement: ProofRequirementId,
    *,
    seed_core_digest: str,
    proposal_digest: str,
    function_recurrence_binding_digest: str,
    proof_stage: str,
    proof_target_semantic_key: Tuple[Any, ...],
) -> None:
    expected = recurrence_proof_requirement(
        seed_core_digest, proposal_digest, function_recurrence_binding_digest,
        proof_stage, proof_target_semantic_key,
    )
    if requirement.to_key() != expected.to_key():
        raise ValueError("recurrence proof requirement does not match runtime proposal binding")


def validate_recurrence_artifact_content(
    artifact: ProofArtifact,
    *,
    seed_core_digest: str,
    proposal_digest: str,
    function_recurrence_binding_digest: str,
) -> RecurrenceValidationEvidence:
    """Recompute the complete typed proof closure carried by an artifact."""

    payload = artifact.payload
    if not isinstance(payload, Mapping):
        raise ValueError("recurrence artifact payload is required")
    raw_evidence = payload.get("recurrence_validation_evidence")
    if not isinstance(raw_evidence, Mapping):
        raise ValueError("recurrence validation evidence payload is required")
    evidence = RecurrenceValidationEvidence.from_dict(raw_evidence)
    if (
        evidence.seed_core_digest != seed_core_digest
        or evidence.proposal_digest != proposal_digest
        or evidence.function_recurrence_binding_digest
        != function_recurrence_binding_digest
    ):
        raise ValueError("recurrence proof evidence binding mismatch")
    for key, expected in (
        ("seed_core_digest", seed_core_digest),
        ("proposal_digest", proposal_digest),
        ("function_recurrence_binding_digest", function_recurrence_binding_digest),
    ):
        if key in payload and payload.get(key) != expected:
            raise ValueError("recurrence artifact outer binding mismatch")
    proof_content = payload.get("proof_content")
    if proof_content is not None:
        if not isinstance(proof_content, Mapping):
            raise ValueError("recurrence proof content must be typed")
        if (
            proof_content.get("proof_result_digest")
            != evidence.proof_result_digest
            or tuple(proof_content.get("dependency_subproof_digests") or ())
            != evidence.dependency_subproof_digests
        ):
            raise ValueError("recurrence proof content digest mismatch")
    closure = semantic_recurrence_closure_digest(
        function_recurrence_binding_digest,
        (artifact.requirement_id.to_key(),),
        evidence.proof_result_digest,
        evidence.dependency_subproof_digests,
    )
    if payload.get("semantic_closure_digest") != closure:
        raise ValueError("recurrence semantic closure digest mismatch")
    if tuple(artifact.artifact_id) != ("validated_recurrence_artifact_v2", closure):
        raise ValueError("recurrence artifact identity is not content-bound")
    return evidence
