"""Function-scoped reachable-outcome proof orchestration.

This module owns proof identity and closure construction.  Extraction candidates
remain semantic inputs; only successful producers become validated artifacts.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import Any, Callable, Mapping, Optional, Tuple

from ..cause_identity import ProofRequirementContract, ProofRequirementId
from .cache import ValidatedUnaryArtifactEntry
from .model import FunctionProofOutcome, ProofArtifact
from .runtime import ObligationRuntimeSession
from .snapshot import SnapshotFingerprintCodec


OUTCOME_PRODUCER_VERSION = "reachable-outcome-producer-v1"
OUTCOME_ENCODING_VERSION = "reachable-outcome-smt-v1"


@dataclass(frozen=True)
class UnaryProducerResult:
    status: str
    evidence: Mapping[str, Any] = field(default_factory=dict)

    @property
    def proved(self) -> bool:
        return self.status == "proved"


@dataclass(frozen=True)
class UnaryPartitionProofResult:
    status: str
    blocker_kind: Optional[str] = None
    final_artifact: Optional[ProofArtifact] = None
    cache_entry: Optional[ValidatedUnaryArtifactEntry] = None

    @property
    def complete(self) -> bool:
        return self.status == "proved" and self.final_artifact is not None


def outcome_seed_digest(seed: Any) -> str:
    stable = seed.stable_key() if callable(getattr(seed, "stable_key", None)) else seed
    return SnapshotFingerprintCodec.digest(stable)


def requirement_for_stage(seed: Any, stage: str) -> ProofRequirementId:
    seed_digest = outcome_seed_digest(seed)
    return ProofRequirementId.create(
        f"unary_outcome_{stage}",
        (
            "function_outcome_seed",
            tuple(getattr(seed, "function_identity", ()) or ()),
            seed_digest,
            int(getattr(seed, "partition_revision", 0) or 0),
        ),
        ProofRequirementContract(
            proposition=f"reachable outcome {stage}",
            relation_direction="unary",
            observation_surface=(
                tuple(getattr(seed, "input_domain_contract", ()) or ()),
                int(getattr(seed, "extraction_schema_version", 0) or 0),
                OUTCOME_ENCODING_VERSION,
            ),
            active_precondition=("function_input_domain",),
        ),
    )


def prove_unary_partition(
    analysis: Any,
    *,
    domain_contract: Any,
    normalization_policy_digest: str,
    producers: Mapping[str, Callable[[], UnaryProducerResult]],
) -> UnaryPartitionProofResult:
    seed = getattr(analysis, "outcome_seed", None)
    if seed is None:
        return UnaryPartitionProofResult("blocked", "outcome_seed_missing")
    runtime = ObligationRuntimeSession.create_unary(
        analysis,
        domain_contract=domain_contract,
        normalization_policy_digest=normalization_policy_digest,
    )
    seed_digest = outcome_seed_digest(seed)
    function_premise_digest = runtime.premise_digest
    snapshot_fingerprint = str(runtime.current_view.semantic_surface["function_snapshot"])
    final_requirement = requirement_for_stage(seed, "partition_complete")
    cached = runtime.unary_artifact_cache.get(
        final_requirement.to_key(),
        function_premise_digest,
        function_snapshot_fingerprint=snapshot_fingerprint,
        outcome_seed_digest=seed_digest,
        producer_version=OUTCOME_PRODUCER_VERSION,
        encoding_version=OUTCOME_ENCODING_VERSION,
    )
    if cached is not None:
        return UnaryPartitionProofResult("proved", final_artifact=cached.artifact, cache_entry=cached)

    previous = ()
    for stage in (
        "termination_classification",
        "cfg_reachability",
        "path_region_completeness",
        "member_classification",
        "same_kind_consistency",
        "cross_kind_disjointness",
        "residual_totality",
        "partition_complete",
    ):
        producer = producers.get(stage)
        if producer is None:
            return UnaryPartitionProofResult("blocked", f"outcome_{stage}_producer_missing")
        requirement = requirement_for_stage(seed, stage)
        result = producer()
        if not isinstance(result, UnaryProducerResult):
            raise TypeError(f"unary outcome producer {stage} returned an invalid result")
        if not result.proved:
            return UnaryPartitionProofResult(result.status, f"outcome_{stage}_{result.status}")
        runtime.proof_outcomes[requirement.to_key()] = FunctionProofOutcome.EQUIVALENT
        evidence = {
            "proof_requirement_id": requirement.to_dict(),
            "proof_status": "complete",
            "proof_source": f"unary_outcome_{stage}",
            "producer_version": OUTCOME_PRODUCER_VERSION,
            "encoding_version": OUTCOME_ENCODING_VERSION,
            **dict(result.evidence),
        }
        runtime._apply_artifact(requirement, evidence)
        artifact = runtime.artifacts[-1]
        # _apply_artifact uses compatibility defaults; outcome artifacts carry
        # explicit versions because they cross function/pair cache boundaries.
        versioned = ProofArtifact(
            artifact_id=artifact.artifact_id,
            requirement_id=artifact.requirement_id,
            produced_from_view_id=artifact.produced_from_view_id,
            premise_digest=artifact.premise_digest,
            dependency_artifact_ids=artifact.dependency_artifact_ids,
            producer_id=artifact.producer_id,
            producer_version=OUTCOME_PRODUCER_VERSION,
            encoding_version=OUTCOME_ENCODING_VERSION,
            artifact_validation_status=artifact.artifact_validation_status,
            payload=artifact.payload,
        )
        runtime.artifacts[-1] = versioned
        previous = (versioned,)

    final_artifact = previous[0]
    runtime.publish_unary_artifact(
        final_artifact,
        function_snapshot_fingerprint=snapshot_fingerprint,
        outcome_seed_digest=seed_digest,
        function_premise_digest=function_premise_digest,
        attempt_candidate_independent=True,
        pair_independent=True,
    )
    entry = runtime.unary_artifact_cache.get(
        final_requirement.to_key(),
        function_premise_digest,
        function_snapshot_fingerprint=snapshot_fingerprint,
        outcome_seed_digest=seed_digest,
        producer_version=OUTCOME_PRODUCER_VERSION,
        encoding_version=OUTCOME_ENCODING_VERSION,
    )
    return UnaryPartitionProofResult("proved", final_artifact=final_artifact, cache_entry=entry)
