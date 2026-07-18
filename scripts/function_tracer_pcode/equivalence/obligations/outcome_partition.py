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
        stage_premise_digest = runtime.view_records[
            runtime.current_view.view_id
        ].premise_digest
        (
            result,
            pilot_receipts,
            pilot_attempt_identity,
            pilot_attempt_ordinal,
        ) = _run_outcome_producer_with_pilot_signal(
            producer,
            seed,
            stage,
            requirement,
            function_premise_digest=stage_premise_digest,
            snapshot_fingerprint=snapshot_fingerprint,
        )
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
        from ..v2.production_signals import (
            active_production_pilot_session,
            record_production_pilot_shadow_error,
        )
        if active_production_pilot_session() is not None:
            try:
                _emit_outcome_producer_pilot_signal(
                    seed=seed,
                    stage=stage,
                    requirement=requirement,
                    result=result,
                    execution_receipts=pilot_receipts,
                    validated_artifact=versioned,
                    function_snapshot_fingerprint=snapshot_fingerprint,
                    function_premise_digest=stage_premise_digest,
                    producer_attempt_identity=pilot_attempt_identity,
                    producer_attempt_ordinal=pilot_attempt_ordinal,
                )
            except Exception as exc:
                record_production_pilot_shadow_error(exc)
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


def _run_outcome_producer_with_pilot_signal(
    producer: Callable[[], UnaryProducerResult],
    seed: Any,
    stage: str,
    requirement: ProofRequirementId,
    *,
    function_premise_digest: str,
    snapshot_fingerprint: str,
) -> Tuple[UnaryProducerResult, Tuple[Any, ...], Optional[str], Optional[int]]:
    """Run the real producer and mirror its explicit result to an opt-in v2 session."""

    from ..v2.production_signals import (
        active_production_pilot_session,
        record_production_pilot_shadow_error,
    )
    pilot_session = active_production_pilot_session()
    if pilot_session is None:
        return producer(), (), None, None
    from ..v2.return_outcome import outcome_stage_capture_scope
    invocation_state = pilot_session.domain_signal_state.setdefault(
        "return_outcome_invocation_authority",
        {"invocation_ordinal": 0, "producer_attempt_ordinal": 0},
    )
    invocation_state["producer_attempt_ordinal"] += 1
    producer_attempt_ordinal = invocation_state["producer_attempt_ordinal"]
    producer_attempt_identity = SnapshotFingerprintCodec.digest((
        "return_outcome_producer_attempt",
        pilot_session.identity.execution_identity_digest,
        requirement.to_key(),
        producer_attempt_ordinal,
    ))

    def next_invocation_ordinal() -> int:
        invocation_state["invocation_ordinal"] += 1
        return invocation_state["invocation_ordinal"]

    with outcome_stage_capture_scope(
        seed=seed,
        stage=stage,
        premise_digest=function_premise_digest,
        function_snapshot_fingerprint=snapshot_fingerprint,
        execution_identity_digest=(
            pilot_session.identity.execution_identity_digest
        ),
        producer_attempt_identity=producer_attempt_identity,
        producer_attempt_ordinal=producer_attempt_ordinal,
        next_invocation_ordinal=next_invocation_ordinal,
    ) as capture:
        result = producer()
    if isinstance(result, UnaryProducerResult) and not result.proved:
        try:
            _emit_outcome_producer_pilot_signal(
                seed=seed,
                stage=stage,
                requirement=requirement,
                result=result,
                execution_receipts=tuple(capture.receipts),
                validated_artifact=None,
                function_snapshot_fingerprint=snapshot_fingerprint,
                function_premise_digest=function_premise_digest,
                producer_attempt_identity=producer_attempt_identity,
                producer_attempt_ordinal=producer_attempt_ordinal,
            )
        except Exception as exc:
            record_production_pilot_shadow_error(exc)
    return (
        result,
        tuple(capture.receipts),
        producer_attempt_identity,
        producer_attempt_ordinal,
    )


def _emit_outcome_producer_pilot_signal(
    *,
    seed: Any,
    stage: str,
    requirement: ProofRequirementId,
    result: UnaryProducerResult,
    execution_receipts: Tuple[Any, ...],
    validated_artifact: Optional[ProofArtifact],
    function_snapshot_fingerprint: str,
    function_premise_digest: str,
    producer_attempt_identity: Optional[str],
    producer_attempt_ordinal: Optional[int],
) -> None:
    from ..v2.contracts import authority_digest
    from ..v2.production_signals import (
        OutcomePartitionProductionSignal,
        active_production_pilot_session,
        emit_outcome_partition_signal,
    )
    from ..v2.return_outcome import (
        WITNESSED_REASON_PROPOSITIONS,
        UnaryOutcomeWitnessArtifact,
        reason_for_stage_status,
    )

    try:
        reason_id = reason_for_stage_status(stage, result.status)
    except ValueError:
        # The bridge must remain a no-op for legacy/custom producers when the
        # pilot is disabled.  The exact v2 encoder rejects an unsealed pair in
        # an active pilot session and records that fail-closed signal error.
        reason_id = None
    witness_artifact = None
    if reason_id in WITNESSED_REASON_PROPOSITIONS:
        sat_receipts = tuple(
            receipt for receipt in execution_receipts
            if getattr(receipt, "observed_status", None) == "sat"
        )
        if len(sat_receipts) != 1:
            raise ValueError("witnessed outcome result requires exactly one SAT receipt")
        witness_artifact = UnaryOutcomeWitnessArtifact.create(
            sat_receipts[0],
            reason_id=reason_id,
            witnessed_proposition=WITNESSED_REASON_PROPOSITIONS[reason_id],
            producer_version=OUTCOME_PRODUCER_VERSION,
            encoding_version=OUTCOME_ENCODING_VERSION,
        )

    artifact_authority = None
    if validated_artifact is not None:
        if not validated_artifact.is_validated:
            raise ValueError("outcome completion artifact is not validated")
        artifact_payload = {
            "artifact_id": validated_artifact.artifact_id,
            "requirement_id": validated_artifact.requirement_id.to_dict(),
            "produced_from_view_id": validated_artifact.produced_from_view_id,
            "premise_digest": validated_artifact.premise_digest,
            "dependency_artifact_ids": validated_artifact.dependency_artifact_ids,
            "producer_id": validated_artifact.producer_id,
            "producer_version": validated_artifact.producer_version,
            "encoding_version": validated_artifact.encoding_version,
            "artifact_validation_status": validated_artifact.artifact_validation_status,
            "function_snapshot_fingerprint": function_snapshot_fingerprint,
            "outcome_seed_digest": outcome_seed_digest(seed),
            "outcome_seed_revision": int(
                getattr(seed, "partition_revision", 0) or 0
            ),
            "stage": stage,
        }
        artifact_authority = {
            **artifact_payload,
            "artifact_authority_digest": authority_digest(artifact_payload),
        }
    emit_outcome_partition_signal(OutcomePartitionProductionSignal(
        stage=stage,
        producer_status=result.status,
        proof_requirement_identity=requirement.to_dict(),
        function_identity=tuple(getattr(seed, "function_identity", ()) or ()),
        outcome_seed_digest=outcome_seed_digest(seed),
        producer_evidence=dict(result.evidence),
        outcome_seed_revision=int(getattr(seed, "partition_revision", 0) or 0),
        function_snapshot_fingerprint=function_snapshot_fingerprint,
        premise_digest=function_premise_digest,
        producer_attempt_identity=producer_attempt_identity,
        producer_attempt_ordinal=producer_attempt_ordinal,
        execution_identity_digest=(
            active_production_pilot_session().identity.execution_identity_digest
        ),
        execution_receipts=execution_receipts,
        witness_artifact=witness_artifact,
        validated_artifact_authority=artifact_authority,
    ), producer_site_manifest_id="outcome-partition-stage-result")
