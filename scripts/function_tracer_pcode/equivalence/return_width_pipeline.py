"""Pre-pairwise construction of canonical return observation surfaces."""

from __future__ import annotations

from dataclasses import dataclass
from typing import Any, Dict, Mapping, Optional, Sequence, Tuple

from .obligations.return_width import (
    UnaryWidthProofResult,
    prove_function_return_width,
    return_width_requirement,
)
from .obligations.snapshot import SnapshotFingerprintCodec
from .return_width_surface import (
    BlockedObservation,
    ConsumerBindingReceipt,
    FunctionReturnWidthSeed,
    PairReturnObservationView,
    PairReturnObservationSeed,
    ProvenObservation,
    WidthBlocker,
    build_input_correspondence_contract,
    prove_object_query_input_correspondence,
    build_pair_return_observation_seed,
    build_observation_view,
    build_top_level_consumer_binding_receipt,
    build_top_level_observation_contract,
    _declared_observation_width,
    extract_function_return_width_seed,
)


@dataclass(frozen=True)
class PreparedFunctionReturnWidths:
    seeds_by_case_id: Mapping[int, FunctionReturnWidthSeed]
    proofs_by_case_id: Mapping[int, UnaryWidthProofResult]
    completion_evidence: Tuple[Mapping[str, Any], ...] = ()


@dataclass(frozen=True)
class PreparedPairReturnObservation:
    status: str
    view: Optional[PairReturnObservationView] = None
    binding_receipt: Optional[ConsumerBindingReceipt] = None
    blockers: Tuple[WidthBlocker, ...] = ()
    required_proof_requirement_ids: Tuple[Mapping[str, Any], ...] = ()
    observation_seed: Optional[PairReturnObservationSeed] = None

    @property
    def proven(self) -> bool:
        return self.status == "proven" and self.view is not None and self.binding_receipt is not None


def prepare_function_return_widths(
    analysis: Any,
    cases: Sequence[Any],
    stats: Optional[Dict[str, int]] = None,
) -> PreparedFunctionReturnWidths:
    seeds: Dict[int, FunctionReturnWidthSeed] = {}
    proofs: Dict[int, UnaryWidthProofResult] = {}
    completion_evidence = []
    seen_targets = set()
    for case in cases:
        seed = extract_function_return_width_seed(analysis, case)
        seeds[id(case)] = seed
        target_key = seed.target_id.stable_key()
        if target_key not in seen_targets:
            seen_targets.add(target_key)
            _inc(stats, "width_target_count")
        if seed.complete:
            _inc(stats, "width_seed_complete_count")
        else:
            _inc(stats, "width_seed_incomplete_count")
        proof = prove_function_return_width(analysis, seed)
        proofs[id(case)] = proof
        _inc(stats, "width_unary_proof_cache_hits" if proof.cache_hit else "width_unary_proof_attempts")
        if proof.complete:
            _inc(stats, "width_unary_proof_successes")
            completion_evidence.append(_width_completion_evidence(proof))
        else:
            _inc(stats, "width_unary_proof_blocked")
    unique_evidence = {
        SnapshotFingerprintCodec.freeze(item["proof_requirement_id"]): item
        for item in completion_evidence
    }
    return PreparedFunctionReturnWidths(
        seeds,
        proofs,
        tuple(unique_evidence[key] for key in sorted(unique_evidence, key=repr)),
    )


def return_coverage_artifact_ids(
    runtime: Any,
    function_identities: Sequence[Tuple[Any, ...]],
) -> Tuple[Tuple[Any, ...], ...]:
    """Return validated final unary coverage artifacts for every function.

    A coverage artifact from only one side must never authorize a pair view.
    """

    by_function = {
        SnapshotFingerprintCodec.freeze(identity): []
        for identity in function_identities
    }
    for artifact in tuple(getattr(runtime, "artifacts", ()) or ()):
        proof_kind = str(getattr(getattr(artifact, "requirement_id", None), "proof_kind", "") or "")
        requirement = getattr(artifact, "requirement_id", None)
        target = tuple(getattr(requirement, "proof_target_key", ()) or ())
        if (
            proof_kind != "unary_outcome_partition_complete"
            or not getattr(artifact, "is_validated", False)
            or len(target) < 2
            or target[0] != "function_outcome_seed"
        ):
            continue
        function_key = SnapshotFingerprintCodec.freeze(target[1])
        if function_key in by_function:
            by_function[function_key].append(tuple(artifact.artifact_id))
    if not by_function or any(not values for values in by_function.values()):
        return ()
    return tuple(sorted({item for values in by_function.values() for item in values}, key=repr))


def prepare_pair_return_observation(
    left_analysis: Any,
    right_analysis: Any,
    left_case: Any,
    right_case: Any,
    left_prepared: PreparedFunctionReturnWidths,
    right_prepared: PreparedFunctionReturnWidths,
    *,
    return_coverage_ids: Sequence[Tuple[Any, ...]],
    proof_runtime: Any = None,
    left_query_parameters: Sequence[Any] = (),
    right_query_parameters: Sequence[Any] = (),
    left_replace_fn: Any = None,
    right_replace_fn: Any = None,
    stats: Optional[Dict[str, int]] = None,
) -> PreparedPairReturnObservation:
    left_seed = left_prepared.seeds_by_case_id[id(left_case)]
    right_seed = right_prepared.seeds_by_case_id[id(right_case)]
    left_proof = left_prepared.proofs_by_case_id[id(left_case)]
    right_proof = right_prepared.proofs_by_case_id[id(right_case)]
    pair_seed = build_pair_return_observation_seed(left_seed, right_seed)
    try:
        from .v2.abi_width_readonly import assess_return_abi_pair
        from .v2.production_signals import emit_abi_width_readonly_signal

        abi_assessment = assess_return_abi_pair(
            left_analysis,
            right_analysis,
            left_seed,
            right_seed,
            pair_seed,
        )
        for signal in abi_assessment.signals:
            emit_abi_width_readonly_signal(
                signal, producer_site_manifest_id="return-width-pair-assessment"
            )
    except Exception as exc:
        from .v2.production_signals import record_production_pilot_shadow_error

        record_production_pilot_shadow_error(exc)
    def blocked_result(blockers, **kwargs):
        _inc(stats, "width_observation_blocked")
        for blocker in tuple(blockers or ()):
            slot = str(getattr(blocker, "missing_slot", "unknown") or "unknown")
            _inc(stats, f"width_observation_blocked_{slot}")
        return PreparedPairReturnObservation(
            "blocked", blockers=tuple(blockers or ()), observation_seed=pair_seed,
            **kwargs,
        )
    if not left_proof.complete or not right_proof.complete:
        blockers = tuple(
            WidthBlocker(
                "unary_width",
                seed.target_id.stable_key(),
                proof.blocker_kind or "validated_unary_width_artifact",
                side,
            )
            for side, seed, proof in (
                ("left", left_seed, left_proof),
                ("right", right_seed, right_proof),
            )
            if not proof.complete
        )
        requirements = tuple(
            proof.validated_artifact.proof_artifact.requirement_id.to_dict()
            if proof.complete
            else return_width_requirement(seed).to_dict()
            for seed, proof in (
                (left_seed, left_proof),
                (right_seed, right_proof),
            )
            if not proof.complete
        )
        return blocked_result(
            blockers,
            required_proof_requirement_ids=requirements,
        )
    contract = build_top_level_observation_contract(left_seed, right_seed)
    if isinstance(contract, BlockedObservation):
        return blocked_result(contract.blockers)
    applicability_digest = _proof_bundle_applicability_digest(
        left_proof,
        right_proof,
        proof_runtime,
        return_coverage_ids,
    )
    if not applicability_digest:
        if left_proof.cache_entry is None or right_proof.cache_entry is None:
            _inc(stats, "width_proof_bundle_missing_unary_cache_entry")
        elif proof_runtime is None:
            _inc(stats, "width_proof_bundle_missing_runtime")
        elif not return_coverage_ids:
            _inc(stats, "width_proof_bundle_missing_return_coverage")
        elif any(
            proof.validated_artifact is None
            or proof.cache_entry.artifact != proof.validated_artifact.proof_artifact
            or not proof.cache_entry.artifact.is_validated
            for proof in (left_proof, right_proof)
        ):
            _inc(stats, "width_proof_bundle_unary_artifact_inapplicable")
        else:
            _inc(stats, "width_proof_bundle_coverage_artifact_inapplicable")
        return blocked_result((WidthBlocker(
                "proof_closure",
                pair_seed.target_id.stable_key(),
                "validated_observation_proof_bundle",
            ),))
    closure_id = (
        "return_width_observation_closure_v1",
        left_proof.validated_artifact.artifact_id,
        right_proof.validated_artifact.artifact_id,
        tuple(return_coverage_ids),
        applicability_digest,
    )
    observation = build_observation_view(
        contract,
        left_proof.validated_artifact,
        right_proof.validated_artifact,
        validated_closure_id=closure_id,
        return_coverage_artifact_ids=return_coverage_ids,
        return_coverage_artifacts_validated=True,
    )
    if not isinstance(observation, ProvenObservation):
        return blocked_result(observation.blockers)
    correspondence = build_input_correspondence_contract(
        tuple(getattr(left_analysis, "parameters", ()) or ()),
        tuple(getattr(right_analysis, "parameters", ()) or ()),
    )
    if isinstance(correspondence, BlockedObservation):
        _inc(stats, "width_binding_blocked")
        return PreparedPairReturnObservation(
            "blocked", view=observation.view, blockers=correspondence.blockers,
            observation_seed=pair_seed,
        )
    nontrivial_binding_proof = prove_object_query_input_correspondence(
        correspondence,
        left_query_parameters,
        right_query_parameters,
    )
    binding = build_top_level_consumer_binding_receipt(
        observation.view,
        correspondence,
        nontrivial_binding_proof_artifacts=(
            (nontrivial_binding_proof,) if nontrivial_binding_proof is not None else ()
        ),
        proof_closure_id=closure_id,
        left_query_parameters=left_query_parameters,
        right_query_parameters=right_query_parameters,
        lowered_left_term=_lower_observation_term(
            left_case,
            left_replace_fn,
            observation.view.canonical_comparison_width,
        ),
        lowered_right_term=_lower_observation_term(
            right_case,
            right_replace_fn,
            observation.view.canonical_comparison_width,
        ),
        proof_bundle_applicability_digest=applicability_digest,
    )
    if isinstance(binding, BlockedObservation):
        _inc(stats, "width_binding_blocked")
        return PreparedPairReturnObservation(
            "blocked", view=observation.view, blockers=binding.blockers,
            observation_seed=pair_seed,
        )
    _inc(stats, "width_observation_proven")
    _inc(stats, "width_binding_receipts")
    return PreparedPairReturnObservation(
        "proven",
        view=observation.view,
        binding_receipt=binding,
        observation_seed=pair_seed,
    )


def observation_audit_digest(prepared: PreparedPairReturnObservation) -> str:
    return SnapshotFingerprintCodec.digest((
        prepared.status,
        prepared.view.digest if prepared.view is not None else None,
        prepared.binding_receipt.binding_digest if prepared.binding_receipt is not None else None,
        tuple((item.blocker_kind, item.target_key, item.missing_slot) for item in prepared.blockers),
        prepared.observation_seed.stable_key() if prepared.observation_seed else None,
    ))


def _inc(stats: Optional[Dict[str, int]], key: str) -> None:
    if stats is not None:
        stats[key] = int(stats.get(key, 0)) + 1


def _proof_bundle_applicability_digest(
    left_proof: UnaryWidthProofResult,
    right_proof: UnaryWidthProofResult,
    runtime: Any,
    coverage_ids: Sequence[Tuple[Any, ...]],
) -> str:
    if (
        left_proof.cache_entry is None
        or right_proof.cache_entry is None
        or runtime is None
        or not coverage_ids
    ):
        return ""
    for proof in (left_proof, right_proof):
        if (
            proof.validated_artifact is None
            or proof.cache_entry.artifact != proof.validated_artifact.proof_artifact
            or not proof.cache_entry.artifact.is_validated
        ):
            return ""
    artifacts = {
        tuple(item.artifact_id): item
        for item in tuple(getattr(runtime, "artifacts", ()) or ())
        if getattr(item, "is_validated", False)
    }
    requested = tuple(tuple(item) for item in coverage_ids)
    if any(item not in artifacts for item in requested):
        return ""
    return SnapshotFingerprintCodec.digest((
        "validated_observation_proof_bundle_v1",
        tuple(
            (
                proof.cache_entry.artifact.artifact_id,
                proof.cache_entry.function_snapshot_fingerprint,
                proof.cache_entry.function_premise_digest,
                proof.cache_entry.semantic_seed_digest,
            )
            for proof in (left_proof, right_proof)
        ),
        tuple(
            (
                item,
                artifacts[item].premise_digest,
                SnapshotFingerprintCodec.digest(artifacts[item].payload),
            )
            for item in requested
        ),
    ))


def _lower_observation_term(case: Any, replace_fn: Any, target_bits: int) -> str:
    if replace_fn is None:
        def replace_fn(node):
            method = getattr(node, "to_smt", None)
            return method() if callable(method) else str(node)
    try:
        return str(case.get_value_smt(
            replace_fn,
            target_bits=int(target_bits),
            use_sign_extension=case.should_sign_extend_value(),
        ))
    except (TypeError, ValueError, AttributeError):
        return ""


def _width_completion_evidence(
    proof: UnaryWidthProofResult,
) -> Mapping[str, Any]:
    artifact = proof.validated_artifact.proof_artifact
    requirement = artifact.requirement_id.to_dict()
    return {
        "proof_requirement_id": requirement,
        "proof_status": "verified",
        "status": "complete",
        "proof_artifact_ref": artifact.artifact_id,
        "proof_source": "validated_unary_return_width_artifact",
        "semantic_seed_digest": proof.validated_artifact.seed.digest,
        "normalization_policy_digest": (
            proof.validated_artifact.seed.normalization_policy_digest
        ),
        "source_snapshot_fingerprint": (
            proof.cache_entry.function_snapshot_fingerprint
            if proof.cache_entry is not None
            else "unavailable"
        ),
        "semantic_seed_or_premise_digest": (
            proof.cache_entry.function_premise_digest
            if proof.cache_entry is not None
            else proof.validated_artifact.seed.digest
        ),
        "evidence_or_artifact_digest": SnapshotFingerprintCodec.digest((
            artifact.artifact_id,
            artifact.payload,
        )),
        "recognizing_stage": "return_width_canonicalization",
        "width_facts": {
            "storage_width": proof.validated_artifact.seed.storage_width,
            "semantic_payload_width": proof.validated_artifact.seed.payload_width,
            "declared_observation_width": _declared_observation_width(
                proof.validated_artifact.seed.calling_convention_fact
            ),
            "extension_kind": (
                proof.validated_artifact.seed.extension_evidence_source.kind
            ),
            "extension_flow_kind": (
                proof.validated_artifact.seed.extension_evidence_source.identity_flow_kind
            ),
        },
    }
