# -*- coding: utf-8 -*-
"""Tests for the decision-neutral relational call/effect shadow model."""

from __future__ import annotations

from copy import deepcopy
import json
from pathlib import Path
from types import SimpleNamespace

import pytest

from scripts.function_tracer_pcode.analysis.effects.summary import (
    CallArgumentEvidence,
    CallSiteEffectSummaryEvidence,
    EffectSummary,
    FunctionControlEffectProfile,
    StoreEffect,
    StoreEffectProvenance,
    UnsupportedCallEffectRef,
)
from scripts.function_tracer_pcode.analysis.returns.analyzer import ReturnAnalyzer
from scripts.function_tracer_pcode.proof.call_effect.obligations import (
    ArtifactObjectIdentity,
    EquivalenceObservationContract,
    InternalSolverProofArtifact,
    Phase2DirectCallEligibility,
    RegionBoundaryCertificate,
    RegionFact,
    RelationalCallEffectObligation,
    SolverProofRecord,
    apply_solver_proof_artifacts_to_manifest,
    build_call_effect_shadow_manifest,
    build_structural_coverage_certificate,
    evaluate_obligation_proof_readiness,
    condition_key,
)
from scripts.function_tracer_pcode.checker.checker import EquivalenceChecker
from scripts.function_tracer_pcode.proof.call_effect.preflight import (
    CallProofDecisionMode,
    StrategySourceAnalysisPair,
    prepare_solver_surface,
    validate_call_resolution_projection,
)
from scripts.function_tracer_pcode.proof.call_effect.producer import (
    _RenderedStage,
    _execute_rendered_stage,
    V2CallEffectExecutionContext,
    produce_pure_direct_call_proofs,
    produce_v2_pure_direct_call_proofs,
)
from scripts.function_tracer_pcode.authority.domains.call_effect import (
    CALL_EFFECT_ARTIFACT_CAPABILITY_REGISTRY,
    CALL_EFFECT_PRODUCTION_STAGE_REGISTRY,
    CALL_EFFECT_REASON_REGISTRY,
    CALL_EFFECT_RECOVERY_REGISTRY,
    CallEffectPilotEncoder,
)
from scripts.function_tracer_pcode.authority.contracts import (
    BlockerEligibilityBaseRow,
    CActiveBaseRow,
    IdentityScope,
    QOpenBaseRow,
    VerifiedLifecycleProjection,
    CensusMode,
    authority_digest,
)
from scripts.function_tracer_pcode.authority.census_contract import (
    CensusManifest,
    join_outcome_relations,
)
from scripts.function_tracer_pcode.authority.decision.decision import FinalizationAuthority
from scripts.function_tracer_pcode.authority.lifecycle.execution_authority import (
    ExecutionAuthorityDeploymentPolicy,
    ProducerStageContract,
    ProducerStageRegistry,
    PINNED_SOLVER_EXECUTION_ISSUER,
    SolverExecutionEvidenceBundle,
    SolverResultEntryOccurrenceReceipt,
    activate_execution_authority_deployment,
    install_execution_authority_signing_key,
    issue_call_effect_requirement_assignment,
)
from scripts.function_tracer_pcode.authority.lifecycle.production_signals import (
    CallEffectBlockerProductionSignal,
    CallEffectPrerequisiteProductionSignal,
    CallEffectProofBatchProductionSignal,
    CompositeProductionSignalEncoder,
    production_signal_scope,
)
from scripts.function_tracer_pcode.authority.lifecycle.pilot import (
    ProductionDualWritePilotConnector,
)
from scripts.function_tracer_pcode.authority.lifecycle.reducer import ShadowLifecycleReducer
from scripts.function_tracer_pcode.proof.call_effect.obligations import (
    _cross_binary_expression_shape,
)
from scripts.function_tracer_pcode.core import (
    CanonicalLocation,
    CallTargetRef,
    ComparisonSurface,
    Condition,
    DeferredCallInfo,
    DeferredCallRef,
    Expression,
    FunctionReturnAnalysis,
    LocationBaseRef,
    PcodeBlockRef,
    PcodeOpRef,
    ReturnInfo,
    expression_provenance_key,
)
from scripts.function_tracer_pcode.smt import ParallelResult, SolverResult, SolverStatus


def _pcode_ref(
    binary_id: str,
    function_entry: int,
    address: int,
    mnemonic: str = "CALL",
    *,
    block_index: int = 0,
    seq_time: int = 0,
    seq_order: int = 0,
) -> PcodeOpRef:
    return PcodeOpRef(
        address_offset=address,
        seq_time=seq_time,
        seq_order=seq_order,
        block_index=block_index,
        mnemonic=mnemonic,
        input_sizes=(8, 4),
        output_size=4,
        binary_id=binary_id,
        function_entry_space="ram",
        function_entry_offset=function_entry,
        target_space="ram",
        target_offset=address,
        opcode=1,
        local_op_ordinal=0,
    )


def _block_ref_for_pcode(ref: PcodeOpRef) -> PcodeBlockRef:
    return PcodeBlockRef(
        block_index=ref.block_index,
        start_address_offset=int(ref.function_entry_offset or 0)
        + int(ref.block_index or 0) * 0x100,
        binary_id=ref.binary_id,
        function_entry_space=ref.function_entry_space,
        function_entry_offset=ref.function_entry_offset,
    )


def _local_store_provenance(ref: PcodeOpRef) -> StoreEffectProvenance:
    return StoreEffectProvenance(
        source_kind="local_store",
        producer_pcode_op_ref=ref,
        producer_block_ref=_block_ref_for_pcode(ref),
    )


def _call_derived_store_provenance(
    call_ref: PcodeOpRef,
    target_ref: CallTargetRef,
    effect_index: int,
    *,
    nested_block_index: int = 0,
    nested_seq_time: int | None = None,
) -> StoreEffectProvenance:
    nested_ref = _pcode_ref(
        str(call_ref.binary_id),
        int(target_ref.entry_offset or 0),
        int(target_ref.entry_offset or 0) + 4 * (effect_index + 1),
        mnemonic="STORE",
        block_index=nested_block_index,
        seq_time=effect_index if nested_seq_time is None else nested_seq_time,
    )
    return StoreEffectProvenance(
        source_kind="call_derived",
        producer_pcode_op_ref=call_ref,
        producer_block_ref=_block_ref_for_pcode(call_ref),
        call_target_ref=target_ref,
        callee_effect_index=effect_index,
        nested_effect_provenance=_local_store_provenance(nested_ref),
    )


def _analysis_with_call(
    binary_id: str,
    caller_entry: int,
    call_address: int,
    callee_entry: int,
) -> FunctionReturnAnalysis:
    pcode_ref = _pcode_ref(binary_id, caller_entry, call_address)
    target = CallTargetRef.from_name(
        "callee",
        program_id=1 if binary_id == "left" else 2,
        entry_offset=callee_entry,
    )
    argument = Expression.parameter("x", 0, size=4)
    evidence = CallArgumentEvidence(
        pcode_op_ref=pcode_ref,
        target_ref=target,
        callee_param_identities=(("parameter_storage", "register", 0, 4),),
        arguments=(argument,),
        sources=("pcode_input",),
        coverage_complete=True,
        recovery_status=CallArgumentEvidence.RECOVERY_COMPLETE,
    )
    control_profile = FunctionControlEffectProfile(
        block_count=1,
        pcode_op_count=2,
        return_block_count=1,
        pcode_enumeration_complete=True,
        cfg_edges_complete=True,
        cfg_acyclic=True,
        terminal_return_coverage_complete=True,
        call_like_identity_complete=True,
    )
    caller_profile = FunctionControlEffectProfile(
        block_count=1,
        pcode_op_count=2,
        return_block_count=1,
        pcode_enumeration_complete=True,
        cfg_edges_complete=True,
        cfg_acyclic=True,
        terminal_return_coverage_complete=True,
        call_count=1,
        call_like_pcode_op_keys=(pcode_ref.stable_key(),),
        call_like_identity_complete=True,
    )
    return FunctionReturnAnalysis(
        function_name="caller",
        entry_point=hex(caller_entry),
        function_ref=CallTargetRef.from_name(
            "caller",
            program_id=1 if binary_id == "left" else 2,
            entry_offset=caller_entry,
        ),
        binary_id=binary_id,
        parameters=[{"name": "x", "index": 0, "size": 4}],
        returns=[],
        effect_summary=EffectSummary(
            parameter_names=["x"],
            effects=[],
            call_argument_evidence={pcode_ref.stable_key(): evidence},
            call_site_effect_summary_evidence=(
                CallSiteEffectSummaryEvidence(
                    pcode_op_ref=pcode_ref,
                    target_ref=target,
                    argument_keys=(expression_provenance_key(argument),),
                    path_condition_keys=(),
                    summary_status="complete",
                    memory_effect_count=0,
                    has_unsupported_nested_call=False,
                    callee_control_profile_key=control_profile.stable_key(),
                    callee_ordered_scalar_store_candidate=True,
                    return_summary_status="complete",
                    return_semantic_bit_width=32,
                    return_signed=True,
                    return_value_keys=(expression_provenance_key(argument),),
                    return_partitions=(((), argument),),
                ),
            ),
            function_control_effect_profile=caller_profile,
        ),
    )


def test_observation_contract_digest_covers_observation_policy():
    default = EquivalenceObservationContract()
    no_termination = EquivalenceObservationContract(observe_termination=False)

    assert default.contract_id != no_termination.contract_id
    assert default.to_dict()["contract_id"] == default.contract_id


def test_solver_proof_record_rejects_naked_completion_claims():
    with pytest.raises(ValueError, match="requires solver_result='unsat'"):
        SolverProofRecord(
            proof_id="proof",
            obligation_id="obligation",
            proof_stage="return_relation",
            observation_contract_id="contract",
            left_object_id="left",
            right_object_id="right",
            status="proven",
        )

    record = SolverProofRecord(
        proof_id="proof",
        obligation_id="obligation",
        proof_stage="return_relation",
        observation_contract_id="contract",
        left_object_id="left",
        right_object_id="right",
        status="proven",
        solver_result="unsat",
        query_digest="a" * 64,
        normalized_assertion_digest="b" * 64,
        stage_input_digest="c" * 64,
        precondition_digest="d" * 64,
        solver_name="z3",
        solver_version="test",
        timeout_ms=1000,
        producer_kind="internal_parallel_solver_runner",
    )
    assert record.to_dict()["solver_result"] == "unsat"


def test_shadow_manifest_pairs_only_mutually_unique_object_shapes():
    left = _analysis_with_call("left", 0x1000, 0x1010, 0x2000)
    right = _analysis_with_call("right", 0x3000, 0x3010, 0x4000)

    manifest = build_call_effect_shadow_manifest(
        left,
        right,
        binary1_name="left",
        binary2_name="right",
    )

    assert manifest["mode"] == "shadow_no_decision_effect"
    assert manifest["summary"]["left_fact_count"] == 1
    assert manifest["summary"]["right_fact_count"] == 1
    assert manifest["summary"]["paired_obligation_count"] == 1
    assert manifest["summary"]["structural_coverage_complete"] is True
    assert manifest["summary"]["semantic_proof_status"] == "pending"
    obligation = manifest["relational_obligations"][0]
    assert obligation["relation_kind"] == "call_to_call"
    assert obligation["status"] == "pending"
    assert obligation["correspondence_basis"] == "mutually_unique_object_shape_candidate"
    assert manifest["summary"]["phase2_candidate_count"] == 1
    eligibility = manifest["phase2_direct_call_eligibility"][0]
    assert eligibility["status"] == "candidate"
    assert eligibility["candidate_only"] is True
    assert "decision_eligible" not in eligibility
    assert eligibility["required_solver_stages"] == [
        "guard_relation",
        "argument_relation",
        "return_relation",
    ]
    assert eligibility["structural_precondition_stages"] == {
        "target_callee_relation": "complete",
        "abi_relation": "complete",
        "callee_totality_precondition": "complete",
        "termination_relation": "complete",
        "trap_relation": "complete",
        "empty_state_transformer_and_frame": "complete",
    }
    assert manifest["solver_proof_records"] == []
    assert manifest["legacy_replacement_readiness"]["status"] == "blocked"
    assert "semantic_obligation_proofs_incomplete" in manifest[
        "legacy_replacement_readiness"
    ]["failure_causes"]


def test_resolved_internal_call_and_callind_share_candidate_class():
    left = _analysis_with_call("left", 0x1000, 0x1010, 0x2000)
    right = _analysis_with_call("right", 0x3000, 0x3010, 0x4000)
    right_evidence = next(iter(right.effect_summary.call_argument_evidence.values()))
    callind_ref = _pcode_ref("right", 0x3000, 0x3010, "CALLIND")
    object.__setattr__(right_evidence, "pcode_op_ref", callind_ref)
    right.effect_summary.call_argument_evidence = {
        callind_ref.stable_key(): right_evidence
    }
    right_effect = right.effect_summary.call_site_effect_summary_evidence[0]
    object.__setattr__(right_effect, "pcode_op_ref", callind_ref)
    right_profile = right.effect_summary.function_control_effect_profile
    object.__setattr__(right_profile, "call_count", 0)
    object.__setattr__(right_profile, "callind_count", 1)
    object.__setattr__(right_profile, "call_like_pcode_op_keys", (callind_ref.stable_key(),))

    manifest = build_call_effect_shadow_manifest(
        left,
        right,
        binary1_name="left",
        binary2_name="right",
    )

    assert manifest["summary"]["paired_obligation_count"] == 1
    assert manifest["left_facts"][0]["correspondence_operation_class"] == (
        "resolved_internal_call_candidate"
    )
    assert manifest["right_facts"][0]["correspondence_operation_class"] == (
        "resolved_internal_call_candidate"
    )


def test_ambiguous_correspondence_does_not_reuse_peer_fact():
    left1 = _analysis_with_call("left", 0x1000, 0x1010, 0x2000)
    left2 = _analysis_with_call("left", 0x1000, 0x1020, 0x2000)
    left1.effect_summary.call_argument_evidence.update(
        left2.effect_summary.call_argument_evidence
    )
    left1.effect_summary.call_site_effect_summary_evidence += (
        left2.effect_summary.call_site_effect_summary_evidence
    )
    right = _analysis_with_call("right", 0x3000, 0x3010, 0x4000)

    manifest = build_call_effect_shadow_manifest(
        left1,
        right,
        binary1_name="left",
        binary2_name="right",
    )

    assert manifest["summary"]["paired_obligation_count"] == 0
    assert manifest["summary"]["unmatched_left_count"] == 2
    assert manifest["summary"]["unmatched_right_count"] == 1
    assert manifest["coupling"]["duplicate_left_fact_ids"] == []
    assert manifest["coupling"]["duplicate_right_fact_ids"] == []


def test_unmatched_call_obligations_cover_both_sides_without_regions():
    left = _analysis_with_call("left", 0x1000, 0x1010, 0x2000)
    right = _analysis_with_call("right", 0x3000, 0x3010, 0x4000)
    right_argument = Expression.constant(7, 4)
    right_evidence = next(iter(right.effect_summary.call_argument_evidence.values()))
    object.__setattr__(right_evidence, "arguments", (right_argument,))
    object.__setattr__(
        right.effect_summary.call_site_effect_summary_evidence[0],
        "argument_keys",
        (expression_provenance_key(right_argument),),
    )

    manifest = build_call_effect_shadow_manifest(
        left,
        right,
        binary1_name="left",
        binary2_name="right",
    )

    assert {
        item["relation_kind"] for item in manifest["relational_obligations"]
    } == {"unmatched_left", "unmatched_right"}
    assert manifest["summary"]["structural_coverage_complete"] is True


def test_structural_coverage_requires_exact_pcode_call_census_identity():
    left = _analysis_with_call("left", 0x1000, 0x1010, 0x2000)
    right = _analysis_with_call("right", 0x3000, 0x3010, 0x4000)
    missing_ref = _pcode_ref("left", 0x1000, 0x1020)
    profile = left.effect_summary.function_control_effect_profile
    object.__setattr__(profile, "call_count", 2)
    object.__setattr__(
        profile,
        "call_like_pcode_op_keys",
        profile.call_like_pcode_op_keys + (missing_ref.stable_key(),),
    )

    manifest = build_call_effect_shadow_manifest(
        left,
        right,
        binary1_name="left",
        binary2_name="right",
    )

    coverage = manifest["pcode_call_census_coverage"]["left"]
    assert coverage["status"] == "incomplete"
    assert len(coverage["missing_fact_pcode_op_keys"]) == 1
    assert manifest["summary"]["structural_coverage_complete"] is False


def test_nested_callee_evidence_is_not_counted_as_a_caller_callsite():
    left = _analysis_with_call("left", 0x1000, 0x1010, 0x2000)
    nested = _analysis_with_call("left", 0x2000, 0x2010, 0x2000)
    left.effect_summary.call_argument_evidence.update(
        nested.effect_summary.call_argument_evidence
    )
    left.effect_summary.call_site_effect_summary_evidence += (
        nested.effect_summary.call_site_effect_summary_evidence
    )
    right = _analysis_with_call("right", 0x3000, 0x3010, 0x4000)

    manifest = build_call_effect_shadow_manifest(
        left,
        right,
        binary1_name="left",
        binary2_name="right",
    )

    assert manifest["summary"]["left_fact_count"] == 1
    assert manifest["pcode_call_census_coverage"]["left"]["status"] == "complete"


def test_unmatched_recursive_callee_reports_scc_proof_stage():
    left = _analysis_with_call("left", 0x1000, 0x1010, 0x2000)
    right = _analysis_with_call("right", 0x3000, 0x3010, 0x4000)
    recursive_profile = FunctionControlEffectProfile(
        block_count=2,
        pcode_op_count=4,
        return_block_count=1,
        pcode_enumeration_complete=True,
        cfg_edges_complete=True,
        cfg_acyclic=False,
        terminal_return_coverage_complete=True,
        call_count=1,
        call_like_identity_complete=True,
    )
    left_effect = left.effect_summary.call_site_effect_summary_evidence[0]
    object.__setattr__(left_effect, "summary_status", "incomplete")
    object.__setattr__(left_effect, "callee_control_profile_key", recursive_profile.stable_key())
    object.__setattr__(left_effect, "callee_recursive_scc_proven", True)
    object.__setattr__(left_effect, "callee_recursive_scc_identity", "scc-proof")
    object.__setattr__(
        left_effect,
        "callee_recursive_scc_member_keys",
        (("function", 1, 0x2000),),
    )
    right_effect = right.effect_summary.call_site_effect_summary_evidence[0]
    object.__setattr__(
        right_effect,
        "return_value_keys",
        (expression_provenance_key(Expression.constant(7, 4)),),
    )

    manifest = build_call_effect_shadow_manifest(
        left,
        right,
        binary1_name="left",
        binary2_name="right",
    )

    assert any(
        item["primary_proof_stage"] == "recursive_call_scc_unproven"
        for item in manifest["proof_stage_backlog"]
    )


def test_nonrecursive_nested_call_reports_dependency_closure_missing():
    left = _analysis_with_call("left", 0x1000, 0x1010, 0x2000)
    right = _analysis_with_call("right", 0x3000, 0x3010, 0x4000)
    nested_profile = FunctionControlEffectProfile(
        block_count=2,
        pcode_op_count=4,
        return_block_count=1,
        pcode_enumeration_complete=True,
        cfg_edges_complete=True,
        cfg_acyclic=True,
        terminal_return_coverage_complete=True,
        call_count=1,
        call_like_identity_complete=True,
        recursive_scc_proven=False,
    )
    left_effect = left.effect_summary.call_site_effect_summary_evidence[0]
    object.__setattr__(left_effect, "summary_status", "incomplete")
    object.__setattr__(left_effect, "callee_control_profile_key", nested_profile.stable_key())
    right_effect = right.effect_summary.call_site_effect_summary_evidence[0]
    object.__setattr__(
        right_effect,
        "return_value_keys",
        (expression_provenance_key(Expression.constant(9, 4)),),
    )

    manifest = build_call_effect_shadow_manifest(
        left,
        right,
        binary1_name="left",
        binary2_name="right",
    )

    left_backlog = next(
        item
        for item in manifest["proof_stage_backlog"]
        if "left_callee_dependency_closure_missing" in item["blocking_stages"]
    )
    assert left_backlog["primary_proof_stage"] == "callee_dependency_closure_missing"


def test_recursive_scc_certificate_requires_a_complete_call_graph_cycle():
    analyzer = ReturnAnalyzer(program=None)
    first = ("function", 1, 0x1000)
    second = ("function", 1, 0x2000)
    leaf = ("function", 1, 0x3000)
    analyzer._direct_call_graph = {
        first: {second},
        second: {first},
        leaf: set(),
    }
    analyzer._direct_call_graph_complete_nodes = {first, second, leaf}

    proven, identity, members = analyzer._recursive_scc_certificate(first)
    assert proven is True
    assert identity
    assert set(members) == {first, second}

    leaf_proven, _, _ = analyzer._recursive_scc_certificate(leaf)
    assert leaf_proven is False

    analyzer._direct_call_graph_complete_nodes.remove(second)
    incomplete, _, _ = analyzer._recursive_scc_certificate(first)
    assert incomplete is False


def test_callother_is_a_typed_userop_fact_not_a_callsite():
    analysis = FunctionReturnAnalysis(
        function_name="intrinsic_user",
        entry_point="0x1000",
        function_ref=CallTargetRef.from_name("intrinsic_user", program_id=1, entry_offset=0x1000),
        binary_id="left",
        parameters=[],
        returns=[],
        effect_summary=EffectSummary(
            parameter_names=[],
            effects=[],
            has_unsupported_call=True,
            unsupported_call_sites=(
                UnsupportedCallEffectRef(
                    pcode_op_ref=_pcode_ref("left", 0x1000, 0x1010, "CALLOTHER"),
                    target_ref=None,
                    reason="unsupported_intrinsic",
                    order_key=1,
                    target_expr=Expression.constant(17, 4),
                    arguments=(Expression.constant(1, 4),),
                ),
            ),
        ),
    )
    empty = FunctionReturnAnalysis(
        function_name="empty",
        entry_point="0x3000",
        binary_id="right",
        parameters=[],
        returns=[],
    )

    manifest = build_call_effect_shadow_manifest(
        analysis,
        empty,
        binary1_name="left",
        binary2_name="right",
    )

    assert manifest["left_facts"][0]["fact_kind"] == "userop"
    assert manifest["left_facts"][0]["unsupported_reason"] == "unsupported_intrinsic"
    assert manifest["relational_obligations"][0]["relation_kind"] == "unmatched_left"


def test_region_fact_exposes_boundary_completeness_instead_of_assuming_it():
    boundary = RegionBoundaryCertificate(
        entry_block_key=("block", 1),
        exit_block_keys=(("block", 2),),
        block_keys=(("block", 1), ("block", 2)),
        pcode_op_keys=(("pcode", 1),),
        single_entry=True,
        all_exits_enumerated=True,
        cross_edges_enumerated=False,
        guard_partition_complete=True,
    )
    region = RegionFact(
        fact_id="region",
        function_identity=ArtifactObjectIdentity(
            binary_id="left",
            function_key=("function", 1, 0x1000),
        ),
        boundary=boundary,
    )

    assert region.to_dict()["boundary"]["is_complete"] is False


def _analysis_with_inline_region(binary_id: str, entry: int) -> FunctionReturnAnalysis:
    value = Expression.parameter("x", 0, size=4)
    profile = FunctionControlEffectProfile(
        block_count=1,
        pcode_op_count=2,
        return_block_count=1,
        pcode_enumeration_complete=True,
        cfg_edges_complete=True,
        cfg_acyclic=True,
        terminal_return_coverage_complete=True,
        call_like_identity_complete=True,
        region_entry_block_key=("pcode_block", binary_id, entry, 0),
        region_exit_block_keys=(("pcode_block", binary_id, entry, 0),),
        region_block_keys=(("pcode_block", binary_id, entry, 0),),
        region_pcode_op_keys=(("pcode_op", binary_id, entry, 0),),
        region_live_in_keys=(("register", 0, 4),),
        region_live_out_keys=(("register", 0, 4),),
        region_identity_complete=True,
        region_single_entry=True,
        region_all_exits_enumerated=True,
        region_cross_edges_enumerated=True,
    )
    return FunctionReturnAnalysis(
        function_name="inlined",
        entry_point=hex(entry),
        function_ref=CallTargetRef.from_name(
            "inlined", program_id=2, entry_offset=entry
        ),
        binary_id=binary_id,
        parameters=[{"name": "x", "index": 0, "size": 4}],
        returns=[ReturnInfo(address=hex(entry + 4), conditions=[], value=value)],
        return_type="int",
        effect_summary=EffectSummary(
            parameter_names=["x"],
            effects=[],
            function_control_effect_profile=profile,
        ),
    )


def test_unique_unmatched_call_builds_call_to_inline_region_obligation():
    left = _analysis_with_call("left", 0x1000, 0x1010, 0x2000)
    right = _analysis_with_inline_region("right", 0x3000)

    manifest = build_call_effect_shadow_manifest(
        left,
        right,
        binary1_name="left",
        binary2_name="right",
    )

    assert manifest["summary"]["call_to_region_obligation_count"] == 1
    assert manifest["summary"]["unmatched_left_count"] == 0
    assert len(manifest["right_regions"]) == 1
    obligation = manifest["relational_obligations"][0]
    assert obligation["relation_kind"] == "call_to_region"
    eligibility = manifest["phase2_direct_call_eligibility"][0]
    assert eligibility["status"] == "candidate"
    assert eligibility["required_solver_stages"] == [
        "guard_relation",
        "argument_relation",
        "return_relation",
    ]


def test_call_to_region_reports_call_argument_failure_before_region_guard():
    left = _analysis_with_call("left", 0x1000, 0x1010, 0x2000)
    evidence = next(iter(left.effect_summary.call_argument_evidence.values()))
    object.__setattr__(evidence, "coverage_complete", False)
    right = _analysis_with_inline_region("right", 0x3000)

    manifest = build_call_effect_shadow_manifest(
        left,
        right,
        binary1_name="left",
        binary2_name="right",
    )

    backlog = manifest["proof_stage_backlog"][0]
    assert "call_extraction_argument_coverage_incomplete" in backlog["blocking_stages"]
    assert backlog["primary_proof_stage"] == "callsite_argument_evidence_incomplete"


def test_multiple_unmatched_calls_do_not_reuse_one_inline_region():
    left = _analysis_with_call("left", 0x1000, 0x1010, 0x2000)
    second = _analysis_with_call("left", 0x1000, 0x1020, 0x2100)
    left.effect_summary.call_argument_evidence.update(
        second.effect_summary.call_argument_evidence
    )
    left.effect_summary.call_site_effect_summary_evidence += (
        second.effect_summary.call_site_effect_summary_evidence
    )
    profile = left.effect_summary.function_control_effect_profile
    second_ref = next(iter(second.effect_summary.call_argument_evidence.values())).pcode_op_ref
    object.__setattr__(profile, "call_count", 2)
    object.__setattr__(
        profile,
        "call_like_pcode_op_keys",
        profile.call_like_pcode_op_keys + (second_ref.stable_key(),),
    )
    right = _analysis_with_inline_region("right", 0x3000)

    manifest = build_call_effect_shadow_manifest(
        left,
        right,
        binary1_name="left",
        binary2_name="right",
    )

    assert manifest["summary"]["call_to_region_obligation_count"] == 0
    assert manifest["summary"]["unmatched_left_count"] == 2


def test_region_live_in_excludes_call_target_and_classifies_parameter_register():
    class Space:
        def __init__(self, name):
            self.name = name

        def getName(self):
            return self.name

    class Address:
        def __init__(self, space, offset):
            self.space = Space(space)
            self.offset = offset

        def getAddressSpace(self):
            return self.space

        def getOffset(self):
            return self.offset

    class Varnode:
        def __init__(self, space, offset, size):
            self.address = Address(space, offset)
            self.size = size

        def isConstant(self):
            return False

        def getDef(self):
            return None

        def getAddress(self):
            return self.address

        def getSize(self):
            return self.size

    analyzer = ReturnAnalyzer(program=None)
    register = Varnode("register", 16, 4)
    parameters = (
        {"index": 0, "storage": {"space_name": "register", "offset": 16, "size": 4}},
    )

    target_key, target_status = analyzer._region_live_in_key(
        register,
        mnemonic="CALL",
        input_index=0,
        parameters=parameters,
    )
    assert target_key is None
    assert target_status == "excluded_nondata_operand"

    argument_key, argument_status = analyzer._region_live_in_key(
        register,
        mnemonic="CALL",
        input_index=1,
        parameters=parameters,
    )
    assert argument_status == "included"
    assert argument_key[0] == "parameter_input"

    class FunctionManager:
        def getFunctionContaining(self, address):
            return object()

    class Program:
        def getFunctionManager(self):
            return FunctionManager()

        def getListing(self):
            raise RuntimeError("unused")

        def getMemory(self):
            raise RuntimeError("unused")

    code_analyzer = ReturnAnalyzer(program=Program())
    code_key, code_status = code_analyzer._region_live_in_key(
        Varnode("ram", 0x4000, 8),
        mnemonic="COPY",
        input_index=0,
        parameters=(),
    )
    assert code_key is None
    assert code_status == "excluded_artifact_code_address"


def test_untrusted_assert_false_artifacts_cannot_complete_any_proof_stage():
    obligation = RelationalCallEffectObligation(
        obligation_id="obligation",
        relation_kind="call_to_call",
        observation_contract_id="contract",
        left_fact_id="left",
        right_fact_id="right",
    )
    stages = (
        "target_relation",
        "argument_relation",
        "abi_relation",
        "return_relation",
        "termination_relation",
        "trap_relation",
        "empty_state_transformer_and_frame",
    )
    eligibility = Phase2DirectCallEligibility(
        obligation_id="obligation",
        status="candidate",
        blockers=(),
        required_solver_stages=stages,
    )
    artifacts = []
    for index, stage in enumerate(stages):
        record = SolverProofRecord(
            proof_id=f"fake-proof-{index}",
            obligation_id="obligation",
            proof_stage=stage,
            observation_contract_id="contract",
            left_object_id="left",
            right_object_id="right",
            status="proven",
            solver_result="unsat",
            query_digest="a" * 64,
            normalized_assertion_digest="b" * 64,
            stage_input_digest="c" * 64,
            precondition_digest="d" * 64,
            solver_name="z3",
            solver_version="test",
            timeout_ms=1000,
            producer_kind="internal_parallel_solver_runner",
        )
        artifact = InternalSolverProofArtifact(
            record=record,
            query_text=f"(assert false) ; {stage}",
            normalized_assertion_text="(assert false)",
            stage_input_payload={"stage": stage, "index": index},
            precondition_payload={"contract": "contract"},
        )
        artifacts.append(artifact)

    readiness = evaluate_obligation_proof_readiness(obligation, eligibility, artifacts)
    assert readiness.decision_eligible is False
    assert readiness.completed_stages == ()
    assert readiness.missing_stages == stages
    assert "proof_artifact_verification_failed" in readiness.blockers

    wrong_eligibility = Phase2DirectCallEligibility(
        obligation_id="different-obligation",
        status="candidate",
        blockers=(),
        required_solver_stages=stages,
    )
    mismatched = evaluate_obligation_proof_readiness(
        obligation,
        wrong_eligibility,
        artifacts,
    )
    assert mismatched.decision_eligible is False
    assert "eligibility_obligation_id_mismatch" in mismatched.blockers


def test_arbitrary_rendered_assert_false_cannot_enter_trusted_producer():
    rendered = _RenderedStage(
        stage="return_relation",
        query_text="(assert false)\n(check-sat)",
        normalized_assertion_text="false",
        stage_input_payload={"stage": "return_relation"},
        precondition_payload={},
    )

    with pytest.raises(ValueError, match="untrusted_typed_stage_renderer"):
        _execute_rendered_stage(
            rendered,
            None,
            None,
            1,
            (),
        )

def test_deferred_call_result_shape_drops_artifact_local_caller_identity():
    left = (
        "runtime_ref",
        (
            "deferred_call",
            "call_out_of_scope",
            ("function", 11, 0x2000),
            ("deferred_call_site", 11, 0x1000, ("pcode_op", "B1"), ("function", 11, 0x2000), 1),
            None,
            None,
        ),
    )
    right = (
        "runtime_ref",
        (
            "deferred_call",
            "call_out_of_scope",
            ("function", 22, 0x4000),
            ("deferred_call_site", 22, 0x3000, ("pcode_op", "B5"), ("function", 22, 0x4000), 9),
            None,
            None,
        ),
    )

    assert _cross_binary_expression_shape(left) == _cross_binary_expression_shape(right)


def test_function_control_profile_requires_acyclic_complete_return_cfg():
    class Op:
        def __init__(self, mnemonic):
            self.mnemonic = mnemonic

        def getMnemonic(self):
            return self.mnemonic

    class Block:
        def __init__(self, index, mnemonics):
            self.index = index
            self.ops = [Op(name) for name in mnemonics]
            self.out = []

        def getIndex(self):
            return self.index

        def getIterator(self):
            return list(self.ops)

        def getOutSize(self):
            return len(self.out)

        def getOut(self, index):
            return self.out[index]

    class HighFunction:
        def __init__(self, blocks):
            self.blocks = blocks

        def getBasicBlocks(self):
            return list(self.blocks)

    entry = Block(0, ["INT_ADD", "BRANCH"])
    terminal = Block(1, ["RETURN"])
    entry.out = [terminal]
    analyzer = ReturnAnalyzer(program=None)

    profile = analyzer._build_function_control_effect_profile(
        HighFunction([entry, terminal])
    )
    assert profile.phase2_memory_free_scalar_candidate is True

    terminal.out = [entry]
    cyclic = analyzer._build_function_control_effect_profile(
        HighFunction([entry, terminal])
    )
    assert cyclic.cfg_acyclic is False
    assert cyclic.phase2_memory_free_scalar_candidate is False


def test_function_control_profile_cfg_edges_use_profiled_function_entry():
    class Space:
        def getName(self):
            return "ram"

    class Address:
        def __init__(self, offset):
            self.offset = offset

        def getAddressSpace(self):
            return Space()

        def getOffset(self):
            return self.offset

    class Op:
        def __init__(self, mnemonic):
            self.mnemonic = mnemonic

        def getMnemonic(self):
            return self.mnemonic

    class Block:
        def __init__(self, index, start, mnemonic):
            self.index = index
            self.start = Address(start)
            self.ops = [Op(mnemonic)]
            self.out = []

        def getIndex(self):
            return self.index

        def getStart(self):
            return self.start

        def getIterator(self):
            return list(self.ops)

        def getOutSize(self):
            return len(self.out)

        def getOut(self, index):
            return self.out[index]

    class Function:
        def getName(self):
            return "callee"

        def getEntryPoint(self):
            return Address(0x2000)

    entry = Block(0, 0x2000, "BRANCH")
    terminal = Block(1, 0x2010, "RETURN")
    entry.out = [terminal]

    analyzer = ReturnAnalyzer(program=None)
    analyzer._binary_id = "B1"
    analyzer._current_function_entry_address_value = Address(0x1000)
    profile = analyzer._build_function_control_effect_profile(
        type("HighFunction", (), {"getBasicBlocks": lambda self: [entry, terminal]})(),
        Function(),
    )

    source, target = profile.region_cfg_edge_keys[0]
    assert source[2] == ("function_entry", "ram", 0x2000)
    assert target[2] == ("function_entry", "ram", 0x2000)


def test_function_control_profile_rejects_unimplemented_and_ops_after_return():
    class Op:
        def __init__(self, mnemonic):
            self.mnemonic = mnemonic

        def getMnemonic(self):
            return self.mnemonic

    class Block:
        def __init__(self, mnemonics):
            self.ops = [Op(name) for name in mnemonics]

        def getIndex(self):
            return 0

        def getIterator(self):
            return list(self.ops)

        def getOutSize(self):
            return 0

    class HighFunction:
        def __init__(self, mnemonics):
            self.block = Block(mnemonics)

        def getBasicBlocks(self):
            return [self.block]

    analyzer = ReturnAnalyzer(program=None)
    unsupported = analyzer._build_function_control_effect_profile(
        HighFunction(["UNIMPLEMENTED", "RETURN"])
    )
    assert "UNIMPLEMENTED" in unsupported.unsupported_mnemonics
    assert unsupported.phase2_memory_free_scalar_candidate is False

    after_return = analyzer._build_function_control_effect_profile(
        HighFunction(["RETURN", "INT_ADD"])
    )
    assert after_return.pcode_after_return_count == 1
    assert after_return.phase2_memory_free_scalar_candidate is False

    allocation = analyzer._build_function_control_effect_profile(
        HighFunction(["NEW", "RETURN"])
    )
    assert allocation.unsupported_mnemonics == ()
    assert "NEW" in allocation.phase2_unsafe_mnemonics
    assert allocation.phase2_memory_free_scalar_candidate is False

    for mnemonic in ("INT_DIV", "INT_SDIV", "INT_REM", "INT_SREM"):
        trapping = analyzer._build_function_control_effect_profile(
            HighFunction([mnemonic, "RETURN"])
        )
        assert trapping.unsupported_mnemonics == ()
        assert mnemonic in trapping.phase2_unsafe_mnemonics
        assert trapping.phase2_memory_free_scalar_candidate is False


def test_argument_extraction_failure_is_not_labeled_as_guard_coverage():
    left = _analysis_with_call("left", 0x1000, 0x1010, 0x2000)
    right = _analysis_with_call("right", 0x3000, 0x3010, 0x4000)
    for analysis in (left, right):
        evidence = next(iter(analysis.effect_summary.call_argument_evidence.values()))
        object.__setattr__(evidence, "coverage_complete", False)

    manifest = build_call_effect_shadow_manifest(
        left,
        right,
        binary1_name="left",
        binary2_name="right",
    )

    fact = manifest["left_facts"][0]
    assert "argument_coverage_incomplete" in fact["extraction_failure_causes"]
    assert manifest["proof_stage_backlog"][0]["primary_proof_stage"] == (
        "callsite_argument_evidence_incomplete"
    )


def test_unmatched_call_preserves_its_argument_extraction_failure():
    left = _analysis_with_call("left", 0x1000, 0x1010, 0x2000)
    evidence = next(iter(left.effect_summary.call_argument_evidence.values()))
    object.__setattr__(evidence, "coverage_complete", False)
    right = FunctionReturnAnalysis(
        function_name="inlined",
        entry_point="0x3000",
        binary_id="right",
        parameters=[],
        returns=[],
        effect_summary=EffectSummary(
            parameter_names=[],
            effects=[],
            function_control_effect_profile=FunctionControlEffectProfile(
                block_count=1,
                pcode_op_count=1,
                return_block_count=1,
                pcode_enumeration_complete=True,
                cfg_edges_complete=True,
                cfg_acyclic=True,
                terminal_return_coverage_complete=True,
                call_like_identity_complete=True,
            ),
        ),
    )

    manifest = build_call_effect_shadow_manifest(
        left,
        right,
        binary1_name="left",
        binary2_name="right",
    )

    backlog = manifest["proof_stage_backlog"][0]
    assert "left_extraction_argument_coverage_incomplete" in backlog["blocking_stages"]
    assert backlog["primary_proof_stage"] == "callsite_argument_evidence_incomplete"


def _phase2_caller_analysis(binary_id: str, program_id: int, entry: int) -> FunctionReturnAnalysis:
    pcode_ref = _pcode_ref(binary_id, entry, entry + 0x10)
    target = CallTargetRef.from_name(
        "leaf_add",
        program_id=program_id,
        entry_offset=entry + 0x100,
    )
    left = Expression.parameter("a", 0, data_type="int", size=4)
    right = Expression.parameter("b", 1, data_type="int", size=4)
    callee_return = Expression.binary_op("INT_ADD", left, right)
    call_evidence = CallArgumentEvidence(
        pcode_op_ref=pcode_ref,
        target_ref=target,
        callee_param_identities=(
            (("parameter", 0), ("register_storage", 0, 1, 64, 0, 32)),
            (("parameter", 1), ("register_storage", 0, 2, 64, 0, 32)),
        ),
        arguments=(left, right),
        sources=("live_in_unmodified", "live_in_unmodified"),
        coverage_complete=True,
        recovery_status=CallArgumentEvidence.RECOVERY_COMPLETE,
    )
    callee_profile = FunctionControlEffectProfile(
        block_count=1,
        pcode_op_count=3,
        return_block_count=1,
        pcode_enumeration_complete=True,
        cfg_edges_complete=True,
        cfg_acyclic=True,
        terminal_return_coverage_complete=True,
        call_like_identity_complete=True,
    )
    caller_profile = FunctionControlEffectProfile(
        block_count=1,
        pcode_op_count=2,
        return_block_count=1,
        pcode_enumeration_complete=True,
        cfg_edges_complete=True,
        cfg_acyclic=True,
        terminal_return_coverage_complete=True,
        call_count=1,
        call_like_pcode_op_keys=(pcode_ref.stable_key(),),
        call_like_identity_complete=True,
    )
    return FunctionReturnAnalysis(
        function_name="wrapper",
        entry_point=hex(entry),
        function_ref=CallTargetRef.from_name(
            "wrapper",
            program_id=program_id,
            entry_offset=entry,
        ),
        binary_id=binary_id,
        parameters=[
            {"name": "a", "index": 0, "size": 4, "data_type": "int", "is_signed": True},
            {"name": "b", "index": 1, "size": 4, "data_type": "int", "is_signed": True},
        ],
        returns=[
            ReturnInfo(
                address=hex(entry + 0x20),
                conditions=[],
                value=Expression.binary_op("INT_ADD", left, right),
            )
        ],
        return_type="int",
        effect_summary=EffectSummary(
            parameter_names=["a", "b"],
            effects=[],
            call_argument_evidence={pcode_ref.stable_key(): call_evidence},
            call_site_effect_summary_evidence=(
                CallSiteEffectSummaryEvidence(
                    pcode_op_ref=pcode_ref,
                    target_ref=target,
                    argument_keys=(
                        expression_provenance_key(left),
                        expression_provenance_key(right),
                    ),
                    path_condition_keys=(),
                    summary_status="complete",
                    memory_effect_count=0,
                    has_unsupported_nested_call=False,
                    callee_control_profile_key=callee_profile.stable_key(),
                    callee_ordered_scalar_store_candidate=True,
                    return_summary_status="complete",
                    return_semantic_bit_width=32,
                    return_signed=True,
                    return_value_keys=(
                        expression_provenance_key(callee_return),
                    ),
                    return_partitions=(((), callee_return),),
                ),
            ),
            function_control_effect_profile=caller_profile,
        ),
    )


def _observe_phase2_call_result(analysis: FunctionReturnAnalysis) -> None:
    evidence = next(iter(analysis.effect_summary.call_argument_evidence.values()))
    deferred_ref = DeferredCallRef(
        caller_program_id=analysis.function_ref.program_id,
        caller_entry_offset=analysis.function_ref.entry_offset,
        pcode_op_ref=evidence.pcode_op_ref,
        target_ref=evidence.target_ref,
        sequence=0,
    )
    info = DeferredCallInfo(
        deferred_call_ref=deferred_ref,
        target_ref=evidence.target_ref,
        arguments=list(evidence.arguments),
        call_argument_recovery_status="complete",
        call_site_multiplicity=1,
    )
    analysis.deferred_calls = {deferred_ref.stable_key(): info}
    value = Expression.unknown("observed_call_result", runtime_ref=info.unknown_ref)
    value.size = 4
    analysis.returns = [
        ReturnInfo(
            address=hex(int(analysis.entry_point, 16) + 0x20),
            conditions=[],
            value=value,
            pcode_op_ref=_pcode_ref(
                analysis.binary_id,
                int(analysis.entry_point, 16),
                int(analysis.entry_point, 16) + 0x20,
                mnemonic="RETURN",
                seq_time=1,
            ),
        )
    ]


@pytest.mark.parametrize(
    "tamper_kind",
    (
        "consuming_use_id",
        "consumer_domain",
        "invocation_contract",
        "census_digest",
        "different_guarded_use",
        "obligation_use_edge",
    ),
)
def test_prepared_use_domain_mapping_rebuild_rejects_manifest_tampering(tamper_kind):
    pytest.importorskip("z3")
    left = _phase2_caller_analysis("B1", 1, 0x1000)
    right = _phase2_caller_analysis("B2", 2, 0x3000)
    _observe_phase2_call_result(left)
    _observe_phase2_call_result(right)
    source = StrategySourceAnalysisPair.create(left, right)
    checker = EquivalenceChecker(timeout=5, enable_rewrite=False)
    prepared = prepare_solver_surface(
        source,
        observation_contract_digest=checker.observation_contract.contract_id,
        comparison_session_id="mapping-tamper",
        branch_id="PairwiseStrategy",
        generation=1,
        decision_mode=CallProofDecisionMode.PREFLIGHT_PROJECTION,
    )
    manifest = checker._call_effect_shadow_manifest(
        prepared.analysis1,
        prepared.analysis2,
        "left",
        "right",
    )
    original = validate_call_resolution_projection(
        manifest,
        prepared,
        generation=1,
        trusted_proof_artifacts=checker._last_internal_call_effect_artifacts,
    )
    assert original.proven
    assert original.use_mapping_builder_version == "prepared_call_use_mapping_v2"

    tampered = deepcopy(manifest)
    fact = tampered["left_facts"][0]
    binding = fact["output_use_bindings"][0]
    assert binding["schema_version"] == "call_output_use_binding_v2"
    assert binding["producer_pcode_op_key"]
    assert binding["proof_use_key"] == binding["use_id"]
    assert binding["storage_availability"] in {"available", "unavailable"}
    if tamper_kind == "consuming_use_id":
        binding["use_id"] = "reassigned-use"
    elif tamper_kind == "consumer_domain":
        binding["semantic_location"][0] = "effects"
    elif tamper_kind == "invocation_contract":
        binding["invocation_contract"]["proven"] = False
    elif tamper_kind == "census_digest":
        fact["output_use_census_digest"] = "0" * 64
    elif tamper_kind == "obligation_use_edge":
        tampered["relational_obligations"][0]["left_fact_id"] = "reattached-call"
    else:
        binding["semantic_location"] = ["effects", 99, "value"]
        binding["use_guard_keys"] = [["condition", "different"]]

    rejected = validate_call_resolution_projection(
        tampered,
        prepared,
        generation=1,
        trusted_proof_artifacts=checker._last_internal_call_effect_artifacts,
    )
    assert rejected.status == "inconclusive"
    assert "prepared_use_domain_coverage_mapping_mismatch" in rejected.root_blockers


def test_preflight_final_gate_rebuilds_use_mapping_from_prepared_analysis(monkeypatch):
    pytest.importorskip("z3")
    import scripts.function_tracer_pcode.checker.checker as checker_module

    left = _phase2_caller_analysis("B1", 1, 0x1000)
    right = _phase2_caller_analysis("B2", 2, 0x3000)
    _observe_phase2_call_result(left)
    _observe_phase2_call_result(right)
    checker = EquivalenceChecker(timeout=5, enable_rewrite=False)
    trusted_validate = checker_module.validate_call_resolution_projection
    call_count = 0

    def tamper_before_final_gate(manifest, prepared, **kwargs):
        nonlocal call_count
        call_count += 1
        if call_count == 2:
            manifest["left_facts"][0]["output_use_census_digest"] = "f" * 64
        return trusted_validate(manifest, prepared, **kwargs)

    monkeypatch.setattr(
        checker_module,
        "validate_call_resolution_projection",
        tamper_before_final_gate,
    )
    result = checker.check(left, right, "left", "right")

    assert call_count == 2
    assert result.is_equivalent is None
    assert any(
        "deferred_call_use_coverage_mapping_invalid" in tuple(reason.evidence_refs or ())
        for reason in result.unknown_reasons
    )


def _observe_phase2_call_result_in_store(
    analysis: FunctionReturnAnalysis,
    address: int,
) -> None:
    _observe_phase2_call_result(analysis)
    call_value = analysis.returns[0].value
    analysis.returns = [
        ReturnInfo(
            address=hex(int(analysis.entry_point, 16) + 0x20),
            conditions=[],
            value=Expression.constant(0, size=4),
        )
    ]
    profile = analysis.effect_summary.function_control_effect_profile
    object.__setattr__(profile, "store_count", 1)
    analysis.effect_summary.effects = [
        StoreEffect(
            CanonicalLocation(
                base_ref=LocationBaseRef.parameter("a", index=0),
                offset=0,
                size=4,
            ),
            Expression.binary_op(
                "INT_ADD", call_value, Expression.constant(1, size=4)
            ),
            [],
            10,
            provenance=_local_store_provenance(
                _pcode_ref(
                    analysis.binary_id,
                    int(analysis.entry_point, 16),
                    address,
                    mnemonic="STORE",
                    seq_time=1,
                )
            ),
        )
    ]


def test_observed_call_result_projection_is_lowered_and_receipted():
    pytest.importorskip("z3")
    left = _phase2_caller_analysis("B1", 1, 0x1000)
    right = _phase2_caller_analysis("B2", 2, 0x3000)
    _observe_phase2_call_result(left)
    _observe_phase2_call_result(right)

    result = EquivalenceChecker(
        timeout=5,
        enable_rewrite=False,
        enable_completed_recovery_proofs=True,
    ).check(left, right, "left", "right")

    assert result.is_equivalent is True
    projection = result.call_effect_shadow_manifest["preflight_projection"]
    assert projection["status"] == "proven"
    assert len(projection["semantic_bindings"]) == 1
    binding = projection["semantic_bindings"][0]
    assert binding["consumer_domains"] == ("value",)
    assert len(binding["left_use_bindings"]) == 1
    assert len(binding["right_use_bindings"]) == 1
    for use in (*binding["left_use_bindings"], *binding["right_use_bindings"]):
        use = dict(use)
        assert use["operand_ordinal"] == -1
        assert use["storage_identity"] == ()
        assert use["storage_availability"] == "unavailable"
    assert result.call_proof_terminal_provenance["comparison_receipt_id"]
    assert "certified call projection" in (result.smt_formula or "")


def test_observed_call_result_stored_to_memory_is_proven_and_receipted():
    pytest.importorskip("z3")
    left = _phase2_caller_analysis("B1", 1, 0x1000)
    right = _phase2_caller_analysis("B2", 2, 0x3000)
    for analysis, address in ((left, 0x1018), (right, 0x3018)):
        _observe_phase2_call_result_in_store(analysis, address)

    result = EquivalenceChecker(
        timeout=5,
        enable_rewrite=False,
        enable_completed_recovery_proofs=True,
    ).check(left, right, "left", "right")

    assert result.is_equivalent is True
    projection = result.call_effect_shadow_manifest["preflight_projection"]
    binding = projection["semantic_bindings"][0]
    assert dict(binding["left_use_bindings"][0])["semantic_location"][0] == "effects"
    assert dict(binding["right_use_bindings"][0])["semantic_location"][0] == "effects"
    caller_artifact = next(
        artifact
        for artifact in result.call_effect_shadow_manifest["solver_proof_records"]
        if artifact["proof_stage"] == "caller_memory_relation"
    )
    assert caller_artifact["status"] == "proven"
    assert projection["normalization_trust_basis"] == (
        "trusted_solver_semantic_width_tcb_v1"
    )
    assert projection["surface_delta_audit_id"]
    assert projection["semantic_transformation_certificate_id"]
    assert projection["comparison_receipt_disposition_counts"][
        "projection_active_total"
    ] > 0
    assert result.call_effect_shadow_manifest["preflight_gate_delta_diagnostic"][
        "decision_mode"
    ] == (
        "preflight_projection"
    )
    receipt = result.call_proof_terminal_provenance
    assert receipt["comparison_receipt_id"]


def test_observed_call_result_store_does_not_hide_different_call_semantics():
    pytest.importorskip("z3")
    left = _phase2_caller_analysis("B1", 1, 0x1000)
    right = _phase2_caller_analysis("B2", 2, 0x3000)
    _observe_phase2_call_result_in_store(left, 0x1018)
    _observe_phase2_call_result_in_store(right, 0x3018)
    right_evidence = right.effect_summary.call_site_effect_summary_evidence[0]
    different = Expression.constant(99, size=4)
    object.__setattr__(right_evidence, "return_partitions", (((), different),))
    object.__setattr__(
        right_evidence,
        "return_value_keys",
        (expression_provenance_key(different),),
    )

    result = EquivalenceChecker(
        timeout=5,
        enable_rewrite=False,
        enable_completed_recovery_proofs=True,
    ).check(left, right, "left", "right")

    assert result.is_equivalent is not True


def test_no_active_pair_receipt_fails_closed_without_relational_certificate():
    pytest.importorskip("z3")
    left = _phase2_caller_analysis("B1", 1, 0x1000)
    right = _phase2_caller_analysis("B2", 2, 0x3000)
    left.returns = []
    right.returns = []

    result = EquivalenceChecker(
        timeout=5,
        enable_rewrite=False,
        enable_completed_recovery_proofs=True,
    ).check(left, right, "left", "right")

    counts = result.call_effect_shadow_manifest["preflight_projection"][
        "comparison_receipt_disposition_counts"
    ]
    assert counts["projection_active_total"] == 0
    assert counts["projection_no_active_pair_proven"] == 0
    assert any(
        "call_projection_no_active_pair_proof_missing"
        in tuple(reason.evidence_refs or ())
        for reason in result.unknown_reasons
    )


def test_conditional_call_projection_is_distributed_to_consuming_cases_only():
    pytest.importorskip("z3")
    left = _phase2_caller_analysis("B1", 1, 0x1000)
    right = _phase2_caller_analysis("B2", 2, 0x3000)
    parameter = Expression.parameter("a", 0, data_type="int", size=4)
    guard = Condition(
        Expression.binary_op("INT_SLESS", parameter, Expression.constant(0, size=4)),
        False,
    )
    for analysis in (left, right):
        _observe_phase2_call_result(analysis)
        call_return = analysis.returns[0]
        call_return.conditions = [guard]
        analysis.returns.append(
            ReturnInfo(
                address=hex(int(analysis.entry_point, 16) + 0x24),
                conditions=[Condition(guard.expression, True)],
                value=Expression.constant(7, size=4),
            )
        )
        argument_evidence = next(
            iter(analysis.effect_summary.call_argument_evidence.values())
        )
        object.__setattr__(argument_evidence, "path_conditions", ((guard,),))
        effect_evidence = analysis.effect_summary.call_site_effect_summary_evidence[0]
        object.__setattr__(effect_evidence, "path_condition_keys", (condition_key(guard),))

    result = EquivalenceChecker(
        timeout=5,
        enable_rewrite=False,
        enable_completed_recovery_proofs=True,
    ).check(left, right, "left", "right")

    assert result.is_equivalent is True
    assert result.pairwise_debug_stats["guard_overlap_logical_edges"] == 4
    assert result.pairwise_debug_stats["guard_overlap_unsat_edges"] == 2
    assert result.pairwise_debug_stats["guard_overlap_value_candidates"] == 2
    assert not any(
        "call_projection_use_binding_mismatch" in str(reason.detail)
        for reason in result.unknown_reasons
    )


def test_observed_call_to_inline_region_projection_lowers_to_region_value():
    pytest.importorskip("z3")
    left, right, _ = _call_to_region_proof_inputs()
    _observe_phase2_call_result(left)

    result = EquivalenceChecker(
        timeout=5,
        enable_rewrite=False,
        enable_completed_recovery_proofs=True,
    ).check(left, right, "left", "right")

    assert result.is_equivalent is True
    projection = result.call_effect_shadow_manifest["preflight_projection"]
    binding = projection["semantic_bindings"][0]
    assert binding["relation_kind"] == "call_to_region"
    assert binding["call_on_left"] is True
    assert len(binding["left_use_bindings"]) == 1
    assert len(binding["right_use_bindings"]) == 0
    assert "certified call projection" in (result.smt_formula or "")


@pytest.mark.parametrize(
    ("return_guarded", "expected_status"),
    [
        (False, "inconclusive"),
        (True, "proven_guarded_reaching_definition"),
    ],
)
def test_call_output_use_requires_guarded_execution_before_use(
    return_guarded,
    expected_status,
):
    analysis = _phase2_caller_analysis("B1", 1, 0x1000)
    _observe_phase2_call_result(analysis)
    parameter = Expression.parameter("a", 0, data_type="int", size=4)
    guard = Condition(
        Expression.binary_op("INT_SLESS", parameter, Expression.constant(0, size=4)),
        False,
    )
    argument_evidence = next(
        iter(analysis.effect_summary.call_argument_evidence.values())
    )
    object.__setattr__(argument_evidence, "path_conditions", ((guard,),))
    effect_evidence = analysis.effect_summary.call_site_effect_summary_evidence[0]
    object.__setattr__(effect_evidence, "path_condition_keys", (condition_key(guard),))
    if return_guarded:
        analysis.returns[0].conditions = [guard]

    manifest = build_call_effect_shadow_manifest(
        analysis,
        _phase2_caller_analysis("B2", 2, 0x3000),
        binary1_name="left",
        binary2_name="right",
    )

    assert manifest["left_facts"][0][
        "output_use_reaching_definition_status"
    ] == expected_status
    binding = manifest["left_facts"][0]["output_use_bindings"][0]
    if return_guarded:
        assert binding["invocation_contract"]["execution_order_proof"] == (
            "proven_same_block_sequence"
        )
        assert binding["invocation_contract"]["proven"] is True


def test_call_output_use_without_consumer_op_provenance_is_inconclusive():
    analysis = _phase2_caller_analysis("B1", 1, 0x1000)
    counterpart = _phase2_caller_analysis("B2", 2, 0x3000)
    _observe_phase2_call_result(analysis)
    _observe_phase2_call_result(counterpart)
    analysis.returns[0].pcode_op_ref = None
    counterpart.returns[0].pcode_op_ref = None

    manifest = build_call_effect_shadow_manifest(
        analysis,
        counterpart,
        binary1_name="left",
        binary2_name="right",
    )

    fact = manifest["left_facts"][0]
    assert fact["output_use_reaching_definition_status"] == "inconclusive"
    contract = fact["output_use_bindings"][0]["invocation_contract"]
    assert contract["execution_order_proof"] == (
        "inconclusive_use_site_provenance_missing"
    )
    assert contract["proven"] is False
    result = EquivalenceChecker(
        timeout=5,
        enable_rewrite=False,
        enable_completed_recovery_proofs=True,
    ).check(analysis, counterpart, "left", "right")
    assert result.is_equivalent is None
    assert result.call_effect_shadow_manifest["preflight_projection"]["status"] == (
        "inconclusive"
    )


def test_call_output_use_before_call_in_same_block_is_inconclusive():
    analysis = _phase2_caller_analysis("B1", 1, 0x1000)
    _observe_phase2_call_result(analysis)
    analysis.returns[0].pcode_op_ref = _pcode_ref(
        "B1", 0x1000, 0x1008, mnemonic="RETURN", seq_time=0
    )

    manifest = build_call_effect_shadow_manifest(
        analysis,
        _phase2_caller_analysis("B2", 2, 0x3000),
        binary1_name="left",
        binary2_name="right",
    )

    contract = manifest["left_facts"][0]["output_use_bindings"][0][
        "invocation_contract"
    ]
    assert contract["execution_order_proof"] == "inconclusive_same_block_sequence"
    assert contract["proven"] is False


def _configure_call_use_cfg(
    analysis: FunctionReturnAnalysis,
    *,
    bypass_call: bool,
) -> None:
    entry = int(analysis.entry_point, 16)
    old_argument = next(iter(analysis.effect_summary.call_argument_evidence.values()))
    call_ref = _pcode_ref(
        analysis.binary_id,
        entry,
        entry + 0x10,
        block_index=1,
        seq_time=0,
    )
    object.__setattr__(old_argument, "pcode_op_ref", call_ref)
    effect_evidence = analysis.effect_summary.call_site_effect_summary_evidence[0]
    object.__setattr__(effect_evidence, "pcode_op_ref", call_ref)
    profile = analysis.effect_summary.function_control_effect_profile
    blocks = tuple(
        _block_ref_for_pcode(
            _pcode_ref(
                analysis.binary_id,
                entry,
                entry + index * 0x10,
                block_index=index,
            )
        ).stable_key()
        for index in range(3)
    )
    edges = (
        ((blocks[0], blocks[1]), (blocks[0], blocks[2]), (blocks[1], blocks[2]))
        if bypass_call
        else ((blocks[0], blocks[1]), (blocks[1], blocks[2]))
    )
    object.__setattr__(profile, "call_like_pcode_op_keys", (call_ref.stable_key(),))
    object.__setattr__(profile, "region_block_keys", blocks)
    object.__setattr__(profile, "region_cfg_edge_keys", edges)
    object.__setattr__(profile, "region_entry_block_key", blocks[0])
    object.__setattr__(profile, "region_identity_complete", True)
    object.__setattr__(profile, "region_single_entry", True)
    object.__setattr__(profile, "region_all_exits_enumerated", True)
    _observe_phase2_call_result(analysis)
    analysis.returns[0].pcode_op_ref = _pcode_ref(
        analysis.binary_id,
        entry,
        entry + 0x30,
        mnemonic="RETURN",
        block_index=2,
        seq_time=0,
    )


@pytest.mark.parametrize(
    ("bypass_call", "expected_proof"),
    [
        (False, "proven_cfg_dominance"),
        (True, "inconclusive_guarded_subgraph_dominance_missing"),
    ],
)
def test_call_output_use_requires_cfg_dominance(bypass_call, expected_proof):
    analysis = _phase2_caller_analysis("B1", 1, 0x1000)
    _configure_call_use_cfg(analysis, bypass_call=bypass_call)

    manifest = build_call_effect_shadow_manifest(
        analysis,
        _phase2_caller_analysis("B2", 2, 0x3000),
        binary1_name="left",
        binary2_name="right",
    )

    contract = manifest["left_facts"][0]["output_use_bindings"][0][
        "invocation_contract"
    ]
    assert contract["execution_order_proof"] == expected_proof
    assert contract["proven"] is (not bypass_call)


def test_call_output_use_inside_phi_requires_incoming_edge_dominance():
    analysis = _phase2_caller_analysis("B1", 1, 0x1000)
    _observe_phase2_call_result(analysis)
    call_value = analysis.returns[0].value
    analysis.returns[0].value = Expression.phi(
        [(None, call_value), (None, Expression.constant(0, size=4))]
    )

    manifest = build_call_effect_shadow_manifest(
        analysis,
        _phase2_caller_analysis("B2", 2, 0x3000),
        binary1_name="left",
        binary2_name="right",
    )

    contract = manifest["left_facts"][0]["output_use_bindings"][0][
        "invocation_contract"
    ]
    assert contract["execution_order_proof"] == (
        "inconclusive_phi_incoming_edge_dominance_missing"
    )
    assert contract["proven"] is False


def test_return_only_unsat_cannot_discharge_call_effect_obligations():
    pytest.importorskip("z3")
    left = _phase2_caller_analysis("B1", 1, 0x1000)
    right = _phase2_caller_analysis("B2", 2, 0x3000)

    for analysis in (left, right):
        evidence = analysis.effect_summary.call_site_effect_summary_evidence[0]
        object.__setattr__(evidence, "return_summary_status", "candidate")
        object.__setattr__(evidence, "return_partitions", ())

    result = EquivalenceChecker(
        timeout=5,
        enable_rewrite=False,
        enable_completed_recovery_proofs=True,
    ).check(left, right, "left", "right")

    assert result.is_equivalent is None
    manifest = result.call_effect_shadow_manifest
    assert manifest["mode"] == "shadow_no_decision_effect"
    assert manifest["summary"]["semantic_proof_status"] == "pending"
    assert manifest["solver_proof_records"] == []
    assert manifest["structural_coverage_certificate"]["status"] == "complete"
    assert manifest["structural_coverage_certificate"]["decision_effect"] == (
        "diagnostic_precondition_only"
    )
    readiness = manifest["proof_readiness"][0]
    assert readiness["completed_stages"] == []
    assert readiness["decision_eligible"] is False
    assert result.unknown_reasons
    assert {
        reason.proof_stage for reason in result.unknown_reasons
    } == {"callee_return_relation_missing"}


def test_typed_pure_direct_call_proofs_can_promote_equivalence():
    pytest.importorskip("z3")
    left = _phase2_caller_analysis("B1", 1, 0x1000)
    right = _phase2_caller_analysis("B2", 2, 0x3000)

    result = EquivalenceChecker(
        timeout=5,
        enable_rewrite=False,
        enable_completed_recovery_proofs=True,
    ).check(left, right, "left", "right")

    assert result.is_equivalent is True
    assert result.unknown_reasons == []
    manifest = result.call_effect_shadow_manifest
    assert manifest["mode"] == "typed_relational_call_effect_proof"
    assert [
        record["proof_stage"] for record in manifest["solver_proof_records"]
    ] == ["guard_relation", "argument_relation", "return_relation"]
    assert all(
        record["status"] == "proven" and record["solver_result"] == "unsat"
        for record in manifest["solver_proof_records"]
    )
    assert manifest["proof_readiness"][0]["decision_eligible"] is True
    assert manifest["phase2_discharge_gate"]["status"] == "proven"
    assert manifest["summary"]["semantic_proof_status"] == "proven"
    assert manifest["legacy_replacement_readiness"]["status"] == "ready"
    assert manifest["decision_mode"] == "preflight_projection"
    assert manifest["preflight_projection"]["comparison_receipt_id"]
    resolutions = manifest["preflight_projection"]["blocker_resolutions"]
    assert resolutions
    assert len({item["occurrence_id"] for item in resolutions}) == len(resolutions)
    assert all(
        item["status"] == "proven"
        and item["mapping_basis"] == "callsite_pcode_ref"
        and item["requirement_id"]["proof_kind"] == "call_effect_summary_proof"
        for item in resolutions
    )
    assert result.call_proof_terminal_provenance["decision_owner_mode"] == (
        "preflight_projection"
    )
    assert result.call_proof_terminal_provenance["dispatch_cleanup_complete"] is True
    assert manifest["left_facts"][0]["invocation_proof_status"] == "proven_acyclic_cfg"
    assert manifest["left_facts"][0]["output_use_reaching_definition_status"] == (
        "not_observed_closed"
    )


def test_preflight_rejects_call_invocation_without_acyclic_cfg_proof():
    left = _phase2_caller_analysis("B1", 1, 0x1000)
    right = _phase2_caller_analysis("B2", 2, 0x3000)
    for analysis in (left, right):
        profile = analysis.effect_summary.function_control_effect_profile
        object.__setattr__(profile, "cfg_acyclic", False)

    result = EquivalenceChecker(timeout=5, enable_rewrite=False).check(
        left, right, "left", "right"
    )

    assert result.is_equivalent is None
    backlog = result.call_effect_shadow_manifest["proof_stage_backlog"][0]
    assert "left_call_invocation_multiplicity_unproven" in backlog["blocking_stages"]
    assert "right_call_invocation_multiplicity_unproven" in backlog["blocking_stages"]


def test_preflight_proves_single_visit_call_block_outside_cfg_cycle():
    left = _phase2_caller_analysis("B1", 1, 0x1000)
    right = _phase2_caller_analysis("B2", 2, 0x3000)
    for analysis in (left, right):
        profile = analysis.effect_summary.function_control_effect_profile
        call_ref = next(iter(analysis.effect_summary.call_argument_evidence.values())).pcode_op_ref
        blocks = tuple(
            PcodeBlockRef(
                block_index=index,
                start_address_offset=int(call_ref.function_entry_offset) + index * 0x100,
                binary_id=call_ref.binary_id,
                function_entry_space=call_ref.function_entry_space,
                function_entry_offset=call_ref.function_entry_offset,
            ).stable_key()
            for index in range(3)
        )
        object.__setattr__(profile, "cfg_acyclic", False)
        object.__setattr__(profile, "region_block_keys", blocks)
        object.__setattr__(
            profile,
            "region_cfg_edge_keys",
            ((blocks[0], blocks[1]), (blocks[1], blocks[1]), (blocks[1], blocks[2])),
        )
        object.__setattr__(profile, "region_entry_block_key", blocks[0])
        object.__setattr__(profile, "region_exit_block_keys", (blocks[2],))
        object.__setattr__(profile, "region_identity_complete", True)
        object.__setattr__(profile, "region_single_entry", True)
        object.__setattr__(profile, "region_all_exits_enumerated", True)
        object.__setattr__(profile, "region_cross_edges_enumerated", True)

    manifest = build_call_effect_shadow_manifest(
        left,
        right,
        binary1_name="left",
        binary2_name="right",
    )

    assert manifest["left_facts"][0]["invocation_proof_status"] == (
        "proven_cfg_single_visit"
    )
    assert manifest["right_facts"][0]["invocation_proof_status"] == (
        "proven_cfg_single_visit"
    )


def test_preflight_preserves_source_arguments_for_pairwise_override(monkeypatch):
    pytest.importorskip("z3")
    left = _phase2_caller_analysis("B1", 1, 0x1000)
    right = _phase2_caller_analysis("B2", 2, 0x3000)
    checker = EquivalenceChecker(timeout=5, enable_rewrite=False)
    original = checker.pairwise_strategy.check
    observed = []

    def override(a1, a2, save_formula=False):
        observed.append((a1, a2))
        return original(a1, a2, save_formula)

    monkeypatch.setattr(checker.pairwise_strategy, "check", override)
    result = checker.check(left, right, "left", "right")

    assert observed == [(left, right)]
    assert result.is_equivalent is True


def test_preflight_rejects_override_eq_without_consumption_receipt(monkeypatch):
    from scripts.function_tracer_pcode.proof.strategies.proof_gates._shared import StrategyResult

    left = _phase2_caller_analysis("B1", 1, 0x1000)
    right = _phase2_caller_analysis("B2", 2, 0x3000)
    checker = EquivalenceChecker(timeout=5, enable_rewrite=False)

    def override(_a1, _a2, _save_formula=False):
        return StrategyResult(
            is_equivalent=True,
            solver_results=ParallelResult(results=[]),
            total_pairs=1,
            unsat_pairs=1,
        )

    monkeypatch.setattr(checker.pairwise_strategy, "check", override)
    result = checker.check(left, right, "left", "right")

    assert result.is_equivalent is None
    assert any(
        "comparison_receipt_missing" in tuple(reason.evidence_refs or ())
        for reason in result.unknown_reasons
    )


def test_preflight_monolithic_branch_consumes_prepared_surface_and_emits_receipt(monkeypatch):
    pytest.importorskip("z3")
    import scripts.function_tracer_pcode.proof.call_effect.preflight as preflight_module
    from scripts.function_tracer_pcode.proof.strategies import monolithic as monolithic_module

    left = _phase2_caller_analysis("B1", 1, 0x1000)
    right = _phase2_caller_analysis("B2", 2, 0x3000)
    ambient_dispatch_reads = 0
    trusted_current_dispatch_depth = preflight_module.current_dispatch_depth

    def counted_current_dispatch_depth():
        nonlocal ambient_dispatch_reads
        ambient_dispatch_reads += 1
        return trusted_current_dispatch_depth()

    monkeypatch.setattr(
        preflight_module,
        "current_dispatch_depth",
        counted_current_dispatch_depth,
    )

    def reject_uncertified_decision_transform(*_args, **_kwargs):
        raise AssertionError("monolithic decision stage transformed prepared surface")

    monkeypatch.setattr(
        monolithic_module,
        "normalize_analysis_semantic_width",
        reject_uncertified_decision_transform,
    )
    monkeypatch.setattr(
        monolithic_module,
        "align_return_value_extension_surfaces",
        reject_uncertified_decision_transform,
    )

    result = EquivalenceChecker(
        strategy="monolithic",
        timeout=5,
        enable_rewrite=False,
        enable_completed_recovery_proofs=True,
    ).check(left, right, "left", "right")

    assert result.is_equivalent is True
    provenance = result.call_proof_terminal_provenance
    assert provenance["terminal_branch_id"] == "MonolithicStrategy"
    assert provenance["comparison_receipt_id"]
    assert provenance["dispatch_cleanup_complete"] is True
    assert ambient_dispatch_reads == 1


def test_default_preflight_mode_does_not_enter_legacy_post_pairwise_gate(monkeypatch):
    pytest.importorskip("z3")
    left = _phase2_caller_analysis("B1", 1, 0x1000)
    right = _phase2_caller_analysis("B2", 2, 0x3000)
    checker = EquivalenceChecker(timeout=5, enable_rewrite=False)

    def rejected_legacy_path(*_args, **_kwargs):
        raise AssertionError("legacy post-pairwise gate entered")

    monkeypatch.setattr(
        checker,
        "_apply_phase2_relational_call_discharge",
        rejected_legacy_path,
    )

    result = checker.check(left, right, "left", "right")

    assert result.is_equivalent is True
    assert result.call_proof_terminal_provenance["decision_owner_mode"] == (
        "preflight_projection"
    )


def test_non_call_effect_summary_incompleteness_cannot_be_cleared_by_call_proof():
    pytest.importorskip("z3")
    left = _phase2_caller_analysis("B1", 1, 0x1000)
    right = _phase2_caller_analysis("B2", 2, 0x3000)
    left.effect_summary.incomplete_reasons = (
        "effect_summary_path_coverage_incomplete",
    )

    result = EquivalenceChecker(
        timeout=5,
        enable_rewrite=False,
        enable_completed_recovery_proofs=True,
    ).check(left, right, "left", "right")

    assert result.is_equivalent is None
    assert any(
        "function1:effect_summary_path_coverage_incomplete"
        in tuple(reason.evidence_refs or ())
        for reason in result.unknown_reasons
    )
    manifest = result.call_effect_shadow_manifest
    assert manifest["proof_readiness"][0]["decision_eligible"] is True
    assert manifest["phase2_discharge_gate"]["status"] == "blocked"
    assert manifest["phase2_discharge_gate"]["failure_cause"] == (
        "non_call_effect_unsafety_present"
    )
    assert manifest["phase2_discharge_gate"]["non_call_effect_unsafety"] == [
        "effect_summary_path_coverage_incomplete"
    ]


def test_completed_recovery_proof_flag_disables_typed_call_promotion():
    pytest.importorskip("z3")
    left = _phase2_caller_analysis("B1", 1, 0x1000)
    right = _phase2_caller_analysis("B2", 2, 0x3000)

    result = EquivalenceChecker(
        timeout=5,
        enable_rewrite=False,
        enable_completed_recovery_proofs=False,
    ).check(left, right, "left", "right")

    assert result.is_equivalent is None
    manifest = result.call_effect_shadow_manifest
    assert len(manifest["solver_proof_records"]) == 3
    assert manifest["proof_readiness"][0]["decision_eligible"] is True
    assert manifest["phase2_discharge_gate"] == {
        "status": "disabled",
        "decision_effect": "diagnostic_only",
        "failure_cause": "completed_recovery_proofs_disabled",
    }


def _phase2_manifest_with_certificate(left, right):
    manifest = build_call_effect_shadow_manifest(
        left,
        right,
        binary1_name="left",
        binary2_name="right",
    )
    EquivalenceChecker._attach_structural_coverage_certificate(manifest)
    return manifest


def _attach_scalar_store_callee_effect(
    analysis: FunctionReturnAnalysis,
    *,
    value_delta: int = 0,
    location_offset: int = 0,
) -> None:
    evidence = analysis.effect_summary.call_site_effect_summary_evidence[0]
    value = Expression.parameter("b", 1, data_type="int", size=4)
    if value_delta:
        value = Expression.binary_op(
            "INT_ADD", value, Expression.constant(value_delta, size=4)
        )
    effect = StoreEffect(
        location=CanonicalLocation(
            base_ref=LocationBaseRef.parameter("a", index=0),
            offset=location_offset,
            size=4,
        ),
        value=value,
        conditions=[],
        order_key=1,
    )
    profile = FunctionControlEffectProfile(
        block_count=1,
        pcode_op_count=4,
        return_block_count=1,
        pcode_enumeration_complete=True,
        cfg_edges_complete=True,
        cfg_acyclic=True,
        terminal_return_coverage_complete=True,
        store_count=1,
        call_like_identity_complete=True,
    )
    object.__setattr__(evidence, "memory_effect_count", 1)
    object.__setattr__(evidence, "memory_effects", (effect,))
    object.__setattr__(evidence, "callee_control_profile_key", profile.stable_key())
    analysis.effect_summary.effects = [
        StoreEffect(
            location=effect.location,
            value=effect.value,
            conditions=list(effect.conditions),
            order_key=10,
            provenance=_call_derived_store_provenance(
                evidence.pcode_op_ref,
                evidence.target_ref,
                0,
            ),
        )
    ]


def _call_to_region_proof_inputs():
    left = _analysis_with_call("left", 0x1000, 0x1010, 0x2000)
    left.returns = [
        ReturnInfo(
            address="0x1020",
            conditions=[],
            value=Expression.parameter("x", 0, size=4),
        )
    ]
    left.return_type = "int"
    right = _analysis_with_inline_region("right", 0x3000)
    return left, right, _phase2_manifest_with_certificate(left, right)


def _call_to_region_memory_proof_inputs(*, region_value_delta: int = 0):
    left, right, _ = _call_to_region_proof_inputs()
    location = CanonicalLocation(
        base_ref=LocationBaseRef.parameter("x", index=0),
        offset=0,
        size=4,
    )
    call_value = Expression.parameter("x", 0, size=4)
    region_value = Expression.parameter("x", 0, size=4)
    if region_value_delta:
        region_value = Expression.binary_op(
            "INT_ADD",
            region_value,
            Expression.constant(region_value_delta, size=4),
        )
    evidence = left.effect_summary.call_site_effect_summary_evidence[0]
    call_effect = StoreEffect(location, call_value, [], 1)
    region_effect = StoreEffect(
        location,
        region_value,
        [],
        1,
        provenance=_local_store_provenance(
            _pcode_ref(
                "right",
                0x3000,
                0x3018,
                mnemonic="STORE",
            ),
        ),
    )
    callee_profile = FunctionControlEffectProfile(
        block_count=1,
        pcode_op_count=3,
        return_block_count=1,
        pcode_enumeration_complete=True,
        cfg_edges_complete=True,
        cfg_acyclic=True,
        terminal_return_coverage_complete=True,
        store_count=1,
        call_like_identity_complete=True,
    )
    object.__setattr__(evidence, "memory_effect_count", 1)
    object.__setattr__(evidence, "memory_effects", (call_effect,))
    object.__setattr__(evidence, "callee_control_profile_key", callee_profile.stable_key())
    left.effect_summary.effects = [
        StoreEffect(
            location,
            call_value,
            [],
            1,
            provenance=_call_derived_store_provenance(
                evidence.pcode_op_ref,
                evidence.target_ref,
                0,
            ),
        )
    ]
    right.effect_summary.effects = [region_effect]
    object.__setattr__(
        right.effect_summary.function_control_effect_profile,
        "store_count",
        1,
    )
    return left, right, _phase2_manifest_with_certificate(left, right)


def test_typed_call_to_region_proves_guard_input_and_output_relations():
    pytest.importorskip("z3")
    left, right, manifest = _call_to_region_proof_inputs()
    checker = EquivalenceChecker(timeout=5, enable_rewrite=False)

    production = produce_pure_direct_call_proofs(
        manifest,
        left,
        right,
        solver_runner=checker.solver_runner,
        timeout_seconds=5,
    )

    assert [item.record.proof_stage for item in production.artifacts] == [
        "guard_relation",
        "argument_relation",
        "return_relation",
    ]
    assert all(item.record.status == "proven" for item in production.artifacts)
    assert all(item.query_authority is not None for item in production.artifacts)
    assert all(
        item.query_authority.stage == item.record.proof_stage
        and item.query_authority.obligation_id == item.record.obligation_id
        and item.query_authority.observation_contract_id
        == item.record.observation_contract_id
        for item in production.artifacts
    )


def test_v2_typed_call_producer_uses_pinned_execution_and_live_q_open_assignment():
    pytest.importorskip("z3")
    install_execution_authority_signing_key(
        "v2-call-test-deployment-key", b"v" * 32
    )
    activate_execution_authority_deployment(
        ExecutionAuthorityDeploymentPolicy(
            "v2-call-test-policy", 1, "test-owner", "test-key-source",
            "v2-call-test-deployment-key", (), 3600, "test-revocation",
        )
    )
    left, right, manifest = _call_to_region_proof_inputs()
    obligation_id = manifest["phase2_direct_call_eligibility"][0]["obligation_id"]
    stage_kinds = {
        "guard_relation": "call_guard_relation",
        "argument_relation": "call_argument_relation",
        "return_relation": "call_return_relation",
    }
    encoder = CallEffectPilotEncoder()
    composite = CompositeProductionSignalEncoder({
        CallEffectBlockerProductionSignal: encoder,
    })
    connector = ProductionDualWritePilotConnector(
        ShadowLifecycleReducer(
            reason_registry=CALL_EFFECT_REASON_REGISTRY,
            recovery_registry=CALL_EFFECT_RECOVERY_REGISTRY,
        ),
        domain_signal_encoder=composite,
    )
    session = connector.begin({"case": "v2-call-live-prefix"})
    with production_signal_scope(session):
        legacy = produce_pure_direct_call_proofs(
            manifest,
            left,
            right,
            solver_runner=EquivalenceChecker(timeout=5, enable_rewrite=False).solver_runner,
            timeout_seconds=5,
        )
        assert len(legacy.v2_blocker_signals) == 1
        context = composite.build_call_effect_execution_context(
            session,
            legacy.v2_blocker_signals,
            CALL_EFFECT_PRODUCTION_STAGE_REGISTRY,
        )
    projection = context.lifecycle_projection
    registry = CALL_EFFECT_PRODUCTION_STAGE_REGISTRY
    row_map = dict(context.q_open_assignments)
    production = produce_v2_pure_direct_call_proofs(
        manifest, left, right, execution_context=context, timeout_seconds=5
    )
    assert len(production.artifacts) == 3
    for artifact in production.artifacts:
        assert artifact.v2_execution_receipt is not None
        proof_kind = stage_kinds[artifact.record.proof_stage]
        assert CALL_EFFECT_ARTIFACT_CAPABILITY_REGISTRY.authorize_completion(
            artifact,
            reason_id="pure_call_semantics_unproven",
            identity_scope=IdentityScope.RELATIONAL,
            proof_kind=proof_kind,
            validation_context={
                "producer_stage_registry": registry,
                "lifecycle_projection": projection,
            },
        ) == "internal-parallel-solver-runner"
    guard_authority = next(
        item.query_authority for item in production.artifacts
        if item.record.proof_stage == "guard_relation"
    )
    argument_row = row_map[(obligation_id, "argument_relation")]
    final_projection = VerifiedLifecycleProjection.seal(
        result_occurrence_id=projection.result_occurrence_id,
        snapshot_digest=projection.snapshot_digest,
        c_active_base=projection.c_active_base,
        q_open_base=projection.q_open_base,
        blocker_eligibility_base=projection.blocker_eligibility_base,
        satisfaction_projection=projection.satisfaction_projection,
    )
    with pytest.raises(TypeError, match="PREFIX lifecycle authority"):
        issue_call_effect_requirement_assignment(
            projection=final_projection,
            q_open_row=argument_row,
            query_authority=guard_authority,
        )
    with pytest.raises(ValueError, match="semantic target"):
        issue_call_effect_requirement_assignment(
            projection=projection,
            q_open_row=argument_row,
            query_authority=guard_authority,
        )

    guard_row = row_map[(obligation_id, "guard_relation")]
    ambiguous_context = V2CallEffectExecutionContext(
        registry,
        projection,
        projection.result_occurrence_id,
        (
            *tuple(row_map.items()),
            ((obligation_id, "guard_relation"), guard_row),
        ),
    )
    with pytest.raises(ValueError, match="ambiguous live Q_open assignments"):
        ambiguous_context.membership_for(guard_authority)
    assert ambiguous_context.q_open_assignments.count(
        ((obligation_id, "guard_relation"), guard_row)
    ) == 2


def test_v2_call_effect_pilot_completes_stages_but_keeps_semantic_arms_open():
    pytest.importorskip("z3")
    install_execution_authority_signing_key(
        "v2-call-pilot-chain-key", b"c" * 32
    )
    activate_execution_authority_deployment(
        ExecutionAuthorityDeploymentPolicy(
            "v2-call-pilot-chain-policy", 1, "test-owner", "test-source",
            "v2-call-pilot-chain-key", (), 3600, "test-revocation",
        )
    )
    encoder = CallEffectPilotEncoder()
    composite = CompositeProductionSignalEncoder({
        CallEffectBlockerProductionSignal: encoder,
        CallEffectProofBatchProductionSignal: encoder,
    })
    connector = ProductionDualWritePilotConnector(
        ShadowLifecycleReducer(
            reason_registry=CALL_EFFECT_REASON_REGISTRY,
            recovery_registry=CALL_EFFECT_RECOVERY_REGISTRY,
        ),
        domain_signal_encoder=composite,
    )
    session = connector.begin({"case": "v2-call-stage-chain"})
    left, right, manifest = _call_to_region_proof_inputs()
    with production_signal_scope(session):
        legacy = produce_pure_direct_call_proofs(
            manifest,
            left,
            right,
            solver_runner=EquivalenceChecker(timeout=5, enable_rewrite=False).solver_runner,
            timeout_seconds=5,
        )
        assert len(legacy.v2_blocker_signals) == 1
        prefix = session.preview_lifecycle_projection()
        assert len(prefix.c_active_base) == 1
        assert len(prefix.q_open_base) == 5
        assert session.emit_domain_signal(legacy.v2_blocker_signals[0]) == 0
        with pytest.raises(TypeError, match="FINAL lifecycle authority"):
            FinalizationAuthority(session.identity.result_occurrence_id, prefix)
        with pytest.raises(TypeError, match="FINAL lifecycle authorities"):
            join_outcome_relations(
                CensusManifest(
                    "call-prefix-negative", CensusMode.V2_CANONICAL,
                    "test-head", "test-config", (),
                ),
                (),
                (prefix,),
            )
        context = composite.build_call_effect_execution_context(
            session,
            legacy.v2_blocker_signals,
            CALL_EFFECT_PRODUCTION_STAGE_REGISTRY,
        )
        v2 = produce_v2_pure_direct_call_proofs(
            manifest,
            left,
            right,
            execution_context=context,
            timeout_seconds=5,
        )
        assert [artifact.record.proof_stage for artifact in v2.artifacts] == [
            "guard_relation", "argument_relation", "return_relation",
        ]
        batch = CallEffectProofBatchProductionSignal(
            legacy.v2_blocker_signals[0], v2.artifacts
        )
        assert batch.producer_id == "call-effect-proof-batch-v2"
        assert batch._phase7_signal_authority()["producer_id"] == (
            "call-effect-proof-batch-v2"
        )
        with pytest.raises(
            ValueError, match="proof batch producer is not sealed"
        ):
            CallEffectProofBatchProductionSignal(
                legacy.v2_blocker_signals[0],
                v2.artifacts,
                producer_id="internal_typed_pure_direct_call_stage_producer",
            )
        emitted = session.emit_domain_signal(batch)
        assert emitted == 3
    completed = session.preview_lifecycle_projection()
    assert len(completed.c_active_base) == 1
    assert {
        row.proof_kind for row in completed.q_open_base
    } == {
        "inline_region_semantic_proof",
        "callee_summary_semantic_proof",
    }
    evidence = connector.finish(
        session,
        SimpleNamespace(
            error_message=None,
            is_equivalent=None,
            failure_status=None,
            failure_message=None,
            is_timeout=lambda: False,
        ),
        case_id="v2-call-stage-chain",
    )
    assert evidence.pilot_result.candidate.decision_receipt.outcome.value == "UNKNOWN"
    assert len(evidence.execution_authority_evidence_bundles) == 1
    evidence_body = evidence.to_dict()["execution_authority_evidence"][0]
    assert evidence_body["startup_receipt"]["startup_mode"] == "fail_closed"
    assert len(evidence_body["census"]["events"]) == 3
    assert evidence_body["terminal_selection"] is None


def test_v2_call_effect_ambiguous_q_open_refuses_before_execution_and_finishes_unknown():
    pytest.importorskip("z3")
    install_execution_authority_signing_key(
        "v2-call-ambiguous-key", b"a" * 32
    )
    activate_execution_authority_deployment(
        ExecutionAuthorityDeploymentPolicy(
            "v2-call-ambiguous-policy", 1, "test-owner", "test-source",
            "v2-call-ambiguous-key", (), 3600, "test-revocation",
        )
    )
    encoder = CallEffectPilotEncoder()
    composite = CompositeProductionSignalEncoder({
        CallEffectBlockerProductionSignal: encoder,
    })
    connector = ProductionDualWritePilotConnector(
        ShadowLifecycleReducer(
            reason_registry=CALL_EFFECT_REASON_REGISTRY,
            recovery_registry=CALL_EFFECT_RECOVERY_REGISTRY,
        ),
        domain_signal_encoder=composite,
    )
    session = connector.begin({"case": "v2-call-ambiguous-q-open"})
    left, right, manifest = _call_to_region_proof_inputs()
    with production_signal_scope(session):
        legacy = produce_pure_direct_call_proofs(
            manifest,
            left,
            right,
            solver_runner=EquivalenceChecker(timeout=5, enable_rewrite=False).solver_runner,
            timeout_seconds=5,
        )
    context = composite.build_call_effect_execution_context(
        session,
        legacy.v2_blocker_signals,
        CALL_EFFECT_PRODUCTION_STAGE_REGISTRY,
    )
    guard_authority = next(
        artifact.query_authority for artifact in legacy.artifacts
        if artifact.record.proof_stage == "guard_relation"
    )
    guard_key = (guard_authority.obligation_id, guard_authority.stage)
    guard_row = dict(context.q_open_assignments)[guard_key]
    ambiguous = V2CallEffectExecutionContext(
        CALL_EFFECT_PRODUCTION_STAGE_REGISTRY,
        context.lifecycle_projection,
        context.result_occurrence_id,
        (*context.q_open_assignments, (guard_key, guard_row)),
        context.execution_refusal_sink,
    )
    with pytest.raises(ValueError, match="ambiguous live Q_open assignments"):
        ambiguous.membership_for(guard_authority)
    evidence = connector.finish(
        session,
        SimpleNamespace(
            error_message=None,
            is_equivalent=None,
            failure_status=None,
            failure_message=None,
            is_timeout=lambda: False,
        ),
        case_id="v2-call-ambiguous-q-open",
    )
    assert evidence.pilot_result.candidate.decision_receipt.outcome.value == "UNKNOWN"
    assert len(evidence.pilot_result.reduction.projection.c_active_base) == 1
    assert len(evidence.pilot_result.reduction.projection.q_open_base) == 5
    assert evidence.execution_authority_evidence_bundles == ()
    assert len(evidence.execution_refusal_receipts) == 1
    assert evidence.to_dict()["execution_refusal_receipts"][0][
        "refusal_kind"
    ] == "ambiguous_live_q_open_assignment"


def test_v2_call_effect_persists_nonselected_timeout_history(monkeypatch):
    pytest.importorskip("z3")
    install_execution_authority_signing_key(
        "v2-call-history-key", b"h" * 32
    )
    activate_execution_authority_deployment(
        ExecutionAuthorityDeploymentPolicy(
            "v2-call-history-policy", 1, "test-owner", "test-source",
            "v2-call-history-key", (), 3600, "test-revocation",
        )
    )
    import scripts.function_tracer_pcode.authority.lifecycle.execution_authority as authority_module

    monkeypatch.setattr(
        authority_module,
        "_PINNED_PARALLEL_RUN_IMPL",
        lambda _runner, _query, timeout: ParallelResult(results=[
            SolverResult("z3", SolverStatus.TIMEOUT, elapsed_time=timeout),
            SolverResult("z3", SolverStatus.UNSAT, elapsed_time=0.001),
        ]),
    )
    encoder = CallEffectPilotEncoder()
    composite = CompositeProductionSignalEncoder({
        CallEffectBlockerProductionSignal: encoder,
        CallEffectProofBatchProductionSignal: encoder,
    })
    connector = ProductionDualWritePilotConnector(
        ShadowLifecycleReducer(
            reason_registry=CALL_EFFECT_REASON_REGISTRY,
            recovery_registry=CALL_EFFECT_RECOVERY_REGISTRY,
        ),
        domain_signal_encoder=composite,
    )
    session = connector.begin({"case": "v2-call-nonselected-timeout-history"})
    left, right, manifest = _call_to_region_proof_inputs()
    with production_signal_scope(session):
        legacy = produce_pure_direct_call_proofs(
            manifest,
            left,
            right,
            solver_runner=EquivalenceChecker(timeout=5, enable_rewrite=False).solver_runner,
            timeout_seconds=5,
        )
        context = composite.build_call_effect_execution_context(
            session,
            legacy.v2_blocker_signals,
            CALL_EFFECT_PRODUCTION_STAGE_REGISTRY,
        )
        v2 = produce_v2_pure_direct_call_proofs(
            manifest, left, right, execution_context=context, timeout_seconds=5
        )
        assert all(len(artifact.v2_execution_receipts) == 2 for artifact in v2.artifacts)
        assert session.emit_domain_signal(CallEffectProofBatchProductionSignal(
            legacy.v2_blocker_signals[0], v2.artifacts
        )) == 6
    evidence = connector.finish(
        session,
        SimpleNamespace(
            error_message=None,
            is_equivalent=None,
            failure_status=None,
            failure_message=None,
            is_timeout=lambda: False,
        ),
        case_id="v2-call-nonselected-timeout-history",
    )
    assert evidence.pilot_result.observed_nonterminal_timeout_event_count == 3
    assert evidence.pilot_result.terminal_timeout_receipt_count == 0
    body = evidence.to_dict()["execution_authority_evidence"][0]
    assert len(body["census"]["events"]) == 6
    assert len(body["observed_stream_receipt_digests"]) == 3
    assert body["terminal_selection"] is None


def test_v2_call_effect_live_solver_timeout_finalizes_as_timeout(monkeypatch):
    pytest.importorskip("z3")
    install_execution_authority_signing_key(
        "v2-call-terminal-timeout-key", b"t" * 32
    )
    activate_execution_authority_deployment(
        ExecutionAuthorityDeploymentPolicy(
            "v2-call-terminal-timeout-policy", 1, "test-owner", "test-source",
            "v2-call-terminal-timeout-key", (), 3600, "test-revocation",
        )
    )
    import scripts.function_tracer_pcode.authority.lifecycle.execution_authority as authority_module

    monkeypatch.setattr(
        authority_module,
        "_PINNED_PARALLEL_RUN_IMPL",
        lambda _runner, _query, timeout: ParallelResult(results=[
            SolverResult("z3", SolverStatus.TIMEOUT, elapsed_time=timeout),
        ]),
    )
    encoder = CallEffectPilotEncoder()
    composite = CompositeProductionSignalEncoder({
        CallEffectBlockerProductionSignal: encoder,
        CallEffectProofBatchProductionSignal: encoder,
    })
    connector = ProductionDualWritePilotConnector(
        ShadowLifecycleReducer(
            reason_registry=CALL_EFFECT_REASON_REGISTRY,
            recovery_registry=CALL_EFFECT_RECOVERY_REGISTRY,
        ),
        domain_signal_encoder=composite,
    )
    session = connector.begin({"case": "v2-call-terminal-timeout"})
    left, right, manifest = _call_to_region_proof_inputs()
    with production_signal_scope(session):
        legacy = produce_pure_direct_call_proofs(
            manifest,
            left,
            right,
            solver_runner=EquivalenceChecker(timeout=5, enable_rewrite=False).solver_runner,
            timeout_seconds=5,
        )
        context = composite.build_call_effect_execution_context(
            session,
            legacy.v2_blocker_signals,
            CALL_EFFECT_PRODUCTION_STAGE_REGISTRY,
        )
        v2 = produce_v2_pure_direct_call_proofs(
            manifest, left, right, execution_context=context, timeout_seconds=5
        )
        assert [artifact.record.solver_result for artifact in v2.artifacts] == ["timeout"]
        assert session.emit_domain_signal(CallEffectProofBatchProductionSignal(
            legacy.v2_blocker_signals[0], v2.artifacts
        )) == 1
    evidence = connector.finish(
        session,
        SimpleNamespace(
            error_message=None,
            is_equivalent=None,
            failure_status=None,
            failure_message=None,
            is_timeout=lambda: False,
        ),
        case_id="v2-call-terminal-timeout",
    )
    assert evidence.pilot_result.candidate.decision_receipt.outcome.value == "TIMEOUT"
    assert evidence.pilot_result.terminal_timeout_receipt_count == 1
    assert evidence.pilot_result.observed_nonterminal_timeout_event_count == 0
    body = evidence.to_dict()["execution_authority_evidence"][0]
    assert len(body["census"]["events"]) == 1
    assert body["terminal_selection"] is not None
    assert body["terminal_selection"]["proof_requirement_id"] in {
        row.proof_requirement_id
        for row in evidence.pilot_result.reduction.projection.q_open_base
    }
    rematerialized = SolverExecutionEvidenceBundle.from_persisted(
        json.loads(json.dumps(body)),
        registry=CALL_EFFECT_PRODUCTION_STAGE_REGISTRY,
    )
    assert rematerialized.evidence_digest == body["evidence_digest"]


def test_v2_call_effect_partial_stage_prefix_is_not_replayed(monkeypatch):
    pytest.importorskip("z3")
    install_execution_authority_signing_key(
        "v2-call-partial-prefix-key", b"p" * 32
    )
    activate_execution_authority_deployment(
        ExecutionAuthorityDeploymentPolicy(
            "v2-call-partial-prefix-policy",
            1,
            "test-owner",
            "test-source",
            "v2-call-partial-prefix-key",
            (),
            3600,
            "test-revocation",
        )
    )
    import scripts.function_tracer_pcode.authority.lifecycle.execution_authority as authority_module

    monkeypatch.setattr(
        authority_module,
        "_PINNED_PARALLEL_RUN_IMPL",
        lambda _runner, _query, timeout: ParallelResult(results=[
            SolverResult("z3", SolverStatus.UNSAT, elapsed_time=0.001),
        ]),
    )
    encoder = CallEffectPilotEncoder()
    composite = CompositeProductionSignalEncoder({
        CallEffectBlockerProductionSignal: encoder,
        CallEffectProofBatchProductionSignal: encoder,
    })
    connector = ProductionDualWritePilotConnector(
        ShadowLifecycleReducer(
            reason_registry=CALL_EFFECT_REASON_REGISTRY,
            recovery_registry=CALL_EFFECT_RECOVERY_REGISTRY,
        ),
        domain_signal_encoder=composite,
    )
    session = connector.begin({"case": "v2-call-partial-prefix"})
    left, right, manifest = _call_to_region_proof_inputs()
    with production_signal_scope(session):
        legacy = produce_pure_direct_call_proofs(
            manifest,
            left,
            right,
            solver_runner=EquivalenceChecker(
                timeout=5,
                enable_rewrite=False,
            ).solver_runner,
            timeout_seconds=5,
        )
        context = composite.build_call_effect_execution_context(
            session,
            legacy.v2_blocker_signals,
            CALL_EFFECT_PRODUCTION_STAGE_REGISTRY,
        )
        v2 = produce_v2_pure_direct_call_proofs(
            manifest,
            left,
            right,
            execution_context=context,
            timeout_seconds=5,
        )
        assert [artifact.record.proof_stage for artifact in v2.artifacts] == [
            "guard_relation",
            "argument_relation",
            "return_relation",
        ]
        assert session.emit_domain_signal(CallEffectProofBatchProductionSignal(
            legacy.v2_blocker_signals[0],
            v2.artifacts[:2],
        )) == 2
        assert composite.build_call_effect_execution_context(
            session,
            legacy.v2_blocker_signals,
            CALL_EFFECT_PRODUCTION_STAGE_REGISTRY,
        ) is None
    evidence = connector.finish(
        session,
        SimpleNamespace(
            error_message=None,
            is_equivalent=None,
            failure_status=None,
            failure_message=None,
            is_timeout=lambda: False,
        ),
        case_id="v2-call-partial-prefix",
    )
    assert evidence.pilot_result.candidate.decision_receipt.outcome.value == "UNKNOWN"
    open_proof_kinds = {
        row.proof_kind
        for row in evidence.pilot_result.reduction.projection.q_open_base
    }
    assert "call_return_relation" in open_proof_kinds
    assert "call_guard_relation" not in open_proof_kinds
    assert "call_argument_relation" not in open_proof_kinds


def test_v2_call_effect_two_identical_runs_get_distinct_result_occurrences(monkeypatch):
    pytest.importorskip("z3")
    install_execution_authority_signing_key("v2-call-repeat-key", b"r" * 32)
    activate_execution_authority_deployment(ExecutionAuthorityDeploymentPolicy(
        "v2-call-repeat-policy", 1, "test-owner", "test-source",
        "v2-call-repeat-key", (), 3600, "test-revocation",
    ))
    import scripts.function_tracer_pcode.authority.lifecycle.execution_authority as authority_module

    monkeypatch.setattr(
        authority_module,
        "_PINNED_PARALLEL_RUN_IMPL",
        lambda _runner, _query, timeout: ParallelResult(results=[
            SolverResult("z3", SolverStatus.UNSAT, elapsed_time=0.001),
        ]),
    )
    encoder = CallEffectPilotEncoder()
    composite = CompositeProductionSignalEncoder({
        CallEffectBlockerProductionSignal: encoder,
        CallEffectProofBatchProductionSignal: encoder,
    })
    connector = ProductionDualWritePilotConnector(
        ShadowLifecycleReducer(
            reason_registry=CALL_EFFECT_REASON_REGISTRY,
            recovery_registry=CALL_EFFECT_RECOVERY_REGISTRY,
        ),
        domain_signal_encoder=composite,
    )
    left, right, manifest = _call_to_region_proof_inputs()
    evidences = []
    for _ in range(2):
        session = connector.begin({"case": "v2-call-identical-repeat"})
        with production_signal_scope(session):
            legacy = produce_pure_direct_call_proofs(
                manifest, left, right,
                solver_runner=EquivalenceChecker(timeout=5, enable_rewrite=False).solver_runner,
                timeout_seconds=5,
            )
            context = composite.build_call_effect_execution_context(
                session, legacy.v2_blocker_signals,
                CALL_EFFECT_PRODUCTION_STAGE_REGISTRY,
            )
            v2 = produce_v2_pure_direct_call_proofs(
                manifest, left, right, execution_context=context, timeout_seconds=5
            )
            session.emit_domain_signal(CallEffectProofBatchProductionSignal(
                legacy.v2_blocker_signals[0], v2.artifacts
            ))
            repeated_context = composite.build_call_effect_execution_context(
                session, legacy.v2_blocker_signals,
                CALL_EFFECT_PRODUCTION_STAGE_REGISTRY,
            )
            assert repeated_context is None
        evidences.append(connector.finish(
            session,
            SimpleNamespace(
                error_message=None, is_equivalent=None, failure_status=None,
                failure_message=None, is_timeout=lambda: False,
            ),
            case_id="v2-call-identical-repeat",
        ))
    assert evidences[0].pilot_result.reduction.snapshot.result_occurrence_id != (
        evidences[1].pilot_result.reduction.snapshot.result_occurrence_id
    )
    assert (
        evidences[0].result_entry_occurrence_receipt.receipt_digest
        != evidences[1].result_entry_occurrence_receipt.receipt_digest
    )
    rematerialized_occurrence = SolverResultEntryOccurrenceReceipt.from_persisted(
        json.loads(json.dumps(
            evidences[0].to_dict()["result_entry_occurrence_receipt"]
        ))
    )
    assert rematerialized_occurrence.receipt_digest == (
        evidences[0].result_entry_occurrence_receipt.receipt_digest
    )
    assert all(
        len(evidence.execution_authority_evidence_bundles[0][1].census.events) == 3
        for evidence in evidences
    )


def test_v2_call_effect_post_execution_pre_batch_failure_still_seals_ledger(monkeypatch):
    pytest.importorskip("z3")
    install_execution_authority_signing_key("v2-call-prebatch-key", b"b" * 32)
    activate_execution_authority_deployment(ExecutionAuthorityDeploymentPolicy(
        "v2-call-prebatch-policy", 1, "test-owner", "test-source",
        "v2-call-prebatch-key", (), 3600, "test-revocation",
    ))
    import scripts.function_tracer_pcode.authority.lifecycle.execution_authority as authority_module

    monkeypatch.setattr(
        authority_module,
        "_PINNED_PARALLEL_RUN_IMPL",
        lambda _runner, _query, timeout: ParallelResult(results=[
            SolverResult("z3", SolverStatus.UNSAT, elapsed_time=0.001),
        ]),
    )
    encoder = CallEffectPilotEncoder()
    composite = CompositeProductionSignalEncoder({
        CallEffectBlockerProductionSignal: encoder,
        CallEffectProofBatchProductionSignal: encoder,
    })
    connector = ProductionDualWritePilotConnector(
        ShadowLifecycleReducer(
            reason_registry=CALL_EFFECT_REASON_REGISTRY,
            recovery_registry=CALL_EFFECT_RECOVERY_REGISTRY,
        ),
        domain_signal_encoder=composite,
    )
    session = connector.begin({"case": "v2-call-post-execution-pre-batch"})
    left, right, manifest = _call_to_region_proof_inputs()
    with production_signal_scope(session):
        legacy = produce_pure_direct_call_proofs(
            manifest, left, right,
            solver_runner=EquivalenceChecker(timeout=5, enable_rewrite=False).solver_runner,
            timeout_seconds=5,
        )
        context = composite.build_call_effect_execution_context(
            session, legacy.v2_blocker_signals,
            CALL_EFFECT_PRODUCTION_STAGE_REGISTRY,
        )
        v2 = produce_v2_pure_direct_call_proofs(
            manifest, left, right, execution_context=context, timeout_seconds=5
        )
        assert len(v2.artifacts) == 3
    assert PINNED_SOLVER_EXECUTION_ISSUER.has_open_result_ledger(
        CALL_EFFECT_PRODUCTION_STAGE_REGISTRY,
        session.identity.result_occurrence_id,
    )
    session.domain_signal_error_kinds.append("InjectedPostExecutionFailure")
    with pytest.raises(ValueError, match="domain signal encoding is incomplete"):
        connector.finish(
            session,
            SimpleNamespace(
                error_message=None, is_equivalent=None, failure_status=None,
                failure_message=None, is_timeout=lambda: False,
            ),
            case_id="v2-call-post-execution-pre-batch",
        )
    assert not PINNED_SOLVER_EXECUTION_ISSUER.has_open_result_ledger(
        CALL_EFFECT_PRODUCTION_STAGE_REGISTRY,
        session.identity.result_occurrence_id,
    )
    assert len(session.domain_signal_state["call_effect_v2"]["solver_census"].events) == 3


def test_ineligible_call_obligation_emits_typed_prerequisite_frontier():
    install_execution_authority_signing_key(
        "call-prerequisite-key", b"p" * 32
    )
    activate_execution_authority_deployment(ExecutionAuthorityDeploymentPolicy(
        "call-prerequisite-policy", 1, "test-owner", "test-source",
        "call-prerequisite-key", (), 3600, "test-revocation",
    ))
    encoder = CallEffectPilotEncoder()
    composite = CompositeProductionSignalEncoder({
        CallEffectBlockerProductionSignal: encoder,
        CallEffectPrerequisiteProductionSignal: encoder,
    })
    connector = ProductionDualWritePilotConnector(
        ShadowLifecycleReducer(
            reason_registry=CALL_EFFECT_REASON_REGISTRY,
            recovery_registry=CALL_EFFECT_RECOVERY_REGISTRY,
        ),
        domain_signal_encoder=composite,
    )
    left, right, manifest = _call_to_region_proof_inputs()
    manifest = deepcopy(manifest)
    manifest["phase2_direct_call_eligibility"][0]["status"] = "ineligible"
    manifest["phase2_direct_call_eligibility"][0]["blockers"] = [
        "phase2_requires_paired_call_sites"
    ]
    session = connector.begin({"case": "ineligible-call-prerequisite"})
    with production_signal_scope(session):
        production = produce_pure_direct_call_proofs(
            manifest, left, right,
            solver_runner=EquivalenceChecker(timeout=5, enable_rewrite=False).solver_runner,
            timeout_seconds=5,
        )
    projection = session.preview_lifecycle_projection()
    assert len(production.v2_prerequisite_signals) == 1
    assert {row.reason_id for row in projection.c_active_base} == {
        "callsite_correspondence_unproven"
    }
    assert len(projection.q_open_base) == 1


def test_totality_ineligible_call_obligation_emits_pure_semantics_frontier():
    install_execution_authority_signing_key(
        "call-totality-prerequisite-key", b"t" * 32
    )
    activate_execution_authority_deployment(ExecutionAuthorityDeploymentPolicy(
        "call-totality-prerequisite-policy", 1, "test-owner", "test-source",
        "call-totality-prerequisite-key", (), 3600, "test-revocation",
    ))
    encoder = CallEffectPilotEncoder()
    root = Path(__file__).resolve().parents[4]
    phase7_manifest = json.loads((root / (
        "artifacts/unknown_taxonomy_v2/phase7/producer-sites.json"
    )).read_text(encoding="utf-8"))
    from scripts.function_tracer_pcode.authority.sites.runtime import runtime_from_audited_manifest
    connector = ProductionDualWritePilotConnector(
        ShadowLifecycleReducer(
            reason_registry=CALL_EFFECT_REASON_REGISTRY,
            recovery_registry=CALL_EFFECT_RECOVERY_REGISTRY,
        ),
        domain_signal_encoder=CompositeProductionSignalEncoder({
            CallEffectBlockerProductionSignal: encoder,
            CallEffectPrerequisiteProductionSignal: encoder,
        }),
        phase7_runtime_factory=lambda identity: runtime_from_audited_manifest(
            phase7_manifest, identity
        ),
    )
    left, right, manifest = _call_to_region_proof_inputs()
    manifest = deepcopy(manifest)
    manifest["phase2_direct_call_eligibility"][0]["status"] = "ineligible"
    manifest["phase2_direct_call_eligibility"][0]["blockers"] = [
        "call_callee_not_total_trap_free_scalar",
        "inline_region_not_total_trap_free_scalar",
    ]
    session = connector.begin({"case": "ineligible-call-totality"})
    with production_signal_scope(session):
        production = produce_pure_direct_call_proofs(
            manifest, left, right,
            solver_runner=EquivalenceChecker(
                timeout=5, enable_rewrite=False
            ).solver_runner,
            timeout_seconds=5,
        )
    projection = session.preview_lifecycle_projection()
    assert len(production.v2_prerequisite_signals) == 1
    assert production.v2_prerequisite_signals[0].reason_id == (
        "pure_call_semantics_unproven"
    )
    assert {row.reason_id for row in projection.c_active_base} == {
        "pure_call_semantics_unproven"
    }
    assert len(projection.q_open_base) == 5


def test_ineligible_call_obligation_splits_blockers_by_sealed_reason():
    encoder = CallEffectPilotEncoder()
    connector = ProductionDualWritePilotConnector(
        ShadowLifecycleReducer(
            reason_registry=CALL_EFFECT_REASON_REGISTRY,
            recovery_registry=CALL_EFFECT_RECOVERY_REGISTRY,
        ),
        domain_signal_encoder=CompositeProductionSignalEncoder({
            CallEffectBlockerProductionSignal: encoder,
            CallEffectPrerequisiteProductionSignal: encoder,
        }),
    )
    left, right, manifest = _call_to_region_proof_inputs()
    manifest = deepcopy(manifest)
    manifest["phase2_direct_call_eligibility"][0]["status"] = "ineligible"
    manifest["phase2_direct_call_eligibility"][0]["blockers"] = [
        "call_callee_not_total_trap_free_scalar",
        "argument_relation_missing",
    ]
    session = connector.begin({"case": "split-call-prerequisites"})
    with production_signal_scope(session):
        production = produce_pure_direct_call_proofs(
            manifest, left, right,
            solver_runner=EquivalenceChecker(
                timeout=5, enable_rewrite=False
            ).solver_runner,
            timeout_seconds=5,
        )
    assert {
        signal.reason_id for signal in production.v2_prerequisite_signals
    } == {
        "abi_argument_relation_unproven",
        "pure_call_semantics_unproven",
    }
    projection = session.preview_lifecycle_projection()
    assert {row.reason_id for row in projection.c_active_base} == {
        "abi_argument_relation_unproven",
        "pure_call_semantics_unproven",
    }
    assert len(projection.q_open_base) == 6


def test_call_prerequisite_rejects_unknown_infrastructure_blocker_code():
    left, right, manifest = _call_to_region_proof_inputs()
    manifest = deepcopy(manifest)
    manifest["phase2_direct_call_eligibility"][0]["status"] = "ineligible"
    manifest["phase2_direct_call_eligibility"][0]["blockers"] = [
        "call_callee_not_total_trap_free_scalar",
        "new_unsealed_blocker"
    ]
    with pytest.raises(
        ValueError, match="unclassified Phase 2 call eligibility blocker"
    ):
        produce_pure_direct_call_proofs(
            manifest, left, right,
            solver_runner=EquivalenceChecker(
                timeout=5, enable_rewrite=False
            ).solver_runner,
            timeout_seconds=5,
        )


def test_call_effect_memory_requirement_is_derived_before_memory_artifact_exists():
    left, right, manifest = _call_to_region_memory_proof_inputs()
    timeout_runner = SimpleNamespace(run_parallel=lambda _query, timeout: ParallelResult(
        results=[SolverResult("test", SolverStatus.TIMEOUT, elapsed_time=timeout)]
    ))
    production = produce_pure_direct_call_proofs(
        manifest, left, right, solver_runner=timeout_runner, timeout_seconds=1
    )
    assert [artifact.record.proof_stage for artifact in production.artifacts] == [
        "guard_relation"
    ]
    assert len(production.v2_blocker_signals) == 1
    assert production.v2_blocker_signals[0].effect_stage_required is True


def test_typed_call_to_region_proves_ordered_scalar_store_relation():
    pytest.importorskip("z3")
    left, right, manifest = _call_to_region_memory_proof_inputs()
    checker = EquivalenceChecker(timeout=5, enable_rewrite=False)

    production = produce_pure_direct_call_proofs(
        manifest,
        left,
        right,
        solver_runner=checker.solver_runner,
        timeout_seconds=5,
    )

    assert [item.record.proof_stage for item in production.artifacts] == [
        "guard_relation",
        "argument_relation",
        "return_relation",
        "memory_relation",
        "caller_memory_relation",
    ]
    assert all(item.record.status == "proven" for item in production.artifacts)


def test_typed_call_to_region_compares_final_post_state_after_overwrite():
    pytest.importorskip("z3")
    left, right, _ = _call_to_region_proof_inputs()
    location = CanonicalLocation(
        base_ref=LocationBaseRef.parameter("x", index=0),
        offset=0,
        size=4,
    )
    evidence = left.effect_summary.call_site_effect_summary_evidence[0]
    call_effects = (
        StoreEffect(location, Expression.constant(1, size=4), [], 1),
        StoreEffect(location, Expression.constant(2, size=4), [], 2),
    )
    object.__setattr__(evidence, "memory_effect_count", 2)
    object.__setattr__(evidence, "memory_effects", call_effects)
    left.effect_summary.effects = [
        StoreEffect(
            effect.location,
            effect.value,
            list(effect.conditions),
            1,
            provenance=_call_derived_store_provenance(
                evidence.pcode_op_ref,
                evidence.target_ref,
                index,
            ),
        )
        for index, effect in enumerate(call_effects)
    ]
    region_store_ref = _pcode_ref(
        "right",
        0x3000,
        0x3018,
        mnemonic="STORE",
    )
    right.effect_summary.effects = [
        StoreEffect(
            location,
            Expression.constant(2, size=4),
            [],
            1,
            provenance=_local_store_provenance(region_store_ref),
        )
    ]
    object.__setattr__(
        right.effect_summary.function_control_effect_profile,
        "store_count",
        1,
    )
    manifest = _phase2_manifest_with_certificate(left, right)
    checker = EquivalenceChecker(timeout=5, enable_rewrite=False)

    production = produce_pure_direct_call_proofs(
        manifest,
        left,
        right,
        solver_runner=checker.solver_runner,
        timeout_seconds=5,
    )

    assert production.failure_causes == ()
    assert [item.record.proof_stage for item in production.artifacts] == [
        "guard_relation",
        "argument_relation",
        "return_relation",
        "memory_relation",
        "caller_memory_relation",
    ]
    assert all(item.record.status == "proven" for item in production.artifacts)


def test_typed_call_to_region_refutes_different_scalar_store_value():
    pytest.importorskip("z3")
    left, right, manifest = _call_to_region_memory_proof_inputs(
        region_value_delta=1
    )
    checker = EquivalenceChecker(timeout=5, enable_rewrite=False)

    production = produce_pure_direct_call_proofs(
        manifest,
        left,
        right,
        solver_runner=checker.solver_runner,
        timeout_seconds=5,
    )

    assert production.artifacts[-1].record.proof_stage == "memory_relation"
    assert production.artifacts[-1].record.status == "refuted"


def test_typed_call_to_region_refutes_different_inline_result():
    pytest.importorskip("z3")
    left, right, manifest = _call_to_region_proof_inputs()
    right.returns[0].value = Expression.binary_op(
        "INT_ADD",
        Expression.parameter("x", 0, size=4),
        Expression.constant(1, size=4),
    )
    manifest = _phase2_manifest_with_certificate(left, right)
    checker = EquivalenceChecker(timeout=5, enable_rewrite=False)

    production = produce_pure_direct_call_proofs(
        manifest,
        left,
        right,
        solver_runner=checker.solver_runner,
        timeout_seconds=5,
    )

    assert [item.record.status for item in production.artifacts] == [
        "proven",
        "proven",
        "refuted",
    ]


def test_typed_call_to_region_proves_explicit_signed_abi_width_bridge():
    pytest.importorskip("z3")
    left, right, _ = _call_to_region_proof_inputs()
    right.parameters[0]["is_signed"] = True
    wide_parameter = Expression.parameter("x", 0, size=8)
    condition = Condition(
        Expression.binary_op(
            "INT_SLESS", wide_parameter, Expression.constant(0, size=8)
        )
    )
    low_word = Expression.binary_op(
        "SUBPIECE", wide_parameter, Expression.constant(0, size=4)
    )
    low_word.size = 4
    right.returns[0].conditions = [condition]
    right.returns[0].value = low_word
    right.returns.append(
        ReturnInfo(
            address="0x3008",
            conditions=[condition.negate()],
            value=low_word,
        )
    )
    manifest = _phase2_manifest_with_certificate(left, right)
    checker = EquivalenceChecker(timeout=5, enable_rewrite=False)

    production = produce_pure_direct_call_proofs(
        manifest,
        left,
        right,
        solver_runner=checker.solver_runner,
        timeout_seconds=5,
    )

    assert [item.record.status for item in production.artifacts] == [
        "proven",
        "proven",
        "proven",
    ]


def test_typed_call_to_region_proves_signed_return_observation_width_bridge():
    pytest.importorskip("z3")
    left, right, _ = _call_to_region_proof_inputs()
    right.return_type = "long"
    right.comparison_surface = ComparisonSurface(
        kind="return_value",
        explicit_bit_width=64,
        type_name="long",
    )
    manifest = _phase2_manifest_with_certificate(left, right)
    checker = EquivalenceChecker(timeout=5, enable_rewrite=False)

    production = produce_pure_direct_call_proofs(
        manifest,
        left,
        right,
        solver_runner=checker.solver_runner,
        timeout_seconds=5,
    )

    assert [item.record.status for item in production.artifacts] == [
        "proven",
        "proven",
        "proven",
    ]
    payload = production.artifacts[-1].precondition_payload["return_width_relation"]
    assert payload == {
        "narrow_bits": 32,
        "wide_bits": 64,
        "wide_side": "right",
        "extension": "sign_extend",
        "proof_basis": "typed_region_return_producer_and_declared_signedness",
    }


def test_typed_call_to_region_rejects_potentially_trapping_inline_result():
    pytest.importorskip("z3")
    left, right, _ = _call_to_region_proof_inputs()
    parameter = Expression.parameter("x", 0, size=4)
    right.returns[0].value = Expression.binary_op(
        "INT_DIV", parameter, parameter
    )
    manifest = _phase2_manifest_with_certificate(left, right)
    checker = EquivalenceChecker(timeout=5, enable_rewrite=False)

    production = produce_pure_direct_call_proofs(
        manifest,
        left,
        right,
        solver_runner=checker.solver_runner,
        timeout_seconds=5,
    )

    assert [item.record.proof_stage for item in production.artifacts] == [
        "guard_relation",
        "argument_relation",
    ]
    assert any(
        "unsupported_call_region_return_expression" in cause
        for cause in production.failure_causes
    )


def test_typed_call_to_region_proofs_can_promote_equivalence():
    pytest.importorskip("z3")
    left, right, _ = _call_to_region_proof_inputs()

    result = EquivalenceChecker(
        timeout=5,
        enable_rewrite=False,
        enable_completed_recovery_proofs=True,
    ).check(left, right, "left", "right")

    assert result.is_equivalent is True
    assert result.unknown_reasons == []
    manifest = result.call_effect_shadow_manifest
    assert manifest["relational_obligations"][0]["relation_kind"] == "call_to_region"
    assert [
        item["proof_stage"] for item in manifest["solver_proof_records"]
    ] == ["guard_relation", "argument_relation", "return_relation"]
    assert manifest["phase2_discharge_gate"]["status"] == "proven"


def test_call_to_region_proof_cannot_clear_non_call_unsafety():
    pytest.importorskip("z3")
    left, right, _ = _call_to_region_proof_inputs()
    right.effect_summary.incomplete_reasons = (
        "effect_summary_path_coverage_incomplete",
    )

    result = EquivalenceChecker(
        timeout=5,
        enable_rewrite=False,
        enable_completed_recovery_proofs=True,
    ).check(left, right, "left", "right")

    assert result.is_equivalent is None
    manifest = result.call_effect_shadow_manifest
    assert manifest["solver_proof_records"] == []
    assert manifest["phase2_discharge_gate"]["status"] == "blocked"


def test_typed_argument_stage_refutes_one_off_argument_relation():
    pytest.importorskip("z3")
    left = _phase2_caller_analysis("B1", 1, 0x1000)
    right = _phase2_caller_analysis("B2", 2, 0x3000)
    manifest = _phase2_manifest_with_certificate(left, right)
    evidence = next(iter(right.effect_summary.call_argument_evidence.values()))
    first, second = evidence.arguments
    object.__setattr__(
        evidence,
        "arguments",
        (
            first,
            Expression.binary_op("INT_ADD", second, Expression.constant(1, size=4)),
        ),
    )
    checker = EquivalenceChecker(timeout=5, enable_rewrite=False)

    production = produce_pure_direct_call_proofs(
        manifest,
        left,
        right,
        solver_runner=checker.solver_runner,
        timeout_seconds=5,
    )

    assert [item.record.proof_stage for item in production.artifacts] == [
        "guard_relation",
        "argument_relation",
    ]
    assert production.artifacts[0].record.status == "proven"
    assert production.artifacts[1].record.status == "refuted"
    assert production.artifacts[1].record.solver_result == "sat"


def test_typed_guard_stage_refutes_different_call_reachability():
    pytest.importorskip("z3")
    left = _phase2_caller_analysis("B1", 1, 0x1000)
    right = _phase2_caller_analysis("B2", 2, 0x3000)
    manifest = _phase2_manifest_with_certificate(left, right)
    evidence = next(iter(right.effect_summary.call_argument_evidence.values()))
    first_argument = evidence.arguments[0]
    object.__setattr__(
        evidence,
        "path_conditions",
        ((Condition(Expression.binary_op(
            "INT_EQUAL",
            first_argument,
            Expression.constant(0, size=4),
        )),),),
    )
    checker = EquivalenceChecker(timeout=5, enable_rewrite=False)

    production = produce_pure_direct_call_proofs(
        manifest,
        left,
        right,
        solver_runner=checker.solver_runner,
        timeout_seconds=5,
    )

    assert len(production.artifacts) == 1
    assert production.artifacts[0].record.proof_stage == "guard_relation"
    assert production.artifacts[0].record.status == "refuted"
    assert production.artifacts[0].record.solver_result == "sat"


def test_typed_return_stage_refutes_different_pure_callee_result():
    pytest.importorskip("z3")
    left = _phase2_caller_analysis("B1", 1, 0x1000)
    right = _phase2_caller_analysis("B2", 2, 0x3000)
    manifest = _phase2_manifest_with_certificate(left, right)
    arguments = next(iter(right.effect_summary.call_argument_evidence.values())).arguments
    effect = right.effect_summary.call_site_effect_summary_evidence[0]
    object.__setattr__(
        effect,
        "return_partitions",
        (((), Expression.binary_op("INT_SUB", arguments[0], arguments[1])),),
    )
    checker = EquivalenceChecker(timeout=5, enable_rewrite=False)

    production = produce_pure_direct_call_proofs(
        manifest,
        left,
        right,
        solver_runner=checker.solver_runner,
        timeout_seconds=5,
    )

    assert [item.record.status for item in production.artifacts] == [
        "proven",
        "proven",
        "refuted",
    ]
    assert production.artifacts[-1].record.solver_result == "sat"


def test_typed_scalar_store_call_effects_can_promote_equivalence():
    pytest.importorskip("z3")
    left = _phase2_caller_analysis("B1", 1, 0x1000)
    right = _phase2_caller_analysis("B2", 2, 0x3000)
    _attach_scalar_store_callee_effect(left)
    _attach_scalar_store_callee_effect(right)

    result = EquivalenceChecker(
        timeout=5,
        enable_rewrite=False,
        enable_completed_recovery_proofs=True,
    ).check(left, right, "left", "right")

    assert result.is_equivalent is True
    assert [
        item["proof_stage"]
        for item in result.call_effect_shadow_manifest["solver_proof_records"]
    ] == [
        "guard_relation",
        "argument_relation",
        "return_relation",
        "memory_relation",
        "caller_memory_relation",
    ]


def test_typed_call_memory_relation_allows_disjoint_write_reordering():
    pytest.importorskip("z3")
    left = _phase2_caller_analysis("B1", 1, 0x1000)
    right = _phase2_caller_analysis("B2", 2, 0x3000)
    for analysis, specs in (
        (left, [(0, 1, 1), (4, 2, 2)]),
        (right, [(4, 2, 1), (0, 1, 2)]),
    ):
        evidence = analysis.effect_summary.call_site_effect_summary_evidence[0]
        memory_effects = tuple(
            StoreEffect(
                CanonicalLocation(
                    base_ref=LocationBaseRef.parameter("a", index=0),
                    offset=offset,
                    size=4,
                ),
                Expression.constant(value, size=4),
                [],
                order_key,
            )
            for offset, value, order_key in specs
        )
        object.__setattr__(evidence, "memory_effect_count", len(memory_effects))
        object.__setattr__(evidence, "memory_effects", memory_effects)
        analysis.effect_summary.effects = [
            StoreEffect(
                effect.location,
                effect.value,
                list(effect.conditions),
                10,
                provenance=_call_derived_store_provenance(
                    evidence.pcode_op_ref,
                    evidence.target_ref,
                    index,
                ),
            )
            for index, effect in enumerate(memory_effects)
        ]

    checker = EquivalenceChecker(
        timeout=5,
        enable_rewrite=False,
        enable_completed_recovery_proofs=True,
    )
    result = checker.check(left, right, "left", "right")

    assert result.is_equivalent is True
    records = result.call_effect_shadow_manifest["solver_proof_records"]
    assert [record["proof_stage"] for record in records] == [
        "guard_relation",
        "argument_relation",
        "return_relation",
        "memory_relation",
        "caller_memory_relation",
    ]
    memory_artifact = checker._last_internal_call_effect_artifacts[-2]
    assert memory_artifact.precondition_payload["memory_observation_policy"] == (
        "alias_aware_final_post_state"
    )
    assert memory_artifact.precondition_payload["left_partial_order_certificate"][
        "proven_disjoint_pairs"
    ] == ((0, 1),)


def test_typed_call_memory_relation_compares_final_post_state_after_overwrite():
    pytest.importorskip("z3")
    left = _phase2_caller_analysis("B1", 1, 0x1000)
    right = _phase2_caller_analysis("B2", 2, 0x3000)
    for analysis, specs in (
        (left, [(1, 1), (2, 2)]),
        (right, [(2, 1)]),
    ):
        evidence = analysis.effect_summary.call_site_effect_summary_evidence[0]
        location = CanonicalLocation(
            base_ref=LocationBaseRef.parameter("a", index=0),
            offset=0,
            size=4,
        )
        memory_effects = tuple(
            StoreEffect(
                location,
                Expression.constant(value, size=4),
                [],
                order_key,
            )
            for value, order_key in specs
        )
        object.__setattr__(evidence, "memory_effect_count", len(memory_effects))
        object.__setattr__(evidence, "memory_effects", memory_effects)
        analysis.effect_summary.effects = [
            StoreEffect(
                effect.location,
                effect.value,
                list(effect.conditions),
                10,
                provenance=_call_derived_store_provenance(
                    evidence.pcode_op_ref,
                    evidence.target_ref,
                    index,
                ),
            )
            for index, effect in enumerate(memory_effects)
        ]

    result = EquivalenceChecker(
        timeout=5,
        enable_rewrite=False,
        enable_completed_recovery_proofs=True,
    ).check(left, right, "left", "right")

    assert result.is_equivalent is True
    assert [
        record["proof_stage"]
        for record in result.call_effect_shadow_manifest["solver_proof_records"]
    ] == [
        "guard_relation",
        "argument_relation",
        "return_relation",
        "memory_relation",
        "caller_memory_relation",
    ]


def test_typed_call_memory_relation_uses_callee_cfg_not_address_layout():
    pytest.importorskip("z3")
    left = _phase2_caller_analysis("B1", 1, 0x1000)
    right = _phase2_caller_analysis("B2", 2, 0x3000)
    for analysis, specs, cfg_edges in (
        (
            left,
            [(1, 0x2200, 0x2204, 1), (2, 0x2100, 0x2104, 2)],
            [(1, 2)],
        ),
        (right, [(1, 0x4200, 0x4204, 1)], []),
    ):
        evidence = analysis.effect_summary.call_site_effect_summary_evidence[0]
        target_entry = int(evidence.target_ref.entry_offset)
        block_refs = {
            block_index: PcodeBlockRef(
                block_index=block_index,
                start_address_offset=block_start,
                binary_id=analysis.binary_id,
                function_entry_space="ram",
                function_entry_offset=target_entry,
            )
            for block_index, block_start, _, _ in specs
        }
        location = CanonicalLocation(
            base_ref=LocationBaseRef.parameter("a", index=0),
            offset=0,
            size=4,
        )
        callee_effects = []
        caller_effects = []
        for effect_index, (block_index, _, op_address, value) in enumerate(specs):
            nested_ref = _pcode_ref(
                analysis.binary_id,
                target_entry,
                op_address,
                mnemonic="STORE",
                block_index=block_index,
                seq_time=0,
            )
            callee_effects.append(
                StoreEffect(
                    location,
                    Expression.constant(value, size=4),
                    [],
                    op_address << 8,
                )
            )
            caller_effects.append(
                StoreEffect(
                    location,
                    Expression.constant(value, size=4),
                    [],
                    op_address << 8,
                    provenance=StoreEffectProvenance(
                        source_kind="call_derived",
                        producer_pcode_op_ref=evidence.pcode_op_ref,
                        producer_block_ref=_block_ref_for_pcode(
                            evidence.pcode_op_ref
                        ),
                        call_target_ref=evidence.target_ref,
                        callee_effect_index=effect_index,
                        nested_effect_provenance=StoreEffectProvenance(
                            source_kind="local_store",
                            producer_pcode_op_ref=nested_ref,
                            producer_block_ref=block_refs[block_index],
                        ),
                    ),
                )
            )
        object.__setattr__(evidence, "memory_effect_count", len(callee_effects))
        object.__setattr__(evidence, "memory_effects", tuple(callee_effects))
        object.__setattr__(
            evidence,
            "callee_cfg_edge_keys",
            tuple(
                (block_refs[source].stable_key(), block_refs[target].stable_key())
                for source, target in cfg_edges
            ),
        )
        analysis.effect_summary.effects = caller_effects

    result = EquivalenceChecker(
        timeout=5,
        enable_rewrite=False,
        enable_completed_recovery_proofs=True,
    ).check(left, right, "left", "right")

    assert result.is_equivalent is None
    memory_record = result.call_effect_shadow_manifest["solver_proof_records"][3]
    assert memory_record["proof_stage"] == "memory_relation"
    assert memory_record["status"] == "refuted"
    assert memory_record["solver_result"] == "sat"


def test_whole_caller_memory_relation_covers_call_derived_store_provenance():
    pytest.importorskip("z3")
    left = _phase2_caller_analysis("B1", 1, 0x1000)
    right = _phase2_caller_analysis("B2", 2, 0x3000)
    for analysis in (left, right):
        _attach_scalar_store_callee_effect(analysis)
        evidence = analysis.effect_summary.call_site_effect_summary_evidence[0]
        callee_effect = evidence.memory_effects[0]
        analysis.effect_summary.effects = [
            StoreEffect(
                location=callee_effect.location,
                value=callee_effect.value,
                conditions=list(callee_effect.conditions),
                order_key=10,
                provenance=_call_derived_store_provenance(
                    evidence.pcode_op_ref,
                    evidence.target_ref,
                    0,
                ),
            )
        ]

    result = EquivalenceChecker(
        timeout=5,
        enable_rewrite=False,
        enable_completed_recovery_proofs=True,
    ).check(left, right, "left", "right")

    manifest = result.call_effect_shadow_manifest
    assert result.is_equivalent is True
    assert [item["proof_stage"] for item in manifest["solver_proof_records"]] == [
        "guard_relation",
        "argument_relation",
        "return_relation",
        "memory_relation",
        "caller_memory_relation",
    ]
    caller_proof = manifest["solver_proof_records"][-1]
    assert caller_proof["status"] == "proven"
    assert caller_proof["solver_result"] == "unsat"


def test_whole_caller_memory_relation_rejects_missing_call_derived_store():
    pytest.importorskip("z3")
    left = _phase2_caller_analysis("B1", 1, 0x1000)
    right = _phase2_caller_analysis("B2", 2, 0x3000)
    for analysis in (left, right):
        _attach_scalar_store_callee_effect(analysis)
        analysis.effect_summary.effects = []

    result = EquivalenceChecker(
        timeout=5,
        enable_rewrite=False,
        enable_completed_recovery_proofs=True,
    ).check(left, right, "left", "right")

    manifest = result.call_effect_shadow_manifest
    assert result.is_equivalent is None
    assert manifest["proof_readiness"][0]["decision_eligible"] is False
    assert manifest["proof_readiness"][0]["missing_stages"] == [
        "memory_relation",
        "caller_memory_relation",
    ]
    assert manifest["phase2_discharge_gate"]["failure_cause"] == (
        "caller_memory_relation_not_proven"
    )
    assert any(
        "memory_effect_substitution_coverage_missing" in cause
        for cause in manifest["stage_specific_producer"]["failure_causes"]
    )


def test_typed_scalar_store_stage_refutes_different_write_value():
    pytest.importorskip("z3")
    left = _phase2_caller_analysis("B1", 1, 0x1000)
    right = _phase2_caller_analysis("B2", 2, 0x3000)
    _attach_scalar_store_callee_effect(left)
    _attach_scalar_store_callee_effect(right, value_delta=1)
    manifest = _phase2_manifest_with_certificate(left, right)
    checker = EquivalenceChecker(timeout=5, enable_rewrite=False)

    production = produce_pure_direct_call_proofs(
        manifest,
        left,
        right,
        solver_runner=checker.solver_runner,
        timeout_seconds=5,
    )

    assert [item.record.status for item in production.artifacts] == [
        "proven",
        "proven",
        "proven",
        "refuted",
    ]


def test_typed_scalar_store_stage_rejects_different_write_location():
    pytest.importorskip("z3")
    left = _phase2_caller_analysis("B1", 1, 0x1000)
    right = _phase2_caller_analysis("B2", 2, 0x3000)
    _attach_scalar_store_callee_effect(left)
    _attach_scalar_store_callee_effect(right, location_offset=4)
    manifest = _phase2_manifest_with_certificate(left, right)
    checker = EquivalenceChecker(timeout=5, enable_rewrite=False)

    production = produce_pure_direct_call_proofs(
        manifest,
        left,
        right,
        solver_runner=checker.solver_runner,
        timeout_seconds=5,
    )

    assert [item.record.proof_stage for item in production.artifacts] == [
        "guard_relation",
        "argument_relation",
        "return_relation",
    ]
    assert any(
        "memory_effect_location_relation_missing" in cause
        for cause in production.failure_causes
    )


def test_typed_return_stage_refutes_noncanonical_wide_high_bits():
    pytest.importorskip("z3")
    left = _phase2_caller_analysis("B1", 1, 0x1000)
    right = _phase2_caller_analysis("B2", 2, 0x3000)
    manifest = _phase2_manifest_with_certificate(left, right)
    effect = right.effect_summary.call_site_effect_summary_evidence[0]
    original = effect.return_partitions[0][1]
    widened = Expression.unary_op("INT_SEXT", original)
    widened.size = 8
    noncanonical = Expression.binary_op(
        "INT_OR",
        widened,
        Expression.constant(1 << 32, size=8),
    )
    object.__setattr__(effect, "return_semantic_bit_width", 64)
    object.__setattr__(effect, "return_signed", True)
    object.__setattr__(effect, "return_partitions", (((), noncanonical),))
    checker = EquivalenceChecker(timeout=5, enable_rewrite=False)

    production = produce_pure_direct_call_proofs(
        manifest,
        left,
        right,
        solver_runner=checker.solver_runner,
        timeout_seconds=5,
    )

    assert production.artifacts[-1].record.proof_stage == "return_relation"
    assert production.artifacts[-1].record.status == "refuted"
    assert production.artifacts[-1].record.solver_result == "sat"


@pytest.mark.parametrize("operator", ["INT_DIV", "INT_SDIV", "INT_REM", "INT_SREM"])
def test_typed_return_stage_rejects_potentially_trapping_integer_ops(operator):
    pytest.importorskip("z3")
    left = _phase2_caller_analysis("B1", 1, 0x1000)
    right = _phase2_caller_analysis("B2", 2, 0x3000)
    manifest = _phase2_manifest_with_certificate(left, right)
    arguments = next(iter(right.effect_summary.call_argument_evidence.values())).arguments
    effect = right.effect_summary.call_site_effect_summary_evidence[0]
    object.__setattr__(
        effect,
        "return_partitions",
        (((), Expression.binary_op(operator, arguments[0], arguments[1])),),
    )
    checker = EquivalenceChecker(timeout=5, enable_rewrite=False)

    production = produce_pure_direct_call_proofs(
        manifest,
        left,
        right,
        solver_runner=checker.solver_runner,
        timeout_seconds=5,
    )

    assert [item.record.proof_stage for item in production.artifacts] == [
        "guard_relation",
        "argument_relation",
    ]
    assert any("unsupported_return_expression" in item for item in production.failure_causes)
    apply_solver_proof_artifacts_to_manifest(
        manifest,
        production.artifacts,
    )
    assert manifest["proof_readiness"] == [
        {
            "obligation_id": manifest["relational_obligations"][0][
                "obligation_id"
            ],
            "decision_eligible": False,
            "completed_stages": ["guard_relation", "argument_relation"],
            "missing_stages": ["return_relation"],
            "invalid_stages": [],
            "blockers": ["required_solver_stages_missing"],
        }
    ]


@pytest.mark.parametrize("solver_status", [SolverStatus.UNKNOWN, SolverStatus.TIMEOUT])
def test_typed_stage_unknown_or_timeout_never_completes_chain(solver_status):
    left = _phase2_caller_analysis("B1", 1, 0x1000)
    right = _phase2_caller_analysis("B2", 2, 0x3000)
    manifest = _phase2_manifest_with_certificate(left, right)
    runner = SimpleNamespace(
        run_parallel=lambda _query, timeout: ParallelResult(
            results=[SolverResult("test", solver_status)]
        )
    )

    production = produce_pure_direct_call_proofs(
        manifest,
        left,
        right,
        solver_runner=runner,
        timeout_seconds=1,
    )

    assert len(production.artifacts) == 1
    assert production.artifacts[0].record.proof_stage == "guard_relation"
    assert production.artifacts[0].record.status == "inconclusive"
    assert production.artifacts[0].verification_failure() is None


def test_phase2_compatibility_hook_is_decision_neutral():
    checker = EquivalenceChecker(enable_rewrite=False)
    strategy_result = SimpleNamespace(is_equivalent=None, unknown_reasons=["keep"])
    manifest = {}

    checker._apply_phase2_relational_call_discharge(
        strategy_result,
        _phase2_caller_analysis("B1", 1, 0x1000),
        _phase2_caller_analysis("B2", 2, 0x3000),
        manifest,
    )

    assert strategy_result.is_equivalent is None
    assert strategy_result.unknown_reasons == ["keep"]
    assert manifest["phase2_discharge_gate"]["status"] == "blocked"
    assert manifest["phase2_discharge_gate"]["decision_effect"] == "blocks_equivalence"


def test_phase2_discharge_cannot_promote_even_with_fabricated_manifest_proofs():
    left = _phase2_caller_analysis("B1", 1, 0x1000)
    right = _phase2_caller_analysis("B2", 2, 0x3000)
    checker = EquivalenceChecker(timeout=1, enable_rewrite=False)
    manifest = build_call_effect_shadow_manifest(
        left,
        right,
        binary1_name="left",
        binary2_name="right",
    )
    checker._attach_structural_coverage_certificate(manifest)
    manifest["solver_proof_records"] = [
        {
            "proof_stage": stage,
            "status": "proven",
            "solver_result": "unsat",
            "query_text": "(assert false)",
        }
        for stage in manifest["phase2_direct_call_eligibility"][0][
            "required_solver_stages"
        ]
    ]
    manifest["proof_readiness"][0]["decision_eligible"] = True
    strategy_result = SimpleNamespace(
        is_equivalent=None,
        unknown_reasons=["keep"],
        total_pairs=1,
        unsat_pairs=1,
        sat_pairs=0,
        unknown_pairs=0,
        error_pairs=0,
    )

    checker._apply_phase2_relational_call_discharge(
        strategy_result,
        left,
        right,
        manifest,
    )

    assert strategy_result.is_equivalent is None
    assert strategy_result.unknown_reasons == ["keep"]
    assert manifest["phase2_discharge_gate"]["status"] == "blocked"


def test_structural_coverage_certificate_is_exact_and_decision_neutral():
    left = _phase2_caller_analysis("B1", 1, 0x1000)
    right = _phase2_caller_analysis("B2", 2, 0x3000)
    manifest = build_call_effect_shadow_manifest(
        left,
        right,
        binary1_name="left",
        binary2_name="right",
    )
    complete = build_structural_coverage_certificate(manifest)
    assert complete.status == "complete"
    assert complete.verification_failure() is None
    assert complete.to_dict()["decision_effect"] == "diagnostic_precondition_only"
    assert complete.exact_coverage_payload["left_fact_ids"] == manifest["coupling"][
        "left_fact_ids"
    ]

    complete.exact_coverage_payload["structural_coverage_complete"] = False
    assert complete.verification_failure() == "certificate_payload_status_mismatch"

    incomplete_manifest = build_call_effect_shadow_manifest(
        left,
        right,
        binary1_name="left",
        binary2_name="right",
    )
    incomplete_manifest["coupling"]["structural_coverage_complete"] = False
    incomplete = build_structural_coverage_certificate(incomplete_manifest)
    assert incomplete.status == "incomplete"
    assert "structural_endpoint_coverage_incomplete" in incomplete.failure_causes

    mismatched_manifest = build_call_effect_shadow_manifest(
        left,
        right,
        binary1_name="left",
        binary2_name="right",
    )
    mismatched_manifest["pcode_call_census_coverage"]["left"][
        "fact_pcode_op_keys"
    ] = []
    mismatched = build_structural_coverage_certificate(mismatched_manifest)
    assert mismatched.status == "incomplete"
    assert "left_pcode_census_fact_key_mismatch" in mismatched.failure_causes


def test_different_internal_callees_cannot_be_promoted_from_shape_candidate():
    left = _phase2_caller_analysis("B1", 1, 0x1000)
    right = _phase2_caller_analysis("B2", 2, 0x3000)
    right_evidence = next(iter(right.effect_summary.call_argument_evidence.values()))
    different = CallTargetRef.from_name(
        "different_leaf",
        program_id=2,
        entry_offset=0x9000,
    )
    object.__setattr__(right_evidence, "target_ref", different)
    object.__setattr__(right.effect_summary.call_site_effect_summary_evidence[0], "target_ref", different)

    result = EquivalenceChecker(
        timeout=5,
        enable_rewrite=False,
        enable_completed_recovery_proofs=False,
    ).check(left, right, "left", "right")

    assert result.is_equivalent is None
    manifest = result.call_effect_shadow_manifest
    assert manifest["mode"] == "typed_relational_call_effect_proof"
    assert manifest["relational_obligations"][0]["status"] == "pending"


def test_phase2_relational_discharge_rejects_caller_memory_effect():
    pytest.importorskip("z3")
    left = _phase2_caller_analysis("B1", 1, 0x1000)
    right = _phase2_caller_analysis("B2", 2, 0x3000)
    location = CanonicalLocation(
        base_ref=LocationBaseRef.parameter("a", index=0),
        offset=0,
        size=4,
    )
    left.effect_summary.effects = [
        StoreEffect(location, Expression.constant(1, size=4), [], 10)
    ]
    right.effect_summary.effects = [
        StoreEffect(location, Expression.constant(2, size=4), [], 10)
    ]

    result = EquivalenceChecker(
        timeout=5,
        enable_rewrite=False,
        enable_completed_recovery_proofs=True,
    ).check(left, right, "left", "right")

    assert result.is_equivalent is None
    manifest = result.call_effect_shadow_manifest
    assert manifest["mode"] == "typed_relational_call_effect_proof"
    assert manifest["proof_readiness"][0]["decision_eligible"] is False
    assert manifest["proof_readiness"][0]["missing_stages"] == [
        "caller_memory_relation"
    ]
    assert [item["proof_stage"] for item in manifest["solver_proof_records"]] == [
        "guard_relation",
        "argument_relation",
        "return_relation",
    ]
    assert manifest["phase2_discharge_gate"] == {
        "status": "blocked",
        "decision_effect": "blocks_equivalence",
        "failure_cause": "caller_memory_relation_not_proven",
        "caller_memory_effects": [
            {
                "side": "function1",
                "effect_count": 1,
                "explicit_store_count": 0,
                "call_derived_store_count": 0,
            },
            {
                "side": "function2",
                "effect_count": 1,
                "explicit_store_count": 0,
                "call_derived_store_count": 0,
            },
        ],
    }


@pytest.mark.parametrize("right_value", [1, 2])
def test_whole_caller_memory_relation_proves_or_refutes_complete_local_stores(
    right_value,
):
    pytest.importorskip("z3")
    left = _phase2_caller_analysis("B1", 1, 0x1000)
    right = _phase2_caller_analysis("B2", 2, 0x3000)
    location = CanonicalLocation(
        base_ref=LocationBaseRef.parameter("a", index=0),
        offset=0,
        size=4,
    )
    for analysis, value, address in (
        (left, 1, 0x1018),
        (right, right_value, 0x3018),
    ):
        profile = analysis.effect_summary.function_control_effect_profile
        object.__setattr__(profile, "store_count", 1)
        store_ref = _pcode_ref(
            analysis.binary_id,
            int(analysis.entry_point, 16),
            address,
            mnemonic="STORE",
        )
        analysis.effect_summary.effects = [
            StoreEffect(
                location,
                Expression.constant(value, size=4),
                [],
                10,
                provenance=_local_store_provenance(store_ref),
            )
        ]

    result = EquivalenceChecker(
        timeout=5,
        enable_rewrite=False,
        enable_completed_recovery_proofs=True,
    ).check(left, right, "left", "right")

    manifest = result.call_effect_shadow_manifest
    records = manifest["solver_proof_records"]
    assert [item["proof_stage"] for item in records] == [
        "guard_relation",
        "argument_relation",
        "return_relation",
        "caller_memory_relation",
    ]
    caller_record = records[-1]
    if right_value == 1:
        assert caller_record["status"] == "proven"
        assert caller_record["solver_result"] == "unsat"
        assert manifest["proof_readiness"][0]["decision_eligible"] is True
        assert manifest["phase2_discharge_gate"]["status"] == "proven"
        assert result.is_equivalent is True
    else:
        assert caller_record["status"] == "refuted"
        assert caller_record["solver_result"] == "sat"
        assert manifest["proof_readiness"][0]["decision_eligible"] is False
        assert manifest["phase2_discharge_gate"]["failure_cause"] == (
            "caller_memory_relation_not_proven"
        )
        assert result.is_equivalent is None


def _set_complete_local_caller_stores(analysis, specs):
    profile = analysis.effect_summary.function_control_effect_profile
    object.__setattr__(profile, "store_count", len(specs))
    entry = int(analysis.entry_point, 16)
    effects = []
    for ordinal, (parameter_index, offset, size, value, order_key) in enumerate(specs):
        effects.append(
            StoreEffect(
                CanonicalLocation(
                    base_ref=LocationBaseRef.parameter(
                        "a" if parameter_index == 0 else "b",
                        index=parameter_index,
                    ),
                    offset=offset,
                    size=size,
                ),
                Expression.constant(value, size=size),
                [],
                order_key,
                provenance=_local_store_provenance(
                    _pcode_ref(
                        analysis.binary_id,
                        entry,
                        entry + 0x30 + ordinal * 4,
                        mnemonic="STORE",
                        seq_time=ordinal,
                    ),
                ),
            )
        )
    analysis.effect_summary.effects = effects


def _set_cfg_local_caller_stores(analysis, specs, cfg_edges):
    profile = analysis.effect_summary.function_control_effect_profile
    object.__setattr__(profile, "store_count", len(specs))
    entry = int(analysis.entry_point, 16)
    block_refs = {
        block_index: PcodeBlockRef(
            block_index=block_index,
            start_address_offset=block_start,
            binary_id=analysis.binary_id,
            function_entry_space="ram",
            function_entry_offset=entry,
        )
        for block_index, block_start, _, _, _ in specs
    }
    object.__setattr__(
        profile,
        "region_cfg_edge_keys",
        tuple(
            (
                block_refs[source].stable_key(),
                block_refs[target].stable_key(),
            )
            for source, target in cfg_edges
        ),
    )
    effects = []
    for ordinal, (block_index, block_start, op_address, value, conditions) in enumerate(
        specs
    ):
        op_ref = _pcode_ref(
            analysis.binary_id,
            entry,
            op_address,
            mnemonic="STORE",
            block_index=block_index,
            seq_time=ordinal,
        )
        effects.append(
            StoreEffect(
                CanonicalLocation(
                    base_ref=LocationBaseRef.parameter("a", index=0),
                    offset=0,
                    size=4,
                ),
                Expression.constant(value, size=4),
                list(conditions),
                op_address << 8,
                provenance=StoreEffectProvenance(
                    source_kind="local_store",
                    producer_pcode_op_ref=op_ref,
                    producer_block_ref=block_refs[block_index],
                ),
            )
        )
    analysis.effect_summary.effects = effects


def test_whole_caller_final_post_state_allows_disjoint_write_reordering():
    pytest.importorskip("z3")
    left = _phase2_caller_analysis("B1", 1, 0x1000)
    right = _phase2_caller_analysis("B2", 2, 0x3000)
    _set_complete_local_caller_stores(
        left,
        [(0, 0, 4, 1, 10), (0, 4, 4, 2, 20)],
    )
    _set_complete_local_caller_stores(
        right,
        [(0, 4, 4, 2, 10), (0, 0, 4, 1, 20)],
    )

    checker = EquivalenceChecker(
        timeout=5,
        enable_rewrite=False,
        enable_completed_recovery_proofs=True,
    )
    result = checker.check(left, right, "left", "right")

    assert result.is_equivalent is True
    caller_artifact = checker._last_internal_call_effect_artifacts[-1]
    assert caller_artifact.record.proof_stage == "caller_memory_relation"
    assert caller_artifact.record.solver_result == "unsat"
    assert caller_artifact.precondition_payload["memory_observation_policy"] == (
        "complete_alias_aware_final_post_state"
    )
    assert caller_artifact.precondition_payload["left_partial_order_certificate"][
        "proven_disjoint_pairs"
    ] == ((0, 1),)


def test_whole_caller_cfg_order_overrides_reverse_address_layout():
    pytest.importorskip("z3")
    left = _phase2_caller_analysis("B1", 1, 0x1000)
    right = _phase2_caller_analysis("B2", 2, 0x3000)
    _set_cfg_local_caller_stores(
        left,
        [
            (1, 0x1200, 0x1204, 1, ()),
            (2, 0x1100, 0x1104, 2, ()),
        ],
        [(1, 2)],
    )
    _set_cfg_local_caller_stores(
        right,
        [(1, 0x3200, 0x3204, 1, ())],
        [],
    )

    result = EquivalenceChecker(
        timeout=5,
        enable_rewrite=False,
        enable_completed_recovery_proofs=True,
    ).check(left, right, "left", "right")

    assert result.is_equivalent is None
    caller_record = result.call_effect_shadow_manifest["solver_proof_records"][-1]
    assert caller_record["proof_stage"] == "caller_memory_relation"
    assert caller_record["status"] == "refuted"
    assert caller_record["solver_result"] == "sat"


def test_whole_caller_unordered_same_location_requires_guard_exclusivity_proof():
    pytest.importorskip("z3")
    left = _phase2_caller_analysis("B1", 1, 0x1000)
    right = _phase2_caller_analysis("B2", 2, 0x3000)
    for analysis, base in ((left, 0x1000), (right, 0x3000)):
        parameter = Expression.parameter("a", 0, data_type="int", size=4)
        zero = Expression.constant(0, size=4)
        equal = Condition(Expression.binary_op("INT_EQUAL", parameter, zero))
        not_equal = Condition(Expression.binary_op("INT_NOTEQUAL", parameter, zero))
        _set_cfg_local_caller_stores(
            analysis,
            [
                (1, base + 0x100, base + 0x104, 1, (equal,)),
                (2, base + 0x200, base + 0x204, 2, (not_equal,)),
                (0, base, base + 4, 3, (Condition(Expression.constant(0, 1)),)),
            ],
            [(0, 1), (0, 2)],
        )
        # The synthetic entry write is unreachable and exists only to carry both
        # outgoing CFG edges without introducing a third active final-state case.
        analysis.effect_summary.effects = analysis.effect_summary.effects[:2]
        object.__setattr__(
            analysis.effect_summary.function_control_effect_profile,
            "store_count",
            2,
        )

    checker = EquivalenceChecker(
        timeout=5,
        enable_rewrite=False,
        enable_completed_recovery_proofs=True,
    )
    result = checker.check(left, right, "left", "right")

    assert result.is_equivalent is True
    artifact = checker._last_internal_call_effect_artifacts[-1]
    assert artifact.precondition_payload["left_partial_order_certificate"][
        "guard_exclusivity_proof_pairs"
    ] == ((0, 1),)


def test_whole_caller_unordered_nonexclusive_writes_remain_unknown():
    pytest.importorskip("z3")
    left = _phase2_caller_analysis("B1", 1, 0x1000)
    right = _phase2_caller_analysis("B2", 2, 0x3000)
    for analysis, base in ((left, 0x1000), (right, 0x3000)):
        _set_cfg_local_caller_stores(
            analysis,
            [
                (1, base + 0x100, base + 0x104, 1, ()),
                (2, base + 0x200, base + 0x204, 2, ()),
                (0, base, base + 4, 3, ()),
            ],
            [(0, 1), (0, 2)],
        )
        analysis.effect_summary.effects = analysis.effect_summary.effects[:2]
        object.__setattr__(
            analysis.effect_summary.function_control_effect_profile,
            "store_count",
            2,
        )

    result = EquivalenceChecker(
        timeout=5,
        enable_rewrite=False,
        enable_completed_recovery_proofs=True,
    ).check(left, right, "left", "right")

    assert result.is_equivalent is None
    caller_record = result.call_effect_shadow_manifest["solver_proof_records"][-1]
    assert caller_record["proof_stage"] == "caller_memory_relation"
    assert caller_record["status"] == "refuted"
    assert caller_record["solver_result"] == "sat"


def test_whole_caller_final_post_state_eliminates_overwritten_write():
    pytest.importorskip("z3")
    left = _phase2_caller_analysis("B1", 1, 0x1000)
    right = _phase2_caller_analysis("B2", 2, 0x3000)
    _set_complete_local_caller_stores(
        left,
        [(0, 0, 4, 1, 10), (0, 0, 4, 2, 20)],
    )
    _set_complete_local_caller_stores(
        right,
        [(0, 0, 4, 2, 10)],
    )

    result = EquivalenceChecker(
        timeout=5,
        enable_rewrite=False,
        enable_completed_recovery_proofs=True,
    ).check(left, right, "left", "right")

    assert result.is_equivalent is True
    assert result.call_effect_shadow_manifest["phase2_discharge_gate"]["status"] == (
        "proven"
    )


def test_whole_caller_final_post_state_refutes_different_last_write():
    pytest.importorskip("z3")
    left = _phase2_caller_analysis("B1", 1, 0x1000)
    right = _phase2_caller_analysis("B2", 2, 0x3000)
    _set_complete_local_caller_stores(
        left,
        [(0, 0, 4, 1, 10), (0, 0, 4, 2, 20)],
    )
    _set_complete_local_caller_stores(
        right,
        [(0, 0, 4, 2, 10), (0, 0, 4, 1, 20)],
    )

    result = EquivalenceChecker(
        timeout=5,
        enable_rewrite=False,
        enable_completed_recovery_proofs=True,
    ).check(left, right, "left", "right")

    assert result.is_equivalent is None
    caller_record = result.call_effect_shadow_manifest["solver_proof_records"][-1]
    assert caller_record["proof_stage"] == "caller_memory_relation"
    assert caller_record["status"] == "refuted"
    assert caller_record["solver_result"] == "sat"


@pytest.mark.parametrize(
    ("specs", "failure_fragment"),
    [
        (
            [(0, 0, 4, 1, 10), (1, 0, 4, 2, 20)],
            "caller_memory_effect_alias_relation_missing",
        ),
        (
            [(0, 0, 4, 1, 10), (0, 2, 4, 2, 20)],
            "caller_memory_effect_partial_overlap_unsupported",
        ),
    ],
)
def test_whole_caller_final_post_state_keeps_unproven_aliases_unknown(
    specs,
    failure_fragment,
):
    pytest.importorskip("z3")
    left = _phase2_caller_analysis("B1", 1, 0x1000)
    right = _phase2_caller_analysis("B2", 2, 0x3000)
    _set_complete_local_caller_stores(left, specs)
    _set_complete_local_caller_stores(right, specs)

    result = EquivalenceChecker(
        timeout=5,
        enable_rewrite=False,
        enable_completed_recovery_proofs=True,
    ).check(left, right, "left", "right")

    assert result.is_equivalent is None
    manifest = result.call_effect_shadow_manifest
    assert manifest["phase2_discharge_gate"]["failure_cause"] == (
        "caller_memory_relation_not_proven"
    )
    assert any(
        failure_fragment in cause
        for cause in manifest["stage_specific_producer"]["failure_causes"]
    )


def test_external_thunk_target_is_not_a_phase2_internal_call_candidate():
    left = _phase2_caller_analysis("B1", 1, 0x1000)
    right = _phase2_caller_analysis("B2", 2, 0x3000)
    for analysis in (left, right):
        summary = analysis.effect_summary
        argument_evidence = next(iter(summary.call_argument_evidence.values()))
        external = CallTargetRef.from_name(
            "printf",
            program_id=argument_evidence.target_ref.program_id,
            entry_offset=argument_evidence.target_ref.entry_offset,
            is_thunk=True,
            thunked_is_external=True,
            thunked_library_name="libc",
        )
        object.__setattr__(argument_evidence, "target_ref", external)
        effect_evidence = summary.call_site_effect_summary_evidence[0]
        object.__setattr__(effect_evidence, "target_ref", external)

    manifest = build_call_effect_shadow_manifest(
        left,
        right,
        binary1_name="left",
        binary2_name="right",
    )

    assert manifest["summary"]["phase2_candidate_count"] == 0
    blockers = manifest["phase2_direct_call_eligibility"][0]["blockers"]
    assert "left_noninternal_call_target" in blockers
    assert "right_noninternal_call_target" in blockers
