import base64
import copy
from dataclasses import replace
import gzip
import hashlib
import json
from pathlib import Path
import pickle
from types import SimpleNamespace

import pytest

from scripts.function_tracer_pcode.equivalence.v2.contracts import IdentityScope, authority_digest
from scripts.function_tracer_pcode.equivalence.v2.execution_authority import ProducerStageRegistry
from scripts.function_tracer_pcode.equivalence.v2.loop_recurrence import (
    EXPECTED_LOOP_COMMON_REGISTRY_DIGEST,
    EXPECTED_LOOP_PRODUCER_STAGE_REGISTRY_DIGEST,
    LOOP_COMMON_EXECUTION_STAGE_REGISTRY,
    LOOP_PRODUCER_STAGE_REGISTRY_DIGEST,
    LOOP_PRODUCER_STAGE_SPECS,
    LOOP_REASON_REGISTRY,
    LOOP_RECOVERY_REGISTRY,
    LOOP_REASON_SPECS,
    LoopBlockerProductionSignal,
    LoopExactGuardPartitionCompletionAuthority,
    LoopExactGuardPartitionCompletionSignal,
    LoopExactTermRelationCompletionAuthority,
    LoopExactTermRelationCompletionSignal,
    LoopSolverQueryAuthority,
    LoopSolverExecutionContext,
    LoopSolverExecutionBatchSignal,
    LoopRecurrencePilotEncoder,
    RecurrenceRequirementBindingReceipt,
    RecurrenceValidationCompletionAuthority,
    RecurrenceValidationCompletionSignal,
    LoopSourceDisposition,
    LoopStageCapability,
    classify_effect_incomplete_reasons,
    classify_loop_fallback,
    classify_summary_blocker,
    loop_producer_registry_authority_dict,
    summary_signals_from_acceptance,
    validate_loop_registry_conservation,
    _issue_loop_solver_query_authority,
)
from scripts.function_tracer_pcode.equivalence.v2.execution_authority import (
    issue_loop_requirement_assignment,
)
from scripts.function_tracer_pcode.equivalence.v2.production_signals import (
    CompositeProductionSignalEncoder,
    production_signal_scope,
)
from scripts.function_tracer_pcode.equivalence.v2.stream import EventType
from scripts.function_tracer_pcode.model.analysis import FunctionReturnAnalysis
from scripts.function_tracer_pcode.model.recurrence_contracts import (
    QuarantinedRecurrenceProposal,
    RecurrenceSeedCore,
    function_recurrence_binding_digest,
)
from scripts.function_tracer_pcode.equivalence.checker import EquivalenceChecker
from scripts.function_tracer_pcode.equivalence.v2.call_effect import (
    CallEffectPilotEncoder,
    SummaryEffectPrerequisiteProductionSignal,
    summary_effect_prerequisite_signals_from_acceptance,
)
from scripts.function_tracer_pcode.equivalence.obligations.cache import (
    ValidatedUnaryArtifactEntry,
)
from scripts.function_tracer_pcode.equivalence.obligations.model import (
    UnaryArtifactDomain,
)
from scripts.function_tracer_pcode.equivalence.obligations.snapshot import (
    AnalysisSnapshot,
)
from scripts.function_tracer_pcode.equivalence.recurrence_promotion import (
    RecurrenceSidePromotion,
)


def test_loop_registry_full_and_common_digests_are_generated_from_same_rows():
    validate_loop_registry_conservation()
    assert authority_digest(loop_producer_registry_authority_dict()) == (
        EXPECTED_LOOP_PRODUCER_STAGE_REGISTRY_DIGEST
    )
    assert LOOP_PRODUCER_STAGE_REGISTRY_DIGEST == (
        EXPECTED_LOOP_PRODUCER_STAGE_REGISTRY_DIGEST
    )
    projected = ProducerStageRegistry(
        1, tuple(item.to_common_contract() for item in LOOP_PRODUCER_STAGE_SPECS)
    )
    assert projected.normalized_registry_digest == EXPECTED_LOOP_COMMON_REGISTRY_DIGEST
    assert (
        LOOP_COMMON_EXECUTION_STAGE_REGISTRY.normalized_registry_digest
        == EXPECTED_LOOP_COMMON_REGISTRY_DIGEST
    )
    assert tuple(item.terminal_priority for item in LOOP_PRODUCER_STAGE_SPECS) == (
        10, 20, 30, 40, 50, 60, 70, 80, 90
    )


def test_loop_registry_digest_rejects_row_capability_or_priority_drift():
    first = LOOP_PRODUCER_STAGE_SPECS[0]
    mutated = (replace(first, capability=LoopStageCapability.SOLVER_UNSAT_ONLY),) + (
        LOOP_PRODUCER_STAGE_SPECS[1:]
    )
    payload = dict(loop_producer_registry_authority_dict())
    payload["rows"] = tuple(item.to_authority_tuple() for item in mutated)
    assert authority_digest(payload) != EXPECTED_LOOP_PRODUCER_STAGE_REGISTRY_DIGEST

    mutated = LOOP_PRODUCER_STAGE_SPECS[:-1] + (
        replace(LOOP_PRODUCER_STAGE_SPECS[-1], terminal_priority=91),
    )
    payload["rows"] = tuple(item.to_authority_tuple() for item in mutated)
    assert authority_digest(payload) != EXPECTED_LOOP_PRODUCER_STAGE_REGISTRY_DIGEST


@pytest.mark.parametrize(
    ("source_code", "reason_id"),
    (
        ("counted_loop_summary_expression_proof_missing", "loop_exact_summary_relation_unproven"),
        ("loop_summary_guard_mismatch", "loop_summary_guard_correspondence_unproven"),
        ("loop_summary_shape_mismatch", "loop_summary_structure_correspondence_unproven"),
        ("loop_summary_intrinsic_mismatch", "loop_summary_structure_correspondence_unproven"),
        ("loop_summary_operand_mismatch", "loop_summary_structure_correspondence_unproven"),
        ("exact_key_unavailable", "loop_summary_structure_correspondence_unproven"),
        ("exact_key_mismatch", "loop_summary_structure_correspondence_unproven"),
        ("loop_summary_unproven", "loop_summary_semantic_equality_unproven"),
        ("loop_summary_unknown", "loop_summary_semantic_equality_unproven"),
    ),
)
def test_exact_loop_fallback_matrix(source_code, reason_id):
    classified = classify_loop_fallback(source_code)
    assert classified.disposition is LoopSourceDisposition.TYPED_SLICE4_CAUSE
    assert classified.reason_ids == (reason_id,)


@pytest.mark.parametrize(
    "source_code",
    (
        "loop_summary_guard_mismatch_extra",
        "missing_runtime_ref",
        "not_loop_contract",
        "no_shortcut",
        "loop_summary_proof_missing",
        "method_b_closure_blocked",
    ),
)
def test_loop_fallback_near_miss_is_invalid(source_code):
    classified = classify_loop_fallback(source_code)
    assert classified.disposition is LoopSourceDisposition.INFRASTRUCTURE_INVALID
    assert classified.reason_ids == ()


@pytest.mark.parametrize(
    ("source_code", "reason_id"),
    (
        ("summary_return_candidate_invalid:no_proposed_returns", "summary_return_extraction_incomplete"),
        ("summary_return_candidate_invalid:no_new_summary_returns", "summary_return_extraction_incomplete"),
        ("summary_return_candidate_invalid:no_valid_candidates", "summary_return_extraction_incomplete"),
        ("summary_return_candidate_invalid:value_missing", "summary_return_value_extraction_incomplete"),
        ("summary_return_candidate_invalid:transition_evidence_missing", "summary_recurrence_transition_validation_incomplete"),
        ("summary_return_candidate_invalid:transition_evidence_incomplete", "summary_recurrence_transition_validation_incomplete"),
        ("summary_precondition_incomplete:summary_applicability_guard_missing", "summary_return_precondition_incomplete"),
        ("summary_effect_unmodeled:side_effect_provenance_incomplete", "summary_effect_model_incomplete"),
        ("summary_effect_unmodeled:effect_region_incomplete", "summary_effect_model_incomplete"),
        ("summary_effect_unmodeled:memory_read_unmodeled", "summary_effect_model_incomplete"),
        ("summary_effect_unmodeled:memory_write_effects_present", "summary_effect_model_incomplete"),
        ("phi_circular_replacement_unproven:replacement_obligation_missing", "phi_cycle_lowering_unproven"),
        ("summary_return_overlap_unproven:overlap_feasibility_unknown", "summary_return_overlap_feasibility_unproven"),
        ("summary_return_overlap_unproven:value_comparison_unavailable", "summary_return_overlap_input_incomplete"),
        ("summary_return_overlap_unproven:value_equality_not_proved", "summary_return_overlap_value_equality_unproven"),
        ("summary_return_overlap_unproven:memory_read_model_mismatch", "summary_return_memory_observation_mismatch"),
        ("summary_partition_not_total:active_precondition_not_covered", "summary_return_partition_totality_unproven"),
        ("return_coverage_gap:summary_partition_not_total:active_precondition_not_covered", "summary_return_partition_totality_unproven"),
    ),
)
def test_exact_summary_blocker_matrix(source_code, reason_id):
    classified = classify_summary_blocker(source_code)
    assert classified.disposition is LoopSourceDisposition.TYPED_SLICE4_CAUSE
    assert classified.reason_ids == (reason_id,)


@pytest.mark.parametrize(
    "source_code",
    (
        "summary_return_candidate_invalid:unstable_guard_key",
        "summary_return_candidate_invalid:unstable_value_key",
        "summary_return_candidate_invalid:opaque_guard_key",
        "summary_return_candidate_invalid:opaque_value_key",
        "summary_return_candidate_invalid:loop_summary_identity_missing",
        "summary_return_candidate_invalid:unstable_loop_summary_identity",
        "summary_return_candidate_invalid:unstable_transition_evidence",
        "summary_return_candidate_invalid:unknown_new_code",
    ),
)
def test_identity_incomplete_or_unknown_summary_blocker_is_invalid(source_code):
    classified = classify_summary_blocker(source_code)
    assert classified.disposition is LoopSourceDisposition.INFRASTRUCTURE_INVALID
    assert classified.reason_ids == ()


@pytest.mark.parametrize(
    "source_code",
    (
        "summary_return_candidate_invalid:return_width_missing",
        "summary_return_overlap_unproven:return_width_mismatch",
    ),
)
def test_width_summary_blockers_are_deferred_to_slice5(source_code):
    assert classify_summary_blocker(source_code).disposition is (
        LoopSourceDisposition.DEFERRED_SLICE5
    )


def test_slice3_effect_ownership_precedes_slice4_candidate_model():
    assert classify_summary_blocker(
        "summary_effect_unmodeled:effect_summary_missing"
    ).reason_ids == ("effect_observation_coverage_incomplete",)
    assert classify_summary_blocker(
        "summary_effect_unmodeled:unsupported_call_effect"
    ).reason_ids == ("unsupported_call_effect_semantics",)

    classified = classify_effect_incomplete_reasons((
        "callee_effect_summary_missing",
        "effect_order_unavailable",
        "effect_summary_path_coverage_incomplete",
    ))
    assert classified.disposition is LoopSourceDisposition.REFINED_TO_SLICE3
    assert classified.reason_ids == (
        "callee_effect_summary_incomplete",
        "memory_effect_order_extraction_incomplete",
        "effect_observation_coverage_incomplete",
    )


@pytest.mark.parametrize(
    "reasons",
    (
        (),
        ("effect_order_unavailable", "callee_effect_summary_missing"),
        ("effect_order_unavailable", "effect_order_unavailable"),
        ("unknown_effect_reason",),
    ),
)
def test_effect_incomplete_tuple_requires_nonempty_sorted_unique_sealed_members(reasons):
    assert classify_effect_incomplete_reasons(reasons).disposition is (
        LoopSourceDisposition.INFRASTRUCTURE_INVALID
    )


def test_summary_overlap_reasons_are_unary_not_cross_binary_relational():
    overlap_ids = {
        "summary_return_overlap_feasibility_unproven",
        "summary_return_overlap_input_incomplete",
        "summary_return_overlap_value_equality_unproven",
        "summary_return_memory_observation_mismatch",
    }
    assert all(
        LOOP_REASON_SPECS[reason_id].identity_scope is IdentityScope.UNARY
        for reason_id in overlap_ids
    )
    assert all(
        LOOP_REASON_SPECS[reason_id].target_kind == "same_function_return_pair"
        for reason_id in overlap_ids
    )


def test_method_b_is_not_a_reason_or_proof_identity():
    assert not any("method_b" in reason_id for reason_id in LOOP_REASON_SPECS)
    assert not any(
        "method_b" in proof_kind
        for spec in LOOP_REASON_SPECS.values()
        for proof_kind in spec.proof_kinds
    )


def _loop_exact_fixture():
    from unittest.mock import Mock

    from scripts.function_tracer_pcode.equivalence.strategies.pairwise_models import (
        ReturnCase,
    )
    from scripts.function_tracer_pcode.equivalence.strategies.pairwise import (
        PairwiseStrategy,
    )
    from scripts.function_tracer_pcode.model import Condition, Expression, ReturnInfo
    from scripts.function_tracer_pcode.tests.unit.test_object_centric_runtime_refs import (
        _readonly_loop_summary,
        _readonly_sum_expr,
    )

    base = Expression.parameter("base", index=0, data_type="int *", size=8)
    exact_value = Expression.binary_op(
        "INT_ADD",
        Expression.memory(base, size=4),
        Expression.memory(
            Expression.binary_op(
                "INT_ADD", base, Expression.constant(4, size=8)
            ),
            size=4,
        ),
    )
    summary_value = _readonly_sum_expr(_readonly_loop_summary(start=0, step=1))
    count = Expression.parameter("count", index=1, data_type="int", size=4)
    count_is_two = Condition(
        Expression.binary_op(
            "INT_EQUAL", count, Expression.constant(2, size=4)
        ),
        False,
    )
    parameters = [
        {"name": "base", "index": 0, "data_type": "int *", "size": 8},
        {"name": "count", "index": 1, "data_type": "int", "size": 4},
    ]
    exact_return = ReturnInfo(
        address="0x1010",
        value=exact_value,
        conditions=[count_is_two],
        pcode_identity="exact-return-a",
    )
    summary_return = ReturnInfo(
        address="0x2020",
        value=summary_value,
        conditions=[count_is_two],
        pcode_identity="summary-return-b",
    )
    exact_case = ReturnCase(
        0, [count_is_two], exact_value, exact_return, parameters=parameters
    )
    summary_case = ReturnCase(
        1, [count_is_two], summary_value, summary_return, parameters=parameters
    )
    strategy = PairwiseStrategy(Mock(), Mock(), debug=False)
    left = _analysis("left-loop-exact")
    right = _analysis("right-loop-summary")
    blocker = LoopBlockerProductionSignal.from_loop_fallback(
        left,
        right,
        exact_case,
        summary_case,
        "counted_loop_summary_expression_proof_missing",
        observation_contract_id="return-and-memory-v1",
    )
    term = LoopExactTermRelationCompletionSignal.from_pairwise_cases(
        blocker, exact_case, summary_case
    )
    guard = LoopExactGuardPartitionCompletionSignal.from_pairwise_cases(
        term, exact_case, summary_case
    )
    return blocker, term, guard, strategy, exact_case, summary_case, left, right


def _typed_loop_query(
    blocker, requirement, left, right, exact_case, summary_case,
    execution_identity_digest, *, pair_id="(0,1)",
):
    from scripts.function_tracer_pcode.equivalence.strategies.pairwise_query_executor import (
        render_loop_v2_solver_query,
    )

    rendered = render_loop_v2_solver_query(
        blocker=blocker,
        requirement=requirement,
        analysis1=left,
        analysis2=right,
        case1=exact_case,
        case2=summary_case,
        pair_id=pair_id,
        execution_identity_digest=execution_identity_digest,
    )
    return _issue_loop_solver_query_authority(rendered)


def test_loop_exact_blocker_binds_distinct_term_and_guard_requirements():
    blocker, _, _, _, exact_case, summary_case, left, right = _loop_exact_fixture()
    authority = LoopRecurrencePilotEncoder().authority_for_signal(
        _session("loop-exact-result"), blocker
    )
    bindings = dict(authority.bound_contract.slot_bindings)
    assert set(bindings) == {
        "loop_exact_term_relation",
        "loop_exact_guard_partition",
    }
    assert bindings["loop_exact_term_relation"].requirement_id != (
        bindings["loop_exact_guard_partition"].requirement_id
    )


def test_loop_exact_completion_requires_observation_and_term_before_guard():
    blocker, term, guard, _, _, _, _, _ = _loop_exact_fixture()
    encoder = LoopRecurrencePilotEncoder()
    session = _session("loop-exact-result")
    with pytest.raises(ValueError, match="no observed live occurrence"):
        encoder(session, term)
    assert encoder(session, blocker)[0].event_type is EventType.CAUSE_OBSERVED
    with pytest.raises(ValueError, match="prior exact term authority"):
        encoder(session, guard)


def test_loop_exact_term_and_guard_issue_separate_ordered_authorities():
    blocker, term, guard, _, _, _, _, _ = _loop_exact_fixture()
    encoder = LoopRecurrencePilotEncoder()
    session = _session("loop-exact-result")
    encoder(session, blocker)
    term_event = encoder(session, term)
    guard_event = encoder(session, guard)
    assert term_event[0].event_type is EventType.REQUIREMENT_COMPLETED
    assert guard_event[0].event_type is EventType.REQUIREMENT_COMPLETED
    authorities = session.domain_signal_state["loop_exact_completion_authorities"]
    assert [type(item) for item in authorities] == [
        LoopExactTermRelationCompletionAuthority,
        LoopExactGuardPartitionCompletionAuthority,
    ]
    assert authorities[0].completion_receipt.proof_requirement_id != (
        authorities[1].completion_receipt.proof_requirement_id
    )
    assert authorities[0].artifact_digest in authorities[1].dependency_proof_ids
    assert encoder(session, term) == ()
    assert encoder(session, guard) == ()
    assert "method_b" not in repr(tuple(
        item.completion_receipt for item in authorities
    )).lower()


def test_loop_exact_factories_ignore_mutated_producer_instance_methods():
    import scripts.function_tracer_pcode.equivalence.v2.loop_recurrence as loop_module
    from scripts.function_tracer_pcode.equivalence.strategies.pairwise import (
        PairwiseStrategy,
    )
    from scripts.function_tracer_pcode.equivalence.strategies.pairwise_services import (
        orchestration_1,
        readonly_reduction_1,
    )

    _, term, _, strategy, exact_case, summary_case, _, _ = _loop_exact_fixture()
    real_covering = strategy._method_b_covering_case_proof(exact_case, summary_case)
    forged = replace(
        real_covering,
        exact_proof=replace(
            real_covering.exact_proof,
            count_value=999,
            count_values=(999,),
            evidence="caller-self-attested",
        ),
    )
    strategy._method_b_covering_case_proof = lambda *_: forged
    strategy._cases_admit_reduction_count_values = lambda *_: True
    PairwiseStrategy._method_b_covering_case_proof = lambda *_: forged
    PairwiseStrategy._cases_admit_reduction_count_values = lambda *_: True
    with pytest.raises(TypeError, match="class is immutable"):
        loop_module._SealedPairwiseStructuralValidator._method_b_covering_case_proof = (
            lambda *_: forged
        )
    with pytest.raises(TypeError, match="class is immutable"):
        loop_module._SealedPairwiseStructuralValidator._cases_admit_reduction_count_values = (
            lambda *_: True
        )
    original_covering_impl = orchestration_1._impl__method_b_covering_case_proof
    original_guard_impl = readonly_reduction_1._impl__cases_admit_reduction_count_values
    orchestration_1._impl__method_b_covering_case_proof = lambda *_: forged
    readonly_reduction_1._impl__cases_admit_reduction_count_values = lambda *_: True
    try:
        sealed_term = LoopExactTermRelationCompletionSignal.from_pairwise_cases(
            term.blocker, exact_case, summary_case
        )
        sealed_guard = LoopExactGuardPartitionCompletionSignal.from_pairwise_cases(
            sealed_term, exact_case, summary_case
        )
    finally:
        del PairwiseStrategy._method_b_covering_case_proof
        del PairwiseStrategy._cases_admit_reduction_count_values
        orchestration_1._impl__method_b_covering_case_proof = original_covering_impl
        readonly_reduction_1._impl__cases_admit_reduction_count_values = original_guard_impl
    assert ("count_values", (2,)) in sealed_term.structural_proof_body
    assert "caller-self-attested" not in repr(sealed_term.structural_proof_body)
    assert ("admitted_count_values", (2,)) in sealed_guard.structural_coverage_body


def test_loop_exact_guard_joins_the_exact_prior_term_artifact():
    blocker, first_term, _, _, exact_case, summary_case, _, _ = _loop_exact_fixture()
    other_term = LoopExactTermRelationCompletionSignal.from_pairwise_cases(
        blocker,
        exact_case,
        summary_case,
        dependency_proof_ids=("different-dependency",),
    )
    other_guard = LoopExactGuardPartitionCompletionSignal.from_pairwise_cases(
        other_term, exact_case, summary_case
    )
    encoder = LoopRecurrencePilotEncoder()
    session = _session("loop-exact-term-join")
    encoder(session, blocker)
    encoder(session, first_term)
    with pytest.raises(ValueError, match="does not join prior term authority"):
        encoder(session, other_guard)


def test_real_method_b_producer_dual_writes_blocker_term_and_guard():
    from scripts.function_tracer_pcode.equivalence.strategies.pairwise_services._shared import (
        make_internal_v2_reason_diagnostic,
    )

    blocker, _, _, strategy, exact_case, summary_case, _, _ = _loop_exact_fixture()
    analysis1 = _analysis("legacy-method-b-left")
    analysis2 = _analysis("legacy-method-b-right")
    target = strategy._method_b_closure_object_target_key(
        base_ctx={"analysis1": analysis1, "analysis2": analysis2},
        case1=exact_case,
        case2=summary_case,
        pair_id="(0,1)",
    )
    reason = make_internal_v2_reason_diagnostic(
        blocker.reason_id,
        stage="S_PAIRWISE",
        pair_or_case="(0,1)",
        evidence_refs=("counted_loop_summary_expression_proof_missing",),
        object_target_key=target,
    )
    encoder = LoopRecurrencePilotEncoder()
    composite = CompositeProductionSignalEncoder({
        LoopBlockerProductionSignal: encoder,
        LoopExactTermRelationCompletionSignal: encoder,
        LoopExactGuardPartitionCompletionSignal: encoder,
    })

    class _Session:
        def __init__(self):
            self.identity = _session("real-method-b-producer").identity
            self.domain_signal_state = {}
            self.domain_signal_encoder = composite
            self.intents = []

        def emit_domain_signal(self, signal):
            intents = tuple(self.domain_signal_encoder(self, signal))
            self.intents.extend(intents)
            return len(intents)

    session = _Session()
    with production_signal_scope(session):
        from scripts.function_tracer_pcode.equivalence.v2.production_signals import (
            emit_loop_recurrence_signal,
        )

        emit_loop_recurrence_signal(blocker)
        strategy._record_completed_method_b_covering_case_proof_if_safe(
            reason,
            analysis1,
            exact_case,
            summary_case,
            v2_blocker_signal=blocker,
        )

    assert [intent.event_type for intent in session.intents] == [
        EventType.CAUSE_OBSERVED,
        EventType.REQUIREMENT_COMPLETED,
        EventType.REQUIREMENT_COMPLETED,
    ]
    assert analysis1.completed_recovery_proof_evidence == ()
    assert len(session.domain_signal_state["loop_recurrence_completed_requirements"]) == 2
    from scripts.function_tracer_pcode.equivalence.v2.reducer import (
        ShadowLifecycleReducer,
    )
    from scripts.function_tracer_pcode.equivalence.v2.stream import EventRecorder

    recorder = EventRecorder(
        stream_id="real-method-b-stream",
        result_occurrence_id=session.identity.result_occurrence_id,
        source_snapshot_fingerprint=session.identity.source_snapshot_fingerprint,
    )
    for intent in session.intents:
        recorder.append(intent)
    reduction = ShadowLifecycleReducer(
        reason_registry=LOOP_REASON_REGISTRY,
        recovery_registry=LOOP_RECOVERY_REGISTRY,
    ).replay(recorder.seal())
    assert reduction.projection.c_active_base == ()
    assert reduction.projection.q_open_base == ()


def test_loop_solver_query_and_assignment_bind_exact_live_q():
    from scripts.function_tracer_pcode.equivalence.v2.reducer import (
        ShadowLifecycleReducer,
    )
    from scripts.function_tracer_pcode.equivalence.v2.stream import EventRecorder

    blocker, _, _, _, exact_case, summary_case, left, right = _loop_exact_fixture()
    encoder = LoopRecurrencePilotEncoder()
    session = _session("loop-query-result")
    authority = encoder.authority_for_signal(session, blocker)
    requirement = next(
        item for _, item in authority.bound_contract.slot_bindings
        if item.proof_kind == "loop_exact_term_relation"
    )
    query = _typed_loop_query(
        blocker, requirement, left, right, exact_case, summary_case,
        session.identity.execution_identity_digest,
    )
    recorder = EventRecorder(
        stream_id="loop-query-stream",
        result_occurrence_id=session.identity.result_occurrence_id,
        source_snapshot_fingerprint=session.identity.source_snapshot_fingerprint,
    )
    for intent in encoder(session, blocker):
        recorder.append(intent)
    reducer = ShadowLifecycleReducer(
        reason_registry=LOOP_REASON_REGISTRY,
        recovery_registry=LOOP_RECOVERY_REGISTRY,
    )
    projection = reducer.replay_prefix(recorder.prefix_view())
    row = next(
        item for item in projection.q_open_base
        if item.proof_kind == "loop_exact_term_relation"
    )
    assignment = issue_loop_requirement_assignment(
        projection=projection,
        q_open_row=row,
        query_authority=query,
    )
    assignment.validate_against(projection)
    assert assignment.proof_requirement_id == requirement.requirement_id
    assert assignment.proof_stage == "loop_exact_term_relation"
    context = LoopSolverExecutionContext(
        projection,
        session.identity.result_occurrence_id,
        {row.proof_kind: row},
    )
    first = context.membership_for(query)
    second = context.membership_for(query)
    first.validate_against(LOOP_COMMON_EXECUTION_STAGE_REGISTRY)
    second.validate_against(LOOP_COMMON_EXECUTION_STAGE_REGISTRY)
    assert (first.attempt_ordinal, second.attempt_ordinal) == (1, 2)
    assert first.requirement_assignment.assignment_digest == (
        second.requirement_assignment.assignment_digest
    )


def test_loop_solver_query_rejects_direct_construction_and_wrong_live_q():
    blocker, _, _, _, exact_case, summary_case, left, right = _loop_exact_fixture()
    encoder = LoopRecurrencePilotEncoder()
    session = _session("loop-query-negative")
    authority = encoder.authority_for_signal(session, blocker)
    requirements = {
        item.proof_kind: item for _, item in authority.bound_contract.slot_bindings
    }
    with pytest.raises(TypeError, match="typed-renderer issued"):
        LoopSolverQueryAuthority(
            stage="loop_exact_term_relation",
            proof_kind="loop_exact_term_relation",
            obligation_id="caller",
            observation_contract_id="caller",
            semantic_target_digest="caller",
            query_text="(check-sat)",
            normalized_assertion_text="true",
            execution_identity_digest="caller",
            authority_digest="caller",
        )
    with pytest.raises(TypeError, match="typed renderer receipt"):
        _issue_loop_solver_query_authority("(assert false)")
    query = _typed_loop_query(
        blocker, requirements["loop_exact_term_relation"], left, right,
        exact_case, summary_case, session.identity.execution_identity_digest,
    )
    assert query.proof_kind != requirements["loop_exact_guard_partition"].proof_kind
    from scripts.function_tracer_pcode.equivalence.strategies.pairwise_query_executor import (
        render_loop_v2_solver_query,
    )
    import scripts.function_tracer_pcode.equivalence.strategies.pairwise_query_executor as query_executor_module

    rendered = render_loop_v2_solver_query(
        blocker=blocker,
        requirement=requirements["loop_exact_term_relation"],
        analysis1=left,
        analysis2=right,
        case1=exact_case,
        case2=summary_case,
        pair_id="(0,1)",
        execution_identity_digest=session.identity.execution_identity_digest,
    )
    forged_payload = {
        name: getattr(rendered, name)
        for name in rendered.__dataclass_fields__
        if name != "renderer_receipt_digest"
    }
    forged_payload["query_text"] = "(assert true)\n(check-sat)"
    forged_payload["normalized_assertion_text"] = "(assert true)"
    with pytest.raises(TypeError, match="factory-issued"):
        replace(
            rendered,
            **forged_payload,
            renderer_receipt_digest=authority_digest(forged_payload),
        )
    with pytest.raises(TypeError, match="factory-issued"):
        type(rendered)(
            **forged_payload,
            renderer_receipt_digest=authority_digest(forged_payload),
        )
    unissued = object.__new__(type(rendered))
    for name, value in forged_payload.items():
        object.__setattr__(unissued, name, value)
    object.__setattr__(
        unissued, "renderer_receipt_digest", authority_digest(forged_payload)
    )
    with pytest.raises(ValueError, match="renderer receipt is invalid"):
        unissued.validate()
    with pytest.raises(ValueError, match="renderer receipt is invalid"):
        _issue_loop_solver_query_authority(unissued)
    assert not hasattr(rendered, "_renderer_token")
    assert not hasattr(
        query_executor_module, "_issue_rendered_loop_v2_solver_query"
    )
    assert not hasattr(
        query_executor_module, "_ISSUED_LOOP_V2_RENDERER_RECEIPTS"
    )
    assert not hasattr(
        query_executor_module, "_derive_loop_v2_solver_query_payload"
    )
    with pytest.raises(TypeError, match="receipt type is immutable"):
        type(rendered).validate = lambda _self: None
    assert copy.copy(rendered) is rendered
    assert copy.deepcopy(rendered) is rendered
    with pytest.raises(TypeError, match="not pickle-authority"):
        pickle.dumps(rendered)


def _loop_solver_runtime_fixture(result_id):
    from scripts.function_tracer_pcode.equivalence.v2.reducer import (
        ShadowLifecycleReducer,
    )
    from scripts.function_tracer_pcode.equivalence.v2.stream import EventRecorder

    blocker, _, _, _, exact_case, summary_case, left, right = _loop_exact_fixture()
    encoder = LoopRecurrencePilotEncoder()
    session = _session(result_id)
    authority = encoder.authority_for_signal(session, blocker)
    requirement = next(
        item for _, item in authority.bound_contract.slot_bindings
        if item.proof_kind == "loop_exact_term_relation"
    )
    query = _typed_loop_query(
        blocker, requirement, left, right, exact_case, summary_case,
        session.identity.execution_identity_digest,
    )
    recorder = EventRecorder(
        stream_id=result_id + "-stream",
        result_occurrence_id=result_id,
        source_snapshot_fingerprint=session.identity.source_snapshot_fingerprint,
    )
    for intent in encoder(session, blocker):
        recorder.append(intent)
    projection = ShadowLifecycleReducer(
        reason_registry=LOOP_REASON_REGISTRY,
        recovery_registry=LOOP_RECOVERY_REGISTRY,
    ).replay_prefix(recorder.prefix_view())
    row = next(
        item for item in projection.q_open_base
        if item.proof_kind == "loop_exact_term_relation"
    )
    context = LoopSolverExecutionContext(projection, result_id, {row.proof_kind: row})
    return (
        blocker,
        encoder,
        session,
        projection,
        query,
        context.membership_for(query),
        (requirement, left, right, exact_case, summary_case),
    )


def _plan_and_commit_loop_solver_batch(encoder, session, batch):
    intents = tuple(encoder(session, batch))
    encoder.commit_emitted_signal(session, batch, intents)
    return intents


def test_loop_solver_timeout_then_unsat_observes_timeout_and_completes_q(monkeypatch):
    import scripts.function_tracer_pcode.equivalence.v2.execution_authority as execution_module
    from scripts.function_tracer_pcode.equivalence.v2.execution_authority import (
        ExecutionAuthorityDeploymentPolicy,
        PINNED_SOLVER_EXECUTION_ISSUER,
        activate_execution_authority_deployment,
        install_execution_authority_signing_key,
    )
    from scripts.function_tracer_pcode.smt.interface import SolverResult, SolverStatus
    from scripts.function_tracer_pcode.smt.parallel import ParallelResult

    key_id = "loop-solver-test-key"
    install_execution_authority_signing_key(key_id, b"l" * 32)
    activate_execution_authority_deployment(ExecutionAuthorityDeploymentPolicy(
        "loop-solver-test-policy", 1, "test-owner", "test-source",
        key_id, (), 3600, "test-revocation",
    ))
    monkeypatch.setattr(
        execution_module,
        "_PINNED_PARALLEL_RUN_IMPL",
        lambda _runner, _query, timeout: ParallelResult(results=[
            SolverResult("z3", SolverStatus.TIMEOUT, elapsed_time=timeout),
            SolverResult("z3", SolverStatus.UNSAT, elapsed_time=0.001),
        ]),
    )
    blocker, encoder, session, projection, query, membership, render_inputs = (
        _loop_solver_runtime_fixture("loop-timeout-unsat-result")
    )
    receipts = PINNED_SOLVER_EXECUTION_ISSUER.execute(
        registry=LOOP_COMMON_EXECUTION_STAGE_REGISTRY,
        result_occurrence_id=session.identity.result_occurrence_id,
        membership=membership,
        invocation_identity="loop-timeout-unsat-invocation",
        first_invocation_ordinal=1,
        query=query.query_text,
        configured_timeout_ms=1000,
        query_authority=query,
        lifecycle_projection=projection,
    )
    authority = encoder.authority_for_signal(session, blocker)
    requirement = next(
        item for _, item in authority.bound_contract.slot_bindings
        if item.proof_kind == query.proof_kind
    )
    _, left, right, exact_case, summary_case = render_inputs
    substituted_query = _typed_loop_query(
        blocker, requirement, left, right, exact_case, summary_case,
        "substituted-execution-identity",
        pair_id="(substituted,query)",
    )
    with pytest.raises(ValueError, match="differs from supplied query"):
        LoopSolverExecutionBatchSignal.from_issuer_results(
            blocker, substituted_query, membership, receipts, projection
        )
    batch = LoopSolverExecutionBatchSignal.from_issuer_results(
        blocker, query, membership, tuple(reversed(receipts)), projection
    )
    intents = _plan_and_commit_loop_solver_batch(encoder, session, batch)
    assert [item.event_type for item in intents] == [
        EventType.SOLVER_TIMEOUT,
        EventType.REQUIREMENT_COMPLETED,
    ]
    assert len(session.domain_signal_state["loop_solver_unsat_completion_receipts"]) == 1
    term_authority = session.domain_signal_state[
        "loop_exact_completion_authorities"
    ][0]
    guard_signal = (
        LoopExactGuardPartitionCompletionSignal.from_pairwise_cases_after_term_authority(
            blocker,
            term_authority,
            exact_case,
            summary_case,
        )
    )
    guard_intents = encoder(session, guard_signal)
    assert [item.event_type for item in guard_intents] == [
        EventType.REQUIREMENT_COMPLETED
    ]
    census = PINNED_SOLVER_EXECUTION_ISSUER.seal_result_census(
        LOOP_COMMON_EXECUTION_STAGE_REGISTRY,
        session.identity.result_occurrence_id,
    )
    assert [event.execution_receipt.observed_status for event in census.events] == [
        "timeout", "unsat"
    ]
    from scripts.function_tracer_pcode.equivalence.v2.reducer import (
        ShadowLifecycleReducer,
    )
    from scripts.function_tracer_pcode.equivalence.v2.stream import (
        CauseObservedEventAuthority,
        EventIntent,
        EventRecorder,
    )

    recorder = EventRecorder(
        stream_id="loop-timeout-unsat-replay",
        result_occurrence_id=session.identity.result_occurrence_id,
        source_snapshot_fingerprint=session.identity.source_snapshot_fingerprint,
    )
    recorder.append(EventIntent(
        EventType.CAUSE_OBSERVED,
        CauseObservedEventAuthority(encoder.authority_for_signal(session, blocker)),
    ))
    for intent in (*intents, *guard_intents):
        recorder.append(intent)
    reduction = ShadowLifecycleReducer(
        reason_registry=LOOP_REASON_REGISTRY,
        recovery_registry=LOOP_RECOVERY_REGISTRY,
    ).replay(recorder.seal())
    assert reduction.projection.c_active_base == ()
    assert reduction.projection.q_open_base == ()


def test_loop_solver_sat_never_completes_unknown_and_requires_safety_handoff(monkeypatch):
    import scripts.function_tracer_pcode.equivalence.v2.execution_authority as execution_module
    from scripts.function_tracer_pcode.equivalence.v2.execution_authority import (
        ExecutionAuthorityDeploymentPolicy,
        PINNED_SOLVER_EXECUTION_ISSUER,
        activate_execution_authority_deployment,
        install_execution_authority_signing_key,
    )
    from scripts.function_tracer_pcode.smt.interface import SolverResult, SolverStatus
    from scripts.function_tracer_pcode.smt.parallel import ParallelResult

    key_id = "loop-sat-handoff-key"
    install_execution_authority_signing_key(key_id, b"h" * 32)
    activate_execution_authority_deployment(ExecutionAuthorityDeploymentPolicy(
        "loop-sat-handoff-policy", 1, "test-owner", "test-source",
        key_id, (), 3600, "test-revocation",
    ))
    monkeypatch.setattr(
        execution_module,
        "_PINNED_PARALLEL_RUN_IMPL",
        lambda _runner, _query, timeout: ParallelResult(results=[
            SolverResult(
                "z3", SolverStatus.SAT, elapsed_time=0.001, model={}
            ),
        ]),
    )
    blocker, encoder, session, projection, query, membership, _ = (
        _loop_solver_runtime_fixture("loop-sat-handoff-result")
    )
    receipts = PINNED_SOLVER_EXECUTION_ISSUER.execute(
        registry=LOOP_COMMON_EXECUTION_STAGE_REGISTRY,
        result_occurrence_id=session.identity.result_occurrence_id,
        membership=membership,
        invocation_identity="loop-sat-handoff-invocation",
        first_invocation_ordinal=1,
        query=query.query_text,
        configured_timeout_ms=1000,
        query_authority=query,
        lifecycle_projection=projection,
    )
    batch = LoopSolverExecutionBatchSignal.from_issuer_results(
        blocker, query, membership, receipts, projection
    )
    assert _plan_and_commit_loop_solver_batch(
        encoder,
        session,
        batch,
    ) == ()
    assert "loop_solver_unsat_completion_receipts" not in session.domain_signal_state
    assert len(session.domain_signal_state["loop_sat_safety_handoffs"]) == 1
    from scripts.function_tracer_pcode.equivalence.v2.execution_authority import (
        ModelBoundRelationalRefutationArtifact,
    )
    from scripts.function_tracer_pcode.equivalence.v2.production_signals import (
        SatSafetyBlockerProductionSignal,
    )

    artifacts = session.domain_signal_state[
        "loop_model_bound_refutation_artifacts"
    ]
    assert len(artifacts) == 1
    assert type(artifacts[0]) is ModelBoundRelationalRefutationArtifact
    assert type(session.domain_signal_state["loop_sat_safety_handoffs"][0]) is (
        SatSafetyBlockerProductionSignal
    )
    census = PINNED_SOLVER_EXECUTION_ISSUER.seal_result_census(
        LOOP_COMMON_EXECUTION_STAGE_REGISTRY,
        session.identity.result_occurrence_id,
    )
    assert [event.execution_receipt.observed_status for event in census.events] == [
        "sat", "sat"
    ]


def test_loop_sat_refutation_fails_closed_when_fixed_model_replay_is_not_sat(
    monkeypatch,
):
    import scripts.function_tracer_pcode.equivalence.v2.execution_authority as execution_module
    from scripts.function_tracer_pcode.equivalence.v2.execution_authority import (
        ExecutionAuthorityDeploymentPolicy,
        PINNED_SOLVER_EXECUTION_ISSUER,
        activate_execution_authority_deployment,
        install_execution_authority_signing_key,
    )
    from scripts.function_tracer_pcode.smt.interface import SolverResult, SolverStatus
    from scripts.function_tracer_pcode.smt.parallel import ParallelResult

    key_id = "loop-sat-replay-negative-key"
    install_execution_authority_signing_key(key_id, b"n" * 32)
    activate_execution_authority_deployment(ExecutionAuthorityDeploymentPolicy(
        "loop-sat-replay-negative-policy", 1, "test-owner", "test-source",
        key_id, (), 3600, "test-revocation",
    ))
    calls = iter((
        ParallelResult(results=[SolverResult(
            "z3", SolverStatus.SAT, elapsed_time=0.001, model={}
        )]),
        ParallelResult(results=[SolverResult(
            "z3", SolverStatus.UNSAT, elapsed_time=0.001
        )]),
    ))
    monkeypatch.setattr(
        execution_module,
        "_PINNED_PARALLEL_RUN_IMPL",
        lambda _runner, _query, timeout: next(calls),
    )
    blocker, encoder, session, projection, query, membership, _ = (
        _loop_solver_runtime_fixture("loop-sat-replay-negative-result")
    )
    receipts = PINNED_SOLVER_EXECUTION_ISSUER.execute(
        registry=LOOP_COMMON_EXECUTION_STAGE_REGISTRY,
        result_occurrence_id=session.identity.result_occurrence_id,
        membership=membership,
        invocation_identity="loop-sat-replay-negative-invocation",
        first_invocation_ordinal=1,
        query=query.query_text,
        configured_timeout_ms=1000,
        query_authority=query,
        lifecycle_projection=projection,
    )
    batch = LoopSolverExecutionBatchSignal.from_issuer_results(
        blocker, query, membership, receipts, projection
    )
    with pytest.raises(ValueError, match="fixed-model replay was not SAT"):
        encoder(session, batch)
    assert "loop_model_bound_refutation_artifacts" not in session.domain_signal_state
    assert "loop_sat_safety_handoffs" not in session.domain_signal_state
    assert "loop_solver_unsat_completion_receipts" not in session.domain_signal_state
    census = PINNED_SOLVER_EXECUTION_ISSUER.seal_result_census(
        LOOP_COMMON_EXECUTION_STAGE_REGISTRY,
        session.identity.result_occurrence_id,
    )
    assert [event.execution_receipt.observed_status for event in census.events] == [
        "sat", "unsat"
    ]


def test_loop_solver_batch_commit_failure_rolls_back_stream_and_all_ledgers(
    monkeypatch,
):
    import scripts.function_tracer_pcode.equivalence.v2.execution_authority as execution_module
    from scripts.function_tracer_pcode.equivalence.v2.execution_authority import (
        ExecutionAuthorityDeploymentPolicy,
        PINNED_SOLVER_EXECUTION_ISSUER,
        activate_execution_authority_deployment,
        install_execution_authority_signing_key,
    )
    from scripts.function_tracer_pcode.equivalence.v2.pilot import (
        ProductionDualWritePilotConnector,
    )
    from scripts.function_tracer_pcode.equivalence.v2.production_signals import (
        active_loop_requirement_for_signal,
        execute_loop_solver_rendered_query,
    )
    from scripts.function_tracer_pcode.equivalence.v2.reducer import (
        ShadowLifecycleReducer,
    )
    from scripts.function_tracer_pcode.equivalence.strategies.pairwise_query_executor import (
        render_loop_v2_solver_query,
    )
    from scripts.function_tracer_pcode.smt.interface import SolverResult, SolverStatus
    from scripts.function_tracer_pcode.smt.parallel import ParallelResult

    key_id = "loop-stream-rollback-key"
    install_execution_authority_signing_key(key_id, b"r" * 32)
    activate_execution_authority_deployment(ExecutionAuthorityDeploymentPolicy(
        "loop-stream-rollback-policy", 1, "test-owner", "test-source",
        key_id, (), 3600, "test-revocation",
    ))
    monkeypatch.setattr(
        execution_module,
        "_PINNED_PARALLEL_RUN_IMPL",
        lambda _runner, _query, timeout: ParallelResult(results=[
            SolverResult("z3", SolverStatus.SAT, elapsed_time=0.001, model={}),
        ]),
    )
    loop_encoder = LoopRecurrencePilotEncoder()
    composite = CompositeProductionSignalEncoder({
        LoopBlockerProductionSignal: loop_encoder,
        LoopSolverExecutionBatchSignal: loop_encoder,
    })
    connector = ProductionDualWritePilotConnector(
        ShadowLifecycleReducer(
            reason_registry=LOOP_REASON_REGISTRY,
            recovery_registry=LOOP_RECOVERY_REGISTRY,
        ),
        domain_signal_encoder=composite,
    )
    session = connector.begin({"case": "loop-stream-rollback"})
    blocker, _, _, _, exact_case, summary_case, left, right = _loop_exact_fixture()
    with production_signal_scope(session):
        assert session.emit_domain_signal(blocker) == 1
        requirement = active_loop_requirement_for_signal(
            blocker, "loop_exact_term_relation"
        )
        rendered = render_loop_v2_solver_query(
            blocker=blocker,
            requirement=requirement,
            analysis1=left,
            analysis2=right,
            case1=exact_case,
            case2=summary_case,
            pair_id="(0,1)",
            execution_identity_digest=session.identity.execution_identity_digest,
        )

        def fail_during_commit(state, payload):
            state.setdefault("loop_solver_execution_receipts", set()).update(
                payload["fresh_receipt_digests"]
            )
            state.setdefault(
                "loop_model_bound_refutation_artifacts", []
            ).extend(payload["model_artifacts"])
            raise RuntimeError("forced loop ledger commit failure")

        monkeypatch.setattr(
            loop_encoder,
            "_apply_solver_batch_commit_payload",
            fail_during_commit,
        )
        with pytest.raises(RuntimeError, match="forced loop ledger commit failure"):
            execute_loop_solver_rendered_query(
                blocker, rendered, configured_timeout_ms=1000
            )
    assert session.recorder.event_count == 1
    for key in (
        "loop_solver_execution_receipts",
        "loop_recurrence_completed_requirements",
        "loop_model_bound_refutation_artifacts",
        "loop_sat_safety_handoffs",
        "loop_exact_completion_authorities",
        "loop_solver_unsat_completion_receipts",
        "loop_solver_pending_emission_transactions",
    ):
        assert key not in session.domain_signal_state
    PINNED_SOLVER_EXECUTION_ISSUER.seal_result_census(
        LOOP_COMMON_EXECUTION_STAGE_REGISTRY,
        session.identity.result_occurrence_id,
    )


def test_loop_solver_phase7_execution_buffer_failure_precedes_stream_and_ledgers(
    monkeypatch,
):
    import scripts.function_tracer_pcode.equivalence.v2.execution_authority as execution_module
    from scripts.function_tracer_pcode.equivalence.v2.execution_authority import (
        ExecutionAuthorityDeploymentPolicy,
        PINNED_SOLVER_EXECUTION_ISSUER,
        activate_execution_authority_deployment,
        install_execution_authority_signing_key,
    )
    from scripts.function_tracer_pcode.equivalence.v2.phase7_runtime import (
        runtime_from_audited_manifest,
    )
    from scripts.function_tracer_pcode.equivalence.v2.pilot import (
        ProductionDualWritePilotConnector,
    )
    from scripts.function_tracer_pcode.equivalence.v2.production_signals import (
        active_loop_requirement_for_signal,
        execute_loop_solver_rendered_query,
    )
    from scripts.function_tracer_pcode.equivalence.v2.reducer import (
        ShadowLifecycleReducer,
    )
    from scripts.function_tracer_pcode.equivalence.strategies.pairwise_query_executor import (
        render_loop_v2_solver_query,
    )
    from scripts.function_tracer_pcode.smt.interface import SolverResult, SolverStatus
    from scripts.function_tracer_pcode.smt.parallel import ParallelResult

    key_id = "loop-phase7-buffer-rollback-key"
    install_execution_authority_signing_key(key_id, b"b" * 32)
    activate_execution_authority_deployment(ExecutionAuthorityDeploymentPolicy(
        "loop-phase7-buffer-rollback-policy", 1, "test-owner", "test-source",
        key_id, (), 3600, "test-revocation",
    ))
    monkeypatch.setattr(
        execution_module,
        "_PINNED_PARALLEL_RUN_IMPL",
        lambda _runner, _query, timeout: ParallelResult(results=[
            SolverResult("z3", SolverStatus.UNSAT, elapsed_time=0.001),
        ]),
    )
    loop_encoder = LoopRecurrencePilotEncoder()
    composite = CompositeProductionSignalEncoder({
        LoopBlockerProductionSignal: loop_encoder,
        LoopSolverExecutionBatchSignal: loop_encoder,
    })
    connector = ProductionDualWritePilotConnector(
        ShadowLifecycleReducer(
            reason_registry=LOOP_REASON_REGISTRY,
            recovery_registry=LOOP_RECOVERY_REGISTRY,
        ),
        domain_signal_encoder=composite,
    )
    session = connector.begin({"case": "loop-phase7-buffer-rollback"})
    blocker, _, _, _, exact_case, summary_case, left, right = _loop_exact_fixture()
    with production_signal_scope(session):
        assert session.emit_domain_signal(blocker) == 1
        requirement = active_loop_requirement_for_signal(
            blocker, "loop_exact_term_relation"
        )
        rendered = render_loop_v2_solver_query(
            blocker=blocker,
            requirement=requirement,
            analysis1=left,
            analysis2=right,
            case1=exact_case,
            case2=summary_case,
            pair_id="(0,1)",
            execution_identity_digest=session.identity.execution_identity_digest,
        )
        root = Path(__file__).resolve().parents[4]
        manifest = json.loads((root / (
            "artifacts/unknown_taxonomy_v2/phase7/producer-sites.json"
        )).read_text(encoding="utf-8"))
        runtime = runtime_from_audited_manifest(manifest, session.identity)
        session.phase7_runtime = runtime
        real_buffer = runtime.buffer_execution_intent

        def fail_after_buffer(intent):
            real_buffer(intent)
            raise RuntimeError("forced loop Phase 7 execution buffer failure")

        monkeypatch.setattr(runtime, "buffer_execution_intent", fail_after_buffer)
        with pytest.raises(
            RuntimeError, match="forced loop Phase 7 execution buffer failure"
        ):
            execute_loop_solver_rendered_query(
                blocker, rendered, configured_timeout_ms=1000
            )
    assert session.recorder.event_count == 1
    for key in (
        "loop_solver_execution_receipts",
        "loop_recurrence_completed_requirements",
        "loop_model_bound_refutation_artifacts",
        "loop_sat_safety_handoffs",
        "loop_exact_completion_authorities",
        "loop_solver_unsat_completion_receipts",
        "loop_solver_pending_emission_transactions",
    ):
        assert key not in session.domain_signal_state
    assert runtime._execution_intents == []
    assert runtime._signal_transactions == {}
    assert session._phase7_signal_transactions == {}
    PINNED_SOLVER_EXECUTION_ISSUER.seal_result_census(
        LOOP_COMMON_EXECUTION_STAGE_REGISTRY,
        session.identity.result_occurrence_id,
    )


def _loop_sat_safety_handoff(label):
    from scripts.function_tracer_pcode.equivalence.v2.production_signals import (
        SatSafetyBlockerProductionSignal,
    )

    return SatSafetyBlockerProductionSignal(
        "OBSERVED",
        "counterexample_analysis_safety_unproven",
        ("loop_model_bound_refutation", label),
        ("model_bound_refutation_requires_counterexample_safety", label),
        ("artifact", label),
        "loop-model-bound-refutation-handoff-v1",
    )


class _LoopSatHandoffRoute:
    def __init__(self, observed=()):
        self.observed = set(observed)

    @staticmethod
    def accepts_signal_type(signal_type):
        from scripts.function_tracer_pcode.equivalence.v2.production_signals import (
            SatSafetyBlockerProductionSignal,
        )

        return signal_type is SatSafetyBlockerProductionSignal

    def has_observed(self, _session, signal):
        return id(signal) in self.observed


def test_loop_sat_handoff_is_retained_when_encoder_returns_zero(monkeypatch):
    import scripts.function_tracer_pcode.equivalence.v2.production_signals as module

    handoff = _loop_sat_safety_handoff("encoder-zero")
    session = SimpleNamespace(
        domain_signal_state={"loop_sat_safety_handoffs": [handoff]},
        domain_signal_encoder=_LoopSatHandoffRoute(),
    )
    monkeypatch.setattr(module, "emit_sat_safety_signal", lambda *_a, **_k: 0)
    with pytest.raises(ValueError, match="neither emitted nor deduplicated"):
        module._consume_loop_sat_safety_handoffs(session)
    assert session.domain_signal_state["loop_sat_safety_handoffs"] == [handoff]


def test_loop_sat_handoff_is_retained_when_phase7_activation_fails(monkeypatch):
    import scripts.function_tracer_pcode.equivalence.v2.production_signals as module

    handoff = _loop_sat_safety_handoff("phase7-failure")
    session = SimpleNamespace(
        domain_signal_state={"loop_sat_safety_handoffs": [handoff]},
        domain_signal_encoder=_LoopSatHandoffRoute(),
    )

    def fail_activation(*_args, **_kwargs):
        raise RuntimeError("forced Phase 7 activation failure")

    monkeypatch.setattr(module, "emit_sat_safety_signal", fail_activation)
    with pytest.raises(RuntimeError, match="forced Phase 7 activation failure"):
        module._consume_loop_sat_safety_handoffs(session)
    assert session.domain_signal_state["loop_sat_safety_handoffs"] == [handoff]


def test_loop_sat_handoff_consumes_only_successful_prefix(monkeypatch):
    import scripts.function_tracer_pcode.equivalence.v2.production_signals as module

    first = _loop_sat_safety_handoff("first")
    second = _loop_sat_safety_handoff("second")
    session = SimpleNamespace(
        domain_signal_state={"loop_sat_safety_handoffs": [first, second]},
        domain_signal_encoder=_LoopSatHandoffRoute(),
    )
    results = iter((1, 0))
    monkeypatch.setattr(
        module, "emit_sat_safety_signal", lambda *_a, **_k: next(results)
    )
    with pytest.raises(ValueError, match="neither emitted nor deduplicated"):
        module._consume_loop_sat_safety_handoffs(session)
    assert session.domain_signal_state["loop_sat_safety_handoffs"] == [second]


def test_loop_sat_handoff_consumes_typed_duplicate_without_emit(monkeypatch):
    import scripts.function_tracer_pcode.equivalence.v2.production_signals as module

    handoff = _loop_sat_safety_handoff("typed-duplicate")
    session = SimpleNamespace(
        domain_signal_state={"loop_sat_safety_handoffs": [handoff]},
        domain_signal_encoder=_LoopSatHandoffRoute((id(handoff),)),
    )

    def unexpected_emit(*_args, **_kwargs):
        raise AssertionError("typed duplicate must not be emitted again")

    monkeypatch.setattr(module, "emit_sat_safety_signal", unexpected_emit)
    assert module._consume_loop_sat_safety_handoffs(session) == 0
    assert "loop_sat_safety_handoffs" not in session.domain_signal_state


def test_loop_sat_handoff_append_failure_allows_reemit_but_keeps_failure_authority(
    monkeypatch,
):
    import scripts.function_tracer_pcode.equivalence.v2.production_signals as module
    from scripts.function_tracer_pcode.equivalence.v2.phase7_runtime import (
        runtime_from_audited_manifest,
    )
    from scripts.function_tracer_pcode.equivalence.v2.pilot import (
        ProductionDualWritePilotConnector,
    )
    from scripts.function_tracer_pcode.equivalence.v2.reducer import (
        ShadowLifecycleReducer,
    )
    from scripts.function_tracer_pcode.equivalence.v2.sat_safety import (
        SAT_SAFETY_REASON_REGISTRY,
        SAT_SAFETY_RECOVERY_REGISTRY,
        SatSafetyPilotEncoder,
    )

    root = Path(__file__).resolve().parents[4]
    manifest = json.loads((root / (
        "artifacts/unknown_taxonomy_v2/phase7/producer-sites.json"
    )).read_text(encoding="utf-8"))
    safety_encoder = SatSafetyPilotEncoder()
    composite = CompositeProductionSignalEncoder({
        module.SatSafetyBlockerProductionSignal: safety_encoder,
    })
    connector = ProductionDualWritePilotConnector(
        ShadowLifecycleReducer(
            reason_registry=SAT_SAFETY_REASON_REGISTRY,
            recovery_registry=SAT_SAFETY_RECOVERY_REGISTRY,
        ),
        domain_signal_encoder=composite,
        phase7_runtime_factory=lambda identity: runtime_from_audited_manifest(
            manifest, identity
        ),
    )
    session = connector.begin({"case": "loop-sat-append-failure-retry"})
    handoff = _loop_sat_safety_handoff("real-encoder-append-failure")
    session.domain_signal_state["loop_sat_safety_handoffs"] = [handoff]
    real_emit_many = session.emit_many
    calls = {"count": 0}

    def fail_first_append(
        intents, commit_callback=None, *,
        phase7_execution_intents_prebuffered=False,
    ):
        calls["count"] += 1
        if calls["count"] == 1:
            raise RuntimeError("forced SAT safety stream append failure")
        return real_emit_many(
            intents,
            commit_callback,
            phase7_execution_intents_prebuffered=(
                phase7_execution_intents_prebuffered
            ),
        )

    monkeypatch.setattr(session, "emit_many", fail_first_append)
    with production_signal_scope(session):
        with pytest.raises(
            ValueError, match="neither emitted nor deduplicated"
        ):
            module._consume_loop_sat_safety_handoffs(session)
        assert session.recorder.event_count == 0
        assert not safety_encoder.has_observed(session, handoff)
        assert session.domain_signal_state["loop_sat_safety_handoffs"] == [
            handoff
        ]
        for key in (
            "sat_safety_observed",
            "sat_safety_completed",
            "sat_safety_pending_emission_transactions",
        ):
            assert key not in session.domain_signal_state
        runtime = session.phase7_runtime
        assert runtime._pending == {}
        assert runtime._materialized == []
        assert runtime._signal_transactions == {}
        assert runtime._discovery_factory._issued == {}
        assert runtime._discovery_factory._ordinals == {}
        assert session._phase7_signal_sites == {}
        assert session._phase7_signal_transactions == {}

        assert module._consume_loop_sat_safety_handoffs(session) == 1
    assert session.recorder.event_count == 1
    assert safety_encoder.has_observed(session, handoff)
    assert "loop_sat_safety_handoffs" not in session.domain_signal_state
    assert session.phase7_runtime._pending == {}
    assert len(session.phase7_runtime._materialized) == 1
    assert session.phase7_runtime._discovery_factory._ordinals == {
        "pairwise-loop-sat-safety-observed": 1
    }
    with pytest.raises(
        ValueError, match="production domain signal encoding is incomplete"
    ):
        connector.finish(
            session,
            SimpleNamespace(
                error_message=None,
                is_equivalent=None,
                failure_status=None,
                failure_message=None,
                is_timeout=lambda: False,
            ),
            case_id="loop-sat-append-failure-reemit",
        )


@pytest.mark.parametrize(
    ("status", "event_type"),
    (
        ("unknown", EventType.SOLVER_UNKNOWN),
        ("error", EventType.SOLVER_ERROR),
        ("timeout", EventType.SOLVER_TIMEOUT),
    ),
)
def test_loop_solver_nonproof_statuses_never_complete_q(
    monkeypatch, status, event_type
):
    import scripts.function_tracer_pcode.equivalence.v2.execution_authority as execution_module
    from scripts.function_tracer_pcode.equivalence.v2.execution_authority import (
        ExecutionAuthorityDeploymentPolicy,
        PINNED_SOLVER_EXECUTION_ISSUER,
        activate_execution_authority_deployment,
        install_execution_authority_signing_key,
    )
    from scripts.function_tracer_pcode.smt.interface import SolverResult, SolverStatus
    from scripts.function_tracer_pcode.smt.parallel import ParallelResult

    key_id = "loop-nonproof-" + status
    install_execution_authority_signing_key(key_id, status.encode() * 32)
    activate_execution_authority_deployment(ExecutionAuthorityDeploymentPolicy(
        "loop-nonproof-policy-" + status, 1, "test-owner", "test-source",
        key_id, (), 3600, "test-revocation",
    ))
    monkeypatch.setattr(
        execution_module,
        "_PINNED_PARALLEL_RUN_IMPL",
        lambda _runner, _query, timeout: ParallelResult(results=[
            SolverResult("z3", SolverStatus[status.upper()], elapsed_time=0.001),
        ]),
    )
    blocker, encoder, session, projection, query, membership, _ = (
        _loop_solver_runtime_fixture("loop-nonproof-result-" + status)
    )
    receipts = PINNED_SOLVER_EXECUTION_ISSUER.execute(
        registry=LOOP_COMMON_EXECUTION_STAGE_REGISTRY,
        result_occurrence_id=session.identity.result_occurrence_id,
        membership=membership,
        invocation_identity="loop-nonproof-invocation-" + status,
        first_invocation_ordinal=1,
        query=query.query_text,
        configured_timeout_ms=1000,
        query_authority=query,
        lifecycle_projection=projection,
    )
    batch = LoopSolverExecutionBatchSignal.from_issuer_results(
        blocker, query, membership, receipts, projection
    )
    intents = _plan_and_commit_loop_solver_batch(
        encoder,
        session,
        batch,
    )
    assert [item.event_type for item in intents] == [event_type]
    assert "loop_solver_unsat_completion_receipts" not in session.domain_signal_state
    PINNED_SOLVER_EXECUTION_ISSUER.seal_result_census(
        LOOP_COMMON_EXECUTION_STAGE_REGISTRY,
        session.identity.result_occurrence_id,
    )


@pytest.mark.parametrize(
    ("tail_status", "expects_terminal", "expected_open_requirements"),
    (
        ("unknown", False, 2),
        ("error", False, 2),
        ("timeout", True, 2),
        ("unsat", False, 1),
        ("sat", False, 2),
    ),
)
@pytest.mark.parametrize("reverse_batch_receipts", (False, True))
def test_loop_timeout_retry_history_uses_census_order_and_live_frontier(
    monkeypatch,
    tail_status,
    expects_terminal,
    expected_open_requirements,
    reverse_batch_receipts,
):
    import scripts.function_tracer_pcode.equivalence.v2.execution_authority as execution_module
    from scripts.function_tracer_pcode.equivalence.v2.execution_authority import (
        ExecutionAuthorityDeploymentPolicy,
        PINNED_SOLVER_EXECUTION_ISSUER,
        TerminalLifecycleProjectionAuthority,
        TerminalTimeoutSelectionReceipt,
        activate_execution_authority_deployment,
        install_execution_authority_signing_key,
    )
    from scripts.function_tracer_pcode.equivalence.v2.reducer import (
        ShadowLifecycleReducer,
    )
    from scripts.function_tracer_pcode.equivalence.v2.stream import (
        CauseObservedEventAuthority,
        EventIntent,
        EventRecorder,
    )
    from scripts.function_tracer_pcode.smt.interface import SolverResult, SolverStatus
    from scripts.function_tracer_pcode.smt.parallel import ParallelResult

    suffix = f"{tail_status}-{int(reverse_batch_receipts)}"
    key_id = "loop-retry-key-" + suffix
    install_execution_authority_signing_key(key_id, (suffix.encode() * 32)[:32])
    activate_execution_authority_deployment(ExecutionAuthorityDeploymentPolicy(
        "loop-retry-policy-" + suffix, 1, "test-owner", "test-source",
        key_id, (), 3600, "test-revocation",
    ))
    tail = SolverResult(
        "z3",
        SolverStatus[tail_status.upper()],
        elapsed_time=0.001,
        model={} if tail_status == "sat" else None,
    )
    monkeypatch.setattr(
        execution_module,
        "_PINNED_PARALLEL_RUN_IMPL",
        lambda _runner, _query, timeout: ParallelResult(results=[
            SolverResult("z3", SolverStatus.TIMEOUT, elapsed_time=timeout),
            tail,
        ]),
    )
    blocker, encoder, session, projection, query, membership, _ = (
        _loop_solver_runtime_fixture("loop-retry-result-" + suffix)
    )
    receipts = PINNED_SOLVER_EXECUTION_ISSUER.execute(
        registry=LOOP_COMMON_EXECUTION_STAGE_REGISTRY,
        result_occurrence_id=session.identity.result_occurrence_id,
        membership=membership,
        invocation_identity="loop-retry-invocation-" + suffix,
        first_invocation_ordinal=1,
        query=query.query_text,
        configured_timeout_ms=1000,
        query_authority=query,
        lifecycle_projection=projection,
    )
    supplied = tuple(reversed(receipts)) if reverse_batch_receipts else receipts
    batch = LoopSolverExecutionBatchSignal.from_issuer_results(
        blocker, query, membership, supplied, projection
    )
    intents = _plan_and_commit_loop_solver_batch(
        encoder,
        session,
        batch,
    )
    recorder = EventRecorder(
        stream_id="loop-retry-stream-" + suffix,
        result_occurrence_id=session.identity.result_occurrence_id,
        source_snapshot_fingerprint=session.identity.source_snapshot_fingerprint,
    )
    recorder.append(EventIntent(
        EventType.CAUSE_OBSERVED,
        CauseObservedEventAuthority(encoder.authority_for_signal(session, blocker)),
    ))
    for intent in intents:
        recorder.append(intent)
    stream = recorder.seal()
    reduction = ShadowLifecycleReducer(
        reason_registry=LOOP_REASON_REGISTRY,
        recovery_registry=LOOP_RECOVERY_REGISTRY,
    ).replay(stream)
    assert len(reduction.projection.q_open_base) == expected_open_requirements
    census = PINNED_SOLVER_EXECUTION_ISSUER.seal_result_census(
        LOOP_COMMON_EXECUTION_STAGE_REGISTRY,
        session.identity.result_occurrence_id,
    )
    expected_census_statuses = ["timeout", tail_status]
    if tail_status == "sat":
        expected_census_statuses.extend(("timeout", "sat"))
    assert [event.execution_receipt.observed_status for event in census.events] == (
        expected_census_statuses
    )
    terminal_projection = TerminalLifecycleProjectionAuthority.create(
        session.identity.result_occurrence_id,
        (row.proof_requirement_id for row in reduction.projection.q_open_base),
    )
    selection = TerminalTimeoutSelectionReceipt.select(
        LOOP_COMMON_EXECUTION_STAGE_REGISTRY,
        census,
        terminal_projection,
    )
    assert (selection is not None) is expects_terminal


def test_loop_connector_finalizes_open_ledger_and_selects_terminal_timeout(monkeypatch):
    import scripts.function_tracer_pcode.equivalence.v2.execution_authority as execution_module
    from scripts.function_tracer_pcode.equivalence.v2.execution_authority import (
        ExecutionAuthorityDeploymentPolicy,
        PINNED_SOLVER_EXECUTION_ISSUER,
        activate_execution_authority_deployment,
        install_execution_authority_signing_key,
    )
    from scripts.function_tracer_pcode.equivalence.v2.pilot import (
        ProductionDualWritePilotConnector,
    )
    from scripts.function_tracer_pcode.equivalence.v2.production_signals import (
        active_loop_requirement_for_signal,
        execute_loop_solver_rendered_query,
    )
    from scripts.function_tracer_pcode.equivalence.v2.reducer import (
        ShadowLifecycleReducer,
    )
    from scripts.function_tracer_pcode.equivalence.strategies.pairwise_query_executor import (
        render_loop_v2_solver_query,
    )
    from scripts.function_tracer_pcode.smt.interface import SolverResult, SolverStatus
    from scripts.function_tracer_pcode.smt.parallel import ParallelResult

    key_id = "loop-terminal-timeout-key"
    install_execution_authority_signing_key(key_id, b"t" * 32)
    activate_execution_authority_deployment(ExecutionAuthorityDeploymentPolicy(
        "loop-terminal-timeout-policy", 1, "test-owner", "test-source",
        key_id, (), 3600, "test-revocation",
    ))
    monkeypatch.setattr(
        execution_module,
        "_PINNED_PARALLEL_RUN_IMPL",
        lambda _runner, _query, timeout: ParallelResult(results=[
            SolverResult("z3", SolverStatus.TIMEOUT, elapsed_time=timeout),
        ]),
    )
    encoder = LoopRecurrencePilotEncoder()
    composite = CompositeProductionSignalEncoder({
        LoopBlockerProductionSignal: encoder,
        LoopSolverExecutionBatchSignal: encoder,
    })
    connector = ProductionDualWritePilotConnector(
        ShadowLifecycleReducer(
            reason_registry=LOOP_REASON_REGISTRY,
            recovery_registry=LOOP_RECOVERY_REGISTRY,
        ),
        domain_signal_encoder=composite,
    )
    session = connector.begin({"case": "loop-terminal-timeout"})
    blocker, _, _, _, exact_case, summary_case, left, right = _loop_exact_fixture()
    with production_signal_scope(session):
        assert session.emit_domain_signal(blocker) == 1
        requirement = active_loop_requirement_for_signal(
            blocker, "loop_exact_term_relation"
        )
        rendered = render_loop_v2_solver_query(
            blocker=blocker,
            requirement=requirement,
            analysis1=left,
            analysis2=right,
            case1=exact_case,
            case2=summary_case,
            pair_id="(0,1)",
            execution_identity_digest=session.identity.execution_identity_digest,
        )
        assert execute_loop_solver_rendered_query(
            blocker, rendered, configured_timeout_ms=1000
        ) == 1
    evidence = connector.finish(
        session,
        SimpleNamespace(
            error_message=None,
            is_equivalent=None,
            failure_status=None,
            failure_message=None,
            is_timeout=lambda: False,
        ),
        case_id="loop-terminal-timeout",
    )
    assert evidence.pilot_result.candidate.decision_receipt.outcome.value == "TIMEOUT"
    timeout_projection = evidence.pilot_result.reduction.projection
    assert len(timeout_projection.c_active_base) == 1
    assert len(timeout_projection.q_open_base) == 2
    assert len(
        evidence.pilot_result.reduction.snapshot.terminal_timeout_event_digests
    ) == 1
    assert evidence.pilot_result.bound_solver_event_count == 1
    assert len(evidence.execution_authority_evidence_bundles) == 1
    assert not PINNED_SOLVER_EXECUTION_ISSUER.has_open_result_ledger(
        LOOP_COMMON_EXECUTION_STAGE_REGISTRY,
        session.identity.result_occurrence_id,
    )


def test_loop_connector_materializes_unemitted_receipt_before_sealing(monkeypatch):
    import scripts.function_tracer_pcode.equivalence.v2.execution_authority as execution_module
    from scripts.function_tracer_pcode.equivalence.v2.execution_authority import (
        ExecutionAuthorityDeploymentPolicy,
        PINNED_SOLVER_EXECUTION_ISSUER,
        activate_execution_authority_deployment,
        install_execution_authority_signing_key,
    )
    from scripts.function_tracer_pcode.equivalence.v2.loop_recurrence import (
        _issue_loop_solver_query_authority,
    )
    from scripts.function_tracer_pcode.equivalence.v2.pilot import (
        ProductionDualWritePilotConnector,
    )
    from scripts.function_tracer_pcode.equivalence.v2.reducer import (
        ShadowLifecycleReducer,
    )
    from scripts.function_tracer_pcode.equivalence.strategies.pairwise_query_executor import (
        render_loop_v2_solver_query,
    )
    from scripts.function_tracer_pcode.smt.interface import SolverResult, SolverStatus
    from scripts.function_tracer_pcode.smt.parallel import ParallelResult

    key_id = "loop-unemitted-receipt-key"
    install_execution_authority_signing_key(key_id, b"u" * 32)
    activate_execution_authority_deployment(ExecutionAuthorityDeploymentPolicy(
        "loop-unemitted-receipt-policy", 1, "test-owner", "test-source",
        key_id, (), 3600, "test-revocation",
    ))
    monkeypatch.setattr(
        execution_module,
        "_PINNED_PARALLEL_RUN_IMPL",
        lambda _runner, _query, timeout: ParallelResult(results=[
            SolverResult("z3", SolverStatus.TIMEOUT, elapsed_time=timeout),
        ]),
    )
    encoder = LoopRecurrencePilotEncoder()
    composite = CompositeProductionSignalEncoder({
        LoopBlockerProductionSignal: encoder,
        LoopSolverExecutionBatchSignal: encoder,
    })
    connector = ProductionDualWritePilotConnector(
        ShadowLifecycleReducer(
            reason_registry=LOOP_REASON_REGISTRY,
            recovery_registry=LOOP_RECOVERY_REGISTRY,
        ),
        domain_signal_encoder=composite,
    )
    session = connector.begin({"case": "loop-unemitted-receipt"})
    blocker, _, _, _, exact_case, summary_case, left, right = _loop_exact_fixture()
    assert session.emit_domain_signal(blocker) == 1
    requirement = composite.loop_requirement_for_signal(
        session, blocker, "loop_exact_term_relation"
    )
    rendered = render_loop_v2_solver_query(
        blocker=blocker,
        requirement=requirement,
        analysis1=left,
        analysis2=right,
        case1=exact_case,
        case2=summary_case,
        pair_id="(0,1)",
        execution_identity_digest=session.identity.execution_identity_digest,
    )
    query = _issue_loop_solver_query_authority(rendered)
    context = composite.build_loop_execution_context(session, blocker, (query,))
    membership = context.membership_for(query)
    receipts = PINNED_SOLVER_EXECUTION_ISSUER.execute(
        registry=LOOP_COMMON_EXECUTION_STAGE_REGISTRY,
        result_occurrence_id=session.identity.result_occurrence_id,
        membership=membership,
        invocation_identity="loop-unemitted-receipt-invocation",
        first_invocation_ordinal=1,
        query=query.query_text,
        configured_timeout_ms=1000,
        query_authority=query,
        lifecycle_projection=context.lifecycle_projection,
    )
    assert len(receipts) == 1
    assert session.recorder.event_count == 1

    evidence = connector.finish(
        session,
        SimpleNamespace(
            error_message=None,
            is_equivalent=None,
            failure_status=None,
            failure_message=None,
            is_timeout=lambda: False,
        ),
        case_id="loop-unemitted-receipt",
    )
    assert evidence.pilot_result.candidate.decision_receipt.outcome.value == "TIMEOUT"
    assert evidence.pilot_result.bound_solver_event_count == 1
    assert not PINNED_SOLVER_EXECUTION_ISSUER.has_open_result_ledger(
        LOOP_COMMON_EXECUTION_STAGE_REGISTRY,
        session.identity.result_occurrence_id,
    )


def test_loop_sat_refutation_enters_phase6_1_safety_backlog(monkeypatch):
    import scripts.function_tracer_pcode.equivalence.v2.execution_authority as execution_module
    from scripts.function_tracer_pcode.equivalence.v2.execution_authority import (
        ExecutionAuthorityDeploymentPolicy,
        ModelBoundRelationalRefutationArtifact,
        activate_execution_authority_deployment,
        install_execution_authority_signing_key,
    )
    from scripts.function_tracer_pcode.equivalence.v2.pilot import (
        ProductionDualWritePilotConnector,
    )
    from scripts.function_tracer_pcode.equivalence.v2.production_signals import (
        SatSafetyBlockerProductionSignal,
        active_loop_requirement_for_signal,
        execute_loop_solver_rendered_query,
    )
    from scripts.function_tracer_pcode.equivalence.v2.reducer import (
        ShadowLifecycleReducer,
    )
    from scripts.function_tracer_pcode.equivalence.v2.registry import (
        SealedReasonRegistry,
        SealedRecoveryRegistry,
    )
    from scripts.function_tracer_pcode.equivalence.v2.sat_safety import (
        SAT_SAFETY_REASON_REGISTRY,
        SAT_SAFETY_RECOVERY_REGISTRY,
        SatSafetyPilotEncoder,
    )
    from scripts.function_tracer_pcode.equivalence.strategies.pairwise_query_executor import (
        render_loop_v2_solver_query,
    )
    from scripts.function_tracer_pcode.smt.interface import SolverResult, SolverStatus
    from scripts.function_tracer_pcode.smt.parallel import ParallelResult

    key_id = "loop-sat-phase6-1-key"
    install_execution_authority_signing_key(key_id, b"s" * 32)
    activate_execution_authority_deployment(ExecutionAuthorityDeploymentPolicy(
        "loop-sat-phase6-1-policy", 1, "test-owner", "test-source",
        key_id, (), 3600, "test-revocation",
    ))
    monkeypatch.setattr(
        execution_module,
        "_PINNED_PARALLEL_RUN_IMPL",
        lambda _runner, _query, timeout: ParallelResult(results=[
            SolverResult("z3", SolverStatus.SAT, elapsed_time=0.001, model={}),
        ]),
    )
    loop_encoder = LoopRecurrencePilotEncoder()
    safety_encoder = SatSafetyPilotEncoder()
    composite = CompositeProductionSignalEncoder({
        LoopBlockerProductionSignal: loop_encoder,
        LoopSolverExecutionBatchSignal: loop_encoder,
        SatSafetyBlockerProductionSignal: safety_encoder,
    })
    reason_registry = SealedReasonRegistry.build((
        *LOOP_REASON_REGISTRY.snapshot(),
        *SAT_SAFETY_REASON_REGISTRY.snapshot(),
    ))
    recovery_registry = SealedRecoveryRegistry.build((
        *LOOP_RECOVERY_REGISTRY.snapshot(),
        *SAT_SAFETY_RECOVERY_REGISTRY.snapshot(),
    ))
    connector = ProductionDualWritePilotConnector(
        ShadowLifecycleReducer(
            reason_registry=reason_registry,
            recovery_registry=recovery_registry,
        ),
        domain_signal_encoder=composite,
    )
    session = connector.begin({"case": "loop-sat-phase6-1"})
    blocker, _, _, _, exact_case, summary_case, left, right = _loop_exact_fixture()
    with production_signal_scope(session):
        assert session.emit_domain_signal(blocker) == 1
        requirement = active_loop_requirement_for_signal(
            blocker, "loop_exact_term_relation"
        )
        rendered = render_loop_v2_solver_query(
            blocker=blocker,
            requirement=requirement,
            analysis1=left,
            analysis2=right,
            case1=exact_case,
            case2=summary_case,
            pair_id="(0,1)",
            execution_identity_digest=session.identity.execution_identity_digest,
        )
        assert execute_loop_solver_rendered_query(
            blocker, rendered, configured_timeout_ms=1000
        ) == 1
    assert session.domain_signal_error_kinds == []
    artifacts = session.domain_signal_state[
        "loop_model_bound_refutation_artifacts"
    ]
    assert len(artifacts) == 1
    assert type(artifacts[0]) is ModelBoundRelationalRefutationArtifact
    evidence = connector.finish(
        session,
        SimpleNamespace(
            error_message=None,
            is_equivalent=None,
            failure_status=None,
            failure_message=None,
            is_timeout=lambda: False,
        ),
        case_id="loop-sat-phase6-1",
    )
    projection = evidence.pilot_result.reduction.projection
    assert evidence.pilot_result.candidate.decision_receipt.outcome.value == "UNKNOWN"
    assert len(projection.c_active_base) == 2
    assert len(projection.q_open_base) == 3
    assert {row.reason_id for row in projection.c_active_base} == {
        "loop_exact_summary_relation_unproven",
        "counterexample_analysis_safety_unproven",
    }


def _analysis(name="loop_fn"):
    return FunctionReturnAnalysis(
        function_name=name,
        entry_point="0x1000",
        parameters=[],
        returns=[],
        binary_id="binary-content-a",
    )


def _proposal(seed="seed-a", pattern="counted-loop"):
    return QuarantinedRecurrenceProposal(seed, pattern, (), ())


def _session(result_occurrence_id="result-loop-a"):
    return SimpleNamespace(
        identity=SimpleNamespace(
            result_occurrence_id=result_occurrence_id,
            source_snapshot_fingerprint="source-snapshot-a",
            execution_identity_digest="execution-a",
        ),
        domain_signal_state={},
    )


def test_loop_blocker_signal_direct_construction_is_rejected():
    with pytest.raises(TypeError, match="object-factory issued"):
        LoopBlockerProductionSignal(
            "recurrence_proposal_validation_unproven",
            IdentityScope.UNARY,
            "recurrence_proposal",
            ("target",),
            ("missing",),
            ("proposition",),
            ("surface",),
            ("active",),
            ("unary",),
            ("evidence",),
            "caller",
        )


def test_recurrence_proposal_signal_is_derived_from_exact_typed_objects():
    analysis = _analysis()
    proposal = _proposal()
    signal = LoopBlockerProductionSignal.from_recurrence_proposal(analysis, proposal)
    assert signal.reason_id == "recurrence_proposal_validation_unproven"
    assert signal.identity_scope is IdentityScope.UNARY
    assert signal.target_kind == "recurrence_proposal"
    assert signal.canonical_target_key == (
        "recurrence_proposal_target_v2",
        analysis.outcome_function_identity(),
        proposal.seed_core_digest,
        proposal.digest,
        "recurrence-successor-derivation-v2",
    )
    with pytest.raises(TypeError, match="exact function analysis"):
        LoopBlockerProductionSignal.from_recurrence_proposal(object(), proposal)
    with pytest.raises(TypeError, match="exact quarantined proposal"):
        LoopBlockerProductionSignal.from_recurrence_proposal(analysis, object())


def test_loop_encoder_materializes_one_active_cause_and_one_open_requirement():
    signal = LoopBlockerProductionSignal.from_recurrence_proposal(
        _analysis(), _proposal()
    )
    session = _session()
    encoder = LoopRecurrencePilotEncoder()
    intents = encoder(session, signal)
    assert len(intents) == 1
    assert intents[0].event_type is EventType.CAUSE_OBSERVED
    authority = intents[0].authority_payload.occurrence_authority
    assert authority.occurrence.reason_id == signal.reason_id
    assert authority.occurrence.identity_scope is IdentityScope.UNARY
    assert len(authority.occurrence.proof_requirement_ids) == 1
    assert authority.bound_contract.slot_bindings[0][1].proof_kind == (
        "recurrence_transition_termination_validation"
    )
    assert encoder(session, signal) == ()


def test_recurrence_same_cause_dedups_per_result_but_not_across_results():
    signal = LoopBlockerProductionSignal.from_recurrence_proposal(
        _analysis(), _proposal()
    )
    encoder = LoopRecurrencePilotEncoder()
    first = encoder(_session("result-a"), signal)[0].authority_payload.occurrence_authority.occurrence
    second = encoder(_session("result-b"), signal)[0].authority_payload.occurrence_authority.occurrence
    assert first.cause_id == second.cause_id
    assert first.occurrence_id != second.occurrence_id


def test_real_checker_recurrence_blocker_uses_exact_v2_reason():
    left = _analysis("left-loop")
    left.quarantined_recurrence_proposals = (_proposal(),)
    right = _analysis("right-loop")
    encoder = LoopRecurrencePilotEncoder()
    composite = CompositeProductionSignalEncoder({
        LoopBlockerProductionSignal: encoder,
    })

    class _Session:
        def __init__(self):
            self.identity = _session().identity
            self.domain_signal_state = {}
            self.domain_signal_encoder = composite
            self.intents = []

        def emit_domain_signal(self, signal):
            emitted = tuple(self.domain_signal_encoder(self, signal))
            self.intents.extend(emitted)
            return len(emitted)

    session = _Session()
    strategy_result = SimpleNamespace(
        unknown_reasons=[],
        is_equivalent=None,
        sat_pairs=0,
        counterexample_raw=None,
    )
    with production_signal_scope(session):
        reasons = EquivalenceChecker._attach_recurrence_proposal_blockers(
            strategy_result,
            left,
            right,
            branch_id="pairwise-branch-a",
        )
    assert [reason.reason_id for reason in reasons] == [
        "recurrence_proposal_validation_unproven"
    ]
    assert len(session.intents) == 1
    authority = session.intents[0].authority_payload.occurrence_authority
    assert authority.occurrence.reason_id == (
        "recurrence_proposal_validation_unproven"
    )
    assert strategy_result.is_equivalent is None


def _validated_side_promotion():
    from scripts.function_tracer_pcode.tests.unit.test_recurrence_proof_contract import (
        _content_bound_artifact,
    )

    source = _analysis("promoted-loop")
    seed = RecurrenceSeedCore(
        source.outcome_function_identity(), ("active",), (), ("pure",)
    )
    proposal = _proposal(seed.digest, "unit-step")
    premise = "a" * 64
    target = (
        "function_recurrence_promotion_v1",
        source.outcome_function_identity(),
        proposal.pattern_kind,
    )
    artifact = _content_bound_artifact(
        seed, proposal, premise, target, ("view", proposal.digest)
    )
    artifact = replace(
        artifact,
        producer_id="equivalence_recurrence_validator",
        payload={
            **artifact.payload,
            "proof_stage": "recurrence_validation_complete",
            "object_target_key": artifact.requirement_id.proof_target_key,
        },
    )
    binding = function_recurrence_binding_digest(
        seed.digest, proposal.digest, premise
    )
    entry = ValidatedUnaryArtifactEntry(
        artifact,
        UnaryArtifactDomain.RECURRENCE_SUMMARY_V1.value,
        premise,
        AnalysisSnapshot.from_function_analysis(source).semantic_fingerprint,
        seed.digest,
        "recurrence-summary-normalization-v1",
        True,
        True,
        premise_schema_id="function_unary_premise_v2",
        premise_codec_id="recurrence_digest_codec_v1",
        proposal_digest=proposal.digest,
        function_recurrence_binding_digest=binding,
    )
    successor = source.with_accepted_return_partition(
        [], reason=proposal.pattern_kind
    )
    return RecurrenceSidePromotion(
        "left", source, successor, proposal, seed, entry
    )


def test_recurrence_completion_signal_requires_exact_validated_promotion():
    side = _validated_side_promotion()
    signal = RecurrenceValidationCompletionSignal.from_side_promotion(side)
    assert signal.blocker.reason_id == "recurrence_proposal_validation_unproven"
    with pytest.raises(TypeError, match="promotion-factory issued"):
        RecurrenceValidationCompletionSignal(
            signal.blocker,
            side.source_analysis,
            side.successor_analysis,
            side.proposal,
            side.seed_core,
            side.entry,
        )
    with pytest.raises(TypeError, match="exact side promotion"):
        RecurrenceValidationCompletionSignal.from_side_promotion(object())


def test_recurrence_completion_rejects_inner_target_in_production_payload():
    side = _validated_side_promotion()
    requirement_target = side.entry.artifact.requirement_id.proof_target_key
    inner_target = dict(requirement_target[1:])["proof_target"]
    artifact = replace(
        side.entry.artifact,
        payload={
            **side.entry.artifact.payload,
            "object_target_key": inner_target,
        },
    )
    entry = replace(side.entry, artifact=artifact)
    with pytest.raises(
        ValueError, match="artifact payload target differs from its requirement"
    ):
        RecurrenceValidationCompletionSignal.from_side_promotion(
            replace(side, entry=entry)
        )


def test_pairwise_loop_signal_contract_is_dispatch_certificate_bound():
    from scripts.function_tracer_pcode.equivalence.strategies.pairwise_services.orchestration_1 import (
        dispatch_bound_observation_contract_digest,
    )

    dispatch = SimpleNamespace(
        prepared=SimpleNamespace(
            certificate=SimpleNamespace(
                observation_contract_digest="observation-contract-digest"
            )
        )
    )
    assert dispatch_bound_observation_contract_digest(
        {"observation_contract_digest": "observation-contract-digest"},
        dispatch,
    ) == "observation-contract-digest"
    with pytest.raises(ValueError, match="differs from dispatch"):
        dispatch_bound_observation_contract_digest(
            {"observation_contract_digest": "other-contract"}, dispatch
        )
    with pytest.raises(ValueError, match="requires a prepared dispatch"):
        dispatch_bound_observation_contract_digest({}, None)


def test_recurrence_completion_issues_binding_and_completes_exact_observed_q():
    side = _validated_side_promotion()
    blocker = LoopBlockerProductionSignal.from_recurrence_proposal(
        side.source_analysis, side.proposal
    )
    completion_signal = RecurrenceValidationCompletionSignal.from_side_promotion(side)
    session = _session()
    encoder = LoopRecurrencePilotEncoder()
    assert encoder(session, blocker)[0].event_type is EventType.CAUSE_OBSERVED
    completed = encoder(session, completion_signal)
    assert len(completed) == 1
    assert completed[0].event_type is EventType.REQUIREMENT_COMPLETED
    authorities = session.domain_signal_state["recurrence_completion_authorities"]
    assert len(authorities) == 1
    authority = authorities[0]
    assert type(authority) is RecurrenceValidationCompletionAuthority
    authority.validate()
    binding = authority.binding_receipt
    assert type(binding) is RecurrenceRequirementBindingReceipt
    assert binding.legacy_requirement_key == side.entry.artifact.requirement_id.to_key()
    assert binding.original_function_snapshot == (
        AnalysisSnapshot.from_function_analysis(side.source_analysis).semantic_fingerprint
    )
    assert binding.successor_analysis_view_identity == (
        side.successor_analysis.analysis_view_identity
    )
    assert binding.successor_partition_revision == 1
    assert encoder(session, completion_signal) == ()


def test_recurrence_completion_before_observation_is_rejected():
    signal = RecurrenceValidationCompletionSignal.from_side_promotion(
        _validated_side_promotion()
    )
    with pytest.raises(ValueError, match="no observed live occurrence"):
        LoopRecurrencePilotEncoder()(_session(), signal)


def test_recurrence_completion_rejects_stale_source_or_successor_lineage():
    side = _validated_side_promotion()
    stale_entry = replace(side.entry, function_snapshot_fingerprint="stale")
    with pytest.raises(ValueError, match="entry authority mismatch"):
        RecurrenceValidationCompletionSignal.from_side_promotion(
            replace(side, entry=stale_entry)
        )
    with pytest.raises(ValueError, match="successor lineage"):
        RecurrenceValidationCompletionSignal.from_side_promotion(
            replace(side, successor_analysis=side.source_analysis)
        )


def test_summary_overlap_signals_are_unary_and_bind_exact_same_function_peers():
    from scripts.function_tracer_pcode.analysis.summary_returns import (
        accept_summary_return_candidates,
    )
    from scripts.function_tracer_pcode.model import ReturnInfo
    from scripts.function_tracer_pcode.tests.unit.test_summary_return_candidates import (
        _analysis_with_exact_returns,
        _cond,
        _const,
        _empty_effect_summary,
        _n,
        _summary_const,
        _with_summary_proof,
    )

    analysis = _analysis_with_exact_returns(effect_summary=_empty_effect_summary())
    summary_return = _with_summary_proof(ReturnInfo(
        address="0x1008",
        value=_summary_const(2),
        conditions=[_cond("INT_SLESS", _const(0), _n())],
        pcode_identity="summary:n_positive",
    ))
    accepted = accept_summary_return_candidates(
        analysis,
        [analysis.returns[0], summary_return],
        summary_note="counted_loop_summary",
    )
    signals = summary_signals_from_acceptance(analysis, accepted)
    overlap = tuple(
        signal for signal in signals
        if signal.reason_id == "summary_return_overlap_value_equality_unproven"
    )
    assert overlap
    assert all(signal.identity_scope is IdentityScope.UNARY for signal in overlap)
    assert all(
        signal.canonical_target_key[0]
        == "same_function_summary_return_pair_v2"
        for signal in overlap
    )
    assert all(
        signal.canonical_target_key[1] == analysis.outcome_function_identity()
        for signal in overlap
    )
    assert len({authority_digest(signal.canonical_target_key) for signal in overlap}) == len(
        overlap
    )


def test_slice3_effect_prerequisite_suppresses_candidate_local_slice4_effect_cause():
    from scripts.function_tracer_pcode.analysis.summary_returns import (
        accept_summary_return_candidates,
    )
    from scripts.function_tracer_pcode.model import ReturnInfo
    from scripts.function_tracer_pcode.tests.unit.test_summary_return_candidates import (
        _analysis_with_exact_returns,
        _cond,
        _const,
        _n,
        _summary_const,
        _with_summary_proof,
    )

    analysis = _analysis_with_exact_returns(effect_summary=None)
    summary_return = _with_summary_proof(ReturnInfo(
        address="0x1008",
        value=_summary_const(2),
        conditions=[_cond("INT_SLESS", _const(1), _n())],
        pcode_identity="summary:n_gt_one",
    ))
    accepted = accept_summary_return_candidates(
        analysis,
        [*analysis.returns, summary_return],
        summary_note="counted_loop_summary",
    )
    assert any(
        item.source_code == "summary_effect_unmodeled:effect_summary_missing"
        for item in accepted.blocker_occurrences
    )
    signals = summary_signals_from_acceptance(analysis, accepted)
    assert not any(
        signal.reason_id == "summary_effect_model_incomplete" for signal in signals
    )
    slice3_signals = summary_effect_prerequisite_signals_from_acceptance(
        analysis, accepted
    )
    assert slice3_signals
    assert all(
        type(signal) is SummaryEffectPrerequisiteProductionSignal
        for signal in slice3_signals
    )
    assert {signal.reason_id for signal in slice3_signals} == {
        "effect_observation_coverage_incomplete"
    }
    session = _session("summary-effect-result")
    encoder = CallEffectPilotEncoder()
    intents = tuple(
        intent
        for signal in slice3_signals
        for intent in encoder(session, signal)
    )
    assert len(intents) == 1
    authority = intents[0].authority_payload.occurrence_authority
    assert authority.occurrence.identity_scope is IdentityScope.UNARY
    assert authority.occurrence.reason_id == (
        "effect_observation_coverage_incomplete"
    )
    assert len(authority.occurrence.proof_requirement_ids) == 1


def test_slice4_validation_artifact_is_source_and_relation_bound():
    from scripts.function_tracer_pcode.validation.unknown_taxonomy_audit import (
        build_inventory_review_template,
    )

    root = Path(__file__).resolve().parents[4]
    path = root / (
        "artifacts/unknown_taxonomy_v2/phase6/"
        "slice4_representative_validation.json"
    )
    payload = json.loads(path.read_text(encoding="utf-8"))
    saved_digest = payload.pop("artifact_digest")
    assert authority_digest(payload) == saved_digest
    assert payload["status"] == "fixed_review_go"

    current = build_inventory_review_template(root)
    live_inventory = json.loads((root / (
        "artifacts/unknown_taxonomy_v2/phase6/slice2_inventory_delta.json"
    )).read_text(encoding="utf-8"))
    assert payload["source_inventory"]["current_source"] == {
        "candidate_set_digest": current["candidate_set_digest"],
        "candidate_count": len(current["entries"]),
    }
    assert payload["source_inventory"]["current_source"] == (
        live_inventory["current_source"]
    )
    assert payload["source_inventory"]["live_delta"] == {
        "added": 0,
        "removed": 0,
    }
    assert payload["sealed_contract"]["reason_count"] == len(LOOP_REASON_SPECS)
    assert payload["sealed_contract"]["producer_stage_count"] == len(
        LOOP_PRODUCER_STAGE_SPECS
    )
    assert payload["sealed_contract"]["full_registry_digest"] == (
        LOOP_PRODUCER_STAGE_REGISTRY_DIGEST
    )
    assert payload["sealed_contract"]["common_registry_digest"] == (
        LOOP_COMMON_EXECUTION_STAGE_REGISTRY.normalized_registry_digest
    )

    for source, expected in payload["files"].items():
        assert hashlib.sha256((root / source).read_bytes()).hexdigest() == expected
    for binary, expected in payload["binary_inputs"].items():
        assert hashlib.sha256((root / binary).read_bytes()).hexdigest() == expected

    for case_id, evidence in payload["stored_run_outputs"].items():
        encoded_path = root / evidence["path"]
        encoded = encoded_path.read_bytes()
        assert hashlib.sha256(encoded).hexdigest() == evidence["encoded_sha256"]
        raw = gzip.decompress(base64.b64decode(b"".join(encoded.split())))
        assert hashlib.sha256(raw).hexdigest() == evidence["result_json_sha256"]
        result = json.loads(raw)
        expected = evidence["expected_projection"]
        promotion = result["recurrence_promotion_receipt"]
        assert result["is_equivalent"] is True
        assert result["is_timeout"] is False
        assert result["unknown_reasons"] == []
        assert result["solver_results"]["first_definitive"]["status"] == "UNSAT"
        assert promotion["state"] == "composed"
        assert promotion["promoted_successor_final_outcome"] == "EQ"
        assert promotion["promoted_successor_comparison_receipt_id"] == (
            expected["promoted_successor_comparison_receipt_id"]
        )
        assert {
            side: {
                "pattern_kind": promotion[side]["pattern_kind"],
                "transition_proposition_tags": promotion[side][
                    "transition_proposition_tags"
                ],
                "validated_artifact_imported": promotion[side][
                    "validated_artifact_imported"
                ],
            }
            for side in ("left", "right")
        } == expected["sides"]
        assert case_id in {
            row["case_id"] for row in payload["current_head_real_binary_runs"]
        }

    relations = payload["relation_evidence"]
    assert relations["loop_exact_observed"] == {
        "c_active": 1,
        "q_open": 2,
    }
    assert relations["loop_exact_term_completed"] == {
        "c_active": 1,
        "q_open": 1,
    }
    assert relations["loop_exact_guard_completed"] == {
        "c_active": 0,
        "q_open": 0,
    }
    assert relations["terminal_solver_timeout"] == {
        "final_outcome": "TIMEOUT",
        "c_active": 1,
        "q_open": 2,
        "terminal_timeout_events": 1,
    }
    assert relations["solver_sat_safety_handoff"] == {
        "final_outcome": "UNKNOWN",
        "c_active": 2,
        "q_open": 3,
    }
    assert relations["timeout_then_unsat_and_guard_proof"] == {
        "final_outcome": "EQUIVALENT_ELIGIBLE",
        "c_active": 0,
        "q_open": 0,
        "observed_nonterminal_timeout_events": 1,
    }

    before_after = payload["before_after"]
    assert all(
        row["before"]["decision"] == row["after"]["decision"] == "EQUIVALENT"
        and row["before"]["unknown_reason_count"] == 0
        and row["after"]["unknown_reason_count"] == 0
        for row in before_after["default_off_current_head_runs"]
    )
    canonical = before_after["typed_integration_contract"]
    assert canonical["terminal_solver_timeout"]["before"]["decision"] == "UNKNOWN"
    assert canonical["terminal_solver_timeout"]["after"] == {
        "decision": "TIMEOUT",
        "reason_ids": ["loop_exact_summary_relation_unproven"],
        "unique_active_causes": 1,
        "open_requirements": 2,
        "terminal_timeout_events": 1,
    }
    assert canonical["solver_sat_safety_handoff"]["after"] == {
        "decision": "UNKNOWN",
        "reason_ids": [
            "loop_exact_summary_relation_unproven",
            "counterexample_analysis_safety_unproven",
        ],
        "unique_active_causes": 2,
        "open_requirements": 3,
    }
    assert canonical["timeout_then_unsat_and_guard_proof"]["after"] == {
        "lifecycle_eligibility": "EQUIVALENT_ELIGIBLE",
        "reason_ids": [],
        "unique_active_causes": 0,
        "open_requirements": 0,
        "observed_nonterminal_timeout_events": 1,
    }

    assert payload["validation"]["related_contract_suite"] == "440 passed"
    assert payload["validation"]["real_binary_matrix"] == "4 passed"
