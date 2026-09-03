# -*- coding: utf-8 -*-

import hashlib
from unittest.mock import Mock

import pytest

from scripts.function_tracer_pcode.checker.attempts import record_attempt_from_result
from scripts.function_tracer_pcode.checker.checker import EquivalenceChecker
from scripts.function_tracer_pcode.checker.debug_trace import DebugTrace
from scripts.function_tracer_pcode.checker.result import EquivalenceResult
from scripts.function_tracer_pcode.proof.strategies.base import StrategyResult
from scripts.function_tracer_pcode.proof.strategies.monolithic import MonolithicStrategy
from scripts.function_tracer_pcode.checker.unknown_reason import (
    _UNKNOWN_REASON_REGISTRY,
    _UNKNOWN_RECOVERY_PLAN_REGISTRY,
    UnknownCountKind,
    UnknownRecoveryAction,
    UnknownRecoveryActionStatus,
    UnknownRecoveryProofObligation,
    UnknownReasonRecord,
    UnknownRecoveryProofKind,
    UnknownReasonId,
    build_proof_obligation_id,
    build_unknown_recovery_actions,
    get_unknown_recovery_plan,
    get_unknown_reason_definition,
    make_unknown_reason,
    make_internal_v2_reason_diagnostic,
    make_production_unknown_reason,
    summarize_unknown_recovery_backlog,
)


def test_internal_v2_reason_diagnostic_accepts_only_exact_v2_reason_ids():
    record = make_internal_v2_reason_diagnostic(
        "expression_semantics_unsupported",
        stage="S_PAIRWISE",
        detail="unsupported intrinsic",
    )
    assert record.reason_id == "expression_semantics_unsupported"
    assert record.reason_class == "operational_gap"
    assert record.decision_effect == "blocks_decision"
    assert UnknownReasonRecord.from_dict(record.to_dict()) == record

    with pytest.raises(ValueError, match="reader-only"):
        make_internal_v2_reason_diagnostic("unresolved_expression")
    with pytest.raises(KeyError, match="unknown exact v2 reason ID"):
        make_internal_v2_reason_diagnostic("made_up_reason")

    with pytest.raises(TypeError, match="exact issuer"):
        make_production_unknown_reason("expression_semantics_unsupported", projection_factory=None)
from scripts.function_tracer_pcode.proof.strategies.pairwise_models import QueryResult
from scripts.function_tracer_pcode.proof.strategies.pairwise_query_executor import (
    solve_query_internal,
    solve_query_twostage,
)
from scripts.function_tracer_pcode.core import Expression
from scripts.function_tracer_pcode.smt import ParallelResult, SolverResult, SolverStatus
from conftest import create_mock_analysis


def _unknown_solver_result() -> ParallelResult:
    return ParallelResult(
        results=[
            SolverResult(
                solver_name="mock",
                status=SolverStatus.UNKNOWN,
                elapsed_time=0.01,
            )
        ]
    )


def _nested_contains(value, needle) -> bool:
    if value == needle:
        return True
    if isinstance(value, (tuple, list)):
        return any(_nested_contains(item, needle) for item in value)
    if isinstance(value, dict):
        return any(_nested_contains(key, needle) or _nested_contains(item, needle) for key, item in value.items())
    return False


def test_unknown_reason_record_has_plan13_schema_fields():
    record = make_unknown_reason(
        UnknownReasonId.RETURN_WIDTH_BRIDGE_MISSING,
        stage="S_PAIRWISE",
        pair_or_case="(0,1)",
        evidence_refs=("return_32", "return_64"),
    )

    payload = record.to_dict()

    assert {
        "reason_id",
        "reason_class",
        "decision_effect",
        "reason_scope",
        "aggregation_unit",
        "stage",
        "pair_or_case",
        "evidence_refs",
        "recovery_proof_kind",
        "target_regression",
    }.issubset(payload)
    assert payload["reason_id"] == UnknownReasonId.RETURN_WIDTH_BRIDGE_MISSING.value
    assert payload["recovery_proof_kind"] == UnknownRecoveryProofKind.ABI_RELATION_HIGH_BIT_PROOF.value
    assert payload["count_kind"] == UnknownCountKind.REASON_RECORD.value


def test_unknown_reason_registry_normalizes_scoped_reason_text():
    record = make_unknown_reason("function1:return_coverage_gap")

    assert record.reason_id == UnknownReasonId.RETURN_COVERAGE_GAP.value
    assert get_unknown_reason_definition(record.reason_id).reason_id == record.reason_id


def test_unknown_reason_registry_rejects_free_form_substring_matches():
    record = make_unknown_reason("foo_return_coverage_gap_bar")

    assert record.reason_id == UnknownReasonId.UNKNOWN.value
    assert record.detail == "foo_return_coverage_gap_bar"
    assert record.evidence_refs[0] == "foo_return_coverage_gap_bar"


def test_recovery_proof_kind_rejects_unregistered_values():
    record = make_unknown_reason(
        UnknownReasonId.RETURN_WIDTH_BRIDGE_MISSING,
        recovery_proof_kind="typo",
    )

    assert record.recovery_proof_kind == UnknownRecoveryProofKind.NONE.value
    assert record.detail == "invalid recovery_proof_kind: typo"
    assert record.evidence_refs[0] == "invalid_recovery_proof_kind:typo"


def test_recovery_fallback_reason_ids_are_registered_not_solver_timeout():
    normalization = make_unknown_reason(UnknownReasonId.NORMALIZATION_NO_CHANGE)
    rewrite = make_unknown_reason(UnknownReasonId.SOLVER_PROVEN_REWRITE_PROOF_FAILED)

    assert normalization.reason_id == UnknownReasonId.NORMALIZATION_NO_CHANGE.value
    assert rewrite.reason_id == UnknownReasonId.SOLVER_PROVEN_REWRITE_PROOF_FAILED.value
    assert normalization.reason_id != UnknownReasonId.SOLVER_UNKNOWN_TIMEOUT.value
    assert rewrite.reason_id != UnknownReasonId.SOLVER_UNKNOWN_TIMEOUT.value


def test_plan15_recovery_plan_maps_core_reasons_to_required_proofs():
    return_width = get_unknown_recovery_plan(UnknownReasonId.RETURN_WIDTH_BRIDGE_MISSING)
    recoverable_partial = get_unknown_recovery_plan(UnknownReasonId.RECOVERABLE_PARTIAL)
    readonly_identity = get_unknown_recovery_plan(UnknownReasonId.READONLY_IDENTITY_MISSING)
    method_b = get_unknown_recovery_plan(UnknownReasonId.METHOD_B_CLOSURE_BLOCKED)
    sat_unsafety = get_unknown_recovery_plan(UnknownReasonId.SAT_UNSAFETY)

    assert [obligation.proof_kind for obligation in return_width.proof_obligations] == [
        UnknownRecoveryProofKind.ABI_RELATION_PROOF.value,
        UnknownRecoveryProofKind.HIGH_BIT_PROOF.value,
    ]
    assert [obligation.required_evidence for obligation in return_width.proof_obligations] == [
        ("calling_convention", "return_storage", "narrow_return_width"),
        ("producer_width", "extension_semantics", "high_bits_irrelevant_or_equal"),
    ]
    assert [obligation.proof_kind for obligation in recoverable_partial.proof_obligations] == [
        UnknownRecoveryProofKind.PATH_SENSITIVE_ARGUMENT_MERGE.value,
    ]
    assert [obligation.required_evidence for obligation in recoverable_partial.proof_obligations] == [
        ("callsite_guard_partition", "argument_value_by_path", "callee_parameter_storage"),
    ]
    assert [obligation.proof_kind for obligation in readonly_identity.proof_obligations] == [
        UnknownRecoveryProofKind.STORAGE_BACKED_IDENTITY_PROPAGATION.value,
    ]
    assert [obligation.required_evidence for obligation in readonly_identity.proof_obligations] == [
        ("object_storage_identity", "count_identity", "guard_implication", "finite_witness"),
    ]
    assert [obligation.proof_kind for obligation in method_b.proof_obligations] == [
        UnknownRecoveryProofKind.PROOF_BACKED_COVERING_CASE.value,
        UnknownRecoveryProofKind.GUARD_PARTITION_COMPLETION.value,
    ]
    assert [obligation.required_evidence for obligation in method_b.proof_obligations] == [
        ("seed_compensation", "term_sequence", "pure_side_effect_profile"),
        ("guard_partition", "partition_coverage_proof"),
    ]
    assert [obligation.proof_kind for obligation in sat_unsafety.proof_obligations] == [
        UnknownRecoveryProofKind.SAT_UNSAFETY_RESOLUTION.value,
    ]
    assert [obligation.required_evidence for obligation in sat_unsafety.proof_obligations] == [
        ("counterexample_replay", "active_unsafety_discharge", "coverage_effect_safety"),
    ]


def test_plan16_operational_backlog_reasons_have_registered_actions():
    reason_ids = (
        UnknownReasonId.LOOP_SUMMARY_PROOF_MISSING,
        UnknownReasonId.RETURN_COVERAGE_GAP,
        UnknownReasonId.RETURN_COVERAGE_INCONCLUSIVE,
        UnknownReasonId.SAT_UNSAFETY,
        UnknownReasonId.UNRESOLVED_EXPRESSION,
        UnknownReasonId.SOLVER_UNKNOWN_TIMEOUT,
        UnknownReasonId.NORMALIZATION_NO_CHANGE,
        UnknownReasonId.SOLVER_PROVEN_REWRITE_NO_CHANGE,
        UnknownReasonId.SOLVER_PROVEN_REWRITE_PROOF_FAILED,
    )

    for reason_id in reason_ids:
        actions = build_unknown_recovery_actions([make_unknown_reason(reason_id)])
        assert actions
        assert {action.status for action in actions} == {
            UnknownRecoveryActionStatus.PLANNED.value,
        }
        assert all(action.proof_stage != "unspecified" for action in actions)
        assert all(action.required_evidence for action in actions)
        assert {action.target_regression for action in actions} == {reason_id.value}


def test_unresolved_expression_recovery_plan_tracks_typed_lowering_work():
    target = ("unresolved_expression", ("pair", "(0,0)"), ("object", "expr"))
    record = make_unknown_reason(
        UnknownReasonId.UNRESOLVED_EXPRESSION,
        stage="S_PAIRWISE",
        pair_or_case="(0,0)",
        evidence_kind="unresolved_expression_safety",
        object_target_key=target,
    )
    actions = build_unknown_recovery_actions([record])
    plan = get_unknown_recovery_plan(UnknownReasonId.UNRESOLVED_EXPRESSION)

    assert [obligation.proof_stage for obligation in plan.proof_obligations] == [
        "typed_expression_lowering",
        "type_normalization",
    ]
    assert [action.proof_stage for action in actions] == [
        "typed_expression_lowering",
        "type_normalization",
    ]
    assert {action.proof_kind for action in actions} == {
        UnknownRecoveryProofKind.SOLVER_RETRY_OR_NORMALIZATION.value,
    }
    assert {action.status for action in actions} == {
        UnknownRecoveryActionStatus.PLANNED.value,
    }
    assert all(action.object_target_key == target for action in actions)
    assert all(action.proof_obligation_id for action in actions)
    assert actions[0].proof_obligation_id == build_proof_obligation_id(
        UnknownReasonId.UNRESOLVED_EXPRESSION,
        "typed_expression_lowering",
        UnknownRecoveryProofKind.SOLVER_RETRY_OR_NORMALIZATION,
        "unresolved_expression_safety",
        target,
    )


def test_solver_timeout_reason_carries_full_query_proof_target():
    strategy = MonolithicStrategy(Mock(), Mock())
    left = create_mock_analysis("fc_long_branch_dispatch")
    right = create_mock_analysis("fc_long_branch_dispatch")
    left.binary_id = "B8"
    right.binary_id = "B9"
    query = "(check-sat)"

    target = strategy._solver_timeout_object_target_key(
        analysis1=left,
        analysis2=right,
        stage="S_MONOLITHIC_FALLBACK",
        query=query,
        timeout_seconds=10,
        solver_name="Z3",
    )
    record = make_unknown_reason(
        UnknownReasonId.SOLVER_UNKNOWN_TIMEOUT,
        stage="S_MONOLITHIC_FALLBACK",
        evidence_kind="query_hash",
        object_target_key=target,
    )
    actions = build_unknown_recovery_actions([record])

    assert target[0] == "solver_timeout"
    assert ("pair", "B8_B9") in target
    assert ("query_hash", hashlib.sha256(query.encode("utf-8")).hexdigest()) in target
    assert ("timeout_budget_seconds", 10) in target
    assert record.proof_obligation_id == build_proof_obligation_id(
        UnknownReasonId.SOLVER_UNKNOWN_TIMEOUT,
        "solver_timeout_retry",
        UnknownRecoveryProofKind.SOLVER_RETRY_OR_NORMALIZATION,
        "query_hash",
        target,
    )
    assert actions[0].object_target_key == target
    assert actions[0].proof_obligation_id == record.proof_obligation_id
    assert actions[0].required_evidence == (
        "query_hash",
        "timeout_budget",
        "solver_options",
        "normalized_query",
    )
    assert not _nested_contains(target, getattr(left.function_ref, "program_id", None))


def test_solver_timeout_target_uses_parallel_solver_metadata_over_fallback_name():
    strategy = MonolithicStrategy(Mock(), Mock())
    left = create_mock_analysis("fc_long_branch_dispatch")
    right = create_mock_analysis("fc_long_branch_dispatch")
    left.binary_id = "B8"
    right.binary_id = "B9"
    parallel_result = ParallelResult(
        results=[
            SolverResult(
                solver_name="CVC5",
                status=SolverStatus.TIMEOUT,
                elapsed_time=10.0,
            )
        ]
    )

    target = strategy._solver_timeout_object_target_key(
        analysis1=left,
        analysis2=right,
        stage="S_MONOLITHIC_FALLBACK",
        query="(check-sat)",
        timeout_seconds=10,
        solver_name="Z3",
        parallel_result=parallel_result,
    )

    assert ("solver_options", ("solver", "CVC5"), ("timeout_seconds", 10)) in target
    assert ("solver_options", ("solver", "Z3"), ("timeout_seconds", 10)) not in target


def test_solver_timeout_target_records_multiple_solver_names_stably():
    strategy = MonolithicStrategy(Mock(), Mock())
    left = create_mock_analysis("fc_long_branch_dispatch")
    right = create_mock_analysis("fc_long_branch_dispatch")
    parallel_result = ParallelResult(
        results=[
            SolverResult("Yices2", SolverStatus.UNKNOWN),
            SolverResult("CVC5", SolverStatus.TIMEOUT),
            SolverResult("Yices2", SolverStatus.TIMEOUT),
        ]
    )

    target = strategy._solver_timeout_object_target_key(
        analysis1=left,
        analysis2=right,
        stage="S_MONOLITHIC_FALLBACK",
        query="(check-sat)",
        timeout_seconds=10,
        parallel_result=parallel_result,
    )

    assert ("solver_options", ("solvers", ("CVC5", "Yices2")), ("timeout_seconds", 10)) in target


def test_solver_timeout_target_requires_actual_parallel_solver_metadata():
    strategy = MonolithicStrategy(Mock(), Mock())
    left = create_mock_analysis("fc_long_branch_dispatch")
    right = create_mock_analysis("fc_long_branch_dispatch")
    parallel_result = ParallelResult(results=[], is_equivalent=None)

    target = strategy._solver_timeout_object_target_key(
        analysis1=left,
        analysis2=right,
        stage="S_MONOLITHIC_FALLBACK",
        query="(check-sat)",
        timeout_seconds=10,
        solver_name="Z3",
        parallel_result=parallel_result,
    )
    record = make_unknown_reason(
        UnknownReasonId.SOLVER_UNKNOWN_TIMEOUT,
        stage="S_MONOLITHIC_FALLBACK",
        evidence_kind="query_hash",
        object_target_key=target,
    )
    actions = build_unknown_recovery_actions([record])

    assert target is None
    assert record.object_target_key is None
    assert record.proof_obligation_id is None
    assert actions[0].object_target_key is None
    assert actions[0].proof_obligation_id is None


def test_legacy_recovery_action_inherits_known_reason_tuple_defaults():
    action = UnknownRecoveryAction.from_dict(
        {
            "reason_id": UnknownReasonId.RETURN_COVERAGE_INCONCLUSIVE.value,
            "proof_kind": UnknownRecoveryProofKind.RETURN_COVERAGE_COMPLETION.value,
            "proof_stage": "return_coverage_smt_disambiguation",
            "status": UnknownRecoveryActionStatus.PLANNED.value,
            "stage": "S_PAIRWISE",
            "evidence_refs": ["function2:return_coverage_inconclusive"],
        }
    )

    assert action.decision_effect == "blocks_decision"
    assert action.reason_scope == "function"
    assert action.aggregation_unit == "function"
    assert action.target_regression == "return_coverage_inconclusive"


def test_unknown_legacy_recovery_action_keeps_diagnostic_defaults():
    action = UnknownRecoveryAction.from_dict({"proof_stage": "unspecified"})

    assert action.reason_id == UnknownReasonId.UNKNOWN.value
    assert action.decision_effect == "diagnostic_only"
    assert action.reason_scope == "global"
    assert action.aggregation_unit == "result"
    assert action.target_regression is None


def test_recovery_kind_reasons_all_have_registered_plans():
    definitions = dict(_UNKNOWN_REASON_REGISTRY)
    plans = dict(_UNKNOWN_RECOVERY_PLAN_REGISTRY)

    missing = sorted(
        reason_id
        for reason_id, definition in definitions.items()
        if definition.recovery_proof_kind != UnknownRecoveryProofKind.NONE.value
        and reason_id not in plans
    )

    assert missing == []


def test_unknown_reason_record_serializes_recovery_proof_obligations():
    record = make_unknown_reason(UnknownReasonId.RETURN_WIDTH_BRIDGE_MISSING)
    payload = record.to_dict()
    roundtrip = UnknownReasonRecord.from_dict(payload)

    assert payload["recovery_proof_kind"] == UnknownRecoveryProofKind.ABI_RELATION_HIGH_BIT_PROOF.value
    assert [
        obligation["proof_stage"]
        for obligation in payload["recovery_proof_obligations"]
    ] == ["abi_relation", "high_bit_relation"]
    assert [
        obligation.proof_kind
        for obligation in roundtrip.recovery_proof_obligations
    ] == [
        UnknownRecoveryProofKind.ABI_RELATION_PROOF.value,
        UnknownRecoveryProofKind.HIGH_BIT_PROOF.value,
    ]


def test_equivalence_blocking_unsafety_can_emit_pending_call_effect_proof_obligation():
    record = make_unknown_reason(
        UnknownReasonId.EQUIVALENCE_BLOCKING_UNSAFETY,
        stage="S_PAIRWISE",
        evidence_refs=("function1:effect_call_argument_evidence_incomplete",),
        recovery_proof_kind=UnknownRecoveryProofKind.CALL_EFFECT_SUMMARY_PROOF,
        recovery_proof_obligations=(
            UnknownRecoveryProofObligation.create(
                UnknownRecoveryProofKind.CALL_EFFECT_SUMMARY_PROOF,
                "object_evidence_collected",
                required_evidence=(
                    "call_effect_summary",
                    "runtime_ref",
                    "callsite_storage",
                ),
            ),
        ),
        evidence_kind="call_effect_summary",
        object_target_key=("deferred_call_site", 1, 0x401000, ("pcode_op", 0x401020, 7, 0, None, "CALL")),
        recovery_action="call_effect_summary_proof_required",
        action_status=UnknownRecoveryActionStatus.PENDING_PROOF,
    )

    payload = record.to_dict()
    actions = build_unknown_recovery_actions([record])

    assert payload["count_kind"] == UnknownCountKind.REASON_RECORD.value
    assert payload["proof_stage"] == "object_evidence_collected"
    assert payload["evidence_kind"] == "call_effect_summary"
    assert payload["object_target_key"] == (
        "deferred_call_site",
        1,
        0x401000,
        ("pcode_op", 0x401020, 7, 0, None, "CALL"),
    )
    assert payload["recovery_action"] == "call_effect_summary_proof_required"
    assert payload["action_status"] == UnknownRecoveryActionStatus.PENDING_PROOF.value
    assert actions[0].count_kind == UnknownCountKind.PROOF_ACTION.value
    assert actions[0].status == UnknownRecoveryActionStatus.PENDING_PROOF.value
    assert actions[0].proof_stage == "object_evidence_collected"
    assert actions[0].evidence_kind == "call_effect_summary"
    assert actions[0].proof_obligation_id == (
        "equivalence_blocking_unsafety",
        "object_evidence_collected",
        "call_effect_summary_proof",
        "call_effect_summary",
        (
            "deferred_call_site",
            1,
            0x401000,
            ("pcode_op", 0x401020, 7, 0, None, "CALL"),
        ),
    )


def test_proof_obligation_id_full_key_distinguishes_evidence_and_object_target():
    base_target = (
        "runtime_ref",
        "B10",
        ("function_ref", ("function", 1, 0x401000)),
        ("pcode_op", "ram", 0x401020, "ram", 0x401020, 7, "CALLIND", 0),
        ("argument", 0, ("register", "a0", 8)),
    )
    argument_one_target = (
        "runtime_ref",
        "B10",
        ("function_ref", ("function", 1, 0x401000)),
        ("pcode_op", "ram", 0x401020, "ram", 0x401020, 7, "CALLIND", 0),
        ("argument", 1, ("register", "a1", 8)),
    )

    call_effect_id = build_proof_obligation_id(
        UnknownReasonId.EQUIVALENCE_BLOCKING_UNSAFETY,
        "object_evidence_collected",
        UnknownRecoveryProofKind.CALL_EFFECT_SUMMARY_PROOF,
        "call_effect_summary",
        base_target,
    )
    runtime_ref_id = build_proof_obligation_id(
        UnknownReasonId.EQUIVALENCE_BLOCKING_UNSAFETY,
        "object_evidence_collected",
        UnknownRecoveryProofKind.CALL_EFFECT_SUMMARY_PROOF,
        "runtime_ref",
        base_target,
    )
    argument_one_id = build_proof_obligation_id(
        UnknownReasonId.EQUIVALENCE_BLOCKING_UNSAFETY,
        "object_evidence_collected",
        UnknownRecoveryProofKind.CALL_EFFECT_SUMMARY_PROOF,
        "call_effect_summary",
        argument_one_target,
    )

    assert call_effect_id != runtime_ref_id
    assert call_effect_id != argument_one_id
    assert call_effect_id == (
        "equivalence_blocking_unsafety",
        "object_evidence_collected",
        "call_effect_summary_proof",
        "call_effect_summary",
        base_target,
    )


def test_unknown_recovery_backlog_groups_required_proofs_by_reason():
    summary = summarize_unknown_recovery_backlog(
        [
            make_unknown_reason(
                UnknownReasonId.RETURN_WIDTH_BRIDGE_MISSING,
                pair_or_case="(0,0)",
            ),
            make_unknown_reason(
                UnknownReasonId.METHOD_B_CLOSURE_BLOCKED,
                pair_or_case="(0,1)",
            ),
        ]
    )

    assert summary[UnknownReasonId.RETURN_WIDTH_BRIDGE_MISSING.value]["proof_obligation_counts"] == {
        UnknownRecoveryProofKind.ABI_RELATION_PROOF.value: 1,
        UnknownRecoveryProofKind.HIGH_BIT_PROOF.value: 1,
    }
    assert summary[UnknownReasonId.METHOD_B_CLOSURE_BLOCKED.value]["proof_obligation_counts"] == {
        UnknownRecoveryProofKind.PROOF_BACKED_COVERING_CASE.value: 1,
        UnknownRecoveryProofKind.GUARD_PARTITION_COMPLETION.value: 1,
    }


def test_strategy_and_equivalence_result_serialize_typed_unknown_reasons():
    strategy_result = StrategyResult(
        is_equivalent=None,
        solver_results=_unknown_solver_result(),
        unknown_pairs=1,
        total_pairs=1,
        unknown_reasons=[
            make_unknown_reason(
                UnknownReasonId.UNRESOLVED_VALUE_EXPRESSION,
                stage="S_PAIRWISE",
                pair_or_case="(0,0)",
            )
        ],
    )
    result = EquivalenceResult(
        is_equivalent=None,
        function1_name="left",
        function2_name="right",
        binary1_name="left.bin",
        binary2_name="right.bin",
        solver_results=strategy_result.solver_results,
        pairwise_stats={
            "total_pairs": strategy_result.total_pairs,
            "unsat_pairs": strategy_result.unsat_pairs,
            "sat_pairs": strategy_result.sat_pairs,
            "unknown_pairs": strategy_result.unknown_pairs,
            "error_pairs": strategy_result.error_pairs,
        },
        unknown_reasons=strategy_result.unknown_reasons,
    )

    payload = result.to_dict()

    assert payload["unknown_reasons"][0]["reason_id"] == UnknownReasonId.UNRESOLVED_VALUE_EXPRESSION.value
    assert payload["unknown_reasons"][0]["pair_or_case"] == "(0,0)"


def test_equivalence_result_serializes_unknown_recovery_backlog():
    result = EquivalenceResult(
        is_equivalent=None,
        function1_name="left",
        function2_name="right",
        binary1_name="left.bin",
        binary2_name="right.bin",
        solver_results=_unknown_solver_result(),
        unknown_reasons=[
            make_unknown_reason(
                UnknownReasonId.RECOVERABLE_PARTIAL,
                stage="S_EFFECT_SUMMARY",
                pair_or_case="left",
            ),
            make_unknown_reason(
                UnknownReasonId.READONLY_IDENTITY_MISSING,
                stage="S_PAIRWISE",
                pair_or_case="(0,0)",
            ),
        ],
    )

    backlog = result.to_dict()["unknown_recovery_backlog"]

    assert backlog[UnknownReasonId.RECOVERABLE_PARTIAL.value]["proof_obligation_counts"] == {
        UnknownRecoveryProofKind.PATH_SENSITIVE_ARGUMENT_MERGE.value: 1,
    }
    assert backlog[UnknownReasonId.READONLY_IDENTITY_MISSING.value]["proof_obligation_counts"] == {
        UnknownRecoveryProofKind.STORAGE_BACKED_IDENTITY_PROPAGATION.value: 1,
    }


def test_equivalence_result_unknown_reason_text_uses_recovery_actions():
    result = EquivalenceResult(
        is_equivalent=None,
        function1_name="left",
        function2_name="right",
        binary1_name="left.bin",
        binary2_name="right.bin",
        solver_results=_unknown_solver_result(),
        unknown_reasons=[
            make_unknown_reason(
                UnknownReasonId.UNRESOLVED_VALUE_EXPRESSION,
                stage="S_PAIRWISE",
                pair_or_case="(0,0)",
                action_status=UnknownRecoveryActionStatus.PENDING_PROOF,
                recovery_proof_obligations=(
                    UnknownRecoveryProofObligation(
                        proof_kind=UnknownRecoveryProofKind.SOLVER_RETRY_OR_NORMALIZATION,
                        proof_stage="deferred_call_return_resolution",
                    ),
                ),
            )
        ],
    )

    rendered = result.to_string()

    assert (
        "recovery=solver_retry_or_normalization (pending_proof)"
        in rendered
    )


def test_equivalence_result_gates_equivalent_decision_when_pending_proof_exists():
    record = make_unknown_reason(
        UnknownReasonId.EQUIVALENCE_BLOCKING_UNSAFETY,
        recovery_proof_kind=UnknownRecoveryProofKind.CALL_EFFECT_SUMMARY_PROOF,
        recovery_proof_obligations=(
            UnknownRecoveryProofObligation.create(
                UnknownRecoveryProofKind.CALL_EFFECT_SUMMARY_PROOF,
                "object_evidence_collected",
                required_evidence=("call_effect_summary",),
            ),
        ),
        proof_stage="object_evidence_collected",
        evidence_kind="call_effect_summary",
        object_target_key=("call_effect_blocker", "function1", ("function", 1, 0x1000)),
        recovery_action="call_effect_summary_proof_required",
        action_status=UnknownRecoveryActionStatus.PENDING_PROOF,
    )
    result = EquivalenceResult(
        is_equivalent=True,
        function1_name="left",
        function2_name="right",
        binary1_name="left.bin",
        binary2_name="right.bin",
        solver_results=ParallelResult(
            results=[
                SolverResult(
                    solver_name="mock",
                    status=SolverStatus.UNSAT,
                    elapsed_time=0.01,
                )
            ]
        ),
        unknown_reasons=[record],
    )

    assert result.is_equivalent is None
    assert result.decision_gated_by_pending_proof is True
    assert result.to_dict()["decision_gated_by_pending_proof"] is True


def test_equivalence_result_allows_equivalent_decision_when_proof_is_complete():
    record = make_unknown_reason(
        UnknownReasonId.EQUIVALENCE_BLOCKING_UNSAFETY,
        recovery_proof_kind=UnknownRecoveryProofKind.CALL_EFFECT_SUMMARY_PROOF,
        recovery_proof_obligations=(
            UnknownRecoveryProofObligation.create(
                UnknownRecoveryProofKind.CALL_EFFECT_SUMMARY_PROOF,
                "object_evidence_collected",
                required_evidence=("call_effect_summary",),
            ),
        ),
        proof_stage="object_evidence_collected",
        evidence_kind="call_effect_summary",
        object_target_key=("unsupported_call_effect", "function1", ("function", 1, 0x1000)),
        recovery_action="call_effect_summary_proof_required",
        action_status=UnknownRecoveryActionStatus.PROOF_COMPLETE,
    )
    result = EquivalenceResult(
        is_equivalent=True,
        function1_name="left",
        function2_name="right",
        binary1_name="left.bin",
        binary2_name="right.bin",
        solver_results=ParallelResult(
            results=[
                SolverResult(
                    solver_name="mock",
                    status=SolverStatus.UNSAT,
                    elapsed_time=0.01,
                )
            ]
        ),
        unknown_reasons=[record],
    )

    assert result.is_equivalent is True
    assert result.decision_gated_by_pending_proof is False
    assert result.unknown_recovery_actions[0].status == UnknownRecoveryActionStatus.PROOF_COMPLETE.value


def test_equivalence_result_serializes_completed_recovery_proof_evidence():
    evidence = {
        "object_derived": True,
        "status": "complete",
        "reason_id": UnknownReasonId.RETURN_COVERAGE_GAP.value,
        "recovery_proof_kind": UnknownRecoveryProofKind.RETURN_COVERAGE_COMPLETION.value,
        "proof_stage": "return_guard_coverage",
        "evidence_kind": "case_guard_disjunction",
        "object_target_key": ("return_coverage", "function1", ("function_ref", ("function", "B11", 0x1000))),
        "proof_obligation_id": (
            UnknownReasonId.RETURN_COVERAGE_GAP.value,
            "return_guard_coverage",
            UnknownRecoveryProofKind.RETURN_COVERAGE_COMPLETION.value,
            "case_guard_disjunction",
            ("return_coverage", "function1", ("function_ref", ("function", "B11", 0x1000))),
        ),
    }
    result = EquivalenceResult(
        is_equivalent=True,
        function1_name="left",
        function2_name="right",
        binary1_name="left.bin",
        binary2_name="right.bin",
        solver_results=_unknown_solver_result(),
        completed_recovery_proof_evidence=[{"side": "function1", "evidence": evidence}],
    )

    assert result.to_dict()["completed_recovery_proof_evidence"] == [
        {"side": "function1", "evidence": evidence}
    ]


class _FakeCase:
    value_expr = Expression.constant(1, size=4)
    conditions = []


class _NonZ3TimeoutRunner:
    def __init__(self):
        self.received_timeouts = []

    def run_sequential(self, _query, timeout=None):
        self.received_timeouts.append(timeout)
        return ParallelResult(
            results=[
                SolverResult(
                    solver_name="CVC5",
                    status=SolverStatus.TIMEOUT,
                    elapsed_time=float(timeout or 0),
                )
            ],
            first_definitive=None,
            is_equivalent=None,
        )


class _NoSolverTimeoutRunner:
    def run_sequential(self, _query, timeout=None):
        return ParallelResult(results=[], is_equivalent=None)


class _NonZ3PairwiseTimeoutStrategy(MonolithicStrategy):
    per_query_timeout = 1
    per_query_timeout_hard = 2
    save_unknown_queries = False
    enable_solver_proven_rewrite_fallback = False
    enable_normalization_fallback = False

    def __init__(self):
        super().__init__(Mock(), _NonZ3TimeoutRunner())

    def _build_condition_only_query(self, *_args, **_kwargs):
        return "(check-sat)"

    def _build_pair_query(self, *_args, **_kwargs):
        return "(check-sat)"

    def _solve_query_internal(self, query, pair_id, stage="full", use_hard_timeout=False):
        return solve_query_internal(
            self,
            query,
            pair_id,
            stage=stage,
            use_hard_timeout=use_hard_timeout,
        )


class _NoSolverPairwiseTimeoutStrategy(_NonZ3PairwiseTimeoutStrategy):
    def __init__(self):
        MonolithicStrategy.__init__(self, Mock(), _NoSolverTimeoutRunner())


def test_pairwise_solver_timeout_remains_execution_metadata_not_reason():
    strategy = _NonZ3PairwiseTimeoutStrategy()
    left = create_mock_analysis("fc_long_branch_dispatch")
    right = create_mock_analysis("fc_long_branch_dispatch")
    left.binary_id = "B8"
    right.binary_id = "B9"

    result = solve_query_twostage(
        strategy,
        {
            "analysis1": left,
            "analysis2": right,
            "return_size1": 32,
            "return_size2": 32,
        },
        _FakeCase(),
        _FakeCase(),
        None,
        None,
        "(0,0)",
    )

    assert result.is_equivalent is None
    assert result.blocking_reason is None
    assert getattr(result.solver_results.results[0], "solver_name") == "CVC5"
    assert result.object_target_key is None


def test_pairwise_solver_timeout_keeps_no_solver_result_without_proof_target():
    strategy = _NoSolverPairwiseTimeoutStrategy()
    left = create_mock_analysis("fc_long_branch_dispatch")
    right = create_mock_analysis("fc_long_branch_dispatch")

    result = solve_query_twostage(
        strategy,
        {
            "analysis1": left,
            "analysis2": right,
            "return_size1": 32,
            "return_size2": 32,
        },
        _FakeCase(),
        _FakeCase(),
        None,
        None,
        "(0,0)",
    )

    assert result.is_equivalent is None
    assert result.blocking_reason is None
    assert result.solver_results.results == []
    assert result.object_target_key is None


class _FallbackReasonStrategy:
    per_query_timeout = 1
    per_query_timeout_hard = 1
    enable_solver_proven_rewrite_fallback = True
    enable_normalization_fallback = False
    _active_normalization_stats = None

    def _debug_print(self, _message):
        return None

    def _build_condition_only_query(self, *_args, **_kwargs):
        return "(check-sat)"

    def _build_pair_query(self, *_args, **_kwargs):
        return "(check-sat)"

    def _solve_query_internal(self, *_args, **_kwargs):
        return QueryResult(is_equivalent=None)

    def _try_solver_proven_rewrite_equivalence(self, *_args, **_kwargs):
        result = QueryResult(is_equivalent=None)
        result.pair_stage = "rewrite-no-change"
        result.blocking_reason = UnknownReasonId.SOLVER_PROVEN_REWRITE_NO_CHANGE.value
        result.blocking_detail = "no rewrite candidate"
        return result


def test_pairwise_twostage_preserves_recovery_fallback_blocking_reason():
    result = solve_query_twostage(
        _FallbackReasonStrategy(),
        {"return_size1": 32, "return_size2": 32},
        _FakeCase(),
        _FakeCase(),
        None,
        None,
        "(0,0)",
    )

    assert result.is_equivalent is None
    assert result.blocking_reason == UnknownReasonId.SOLVER_PROVEN_REWRITE_NO_CHANGE.value
    assert result.blocking_reason != UnknownReasonId.SOLVER_UNKNOWN_TIMEOUT.value


def test_debug_trace_attempt_carries_typed_unknown_reasons():
    trace = DebugTrace()
    result = EquivalenceResult(
        is_equivalent=None,
        function1_name="left",
        function2_name="right",
        binary1_name="left.bin",
        binary2_name="right.bin",
        solver_results=_unknown_solver_result(),
        unknown_reasons=[
            make_unknown_reason(
                UnknownReasonId.SOLVER_UNKNOWN_TIMEOUT,
                stage="S_MONOLITHIC_FALLBACK",
            )
        ],
    )

    record_attempt_from_result(
        trace,
        attempt_id=1,
        retry_count=0,
        phase="P0_BASELINE",
        result=result,
        transition_reason="UNKNOWN",
        type_fix_result=None,
        strategy_name="monolithic",
    )

    payload = trace.to_dict()

    assert payload["attempts"][0]["unknown_reasons"][0]["reason_id"] == UnknownReasonId.SOLVER_UNKNOWN_TIMEOUT.value
    assert payload["unknown_reason_counts"][UnknownReasonId.SOLVER_UNKNOWN_TIMEOUT.value] == 1


def test_unknown_reason_propagates_from_strategy_result_to_final_summary():
    strategy_result = StrategyResult(
        is_equivalent=None,
        solver_results=_unknown_solver_result(),
        total_pairs=2,
        unknown_pairs=2,
        unknown_reasons=[
            make_unknown_reason(
                UnknownReasonId.RETURN_WIDTH_BRIDGE_MISSING,
                stage="S_PAIRWISE",
                pair_or_case="(0,0)",
            ),
            make_unknown_reason(
                UnknownReasonId.NORMALIZATION_NO_CHANGE,
                stage="S_PAIRWISE",
                pair_or_case="(0,1)",
            ),
        ],
    )
    result = EquivalenceResult(
        is_equivalent=strategy_result.is_equivalent,
        function1_name="left",
        function2_name="right",
        binary1_name="left.bin",
        binary2_name="right.bin",
        solver_results=strategy_result.solver_results,
        pairwise_stats={
            "total_pairs": strategy_result.total_pairs,
            "unsat_pairs": strategy_result.unsat_pairs,
            "sat_pairs": strategy_result.sat_pairs,
            "unknown_pairs": strategy_result.unknown_pairs,
            "error_pairs": strategy_result.error_pairs,
        },
        unknown_reasons=strategy_result.unknown_reasons,
    )
    trace = DebugTrace(final_result=None)

    record_attempt_from_result(
        trace,
        attempt_id=1,
        retry_count=0,
        phase="P0_BASELINE",
        result=result,
        transition_reason="UNKNOWN",
        type_fix_result=None,
        strategy_name="pairwise",
    )

    result_payload = result.to_dict()
    trace_payload = trace.to_dict()

    assert [
        reason["reason_id"] for reason in result_payload["unknown_reasons"]
    ] == [
        UnknownReasonId.RETURN_WIDTH_BRIDGE_MISSING.value,
        UnknownReasonId.NORMALIZATION_NO_CHANGE.value,
    ]
    assert [
        reason["reason_id"]
        for reason in trace_payload["attempts"][0]["unknown_reasons"]
    ] == [
        UnknownReasonId.RETURN_WIDTH_BRIDGE_MISSING.value,
        UnknownReasonId.NORMALIZATION_NO_CHANGE.value,
    ]
    assert sum(trace_payload["unknown_reason_counts"].values()) == strategy_result.unknown_pairs
    assert trace_payload["unknown_reason_counts"] == {
        UnknownReasonId.RETURN_WIDTH_BRIDGE_MISSING.value: 1,
        UnknownReasonId.NORMALIZATION_NO_CHANGE.value: 1,
    }


class _FakeStrategy:
    def __init__(self, result: StrategyResult):
        self.result = result

    def check(self, *_args, **_kwargs):
        return self.result


def test_checker_check_bridges_strategy_unknown_reasons_to_equivalence_result():
    strategy_result = StrategyResult(
        is_equivalent=None,
        solver_results=_unknown_solver_result(),
        total_pairs=1,
        unknown_pairs=1,
        unknown_reasons=[
            make_unknown_reason(
                UnknownReasonId.SOLVER_PROVEN_REWRITE_PROOF_FAILED,
                stage="S_PAIRWISE",
                pair_or_case="(0,0)",
            )
        ],
    )
    checker = EquivalenceChecker(
        timeout=1,
        debug=False,
        enable_rewrite=False,
        strategy="pairwise",
    )

    result = checker.check(
        create_mock_analysis("left"),
        create_mock_analysis("right"),
        "left.bin",
        "right.bin",
        force_strategy=_FakeStrategy(strategy_result),
    )

    assert result.is_equivalent is None
    assert result.unknown_reasons[0].reason_id == UnknownReasonId.SOLVER_PROVEN_REWRITE_PROOF_FAILED.value
    assert result.to_dict()["unknown_reasons"][0]["pair_or_case"] == "(0,0)"


def test_checker_check_builds_reason_selected_recovery_actions():
    strategy_result = StrategyResult(
        is_equivalent=None,
        solver_results=_unknown_solver_result(),
        total_pairs=1,
        unknown_pairs=1,
        unknown_reasons=[
            make_unknown_reason(
                UnknownReasonId.RETURN_WIDTH_BRIDGE_MISSING,
                stage="S_PAIRWISE",
                pair_or_case="(0,0)",
                evidence_refs=("return_storage:r0",),
            )
        ],
    )
    checker = EquivalenceChecker(
        timeout=1,
        debug=False,
        enable_rewrite=False,
        strategy="pairwise",
    )

    result = checker.check(
        create_mock_analysis("left"),
        create_mock_analysis("right"),
        "left.bin",
        "right.bin",
        force_strategy=_FakeStrategy(strategy_result),
    )
    payload = result.to_dict()

    assert [action.proof_kind for action in result.unknown_recovery_actions] == [
        UnknownRecoveryProofKind.ABI_RELATION_PROOF.value,
        UnknownRecoveryProofKind.HIGH_BIT_PROOF.value,
    ]
    assert [action.status for action in result.unknown_recovery_actions] == [
        UnknownRecoveryActionStatus.PLANNED.value,
        UnknownRecoveryActionStatus.PLANNED.value,
    ]
    assert payload["unknown_recovery_actions"][0]["required_evidence"] == [
        "calling_convention",
        "return_storage",
        "narrow_return_width",
    ]
    assert payload["unknown_recovery_actions"][1]["required_evidence"] == [
        "producer_width",
        "extension_semantics",
        "high_bits_irrelevant_or_equal",
    ]


def test_return_width_action_status_does_not_collapse_obligation_proof_kinds():
    reason = make_unknown_reason(
        UnknownReasonId.RETURN_WIDTH_BRIDGE_MISSING,
        stage="S_PAIRWISE",
        pair_or_case="(0,0)",
        evidence_refs=("return_storage:r0",),
        action_status=UnknownRecoveryActionStatus.PLANNED,
    )

    actions = build_unknown_recovery_actions([reason])

    assert [action.proof_kind for action in actions] == [
        UnknownRecoveryProofKind.ABI_RELATION_PROOF.value,
        UnknownRecoveryProofKind.HIGH_BIT_PROOF.value,
    ]
    assert [action.status for action in actions] == [
        UnknownRecoveryActionStatus.PLANNED.value,
        UnknownRecoveryActionStatus.PLANNED.value,
    ]


def test_checker_accepts_pairwise_unknown_dir_from_cli_contract():
    checker = EquivalenceChecker(
        pairwise_save_unknown=True,
        pairwise_unknown_dir="/tmp/pairwise-unknown",
    )

    assert checker.pairwise_strategy.save_unknown_queries is True
    assert checker.pairwise_strategy.unknown_query_dir == "/tmp/pairwise-unknown"
    assert checker.loop_template_strategy.unknown_query_dir == "/tmp/pairwise-unknown"


def test_unknown_by_reason_counts_primary_reason_once_per_pair():
    trace = DebugTrace(final_result=None)
    result = EquivalenceResult(
        is_equivalent=None,
        function1_name="left",
        function2_name="right",
        binary1_name="left.bin",
        binary2_name="right.bin",
        solver_results=_unknown_solver_result(),
        pairwise_stats={
            "total_pairs": 1,
            "unsat_pairs": 0,
            "sat_pairs": 0,
            "unknown_pairs": 1,
            "error_pairs": 0,
        },
        unknown_reasons=[
            make_unknown_reason(
                UnknownReasonId.RETURN_WIDTH_BRIDGE_MISSING,
                stage="S_PAIRWISE",
                pair_or_case="(0,0)",
            ),
            make_unknown_reason(
                UnknownReasonId.NORMALIZATION_NO_CHANGE,
                stage="S_PAIRWISE",
                pair_or_case="(0,0)",
            ),
        ],
    )

    record_attempt_from_result(
        trace,
        attempt_id=1,
        retry_count=0,
        phase="P0_BASELINE",
        result=result,
        transition_reason="UNKNOWN",
        type_fix_result=None,
        strategy_name="pairwise",
    )

    payload = trace.to_dict()

    assert sum(payload["unknown_reason_counts"].values()) == result.pairwise_stats["unknown_pairs"]
    assert payload["unknown_reason_counts"] == {
        UnknownReasonId.RETURN_WIDTH_BRIDGE_MISSING.value: 1,
    }
    assert payload["observed_unknown_reason_counts"] == {
        UnknownReasonId.RETURN_WIDTH_BRIDGE_MISSING.value: 1,
        UnknownReasonId.NORMALIZATION_NO_CHANGE.value: 1,
    }


def test_intermediate_observed_unknown_reason_is_not_final_contributor():
    trace = DebugTrace(final_result=True)
    observed_unknown = EquivalenceResult(
        is_equivalent=None,
        function1_name="left",
        function2_name="right",
        binary1_name="left.bin",
        binary2_name="right.bin",
        solver_results=_unknown_solver_result(),
        pairwise_stats={
            "total_pairs": 1,
            "unsat_pairs": 0,
            "sat_pairs": 0,
            "unknown_pairs": 1,
            "error_pairs": 0,
        },
        unknown_reasons=[
            make_unknown_reason(
                UnknownReasonId.RETURN_WIDTH_BRIDGE_MISSING,
                stage="S_PAIRWISE",
                pair_or_case="(0,0)",
            )
        ],
    )
    final_equivalent = EquivalenceResult(
        is_equivalent=True,
        function1_name="left",
        function2_name="right",
        binary1_name="left.bin",
        binary2_name="right.bin",
        solver_results=ParallelResult(
            results=[
                SolverResult(
                    solver_name="mock",
                    status=SolverStatus.UNSAT,
                    elapsed_time=0.01,
                )
            ]
        ),
    )

    record_attempt_from_result(
        trace,
        attempt_id=1,
        retry_count=0,
        phase="P0_BASELINE",
        result=observed_unknown,
        transition_reason="UNKNOWN",
        type_fix_result=None,
        strategy_name="pairwise",
    )
    record_attempt_from_result(
        trace,
        attempt_id=2,
        retry_count=1,
        phase="P1_RECOVERY",
        result=final_equivalent,
        transition_reason="UNSAT",
        type_fix_result=None,
        strategy_name="pairwise",
    )

    payload = trace.to_dict()

    assert payload["observed_unknown_reason_counts"] == {
        UnknownReasonId.RETURN_WIDTH_BRIDGE_MISSING.value: 1,
    }
    assert payload["unknown_reason_counts"] == {}


def test_debug_trace_recovery_backlog_uses_final_primary_reason_per_pair():
    trace = DebugTrace(final_result=None)
    result = EquivalenceResult(
        is_equivalent=None,
        function1_name="left",
        function2_name="right",
        binary1_name="left.bin",
        binary2_name="right.bin",
        solver_results=_unknown_solver_result(),
        pairwise_stats={
            "total_pairs": 1,
            "unsat_pairs": 0,
            "sat_pairs": 0,
            "unknown_pairs": 1,
            "error_pairs": 0,
        },
        unknown_reasons=[
            make_unknown_reason(
                UnknownReasonId.RETURN_WIDTH_BRIDGE_MISSING,
                stage="S_PAIRWISE",
                pair_or_case="(0,0)",
            ),
            make_unknown_reason(
                UnknownReasonId.METHOD_B_CLOSURE_BLOCKED,
                stage="S_PAIRWISE",
                pair_or_case="(0,0)",
            ),
        ],
    )

    record_attempt_from_result(
        trace,
        attempt_id=1,
        retry_count=0,
        phase="P0_BASELINE",
        result=result,
        transition_reason="UNKNOWN",
        type_fix_result=None,
        strategy_name="pairwise",
    )

    payload = trace.to_dict()

    assert payload["unknown_recovery_backlog"] == {
        UnknownReasonId.RETURN_WIDTH_BRIDGE_MISSING.value: {
            "count": 1,
            "target_regression": "return_width_bridge_missing",
            "recovery_proof_kind": UnknownRecoveryProofKind.ABI_RELATION_HIGH_BIT_PROOF.value,
            "proof_obligation_counts": {
                UnknownRecoveryProofKind.ABI_RELATION_PROOF.value: 1,
                UnknownRecoveryProofKind.HIGH_BIT_PROOF.value: 1,
            },
            "proof_obligations": [
                {
                    "proof_kind": UnknownRecoveryProofKind.ABI_RELATION_PROOF.value,
                    "proof_stage": "abi_relation",
                    "required_evidence": [
                        "calling_convention",
                        "return_storage",
                        "narrow_return_width",
                    ],
                    "description": "Prove the compared return storages are related by the active ABI.",
                },
                {
                    "proof_kind": UnknownRecoveryProofKind.HIGH_BIT_PROOF.value,
                    "proof_stage": "high_bit_relation",
                    "required_evidence": [
                        "producer_width",
                        "extension_semantics",
                        "high_bits_irrelevant_or_equal",
                    ],
                    "description": "Prove the wider return high bits cannot change the semantic result.",
                },
            ],
        },
    }
    assert UnknownReasonId.METHOD_B_CLOSURE_BLOCKED.value in payload["observed_unknown_recovery_backlog"]
