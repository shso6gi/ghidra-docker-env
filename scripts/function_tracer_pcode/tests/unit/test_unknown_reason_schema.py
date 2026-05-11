# -*- coding: utf-8 -*-

from scripts.function_tracer_pcode.equivalence.attempts import record_attempt_from_result
from scripts.function_tracer_pcode.equivalence.debug_trace import DebugTrace
from scripts.function_tracer_pcode.equivalence.result import EquivalenceResult
from scripts.function_tracer_pcode.equivalence.strategies.base import StrategyResult
from scripts.function_tracer_pcode.equivalence.unknown_reason import (
    UnknownRecoveryProofKind,
    UnknownReasonId,
    get_unknown_reason_definition,
    make_unknown_reason,
)
from scripts.function_tracer_pcode.equivalence.strategies.pairwise_models import QueryResult
from scripts.function_tracer_pcode.equivalence.strategies.pairwise_query_executor import solve_query_twostage
from scripts.function_tracer_pcode.model import Expression
from scripts.function_tracer_pcode.smt import ParallelResult, SolverResult, SolverStatus


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


class _FakeCase:
    value_expr = Expression.constant(1, size=4)
    conditions = []


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
