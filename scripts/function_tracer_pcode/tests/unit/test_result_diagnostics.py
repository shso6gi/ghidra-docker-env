"""Issue #17: diagnostics block, projected-reason details, and their aggregation."""
from types import SimpleNamespace

from scripts.function_tracer_pcode.checker.diagnostics import (
    AnalysisTimer,
    expression_stats,
    result_diagnostics_payload,
)
from scripts.function_tracer_pcode.checker.unknown_reason import (
    UnknownReasonId,
    build_projection_diagnostic,
    format_projection_detail,
    make_unknown_reason,
)
from scripts.function_tracer_pcode.core import Condition, Expression, FunctionReturnAnalysis, ReturnInfo
from scripts.function_tracer_pcode.reporting.unknown_reason_summary import (
    format_validation_unknown_summary,
    summarize_validation_unknowns,
)


def _analysis():
    x = Expression.parameter("x", 0, size=4)
    guard = Condition(Expression.binary_op("INT_SLESS", x, Expression.constant(3, size=4)))
    value = Expression.binary_op("INT_ADD", Expression.binary_op("INT_MULT", x, x), Expression.constant(1, size=4))
    return FunctionReturnAnalysis(
        function_name="f", entry_point="0x1000",
        parameters=[{"name": "x", "index": 0, "size": 4}],
        returns=[ReturnInfo("0x1010", value, [guard]), ReturnInfo("0x1020", Expression.constant(0, size=4), [])],
        return_type="int",
    )


def test_expression_stats_count_nodes_and_depth_over_values_and_guards():
    stats = expression_stats(_analysis())
    assert stats["return_case_count"] == 2
    # value: ADD(MULT(x, x), 1) = 4 distinct nodes (x shared), guard: SLESS(x, 3) = 2 new, const 0 = 1
    assert stats["node_count"] == 7
    assert stats["max_depth"] == 3


def test_analysis_timer_records_seconds_and_expression_stats():
    timer = AnalysisTimer()
    analysis = timer.timed("function1", lambda: _analysis())
    timer.record_analysis("function1", analysis)
    snapshot = timer.snapshot()
    assert snapshot["analysis_seconds"]["function1"] >= 0.0
    assert snapshot["expressions"]["function1"]["node_count"] == 7


def test_result_diagnostics_payload_merges_recorded_and_live_statistics():
    attempt = SimpleNamespace(
        attempt_id="a1", phase="P0_BASE", strategy="pairwise", elapsed_time=1.5,
        solver_results=SimpleNamespace(results=[SimpleNamespace(elapsed_time=0.25), SimpleNamespace(elapsed_time=0.5)]),
    )
    result = SimpleNamespace(
        diagnostics={"analysis_seconds": {"function1": 0.4, "function2": 0.6}, "expressions": {"function1": {"node_count": 7}}},
        debug_trace=SimpleNamespace(attempts=[attempt]),
        total_time=2.0, pairwise_stats={"total_pairs": 3, "unsat_pairs": 3}, stage_path=["S_PAIRWISE"],
        solver_results=None,
    )
    payload = result_diagnostics_payload(result)
    assert payload["schema"] == "result-diagnostics-v1"
    assert payload["timings"]["total_seconds"] == 2.0
    assert payload["timings"]["analysis_seconds"] == {"function1": 0.4, "function2": 0.6}
    assert payload["timings"]["solver_seconds"] == 0.75
    assert payload["solver_invocations"] == 2
    assert payload["timings"]["attempts"][0]["phase"] == "P0_BASE"
    assert payload["expressions"]["function1"]["node_count"] == 7
    assert payload["pairs"]["total_pairs"] == 3


def _occurrence():
    cause_id = SimpleNamespace(
        canonical_target_key=("function_decompilation_target_v1", "ab" * 32),
        missing_semantic_fact=("missing_operational_artifact", "function_decompilation_artifact"),
    )
    return SimpleNamespace(
        occurrence_id="occ-1", cause_id=cause_id, target_kind="function_decompilation",
        identity_scope=SimpleNamespace(value="UNARY"), producer_id="decompiler-artifact-extraction-v2",
        evidence_kind="operational_artifact", evidence_refs=("ref-1",),
    )


def test_projection_diagnostic_carries_functions_cause_and_legacy_site():
    legacy = make_unknown_reason(
        UnknownReasonId.SAT_COUNTEREXAMPLE_AMBIGUOUS, stage="S_PAIRWISE", pair_or_case="(0,1)",
        detail="return slot width unknown for d0", evidence_refs=("width",),
    )
    receipt = SimpleNamespace(reason_id=UnknownReasonId.SAT_COUNTEREXAMPLE_AMBIGUOUS.value, occurrence_id="occ-1")
    diagnostic = build_projection_diagnostic(
        receipt, cause_occurrence=_occurrence(), legacy_reasons=[legacy],
        function_names={"function1": "snippet", "function2": "snippet"},
        binary_names={"binary1": "newV-arm64-clang-O0", "binary2": "newV-arm64-clang-O1"},
    )
    assert diagnostic["functions"] == {"function1": "snippet", "function2": "snippet"}
    assert diagnostic["cause"]["target_kind"] == "function_decompilation"
    assert diagnostic["cause"]["identity_scope"] == "UNARY"
    assert tuple(diagnostic["cause"]["missing_semantic_fact"]) == ("missing_operational_artifact", "function_decompilation_artifact")
    assert diagnostic["legacy"][0]["pair_or_case"] == "(0,1)"
    text = format_projection_detail(diagnostic)
    assert text.startswith("snippet vs snippet; decompiler-artifact-extraction-v2/function_decompilation (UNARY); missing missing_operational_artifact/function_decompilation_artifact")
    assert "at (0,1)" in text and "return slot width unknown for d0" in text


def test_summary_aggregates_reason_detail_and_diagnostics_and_marks_generic_unknown():
    detailed = make_unknown_reason(
        UnknownReasonId.SAT_COUNTEREXAMPLE_AMBIGUOUS, stage="V2_TYPED_RESULT_PROJECTION",
        detail="f vs f; width/return_slot (UNARY); missing slot", aggregation_unit="result",
    ).to_dict()
    payloads = [
        {"final_outcome": "UNKNOWN", "is_equivalent": None, "unknown_reasons": [detailed],
         "diagnostics": {"timings": {"total_seconds": 2.0, "analysis_seconds": {"function1": 0.5, "function2": 0.5}, "solver_seconds": 0.3},
                         "expressions": {"function1": {"node_count": 10, "max_depth": 4}}}},
        {"final_outcome": "UNKNOWN", "is_equivalent": None, "unknown_reasons": []},
    ]
    summary = summarize_validation_unknowns(payloads)
    assert summary.unknown_by_reason_detail == {
        f"{UnknownReasonId.SAT_COUNTEREXAMPLE_AMBIGUOUS.value} | f vs f; width/return_slot (UNARY); missing slot": 1,
        f"{UnknownReasonId.UNKNOWN.value} | result payload carries no unknown_reasons record": 1,
    }
    assert summary.diagnostics_stats["results_with_diagnostics"] == 1
    assert summary.diagnostics_stats["analysis_seconds"]["max"] == 1.0
    assert summary.diagnostics_stats["expression_node_count"]["max"] == 10.0
    text = format_validation_unknown_summary(summary)
    assert "UNKNOWN by reason detail" in text and "Diagnostics (per-result timings" in text
