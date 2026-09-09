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
from scripts.function_tracer_pcode.core import Condition, Expression, ExpressionType, FunctionReturnAnalysis, ReturnInfo
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


def test_analysis_timer_accumulates_callee_parameter_cache_stats_per_side():
    """Issue #47: 同じ side を再解析しても analyzer instance ごとの計数を足し合わせる。"""
    timer = AnalysisTimer()
    first = SimpleNamespace(
        callee_parameter_cache_diagnostics=lambda: {
            "schema": "callee-parameter-decompile-cache-v1",
            "hits": 2, "misses": 3, "snapshots_stored": 3, "invalidations": 0,
            "miss_reasons": {"no_snapshot": 3}, "uncacheable_reasons": {}, "entries": 3,
        }
    )
    second = SimpleNamespace(
        callee_parameter_cache_diagnostics=lambda: {
            "schema": "callee-parameter-decompile-cache-v1",
            "hits": 1, "misses": 1, "snapshots_stored": 0, "invalidations": 1,
            "miss_reasons": {"no_snapshot": 1}, "uncacheable_reasons": {"decompile_incomplete": 1},
            "entries": 1,
        }
    )
    timer.record_callee_parameter_cache("function2", first)
    timer.record_callee_parameter_cache("function2", second)
    stats = timer.snapshot()["callee_parameter_cache"]["function2"]
    assert stats["hits"] == 3 and stats["misses"] == 4 and stats["invalidations"] == 1
    assert stats["miss_reasons"] == {"no_snapshot": 4}
    assert stats["uncacheable_reasons"] == {"decompile_incomplete": 1}
    assert stats["analyzer_instances"] == 2 and stats["snapshot_entries"] == 1


def test_analysis_timer_accumulates_callee_analysis_cache_stats_per_side():
    """Issue #47: 解析 cache 側も side ごとに instance をまたいで足し合わせる。"""
    timer = AnalysisTimer()

    def _analyzer(payload):
        return SimpleNamespace(callee_analysis_cache_diagnostics=lambda: payload)

    first = _analyzer({
        "schema": "callee-analysis-cache-v1", "hits": 4, "misses": 2,
        "miss_reasons": {"target_first_analysis": 2},
        "bound_misses_without_unbound_entry": 1,
        "targets": [{"target": "function:log@0x1000", "hits": 4, "misses": 2,
                     "miss_reasons": {"target_first_analysis": 2},
                     "bound_misses_without_unbound_entry": 1, "distinct_scope_keys": 2}],
        "targets_truncated": 0, "repeated_miss_targets": {"target_first_analysis": ["function:log@0x1000"]},
        "entries": 3,
    })
    second = _analyzer({
        "schema": "callee-analysis-cache-v1", "hits": 1, "misses": 3,
        "miss_reasons": {"bound_signature_differs": 3},
        "bound_misses_without_unbound_entry": 3,
        "targets": [{"target": "function:log@0x1000", "hits": 1, "misses": 3,
                     "miss_reasons": {"bound_signature_differs": 3},
                     "bound_misses_without_unbound_entry": 3, "distinct_scope_keys": 4}],
        "targets_truncated": 0, "repeated_miss_targets": {"bound_signature_differs": ["function:log@0x1000"]},
        "entries": 5,
    })
    timer.record_callee_analysis_cache("function2", first)
    timer.record_callee_analysis_cache("function2", second)
    stats = timer.snapshot()["callee_analysis_cache"]["function2"]
    assert stats["hits"] == 5 and stats["misses"] == 5
    assert stats["miss_reasons"] == {"bound_signature_differs": 3, "target_first_analysis": 2}
    assert stats["bound_misses_without_unbound_entry"] == 4
    assert stats["analyzer_instances"] == 2 and stats["cache_entries"] == 5
    row = stats["targets"][0]
    assert row["hits"] == 5 and row["misses"] == 5 and row["distinct_scope_keys"] == 4
    assert row["bound_signature_induced_misses"] == 3
    assert stats["bound_signature_induced_misses"] == 3
    assert stats["storage_bound_signature_induced_misses"] == 0
    assert stats["repeated_miss_targets"] == {
        "bound_signature_differs": ["function:log@0x1000"],
        "target_first_analysis": ["function:log@0x1000"],
    }


def test_analysis_timer_accumulates_callee_unbound_reuse_stats_per_side():
    """Issue #47 (PR-B): 再利用の計数も side ごとに instance をまたいで足し合わせる。"""
    timer = AnalysisTimer()

    def _analyzer(payload):
        return SimpleNamespace(callee_unbound_reuse_diagnostics=lambda: payload)

    first = _analyzer({
        "schema": "callee-unbound-reuse-v1", "reuses": 20, "unbound_analyses": 1,
        "shadow_comparisons": 0, "shadow_mismatches": 0,
        "verdicts": {"eligible_external_placeholder": 1},
        "declines": {},
        "targets": [{"target": "function:log@0x1000", "reuses": 20, "unbound_analyses": 1,
                     "shadow_comparisons": 0, "shadow_mismatches": 0, "declines": {},
                     "eligible": True, "verdict_reason": "eligible_external_placeholder"}],
        "targets_truncated": 0, "shadow_mismatch_targets": [], "entries": 1,
    })
    second = _analyzer({
        "schema": "callee-unbound-reuse-v1", "reuses": 5, "unbound_analyses": 1,
        "shadow_comparisons": 2, "shadow_mismatches": 1,
        "verdicts": {"callee_is_internal": 1},
        "declines": {"unbound_analysis_unavailable": 1},
        "targets": [{"target": "function:log@0x1000", "reuses": 5, "unbound_analyses": 1,
                     "shadow_comparisons": 2, "shadow_mismatches": 1,
                     "declines": {"unbound_analysis_unavailable": 1}}],
        "targets_truncated": 0, "shadow_mismatch_targets": ["function:log@0x1000"], "entries": 2,
    })
    timer.record_callee_unbound_reuse("function2", first)
    timer.record_callee_unbound_reuse("function2", second)
    stats = timer.snapshot()["callee_unbound_reuse"]["function2"]
    assert stats["reuses"] == 25 and stats["unbound_analyses"] == 2
    assert stats["shadow_comparisons"] == 2 and stats["shadow_mismatches"] == 1
    assert stats["verdicts"] == {"callee_is_internal": 1, "eligible_external_placeholder": 1}
    assert stats["declines"] == {"unbound_analysis_unavailable": 1}
    assert stats["analyzer_instances"] == 2 and stats["verdict_entries"] == 2
    assert stats["shadow_mismatch_targets"] == ["function:log@0x1000"]
    row = stats["targets"][0]
    assert row["reuses"] == 25 and row["shadow_mismatches"] == 1
    # 先に観測した判定内容は後続の instance でも失わない。
    assert row["eligible"] is True
    assert row["verdict_reason"] == "eligible_external_placeholder"


def test_result_diagnostics_payload_carries_the_callee_unbound_reuse_block():
    result = SimpleNamespace(
        diagnostics={"callee_unbound_reuse": {"function2": {"reuses": 43, "unbound_analyses": 1}}},
        debug_trace=None, total_time=1.0, pairwise_stats={}, stage_path=[], solver_results=None,
    )
    payload = result_diagnostics_payload(result)
    assert payload["caches"]["callee_unbound_reuse"]["function2"] == {
        "reuses": 43, "unbound_analyses": 1
    }
    # 3 つの cache 診断は別概念として並ぶ。
    assert payload["caches"]["callee_analysis"] == {}
    assert payload["caches"]["callee_parameter_decompile"] == {}


def test_result_diagnostics_payload_carries_the_callee_analysis_cache_block():
    result = SimpleNamespace(
        diagnostics={"callee_analysis_cache": {"function2": {"hits": 9, "misses": 2}}},
        debug_trace=None, total_time=1.0, pairwise_stats={}, stage_path=[], solver_results=None,
    )
    payload = result_diagnostics_payload(result)
    assert payload["caches"]["callee_analysis"]["function2"] == {"hits": 9, "misses": 2}
    assert payload["caches"]["callee_parameter_decompile"] == {}


def test_result_diagnostics_payload_carries_the_callee_parameter_cache_block():
    result = SimpleNamespace(
        diagnostics={"callee_parameter_cache": {"function1": {"hits": 4, "misses": 1}}},
        debug_trace=None, total_time=1.0, pairwise_stats={}, stage_path=[], solver_results=None,
    )
    payload = result_diagnostics_payload(result)
    assert payload["caches"]["callee_parameter_decompile"]["function1"] == {"hits": 4, "misses": 1}
    assert payload["caches"]["callee_analysis"] == {}


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
        projected_reason_counts={UnknownReasonId.SAT_COUNTEREXAMPLE_AMBIGUOUS.value: 1},
    )
    assert diagnostic["legacy_match"] == "unique"
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



def _deep_chain(depth):
    expr = Expression.constant(1, size=4)
    for _ in range(depth):
        expr = Expression(ExpressionType.UNARY_OP, operator="INT_2COMP", operands=[expr], size=4)
    return expr


def test_expression_stats_walks_ten_thousand_deep_expressions_without_recursion():
    analysis = FunctionReturnAnalysis(
        function_name="deep", entry_point="0x1000", parameters=[],
        returns=[ReturnInfo("0x1010", _deep_chain(10_000), [])], return_type="int",
    )
    stats = expression_stats(analysis)
    assert stats["node_count"] == 10_001
    assert stats["max_depth"] == 10_001
    assert "error" not in stats

    timer = AnalysisTimer()
    timer.record_analysis("function1", analysis)  # must not raise
    assert timer.snapshot()["expressions"]["function1"]["node_count"] == 10_001


def test_diagnostics_are_fail_open_and_never_raise():
    class _Poisoned:
        @property
        def returns(self):
            raise RuntimeError("diagnostics must not propagate this")

    timer = AnalysisTimer()
    timer.record_analysis("function1", _Poisoned())
    assert timer.snapshot()["expressions"]["function1"]["error"].startswith("RuntimeError")

    class _BrokenResult:
        diagnostics = None
        total_time = 1.0
        pairwise_stats = None
        stage_path = ()
        solver_results = None

        @property
        def debug_trace(self):
            raise ValueError("broken trace")

    payload = result_diagnostics_payload(_BrokenResult())
    assert payload["schema"] == "result-diagnostics-v1"
    assert payload["error"].startswith("ValueError")


def _legacy(reason_id, target, pair, detail):
    return make_unknown_reason(
        reason_id, stage="S_PAIRWISE", pair_or_case=pair, detail=detail,
        evidence_refs=("analysis_safety_gap",), object_target_key=target,
    )


def _cause_with_target(target):
    occurrence = _occurrence()
    occurrence.cause_id = SimpleNamespace(canonical_target_key=target, missing_semantic_fact=("fact",))
    occurrence.evidence_refs = ("analysis_safety_gap",)
    return occurrence


def test_legacy_reason_matching_is_exact_or_unique_never_a_sibling_site():
    reason = UnknownReasonId.SAT_COUNTEREXAMPLE_AMBIGUOUS
    site_a = ("counterexample_safety_gate", ("pair", "(0,1)"))
    site_b = ("counterexample_safety_gate", ("pair", "(2,3)"))
    legacy = [
        _legacy(reason, site_a, "(0,1)", "site A detail"),
        _legacy(reason, site_b, "(2,3)", "site B detail"),
    ]
    receipt = SimpleNamespace(reason_id=reason.value, occurrence_id="occ-1")
    names = {"function1": "f", "function2": "f"}

    # Exact: the cause target equals site B's object target key -> only site B.
    exact = build_projection_diagnostic(
        receipt, cause_occurrence=_cause_with_target(site_b), legacy_reasons=legacy,
        function_names=names, projected_reason_counts={reason.value: 2},
    )
    assert exact["legacy_match"] == "exact"
    assert [item["pair_or_case"] for item in exact["legacy"]] == ["(2,3)"]
    assert "site A detail" not in format_projection_detail(exact)

    # Ambiguous: two candidate sites, cause target matches neither -> no legacy attached.
    ambiguous = build_projection_diagnostic(
        receipt, cause_occurrence=_cause_with_target(("other", "target")), legacy_reasons=legacy,
        function_names=names, projected_reason_counts={reason.value: 2},
    )
    assert "legacy" not in ambiguous
    assert "site" not in format_projection_detail(ambiguous)

    # Unique 1:1: one legacy record and one projected cause for the reason.
    unique = build_projection_diagnostic(
        receipt, cause_occurrence=_cause_with_target(("other", "target")), legacy_reasons=legacy[:1],
        function_names=names, projected_reason_counts={reason.value: 1},
    )
    assert unique["legacy_match"] == "unique"

    # One legacy record but two projected causes: still ambiguous.
    not_unique = build_projection_diagnostic(
        receipt, cause_occurrence=_cause_with_target(("other", "target")), legacy_reasons=legacy[:1],
        function_names=names, projected_reason_counts={reason.value: 2},
    )
    assert "legacy" not in not_unique
