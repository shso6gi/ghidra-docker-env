"""Phase 6a-2: AnalysisRuntimeState が長寿命 runtime 状態を所有し、facade 属性 seam が維持されることの回帰テスト。"""

import dataclasses
from unittest.mock import Mock

from scripts.function_tracer_pcode.analysis.returns.analyzer import ReturnAnalyzer
from scripts.function_tracer_pcode.analysis.runtime_state import AnalysisRuntimeState

FIELDS = [f.name for f in dataclasses.fields(AnalysisRuntimeState)]
EXPECTED = {
    "call_analysis_cache", "local_target_cache", "effect_summary_cache", "effect_summary_parameter_cache",
    "direct_call_graph", "direct_call_graph_complete_nodes", "analysis_in_progress", "deferred_call_counter",
    # Issue #131: 効果要約 1 件に対応する切り捨て診断（key/寿命は effect_summary_cache と同じ）
    "effect_summary_budget_diagnostics",
    # Issue #47 (PR-A): decompile 成功時のみ作る complete な callee parameter snapshot と、
    # その hit/miss 計数（診断専用）。
    "callee_parameter_decompile_cache", "callee_parameter_decompile_stats",
    # Issue #47: callee 解析 cache（call_analysis_cache）側の hit/miss 診断。
    "callee_analysis_cache_stats",
    # Issue #47 (PR-B): external placeholder callee の束縛ゼロ解析再利用の静的判定と計数。
    "callee_unbound_reuse_verdicts", "callee_unbound_reuse_stats",
}


def _analyzer():
    return ReturnAnalyzer(program=Mock(), debug=False)


def test_runtime_state_has_exactly_the_expected_fields():
    assert set(FIELDS) == EXPECTED


def test_facade_reads_return_the_owner_objects_by_identity():
    analyzer = _analyzer()
    state = analyzer._runtime_state
    assert isinstance(state, AnalysisRuntimeState)
    for f in FIELDS:
        facade = getattr(analyzer, "_" + f)
        owned = getattr(state, f)
        assert facade is owned if f != "deferred_call_counter" else facade == owned == 0, f
    # 生の instance 属性としては持たない（property 経由のみ）
    assert not (set("_" + f for f in FIELDS) & set(vars(analyzer)))


def test_in_place_mutation_through_the_facade_lands_in_the_owner():
    analyzer = _analyzer()
    state = analyzer._runtime_state
    analyzer._call_analysis_cache[("f",)] = "analysis"
    analyzer._local_target_cache[("t",)] = None
    analyzer._effect_summary_cache[("e",)] = "summary"
    analyzer._effect_summary_parameter_cache[("p",)] = []
    analyzer._direct_call_graph[("a",)] = {("b",)}
    analyzer._direct_call_graph_complete_nodes.add(("a",))
    analyzer._analysis_in_progress[("g",)] = "in-progress"
    assert state.call_analysis_cache == {("f",): "analysis"}
    assert state.local_target_cache == {("t",): None}
    assert state.effect_summary_cache == {("e",): "summary"}
    assert ("p",) in state.effect_summary_parameter_cache
    assert state.direct_call_graph == {("a",): {("b",)}} and ("a",) in state.direct_call_graph_complete_nodes
    assert state.analysis_in_progress == {("g",): "in-progress"}
    analyzer._analysis_in_progress.pop(("g",), None)
    assert not state.analysis_in_progress
    analyzer._direct_call_graph_complete_nodes.remove(("a",))
    assert not state.direct_call_graph_complete_nodes


def test_direct_assignment_replaces_the_owner_field_by_identity():
    """test_call_effect_obligations の `analyzer._direct_call_graph = {...}` seam。"""
    analyzer = _analyzer()
    graph, nodes = {("x",): set()}, {("x",)}
    analyzer._direct_call_graph = graph
    analyzer._direct_call_graph_complete_nodes = nodes
    assert analyzer._runtime_state.direct_call_graph is graph
    assert analyzer._runtime_state.direct_call_graph_complete_nodes is nodes
    assert analyzer._direct_call_graph is graph


def test_augmented_assignment_on_the_counter_goes_through_the_setter():
    analyzer = _analyzer()
    analyzer._deferred_call_counter += 1
    analyzer._deferred_call_counter += 1
    assert analyzer._runtime_state.deferred_call_counter == 2 == analyzer._deferred_call_counter


def test_collaborators_hold_the_runtime_state_owner_directly():
    """6a-5 以降: collaborator は per-field supplier ではなく owner そのものを直接依存として持つ。"""
    analyzer = _analyzer()
    state = analyzer._runtime_state
    assert analyzer._effect_integration.runtime_state is state
    assert analyzer._divergence_proofs.runtime_state is state
    # 直接代入 seam で owner のフィールドを差し替えても、owner 経由で読む collaborator は新しい object を見る
    analyzer._direct_call_graph = {}
    assert analyzer._effect_integration.runtime_state.direct_call_graph is analyzer._runtime_state.direct_call_graph

def test_runtime_state_survives_nested_analysis_contexts_unlike_the_session():
    """AnalysisSession は _analysis_context で push/pop されるが、runtime state は analyzer 寿命で不変。"""
    analyzer = _analyzer()
    state = analyzer._runtime_state
    analyzer._call_analysis_cache[("outer",)] = "o"
    with analyzer._analysis_context([], None):
        assert analyzer._runtime_state is state
        analyzer._call_analysis_cache[("inner",)] = "i"
        analyzer._deferred_call_counter += 1
    assert analyzer._runtime_state is state
    assert set(state.call_analysis_cache) == {("outer",), ("inner",)}
    assert state.deferred_call_counter == 1
