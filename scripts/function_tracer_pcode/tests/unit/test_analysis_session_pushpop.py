"""Phase 6a-1: `_analysis_context` が AnalysisSession object を push/pop することの回帰テスト。

8 フィールドすべてについて、親 session の同一性復元 / 子の変更の非漏洩 / 親 container の同一性維持 /
例外終了時の同一復元を固定する。blocked_return_path_conditions と return_path_entry_cache の分離は
旧実装（6 フィールドのみ個別退避）に対する意図的な state-lifetime 修正。
"""

import dataclasses
from unittest.mock import Mock

import pytest

from scripts.function_tracer_pcode.analysis.returns.analyzer import ReturnAnalyzer
from scripts.function_tracer_pcode.analysis.session import AnalysisSession

FIELDS = [f.name for f in dataclasses.fields(AnalysisSession)]
FACADE = {
    "parameters": "_current_parameters",
    "effect_summary": "_current_effect_summary",
    "deferred_calls": "_current_deferred_calls",
    "function_prototype": "_current_function_prototype",
    "function_entry_address": "_current_function_entry_address_value",
    "blocked_return_path_conditions": "_current_blocked_return_path_conditions",
    "noreturn_terminal_observations": "_current_noreturn_terminal_observations",
    "return_path_entry_cache": "_return_path_entry_cache",
}


def _analyzer():
    return ReturnAnalyzer(program=Mock(), debug=False)


def _populate_parent(analyzer):
    parent = analyzer._ensure_analysis_session()
    parent.parameters = [{"name": "p0"}]
    parent.effect_summary = object()
    parent.deferred_calls = {("d",): "deferred"}
    parent.function_prototype = object()
    parent.function_entry_address = "0x100"
    parent.blocked_return_path_conditions = [["blocked"]]
    parent.noreturn_terminal_observations = [{"obs": 1}]
    parent.return_path_entry_cache = {("k",): None}
    return parent, {f: getattr(parent, f) for f in FIELDS}


def test_session_dataclass_has_exactly_the_eight_fields_under_test():
    assert set(FIELDS) == set(FACADE)


def test_child_is_a_fresh_session_initialised_from_the_bound_values_only():
    analyzer = _analyzer()
    parent, _ = _populate_parent(analyzer)
    params, summary, proto = [{"name": "child"}], object(), object()
    with analyzer._analysis_context(params, summary, function_prototype=proto, function_entry_address="0x200"):
        child = analyzer._ensure_analysis_session()
        assert child is not parent
        assert child.parameters is params and child.effect_summary is summary
        assert child.function_prototype is proto and child.function_entry_address == "0x200"
        # 子が新規に所有する 4 container は空で、親のものとは別 object
        for f in ("deferred_calls", "blocked_return_path_conditions", "noreturn_terminal_observations", "return_path_entry_cache"):
            assert not getattr(child, f) and getattr(child, f) is not getattr(parent, f), f
        # facade property は子を見る
        assert analyzer._current_parameters is params
        assert analyzer._return_path_entry_cache is child.return_path_entry_cache


def test_parent_session_is_restored_by_identity_and_child_mutations_do_not_leak():
    analyzer = _analyzer()
    parent, before = _populate_parent(analyzer)
    with analyzer._analysis_context([{"name": "child"}], None):
        analyzer._current_deferred_calls[("c",)] = "child-deferred"
        analyzer._current_blocked_return_path_conditions.append(["child-blocked"])
        analyzer._current_noreturn_terminal_observations.append({"obs": "child"})
        analyzer._return_path_entry_cache[("child",)] = None
        analyzer._current_parameters.append({"name": "extra"})
    assert analyzer._ensure_analysis_session() is parent
    for f in FIELDS:
        assert getattr(parent, f) is before[f], f          # 親の container は同一 object のまま
        assert getattr(analyzer, FACADE[f]) is before[f], f  # 旧 API も同じ object を参照で返す
    assert parent.deferred_calls == {("d",): "deferred"}
    assert parent.blocked_return_path_conditions == [["blocked"]]
    assert parent.noreturn_terminal_observations == [{"obs": 1}]
    assert parent.return_path_entry_cache == {("k",): None}
    assert parent.parameters == [{"name": "p0"}]


def test_exception_exit_restores_the_parent_identically():
    analyzer = _analyzer()
    parent, before = _populate_parent(analyzer)
    with pytest.raises(RuntimeError):
        with analyzer._analysis_context([], None):
            analyzer._return_path_entry_cache[("x",)] = None
            analyzer._current_blocked_return_path_conditions.append(["x"])
            raise RuntimeError("boom")
    assert analyzer._ensure_analysis_session() is parent
    for f in FIELDS:
        assert getattr(parent, f) is before[f], f
    assert parent.return_path_entry_cache == {("k",): None}
    assert parent.blocked_return_path_conditions == [["blocked"]]


def test_nested_contexts_restore_each_level():
    analyzer = _analyzer()
    root, _ = _populate_parent(analyzer)
    with analyzer._analysis_context([{"name": "l1"}], None):
        l1 = analyzer._ensure_analysis_session()
        analyzer._return_path_entry_cache[("l1",)] = None
        with analyzer._analysis_context([{"name": "l2"}], None):
            l2 = analyzer._ensure_analysis_session()
            assert l2 is not l1 and not l2.return_path_entry_cache
            analyzer._return_path_entry_cache[("l2",)] = None
        assert analyzer._ensure_analysis_session() is l1
        assert l1.return_path_entry_cache == {("l1",): None}
    assert analyzer._ensure_analysis_session() is root
    assert root.return_path_entry_cache == {("k",): None}


def test_analyze_function_no_longer_clears_the_parent_cache_before_entering_the_context():
    import inspect
    from scripts.function_tracer_pcode.analysis.returns import analyze_function
    src = inspect.getsource(analyze_function)
    assert "self._return_path_entry_cache = {}" not in src
