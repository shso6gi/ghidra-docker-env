# -*- coding: utf-8 -*-
"""Debug-only expression rendering regressions."""

from unittest.mock import Mock

from scripts.function_tracer_pcode.analysis.debug import render
from scripts.function_tracer_pcode.analysis.debug.render import (
    summarize_conditions,
    summarize_expressions,
    summarize_runtime_ref,
    summarize_values,
)
from scripts.function_tracer_pcode.analysis.returns.analyzer import ReturnAnalyzer
from scripts.function_tracer_pcode.core import Condition, Expression
from scripts.function_tracer_pcode.semantics.transform.expander import ExpressionExpander
from scripts.function_tracer_pcode.semantics.transform.expander_support import ExpandedValue


def test_expander_debug_expr_summary_does_not_require_full_to_string(monkeypatch):
    tracer = Mock()
    tracker = Mock()
    expander = ExpressionExpander(tracer, tracker, debug=True)

    expr = Expression.binary_op(
        "INT_ADD",
        Expression.unknown("phi_circular"),
        Expression.binary_op("INT_MULT", Expression.parameter("n"), Expression.constant(2, 4)),
    )

    def _boom(_self, simplify=True):
        raise AssertionError("full to_string should not be used for debug summary")

    monkeypatch.setattr(Expression, "to_string", _boom)

    summary = expander._debug_expr_summary(expr)

    assert "INT_ADD" in summary
    assert "UNKNOWN(phi_circular)" in summary


def test_expander_debug_budget_skips_heavy_summary_work(monkeypatch):
    tracer = Mock()
    tracker = Mock()
    expander = ExpressionExpander(tracer, tracker, debug=True)
    expander._debug_message_limit = 0

    expr = Expression.binary_op(
        "INT_ADD",
        Expression.parameter("n"),
        Expression.constant(2, 4),
    )

    def _boom(_self, simplify=True):
        raise AssertionError("suppressed expander debug should not call full to_string")

    monkeypatch.setattr(Expression, "to_string", _boom)

    assert expander._debug_expr_summary(expr) == "<debug-suppressed>"


def test_return_analyzer_dispose_ignores_jvm_not_running_error():
    analyzer = ReturnAnalyzer(program=Mock(), debug=False)
    analyzer._decompiler = Mock()
    analyzer._decompiler.dispose.side_effect = Exception("Java Virtual Machine is not running")

    analyzer.dispose()

    assert analyzer._decompiler is None


# ------------------------------------------------- 列サマリーの有界性（#22）


class _ExplosiveIterable:
    """``allowed`` 個を超えて読まれたら失敗する iterable（長さは名乗らない）。"""

    def __init__(self, items, allowed: int):
        self._items = list(items)
        self._allowed = allowed
        self.consumed = 0

    def __iter__(self):
        for item in self._items:
            self.consumed += 1
            if self.consumed > self._allowed:
                raise AssertionError(
                    f"debug summary consumed {self.consumed} elements "
                    f"(allowed {self._allowed})"
                )
            yield item


def _expressions(count: int):
    return [Expression.parameter(f"p{index}") for index in range(count)]


def test_sequence_summary_reports_the_exact_remainder_for_a_sized_sequence():
    summary = summarize_expressions(_expressions(10), max_items=3)

    assert summary.startswith("[PARAM(p0), PARAM(p1), PARAM(p2),")
    assert summary.endswith("+7 more]")


def test_sequence_summary_renders_only_the_listed_elements(monkeypatch):
    """``max_items`` より後ろの要素は render しない（出力だけでなく作業も有界）。"""

    rendered = []

    def _counting(expr, max_depth: int = 4) -> str:
        rendered.append(expr)
        return "x"

    monkeypatch.setattr(render, "summarize_expression", _counting)

    assert render.summarize_expressions(_expressions(50), max_items=4) == "[x, x, x, x, +46 more]"
    assert len(rendered) == 4


def test_sequence_summary_does_not_drain_an_iterable_of_unknown_length():
    """長さを名乗らない iterable は ``max_items + 1`` 個までしか読まない。"""

    items = _ExplosiveIterable(_expressions(1000), allowed=4)

    summary = summarize_expressions(items, max_items=3)

    assert summary == "[PARAM(p0), PARAM(p1), PARAM(p2), +more]"
    assert items.consumed == 4


def test_condition_sequence_summary_is_bounded_the_same_way():
    conditions = [Condition(Expression.parameter(f"p{index}")) for index in range(6)]

    assert summarize_conditions(conditions, max_items=2) == "[PARAM(p0), PARAM(p1), +4 more]"
    assert summarize_conditions(_ExplosiveIterable(conditions, allowed=3), max_items=2) == (
        "[PARAM(p0), PARAM(p1), +more]"
    )


def test_value_sequence_summary_bounds_both_the_count_and_each_element():
    assert summarize_values(["a", "b", "c"], max_items=2) == "[a, b, +1 more]"
    assert summarize_values(["x" * 200], max_text=8) == "[xxxxxxxx...]"
    assert summarize_values(None) == "[]"
    assert summarize_values([None]) == "[None]"


def test_repr_of_an_expanded_value_stays_bounded():
    """``repr()`` は暗黙に呼ばれるので、長い条件列でも先頭しか見ない。"""

    conditions = [Condition(Expression.parameter(f"p{index}")) for index in range(200)]

    text = repr(ExpandedValue(Expression.parameter("v"), conditions))

    assert "+192 more" in text
    assert len(text) < 400


def test_runtime_ref_summary_does_not_format_the_raw_object():
    class _Ref:
        def stable_key(self):
            return ("loop", "x" * 300, *range(50))

        def __repr__(self):  # pragma: no cover - 呼ばれたら失敗
            raise AssertionError("debug summary must not repr a runtime ref")

    summary = summarize_runtime_ref(_Ref())

    assert summary.startswith("_Ref[loop, ")
    assert "+44 more" in summary
    assert len(summary) < 300
