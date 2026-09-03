# -*- coding: utf-8 -*-
"""Debug-only expression rendering regressions."""

from unittest.mock import Mock

from scripts.function_tracer_pcode.analysis.returns.analyzer import ReturnAnalyzer
from scripts.function_tracer_pcode.core import Expression
from scripts.function_tracer_pcode.semantics.transform.expander import ExpressionExpander


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
