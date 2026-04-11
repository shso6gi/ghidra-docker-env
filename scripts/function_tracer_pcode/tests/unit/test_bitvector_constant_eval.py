# -*- coding: utf-8 -*-
"""Bit-vector constant evaluation regressions."""

from scripts.function_tracer_pcode.analysis.condition.bitvector import eval_constant_raw
from scripts.function_tracer_pcode.model import Expression


def test_eval_constant_raw_short_circuits_large_nonconstant_expression(monkeypatch):
    expr = Expression.parameter("n")
    for _ in range(64):
        expr = Expression.binary_op("INT_ADD", expr, Expression.constant(1, 4))

    def _boom(_self):
        raise AssertionError("non-constant evaluation should not need get_bit_width")

    monkeypatch.setattr(Expression, "get_bit_width", _boom)

    assert eval_constant_raw(expr) is None


def test_eval_constant_raw_preserves_simple_constant_arithmetic():
    expr = Expression.binary_op(
        "INT_ADD",
        Expression.constant(3, 4),
        Expression.constant(5, 4),
    )

    assert eval_constant_raw(expr) == (8, 32)
