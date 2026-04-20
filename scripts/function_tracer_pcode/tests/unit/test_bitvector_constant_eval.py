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


def test_eval_constant_raw_handles_subpiece_and_piece_constants():
    low_word = Expression.binary_op(
        "SUBPIECE",
        Expression.constant(0x1122334455667788, 8),
        Expression.constant(0, 8),
    )
    high_word = Expression.binary_op(
        "SUBPIECE",
        Expression.constant(0x1122334455667788, 8),
        Expression.constant(4, 8),
    )
    rebuilt = Expression.binary_op("PIECE", high_word, low_word)
    rebuilt.size = 8

    assert eval_constant_raw(low_word) == (0x55667788, 32)
    assert eval_constant_raw(high_word) == (0x11223344, 32)
    assert eval_constant_raw(rebuilt) == (0x1122334455667788, 64)
