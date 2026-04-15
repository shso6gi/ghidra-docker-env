# -*- coding: utf-8 -*-
"""Scalar constraint extraction regressions."""

from scripts.function_tracer_pcode.analysis.condition.scalar import extract_scalar_constraint
from scripts.function_tracer_pcode.model import Condition, Expression


def test_extract_scalar_constraint_handles_simple_affine_parameter():
    expr = Expression.binary_op(
        "INT_LESS",
        Expression.binary_op("INT_ADD", Expression.parameter("n"), Expression.constant(1, 4)),
        Expression.constant(8, 4),
    )

    fact = extract_scalar_constraint(Condition(expr, negated=False))

    assert fact is not None
    assert fact.kind == "upper"
    assert fact.key[0][0] == "binary"
    assert fact.key[0][1] == "INT_ADD"


def test_extract_scalar_constraint_skips_overly_complex_expression_without_to_string(monkeypatch):
    huge = Expression.parameter("n")
    for _ in range(64):
        huge = Expression.binary_op("INT_ADD", huge, Expression.constant(1, 4))

    expr = Expression.binary_op("INT_LESS", huge, Expression.constant(100, 4))

    def _boom(_self, simplify=True):
        raise AssertionError("to_string should not be used by scalar extraction")

    monkeypatch.setattr(Expression, "to_string", _boom)

    fact = extract_scalar_constraint(Condition(expr, negated=False))

    assert fact is None
