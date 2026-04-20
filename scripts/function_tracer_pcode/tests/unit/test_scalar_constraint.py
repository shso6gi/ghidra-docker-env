# -*- coding: utf-8 -*-
"""Scalar constraint extraction regressions."""

from scripts.function_tracer_pcode.analysis.condition.scalar import extract_scalar_constraint
from scripts.function_tracer_pcode.model import Condition, Expression, ExpressionType


def test_extract_scalar_constraint_handles_simple_affine_parameter():
    expr = Expression.binary_op(
        "INT_LESS",
        Expression.binary_op("INT_ADD", Expression.parameter("n"), Expression.constant(1, 4)),
        Expression.constant(8, 4),
    )

    fact = extract_scalar_constraint(Condition(expr, negated=False))

    assert fact is not None
    assert fact.kind == "upper"
    assert fact.expr.expr_type == ExpressionType.PARAMETER
    assert fact.expr.name == "n"


def test_extract_scalar_constraint_handles_subtract_affine_parameter():
    expr = Expression.binary_op(
        "INT_LESSEQUAL",
        Expression.binary_op("INT_SUB", Expression.parameter("n"), Expression.constant(2, 4)),
        Expression.constant(6, 4),
    )

    fact = extract_scalar_constraint(Condition(expr, negated=False))

    assert fact is not None
    assert fact.kind == "upper"
    assert fact.value == 8
    assert fact.expr.expr_type == ExpressionType.PARAMETER
    assert fact.expr.name == "n"


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


def test_extract_scalar_constraint_handles_right_hand_side_affine_form():
    expr = Expression.binary_op(
        "INT_LESS",
        Expression.constant(10, 4),
        Expression.binary_op(
            "INT_ADD",
            Expression.parameter("n"),
            Expression.constant(3, 4),
        ),
    )

    fact = extract_scalar_constraint(Condition(expr, negated=False))

    assert fact is not None
    assert fact.kind == "lower"
    assert fact.inclusive is False
    assert fact.value == 7
    assert fact.expr.expr_type == ExpressionType.PARAMETER
    assert fact.expr.name == "n"
