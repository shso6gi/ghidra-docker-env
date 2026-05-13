# -*- coding: utf-8 -*-
"""Scalar constraint extraction regressions."""

from scripts.function_tracer_pcode.analysis.condition.scalar import extract_scalar_constraint
from scripts.function_tracer_pcode.analysis.condition.simplifier import ConditionSimplifier
from scripts.function_tracer_pcode.model import Condition, Expression, ExpressionType


def test_extract_scalar_constraint_rejects_affine_parameter_inequality_without_overflow_proof():
    expr = Expression.binary_op(
        "INT_LESS",
        Expression.binary_op("INT_ADD", Expression.parameter("n"), Expression.constant(1, 4)),
        Expression.constant(8, 4),
    )

    fact = extract_scalar_constraint(Condition(expr, negated=False))

    assert fact is None


def test_extract_scalar_constraint_rejects_subtract_affine_parameter_inequality_without_overflow_proof():
    expr = Expression.binary_op(
        "INT_LESSEQUAL",
        Expression.binary_op("INT_SUB", Expression.parameter("n"), Expression.constant(2, 4)),
        Expression.constant(6, 4),
    )

    fact = extract_scalar_constraint(Condition(expr, negated=False))

    assert fact is None


def test_extract_scalar_constraint_handles_affine_parameter_equality_modulo_width():
    expr = Expression.binary_op(
        "INT_EQUAL",
        Expression.binary_op("INT_SUB", Expression.parameter("n"), Expression.constant(2, 4)),
        Expression.constant(6, 4),
    )

    fact = extract_scalar_constraint(Condition(expr, negated=False))

    assert fact is not None
    assert fact.kind == "eq"
    assert fact.raw_value == 8
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


def test_extract_scalar_constraint_rejects_right_hand_side_affine_inequality_without_overflow_proof():
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

    assert fact is None


def test_subtract_implied_conditions_keeps_signed_lower_bound_across_wrapping_subtract_guard():
    n = Expression.parameter("n", size=4, data_type="int")
    lower = Condition(
        Expression.binary_op("INT_SLESSEQUAL", Expression.constant(1, 4), n),
        negated=False,
    )
    shifted = Condition(
        Expression.binary_op(
            "INT_SLESSEQUAL",
            Expression.constant(3, 4),
            Expression.binary_op("INT_SUB", n, Expression.constant(4, 4)),
        ),
        negated=False,
    )

    residual = ConditionSimplifier.subtract_implied_conditions([lower], [shifted])

    assert len(residual) == 1
    assert residual[0].expression.equals(lower.expression)
