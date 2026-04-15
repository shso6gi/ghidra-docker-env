# -*- coding: utf-8 -*-
"""Scalar comparison extraction helpers for condition analysis."""

from dataclasses import dataclass
from typing import Optional, Tuple

from ...model import (
    Condition,
    Expression,
    ExpressionType,
    StructuralKey,
    expression_key_safe,
)
from .bitvector import eval_constant_raw, normalize_raw_value, to_signed_value


@dataclass(frozen=True)
class ScalarConstraint:
    """Single-variable scalar constraint derived from a condition."""

    key: Tuple[StructuralKey, int]
    kind: str
    expr: Expression
    raw_value: Optional[int] = None
    value: Optional[int] = None
    inclusive: Optional[bool] = None
    signed: bool = False


_SCALAR_KEY_MAX_NODES = 32


def _stable_scalar_expr_key(expr: Expression) -> Optional[StructuralKey]:
    """Build a bounded structural key for scalar constraints.

    We intentionally decline expressions that are too large or contain
    unsupported node types so contradiction checks stay cheap and conservative.
    """

    rendered = expression_key_safe(
        expr,
        budget=_SCALAR_KEY_MAX_NODES,
        normalize_commutative=True,
    )
    return rendered


def extract_scalar_constraint(condition: Condition) -> Optional[ScalarConstraint]:
    expr = condition.expression
    negated = condition.negated

    while expr.expr_type == ExpressionType.UNARY_OP and expr.operator == "BOOL_NEGATE":
        negated = not negated
        if expr.operands:
            expr = expr.operands[0]
        else:
            break

    if expr.expr_type != ExpressionType.BINARY_OP or len(expr.operands) != 2:
        return None

    left = expr.operands[0]
    right = expr.operands[1]
    left_eval = eval_constant_raw(left)
    right_eval = eval_constant_raw(right)

    if (left_eval is None) == (right_eval is None):
        return None

    if right_eval is not None:
        variable_expr = left
        const_raw, const_bits = right_eval
        const_on_left = False
    else:
        variable_expr = right
        assert left_eval is not None
        const_raw, const_bits = left_eval
        const_on_left = True

    variable_key = _stable_scalar_expr_key(variable_expr)
    if variable_key is None:
        return None
    bits = max(variable_expr.get_bit_width(), const_bits)
    signed = expr.operator in ("INT_SLESS", "INT_SLESSEQUAL")
    constant_raw = normalize_raw_value(const_raw, bits)
    constant_value = to_signed_value(constant_raw, bits) if signed else constant_raw

    if expr.operator == "INT_EQUAL":
        return ScalarConstraint(
            key=(variable_key, bits),
            kind="ne" if negated else "eq",
            raw_value=constant_raw,
            expr=variable_expr,
        )

    if expr.operator == "INT_NOTEQUAL":
        return ScalarConstraint(
            key=(variable_key, bits),
            kind="eq" if negated else "ne",
            raw_value=constant_raw,
            expr=variable_expr,
        )

    if expr.operator not in ("INT_SLESS", "INT_SLESSEQUAL", "INT_LESS", "INT_LESSEQUAL"):
        return None

    is_lessequal = expr.operator in ("INT_SLESSEQUAL", "INT_LESSEQUAL")
    if const_on_left:
        if negated:
            fact_kind = "upper"
            inclusive = not is_lessequal
        else:
            fact_kind = "lower"
            inclusive = is_lessequal
    else:
        if negated:
            fact_kind = "lower"
            inclusive = not is_lessequal
        else:
            fact_kind = "upper"
            inclusive = is_lessequal

    return ScalarConstraint(
        key=(variable_key, bits),
        kind=fact_kind,
        value=constant_value,
        inclusive=inclusive,
        signed=signed,
        expr=variable_expr,
    )
