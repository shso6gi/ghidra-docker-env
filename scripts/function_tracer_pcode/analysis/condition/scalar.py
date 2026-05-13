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
from ...model.render_smt import expression_smt_bit_width
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
_SCALAR_AFFINE_MAX_NODES = 64


def _decompose_affine_expression(
    expr: Expression,
) -> Optional[Tuple[Optional[Expression], int, int]]:
    """Decompose expression into a base expression plus signed constant offset.

    Returns a tuple of:
    - optional base expression
    - signed integer constant offset
    - bit-width for normalized constants

    Only affine chains composed of INT_ADD/INT_SUB are accepted.
    """
    terms = [(expr, 1)]
    base_expr: Optional[Expression] = None
    offset = 0
    observed_bits = max(1, int(expression_smt_bit_width(expr) or 1))
    processed_nodes = 0

    while terms:
        if processed_nodes > _SCALAR_AFFINE_MAX_NODES:
            return None
        current, sign = terms.pop()
        if current is None:
            continue
        processed_nodes += 1

        if current.expr_type == ExpressionType.BINARY_OP and current.operator in {
            "INT_ADD",
            "INT_SUB",
        }:
            left, right = current.operands
            if current.operator == "INT_ADD":
                terms.append((left, sign))
                terms.append((right, sign))
            else:
                terms.append((left, sign))
                terms.append((right, -sign))
            continue

        constant_eval = eval_constant_raw(current)
        if constant_eval is not None:
            raw, bits = constant_eval
            bits = max(1, int(bits))
            offset += sign * to_signed_value(raw, bits)
            observed_bits = max(observed_bits, bits)
            continue

        if base_expr is None:
            base_expr = current
            observed_bits = max(
                observed_bits,
                max(1, int(expression_smt_bit_width(current) or 1)),
            )
            continue

        if base_expr.equals(current):
            # Non-unit coefficient for the same base would require richer handling.
            return None

        return None

    if base_expr is None:
        # Constant-only expression.
        return None, offset, observed_bits

    return base_expr, offset, observed_bits


def _stable_scalar_expr_key(expr: Expression) -> Optional[StructuralKey]:
    """Build a bounded structural key for scalar constraints."""

    rendered = expression_key_safe(
        expr,
        budget=_SCALAR_KEY_MAX_NODES,
        normalize_commutative=True,
    )
    return rendered


def _normalize_affine_constant(
    constant: int,
    base_offset: int,
    bits: int,
) -> int:
    """Shift constant by subtracting a base affine offset."""

    normalized_bits = max(1, bits)
    return normalize_raw_value(constant - base_offset, normalized_bits)


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
    left_decomp = _decompose_affine_expression(left)
    right_decomp = _decompose_affine_expression(right)
    if left_decomp is None or right_decomp is None:
        return None

    left_base, left_offset, left_bits = left_decomp
    right_base, right_offset, right_bits = right_decomp

    if left_base is None and right_base is None:
        return None

    if left_base is not None and right_base is not None:
        if not left_base.equals(right_base):
            return None
        # Both sides reference same affine base; constraint is constant-only and is
        # handled at later stages via direct truth evaluation.
        return None

    if left_base is not None:
        variable_expr = left_base
        variable_bits = left_bits
        const_raw = right_offset
        const_bits = right_bits
        base_offset = left_offset
        const_on_left = False
    else:
        variable_expr = right_base
        if variable_expr is None:
            return None
        variable_bits = right_bits
        const_raw = left_offset
        const_bits = left_bits
        base_offset = right_offset
        const_on_left = True

    variable_key = _stable_scalar_expr_key(variable_expr)
    if variable_key is None:
        return None

    bits = max(1, int(variable_bits), int(const_bits))
    if bits <= 0:
        return None

    if expr.operator in (
        "INT_SLESS",
        "INT_SLESSEQUAL",
        "INT_LESS",
        "INT_LESSEQUAL",
    ) and base_offset != 0:
        return None

    adjusted_constant_raw = _normalize_affine_constant(
        constant=const_raw,
        base_offset=base_offset,
        bits=bits,
    )
    constant_raw = normalize_raw_value(adjusted_constant_raw, bits)
    signed = expr.operator in ("INT_SLESS", "INT_SLESSEQUAL")
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

    if expr.operator not in (
        "INT_SLESS",
        "INT_SLESSEQUAL",
        "INT_LESS",
        "INT_LESSEQUAL",
    ):
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
