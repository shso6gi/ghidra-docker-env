# -*- coding: utf-8 -*-
"""Normalize branch-conditioned absolute-value idioms."""

from ...model import Expression, ExpressionType
from .context import NormalizationContext


def normalize_bitwise_abs(
    expr: Expression,
    context: NormalizationContext,
) -> Expression:
    """
    `abs(x)` のビットハックを facts に基づいて単純化する。

    パターン:
      ((x >> (w-1)) + x) ^ (x >> (w-1))

    facts:
      - x >= 0 なら x
      - x < 0 なら -x
    """
    if expr.expr_type != ExpressionType.BINARY_OP or expr.operator != "INT_XOR":
        return expr

    if len(expr.operands) != 2:
        return expr

    simplified = _rewrite_abs_if_sign_known(expr.operands[0], expr.operands[1], expr.size, context)
    if simplified is not None:
        return simplified

    return expr


def _rewrite_abs_if_sign_known(
    left: Expression,
    right: Expression,
    result_size: int,
    context: NormalizationContext,
):
    shift_expr, add_expr = _split_shift_and_add(left, right)
    if shift_expr is None or add_expr is None:
        return None

    inner = _extract_abs_inner(shift_expr, add_expr)
    if inner is None:
        return None

    if context.is_expr_nonneg(inner):
        context.record_rule(
            rule_name="BITWISE_ABS_CANONICALIZATION",
            before_expr=Expression.binary_op("INT_XOR", left, right).to_smt(),
            after_expr=inner.to_smt(),
            reason="Reduced abs bit-hack to original value using nonnegative fact",
        )
        return inner

    if context.is_expr_neg(inner):
        negated = Expression.unary_op("INT_2COMP", inner)
        negated.size = inner.size
        context.record_rule(
            rule_name="BITWISE_ABS_CANONICALIZATION",
            before_expr=Expression.binary_op("INT_XOR", left, right).to_smt(),
            after_expr=negated.to_smt(),
            reason="Reduced abs bit-hack to negation using negative fact",
        )
        return negated

    return None


def _split_shift_and_add(left: Expression, right: Expression):
    if _is_sign_mask(left) and _is_add(right):
        return left, right
    if _is_sign_mask(right) and _is_add(left):
        return right, left
    return None, None


def _extract_abs_inner(shift_expr: Expression, add_expr: Expression):
    if len(shift_expr.operands) != 2 or len(add_expr.operands) != 2:
        return None

    inner = shift_expr.operands[0]
    if not _is_sign_shift_amount(shift_expr.operands[1], inner):
        return None

    add_left, add_right = add_expr.operands
    if _same_expr(add_left, inner) and _same_expr(add_right, shift_expr):
        return inner
    if _same_expr(add_right, inner) and _same_expr(add_left, shift_expr):
        return inner
    return None


def _is_sign_mask(expr: Expression) -> bool:
    return (
        expr.expr_type == ExpressionType.BINARY_OP
        and expr.operator == "INT_SRIGHT"
        and len(expr.operands) == 2
        and _is_sign_shift_amount(expr.operands[1], expr.operands[0])
    )


def _is_add(expr: Expression) -> bool:
    return expr.expr_type == ExpressionType.BINARY_OP and expr.operator == "INT_ADD"


def _is_sign_shift_amount(amount: Expression, value: Expression) -> bool:
    if amount.expr_type != ExpressionType.CONSTANT:
        return False
    value_bits = value.get_bit_width()
    return amount.value == value_bits - 1


def _same_expr(lhs: Expression, rhs: Expression) -> bool:
    return lhs.structural_key(normalize_commutative=True) == rhs.structural_key(
        normalize_commutative=True
    )
