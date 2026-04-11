# -*- coding: utf-8 -*-
"""Safe canonicalization for simple arithmetic-series closed forms."""

from typing import Optional, Tuple

from ...model import Expression, ExpressionType
from .context import NormalizationContext


def normalize_series_patterns(
    expr: Expression,
    context: NormalizationContext,
) -> Expression:
    """Canonicalize equivalent quadratic closed forms for simple arithmetic series."""
    canonical = _match_sum_to_triangular(expr)
    if canonical is expr:
        return expr

    context.record_rule(
        rule_name="SERIES_CANONICALIZATION",
        before_expr=expr.to_smt(),
        after_expr=canonical.to_smt(),
        reason="Canonicalized equivalent arithmetic-series closed form",
    )
    return canonical


def _match_sum_to_triangular(expr: Expression) -> Expression:
    if expr.expr_type != ExpressionType.BINARY_OP or expr.operator != "INT_SUB" or len(expr.operands) != 2:
        return expr

    base_expr, square_term = _match_base_plus_square(expr.operands[0])
    if base_expr is None or square_term is None:
        return expr

    square_base = _match_square(square_term)
    if square_base is None:
        return expr

    square_origin = _match_var_plus_const(square_base)
    base_origin = _match_var_plus_const(base_expr)
    if square_origin is None or base_origin is None:
        return expr

    base_var, base_bias = base_origin
    square_var, square_bias = square_origin
    if not _same_nonconstant_expr(base_var, square_var):
        return expr
    if base_bias != 0 or square_bias != -1:
        return expr

    tri_operands = _match_half_product(expr.operands[1], target_size=expr.size or base_expr.size or 0)
    if tri_operands is None:
        return expr
    left_tri, right_tri = tri_operands
    left_origin = _match_var_plus_const(left_tri)
    right_origin = _match_var_plus_const(right_tri)
    if left_origin is None or right_origin is None:
        return expr

    left_var, left_bias = left_origin
    right_var, right_bias = right_origin
    if not _same_nonconstant_expr(base_var, left_var) or not _same_nonconstant_expr(base_var, right_var):
        return expr

    offsets = sorted([left_bias, right_bias])
    if offsets != [-2, -1]:
        return expr

    return _build_triangular(base_var, expr.size or base_var.size or 4)


def _match_base_plus_square(expr: Expression) -> Tuple[Optional[Expression], Optional[Expression]]:
    if expr.expr_type != ExpressionType.BINARY_OP or expr.operator != "INT_ADD" or len(expr.operands) != 2:
        return None, None
    left, right = expr.operands
    if _match_square(left) is not None:
        return right, left
    if _match_square(right) is not None:
        return left, right
    return None, None


def _match_square(expr: Expression) -> Optional[Expression]:
    if expr.expr_type != ExpressionType.BINARY_OP or expr.operator != "INT_MULT" or len(expr.operands) != 2:
        return None
    left, right = expr.operands
    if _same_nonconstant_expr(left, right):
        return left
    return None


def _match_half_product(expr: Expression, target_size: int) -> Optional[Tuple[Expression, Expression]]:
    inner = expr
    if (
        inner.expr_type == ExpressionType.BINARY_OP
        and inner.operator == "SUBPIECE"
        and len(inner.operands) == 2
        and inner.operands[1].expr_type == ExpressionType.CONSTANT
        and int(inner.operands[1].value) == 0
    ):
        inner = inner.operands[0]

    if inner.expr_type != ExpressionType.BINARY_OP or inner.operator != "INT_RIGHT" or len(inner.operands) != 2:
        return None
    shift = inner.operands[1]
    if shift.expr_type != ExpressionType.CONSTANT or int(shift.value) != 1:
        return None

    mult = inner.operands[0]
    if mult.expr_type != ExpressionType.BINARY_OP or mult.operator != "INT_MULT" or len(mult.operands) != 2:
        return None

    left = _strip_zero_extend(mult.operands[0], target_size)
    right = _strip_zero_extend(mult.operands[1], target_size)
    if left is None or right is None:
        return None
    return left, right


def _strip_zero_extend(expr: Expression, target_size: int) -> Optional[Expression]:
    if expr.expr_type == ExpressionType.UNARY_OP and expr.operator in {"INT_ZEXT", "INT_SEXT"} and expr.operands:
        inner = expr.operands[0]
        if target_size <= 0 or (inner.size and inner.size <= target_size):
            return inner
    return expr


def _match_var_plus_const(expr: Expression) -> Optional[Tuple[Expression, int]]:
    if expr.expr_type in {ExpressionType.PARAMETER, ExpressionType.VARIABLE}:
        return expr, 0

    if expr.expr_type != ExpressionType.BINARY_OP or len(expr.operands) != 2:
        return None

    left, right = expr.operands
    if expr.operator == "INT_ADD":
        left_const = _signed_const_value(left)
        right_const = _signed_const_value(right)
        if left_const is not None:
            return _with_bias(right, left_const)
        if right_const is not None:
            return _with_bias(left, right_const)
    if expr.operator == "INT_SUB" and right.expr_type == ExpressionType.CONSTANT:
        return _with_bias(left, -int(right.value))
    return None


def _with_bias(expr: Expression, bias: int) -> Optional[Tuple[Expression, int]]:
    if expr.expr_type in {ExpressionType.PARAMETER, ExpressionType.VARIABLE}:
        return expr, bias
    return None


def _same_nonconstant_expr(left: Expression, right: Expression) -> bool:
    try:
        return left.to_smt() == right.to_smt()
    except Exception:
        return left.to_string() == right.to_string()


def _build_triangular(base_expr: Expression, target_size: int) -> Expression:
    wide_size = max(8, target_size * 2)
    wide_base = Expression.unary_op("INT_ZEXT", base_expr)
    wide_base.size = wide_size
    wide_one = Expression.constant(1, wide_size)
    incremented = Expression.binary_op("INT_ADD", wide_base, wide_one)
    incremented.size = wide_size
    product = Expression.binary_op("INT_MULT", wide_base, incremented)
    product.size = wide_size
    shifted = Expression.binary_op("INT_RIGHT", product, wide_one)
    shifted.size = wide_size
    if wide_size == target_size:
        return shifted
    truncated = Expression.binary_op("SUBPIECE", shifted, Expression.constant(0, 4))
    truncated.size = target_size
    return truncated


def _signed_const_value(expr: Expression) -> Optional[int]:
    if expr.expr_type == ExpressionType.CONSTANT:
        return int(expr.value)
    if expr.expr_type == ExpressionType.UNARY_OP and expr.operator == "INT_2COMP" and expr.operands:
        inner = expr.operands[0]
        if inner.expr_type == ExpressionType.CONSTANT:
            return -int(inner.value)
    return None
