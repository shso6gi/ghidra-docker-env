# -*- coding: utf-8 -*-
"""Shift amount normalization powered by range/origin facts."""

from scripts.function_tracer_pcode.core import Expression, ExpressionType
from scripts.function_tracer_pcode.semantics.normalize.context import NormalizationContext
from scripts.function_tracer_pcode.core.render_smt import render_expression_smt_evidence


SHIFT_OPS = frozenset({"INT_LEFT", "INT_RIGHT", "INT_SRIGHT"})


def normalize_shift_amounts(
    expr: Expression,
    context: NormalizationContext
) -> Expression:
    """
    Shift amount を安全に正規化する

    ルール:
    1. x & (2^k-1) -> x  if x < 2^k が facts から保証される
    2. sext(x) -> x      if x >= 0 が facts から保証される
    3. zext(x) -> x      if shift amount として使われている

    2,3 で extension を外しても、親の shift 演算レンダリング時に
    必要なら zero_extend されるため、shift count としての値は保存される。
    """
    if expr.expr_type != ExpressionType.BINARY_OP or expr.operator not in SHIFT_OPS:
        return expr

    if len(expr.operands) < 2:
        return expr

    left = expr.operands[0]
    right = expr.operands[1]

    if left.expr_type == ExpressionType.CONSTANT and int(left.value) == 0:
        zero = Expression.constant(0, size=expr.size or left.size)
        zero.size = expr.size or zero.size
        context.record_rule(
            rule_name="SHIFT_ZERO_SIMPLIFICATION",
            before_expr=render_expression_smt_evidence(expr),
            after_expr=render_expression_smt_evidence(zero),
            reason="Shifted zero remains zero for all shift counts",
        )
        return zero

    if right.expr_type == ExpressionType.CONSTANT and int(right.value) == 0:
        context.record_rule(
            rule_name="SHIFT_ZERO_SIMPLIFICATION",
            before_expr=render_expression_smt_evidence(expr),
            after_expr=render_expression_smt_evidence(left),
            reason="Shift by zero preserves the left operand",
        )
        return left

    normalized_right = _normalize_shift_count(right, context)
    if normalized_right is right:
        return expr

    normalized = Expression.binary_op(expr.operator, left, normalized_right)
    normalized.size = expr.size
    context.record_rule(
        rule_name="SHIFT_AMOUNT_NORMALIZATION",
        before_expr=render_expression_smt_evidence(expr),
        after_expr=render_expression_smt_evidence(normalized),
        reason="Normalized shift count using range/origin facts",
    )
    return normalized


def _normalize_shift_count(
    expr: Expression,
    context: NormalizationContext
) -> Expression:
    current = expr

    while True:
        next_expr = _normalize_shift_count_once(current, context)
        if next_expr is current:
            return current
        current = next_expr


def _normalize_shift_count_once(
    expr: Expression,
    context: NormalizationContext
) -> Expression:
    if expr.expr_type == ExpressionType.BINARY_OP and expr.operator == "INT_AND":
        simplified = _normalize_masked_shift_count(expr, context)
        if simplified is not expr:
            return simplified

    if expr.expr_type == ExpressionType.UNARY_OP and expr.operator in {"INT_SEXT", "INT_ZEXT"}:
        simplified = _normalize_extended_shift_count(expr, context)
        if simplified is not expr:
            return simplified

    return expr


def _normalize_masked_shift_count(
    expr: Expression,
    context: NormalizationContext
) -> Expression:
    if len(expr.operands) != 2:
        return expr

    left, right = expr.operands
    mask_operand = None
    value_operand = None

    if left.expr_type == ExpressionType.CONSTANT:
        mask_operand = left
        value_operand = right
    elif right.expr_type == ExpressionType.CONSTANT:
        mask_operand = right
        value_operand = left
    else:
        return expr

    mask_value = mask_operand.value
    if not isinstance(mask_value, int) or mask_value < 0:
        return expr

    if not _is_all_ones_mask(mask_value):
        return expr

    var_name = _extract_origin_var_name(value_operand)
    if not var_name:
        return expr

    if not context.has_upper_bound_le(var_name, mask_value + 1):
        return expr

    return value_operand


def _normalize_extended_shift_count(
    expr: Expression,
    context: NormalizationContext
) -> Expression:
    if not expr.operands:
        return expr

    inner = expr.operands[0]
    if inner.expr_type not in (ExpressionType.PARAMETER, ExpressionType.VARIABLE):
        return expr

    if expr.operator == "INT_ZEXT":
        return inner

    var_name = inner.name
    if not var_name:
        return expr

    inner_bits = inner.get_bit_width()
    sign_safe_limit = 1 << (inner_bits - 1)
    if context.has_upper_bound_le(var_name, sign_safe_limit) or context.is_nonneg(var_name):
        return inner

    return expr


def _extract_origin_var_name(expr: Expression):
    if expr.expr_type in (ExpressionType.PARAMETER, ExpressionType.VARIABLE):
        return expr.name

    if expr.expr_type == ExpressionType.UNARY_OP and expr.operator in {"INT_SEXT", "INT_ZEXT"}:
        if expr.operands:
            inner = expr.operands[0]
            if inner.expr_type in (ExpressionType.PARAMETER, ExpressionType.VARIABLE):
                return inner.name

    return None


def _is_all_ones_mask(value: int) -> bool:
    return value >= 0 and (value & (value + 1)) == 0
