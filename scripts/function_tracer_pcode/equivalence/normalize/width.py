# -*- coding: utf-8 -*-
"""Safe width-adapter simplifications."""

from ...model import Expression, ExpressionType
from .context import NormalizationContext


def normalize_width_adapters(
    expr: Expression,
    context: NormalizationContext,
) -> Expression:
    """Collapse redundant width adapters without changing bitvector semantics."""
    simplified = expr

    if expr.expr_type == ExpressionType.UNARY_OP:
        simplified = _normalize_extension(expr)
    elif expr.expr_type == ExpressionType.BINARY_OP and expr.operator in {"INT_RIGHT", "INT_SRIGHT"}:
        simplified = _normalize_shifted_piece(expr)
    elif expr.expr_type == ExpressionType.BINARY_OP and expr.operator == "INT_AND":
        simplified = _normalize_low_mask(expr)
    elif expr.expr_type == ExpressionType.BINARY_OP and expr.operator == "SUBPIECE":
        simplified = _normalize_subpiece(expr)

    if simplified is expr:
        return expr

    context.record_rule(
        rule_name="WIDTH_ADAPTER_SIMPLIFICATION",
        before_expr=expr.to_smt(),
        after_expr=simplified.to_smt(),
        reason="Collapsed redundant extension/subpiece pattern",
    )
    return simplified


def _normalize_extension(expr: Expression) -> Expression:
    if expr.operator not in {"INT_ZEXT", "INT_SEXT"} or len(expr.operands) != 1:
        return expr

    operand = expr.operands[0]
    target_size = expr.size or operand.size
    if target_size <= 0:
        return expr

    if operand.expr_type == ExpressionType.CONSTANT:
        source_bits = max(1, operand.get_bit_width())
        target_bits = target_size * 8
        mask = (1 << source_bits) - 1
        value = int(operand.value) & mask
        if expr.operator == "INT_SEXT" and source_bits > 0 and (value & (1 << (source_bits - 1))):
            value |= ((1 << target_bits) - 1) ^ mask
        else:
            value &= (1 << target_bits) - 1
        folded = Expression.constant(value, target_size)
        folded.size = target_size
        return folded

    if operand.size and operand.size == target_size:
        return operand

    return expr


def _normalize_subpiece(expr: Expression) -> Expression:
    if len(expr.operands) != 2:
        return expr

    source, offset = expr.operands
    if offset.expr_type != ExpressionType.CONSTANT:
        return expr

    target_size = expr.size or 0
    byte_offset = int(offset.value)

    if byte_offset == 0 and source.size and target_size and source.size == target_size:
        return source

    if (
        byte_offset == 0
        and source.expr_type == ExpressionType.UNARY_OP
        and source.operator in {"INT_ZEXT", "INT_SEXT"}
        and source.operands
    ):
        inner = source.operands[0]
        if inner.size and target_size and inner.size == target_size:
            return inner

    if byte_offset == 0 and source.expr_type == ExpressionType.CONSTANT and target_size > 0:
        target_bits = target_size * 8
        value = int(source.value) & ((1 << target_bits) - 1)
        folded = Expression.constant(value, target_size)
        folded.size = target_size
        return folded

    if (
        source.expr_type == ExpressionType.BINARY_OP
        and source.operator == "PIECE"
        and len(source.operands) == 2
        and source.operands[0].size
        and source.operands[1].size
        and target_size > 0
    ):
        high, low = source.operands
        low_size = low.size
        high_size = high.size

        if byte_offset == 0 and target_size <= low_size:
            if target_size == low_size:
                return low
            truncated = Expression.binary_op("SUBPIECE", low, Expression.constant(0, 4))
            truncated.size = target_size
            return truncated

        if byte_offset >= low_size:
            high_offset = byte_offset - low_size
            if high_offset == 0 and target_size <= high_size:
                if target_size == high_size:
                    return high
                truncated = Expression.binary_op("SUBPIECE", high, Expression.constant(0, 4))
                truncated.size = target_size
                return truncated
            if high_offset > 0 and high_offset < high_size and high_offset + target_size <= high_size:
                truncated = Expression.binary_op("SUBPIECE", high, Expression.constant(high_offset, 4))
                truncated.size = target_size
                return truncated

    return expr


def _normalize_shifted_piece(expr: Expression) -> Expression:
    if len(expr.operands) != 2:
        return expr

    source, amount = expr.operands
    if (
        amount.expr_type != ExpressionType.CONSTANT
        or source.expr_type != ExpressionType.BINARY_OP
        or source.operator != "PIECE"
        or len(source.operands) != 2
    ):
        return expr

    high, low = source.operands
    if not high.size or not low.size:
        return expr

    shift_bits = int(amount.value)
    low_bits = low.size * 8
    if shift_bits < low_bits or shift_bits % 8 != 0:
        return expr

    remaining_bits = shift_bits - low_bits
    if remaining_bits == 0:
        if expr.size == high.size:
            return high
        widened = Expression.unary_op("INT_ZEXT", high)
        widened.size = expr.size or source.size or high.size
        return widened

    if remaining_bits % 8 != 0:
        return expr

    shifted_high = Expression.binary_op(
        expr.operator,
        high,
        Expression.constant(remaining_bits, size=amount.size or 4),
    )
    shifted_high.size = expr.size or high.size
    return shifted_high


def _normalize_low_mask(expr: Expression) -> Expression:
    if len(expr.operands) != 2:
        return expr

    left, right = expr.operands
    mask_expr = left if left.expr_type == ExpressionType.CONSTANT else right if right.expr_type == ExpressionType.CONSTANT else None
    value_expr = right if mask_expr is left else left if mask_expr is right else None
    if mask_expr is None or value_expr is None:
        return expr

    mask_value = int(mask_expr.value)
    if mask_value < 0 or (mask_value & (mask_value + 1)) != 0:
        return expr

    mask_bits = mask_value.bit_length()
    if mask_bits <= 0 or mask_bits % 8 != 0:
        return expr

    target_size = mask_bits // 8
    if value_expr.size and value_expr.size == target_size:
        return value_expr

    truncated = Expression.binary_op("SUBPIECE", value_expr, Expression.constant(0, 4))
    truncated.size = target_size
    return truncated
