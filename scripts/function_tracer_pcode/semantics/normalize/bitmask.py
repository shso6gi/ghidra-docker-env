# -*- coding: utf-8 -*-
"""Fact-aware bitmask and byte-reconstruction simplifications."""

from __future__ import annotations

from scripts.function_tracer_pcode.core.address_provenance import carries_image_address


from typing import List, Optional, Tuple

from scripts.function_tracer_pcode.core import Expression, ExpressionType
from scripts.function_tracer_pcode.semantics.normalize.context import NormalizationContext
from scripts.function_tracer_pcode.core.render_smt import render_expression_smt_evidence


def normalize_fact_mask_patterns(
    expr: Expression,
    context: NormalizationContext,
) -> Expression:
    """Simplify fact-proven masks and byte-wise reconstructions."""
    simplified = _simplify_shift_bounds(expr)
    if simplified is not expr:
        context.record_rule(
            rule_name="SHIFT_BOUND_SIMPLIFICATION",
            before_expr=render_expression_smt_evidence(expr),
            after_expr=render_expression_smt_evidence(simplified),
            reason="Collapsed width-bounded shift/subpiece into a constant",
        )
        expr = simplified

    simplified = _simplify_proven_boolean_compare(expr, context)
    if simplified is not expr:
        context.record_rule(
            rule_name="FACT_MASK_SIMPLIFICATION",
            before_expr=render_expression_smt_evidence(expr),
            after_expr=render_expression_smt_evidence(simplified),
            reason="Folded fact-proven comparison into a constant mask/guard",
        )
        expr = simplified

    simplified = _fold_constant_expression(expr)
    if simplified is not expr:
        context.record_rule(
            rule_name="CONSTANT_FOLDING",
            before_expr=render_expression_smt_evidence(expr),
            after_expr=render_expression_smt_evidence(simplified),
            reason="Folded constant bit-vector expression",
        )
        expr = simplified

    simplified = _reconstruct_contiguous_bytes(expr)
    if simplified is not expr:
        context.record_rule(
            rule_name="BYTE_RECONSTRUCTION",
            before_expr=render_expression_smt_evidence(expr),
            after_expr=render_expression_smt_evidence(simplified),
            reason="Reconstructed contiguous byte slices into the original value",
        )
        expr = simplified

    return expr


def _simplify_shift_bounds(expr: Expression) -> Expression:
    if expr.expr_type != ExpressionType.BINARY_OP or len(expr.operands) != 2:
        return expr

    left, right = expr.operands
    right_value = _const_value(right)
    if right_value is None:
        return expr

    if expr.operator == "INT_RIGHT":
        left_bits = left.get_bit_width()
        if left_bits > 0 and right_value >= left_bits:
            return Expression.constant(0, size=expr.size or left.size or 1)

    if expr.operator == "INT_LEFT":
        left_bits = left.get_bit_width()
        if left_bits > 0 and right_value >= left_bits:
            return Expression.constant(0, size=expr.size or left.size or 1)

    if expr.operator == "SUBPIECE":
        left_bits = left.get_bit_width()
        if left_bits > 0 and right_value * 8 >= left_bits:
            return Expression.constant(0, size=expr.size or 1)

    return expr


def _simplify_proven_boolean_compare(
    expr: Expression,
    context: NormalizationContext,
) -> Expression:
    if expr.expr_type != ExpressionType.BINARY_OP or len(expr.operands) != 2:
        return expr

    left, right = expr.operands
    result_size = expr.size or 1

    if expr.operator in {"INT_SLESS", "INT_LESS"} and _is_zero(left):
        if context.is_expr_pos(right):
            return Expression.constant(1, size=result_size)

    if expr.operator in {"INT_SLESSEQUAL", "INT_LESSEQUAL"} and _is_zero(left):
        if context.is_expr_nonneg(right):
            return Expression.constant(1, size=result_size)

    if expr.operator == "INT_NOTEQUAL":
        if _is_zero(right) and context.is_expr_nonzero(left):
            return Expression.constant(1, size=result_size)
        if _is_zero(left) and context.is_expr_nonzero(right):
            return Expression.constant(1, size=result_size)

    if expr.operator == "INT_EQUAL":
        if _is_zero(right) and context.is_expr_nonzero(left):
            return Expression.constant(0, size=result_size)
        if _is_zero(left) and context.is_expr_nonzero(right):
            return Expression.constant(0, size=result_size)

    return expr


def _fold_constant_expression(expr: Expression) -> Expression:
    # Issue #282: image の番地の出自を持つ定数は畳み込まない（新しい定数に出自を移せない）。畳み込むのは operand が
    # すべて定数のときだけなので、そのときだけ調べる（部分木を毎回辿らない）
    operands = list(expr.operands or ())
    if (
        operands
        and all(getattr(op, "expr_type", None) == ExpressionType.CONSTANT for op in operands)
        and any(carries_image_address(op) for op in operands)
    ):
        return expr
    if expr.expr_type == ExpressionType.UNARY_OP and expr.operands:
        operand = expr.operands[0]
        operand_value = _const_value(operand)
        if operand_value is None:
            return expr
        target_size = expr.size or operand.size or 1
        target_bits = max(1, target_size * 8)
        modulus = 1 << target_bits

        if expr.operator == "INT_ZEXT":
            return Expression.constant(operand_value % modulus, size=target_size)
        if expr.operator == "INT_SEXT":
            source_bits = max(1, operand.get_bit_width())
            mask = (1 << source_bits) - 1
            value = operand_value & mask
            if value & (1 << (source_bits - 1)):
                value |= (modulus - 1) ^ mask
            return Expression.constant(value % modulus, size=target_size)
        if expr.operator == "INT_2COMP":
            return Expression.constant((-operand_value) % modulus, size=target_size)
        if expr.operator == "INT_NEGATE":
            return Expression.constant((~operand_value) % modulus, size=target_size)
        return expr

    if expr.expr_type != ExpressionType.BINARY_OP or len(expr.operands) != 2:
        return expr

    left, right = expr.operands
    left_value = _const_value(left)
    right_value = _const_value(right)
    if left_value is None or right_value is None:
        return expr

    target_size = expr.size or max(left.size, right.size, 1)
    target_bits = max(1, target_size * 8)
    modulus = 1 << target_bits

    if expr.operator == "INT_ADD":
        return Expression.constant((left_value + right_value) % modulus, size=target_size)
    if expr.operator == "INT_SUB":
        return Expression.constant((left_value - right_value) % modulus, size=target_size)
    if expr.operator == "INT_MULT":
        return Expression.constant((left_value * right_value) % modulus, size=target_size)
    if expr.operator == "INT_AND":
        return Expression.constant(left_value & right_value, size=target_size)
    if expr.operator == "INT_OR":
        return Expression.constant((left_value | right_value) % modulus, size=target_size)
    if expr.operator == "INT_XOR":
        return Expression.constant((left_value ^ right_value) % modulus, size=target_size)
    if expr.operator == "INT_LEFT":
        return Expression.constant((left_value << right_value) % modulus, size=target_size)
    if expr.operator == "INT_RIGHT":
        return Expression.constant((left_value % modulus) >> right_value, size=target_size)
    if expr.operator == "INT_SRIGHT":
        signed_left = _to_signed(left_value, left.get_bit_width())
        return Expression.constant((signed_left >> right_value) % modulus, size=target_size)
    if expr.operator == "PIECE":
        low_bits = right.get_bit_width()
        return Expression.constant(((left_value << low_bits) | right_value) % modulus, size=target_size)
    if expr.operator == "SUBPIECE":
        source_bits = left.get_bit_width()
        source_mask = (1 << source_bits) - 1
        truncated = ((left_value & source_mask) >> (right_value * 8)) % modulus
        return Expression.constant(truncated, size=target_size)
    if expr.operator in {"INT_EQUAL", "INT_NOTEQUAL", "INT_LESS", "INT_SLESS", "INT_LESSEQUAL", "INT_SLESSEQUAL"}:
        result = _evaluate_constant_compare(expr.operator, left_value, right_value, left.get_bit_width(), right.get_bit_width())
        return Expression.constant(1 if result else 0, size=expr.size or 1)

    return expr


def _reconstruct_contiguous_bytes(expr: Expression) -> Expression:
    chunks = _flatten_piece_chunks(expr)
    if chunks is None or len(chunks) < 2:
        return expr

    extracted = [_extract_chunk_source(term) for term in chunks]
    if any(item is None for item in extracted):
        return expr

    source_expr = extracted[0][0]
    if any(not _same_expr(source_expr, item[0]) for item in extracted if item is not None):
        return expr

    running_offset = 0
    for _source, offset, chunk_size in reversed(extracted):
        if offset != running_offset:
            return expr
        running_offset += chunk_size

    target_size = running_offset
    if source_expr.size == target_size:
        return source_expr

    rebuilt = Expression.binary_op("SUBPIECE", source_expr, Expression.constant(0, size=4))
    rebuilt.size = target_size
    return rebuilt


def _flatten_piece_chunks(expr: Expression) -> Optional[List[Expression]]:
    if expr.size and expr.size > 0:
        chunk = _extract_chunk_source(expr)
        if chunk is not None:
            return [expr]
    if expr.expr_type != ExpressionType.BINARY_OP or expr.operator != "PIECE" or len(expr.operands) != 2:
        return None
    left_chunks = _flatten_piece_chunks(expr.operands[0])
    right_chunks = _flatten_piece_chunks(expr.operands[1])
    if left_chunks is None or right_chunks is None:
        return None
    return left_chunks + right_chunks


def _extract_chunk_source(expr: Expression) -> Optional[Tuple[Expression, int, int]]:
    if not expr.size or expr.size <= 0:
        return None

    if expr.expr_type == ExpressionType.BINARY_OP and expr.operator == "PIECE" and len(expr.operands) == 2:
        return None

    current = expr
    while current.expr_type == ExpressionType.UNARY_OP and current.operands:
        if current.operator not in {"INT_ZEXT", "INT_SEXT"}:
            break
        current = current.operands[0]

    if current.expr_type == ExpressionType.BINARY_OP and current.operator == "INT_AND" and len(current.operands) == 2:
        left, right = current.operands
        if _is_all_ones_mask_for_size(left, expr.size):
            return _extract_chunk_source(right)
        if _is_all_ones_mask_for_size(right, expr.size):
            return _extract_chunk_source(left)

    if (
        current.expr_type == ExpressionType.BINARY_OP
        and current.operator == "SUBPIECE"
        and len(current.operands) == 2
        and current.operands[1].expr_type == ExpressionType.CONSTANT
    ):
        offset = int(current.operands[1].value)
        return current.operands[0], offset, expr.size

    if (
        current.expr_type == ExpressionType.BINARY_OP
        and current.operator in {"INT_RIGHT", "INT_SRIGHT"}
        and len(current.operands) == 2
        and current.operands[1].expr_type == ExpressionType.CONSTANT
    ):
        shift_bits = int(current.operands[1].value)
        if shift_bits % 8 == 0:
            return current.operands[0], shift_bits // 8, expr.size

    return None


def _flatten_piece_bytes(expr: Expression) -> Optional[List[Expression]]:
    if expr.size == 1:
        return [expr]
    if expr.expr_type != ExpressionType.BINARY_OP or expr.operator != "PIECE" or len(expr.operands) != 2:
        return None
    left_bytes = _flatten_piece_bytes(expr.operands[0])
    right_bytes = _flatten_piece_bytes(expr.operands[1])
    if left_bytes is None or right_bytes is None:
        return None
    return left_bytes + right_bytes


def _is_zero(expr: Expression) -> bool:
    return expr.expr_type == ExpressionType.CONSTANT and int(expr.value) == 0


def _is_all_ones_mask_for_size(expr: Expression, size: int) -> bool:
    if expr.expr_type != ExpressionType.CONSTANT or size <= 0:
        return False
    mask = (1 << (size * 8)) - 1
    return (int(expr.value) & mask) == mask


def _const_value(expr: Expression) -> Optional[int]:
    if expr.expr_type == ExpressionType.CONSTANT:
        return int(expr.value)
    return None


def _same_expr(left: Expression, right: Expression) -> bool:
    return _expr_signature(left) == _expr_signature(right)


def _expr_signature(expr: Expression):
    from scripts.function_tracer_pcode.core import expression_key_or_identity

    return expression_key_or_identity(
        expr,
        normalize_commutative=True,
        strip_width_adapters=True,
        collapse_full_masks=True,
        include_memory_read_order=False,
    )


def _to_signed(value: int, bits: int) -> int:
    if bits <= 0:
        return value
    mask = (1 << bits) - 1
    value &= mask
    sign_bit = 1 << (bits - 1)
    if value & sign_bit:
        return value - (1 << bits)
    return value


def _evaluate_constant_compare(
    operator: str,
    left_value: int,
    right_value: int,
    left_bits: int,
    right_bits: int,
) -> bool:
    if operator == "INT_EQUAL":
        return left_value == right_value
    if operator == "INT_NOTEQUAL":
        return left_value != right_value
    if operator == "INT_LESS":
        return left_value < right_value
    if operator == "INT_LESSEQUAL":
        return left_value <= right_value
    if operator == "INT_SLESS":
        return _to_signed(left_value, left_bits) < _to_signed(right_value, right_bits)
    if operator == "INT_SLESSEQUAL":
        return _to_signed(left_value, left_bits) <= _to_signed(right_value, right_bits)
    return False
