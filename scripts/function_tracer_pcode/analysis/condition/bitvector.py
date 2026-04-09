# -*- coding: utf-8 -*-
"""Bit-vector constant evaluation helpers for condition analysis."""

from typing import Optional, Tuple

from ...model import Expression, ExpressionType


def normalize_raw_value(value: int, bits: int) -> int:
    if bits <= 0:
        return value
    return value % (1 << bits)


def to_signed_value(value: int, bits: int) -> int:
    if bits <= 0:
        return value
    sign_bit = 1 << (bits - 1)
    if value & sign_bit:
        return value - (1 << bits)
    return value


def eval_constant_raw(expr: Expression) -> Optional[Tuple[int, int]]:
    if expr is None:
        return None

    bits = expr.get_bit_width()

    if expr.expr_type == ExpressionType.CONSTANT:
        return (normalize_raw_value(int(expr.value), bits), bits)

    if expr.expr_type == ExpressionType.LITERAL:
        try:
            return (normalize_raw_value(int(expr.value, 0), bits), bits)
        except (TypeError, ValueError):
            return None

    if expr.expr_type == ExpressionType.UNARY_OP and expr.operands:
        operand_eval = eval_constant_raw(expr.operands[0])
        if operand_eval is None:
            return None
        operand_raw, operand_bits = operand_eval
        operand_signed = to_signed_value(operand_raw, operand_bits)

        if expr.operator in ("COPY", "CAST", "INT_ZEXT"):
            return (normalize_raw_value(operand_raw, bits), bits)
        if expr.operator == "INT_SEXT":
            return (normalize_raw_value(operand_signed, bits), bits)
        if expr.operator == "INT_NEGATE":
            return (normalize_raw_value(~operand_raw, bits), bits)
        if expr.operator == "INT_2COMP":
            return (normalize_raw_value(-operand_signed, bits), bits)
        if expr.operator == "BOOL_NEGATE":
            return (0 if operand_raw else 1, 1)
        return None

    if expr.expr_type == ExpressionType.BINARY_OP and len(expr.operands) == 2:
        left_eval = eval_constant_raw(expr.operands[0])
        right_eval = eval_constant_raw(expr.operands[1])
        if left_eval is None or right_eval is None:
            return None

        left_raw, left_bits = left_eval
        right_raw, right_bits = right_eval
        left_signed = to_signed_value(left_raw, left_bits)
        right_signed = to_signed_value(right_raw, right_bits)

        if expr.operator == "INT_ADD":
            return (normalize_raw_value(left_raw + right_raw, bits), bits)
        if expr.operator == "INT_SUB":
            return (normalize_raw_value(left_raw - right_raw, bits), bits)
        if expr.operator == "INT_MULT":
            return (normalize_raw_value(left_raw * right_raw, bits), bits)
        if expr.operator == "INT_AND":
            return (normalize_raw_value(left_raw & right_raw, bits), bits)
        if expr.operator == "INT_OR":
            return (normalize_raw_value(left_raw | right_raw, bits), bits)
        if expr.operator in ("INT_XOR", "BOOL_XOR"):
            return (normalize_raw_value(left_raw ^ right_raw, bits), bits)
        if expr.operator == "INT_LEFT":
            return (normalize_raw_value(left_raw << right_raw, bits), bits)
        if expr.operator == "INT_RIGHT":
            return (normalize_raw_value(left_raw >> right_raw, bits), bits)
        if expr.operator == "INT_SRIGHT":
            return (normalize_raw_value(left_signed >> right_raw, bits), bits)
        if expr.operator in ("INT_DIV", "DIV"):
            if right_raw == 0:
                return None
            return (normalize_raw_value(left_raw // right_raw, bits), bits)
        if expr.operator in ("INT_SDIV", "SDIV"):
            if right_signed == 0:
                return None
            quotient = abs(left_signed) // abs(right_signed)
            if (left_signed < 0) ^ (right_signed < 0):
                quotient = -quotient
            return (normalize_raw_value(quotient, bits), bits)
        if expr.operator == "INT_EQUAL":
            return (1 if left_raw == right_raw else 0, 1)
        if expr.operator == "INT_NOTEQUAL":
            return (1 if left_raw != right_raw else 0, 1)
        if expr.operator == "INT_LESS":
            return (1 if left_raw < right_raw else 0, 1)
        if expr.operator == "INT_LESSEQUAL":
            return (1 if left_raw <= right_raw else 0, 1)
        if expr.operator == "INT_SLESS":
            return (1 if left_signed < right_signed else 0, 1)
        if expr.operator == "INT_SLESSEQUAL":
            return (1 if left_signed <= right_signed else 0, 1)
        if expr.operator == "BOOL_AND":
            return (1 if left_raw and right_raw else 0, 1)
        if expr.operator == "BOOL_OR":
            return (1 if left_raw or right_raw else 0, 1)

    return None
