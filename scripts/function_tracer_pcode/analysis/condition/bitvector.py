# -*- coding: utf-8 -*-
"""Bit-vector constant evaluation helpers for condition analysis."""

from typing import Dict, Optional, Set, Tuple

from ...model import Expression, ExpressionType


_EVAL_CACHE_LIMIT = 4096
_eval_cache: Dict[Expression, Optional[Tuple[int, int]]] = {}


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
    return _eval_constant_raw_internal(expr, set())


def _default_bits(expr: Expression) -> int:
    size = getattr(expr, "size", 0) or 0
    if size > 0:
        return size * 8

    if expr.expr_type == ExpressionType.BINARY_OP:
        if expr.operator in (
            "INT_EQUAL",
            "INT_NOTEQUAL",
            "INT_LESS",
            "INT_LESSEQUAL",
            "INT_SLESS",
            "INT_SLESSEQUAL",
            "BOOL_AND",
            "BOOL_OR",
            "BOOL_XOR",
        ):
            return 1

    if expr.expr_type == ExpressionType.UNARY_OP and expr.operator == "BOOL_NEGATE":
        return 1

    return 32


def _remember(expr: Expression, value: Optional[Tuple[int, int]]) -> Optional[Tuple[int, int]]:
    if len(_eval_cache) >= _EVAL_CACHE_LIMIT:
        _eval_cache.clear()
    _eval_cache[expr] = value
    return value


def _eval_constant_raw_internal(
    expr: Optional[Expression],
    visiting: Set[Expression],
) -> Optional[Tuple[int, int]]:
    if expr is None:
        return None

    cached = _eval_cache.get(expr)
    if cached is not None or expr in _eval_cache:
        return cached

    if expr in visiting:
        return _remember(expr, None)

    expr_type = expr.expr_type
    if expr_type in (
        ExpressionType.PARAMETER,
        ExpressionType.VARIABLE,
        ExpressionType.CALL,
        ExpressionType.MEMORY,
        ExpressionType.PHI,
        ExpressionType.UNKNOWN,
    ):
        return _remember(expr, None)

    visiting.add(expr)
    try:
        if expr_type == ExpressionType.CONSTANT:
            bits = _default_bits(expr)
            return _remember(expr, (normalize_raw_value(int(expr.value), bits), bits))

        if expr_type == ExpressionType.LITERAL:
            try:
                bits = _default_bits(expr)
                return _remember(expr, (normalize_raw_value(int(expr.value, 0), bits), bits))
            except (TypeError, ValueError):
                return _remember(expr, None)

        if expr_type == ExpressionType.UNARY_OP and expr.operands:
            operand_eval = _eval_constant_raw_internal(expr.operands[0], visiting)
            if operand_eval is None:
                return _remember(expr, None)
            operand_raw, operand_bits = operand_eval
            operand_signed = to_signed_value(operand_raw, operand_bits)
            bits = _default_bits(expr) if expr.operator != "BOOL_NEGATE" else 1

            if expr.operator in ("COPY", "CAST", "INT_ZEXT"):
                return _remember(expr, (normalize_raw_value(operand_raw, bits), bits))
            if expr.operator == "INT_SEXT":
                return _remember(expr, (normalize_raw_value(operand_signed, bits), bits))
            if expr.operator == "INT_NEGATE":
                return _remember(expr, (normalize_raw_value(~operand_raw, bits), bits))
            if expr.operator == "INT_2COMP":
                return _remember(expr, (normalize_raw_value(-operand_signed, bits), bits))
            if expr.operator == "BOOL_NEGATE":
                return _remember(expr, (0 if operand_raw else 1, 1))
            return _remember(expr, None)

        if expr_type == ExpressionType.INTRINSIC and expr.operands:
            operand_evals = [
                _eval_constant_raw_internal(operand, visiting)
                for operand in expr.operands
            ]
            if any(value is None for value in operand_evals):
                return _remember(expr, None)

            resolved = [value for value in operand_evals if value is not None]
            raw_values = [raw for raw, _bits in resolved]
            signed_values = [to_signed_value(raw, bits) for raw, bits in resolved]
            bits = _default_bits(expr)
            name = getattr(expr, "name", None) or ""

            if name in ("COPY", "CAST", "INT_ZEXT") and raw_values:
                return _remember(expr, (normalize_raw_value(raw_values[0], bits), bits))
            if name == "INT_SEXT" and raw_values:
                return _remember(expr, (normalize_raw_value(signed_values[0], bits), bits))
            if name in {"INT_ADD", "PTRSUB"} and len(raw_values) >= 2:
                return _remember(expr, (normalize_raw_value(raw_values[0] + raw_values[1], bits), bits))
            if name == "PTRADD":
                if len(raw_values) >= 3:
                    return _remember(
                        expr,
                        (normalize_raw_value(raw_values[0] + (raw_values[1] * raw_values[2]), bits), bits),
                    )
                if len(raw_values) >= 2:
                    return _remember(expr, (normalize_raw_value(raw_values[0] + raw_values[1], bits), bits))
            return _remember(expr, None)

        if expr_type == ExpressionType.BINARY_OP and len(expr.operands) == 2:
            left_eval = _eval_constant_raw_internal(expr.operands[0], visiting)
            if left_eval is None:
                return _remember(expr, None)
            right_eval = _eval_constant_raw_internal(expr.operands[1], visiting)
            if right_eval is None:
                return _remember(expr, None)

            left_raw, left_bits = left_eval
            right_raw, right_bits = right_eval
            left_signed = to_signed_value(left_raw, left_bits)
            right_signed = to_signed_value(right_raw, right_bits)
            bits = _default_bits(expr)

            if expr.operator == "INT_ADD":
                return _remember(expr, (normalize_raw_value(left_raw + right_raw, bits), bits))
            if expr.operator == "INT_SUB":
                return _remember(expr, (normalize_raw_value(left_raw - right_raw, bits), bits))
            if expr.operator == "INT_MULT":
                return _remember(expr, (normalize_raw_value(left_raw * right_raw, bits), bits))
            if expr.operator == "INT_AND":
                return _remember(expr, (normalize_raw_value(left_raw & right_raw, bits), bits))
            if expr.operator == "INT_OR":
                return _remember(expr, (normalize_raw_value(left_raw | right_raw, bits), bits))
            if expr.operator in ("INT_XOR", "BOOL_XOR"):
                return _remember(expr, (normalize_raw_value(left_raw ^ right_raw, bits), bits))
            if expr.operator == "INT_LEFT":
                return _remember(expr, (normalize_raw_value(left_raw << right_raw, bits), bits))
            if expr.operator == "INT_RIGHT":
                return _remember(expr, (normalize_raw_value(left_raw >> right_raw, bits), bits))
            if expr.operator == "INT_SRIGHT":
                return _remember(expr, (normalize_raw_value(left_signed >> right_raw, bits), bits))
            if expr.operator in ("INT_DIV", "DIV"):
                if right_raw == 0:
                    return _remember(expr, None)
                return _remember(expr, (normalize_raw_value(left_raw // right_raw, bits), bits))
            if expr.operator in ("INT_SDIV", "SDIV"):
                if right_signed == 0:
                    return _remember(expr, None)
                quotient = abs(left_signed) // abs(right_signed)
                if (left_signed < 0) ^ (right_signed < 0):
                    quotient = -quotient
                return _remember(expr, (normalize_raw_value(quotient, bits), bits))
            if expr.operator == "INT_EQUAL":
                return _remember(expr, (1 if left_raw == right_raw else 0, 1))
            if expr.operator == "INT_NOTEQUAL":
                return _remember(expr, (1 if left_raw != right_raw else 0, 1))
            if expr.operator == "INT_LESS":
                return _remember(expr, (1 if left_raw < right_raw else 0, 1))
            if expr.operator == "INT_LESSEQUAL":
                return _remember(expr, (1 if left_raw <= right_raw else 0, 1))
            if expr.operator == "INT_SLESS":
                return _remember(expr, (1 if left_signed < right_signed else 0, 1))
            if expr.operator == "INT_SLESSEQUAL":
                return _remember(expr, (1 if left_signed <= right_signed else 0, 1))
            if expr.operator == "BOOL_AND":
                return _remember(expr, (1 if left_raw and right_raw else 0, 1))
            if expr.operator == "BOOL_OR":
                return _remember(expr, (1 if left_raw or right_raw else 0, 1))

        return _remember(expr, None)
    finally:
        visiting.discard(expr)
