# -*- coding: utf-8 -*-
"""Python-like rendering helpers for Expression."""

from typing import Dict, Optional


def expression_to_string(expr, simplify: bool = True) -> str:
    """式を Python 互換の文字列へ変換する。"""
    return _to_string_internal(expr, simplify)


def _to_string_internal(expr, simplify: bool) -> str:
    expr_type = expr.expr_type
    expr_kind = expr_type.__class__

    if expr_type == expr_kind.CONSTANT:
        return expr._format_constant(expr.value)

    if expr_type == expr_kind.PARAMETER:
        return expr.name if expr.name else f"param_{expr.value}"

    if expr_type == expr_kind.VARIABLE:
        return expr.name if expr.name else "var"

    if expr_type == expr_kind.BINARY_OP:
        left = expr.operands[0]
        right = expr.operands[1]
        left_str = left._to_string_internal(simplify)
        right_str = right._to_string_internal(simplify)

        if expr.operator == "PIECE":
            return format_piece_expression(expr, left, right, simplify)

        if expr.operator == "SUBPIECE":
            return format_subpiece_expression(expr, left, right, simplify)

        op = expr._get_python_operator(expr.operator)
        return f"({left_str} {op} {right_str})"

    if expr_type == expr_kind.UNARY_OP:
        operand = expr.operands[0]._to_string_internal(simplify)
        op = expr._get_python_operator(expr.operator)
        if op == "not":
            return f"(not {operand})"
        if op in ("-", "~"):
            return f"({op}{operand})"
        return f"{op}({operand})"

    if expr_type == expr_kind.CALL:
        args = ", ".join(operand._to_string_internal(simplify) for operand in expr.operands)
        return f"{expr.name}({args})"

    if expr_type == expr_kind.INTRINSIC:
        args = ", ".join(operand._to_string_internal(simplify) for operand in expr.operands)
        return f"{expr.name}({args})"

    if expr_type == expr_kind.MEMORY:
        addr = expr.operands[0]._to_string_internal(simplify)
        return f"MEM[{addr}]"

    if expr_type == expr_kind.PHI:
        branches = expr.value
        if not branches:
            return "UNKNOWN"
        if len(branches) == 1:
            _, val = branches[0]
            if hasattr(val, "_to_string_internal"):
                return val._to_string_internal(simplify)
            return str(val)

        parts = []
        for cond, val in branches:
            if hasattr(val, "_to_string_internal"):
                val_str = val._to_string_internal(simplify)
            else:
                val_str = str(val)
            if cond is not None:
                if hasattr(cond, "_to_string_internal"):
                    cond_str = cond._to_string_internal(simplify)
                elif hasattr(cond, "to_string"):
                    cond_str = cond.to_string()
                else:
                    cond_str = str(cond)
                parts.append(f"{val_str} if {cond_str}")
            else:
                parts.append(val_str)
        return "PHI(" + ", ".join(parts) + ")"

    return expr.name if expr.name else "UNKNOWN"


def format_piece_expression(expr, high, low, simplify: bool) -> str:
    """PIECE を Python 互換形式に変換する。"""
    high_str = high._to_string_internal(simplify)
    low_str = low._to_string_internal(simplify)
    shift_bits = low.get_bit_width()

    if simplify:
        high_kind = high.expr_type.__class__
        low_kind = low.expr_type.__class__
        if high.expr_type == high_kind.CONSTANT and high.value == 0:
            return low_str
        if low.expr_type == low_kind.CONSTANT and low.value == 0:
            return f"({high_str} << {shift_bits})"

    return f"(({high_str} << {shift_bits}) | {low_str})"


def format_subpiece_expression(expr, source, offset, simplify: bool) -> str:
    """SUBPIECE を Python 互換形式に変換する。"""
    source_str = source._to_string_internal(simplify)

    offset_kind = offset.expr_type.__class__
    if offset.expr_type == offset_kind.CONSTANT:
        byte_offset = offset.value
    else:
        offset_str = offset._to_string_internal(simplify)
        output_bits = expr.get_bit_width()
        mask = (1 << output_bits) - 1
        mask_str = expr._format_constant(mask)
        return f"(({source_str} >> ({offset_str} * 8)) & {mask_str})"

    output_bits = expr.get_bit_width()
    mask = (1 << output_bits) - 1
    mask_str = expr._format_constant(mask)
    shift_bits = byte_offset * 8

    if simplify and shift_bits == 0:
        return f"({source_str} & {mask_str})"

    return f"(({source_str} >> {shift_bits}) & {mask_str})"


def get_python_operator(operator: Optional[str]) -> str:
    """P-code オペレータを Python 演算子へ変換する。"""
    if operator is None:
        return ""

    op_map: Dict[str, str] = {
        "INT_ADD": "+",
        "INT_SUB": "-",
        "INT_MULT": "*",
        "INT_DIV": "//",
        "INT_SDIV": "//",
        "INT_REM": "%",
        "INT_SREM": "%",
        "INT_AND": "&",
        "INT_OR": "|",
        "INT_XOR": "^",
        "INT_LEFT": "<<",
        "INT_RIGHT": ">>",
        "INT_SRIGHT": ">>",
        "INT_EQUAL": "==",
        "INT_NOTEQUAL": "!=",
        "INT_LESS": "<",
        "INT_SLESS": "<",
        "INT_LESSEQUAL": "<=",
        "INT_SLESSEQUAL": "<=",
        "BOOL_AND": "and",
        "BOOL_OR": "or",
        "BOOL_XOR": "^",
        "INT_NEGATE": "~",
        "INT_2COMP": "-",
        "BOOL_NEGATE": "not",
        "INT_ZEXT": "int",
        "INT_SEXT": "int",
        "COPY": "",
        "FLOAT_ADD": "+",
        "FLOAT_SUB": "-",
        "FLOAT_MULT": "*",
        "FLOAT_DIV": "/",
    }
    return op_map.get(operator, operator)
