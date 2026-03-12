# -*- coding: utf-8 -*-
"""SMT-LIB rendering helpers for Expression."""

from typing import Optional


_BOOLEAN_BINARY_OPERATORS = {
    "INT_EQUAL",
    "INT_NOTEQUAL",
    "INT_LESS",
    "INT_SLESS",
    "INT_LESSEQUAL",
    "INT_SLESSEQUAL",
    "FLOAT_EQUAL",
    "FLOAT_NOTEQUAL",
    "FLOAT_LESS",
    "FLOAT_LESSEQUAL",
    "BOOL_AND",
    "BOOL_OR",
    "BOOL_XOR",
}


def expression_to_smt(expr) -> str:
    """式を SMT-LIB 文字列へ変換する。"""
    return _to_smt_internal(expr)


def expression_returns_bool(expr) -> bool:
    """式が SMT 上で Bool sort を返すか判定する。"""
    if expr is None:
        return False

    expr_type = expr.expr_type
    expr_kind = expr_type.__class__

    if expr_type == expr_kind.BINARY_OP:
        return expr.operator in _BOOLEAN_BINARY_OPERATORS

    if expr_type == expr_kind.UNARY_OP:
        return expr.operator == "BOOL_NEGATE"

    if expr_type == expr_kind.PHI:
        branches = expr.value or []
        return bool(branches) and all(
            expression_returns_bool(branch_value) for _, branch_value in branches
        )

    return False


def _coerce_bool_to_bitvec(expr, expr_smt: str, bits: int) -> str:
    """Bool sort の式を 0/1 の bitvector へ変換する。"""
    if bits <= 0 or not expression_returns_bool(expr):
        return expr_smt
    return f"(ite {expr_smt} (_ bv1 {bits}) (_ bv0 {bits}))"


def _to_smt_internal(expr) -> str:
    expr_type = expr.expr_type
    expr_kind = expr_type.__class__

    if expr_type == expr_kind.CONSTANT:
        bits = expr.get_bit_width()
        value = expr.value
        if value < 0:
            value = value & ((1 << bits) - 1)
        return f"(_ bv{value} {bits})"

    if expr_type == expr_kind.PARAMETER:
        return expr.name if expr.name else f"param_{expr.value}"

    if expr_type == expr_kind.VARIABLE:
        return expr.name if expr.name else "var"

    if expr_type == expr_kind.BINARY_OP:
        left = expr.operands[0]
        right = expr.operands[1]

        if expr.operator == "PIECE":
            return f"(concat {left._to_smt_internal()} {right._to_smt_internal()})"

        if expr.operator == "SUBPIECE":
            source_smt = left._to_smt_internal()
            right_kind = right.expr_type.__class__
            if right.expr_type == right_kind.CONSTANT:
                byte_offset = right.value
                output_size = expr.size if expr.size else 4
                high_bit = (byte_offset + output_size) * 8 - 1
                low_bit = byte_offset * 8
                return f"((_ extract {high_bit} {low_bit}) {source_smt})"
            return f"(subpiece {source_smt} {right._to_smt_internal()})"

        left_bits = left.get_bit_width()
        right_bits = right.get_bit_width()
        left_smt = left._to_smt_internal()
        right_smt = right._to_smt_internal()

        if expr.operator in ["INT_LEFT", "INT_RIGHT", "INT_SRIGHT"]:
            left_smt = _coerce_bool_to_bitvec(left, left_smt, left_bits)
            right_smt = _coerce_bool_to_bitvec(right, right_smt, right_bits)
            result_bits = left_bits
            if right_bits != result_bits:
                if right_bits > result_bits:
                    right_smt = f"((_ extract {result_bits - 1} 0) {right_smt})"
                else:
                    right_smt = f"((_ zero_extend {result_bits - right_bits}) {right_smt})"
            op = expr._get_smt_operator(expr.operator)
            return f"({op} {left_smt} {right_smt})"

        if expr.operator in [
            "INT_AND",
            "INT_OR",
            "INT_XOR",
            "INT_ADD",
            "INT_SUB",
            "INT_MULT",
            "INT_DIV",
            "INT_SDIV",
            "INT_REM",
            "INT_SREM",
        ]:
            left_smt = _coerce_bool_to_bitvec(left, left_smt, left_bits)
            right_smt = _coerce_bool_to_bitvec(right, right_smt, right_bits)
            if left_bits != right_bits:
                target_bits = max(left_bits, right_bits)
                if left_bits < target_bits:
                    left_smt = f"((_ zero_extend {target_bits - left_bits}) {left_smt})"
                if right_bits < target_bits:
                    right_smt = f"((_ zero_extend {target_bits - right_bits}) {right_smt})"
            op = expr._get_smt_operator(expr.operator)
            return f"({op} {left_smt} {right_smt})"

        if expr.operator in [
            "INT_EQUAL",
            "INT_NOTEQUAL",
            "INT_LESS",
            "INT_SLESS",
            "INT_LESSEQUAL",
            "INT_SLESSEQUAL",
        ]:
            if left_bits != right_bits:
                target_bits = max(left_bits, right_bits)
                if left_bits < target_bits:
                    left_smt = f"((_ zero_extend {target_bits - left_bits}) {left_smt})"
                if right_bits < target_bits:
                    right_smt = f"((_ zero_extend {target_bits - right_bits}) {right_smt})"
            op = expr._get_smt_operator(expr.operator)
            return f"({op} {left_smt} {right_smt})"

        op = expr._get_smt_operator(expr.operator)
        return f"({op} {left_smt} {right_smt})"

    if expr_type == expr_kind.UNARY_OP:
        operand = expr.operands[0]
        operand_smt = operand._to_smt_internal()
        operand_bits = operand.get_bit_width()

        if expr.operator == "INT_ZEXT":
            output_bits = (expr.size if expr.size else 8) * 8
            if expression_returns_bool(operand):
                return _coerce_bool_to_bitvec(operand, operand_smt, output_bits)
            extend_bits = output_bits - operand_bits
            if extend_bits > 0:
                return f"((_ zero_extend {extend_bits}) {operand_smt})"
            if extend_bits == 0:
                return operand_smt
            return f"((_ extract {output_bits - 1} 0) {operand_smt})"

        if expr.operator == "INT_SEXT":
            output_bits = (expr.size if expr.size else 8) * 8
            if expression_returns_bool(operand):
                return _coerce_bool_to_bitvec(operand, operand_smt, output_bits)
            extend_bits = output_bits - operand_bits
            if extend_bits > 0:
                return f"((_ sign_extend {extend_bits}) {operand_smt})"
            if extend_bits == 0:
                return operand_smt
            return f"((_ extract {output_bits - 1} 0) {operand_smt})"

        if expr.operator == "INT_NEGATE":
            return f"(bvnot {operand_smt})"

        if expr.operator == "INT_2COMP":
            return f"(bvneg {operand_smt})"

        if expr.operator == "BOOL_NEGATE":
            return f"(not {operand_smt})"

        op = expr._get_smt_operator(expr.operator)
        return f"({op} {operand_smt})"

    if expr_type == expr_kind.CALL:
        args = " ".join(operand._to_smt_internal() for operand in expr.operands)
        if args:
            return f"({expr.name} {args})"
        return f"{expr.name}"

    if expr_type == expr_kind.MEMORY:
        return f"(select mem {expr.operands[0]._to_smt_internal()})"

    if expr_type == expr_kind.PHI:
        branches = expr.value
        if not branches:
            return "undefined"

        last_val = branches[-1][1]
        if hasattr(last_val, "_to_smt_internal"):
            result = last_val._to_smt_internal()
        else:
            result = str(last_val)

        for index in range(len(branches) - 2, -1, -1):
            cond, val = branches[index]
            if cond is not None and hasattr(cond, "_to_smt_internal"):
                cond_str = cond._to_smt_internal()
            elif cond is not None and hasattr(cond, "to_smt"):
                cond_str = cond.to_smt()
            else:
                cond_str = "true"

            if hasattr(val, "_to_smt_internal"):
                val_str = val._to_smt_internal()
            else:
                val_str = str(val)

            result = f"(ite {cond_str} {val_str} {result})"

        return result

    return "unknown"


def get_smt_operator(operator: Optional[str] = None) -> str:
    """P-code オペレータを SMT-LIB 演算子へ変換する。"""
    if operator is None:
        return "unknown"

    op_map = {
        "INT_ADD": "bvadd",
        "INT_SUB": "bvsub",
        "INT_MULT": "bvmul",
        "INT_DIV": "bvudiv",
        "INT_SDIV": "bvsdiv",
        "INT_REM": "bvurem",
        "INT_SREM": "bvsrem",
        "INT_AND": "bvand",
        "INT_OR": "bvor",
        "INT_XOR": "bvxor",
        "INT_LEFT": "bvshl",
        "INT_RIGHT": "bvlshr",
        "INT_SRIGHT": "bvashr",
        "INT_EQUAL": "=",
        "INT_NOTEQUAL": "distinct",
        "INT_LESS": "bvult",
        "INT_SLESS": "bvslt",
        "INT_LESSEQUAL": "bvule",
        "INT_SLESSEQUAL": "bvsle",
        "INT_NEGATE": "bvnot",
        "INT_2COMP": "bvneg",
        "BOOL_NEGATE": "not",
        "BOOL_AND": "and",
        "BOOL_OR": "or",
        "BOOL_XOR": "xor",
    }
    return op_map.get(operator, operator.lower())
