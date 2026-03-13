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

_SIGNED_COMPARISON_OPERATORS = {
    "INT_SLESS",
    "INT_SLESSEQUAL",
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


def expression_contains_signed_comparison(expr) -> bool:
    """式木のどこかに signed 比較が含まれるか判定する。"""
    if expr is None:
        return False

    expr_type = expr.expr_type
    expr_kind = expr_type.__class__

    if expr_type == expr_kind.BINARY_OP and expr.operator in _SIGNED_COMPARISON_OPERATORS:
        return True

    if getattr(expr, "operands", None):
        for operand in expr.operands:
            if expression_contains_signed_comparison(operand):
                return True

    if expr_type == expr_kind.PHI and expr.value:
        for cond, branch_value in expr.value:
            if cond is not None:
                if hasattr(cond, "expression") and expression_contains_signed_comparison(cond.expression):
                    return True
                if hasattr(cond, "operands") and expression_contains_signed_comparison(cond):
                    return True
            if expression_contains_signed_comparison(branch_value):
                return True

    return False


def _coerce_bool_to_bitvec(expr, expr_smt: str, bits: int) -> str:
    """Bool sort の式を 0/1 の bitvector へ変換する。"""
    if bits <= 0 or not expression_returns_bool(expr):
        return expr_smt
    return f"(ite {expr_smt} (_ bv1 {bits}) (_ bv0 {bits}))"


def _rewrite_ambiguous_negative_constant(expr, expr_smt: str, target_bits: int, prefer_sign_extension: bool) -> str:
    """32bit 由来の負定数が 64bit で zero-extended された形なら sign-extended に補正する。"""
    if not prefer_sign_extension:
        return expr_smt
    if getattr(expr, "expr_type", None) is None:
        return expr_smt
    if expr.expr_type != expr.expr_type.__class__.CONSTANT:
        return expr_smt
    if target_bits <= 32:
        return expr_smt

    value = getattr(expr, "value", None)
    if not isinstance(value, int) or value < 0 or value > 0xffffffff:
        return expr_smt
    if (value & 0x80000000) == 0:
        return expr_smt

    sign_extended = value | (((1 << (target_bits - 32)) - 1) << 32)
    return f"(_ bv{sign_extended} {target_bits})"


def _coerce_expr_to_bitvec_width(
    expr,
    expr_smt: str,
    target_bits: int,
    prefer_sign_extension: bool = False,
) -> str:
    """式を target_bits 幅の bitvector に揃える。"""
    if target_bits <= 0:
        return expr_smt

    expr_smt = _coerce_bool_to_bitvec(expr, expr_smt, target_bits)
    if expression_returns_bool(expr):
        return expr_smt
    expr_smt = _rewrite_ambiguous_negative_constant(
        expr, expr_smt, target_bits, prefer_sign_extension
    )

    expr_bits = expr.get_bit_width() if hasattr(expr, "get_bit_width") else target_bits
    if expr_bits == target_bits:
        return expr_smt
    if expr_bits < target_bits:
        op = "sign_extend" if prefer_sign_extension else "zero_extend"
        return f"((_ {op} {target_bits - expr_bits}) {expr_smt})"
    return f"((_ extract {target_bits - 1} 0) {expr_smt})"


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

        phi_returns_bool = expression_returns_bool(expr)
        target_bits = expr.get_bit_width() if hasattr(expr, "get_bit_width") else 0
        prefer_sign_extension = expression_contains_signed_comparison(expr)

        def render_branch_value(branch_expr):
            if hasattr(branch_expr, "_to_smt_internal"):
                branch_smt = branch_expr._to_smt_internal()
            else:
                branch_smt = str(branch_expr)

            if phi_returns_bool or not hasattr(branch_expr, "get_bit_width"):
                return branch_smt

            return _coerce_expr_to_bitvec_width(
                branch_expr,
                branch_smt,
                target_bits,
                prefer_sign_extension=prefer_sign_extension,
            )

        last_val = branches[-1][1]
        result = render_branch_value(last_val)

        for index in range(len(branches) - 2, -1, -1):
            cond, val = branches[index]
            if cond is not None and hasattr(cond, "_to_smt_internal"):
                cond_str = cond._to_smt_internal()
            elif cond is not None and hasattr(cond, "to_smt"):
                cond_str = cond.to_smt()
            else:
                cond_str = "true"

            val_str = render_branch_value(val)

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
