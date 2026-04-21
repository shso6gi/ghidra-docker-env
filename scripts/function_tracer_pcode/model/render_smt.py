# -*- coding: utf-8 -*-
"""SMT-LIB rendering helpers for Expression."""

import hashlib
import re
from typing import Any, List, Mapping, Optional, Tuple

from .intrinsics import (
    PTRADD_OPCODE,
    PTRSUB_OPCODE,
    is_supported_pcode_intrinsic,
)
from .signature import get_declared_type_signedness
from .runtime_refs import AddressValueRef, CanonicalLocation, PostStateReadRef, PostStateValueRef


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

_MEMORY_ARRAY_WIDTHS = {8, 16, 32, 64}
_SMT_IDENTIFIER_RE = re.compile(r"^[A-Za-z_][A-Za-z0-9_]*$")
_ARITHMETIC_BINARY_OPERATORS = {
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
}

_SUPPORTED_BINARY_OPERATORS = (
    _ARITHMETIC_BINARY_OPERATORS
    | _BOOLEAN_BINARY_OPERATORS
    | {"PIECE", "SUBPIECE", "INT_LEFT", "INT_RIGHT", "INT_SRIGHT"}
)
_SUPPORTED_UNARY_OPERATORS = {
    "INT_ZEXT",
    "INT_SEXT",
    "INT_NEGATE",
    "INT_2COMP",
    "BOOL_NEGATE",
}


def expression_to_smt(
    expr,
    *,
    symbol_name_mapping: Optional[Mapping[str, str]] = None,
) -> str:
    """式を SMT-LIB 文字列へ変換する。"""
    return _to_smt_internal(expr, symbol_name_mapping=symbol_name_mapping)


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


def expression_smt_bit_width(expr) -> int:
    """式を SMT 化したときの bitvector 幅を推定する。"""
    if expr is None:
        return 0

    if expression_returns_bool(expr):
        return 1

    expr_type = expr.expr_type
    expr_kind = expr_type.__class__

    if expr_type in {expr_kind.CONSTANT, expr_kind.PARAMETER, expr_kind.VARIABLE, expr_kind.MEMORY}:
        return expr.get_bit_width() if hasattr(expr, "get_bit_width") else 0

    if expr_type == expr_kind.UNKNOWN:
        return expr.get_bit_width() if hasattr(expr, "get_bit_width") else 0

    if expr_type == expr_kind.INTRINSIC:
        explicit_bits = expr.get_bit_width() if hasattr(expr, "get_bit_width") else 0
        operand_bits = max(
            (expression_smt_bit_width(operand) for operand in getattr(expr, "operands", []) or []),
            default=0,
        )
        return max(explicit_bits, operand_bits)

    if expr_type == expr_kind.UNARY_OP:
        operand = expr.operands[0] if getattr(expr, "operands", None) else None
        operand_bits = expression_smt_bit_width(operand)
        if expr.operator in {"INT_ZEXT", "INT_SEXT"}:
            explicit_bits = (expr.size or 0) * 8
            return explicit_bits or operand_bits
        if expr.operator == "BOOL_NEGATE":
            return 1
        return operand_bits

    if expr_type == expr_kind.BINARY_OP:
        left = expr.operands[0] if len(getattr(expr, "operands", [])) >= 1 else None
        right = expr.operands[1] if len(getattr(expr, "operands", [])) >= 2 else None
        left_bits = expression_smt_bit_width(left)
        right_bits = expression_smt_bit_width(right)

        if expr.operator == "PIECE":
            return left_bits + right_bits
        if expr.operator == "SUBPIECE":
            explicit_bits = (expr.size or 0) * 8
            return explicit_bits or max(left_bits, right_bits)
        if expr.operator in {"INT_LEFT", "INT_RIGHT", "INT_SRIGHT"}:
            return left_bits
        if expr.operator in _BOOLEAN_BINARY_OPERATORS:
            return 1
        if expr.operator in _ARITHMETIC_BINARY_OPERATORS:
            return _preferred_arithmetic_width(left, right, left_bits, right_bits)
        return max(left_bits, right_bits)

    if expr_type == expr_kind.PHI:
        branches = expr.value or []
        explicit_bits = expr.get_bit_width() if hasattr(expr, "get_bit_width") else 0
        branch_bits = max(
            (expression_smt_bit_width(branch_value) for _, branch_value in branches),
            default=0,
        )
        return max(explicit_bits, branch_bits)

    return expr.get_bit_width() if hasattr(expr, "get_bit_width") else 0


def normalize_call_symbol_name(name: Optional[str]) -> str:
    """CALL 名を SMT-LIB で安全な識別子に変換する。"""
    raw_name = str(name or "call")
    if _SMT_IDENTIFIER_RE.fullmatch(raw_name):
        return f"call_{raw_name}"
    digest = hashlib.sha1(raw_name.encode("utf-8")).hexdigest()[:16]
    return f"call_{digest}_{len(raw_name)}"


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


def expression_contains_unsupported_smt_ops(expr, *, allow_call: bool = False) -> bool:
    """SMT renderer が直接扱えない演算子を含むか判定する。"""
    if expr is None:
        return False

    expr_type = expr.expr_type
    expr_kind = expr_type.__class__

    if expr_type == expr_kind.CALL and not allow_call:
        return True

    if expr_type == expr_kind.BINARY_OP and expr.operator not in _SUPPORTED_BINARY_OPERATORS:
        return True

    if expr_type == expr_kind.UNARY_OP and expr.operator not in _SUPPORTED_UNARY_OPERATORS:
        return True

    if expr_type == expr_kind.INTRINSIC and not is_supported_pcode_intrinsic(
        opcode=getattr(expr, "opcode", None),
        mnemonic=getattr(expr, "name", None),
    ):
        return True

    if getattr(expr, "operands", None):
        for operand in expr.operands:
            if expression_contains_unsupported_smt_ops(operand, allow_call=allow_call):
                return True

    if expr_type == expr_kind.PHI and expr.value:
        for cond, branch_value in expr.value:
            if cond is not None and expression_contains_unsupported_smt_ops(
                cond.expression,
                allow_call=allow_call,
            ):
                return True
            if expression_contains_unsupported_smt_ops(branch_value, allow_call=allow_call):
                return True

    return False


def collect_unknown_smt_declarations(expr) -> List[Tuple[str, int]]:
    """Collect deterministic SMT declarations needed for UNKNOWN runtime objects."""
    declarations: List[Tuple[str, int]] = []
    seen = set()
    for node in _iter_expression_nodes(expr):
        if node is None or getattr(node, "expr_type", None) is None:
            continue
        expr_kind = node.expr_type.__class__
        runtime_ref = getattr(node, "runtime_ref", None)
        decl = None
        if node.expr_type == expr_kind.UNKNOWN:
            decl = _unknown_smt_declaration(node)
        elif (
            node.expr_type == expr_kind.VARIABLE
            and isinstance(runtime_ref, (CanonicalLocation, PostStateReadRef, PostStateValueRef))
        ):
            decl = (
                node.to_smt(),
                max(1, int(expression_smt_bit_width(node) or 1)),
            )
        if decl is None:
            continue
        if decl in seen:
            continue
        seen.add(decl)
        declarations.append(decl)
    return declarations


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

    expr_bits = expression_smt_bit_width(expr) or target_bits
    if expr_bits == target_bits:
        return expr_smt
    if expr_bits < target_bits:
        op = "sign_extend" if prefer_sign_extension else "zero_extend"
        return f"((_ {op} {target_bits - expr_bits}) {expr_smt})"
    if expr is not None and getattr(expr, "expr_type", None) == expr.expr_type.__class__.CONSTANT:
        value = getattr(expr, "value", 0)
        if isinstance(value, int) and target_bits > 0:
            value = value & ((1 << target_bits) - 1)
            return f"(_ bv{value} {target_bits})"
    return f"((_ extract {target_bits - 1} 0) {expr_smt})"


def _constant_fits_width(expr, target_bits: int) -> bool:
    if expr is None or getattr(expr, "expr_type", None) is None:
        return False
    if expr.expr_type != expr.expr_type.__class__.CONSTANT:
        return False
    if target_bits <= 0:
        return False

    value = getattr(expr, "value", None)
    if not isinstance(value, int):
        return False
    mask = (1 << target_bits) - 1
    return (value & ~mask) == 0 or value < 0


def _preferred_arithmetic_width(left, right, left_bits: int, right_bits: int) -> int:
    if left_bits == right_bits:
        return left_bits
    if (
        left_bits > right_bits
        and _constant_fits_width(left, right_bits)
        and not expression_returns_bool(right)
    ):
        return right_bits
    if (
        right_bits > left_bits
        and _constant_fits_width(right, left_bits)
        and not expression_returns_bool(left)
    ):
        return left_bits
    return max(left_bits, right_bits)


def _expr_prefers_signed_extension(expr) -> bool:
    """式を widening するとき sign-extend を優先すべきか判定する。"""
    if expr is None:
        return False

    expr_type = expr.expr_type
    expr_kind = expr_type.__class__

    if expr_type in {expr_kind.PARAMETER, expr_kind.VARIABLE}:
        data_type_obj = getattr(expr, "data_type_obj", None)
        if data_type_obj is not None:
            return bool(
                get_declared_type_signedness(
                    data_type_obj,
                    fallback_name=None,
                    fallback_signed=False,
                )
            )
        return False

    if expr_type == expr_kind.CONSTANT:
        value = getattr(expr, "value", None)
        return isinstance(value, int) and value < 0

    if expr_type == expr_kind.UNARY_OP:
        if expr.operator == "INT_SEXT":
            return True
        if expr.operator == "INT_ZEXT":
            return False
        operands = getattr(expr, "operands", None) or []
        return any(_expr_prefers_signed_extension(operand) for operand in operands)

    if expr_type == expr_kind.BINARY_OP:
        if expr.operator in {"INT_SDIV", "INT_SREM", "INT_SRIGHT"}:
            return True
        operands = getattr(expr, "operands", None) or []
        return any(_expr_prefers_signed_extension(operand) for operand in operands)

    if expr_type == expr_kind.PHI:
        branches = getattr(expr, "value", None) or []
        return any(_expr_prefers_signed_extension(branch_value) for _, branch_value in branches)

    operands = getattr(expr, "operands", None) or []
    return any(_expr_prefers_signed_extension(operand) for operand in operands)


def _iter_expression_nodes(expr) -> List[Any]:
    if expr is None:
        return []

    nodes: List[Any] = []
    pending: List[Any] = [expr]
    while pending:
        current = pending.pop()
        if current is None:
            continue
        nodes.append(current)

        expr_type = getattr(current, "expr_type", None)
        expr_kind = getattr(expr_type, "__class__", None)
        if expr_type is not None and expr_kind is not None and expr_type == expr_kind.PHI and current.value:
            for cond, value in reversed(current.value):
                if value is not None:
                    pending.append(value)
                cond_expr = getattr(cond, "expression", None) if cond is not None else None
                if cond_expr is not None:
                    pending.append(cond_expr)
            continue

        operands = getattr(current, "operands", None) or []
        pending.extend(reversed([operand for operand in operands if operand is not None]))

    return nodes


def _unknown_runtime_identity_key(expr) -> Tuple[Any, ...]:
    runtime_ref = getattr(expr, "runtime_ref", None)
    stable_key = getattr(runtime_ref, "stable_key", None)
    if callable(stable_key):
        try:
            identity = stable_key()
        except Exception:
            identity = None
        if identity is not None:
            return ("runtime_ref", identity)
    return (
        "expression_unknown",
        getattr(expr, "name", None),
        int(expression_smt_bit_width(expr) or 1),
    )


def _unknown_smt_symbol_name(expr) -> str:
    identity = _unknown_runtime_identity_key(expr)
    bits = max(1, int(expression_smt_bit_width(expr) or 1))
    digest = hashlib.sha1(repr(identity).encode("utf-8")).hexdigest()[:16]
    return f"rtunk_{digest}_{bits}"


def _unknown_smt_declaration(expr) -> Tuple[str, int]:
    bits = max(1, int(expression_smt_bit_width(expr) or 1))
    return (_unknown_smt_symbol_name(expr), bits)


def _to_smt_internal(
    expr,
    prefer_signed_arithmetic: bool = False,
    symbol_name_mapping: Optional[Mapping[str, str]] = None,
    address_context: bool = False,
) -> str:
    expr_type = expr.expr_type
    expr_kind = expr_type.__class__

    if expr_type == expr_kind.CONSTANT:
        bits = expr.get_bit_width()
        value = expr.value
        if value < 0:
            value = value & ((1 << bits) - 1)
        return f"(_ bv{value} {bits})"

    if expr_type == expr_kind.PARAMETER:
        name = expr.name if expr.name else f"param_{expr.value}"
        if symbol_name_mapping is None:
            return name
        return symbol_name_mapping.get(name, name)

    if expr_type == expr_kind.VARIABLE:
        if address_context:
            address_ref = _coerce_address_value_ref(expr)
            if address_ref is not None:
                bits = max(1, expression_smt_bit_width(expr))
                return f"(_ bv{int(address_ref.address_offset)} {bits})"
        name = expr.name if expr.name else "var"
        if symbol_name_mapping is None:
            return name
        return symbol_name_mapping.get(name, name)

    if expr_type == expr_kind.UNKNOWN:
        return _unknown_smt_symbol_name(expr)

    if expr_type == expr_kind.INTRINSIC:
        return _lower_intrinsic_to_smt(
            expr,
            prefer_signed_arithmetic=prefer_signed_arithmetic,
            symbol_name_mapping=symbol_name_mapping,
            address_context=address_context,
        )

    if expr_type == expr_kind.BINARY_OP:
        left = expr.operands[0]
        right = expr.operands[1]

        if expr.operator == "PIECE":
            return (
                f"(concat "
                f"{_to_smt_internal(left, prefer_signed_arithmetic, symbol_name_mapping, address_context)} "
                f"{_to_smt_internal(right, prefer_signed_arithmetic, symbol_name_mapping, address_context)})"
            )

        if expr.operator == "SUBPIECE":
            source_smt = _to_smt_internal(
                left,
                prefer_signed_arithmetic,
                symbol_name_mapping,
                address_context,
            )
            right_kind = right.expr_type.__class__
            if right.expr_type == right_kind.CONSTANT:
                byte_offset = right.value
                output_size = expr.size if expr.size else 4
                high_bit = (byte_offset + output_size) * 8 - 1
                low_bit = byte_offset * 8
                return f"((_ extract {high_bit} {low_bit}) {source_smt})"
            return (
                f"(subpiece {source_smt} "
                f"{_to_smt_internal(right, prefer_signed_arithmetic, symbol_name_mapping, address_context)})"
            )

        left_bits = expression_smt_bit_width(left)
        right_bits = expression_smt_bit_width(right)
        left_smt = _to_smt_internal(left, prefer_signed_arithmetic, symbol_name_mapping, address_context)
        right_smt = _to_smt_internal(right, prefer_signed_arithmetic, symbol_name_mapping, address_context)

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

        if expr.operator in _ARITHMETIC_BINARY_OPERATORS:
            left_smt = _coerce_bool_to_bitvec(left, left_smt, left_bits)
            right_smt = _coerce_bool_to_bitvec(right, right_smt, right_bits)
            if left_bits != right_bits:
                target_bits = _preferred_arithmetic_width(left, right, left_bits, right_bits)
                if left_bits < target_bits:
                    left_extend = (
                        "sign_extend"
                        if prefer_signed_arithmetic and _expr_prefers_signed_extension(left)
                        else "zero_extend"
                    )
                    left_smt = f"((_ {left_extend} {target_bits - left_bits}) {left_smt})"
                elif left_bits > target_bits:
                    left_smt = _coerce_expr_to_bitvec_width(
                        left,
                        left_smt,
                        target_bits,
                        prefer_sign_extension=False,
                    )
                if right_bits < target_bits:
                    right_extend = (
                        "sign_extend"
                        if prefer_signed_arithmetic and _expr_prefers_signed_extension(right)
                        else "zero_extend"
                    )
                    right_smt = f"((_ {right_extend} {target_bits - right_bits}) {right_smt})"
                elif right_bits > target_bits:
                    right_smt = _coerce_expr_to_bitvec_width(
                        right,
                        right_smt,
                        target_bits,
                        prefer_sign_extension=False,
                    )
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
            prefer_sign_extension = expr.operator in _SIGNED_COMPARISON_OPERATORS
            left_is_bool = expression_returns_bool(left)
            right_is_bool = expression_returns_bool(right)
            left_smt = _to_smt_internal(left, False, symbol_name_mapping, address_context)
            right_smt = _to_smt_internal(right, False, symbol_name_mapping, address_context)

            # Bool sort を含む比較は、そのまま zero/sign-extend すると
            # SMT 上で sort error になる。bitvector 比較が必要な場合のみ
            # 0/1 へ変換してから幅を揃える。
            if left_is_bool or right_is_bool:
                should_compare_as_bool = (
                    left_is_bool
                    and right_is_bool
                    and expr.operator in {"INT_EQUAL", "INT_NOTEQUAL"}
                )
                if not should_compare_as_bool:
                    target_bits = max(left_bits, right_bits, 1)
                    left_smt = _coerce_expr_to_bitvec_width(
                        left,
                        left_smt,
                        target_bits,
                        prefer_sign_extension=prefer_sign_extension,
                    )
                    right_smt = _coerce_expr_to_bitvec_width(
                        right,
                        right_smt,
                        target_bits,
                        prefer_sign_extension=prefer_sign_extension,
                    )
            elif left_bits != right_bits:
                target_bits = max(left_bits, right_bits)
                if left_bits < target_bits:
                    op = "sign_extend" if prefer_sign_extension else "zero_extend"
                    left_smt = f"((_ {op} {target_bits - left_bits}) {left_smt})"
                if right_bits < target_bits:
                    op = "sign_extend" if prefer_sign_extension else "zero_extend"
                    right_smt = f"((_ {op} {target_bits - right_bits}) {right_smt})"
            op = expr._get_smt_operator(expr.operator)
            return f"({op} {left_smt} {right_smt})"

        op = expr._get_smt_operator(expr.operator)
        return f"({op} {left_smt} {right_smt})"

    if expr_type == expr_kind.UNARY_OP:
        operand = expr.operands[0]
        operand_smt = _to_smt_internal(
            operand,
            prefer_signed_arithmetic,
            symbol_name_mapping,
            address_context,
        )
        operand_bits = expression_smt_bit_width(operand)

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
        args = " ".join(
            _to_smt_internal(
                operand,
                prefer_signed_arithmetic,
                symbol_name_mapping,
                address_context,
            )
            for operand in expr.operands
        )
        raw_func_name = getattr(expr, "name", None)
        func_name = normalize_call_symbol_name(raw_func_name)
        if symbol_name_mapping is not None:
            func_name = (
                symbol_name_mapping.get(raw_func_name, func_name)
                if raw_func_name is not None
                else func_name
            )
            func_name = symbol_name_mapping.get(func_name, func_name)
        if args:
            return f"({func_name} {args})"
        return f"{func_name}"

    if expr_type == expr_kind.MEMORY:
        mem_bits = expression_smt_bit_width(expr) or 32
        if mem_bits not in _MEMORY_ARRAY_WIDTHS:
            mem_bits = 32
        addr_expr = expr.operands[0]
        addr_smt = _to_smt_internal(
            addr_expr,
            prefer_signed_arithmetic,
            symbol_name_mapping,
            True,
        )
        addr_smt = _coerce_expr_to_bitvec_width(
            addr_expr,
            addr_smt,
            64,
            prefer_sign_extension=False,
        )
        return f"(select mem{mem_bits} {addr_smt})"

    if expr_type == expr_kind.PHI:
        branches = expr.value
        if not branches:
            return "undefined"

        phi_returns_bool = expression_returns_bool(expr)
        target_bits = expression_smt_bit_width(expr)
        prefer_sign_extension = expression_contains_signed_comparison(expr)

        def render_branch_value(branch_expr):
            if hasattr(branch_expr, "_to_smt_internal"):
                branch_smt = _to_smt_internal(
                    branch_expr,
                    prefer_sign_extension,
                    symbol_name_mapping,
                    address_context,
                )
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
                cond_str = _to_smt_internal(
                    cond,
                    prefer_sign_extension,
                    symbol_name_mapping,
                    address_context,
                )
            elif cond is not None and hasattr(cond, "to_smt"):
                cond_str = cond.to_smt(symbol_name_mapping=symbol_name_mapping)
            else:
                cond_str = "true"

            val_str = render_branch_value(val)

            result = f"(ite {cond_str} {val_str} {result})"

        return result

    return "unknown"


def _intrinsic_result_bits(expr) -> int:
    explicit_bits = expression_smt_bit_width(expr)
    if explicit_bits > 0:
        return explicit_bits
    operands = getattr(expr, "operands", None) or []
    if operands:
        return max(expression_smt_bit_width(operand) for operand in operands)
    return 0


def _lower_intrinsic_to_smt(
    expr,
    *,
    prefer_signed_arithmetic: bool,
    symbol_name_mapping: Optional[Mapping[str, str]],
    address_context: bool,
) -> str:
    opcode = getattr(expr, "opcode", None)
    mnemonic = getattr(expr, "name", None) or ""
    operands = getattr(expr, "operands", None) or []
    result_bits = _intrinsic_result_bits(expr)

    if opcode == PTRADD_OPCODE or mnemonic == "PTRADD":
        if len(operands) != 3:
            raise ValueError(f"PTRADD expects 3 operands, got {len(operands)}")
        base, index, element_size = operands
        base_smt = _to_smt_internal(
            base,
            prefer_signed_arithmetic,
            symbol_name_mapping,
            True,
        )
        index_smt = _to_smt_internal(
            index,
            prefer_signed_arithmetic,
            symbol_name_mapping,
            address_context,
        )
        elem_smt = _to_smt_internal(
            element_size,
            prefer_signed_arithmetic,
            symbol_name_mapping,
            address_context,
        )
        target_bits = max(
            result_bits,
            expression_smt_bit_width(base),
            expression_smt_bit_width(index),
            expression_smt_bit_width(element_size),
            1,
        )
        base_smt = _coerce_expr_to_bitvec_width(base, base_smt, target_bits)
        index_smt = _coerce_expr_to_bitvec_width(index, index_smt, target_bits)
        elem_smt = _coerce_expr_to_bitvec_width(element_size, elem_smt, target_bits)
        return f"(bvadd {base_smt} (bvmul {index_smt} {elem_smt}))"

    if opcode == PTRSUB_OPCODE or mnemonic == "PTRSUB":
        if len(operands) != 2:
            raise ValueError(f"PTRSUB expects 2 operands, got {len(operands)}")
        base, offset = operands
        base_smt = _to_smt_internal(
            base,
            prefer_signed_arithmetic,
            symbol_name_mapping,
            True,
        )
        offset_smt = _to_smt_internal(
            offset,
            prefer_signed_arithmetic,
            symbol_name_mapping,
            address_context,
        )
        target_bits = max(
            result_bits,
            expression_smt_bit_width(base),
            expression_smt_bit_width(offset),
            1,
        )
        base_smt = _coerce_expr_to_bitvec_width(base, base_smt, target_bits)
        offset_smt = _coerce_expr_to_bitvec_width(offset, offset_smt, target_bits)
        return f"(bvadd {base_smt} {offset_smt})"

    raise ValueError(
        f"Unsupported intrinsic for SMT lowering: {mnemonic or opcode}"
    )

def _coerce_address_value_ref(expr) -> Optional[AddressValueRef]:
    runtime_ref = getattr(expr, "runtime_ref", None)
    if isinstance(runtime_ref, AddressValueRef):
        return runtime_ref
    return None


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
