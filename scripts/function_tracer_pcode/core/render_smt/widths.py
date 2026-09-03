"""Bit-width inference and coercion, PIECE/SUBPIECE contracts and signed-extension preference."""

from __future__ import annotations

from typing import List, Optional, Tuple
from scripts.function_tracer_pcode.core.intrinsics import (
    COUNTED_LOOP_SUM_OPCODE,
    COUNTED_STATE_TRANSITION_VALUE_OPCODE,
    READONLY_SUM_OPCODE,
)
from scripts.function_tracer_pcode.core.signature import get_declared_type_signedness


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
        opcode = getattr(expr, "opcode", None)
        mnemonic = getattr(expr, "name", None) or ""
        operand_bits = max(
            (expression_smt_bit_width(operand) for operand in getattr(expr, "operands", []) or []),
            default=0,
        )
        if opcode == READONLY_SUM_OPCODE or mnemonic == "READONLY_SUM":
            return explicit_bits or operand_bits
        if opcode == COUNTED_LOOP_SUM_OPCODE or mnemonic == "COUNTED_LOOP_SUM":
            return explicit_bits or operand_bits
        if opcode == COUNTED_STATE_TRANSITION_VALUE_OPCODE or mnemonic == "COUNTED_STATE_TRANSITION_VALUE":
            return explicit_bits or operand_bits
        return max(explicit_bits, operand_bits)

    if expr_type == expr_kind.UNARY_OP:
        operand = expr.operands[0] if getattr(expr, "operands", None) else None
        operand_bits = expression_smt_bit_width(operand)
        if expr.operator in {"INT2FLOAT", "INT_ZEXT", "INT_SEXT"}:
            explicit_bits = (expr.size or 0) * 8
            return explicit_bits
        if expr.operator == "BOOL_NEGATE":
            return 1
        explicit_bits = expr.get_bit_width() if hasattr(expr, "get_bit_width") else 0
        return explicit_bits or operand_bits

    if expr_type == expr_kind.BINARY_OP:
        left = expr.operands[0] if len(getattr(expr, "operands", [])) >= 1 else None
        right = expr.operands[1] if len(getattr(expr, "operands", [])) >= 2 else None
        left_bits = expression_smt_bit_width(left)
        right_bits = expression_smt_bit_width(right)

        if expr.operator == "PIECE":
            explicit_bits = expr.get_bit_width() if hasattr(expr, "get_bit_width") else 0
            return explicit_bits or (left_bits + right_bits)
        if expr.operator == "SUBPIECE":
            explicit_bits = (expr.size or 0) * 8
            return explicit_bits or max(left_bits, right_bits)
        if expr.operator in {"INT_LEFT", "INT_RIGHT", "INT_SRIGHT"}:
            explicit_bits = expr.get_bit_width() if hasattr(expr, "get_bit_width") else 0
            return explicit_bits or left_bits
        if expr.operator in _BOOLEAN_BINARY_OPERATORS:
            return 1
        if expr.operator in _ARITHMETIC_BINARY_OPERATORS:
            if expr.operator in _BITWISE_BINARY_OPERATORS:
                explicit_bits = expr.get_bit_width() if hasattr(expr, "get_bit_width") else 0
                if explicit_bits > 0:
                    return explicit_bits
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


def _coerce_smt_bitvec_width(
    expr_smt: str,
    source_bits: int,
    target_bits: int,
    *,
    prefer_sign_extension: bool = False,
) -> str:
    if source_bits <= 0 or target_bits <= 0 or source_bits == target_bits:
        return expr_smt
    if source_bits < target_bits:
        op = "sign_extend" if prefer_sign_extension else "zero_extend"
        return f"((_ {op} {target_bits - source_bits}) {expr_smt})"
    return f"((_ extract {target_bits - 1} 0) {expr_smt})"


def _expr_constant_int(expr) -> Optional[int]:
    expr_type = getattr(expr, "expr_type", None)
    if expr_type is None:
        return None
    expr_kind = expr_type.__class__
    if expr_type != expr_kind.CONSTANT:
        return None
    try:
        return int(getattr(expr, "value", 0) or 0)
    except Exception:
        return None


def _safe_size_bytes(expr) -> Optional[int]:
    """Return an expression size in bytes, or ``None`` for malformed metadata."""

    raw_size = getattr(expr, "size", 0)
    if raw_size is None:
        return 0
    if isinstance(raw_size, bool):
        return None
    try:
        size_bytes = int(raw_size)
    except (TypeError, ValueError, OverflowError):
        return None
    if isinstance(raw_size, float) and raw_size != size_bytes:
        return None
    return size_bytes


def _smt_width_if_known(expr) -> int:
    """Return an explicit/derivable width without using model fallbacks."""

    if expr is None:
        return 0
    if expression_returns_bool(expr):
        return 1
    size_bytes = _safe_size_bytes(expr)
    explicit_bits = size_bytes * 8 if size_bytes is not None and size_bytes > 0 else 0
    if explicit_bits > 0:
        return explicit_bits

    expr_type = getattr(expr, "expr_type", None)
    expr_kind = getattr(expr_type, "__class__", None)
    if expr_kind is None:
        return 0
    if expr_type in {
        expr_kind.CONSTANT,
        expr_kind.PARAMETER,
        expr_kind.VARIABLE,
        expr_kind.MEMORY,
        expr_kind.UNKNOWN,
    }:
        return 0
    operands = getattr(expr, "operands", None) or ()
    if expr_type == expr_kind.UNARY_OP:
        if getattr(expr, "operator", None) in {"INT2FLOAT", "INT_ZEXT", "INT_SEXT"}:
            return 0
        return _smt_width_if_known(operands[0]) if len(operands) == 1 else 0
    if expr_type == expr_kind.BINARY_OP:
        operator = getattr(expr, "operator", None)
        if operator == "PIECE" and len(operands) == 2:
            left_bits = _smt_width_if_known(operands[0])
            right_bits = _smt_width_if_known(operands[1])
            return left_bits + right_bits if left_bits > 0 and right_bits > 0 else 0
        if operator == "SUBPIECE":
            return 0
        if operator in _BOOLEAN_BINARY_OPERATORS:
            return 1
        if len(operands) == 2:
            left_bits = _smt_width_if_known(operands[0])
            right_bits = _smt_width_if_known(operands[1])
            if left_bits > 0 and right_bits > 0:
                return max(left_bits, right_bits)
        return 0
    if expr_type == expr_kind.PHI:
        branches = getattr(expr, "value", None) or ()
        branch_widths = tuple(
            _smt_width_if_known(branch_value)
            for _condition, branch_value in branches
        )
        if not branch_widths or any(width <= 0 for width in branch_widths):
            return 0
        return branch_widths[0] if len(set(branch_widths)) == 1 else 0
    return 0


def _piece_subpiece_contract(
    expr,
) -> Tuple[Optional[str], int, int, int, Optional[int]]:
    """Validate a PIECE/SUBPIECE node and return normalized lowering inputs."""

    operator = getattr(expr, "operator", None)
    operands = getattr(expr, "operands", None) or ()
    if len(operands) != 2:
        return f"{operator} requires exactly two operands", 0, 0, 0, None

    left, right = operands
    left_bits = _smt_width_if_known(left)
    right_bits = _smt_width_if_known(right)
    size_bytes = _safe_size_bytes(expr)
    if size_bytes is None:
        return f"{operator} result width is invalid", left_bits, right_bits, 0, None
    if size_bytes < 0:
        return f"{operator} result width is invalid", left_bits, right_bits, 0, None

    if operator == "PIECE":
        if left_bits <= 0 or right_bits <= 0:
            return "PIECE operand width is unavailable", left_bits, right_bits, 0, None
        expected_bits = left_bits + right_bits
        result_bits = size_bytes * 8 if size_bytes > 0 else expected_bits
        if size_bytes > 0 and result_bits != expected_bits:
            return (
                "PIECE result width does not equal the concatenated operand widths",
                left_bits,
                right_bits,
                result_bits,
                None,
            )
        return None, left_bits, right_bits, result_bits, None

    if operator != "SUBPIECE":
        return None, left_bits, right_bits, size_bytes * 8, None
    if left_bits <= 0:
        return "SUBPIECE source width is unavailable", left_bits, right_bits, 0, None
    result_bits = size_bytes * 8
    if result_bits <= 0:
        return "SUBPIECE result width is unavailable", left_bits, right_bits, 0, None
    byte_offset = _expr_constant_int(right)
    if byte_offset is None:
        if right_bits <= 0:
            return "SUBPIECE byte-offset width is unavailable", left_bits, right_bits, result_bits, None
        return "SUBPIECE dynamic byte offset has no exact SMT lowering", left_bits, right_bits, result_bits, None
    if byte_offset < 0:
        return "SUBPIECE byte offset is negative", left_bits, right_bits, result_bits, byte_offset
    low_bit = byte_offset * 8
    high_bit = low_bit + result_bits - 1
    if high_bit >= left_bits:
        return "SUBPIECE extraction range exceeds source width", left_bits, right_bits, result_bits, byte_offset
    return None, left_bits, right_bits, result_bits, byte_offset


def _piece_subpiece_width_issue(expr) -> Optional[str]:
    """Return a width/range defect before lowering a byte/bit-vector adapter."""

    return _piece_subpiece_contract(expr)[0]


def _expr_is_known_zero_bitpattern(expr, bits: int) -> bool:
    value = _expr_constant_int(expr)
    if value is None:
        return False
    mask = (1 << int(bits)) - 1
    return (value & mask) in {0, 1 << (int(bits) - 1)}


def _expr_is_known_nan_or_inf_bitpattern(expr, bits: int) -> bool:
    value = _expr_constant_int(expr)
    if value is None or bits not in _FLOAT_BV_WIDTH_TO_SORT:
        return False
    bits = int(bits)
    value &= (1 << bits) - 1
    ebits, sbits = _FLOAT_BV_WIDTH_TO_SORT[bits]
    fraction_bits = sbits - 1
    exponent_mask = ((1 << ebits) - 1) << fraction_bits
    exponent = value & exponent_mask
    return exponent == exponent_mask


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
    *,
    float_mode: str = "uf",
) -> str:
    """式を target_bits 幅の bitvector に揃える。"""
    if target_bits <= 0:
        return expr_smt

    if float_mode == "fp" and expression_renders_as_fp_sort(expr, float_mode=float_mode):
        expr_bits = expression_smt_bit_width(expr) or target_bits
        expr_smt = f"((_ fp.to_ieee_bv) {expr_smt})"
        return _coerce_smt_bitvec_width(
            expr_smt,
            expr_bits,
            target_bits,
            prefer_sign_extension=prefer_sign_extension,
        )

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
        return _coerce_smt_bitvec_width(
            expr_smt,
            expr_bits,
            target_bits,
            prefer_sign_extension=prefer_sign_extension,
        )
    if expr is not None and getattr(expr, "expr_type", None) == expr.expr_type.__class__.CONSTANT:
        value = getattr(expr, "value", 0)
        if isinstance(value, int) and target_bits > 0:
            value = value & ((1 << target_bits) - 1)
            return f"(_ bv{value} {target_bits})"
    return _coerce_smt_bitvec_width(
        expr_smt,
        expr_bits,
        target_bits,
        prefer_sign_extension=prefer_sign_extension,
    )


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


def _smt_bv_const(value: int, bits: int) -> str:
    mask = (1 << bits) - 1
    return f"(_ bv{int(value) & mask} {bits})"


def _smt_extract(high_bit: int, low_bit: int, value_smt: str) -> str:
    return f"((_ extract {int(high_bit)} {int(low_bit)}) {value_smt})"


def _smt_concat(parts: List[str]) -> str:
    if not parts:
        raise ValueError("SMT concat requires at least one part")
    result = parts[0]
    for part in parts[1:]:
        result = f"(concat {result} {part})"
    return result


def _smt_extend_to_width(expr, expr_smt: str, target_bits: int, *, signed: bool) -> str:
    return _coerce_expr_to_bitvec_width(
        expr,
        expr_smt,
        target_bits,
        prefer_sign_extension=signed,
        float_mode="uf",
    )


def _smt_low_bits(expr_smt: str, current_bits: int, target_bits: int) -> str:
    if current_bits <= target_bits:
        return expr_smt
    return f"((_ extract {target_bits - 1} 0) {expr_smt})"


def _smt_scale_term(expr_smt: str, factor: int, bits: int) -> Optional[str]:
    if factor == 0:
        return None
    if factor == 1:
        return expr_smt
    if factor == -1:
        return f"(bvneg {expr_smt})"
    return f"(bvmul {_smt_bv_const(factor, bits)} {expr_smt})"


# Sibling modules reference each other at call time; import them last to avoid cycles.
from scripts.function_tracer_pcode.core.render_smt.float_theory import (
    expression_renders_as_fp_sort,
)
from scripts.function_tracer_pcode.core.render_smt.render import (
    _ARITHMETIC_BINARY_OPERATORS,
    _BITWISE_BINARY_OPERATORS,
    _BOOLEAN_BINARY_OPERATORS,
    _FLOAT_BV_WIDTH_TO_SORT,
    _coerce_bool_to_bitvec,
    expression_returns_bool,
)
