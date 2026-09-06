"""Core expression -> SMT-LIB renderer, operator table, logic selection and unsupported-op detection."""

from __future__ import annotations

import hashlib
import re
from typing import Mapping, Optional
from scripts.function_tracer_pcode.core.intrinsics import is_supported_pcode_intrinsic


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


_FLOAT_PREDICATE_SMT_NAMES = {
    "FLOAT_EQUAL": "float_equal",
    "FLOAT_NOTEQUAL": "float_notequal",
    "FLOAT_LESS": "float_less",
    "FLOAT_LESSEQUAL": "float_lessequal",
}


_FLOAT_ARITHMETIC_SMT_NAMES = {
    "FLOAT_ADD": "float_add",
    "FLOAT_SUB": "float_sub",
    "FLOAT_MULT": "float_mult",
    "FLOAT_DIV": "float_div",
    "FLOAT_SDIV": "float_div",
    "FLOAT_REM": "float_rem",
    "FLOAT_SREM": "float_rem",
}


_FLOAT_ARITHMETIC_FP_OPS = {
    "FLOAT_ADD": "fp.add",
    "FLOAT_SUB": "fp.sub",
    "FLOAT_MULT": "fp.mul",
    "FLOAT_DIV": "fp.div",
    "FLOAT_SDIV": "fp.div",
    "FLOAT_REM": "fp.rem",
    "FLOAT_SREM": "fp.rem",
}


_FLOAT_ARITHMETIC_FP_SPECS = {
    "FLOAT_ADD": {"fp_op": "fp.add", "rounding": True, "guard_known_exceptional_operands": False},
    "FLOAT_SUB": {"fp_op": "fp.sub", "rounding": True, "guard_known_exceptional_operands": False},
    "FLOAT_MULT": {"fp_op": "fp.mul", "rounding": True, "guard_known_exceptional_operands": False},
    "FLOAT_DIV": {"fp_op": "fp.div", "rounding": True, "guard_known_exceptional_operands": False},
    "FLOAT_REM": {"fp_op": "fp.rem", "rounding": False, "guard_known_exceptional_operands": False},
    "FLOAT_SDIV": {"fp_op": "fp.div", "rounding": True, "guard_known_exceptional_operands": True},
    "FLOAT_SREM": {"fp_op": "fp.rem", "rounding": False, "guard_known_exceptional_operands": True},
}


_FLOAT_BV_WIDTH_TO_SORT = {
    32: (8, 24),
    64: (11, 53),
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


_BITWISE_BINARY_OPERATORS = {"INT_AND", "INT_OR", "INT_XOR"}


_SUPPORTED_BINARY_OPERATORS = (
    _ARITHMETIC_BINARY_OPERATORS
    | _BOOLEAN_BINARY_OPERATORS
    | set(_FLOAT_ARITHMETIC_SMT_NAMES.keys())
    | {"PIECE", "SUBPIECE", "INT_LEFT", "INT_RIGHT", "INT_SRIGHT"}
)


_SUPPORTED_UNARY_OPERATORS = {
    "INT2FLOAT",
    "INT_ZEXT",
    "INT_SEXT",
    "INT_NEGATE",
    "INT_2COMP",
    "BOOL_NEGATE",
    "FLOAT_NEG",
    "FLOAT_ABS",
    "FLOAT_SQRT",
    "FLOAT_NAN",
}


class UnsupportedSmtSemanticsError(ValueError):
    """Base class for typed refusals of unavailable exact SMT semantics."""


class UnsupportedSmtIntrinsicError(UnsupportedSmtSemanticsError):
    """Typed semantic-lowering refusal; message text is diagnostic only."""

    def __init__(self, *, mnemonic: Optional[str], opcode: Optional[str]) -> None:
        self.mnemonic = mnemonic
        self.opcode = opcode
        self.intrinsic_identity = mnemonic or opcode
        super().__init__(
            f"Unsupported intrinsic for SMT lowering: {self.intrinsic_identity}"
        )


class UnknownSmtExtensionWidthError(ValueError):
    """Typed refusal to lower an extension without its P-code output width."""

    def __init__(self, *, operator: str, operand_bits: int) -> None:
        self.operator = operator
        self.operand_bits = int(operand_bits)
        super().__init__(
            f"{operator} output width is unavailable "
            f"(operand width: {self.operand_bits or 'unknown'} bits)"
        )


class UnsupportedSmtOperatorError(UnsupportedSmtSemanticsError):
    """Typed refusal for an operator that has no exact SMT lowering."""

    def __init__(
        self,
        *,
        operator: Optional[str],
        reason: str,
        operand_bits: int = 0,
        result_bits: int = 0,
    ) -> None:
        self.operator = operator
        self.reason = reason
        self.operand_bits = int(operand_bits or 0)
        self.result_bits = int(result_bits or 0)
        super().__init__(
            f"{operator or 'unknown operator'} has no exact SMT lowering: {reason} "
            f"(operand width: {self.operand_bits or 'unknown'} bits, "
            f"result width: {self.result_bits or 'unknown'} bits)"
        )


def expression_to_smt(
    expr,
    *,
    symbol_name_mapping: Optional[Mapping[str, str]] = None,
    float_mode: str = "uf",
) -> str:
    """式を SMT-LIB 文字列へ変換する。"""
    return _to_smt_internal(
        expr,
        symbol_name_mapping=symbol_name_mapping,
        float_mode=float_mode,
    )


def expression_returns_bool(expr) -> bool:
    """式が SMT 上で Bool sort を返すか判定する。"""
    if expr is None:
        return False

    expr_type = expr.expr_type
    expr_kind = expr_type.__class__

    if expr_type == expr_kind.BINARY_OP:
        return expr.operator in _BOOLEAN_BINARY_OPERATORS

    if expr_type == expr_kind.UNARY_OP:
        return expr.operator in {"BOOL_NEGATE", "FLOAT_NAN"}

    if expr_type == expr_kind.PHI:
        branches = expr.value or []
        return bool(branches) and all(
            expression_returns_bool(branch_value) for _, branch_value in branches
        )

    return False


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


def expression_node_has_unsupported_smt_ops(
    expr, *, allow_call: bool = False,
) -> bool:
    """Return whether one node lacks an exact SMT lowering.

    Direct operands are retained so local arity, width, and precision
    invariants can be checked. Descendants are deliberately not traversed.
    """
    if expr is None:
        return False

    expr_type = expr.expr_type
    expr_kind = expr_type.__class__

    if expr_type == expr_kind.CALL and not allow_call:
        return True

    if expr_type == expr_kind.BINARY_OP:
        if expr.operator not in _SUPPORTED_BINARY_OPERATORS:
            return True
        if expr.operator in {"PIECE", "SUBPIECE"}:
            return _piece_subpiece_width_issue(expr) is not None
        if expr.operator in _FLOAT_ARITHMETIC_FP_SPECS:
            operands = getattr(expr, "operands", None) or []
            if len(operands) == 2 and any(
                _is_float_rendered_expr(operand) for operand in operands
            ):
                left_bits = expression_smt_bit_width(operands[0])
                right_bits = expression_smt_bit_width(operands[1])
                result_bits = expression_smt_bit_width(expr)
                if not (
                    left_bits == right_bits == result_bits
                    and result_bits in _FLOAT_BV_WIDTH_TO_SORT
                ):
                    return True

    if expr_type == expr_kind.UNARY_OP:
        if expr.operator not in _SUPPORTED_UNARY_OPERATORS:
            return True
        if expr.operator in {"INT_ZEXT", "INT_SEXT"} and int(expr.size or 0) <= 0:
            return True
        if expr.operator == "INT2FLOAT":
            operands = getattr(expr, "operands", None) or []
            operand_bits = (
                expression_smt_bit_width(operands[0])
                if len(operands) == 1
                else 0
            )
            result_bits = int(expr.size or 0) * 8
            if operand_bits <= 0 or result_bits not in _FLOAT_BV_WIDTH_TO_SORT:
                return True

    if expr_type == expr_kind.INTRINSIC:
        if not is_supported_pcode_intrinsic(
            opcode=getattr(expr, "opcode", None),
            mnemonic=getattr(expr, "name", None),
        ):
            return True
        if getattr(expr, "name", None) == "NEON_ext" and not _neon_ext_operands_are_smt_supported(expr):
            return True

    return False


def expression_contains_unsupported_smt_ops(expr, *, allow_call: bool = False) -> bool:
    """SMT renderer が直接扱えない演算子を含むか判定する。"""
    if expr is None:
        return False

    if expression_node_has_unsupported_smt_ops(expr, allow_call=allow_call):
        return True

    expr_type = expr.expr_type
    expr_kind = expr_type.__class__

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


def expression_uses_smt_uf(expr, *, float_mode: str = "fp") -> bool:
    """Return True when expr needs uninterpreted SMT functions."""
    if expr is None:
        return False
    return bool(
        collect_intrinsic_smt_declarations(expr)
        or collect_float_predicate_smt_declarations(expr, float_mode=float_mode)
    )


def smt_logic_name(
    *,
    uses_float_theory: bool = False,
    uses_arrays: bool = False,
    uses_uf: bool = False,
) -> str:
    if uses_float_theory and uses_arrays:
        return "QF_AUFBVFP"
    if uses_float_theory and uses_uf:
        return "QF_UFFPBV"
    if uses_float_theory:
        return "QF_FPBV"
    if uses_arrays:
        return "QF_AUFBV"
    if uses_uf:
        return "QF_UFBV"
    return "QF_BV"


def _coerce_bool_to_bitvec(expr, expr_smt: str, bits: int) -> str:
    """Bool sort の式を 0/1 の bitvector へ変換する。"""
    if bits <= 0 or not expression_returns_bool(expr):
        return expr_smt
    return f"(ite {expr_smt} (_ bv1 {bits}) (_ bv0 {bits}))"


def _coerce_expr_to_bool(expr, expr_smt: str) -> str:
    """Bitvector-shaped boolean operands are normalized before BOOL_* SMT ops."""
    if expression_returns_bool(expr):
        return expr_smt

    expr_type = getattr(expr, "expr_type", None)
    expr_kind = getattr(expr_type, "__class__", None)
    if expr_kind is not None and expr_type == expr_kind.CONSTANT:
        try:
            return "false" if int(getattr(expr, "value", 0) or 0) == 0 else "true"
        except Exception:
            return "false"

    bits = expression_smt_bit_width(expr)
    if bits <= 0:
        bits = max(1, int(getattr(expr, "size", 0) or 1) * 8)
    return f"(not (= {expr_smt} (_ bv0 {bits})))"


def _to_smt_internal(
    expr,
    prefer_signed_arithmetic: bool = False,
    symbol_name_mapping: Optional[Mapping[str, str]] = None,
    address_context: bool = False,
    float_mode: str = "uf",
) -> str:
    expr_type = expr.expr_type
    expr_kind = expr_type.__class__

    if expr_type == expr_kind.CONSTANT:
        bits = expr.get_bit_width()
        global_address = global_address_smt(expr, bits)
        if global_address is not None:
            # The absolute address of a named global differs between the two
            # binaries; the shared symbolic base address is the identity.
            return global_address
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
                global_address = global_address_smt(expr, bits)
                if global_address is not None:
                    return global_address
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
            float_mode=float_mode,
        )

    if expr_type == expr_kind.BINARY_OP:
        operator = getattr(expr, "operator", None)
        operands = tuple(getattr(expr, "operands", None) or ())

        if operator in {"PIECE", "SUBPIECE"}:
            (
                width_issue,
                left_bits,
                right_bits,
                result_bits,
                byte_offset,
            ) = _piece_subpiece_contract(expr)
            if width_issue is not None:
                raise UnsupportedSmtOperatorError(
                    operator=operator,
                    reason=width_issue,
                    operand_bits=max(left_bits, right_bits),
                    result_bits=result_bits,
                )
            # The contract has already checked arity and normalized every
            # value used below, so these accesses cannot escape as raw index
            # or conversion errors.
            left, right = operands

            if operator == "PIECE":
                left_smt = _to_smt_internal(
                    left,
                    prefer_signed_arithmetic,
                    symbol_name_mapping,
                    address_context,
                    float_mode,
                )
                right_smt = _to_smt_internal(
                    right,
                    prefer_signed_arithmetic,
                    symbol_name_mapping,
                    address_context,
                    float_mode,
                )
                left_smt = _coerce_expr_to_bitvec_width(
                    left, left_smt, left_bits, float_mode=float_mode
                )
                right_smt = _coerce_expr_to_bitvec_width(
                    right, right_smt, right_bits, float_mode=float_mode
                )
                return f"(concat {left_smt} {right_smt})"

            source_smt = _to_smt_internal(
                left,
                prefer_signed_arithmetic,
                symbol_name_mapping,
                address_context,
                float_mode,
            )
            source_smt = _coerce_expr_to_bitvec_width(
                left, source_smt, left_bits, float_mode=float_mode
            )
            low_bit = byte_offset * 8
            high_bit = low_bit + result_bits - 1
            return f"((_ extract {high_bit} {low_bit}) {source_smt})"

        # Other binary operators retain their existing lowering path. Their
        # arity contract is unrelated to the PIECE/SUBPIECE bit-vector gate.
        left = operands[0]
        right = operands[1]

        left_bits = expression_smt_bit_width(left)
        right_bits = expression_smt_bit_width(right)
        left_smt = _to_smt_internal(left, prefer_signed_arithmetic, symbol_name_mapping, address_context, float_mode)
        right_smt = _to_smt_internal(right, prefer_signed_arithmetic, symbol_name_mapping, address_context, float_mode)

        if (
            float_mode == "fp"
            and expr.operator in _FLOAT_PREDICATE_SMT_NAMES
            and _float_predicate_can_use_fp_theory(expr, left_bits, right_bits)
        ):
            return _float_predicate_to_smt(
                expr.operator,
                left_smt,
                right_smt,
                left,
                right,
                left_bits,
                float_mode=float_mode,
            )

        if expr.operator in _FLOAT_ARITHMETIC_SMT_NAMES:
            float_arith_smt = _float_binary_to_smt(
                expr.operator,
                left,
                right,
                left_smt,
                right_smt,
                left_bits,
                right_bits,
                expression_smt_bit_width(expr) or max(left_bits, right_bits),
                float_mode=float_mode,
            )
            if float_arith_smt is not None:
                return float_arith_smt

        if expr.operator in ["INT_LEFT", "INT_RIGHT", "INT_SRIGHT"]:
            left_smt = _coerce_bool_to_bitvec(left, left_smt, left_bits)
            right_smt = _coerce_bool_to_bitvec(right, right_smt, right_bits)
            shift_bits = left_bits
            if right_bits != shift_bits:
                right_smt = _coerce_smt_bitvec_width(right_smt, right_bits, shift_bits)
            op = expr._get_smt_operator(expr.operator)
            shifted_smt = f"({op} {left_smt} {right_smt})"
            return _coerce_smt_bitvec_width(
                shifted_smt,
                shift_bits,
                expression_smt_bit_width(expr) or shift_bits,
            )

        if expr.operator in _ARITHMETIC_BINARY_OPERATORS:
            left_smt = _coerce_bool_to_bitvec(left, left_smt, left_bits)
            right_smt = _coerce_bool_to_bitvec(right, right_smt, right_bits)
            target_bits = (
                expression_smt_bit_width(expr)
                if expr.operator in _BITWISE_BINARY_OPERATORS
                else _preferred_arithmetic_width(left, right, left_bits, right_bits)
            )
            if left_bits != target_bits or right_bits != target_bits:
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
                        float_mode=float_mode,
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
                        float_mode=float_mode,
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
            left_smt = _to_smt_internal(left, False, symbol_name_mapping, address_context, float_mode)
            right_smt = _to_smt_internal(right, False, symbol_name_mapping, address_context, float_mode)

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
                        float_mode=float_mode,
                    )
                    right_smt = _coerce_expr_to_bitvec_width(
                        right,
                        right_smt,
                        target_bits,
                        prefer_sign_extension=prefer_sign_extension,
                        float_mode=float_mode,
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

        if expr.operator in {"BOOL_AND", "BOOL_OR", "BOOL_XOR"}:
            op = expr._get_smt_operator(expr.operator)
            return (
                f"({op} "
                f"{_coerce_expr_to_bool(left, left_smt)} "
                f"{_coerce_expr_to_bool(right, right_smt)})"
            )

        if expr.operator not in _SUPPORTED_BINARY_OPERATORS:
            raise UnsupportedSmtOperatorError(
                operator=expr.operator,
                reason="unsupported binary operator",
                operand_bits=max(left_bits, right_bits),
                result_bits=expression_smt_bit_width(expr),
            )
        op = expr._get_smt_operator(expr.operator)
        return f"({op} {left_smt} {right_smt})"

    if expr_type == expr_kind.UNARY_OP:
        operand = expr.operands[0]
        operand_smt = _to_smt_internal(
            operand,
            prefer_signed_arithmetic,
            symbol_name_mapping,
            address_context,
            float_mode,
        )
        operand_bits = expression_smt_bit_width(operand)

        if expr.operator == "INT2FLOAT":
            output_bits = int(expr.size or 0) * 8
            if float_mode != "fp":
                raise UnsupportedSmtOperatorError(
                    operator=expr.operator,
                    reason="exact integer-to-float lowering requires FP theory mode",
                    operand_bits=operand_bits,
                    result_bits=output_bits,
                )
            if operand_bits <= 0:
                raise UnsupportedSmtOperatorError(
                    operator=expr.operator,
                    reason="input integer width is unavailable",
                    operand_bits=operand_bits,
                    result_bits=output_bits,
                )
            fp_sort = _FLOAT_BV_WIDTH_TO_SORT.get(output_bits)
            if fp_sort is None:
                raise UnsupportedSmtOperatorError(
                    operator=expr.operator,
                    reason="output floating-point width is unsupported",
                    operand_bits=operand_bits,
                    result_bits=output_bits,
                )
            ebits, sbits = fp_sort
            return f"((_ to_fp {ebits} {sbits}) RNE {operand_smt})"

        if expr.operator == "INT_ZEXT":
            output_bits = int(expr.size or 0) * 8
            if output_bits <= 0:
                raise UnknownSmtExtensionWidthError(
                    operator=expr.operator,
                    operand_bits=operand_bits,
                )
            if expression_returns_bool(operand):
                return _coerce_bool_to_bitvec(operand, operand_smt, output_bits)
            extend_bits = output_bits - operand_bits
            if extend_bits > 0:
                return f"((_ zero_extend {extend_bits}) {operand_smt})"
            if extend_bits == 0:
                return operand_smt
            return f"((_ extract {output_bits - 1} 0) {operand_smt})"

        if expr.operator == "INT_SEXT":
            output_bits = int(expr.size or 0) * 8
            if output_bits <= 0:
                raise UnknownSmtExtensionWidthError(
                    operator=expr.operator,
                    operand_bits=operand_bits,
                )
            if expression_returns_bool(operand):
                return _coerce_bool_to_bitvec(operand, operand_smt, output_bits)
            extend_bits = output_bits - operand_bits
            if extend_bits > 0:
                return f"((_ sign_extend {extend_bits}) {operand_smt})"
            if extend_bits == 0:
                return operand_smt
            return f"((_ extract {output_bits - 1} 0) {operand_smt})"

        if expr.operator == "INT_NEGATE":
            target_bits = expression_smt_bit_width(expr) or operand_bits
            operand_smt = _coerce_bool_to_bitvec(operand, operand_smt, target_bits)
            return f"(bvnot {operand_smt})"

        if expr.operator == "INT_2COMP":
            target_bits = expression_smt_bit_width(expr) or operand_bits
            operand_smt = _coerce_bool_to_bitvec(operand, operand_smt, target_bits)
            return f"(bvneg {operand_smt})"

        if expr.operator == "BOOL_NEGATE":
            return f"(not {_coerce_expr_to_bool(operand, operand_smt)})"

        fp_unary_predicate_smt = _float_unary_predicate_to_smt(
            expr.operator,
            operand,
            operand_smt,
            operand_bits,
            float_mode=float_mode,
        )
        if fp_unary_predicate_smt is not None:
            return fp_unary_predicate_smt

        fp_unary_value_smt = _float_unary_value_to_smt(
            expr.operator,
            operand,
            operand_smt,
            operand_bits,
            float_mode=float_mode,
        )
        if fp_unary_value_smt is not None:
            return fp_unary_value_smt

        fp_unary_smt = _float_unary_to_bitvec_smt(
            expr.operator,
            _coerce_smt_bitvec_width(
                operand_smt,
                operand_bits,
                expression_smt_bit_width(expr) or operand_bits,
            ),
            expression_smt_bit_width(expr) or operand_bits,
        )
        if fp_unary_smt is not None:
            return fp_unary_smt

        if expr.operator not in _SUPPORTED_UNARY_OPERATORS:
            raise UnsupportedSmtOperatorError(
                operator=expr.operator,
                reason="unsupported unary operator",
                operand_bits=operand_bits,
                result_bits=expression_smt_bit_width(expr),
            )
        op = expr._get_smt_operator(expr.operator)
        return f"({op} {operand_smt})"

    if expr_type == expr_kind.CALL:
        args = " ".join(
            _to_smt_internal(
                operand,
                prefer_signed_arithmetic,
                symbol_name_mapping,
                address_context,
                float_mode,
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
            float_mode,
        )
        addr_smt = _coerce_expr_to_bitvec_width(
            addr_expr,
            addr_smt,
            64,
            prefer_sign_extension=False,
            float_mode=float_mode,
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
                    float_mode,
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
                float_mode=float_mode,
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
                    float_mode,
                )
            elif cond is not None and hasattr(cond, "to_smt"):
                cond_str = cond.to_smt(symbol_name_mapping=symbol_name_mapping, float_mode=float_mode)
            else:
                cond_str = "true"

            val_str = render_branch_value(val)

            if cond_str == "true":
                result = val_str
            elif cond_str != "false":
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


# Sibling modules reference each other at call time; import them last to avoid cycles.
from scripts.function_tracer_pcode.core.render_smt.float_theory import (
    _float_binary_to_smt,
    _float_predicate_can_use_fp_theory,
    _float_predicate_to_smt,
    _float_unary_predicate_to_smt,
    _float_unary_to_bitvec_smt,
    _float_unary_value_to_smt,
    _is_float_rendered_expr,
    collect_float_predicate_smt_declarations,
)
from scripts.function_tracer_pcode.core.render_smt.intrinsics import (
    _lower_intrinsic_to_smt,
    collect_intrinsic_smt_declarations,
)
from scripts.function_tracer_pcode.core.render_smt.loop_lowering import (
    _neon_ext_operands_are_smt_supported,
)
from scripts.function_tracer_pcode.core.render_smt.unknowns import (
    global_address_smt,
    _coerce_address_value_ref,
    _unknown_smt_symbol_name,
)
from scripts.function_tracer_pcode.core.render_smt.widths import (
    _coerce_expr_to_bitvec_width,
    _coerce_smt_bitvec_width,
    _expr_prefers_signed_extension,
    _piece_subpiece_contract,
    _piece_subpiece_width_issue,
    _preferred_arithmetic_width,
    expression_smt_bit_width,
)
