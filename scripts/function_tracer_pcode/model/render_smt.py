# -*- coding: utf-8 -*-
"""SMT-LIB rendering helpers for Expression."""

import hashlib
import re
from typing import Any, Iterable, List, Mapping, Optional, Tuple

from .intrinsics import (
    COUNTED_LOOP_SUM_OPCODE,
    READONLY_SUM_OPCODE,
    STATE_TRANSITION_LOOP_COUNT_OPCODE,
    PTRADD_OPCODE,
    PTRSUB_OPCODE,
    is_supported_pcode_intrinsic,
)
from .signature import get_declared_type_signedness
from .runtime_refs import (
    AddressValueRef,
    CanonicalLocation,
    CountedLoopSummaryRef,
    PostStateReadRef,
    PostStateValueRef,
    ReadonlyReductionRef,
    StateTransitionLoopSummaryRef,
    loop_summary_method_b_key,
)


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
_FLOAT_UNARY_PREDICATE_SMT_NAMES = {
    "FLOAT_NAN": "float_nan",
}
_FLOAT_UNARY_VALUE_SMT_NAMES = {
    "FLOAT_SQRT": "float_sqrt",
}
_FLOAT_PREDICATE_FP_OPS = {
    "FLOAT_EQUAL": "fp.eq",
    "FLOAT_LESS": "fp.lt",
    "FLOAT_LESSEQUAL": "fp.leq",
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
        return max(explicit_bits, operand_bits)

    if expr_type == expr_kind.UNARY_OP:
        operand = expr.operands[0] if getattr(expr, "operands", None) else None
        operand_bits = expression_smt_bit_width(operand)
        if expr.operator in {"INT_ZEXT", "INT_SEXT"}:
            explicit_bits = (expr.size or 0) * 8
            return explicit_bits or operand_bits
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


def collect_intrinsic_smt_declarations(expr) -> List[str]:
    """Collect deterministic SMT declarations needed for supported intrinsic applications."""
    declarations: List[str] = []
    seen = set()
    for node in _iter_expression_nodes(expr):
        if node is None or getattr(node, "expr_type", None) is None:
            continue
        expr_kind = node.expr_type.__class__
        if node.expr_type != expr_kind.INTRINSIC:
            continue
        decl = _intrinsic_smt_declaration(node)
        if decl is None or decl in seen:
            continue
        seen.add(decl)
        declarations.append(decl)
    return declarations


def collect_float_predicate_smt_declarations(expr, *, float_mode: str = "uf") -> List[str]:
    """Collect declarations for P-code FLOAT_* predicates lowered as UFBV predicates."""
    declarations: List[str] = []
    seen = set()
    for node in _iter_expression_nodes(expr):
        if node is None or getattr(node, "expr_type", None) is None:
            continue
        expr_kind = node.expr_type.__class__
        if node.expr_type == expr_kind.BINARY_OP:
            op = getattr(node, "operator", None)
            smt_name = _FLOAT_PREDICATE_SMT_NAMES.get(op)
            is_predicate = smt_name is not None
            if smt_name is None:
                smt_name = _FLOAT_ARITHMETIC_SMT_NAMES.get(op)
                is_predicate = False
            if smt_name is None:
                continue
            operands = getattr(node, "operands", None) or []
            if len(operands) != 2:
                continue
            left_bits = max(1, int(expression_smt_bit_width(operands[0]) or 1))
            right_bits = max(1, int(expression_smt_bit_width(operands[1]) or 1))
            result_bits = expression_smt_bit_width(node) or max(left_bits, right_bits)
            if result_bits <= 0:
                result_bits = 1
            if is_predicate and float_mode == "fp" and _float_predicate_can_use_fp_theory(
                node,
                left_bits,
                right_bits,
            ):
                continue
            if (not is_predicate and float_mode == "fp" and
                _float_binary_can_use_fp_theory(node, left_bits, right_bits)
                and left_bits == right_bits == result_bits):
                continue
            if is_predicate:
                decl = f"(declare-fun {smt_name} ((_ BitVec {left_bits}) (_ BitVec {right_bits})) Bool)"
            else:
                left_bits = int(left_bits)
                right_bits = int(right_bits)
                decl = (
                    f"(declare-fun {smt_name} "
                    f"((_ BitVec {left_bits}) (_ BitVec {right_bits})) "
                    f"(_ BitVec {result_bits}))"
                )
        elif node.expr_type == expr_kind.UNARY_OP:
            op = getattr(node, "operator", None)
            smt_name = _FLOAT_UNARY_PREDICATE_SMT_NAMES.get(op)
            is_predicate = smt_name is not None
            if smt_name is None:
                smt_name = _FLOAT_UNARY_VALUE_SMT_NAMES.get(op)
                is_predicate = False
            if smt_name is None:
                continue
            operands = getattr(node, "operands", None) or []
            if len(operands) != 1:
                continue
            operand_bits = max(1, int(expression_smt_bit_width(operands[0]) or 1))
            if float_mode == "fp" and operand_bits in _FLOAT_BV_WIDTH_TO_SORT:
                continue
            if is_predicate:
                decl = f"(declare-fun {smt_name} ((_ BitVec {operand_bits})) Bool)"
            else:
                result_bits = expression_smt_bit_width(node) or operand_bits
                if result_bits <= 0:
                    result_bits = operand_bits
                decl = (
                    f"(declare-fun {smt_name} ((_ BitVec {operand_bits})) "
                    f"(_ BitVec {result_bits}))"
                )
        else:
            continue
        if decl in seen:
            continue
        seen.add(decl)
        declarations.append(decl)
    return declarations


def expression_uses_smt_float_theory(expr) -> bool:
    """Return True when expr contains FLOAT_* predicates renderable with SMT FP theory."""
    for node in _iter_expression_nodes(expr):
        if node is None or getattr(node, "expr_type", None) is None:
            continue
        expr_kind = node.expr_type.__class__
        if node.expr_type == expr_kind.BINARY_OP:
            operands = getattr(node, "operands", None) or []
            if len(operands) != 2:
                continue
            if _float_predicate_can_use_fp_theory(
                node,
                expression_smt_bit_width(operands[0]),
                expression_smt_bit_width(operands[1]),
            ):
                return True
            if _float_binary_can_use_fp_theory(
                node,
                expression_smt_bit_width(operands[0]),
                expression_smt_bit_width(operands[1]),
            ):
                return True
        elif node.expr_type == expr_kind.UNARY_OP and getattr(node, "operator", None) == "FLOAT_NAN":
            operands = getattr(node, "operands", None) or []
            if len(operands) == 1 and int(expression_smt_bit_width(operands[0]) or 0) in _FLOAT_BV_WIDTH_TO_SORT:
                return True
        elif node.expr_type == expr_kind.UNARY_OP and getattr(node, "operator", None) == "FLOAT_SQRT":
            operands = getattr(node, "operands", None) or []
            if len(operands) == 1 and int(expression_smt_bit_width(operands[0]) or 0) in _FLOAT_BV_WIDTH_TO_SORT:
                return True
    return False


def expressions_use_smt_float_theory(expressions: Iterable[Any]) -> bool:
    return any(expression_uses_smt_float_theory(expr) for expr in expressions if expr is not None)


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


def _float_predicate_can_use_fp_theory(expr, left_bits: int, right_bits: int) -> bool:
    if getattr(expr, "operator", None) not in _FLOAT_PREDICATE_SMT_NAMES:
        return False
    left_bits = int(left_bits or 0)
    right_bits = int(right_bits or 0)
    return left_bits == right_bits and left_bits in _FLOAT_BV_WIDTH_TO_SORT


def _bitvec_to_fp_smt(expr_smt: str, bits: int) -> str:
    ebits, sbits = _FLOAT_BV_WIDTH_TO_SORT[int(bits)]
    return f"((_ to_fp {ebits} {sbits}) {expr_smt})"


def _float_predicate_to_smt(
    operator: str,
    left_smt: str,
    right_smt: str,
    left_expr,
    right_expr,
    bits: int,
    *,
    float_mode: str,
) -> str:
    left_fp = _normalize_to_fp_expr(left_smt, left_expr, bits, float_mode=float_mode)
    right_fp = _normalize_to_fp_expr(right_smt, right_expr, bits, float_mode=float_mode)
    if operator == "FLOAT_NOTEQUAL":
        return f"(not (fp.eq {left_fp} {right_fp}))"
    fp_op = _FLOAT_PREDICATE_FP_OPS.get(operator)
    if fp_op is None:
        smt_name = _FLOAT_PREDICATE_SMT_NAMES.get(operator, operator.lower())
        return f"({smt_name} {left_smt} {right_smt})"
    return f"({fp_op} {left_fp} {right_fp})"


def _is_float_rendered_expr(expr) -> bool:
    if expr is None:
        return False
    expr_type = getattr(expr, "expr_type", None)
    if expr_type is None:
        return False
    expr_kind = expr_type.__class__
    if expr_type == expr_kind.BINARY_OP:
        return (
            getattr(expr, "operator", None) in _FLOAT_ARITHMETIC_SMT_NAMES
            and _float_binary_can_use_fp_theory(
                expr,
                expression_smt_bit_width(expr.operands[0]) if expr.operands else 0,
                expression_smt_bit_width(expr.operands[1]) if expr.operands else 0,
            )
        )
    if expr_type == expr_kind.PHI:
        # Keep this classifier in lockstep with the PHI renderer below. PHI
        # branches are normalized through _coerce_expr_to_bitvec_width before
        # the ITE is built, so the emitted PHI term is always BitVec even when
        # every source branch started as an FP-theory expression.
        return False
    return False



def expression_smt_sort_kind(expr, *, float_mode: str = "uf") -> str:
    """Classify the SMT sort emitted for an expression: Bool, FP, or BV."""
    if expression_returns_bool(expr):
        return "Bool"
    if float_mode == "fp" and _is_float_rendered_expr(expr):
        return "FP"
    return "BV"


def expression_renders_as_fp_sort(expr, *, float_mode: str = "uf") -> bool:
    """Return True when expression_to_smt returns an SMT FP-sort term."""
    return expression_smt_sort_kind(expr, float_mode=float_mode) == "FP"

def _looks_like_fp_expr(expr_smt: str) -> bool:
    expr_smt = expr_smt.strip()
    return expr_smt.startswith("(fp.") or expr_smt.startswith("((_ to_fp ")


def _normalize_to_fp_expr(
    expr_smt: str,
    expr,
    bits: int,
    *,
    float_mode: str,
) -> str:
    bits = int(bits or 0)
    if float_mode != "fp" or bits <= 0 or bits not in _FLOAT_BV_WIDTH_TO_SORT:
        return expr_smt
    if _looks_like_fp_expr(expr_smt):
        return expr_smt
    if _is_float_rendered_expr(expr):
        return expr_smt
    try:
        return _bitvec_to_fp_smt(expr_smt, bits)
    except KeyError:
        # 非対応幅が混在した場合は原則 bit-vector 経由へフォールバックし、
        # 生成器側での非対応幅誤用を避ける。
        return expr_smt


def _float_binary_can_use_fp_theory(expr, left_bits: int, right_bits: int) -> bool:
    if not _float_binary_can_use_fp_theory_for_operator(
        getattr(expr, "operator", None),
        left_bits,
        right_bits,
    ):
        return False
    operator = getattr(expr, "operator", None)
    operands = getattr(expr, "operands", None) or []
    if len(operands) != 2:
        return False
    return not _float_binary_has_known_exceptional_operand(
        operator,
        operands[0],
        operands[1],
        int(left_bits or 0),
    )


def _float_binary_to_smt(
    operator: str,
    left_expr,
    right_expr,
    left_smt: str,
    right_smt: str,
    left_bits: int,
    right_bits: int,
    result_bits: int,
    *,
    float_mode: str,
) -> Optional[str]:
    fp_spec = _FLOAT_ARITHMETIC_FP_SPECS.get(operator)
    fp_op = fp_spec.get("fp_op") if fp_spec else None
    left_bits = int(left_bits or 0)
    right_bits = int(right_bits or 0)
    result_bits = int(result_bits or 0)
    if fp_op is not None and float_mode == "fp" and _float_binary_can_use_fp_theory_for_operator(
        operator,
        left_bits,
        right_bits,
    ) and not _float_binary_has_known_exceptional_operand(
        operator,
        left_expr,
        right_expr,
        left_bits,
    ):
        if not result_bits:
            result_bits = max(1, max(left_bits, right_bits))
        # FP 演算は演算結果幅とオペランド幅を揃えた時だけ採用する。
        if result_bits == left_bits == right_bits:
            left_fp = _normalize_to_fp_expr(
                left_smt,
                left_expr,
                left_bits,
                float_mode=float_mode,
            )
            right_fp = _normalize_to_fp_expr(
                right_smt,
                right_expr,
                right_bits,
                float_mode=float_mode,
            )
        else:
            left_fp = None
            right_fp = None
        if left_fp is not None and right_fp is not None:
            if not fp_spec.get("rounding", False):
                return f"({fp_op} {left_fp} {right_fp})"
            return f"({fp_op} RNE {left_fp} {right_fp})"
        return None

    if fp_op is not None:
        smt_name = _FLOAT_ARITHMETIC_SMT_NAMES.get(operator, operator.lower())
        return f"({smt_name} {left_smt} {right_smt})"

    return None


def _float_binary_can_use_fp_theory_for_operator(
    operator: str,
    left_bits: int,
    right_bits: int,
) -> bool:
    if operator not in _FLOAT_ARITHMETIC_FP_SPECS:
        return False
    left_bits = int(left_bits or 0)
    right_bits = int(right_bits or 0)
    return left_bits == right_bits and left_bits in _FLOAT_BV_WIDTH_TO_SORT


def _float_binary_has_known_exceptional_operand(
    operator: str,
    left_expr,
    right_expr,
    bits: int,
) -> bool:
    spec = _FLOAT_ARITHMETIC_FP_SPECS.get(operator)
    if not spec or not spec.get("guard_known_exceptional_operands"):
        return False
    bits = int(bits or 0)
    if bits not in _FLOAT_BV_WIDTH_TO_SORT:
        return True
    return (
        _expr_is_known_nan_or_inf_bitpattern(left_expr, bits)
        or _expr_is_known_nan_or_inf_bitpattern(right_expr, bits)
        or _expr_is_known_zero_bitpattern(right_expr, bits)
    )


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


def _float_unary_to_bitvec_smt(operator: str, operand_smt: str, bits: int) -> Optional[str]:
    """Lower bit-preserving unary FP operations emitted by Ghidra."""
    bits = int(bits or 0)
    if bits <= 0:
        return None
    sign_mask = 1 << (bits - 1)
    if operator == "FLOAT_NEG":
        return f"(bvxor {operand_smt} (_ bv{sign_mask} {bits}))"
    if operator == "FLOAT_ABS":
        abs_mask = sign_mask - 1
        return f"(bvand {operand_smt} (_ bv{abs_mask} {bits}))"
    return None


def _float_unary_predicate_to_smt(
    operator: str,
    operand,
    operand_smt: str,
    bits: int,
    *,
    float_mode: str,
) -> Optional[str]:
    smt_name = _FLOAT_UNARY_PREDICATE_SMT_NAMES.get(operator)
    if smt_name is None:
        return None
    bits = int(bits or 0)
    if float_mode == "fp" and bits in _FLOAT_BV_WIDTH_TO_SORT:
        return f"(fp.isNaN {_normalize_to_fp_expr(operand_smt, operand, bits, float_mode=float_mode)})"
    return f"({smt_name} {operand_smt})"


def _float_unary_value_to_smt(
    operator: str,
    operand,
    operand_smt: str,
    bits: int,
    *,
    float_mode: str,
) -> Optional[str]:
    bits = int(bits or 0)
    if operator != "FLOAT_SQRT":
        return None
    if float_mode == "fp" and bits in _FLOAT_BV_WIDTH_TO_SORT:
        fp_operand = _normalize_to_fp_expr(
            operand_smt,
            operand,
            bits,
            float_mode=float_mode,
        )
        return f"((_ fp.to_ieee_bv) (fp.sqrt RNE {fp_operand}))"
    smt_name = _FLOAT_UNARY_VALUE_SMT_NAMES.get(operator)
    if smt_name is None:
        return None
    return f"({smt_name} {operand_smt})"


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
    semantic_key = getattr(runtime_ref, "semantic_key", None)
    if callable(semantic_key):
        try:
            identity = semantic_key()
        except Exception:
            identity = None
        if identity is not None:
            return ("runtime_ref_semantic", identity)
    stable_key = getattr(runtime_ref, "stable_key", None)
    if callable(stable_key):
        try:
            identity = stable_key()
        except Exception:
            identity = None
        if identity is not None:
            stable_origin = _unknown_runtime_stable_origin_key(runtime_ref)
            if stable_origin is not None:
                return ("runtime_ref_with_origin", identity, stable_origin)
            return ("runtime_ref", identity)
    return (
        "expression_unknown_instance",
        id(expr),
        int(expression_smt_bit_width(expr) or 1),
    )


def _unknown_runtime_stable_origin_key(runtime_ref) -> Optional[Tuple[Any, ...]]:
    origin_kind = getattr(runtime_ref, "origin_kind", None)
    origin_ref = getattr(runtime_ref, "origin_ref", None)
    if origin_kind is None or origin_ref is None:
        return None
    stable_key = getattr(origin_ref, "stable_key", None)
    if not callable(stable_key):
        return None
    try:
        origin_key = stable_key()
    except Exception:
        return None
    if origin_key is None:
        return None
    return (origin_kind, origin_key)


def _unknown_smt_symbol_name(expr) -> str:
    identity = _unknown_runtime_identity_key(expr)
    bits = max(1, int(expression_smt_bit_width(expr) or 1))
    digest = hashlib.sha1(repr(identity).encode("utf-8")).hexdigest()[:16]
    return f"rtunk_{digest}_{bits}"


def _unknown_smt_declaration(expr) -> Tuple[str, int]:
    bits = max(1, int(expression_smt_bit_width(expr) or 1))
    return (_unknown_smt_symbol_name(expr), bits)


def _readonly_reduction_ref(expr) -> Optional[ReadonlyReductionRef]:
    runtime_ref = getattr(expr, "runtime_ref", None)
    if isinstance(runtime_ref, ReadonlyReductionRef):
        return runtime_ref
    return None


def _runtime_ref_smt_identity(expr, runtime_ref):
    loop_summary = getattr(runtime_ref, "loop_summary", None)
    if loop_summary is not None:
        requires_effect_proof = getattr(loop_summary, "requires_effect_proof", None)
        requires_path_proof = getattr(loop_summary, "requires_path_proof", None)
        if (
            (callable(requires_effect_proof) and requires_effect_proof())
            or (callable(requires_path_proof) and requires_path_proof())
        ):
            return (
                "opaque_loop_summary_identity",
                type(runtime_ref).__module__,
                type(runtime_ref).__qualname__,
                (
                    "effect_proof_required"
                    if callable(requires_effect_proof) and requires_effect_proof()
                    else "path_proof_required"
                ),
                id(runtime_ref),
                id(loop_summary),
                id(expr),
            )
        method_b_key = loop_summary_method_b_key(loop_summary)
        if method_b_key is not None:
            return (
                "loop_summary_method_b_runtime",
                type(runtime_ref).__module__,
                type(runtime_ref).__qualname__,
                ("ref_constant_bias", int(getattr(runtime_ref, "constant_bias", 0) or 0)),
                method_b_key,
            )
        loop_key = loop_summary.stable_key()
        if loop_key is None:
            return (
                "opaque_loop_summary_identity",
                type(runtime_ref).__module__,
                type(runtime_ref).__qualname__,
                "unkeyable",
                id(runtime_ref),
                id(loop_summary),
                id(expr),
            )
    semantic_key = getattr(runtime_ref, "semantic_key", None)
    if callable(semantic_key):
        identity = semantic_key()
        if identity is not None:
            return identity
    stable_key = getattr(runtime_ref, "stable_key", None)
    if callable(stable_key):
        return stable_key()
    return (
        "opaque_runtime_ref",
        type(runtime_ref).__module__,
        type(runtime_ref).__qualname__,
        id(runtime_ref),
        id(expr),
    )


def _readonly_sum_function_name(expr) -> str:
    operands = getattr(expr, "operands", None) or []
    base_bits = expression_smt_bit_width(operands[0]) if len(operands) >= 1 else 0
    count_bits = expression_smt_bit_width(operands[1]) if len(operands) >= 2 else 0
    result_bits = max(1, int(expression_smt_bit_width(expr) or 1))
    reduction_ref = _readonly_reduction_ref(expr)
    if reduction_ref is None:
        return f"rt_readonly_sum_{base_bits}_{count_bits}_{result_bits}"
    reduction_kind = re.sub(r"[^A-Za-z0-9_]+", "_", reduction_ref.reduction_kind or "sum")
    identity = _runtime_ref_smt_identity(expr, reduction_ref)
    digest = hashlib.sha1(repr(identity).encode("utf-8")).hexdigest()[:16]
    return f"rt_{reduction_kind}_{digest}_{base_bits}_{count_bits}_{result_bits}"


def _counted_loop_sum_ref(expr) -> Optional[CountedLoopSummaryRef]:
    runtime_ref = getattr(expr, "runtime_ref", None)
    if isinstance(runtime_ref, CountedLoopSummaryRef):
        return runtime_ref
    return None


def _state_transition_loop_count_ref(expr) -> Optional[StateTransitionLoopSummaryRef]:
    runtime_ref = getattr(expr, "runtime_ref", None)
    if isinstance(runtime_ref, StateTransitionLoopSummaryRef):
        return runtime_ref
    return None


def _state_transition_loop_count_function_name(expr) -> str:
    operands = getattr(expr, "operands", None) or []
    state_bits = expression_smt_bit_width(operands[0]) if len(operands) >= 1 else 0
    result_bits = max(1, int(expression_smt_bit_width(expr) or 1))
    summary_ref = _state_transition_loop_count_ref(expr)
    if summary_ref is None:
        return f"rt_state_transition_loop_count_{state_bits}_{result_bits}"
    identity = _runtime_ref_smt_identity(expr, summary_ref)
    digest = hashlib.sha1(repr(identity).encode("utf-8")).hexdigest()[:16]
    return f"rt_state_transition_loop_count_{digest}_{state_bits}_{result_bits}"


def _counted_loop_sum_function_name(expr) -> str:
    operands = getattr(expr, "operands", None) or []
    base_bits = expression_smt_bit_width(operands[0]) if len(operands) >= 1 else 0
    start_bits = expression_smt_bit_width(operands[1]) if len(operands) >= 2 else 0
    limit_bits = expression_smt_bit_width(operands[2]) if len(operands) >= 3 else 0
    result_bits = max(1, int(expression_smt_bit_width(expr) or 1))
    summary_ref = _counted_loop_sum_ref(expr)
    if summary_ref is None:
        return f"rt_counted_loop_sum_{base_bits}_{start_bits}_{limit_bits}_{result_bits}"
    identity = _runtime_ref_smt_identity(expr, summary_ref)
    digest = hashlib.sha1(repr(identity).encode("utf-8")).hexdigest()[:16]
    return (
        f"rt_counted_loop_sum_{digest}_"
        f"{base_bits}_{start_bits}_{limit_bits}_{result_bits}"
    )


def _counted_loop_sum_has_exact_lowering(expr) -> bool:
    operands = getattr(expr, "operands", None) or []
    if len(operands) != 3:
        return False
    summary_ref = _counted_loop_sum_ref(expr)
    if summary_ref is None:
        return False
    induction_step = int(getattr(summary_ref, "induction_step", 0) or 0)
    residue_cases = tuple(getattr(summary_ref, "residue_cases", ()) or ())
    if induction_step == 0 or not residue_cases:
        return False
    if induction_step != 1:
        return all(int(modulus) == 1 for modulus, _residue, _coeff, _bias in residue_cases)
    for modulus, _residue, _coeff, _bias in residue_cases:
        modulus = int(modulus)
        if modulus <= 1:
            continue
        mask = modulus - 1
        if mask <= 0 or (mask & (mask + 1)) != 0:
            return False
    return True


def _smt_bv_const(value: int, bits: int) -> str:
    mask = (1 << bits) - 1
    return f"(_ bv{int(value) & mask} {bits})"


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


def _counted_loop_sum_exact_smt(
    expr,
    *,
    base_smt: str,
    start_smt: str,
    limit_smt: str,
    base_bits: int,
    start_bits: int,
    limit_bits: int,
    result_bits: int,
) -> Optional[str]:
    summary_ref = _counted_loop_sum_ref(expr)
    if summary_ref is None:
        return None

    induction_step = int(getattr(summary_ref, "induction_step", 0) or 0)
    residue_cases = tuple(getattr(summary_ref, "residue_cases", ()) or ())
    if induction_step == 0 or not residue_cases:
        return None

    signed_loop = bool(getattr(summary_ref, "signed_loop", False))
    wide_bits = max(64, result_bits * 2, base_bits, start_bits, limit_bits)
    wide_base = _smt_extend_to_width(expr.operands[0], base_smt, wide_bits, signed=signed_loop)
    wide_start = _smt_extend_to_width(expr.operands[1], start_smt, wide_bits, signed=signed_loop)
    wide_limit = _smt_extend_to_width(expr.operands[2], limit_smt, wide_bits, signed=signed_loop)
    zero = _smt_bv_const(0, wide_bits)
    one = _smt_bv_const(1, wide_bits)

    def _triangular(value_smt: str) -> str:
        incremented = f"(bvadd {value_smt} {one})"
        product = f"(bvmul {value_smt} {incremented})"
        return f"(bvlshr {product} {one})"

    def _exact_progression_sum(first_smt: str, count_smt: str, *, step: int) -> str:
        count_minus_one = f"(bvsub {count_smt} {one})"
        triangular = _triangular(count_minus_one)
        stride_term = _smt_scale_term(triangular, step, wide_bits)
        leading_term = f"(bvmul {count_smt} {first_smt})"
        total_nonzero = leading_term
        if stride_term is not None:
            total_nonzero = f"(bvadd {leading_term} {stride_term})"
        return f"(ite (= {count_smt} {zero}) {zero} {total_nonzero})"

    def _loop_le(left_smt: str, right_smt: str) -> str:
        operator = "bvsle" if signed_loop else "bvule"
        return f"({operator} {left_smt} {right_smt})"

    def _distance_le(left_smt: str, right_smt: str) -> str:
        return f"(bvule {left_smt} {right_smt})"

    def _ceil_div_positive(value_smt: str, divisor: int) -> str:
        divisor = int(divisor)
        if divisor <= 1:
            return value_smt
        decremented = f"(bvsub {value_smt} {one})"
        if divisor & (divisor - 1) == 0:
            shift_amount = _smt_bv_const(divisor.bit_length() - 1, wide_bits)
            quotient = f"(bvlshr {decremented} {shift_amount})"
        else:
            quotient = f"(bvudiv {decremented} {_smt_bv_const(divisor, wide_bits)})"
        return f"(bvadd {quotient} {one})"

    if induction_step == 1:
        n_expr = f"(bvsub {wide_limit} {wide_start})"
        no_iteration = _loop_le(wide_limit, wide_start)
        count_all_expr = f"(ite {no_iteration} {zero} {n_expr})"
        total = wide_base
        for modulus, residue, coeff, bias in residue_cases:
            modulus = int(modulus)
            residue = int(residue)
            coeff = int(coeff)
            bias = int(bias)
            if modulus <= 1:
                count_expr = count_all_expr
                offset_expr = zero
            else:
                mask = modulus - 1
                if mask <= 0 or (mask & (mask + 1)) != 0:
                    return None
                mask_smt = _smt_bv_const(mask, wide_bits)
                residue_smt = _smt_bv_const(residue, wide_bits)
                start_low = f"(bvand {wide_start} {mask_smt})"
                raw_offset = f"(bvsub {residue_smt} {start_low})"
                offset_expr = f"(bvand {raw_offset} {mask_smt})"
                positive_span = f"(bvsub {n_expr} {offset_expr})"
                no_matching_residue = f"(or {no_iteration} {_distance_le(n_expr, offset_expr)})"
                count_nonzero = _ceil_div_positive(positive_span, modulus)
                count_expr = f"(ite {no_matching_residue} {zero} {count_nonzero})"
            first_expr = f"(bvadd {wide_start} {offset_expr})"
            progression_sum = _exact_progression_sum(first_expr, count_expr, step=modulus)
            coeff_term = _smt_scale_term(progression_sum, coeff, wide_bits)
            bias_term = _smt_scale_term(count_expr, bias, wide_bits)
            for term in (coeff_term, bias_term):
                if term is not None:
                    total = f"(bvadd {total} {term})"
        return _smt_low_bits(total, wide_bits, result_bits)

    if any(int(modulus) != 1 for modulus, _residue, _coeff, _bias in residue_cases):
        return None

    if induction_step > 0:
        span_expr = f"(bvsub {wide_limit} {wide_start})"
        no_iteration = _loop_le(wide_limit, wide_start)
    else:
        span_expr = f"(bvsub {wide_start} {wide_limit})"
        no_iteration = _loop_le(wide_start, wide_limit)
    count_nonzero = span_expr
    step_magnitude = abs(induction_step)
    if step_magnitude != 1:
        count_nonzero = _ceil_div_positive(span_expr, step_magnitude)
    count_expr = f"(ite {no_iteration} {zero} {count_nonzero})"
    progression_sum = _exact_progression_sum(wide_start, count_expr, step=induction_step)
    total = wide_base
    for _modulus, _residue, coeff, bias in residue_cases:
        coeff_term = _smt_scale_term(progression_sum, int(coeff), wide_bits)
        bias_term = _smt_scale_term(count_expr, int(bias), wide_bits)
        for term in (coeff_term, bias_term):
            if term is not None:
                total = f"(bvadd {total} {term})"
    return _smt_low_bits(total, wide_bits, result_bits)


def _intrinsic_smt_declaration(expr) -> Optional[str]:
    opcode = getattr(expr, "opcode", None)
    mnemonic = getattr(expr, "name", None) or ""
    operands = getattr(expr, "operands", None) or []

    if opcode == READONLY_SUM_OPCODE or mnemonic == "READONLY_SUM":
        if len(operands) != 2:
            raise ValueError(f"READONLY_SUM expects 2 operands, got {len(operands)}")
        base_bits = max(1, int(expression_smt_bit_width(operands[0]) or 1))
        count_bits = max(1, int(expression_smt_bit_width(operands[1]) or 1))
        result_bits = max(1, int(expression_smt_bit_width(expr) or 1))
        return (
            f"(declare-fun {_readonly_sum_function_name(expr)} "
            f"((_ BitVec {base_bits}) (_ BitVec {count_bits})) "
            f"(_ BitVec {result_bits}))"
        )

    if opcode == COUNTED_LOOP_SUM_OPCODE or mnemonic == "COUNTED_LOOP_SUM":
        if _counted_loop_sum_has_exact_lowering(expr):
            return None
        if len(operands) != 3:
            raise ValueError(f"COUNTED_LOOP_SUM expects 3 operands, got {len(operands)}")
        base_bits = max(1, int(expression_smt_bit_width(operands[0]) or 1))
        start_bits = max(1, int(expression_smt_bit_width(operands[1]) or 1))
        limit_bits = max(1, int(expression_smt_bit_width(operands[2]) or 1))
        result_bits = max(1, int(expression_smt_bit_width(expr) or 1))
        return (
            f"(declare-fun {_counted_loop_sum_function_name(expr)} "
            f"((_ BitVec {base_bits}) (_ BitVec {start_bits}) (_ BitVec {limit_bits})) "
            f"(_ BitVec {result_bits}))"
        )

    if opcode == STATE_TRANSITION_LOOP_COUNT_OPCODE or mnemonic == "STATE_TRANSITION_LOOP_COUNT":
        if len(operands) != 1:
            raise ValueError(f"STATE_TRANSITION_LOOP_COUNT expects 1 operand, got {len(operands)}")
        state_bits = max(1, int(expression_smt_bit_width(operands[0]) or 1))
        result_bits = max(1, int(expression_smt_bit_width(expr) or 1))
        return (
            f"(declare-fun {_state_transition_loop_count_function_name(expr)} "
            f"((_ BitVec {state_bits})) "
            f"(_ BitVec {result_bits}))"
        )

    return None


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
            float_mode=float_mode,
        )

    if expr_type == expr_kind.BINARY_OP:
        left = expr.operands[0]
        right = expr.operands[1]

        if expr.operator == "PIECE":
            left_bits = expression_smt_bit_width(left)
            right_bits = expression_smt_bit_width(right)
            concat_smt = (
                f"(concat "
                f"{_to_smt_internal(left, prefer_signed_arithmetic, symbol_name_mapping, address_context, float_mode)} "
                f"{_to_smt_internal(right, prefer_signed_arithmetic, symbol_name_mapping, address_context, float_mode)})"
            )
            return _coerce_smt_bitvec_width(
                concat_smt,
                left_bits + right_bits,
                expression_smt_bit_width(expr) or (left_bits + right_bits),
            )

        if expr.operator == "SUBPIECE":
            source_smt = _to_smt_internal(
                left,
                prefer_signed_arithmetic,
                symbol_name_mapping,
                address_context,
                float_mode,
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
                f"{_to_smt_internal(right, prefer_signed_arithmetic, symbol_name_mapping, address_context, float_mode)})"
            )

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
    float_mode: str = "uf",
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
            float_mode,
        )
        index_smt = _to_smt_internal(
            index,
            prefer_signed_arithmetic,
            symbol_name_mapping,
            address_context,
            float_mode,
        )
        elem_smt = _to_smt_internal(
            element_size,
            prefer_signed_arithmetic,
            symbol_name_mapping,
            address_context,
            float_mode,
        )
        target_bits = max(
            result_bits,
            expression_smt_bit_width(base),
            expression_smt_bit_width(index),
            expression_smt_bit_width(element_size),
            1,
        )
        base_smt = _coerce_expr_to_bitvec_width(base, base_smt, target_bits, float_mode=float_mode)
        index_smt = _coerce_expr_to_bitvec_width(index, index_smt, target_bits, float_mode=float_mode)
        elem_smt = _coerce_expr_to_bitvec_width(element_size, elem_smt, target_bits, float_mode=float_mode)
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
            float_mode,
        )
        offset_smt = _to_smt_internal(
            offset,
            prefer_signed_arithmetic,
            symbol_name_mapping,
            address_context,
            float_mode,
        )
        target_bits = max(
            result_bits,
            expression_smt_bit_width(base),
            expression_smt_bit_width(offset),
            1,
        )
        base_smt = _coerce_expr_to_bitvec_width(base, base_smt, target_bits, float_mode=float_mode)
        offset_smt = _coerce_expr_to_bitvec_width(offset, offset_smt, target_bits, float_mode=float_mode)
        return f"(bvadd {base_smt} {offset_smt})"

    if opcode == READONLY_SUM_OPCODE or mnemonic == "READONLY_SUM":
        if len(operands) != 2:
            raise ValueError(f"READONLY_SUM expects 2 operands, got {len(operands)}")
        base, count = operands
        base_bits = max(1, int(expression_smt_bit_width(base) or 1))
        count_bits = max(1, int(expression_smt_bit_width(count) or 1))
        base_smt = _to_smt_internal(
            base,
            prefer_signed_arithmetic,
            symbol_name_mapping,
            True,
            float_mode,
        )
        count_smt = _to_smt_internal(
            count,
            prefer_signed_arithmetic,
            symbol_name_mapping,
            address_context,
            float_mode,
        )
        base_smt = _coerce_expr_to_bitvec_width(base, base_smt, base_bits, float_mode=float_mode)
        count_smt = _coerce_expr_to_bitvec_width(
            count,
            count_smt,
            count_bits,
            prefer_sign_extension=_expr_prefers_signed_extension(count),
            float_mode=float_mode,
        )
        return f"({_readonly_sum_function_name(expr)} {base_smt} {count_smt})"

    if opcode == COUNTED_LOOP_SUM_OPCODE or mnemonic == "COUNTED_LOOP_SUM":
        if len(operands) != 3:
            raise ValueError(f"COUNTED_LOOP_SUM expects 3 operands, got {len(operands)}")
        base, start, limit = operands
        base_bits = max(1, int(expression_smt_bit_width(base) or 1))
        start_bits = max(1, int(expression_smt_bit_width(start) or 1))
        limit_bits = max(1, int(expression_smt_bit_width(limit) or 1))
        base_smt = _to_smt_internal(
            base,
            prefer_signed_arithmetic,
            symbol_name_mapping,
            address_context,
            float_mode,
        )
        start_smt = _to_smt_internal(
            start,
            prefer_signed_arithmetic,
            symbol_name_mapping,
            address_context,
            float_mode,
        )
        limit_smt = _to_smt_internal(
            limit,
            prefer_signed_arithmetic,
            symbol_name_mapping,
            address_context,
            float_mode,
        )
        base_smt = _coerce_expr_to_bitvec_width(base, base_smt, base_bits, float_mode=float_mode)
        start_smt = _coerce_expr_to_bitvec_width(
            start,
            start_smt,
            start_bits,
            prefer_sign_extension=_expr_prefers_signed_extension(start),
            float_mode=float_mode,
        )
        limit_smt = _coerce_expr_to_bitvec_width(
            limit,
            limit_smt,
            limit_bits,
            prefer_sign_extension=_expr_prefers_signed_extension(limit),
            float_mode=float_mode,
        )
        exact_smt = _counted_loop_sum_exact_smt(
            expr,
            base_smt=base_smt,
            start_smt=start_smt,
            limit_smt=limit_smt,
            base_bits=base_bits,
            start_bits=start_bits,
            limit_bits=limit_bits,
            result_bits=max(1, int(expression_smt_bit_width(expr) or 1)),
        )
        if exact_smt is not None:
            return exact_smt
        return f"({_counted_loop_sum_function_name(expr)} {base_smt} {start_smt} {limit_smt})"

    if opcode == STATE_TRANSITION_LOOP_COUNT_OPCODE or mnemonic == "STATE_TRANSITION_LOOP_COUNT":
        if len(operands) != 1:
            raise ValueError(f"STATE_TRANSITION_LOOP_COUNT expects 1 operand, got {len(operands)}")
        state = operands[0]
        state_bits = max(1, int(expression_smt_bit_width(state) or 1))
        state_smt = _to_smt_internal(
            state,
            prefer_signed_arithmetic,
            symbol_name_mapping,
            address_context,
            float_mode,
        )
        state_smt = _coerce_expr_to_bitvec_width(
            state,
            state_smt,
            state_bits,
            prefer_sign_extension=_expr_prefers_signed_extension(state),
            float_mode=float_mode,
        )
        return f"({_state_transition_loop_count_function_name(expr)} {state_smt})"

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
