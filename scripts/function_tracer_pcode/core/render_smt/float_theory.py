"""Floating-point predicate / arithmetic rendering and FP-theory detection."""

from __future__ import annotations

from typing import List, Optional


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
        elif node.expr_type == expr_kind.UNARY_OP and getattr(node, "operator", None) == "INT2FLOAT":
            operands = getattr(node, "operands", None) or []
            if (
                len(operands) == 1
                and int(expression_smt_bit_width(operands[0]) or 0) > 0
                and int(expression_smt_bit_width(node) or 0) in _FLOAT_BV_WIDTH_TO_SORT
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
    if expr_type == expr_kind.UNARY_OP and getattr(expr, "operator", None) == "INT2FLOAT":
        operands = getattr(expr, "operands", None) or []
        return (
            len(operands) == 1
            and int(expression_smt_bit_width(operands[0]) or 0) > 0
            and int(expression_smt_bit_width(expr) or 0) in _FLOAT_BV_WIDTH_TO_SORT
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
    if (
        fp_op is not None
        and float_mode == "fp"
        and (
            _is_float_rendered_expr(left_expr)
            or _is_float_rendered_expr(right_expr)
        )
        and not (
            left_bits == right_bits == result_bits
            and result_bits in _FLOAT_BV_WIDTH_TO_SORT
        )
    ):
        raise UnsupportedSmtOperatorError(
            operator=operator,
            reason="floating-point operand/result precisions do not match",
            operand_bits=max(left_bits, right_bits),
            result_bits=result_bits,
        )
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


# Sibling modules reference each other at call time; import them last to avoid cycles.
from scripts.function_tracer_pcode.core.render_smt.render import (
    UnsupportedSmtOperatorError,
    _FLOAT_ARITHMETIC_FP_SPECS,
    _FLOAT_ARITHMETIC_SMT_NAMES,
    _FLOAT_BV_WIDTH_TO_SORT,
    _FLOAT_PREDICATE_SMT_NAMES,
    expression_returns_bool,
)
from scripts.function_tracer_pcode.core.render_smt.unknowns import (
    _iter_expression_nodes,
)
from scripts.function_tracer_pcode.core.render_smt.widths import (
    _expr_is_known_nan_or_inf_bitpattern,
    _expr_is_known_zero_bitpattern,
    expression_smt_bit_width,
)
