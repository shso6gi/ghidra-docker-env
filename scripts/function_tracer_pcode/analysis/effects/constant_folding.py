"""Constant evaluation, program-memory reads and known-address truth."""

from __future__ import annotations

from typing import Dict, List, Optional, Sequence, Tuple
from scripts.function_tracer_pcode.core import (
    AddressValueRef,
    Condition,
    Expression,
    ExpressionType,
)
from scripts.function_tracer_pcode.analysis.effects._shared import (
    ConditionSimplifier,
)
from scripts.function_tracer_pcode.analysis.effects._api import (
    _apply_binary_constant_op,
    _apply_unary_constant_op,
    _coerce_storage_info,
    _enumerate_constant_expression_branches,
    _evaluate_constant_expression,
    _is_known_nonnull_stack_address,
    _is_zero_constant,
    _mask_to_expr_width,
    _sign_extend_value,
    canonicalize_location,
)


def _impl__enumerate_constant_expression_branches(
    expr: Optional[Expression],
) -> List[Tuple[List[Condition], int]]:
    if expr is None:
        return []

    if expr.expr_type == ExpressionType.PHI and expr.value:
        resolved: List[Tuple[List[Condition], int]] = []
        for cond, value in expr.value:
            for branch_conditions, branch_value in _enumerate_constant_expression_branches(value):
                merged = list(branch_conditions)
                if cond is not None:
                    merged.insert(0, cond)
                resolved.append((merged, branch_value))
        return resolved

    if expr.expr_type == ExpressionType.UNARY_OP and expr.operands:
        operand_branches = _enumerate_constant_expression_branches(expr.operands[0])
        if operand_branches:
            resolved: List[Tuple[List[Condition], int]] = []
            for branch_conditions, operand_value in operand_branches:
                applied = _apply_unary_constant_op(expr, operand_value)
                if applied is None:
                    continue
                resolved.append((list(branch_conditions), applied))
            if resolved:
                return resolved

    if expr.expr_type == ExpressionType.BINARY_OP and len(expr.operands) == 2:
        left_branches = _enumerate_constant_expression_branches(expr.operands[0])
        right_branches = _enumerate_constant_expression_branches(expr.operands[1])
        if left_branches and right_branches:
            resolved: List[Tuple[List[Condition], int]] = []
            for left_conditions, left_value in left_branches:
                for right_conditions, right_value in right_branches:
                    applied = _apply_binary_constant_op(expr, left_value, right_value)
                    if applied is None:
                        continue
                    resolved.append((list(left_conditions) + list(right_conditions), applied))
            if resolved:
                return resolved

    const_value = _evaluate_constant_expression(expr)
    if const_value is None:
        return []
    return [([], const_value)]


def _impl__evaluate_constant_expression(expr: Optional[Expression]) -> Optional[int]:
    if expr is None:
        return None

    if expr.expr_type == ExpressionType.CONSTANT and isinstance(expr.value, int):
        return int(expr.value)

    if expr.expr_type == ExpressionType.VARIABLE:
        runtime_ref = getattr(expr, "runtime_ref", None)
        if isinstance(runtime_ref, AddressValueRef):
            return int(runtime_ref.address_offset)

    if expr.expr_type == ExpressionType.UNARY_OP and expr.operands:
        operand_value = _evaluate_constant_expression(expr.operands[0])
        if operand_value is None:
            return None
        target_bits = max(8, (expr.size or expr.operands[0].size or 8) * 8)
        if expr.operator in {"CAST", "COPY", "INT_ZEXT"}:
            return operand_value & ((1 << target_bits) - 1)
        if expr.operator == "INT_SEXT":
            return _sign_extend_value(operand_value, expr.operands[0].get_bit_width(), target_bits)
        if expr.operator == "SUBPIECE" and len(expr.operands) >= 2:
            offset_value = _evaluate_constant_expression(expr.operands[1])
            if offset_value is None:
                return None
            shifted = operand_value >> (int(offset_value) * 8)
            return shifted & ((1 << target_bits) - 1)
        return None

    if expr.expr_type == ExpressionType.INTRINSIC:
        intrinsic_name = getattr(expr, "name", None) or ""
        operand_values = [_evaluate_constant_expression(operand) for operand in (expr.operands or [])]
        if any(value is None for value in operand_values):
            return None
        resolved_values = [int(value) for value in operand_values if value is not None]

        if intrinsic_name in {"PTRSUB", "INT_ADD"} and len(resolved_values) >= 2:
            return _mask_to_expr_width(expr, resolved_values[0] + resolved_values[1])
        if intrinsic_name == "PTRADD":
            if len(resolved_values) >= 3:
                return _mask_to_expr_width(
                    expr,
                    resolved_values[0] + (resolved_values[1] * resolved_values[2]),
                )
            if len(resolved_values) >= 2:
                return _mask_to_expr_width(expr, resolved_values[0] + resolved_values[1])
        if intrinsic_name in {"CAST", "COPY", "INT_ZEXT"} and resolved_values:
            target_bits = max(8, (expr.size or expr.operands[0].size or 8) * 8)
            return resolved_values[0] & ((1 << target_bits) - 1)
        if intrinsic_name == "INT_SEXT" and resolved_values:
            target_bits = max(8, (expr.size or expr.operands[0].size or 8) * 8)
            return _sign_extend_value(
                resolved_values[0],
                expr.operands[0].get_bit_width(),
                target_bits,
            )
        return None

    if expr.expr_type == ExpressionType.BINARY_OP and len(expr.operands) == 2:
        left_value = _evaluate_constant_expression(expr.operands[0])
        right_value = _evaluate_constant_expression(expr.operands[1])
        if left_value is None or right_value is None:
            return None

        if expr.operator == "SUBPIECE":
            if right_value < 0:
                return None
            target_bits = max(8, (expr.size or expr.operands[0].size or 8) * 8)
            shifted = left_value >> (int(right_value) * 8)
            return shifted & ((1 << target_bits) - 1)
        if expr.operator in {"INT_ADD", "PTRSUB", "PTRADD"}:
            return _mask_to_expr_width(expr, left_value + right_value)
        if expr.operator == "INT_SUB":
            return _mask_to_expr_width(expr, left_value - right_value)
        if expr.operator == "INT_MULT":
            return _mask_to_expr_width(expr, left_value * right_value)
        if expr.operator == "INT_AND":
            return _mask_to_expr_width(expr, left_value & right_value)
        if expr.operator == "INT_OR":
            return _mask_to_expr_width(expr, left_value | right_value)
        if expr.operator == "INT_XOR":
            return _mask_to_expr_width(expr, left_value ^ right_value)
        if expr.operator == "PIECE":
            low_bits = expr.operands[1].get_bit_width()
            return _mask_to_expr_width(
                expr,
                (left_value << low_bits) | (right_value & ((1 << low_bits) - 1)),
            )
        return None

    return None


def _impl__apply_unary_constant_op(expr: Expression, operand_value: int) -> Optional[int]:
    target_bits = max(8, (expr.size or expr.operands[0].size or 8) * 8)
    if expr.operator in {"CAST", "COPY", "INT_ZEXT"}:
        return operand_value & ((1 << target_bits) - 1)
    if expr.operator == "INT_SEXT":
        return _sign_extend_value(operand_value, expr.operands[0].get_bit_width(), target_bits)
    return None


def _impl__apply_binary_constant_op(expr: Expression, left_value: int, right_value: int) -> Optional[int]:
    if expr.operator == "SUBPIECE":
        if right_value < 0:
            return None
        target_bits = max(8, (expr.size or expr.operands[0].size or 8) * 8)
        shifted = left_value >> (int(right_value) * 8)
        return shifted & ((1 << target_bits) - 1)
    if expr.operator in {"INT_ADD", "PTRSUB", "PTRADD"}:
        return _mask_to_expr_width(expr, left_value + right_value)
    if expr.operator == "INT_SUB":
        return _mask_to_expr_width(expr, left_value - right_value)
    if expr.operator == "INT_MULT":
        return _mask_to_expr_width(expr, left_value * right_value)
    if expr.operator == "INT_AND":
        return _mask_to_expr_width(expr, left_value & right_value)
    if expr.operator == "INT_OR":
        return _mask_to_expr_width(expr, left_value | right_value)
    if expr.operator == "INT_XOR":
        return _mask_to_expr_width(expr, left_value ^ right_value)
    if expr.operator == "PIECE":
        low_bits = expr.operands[1].get_bit_width()
        return _mask_to_expr_width(
            expr,
            (left_value << low_bits) | (right_value & ((1 << low_bits) - 1)),
        )
    return None


def _impl__sign_extend_value(value: int, source_bits: int, target_bits: int) -> int:
    source_bits = max(1, int(source_bits))
    target_bits = max(source_bits, int(target_bits))
    mask = (1 << source_bits) - 1
    value &= mask
    sign_bit = 1 << (source_bits - 1)
    if value & sign_bit:
        value -= 1 << source_bits
    return value & ((1 << target_bits) - 1)


def _impl__read_program_memory_value(
    tracer,
    address_value: int,
    size_bytes: int,
    *,
    purpose: Optional[str] = None,
) -> Optional[int]:
    """image の値（Issue #282, Q1: `analysis.program_image` が具体化してよいときだけ）。"""

    from scripts.function_tracer_pcode.analysis.program_image import DATA_VALUE, read_image_value

    if tracer is None or getattr(tracer, "program", None) is None:
        return None
    return read_image_value(tracer.program, address_value, size_bytes, purpose=purpose or DATA_VALUE)


def _impl__expression_truth_value(expr: Optional[Expression]) -> Optional[bool]:
    if expr is None:
        return None
    return ConditionSimplifier.evaluate_condition_truth(Condition(expr, False))


def _impl__known_nonnull_address_comparison_truth(
    operator: str,
    left: Expression,
    right: Expression,
    parameters: Optional[Sequence[Dict]],
) -> Optional[bool]:
    if operator not in {"INT_EQUAL", "INT_NOTEQUAL"}:
        return None
    if not parameters:
        parameters = []

    if _is_zero_constant(left) and _is_known_nonnull_stack_address(right, parameters):
        return operator == "INT_NOTEQUAL"
    if _is_zero_constant(right) and _is_known_nonnull_stack_address(left, parameters):
        return operator == "INT_NOTEQUAL"
    return None


def _impl__is_zero_constant(expr: Optional[Expression]) -> bool:
    return (
        expr is not None
        and expr.expr_type == ExpressionType.CONSTANT
        and isinstance(expr.value, int)
        and int(expr.value) == 0
    )


def _impl__is_known_nonnull_stack_address(
    expr: Optional[Expression],
    parameters: Sequence[Dict],
) -> bool:
    if expr is None:
        return False
    size = max(1, int(getattr(expr, "size", 0) or 0), 1)
    location = canonicalize_location(expr, parameters, size=size)
    if location is None:
        return False
    return location.base_ref.is_stack_frame()


def _impl__is_stack_frame_base_expression(expr: Optional[Expression]) -> bool:
    if expr is None:
        return False

    # entry SP を起点とする番地の基底は、SP の register の **入口の値** だけ（Issue #282, I11）。frame pointer の
    # register は名前だけでは frame ではない（frame pointer を設定しない関数では callee-saved の汎用 register で、
    # 入口の値は caller の値）。入口の値かどうかは `parameter_entry.is_register_entry_variable` が決める
    from scripts.function_tracer_pcode.analysis.effects.parameter_entry import is_register_entry_variable

    expr_storage = _coerce_storage_info(getattr(expr, "storage_info", None))
    if expr_storage is None or not bool(expr_storage.is_stack_pointer):
        return False
    return is_register_entry_variable(expr)


def _impl__constant_factor(expr: Expression) -> Optional[int]:
    value = _evaluate_constant_expression(expr)
    if value is None:
        return None
    return int(value)
