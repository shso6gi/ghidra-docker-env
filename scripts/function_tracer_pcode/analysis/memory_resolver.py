# -*- coding: utf-8 -*-
"""Helpers for concretizing simple read-only memory loads."""

from __future__ import annotations

import re
from dataclasses import dataclass
from typing import Callable, Dict, List, Optional, Sequence, Tuple

from ..model import Condition, Expression, ExpressionType


MAX_ENUMERATED_INDEX_VALUES = 16


@dataclass
class IndexedAddressPattern:
    """A small subset of address expressions: base + offset + index * scale."""

    base_address: int
    scale: int
    index_expr: Expression
    index_param_name: str
    index_bits: int
    const_offset: int = 0


def collect_memory_bit_widths_from_analysis(analysis) -> List[int]:
    """Return sorted memory load widths (in bits) used by an analysis result."""
    widths = set()
    for ret_info in getattr(analysis, "returns", []) or []:
        _collect_memory_bit_widths_from_expr(ret_info.value, widths)
        for cond in ret_info.conditions or []:
            _collect_memory_bit_widths_from_expr(cond.expression, widths)
    return sorted(widths)


def _collect_memory_bit_widths_from_expr(expr: Optional[Expression], widths: set) -> None:
    """Recursively collect bit widths of MEMORY expressions."""
    if expr is None:
        return

    if expr.expr_type == ExpressionType.MEMORY:
        widths.add(expr.get_bit_width())

    for operand in getattr(expr, "operands", ()) or ():
        _collect_memory_bit_widths_from_expr(operand, widths)

    if expr.expr_type == ExpressionType.PHI and expr.value:
        for cond, value in expr.value:
            if cond is not None and hasattr(cond, "expression"):
                _collect_memory_bit_widths_from_expr(cond.expression, widths)
            _collect_memory_bit_widths_from_expr(value, widths)


def concretize_readonly_loads(
    expr: Expression,
    conditions: Sequence[Condition],
    parameters: Sequence[Dict],
    read_memory_value: Callable[[int, int], Optional[int]],
    debug: bool = False,
) -> Expression:
    """Replace simple read-only indexed loads with a finite PHI/ITE over constants."""
    return _rewrite_expr(expr, list(conditions or []), list(parameters or []), read_memory_value, debug)


def _rewrite_expr(
    expr: Expression,
    conditions: List[Condition],
    parameters: List[Dict],
    read_memory_value: Callable[[int, int], Optional[int]],
    debug: bool,
) -> Expression:
    if expr is None:
        return expr

    if expr.expr_type == ExpressionType.MEMORY and expr.operands:
        rewritten_addr = _rewrite_expr(expr.operands[0], conditions, parameters, read_memory_value, debug)
        candidate = Expression.memory(rewritten_addr, expr.size)
        resolved = _try_resolve_readonly_load(
            candidate,
            conditions,
            parameters,
            read_memory_value,
            debug,
        )
        return resolved or candidate

    if expr.expr_type in (ExpressionType.BINARY_OP, ExpressionType.UNARY_OP, ExpressionType.CALL):
        rewritten_operands = [
            _rewrite_expr(op, conditions, parameters, read_memory_value, debug)
            for op in expr.operands
        ]
        if all(new is old for new, old in zip(rewritten_operands, expr.operands)):
            return expr
        rebuilt = Expression(
            expr_type=expr.expr_type,
            value=expr.value,
            operator=expr.operator,
            operands=rewritten_operands,
            size=expr.size,
            name=expr.name,
            data_type=expr.data_type,
            storage_info=expr.storage_info,
        )
        return rebuilt

    if expr.expr_type == ExpressionType.PHI and expr.value:
        rewritten_branches = []
        changed = False
        for cond, value in expr.value:
            new_value = _rewrite_expr(value, conditions, parameters, read_memory_value, debug)
            rewritten_branches.append((cond, new_value))
            changed = changed or (new_value is not value)
        if not changed:
            return expr
        rebuilt = Expression.phi(rewritten_branches)
        rebuilt.size = expr.size
        return rebuilt

    return expr


def _try_resolve_readonly_load(
    expr: Expression,
    conditions: List[Condition],
    parameters: List[Dict],
    read_memory_value: Callable[[int, int], Optional[int]],
    debug: bool,
) -> Optional[Expression]:
    if expr.expr_type != ExpressionType.MEMORY or not expr.operands:
        return None

    pattern = _extract_indexed_pattern(expr.operands[0])
    if pattern is None:
        return None

    param_info = _get_parameter_info(parameters, pattern.index_param_name)
    if param_info is None:
        return None

    candidate_indices = _enumerate_candidate_indices(pattern, conditions, param_info, debug)
    if not candidate_indices:
        return None

    branches = []
    index_size_bytes = max(1, pattern.index_bits // 8)
    load_size = expr.size if expr.size else 4
    fallback = expr

    for index_value in candidate_indices:
        addr = pattern.base_address + pattern.const_offset + pattern.scale * index_value
        mem_value = read_memory_value(addr, load_size)
        if mem_value is None:
            return None
        cond_expr = Expression.binary_op(
            "INT_EQUAL",
            pattern.index_expr,
            Expression.constant(index_value, index_size_bytes),
        )
        branches.append((Condition(cond_expr, False), Expression.constant(mem_value, load_size)))
        if debug:
            print(
                "[MemoryResolver] concretized load "
                f"addr=0x{addr:x} size={load_size} index={index_value} -> 0x{mem_value:x}"
            )

    branches.append((None, fallback))
    resolved = Expression.phi(branches)
    resolved.size = expr.size
    return resolved


def _extract_indexed_pattern(addr_expr: Expression) -> Optional[IndexedAddressPattern]:
    flattened = _flatten_additive_terms(addr_expr)
    if flattened is None:
        return None

    const_total, scaled_terms = flattened
    if len(scaled_terms) != 1:
        return None

    index_expr, scale = scaled_terms[0]
    param_name, index_bits = _extract_index_param(index_expr)
    if not param_name or index_bits <= 0:
        return None

    return IndexedAddressPattern(
        base_address=const_total,
        const_offset=0,
        scale=scale,
        index_expr=index_expr,
        index_param_name=param_name,
        index_bits=index_bits,
    )


def _flatten_additive_terms(expr: Expression) -> Optional[Tuple[int, List[Tuple[Expression, int]]]]:
    if expr.expr_type == ExpressionType.BINARY_OP and expr.operator == "INT_ADD" and len(expr.operands) == 2:
        left_flat = _flatten_additive_terms(expr.operands[0])
        right_flat = _flatten_additive_terms(expr.operands[1])
        if left_flat is None or right_flat is None:
            return None
        left_const, left_terms = left_flat
        right_const, right_terms = right_flat
        return left_const + right_const, left_terms + right_terms

    const_value = _extract_constant_address(expr)
    if const_value is not None:
        return const_value, []

    scaled = _extract_scaled_index(expr)
    if scaled is not None:
        return 0, [scaled]

    return None


def _extract_constant_address(expr: Expression) -> Optional[int]:
    if expr.expr_type == ExpressionType.CONSTANT and isinstance(expr.value, int):
        return expr.value

    if expr.expr_type == ExpressionType.VARIABLE and expr.name:
        for prefix in ("PTR_", "DAT_", "LAB_"):
            if expr.name.startswith(prefix):
                suffix = expr.name[len(prefix):]
                if re.fullmatch(r"[0-9A-Fa-f]+", suffix):
                    return int(suffix, 16)
    return None


def _extract_scaled_index(expr: Expression) -> Optional[Tuple[Expression, int]]:
    param_name, _ = _extract_index_param(expr)
    if param_name:
        return expr, 1

    if expr.expr_type != ExpressionType.BINARY_OP or expr.operator != "INT_MULT" or len(expr.operands) != 2:
        return None

    left, right = expr.operands

    if right.expr_type == ExpressionType.CONSTANT and isinstance(right.value, int):
        inner = _extract_scaled_index(left)
        if inner is not None:
            inner_expr, inner_scale = inner
            return inner_expr, inner_scale * right.value

    if left.expr_type == ExpressionType.CONSTANT and isinstance(left.value, int):
        inner = _extract_scaled_index(right)
        if inner is not None:
            inner_expr, inner_scale = inner
            return inner_expr, inner_scale * left.value

    return None


def _extract_index_param(expr: Expression) -> Tuple[Optional[str], int]:
    if expr.expr_type == ExpressionType.PARAMETER and expr.name:
        return expr.name, expr.get_bit_width()

    if expr.expr_type == ExpressionType.UNARY_OP and expr.operator in {"INT_SEXT", "INT_ZEXT"} and expr.operands:
        return _extract_index_param(expr.operands[0])

    if expr.expr_type == ExpressionType.BINARY_OP:
        if expr.operator == "SUBPIECE" and len(expr.operands) == 2:
            source, offset = expr.operands
            if offset.expr_type == ExpressionType.CONSTANT and offset.value == 0:
                name, _ = _extract_index_param(source)
                return name, expr.get_bit_width()

        if expr.operator == "INT_AND" and len(expr.operands) == 2:
            left, right = expr.operands
            if right.expr_type == ExpressionType.CONSTANT and right.value == 0xFFFFFFFF:
                name, _ = _extract_index_param(left)
                return name, 32
            if left.expr_type == ExpressionType.CONSTANT and left.value == 0xFFFFFFFF:
                name, _ = _extract_index_param(right)
                return name, 32

    return None, 0


def _get_parameter_info(parameters: Sequence[Dict], name: str) -> Optional[Dict]:
    for param in parameters:
        if param.get("name") == name:
            return param
    return None


def _enumerate_candidate_indices(
    pattern: IndexedAddressPattern,
    conditions: List[Condition],
    param_info: Dict,
    debug: bool,
) -> List[int]:
    nonneg, upper_bound = _extract_index_range(conditions, pattern.index_param_name)
    if upper_bound is None or upper_bound <= 0:
        return []

    is_unsigned = not param_info.get("is_signed", True)
    if not is_unsigned and not nonneg:
        return []

    if upper_bound > MAX_ENUMERATED_INDEX_VALUES:
        return []

    indices = list(range(0, upper_bound))
    if debug:
        print(
            f"[MemoryResolver] candidate indices for {pattern.index_param_name}: {indices}"
        )
    return indices


def _extract_index_range(
    conditions: List[Condition],
    param_name: str,
) -> Tuple[bool, Optional[int]]:
    """Extract a conservative [0, upper_bound) range for a parameter."""
    nonneg = False
    upper_bound: Optional[int] = None

    for cond in conditions:
        if cond.negated:
            continue

        expr = cond.expression
        if expr.expr_type != ExpressionType.BINARY_OP or len(expr.operands) < 2:
            continue

        left, right = expr.operands[0], expr.operands[1]

        if expr.operator == "INT_SLESS":
            if _is_zero_constant(left) and _is_named_param(right, param_name):
                nonneg = True
            elif _is_minus_one_constant(left) and _is_named_param(right, param_name):
                nonneg = True
            elif _is_named_param(left, param_name) and _is_nonnegative_constant(right):
                bound = int(right.value)
                upper_bound = bound if upper_bound is None else min(upper_bound, bound)
        elif expr.operator == "INT_LESS":
            if _is_named_param(left, param_name) and _is_nonnegative_constant(right):
                bound = int(right.value)
                upper_bound = bound if upper_bound is None else min(upper_bound, bound)
        elif expr.operator == "INT_SLESSEQUAL":
            if _is_zero_constant(left) and _is_named_param(right, param_name):
                nonneg = True
            elif _is_named_param(left, param_name) and _is_nonnegative_constant(right):
                bound = int(right.value) + 1
                upper_bound = bound if upper_bound is None else min(upper_bound, bound)

    return nonneg, upper_bound


def _is_named_param(expr: Expression, param_name: str) -> bool:
    return expr.expr_type == ExpressionType.PARAMETER and expr.name == param_name


def _is_zero_constant(expr: Expression) -> bool:
    return expr.expr_type == ExpressionType.CONSTANT and expr.value == 0


def _is_minus_one_constant(expr: Expression) -> bool:
    return expr.expr_type == ExpressionType.CONSTANT and expr.value == -1


def _is_nonnegative_constant(expr: Expression) -> bool:
    return expr.expr_type == ExpressionType.CONSTANT and isinstance(expr.value, int) and expr.value >= 0
