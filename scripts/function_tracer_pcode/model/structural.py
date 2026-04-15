# -*- coding: utf-8 -*-
"""Structural keys for Expression / Condition.

These helpers keep normalization and equivalence internals on the AST/P-code
side instead of round-tripping through rendered strings.
"""

from __future__ import annotations

from typing import Any, Optional, Tuple

from .condition import Condition
from .expression import Expression, ExpressionType


StructuralKey = Tuple[Any, ...]
COMMUTATIVE_BINARY_OPS = frozenset(
    {
        "INT_ADD",
        "INT_MULT",
        "INT_AND",
        "INT_OR",
        "INT_XOR",
        "INT_EQUAL",
        "INT_NOTEQUAL",
        "BOOL_AND",
        "BOOL_OR",
        "BOOL_XOR",
    }
)
WIDTH_ADAPTER_OPS = frozenset({"INT_ZEXT", "INT_SEXT"})


def _atom_key(value: Any) -> StructuralKey:
    if value is None:
        return ("none", "")
    if isinstance(value, bool):
        return ("bool", int(value))
    if isinstance(value, int):
        return ("int", value)
    if isinstance(value, str):
        return ("str", value)
    return ("repr", repr(value))


def _is_all_ones_mask_for_size(expr: Optional[Expression], size: int) -> bool:
    if expr is None or size <= 0 or expr.expr_type != ExpressionType.CONSTANT:
        return False
    mask = (1 << (size * 8)) - 1
    try:
        return (int(expr.value) & mask) == mask
    except (TypeError, ValueError):
        return False


def expression_key(
    expr: Optional[Expression],
    *,
    budget: int = 256,
    normalize_commutative: bool = True,
    strip_width_adapters: bool = False,
    collapse_full_masks: bool = False,
    include_memory_read_order: bool = True,
) -> StructuralKey:
    """Return a stable, hashable structural key for an expression tree."""

    visited: set[int] = set()

    def _build(node: Optional[Expression], remaining: int) -> tuple[StructuralKey, int]:
        if node is None:
            return (("none",), remaining)
        if remaining <= 0:
            return (
                (
                    "truncated",
                    node.expr_type.name,
                    node.operator or "",
                    node.name or "",
                    int(node.size or 0),
                ),
                remaining,
            )

        node_id = id(node)
        if node_id in visited:
            return (("cycle", node.expr_type.name, node.name or "", int(node.size or 0)), remaining)
        visited.add(node_id)

        try:
            remaining -= 1
            current = node

            if strip_width_adapters:
                while (
                    current.expr_type == ExpressionType.UNARY_OP
                    and current.operator in WIDTH_ADAPTER_OPS
                    and current.operands
                ):
                    current = current.operands[0]

            if (
                collapse_full_masks
                and current.expr_type == ExpressionType.BINARY_OP
                and current.operator == "INT_AND"
                and len(current.operands) == 2
            ):
                left, right = current.operands
                mask_size = current.size or right.size or left.size or 0
                if _is_all_ones_mask_for_size(left, mask_size):
                    return _build(right, remaining)
                if _is_all_ones_mask_for_size(right, mask_size):
                    return _build(left, remaining)

            expr_type = current.expr_type

            if expr_type == ExpressionType.CONSTANT:
                return (
                    (
                        "const",
                        _atom_key(current.value),
                        int(current.size or 0),
                    ),
                    remaining,
                )

            if expr_type == ExpressionType.LITERAL:
                return (
                    (
                        "literal",
                        _atom_key(current.value),
                        int(current.size or 0),
                    ),
                    remaining,
                )

            if expr_type in {ExpressionType.PARAMETER, ExpressionType.VARIABLE, ExpressionType.UNKNOWN}:
                return (
                    (
                        expr_type.name.lower(),
                        current.name or "",
                        int(current.size or 0),
                    ),
                    remaining,
                )

            if expr_type == ExpressionType.UNARY_OP:
                operand = current.operands[0] if current.operands else None
                operand_key, remaining = _build(operand, remaining)
                return (
                    (
                        "unary",
                        current.operator or "",
                        int(current.size or 0),
                        operand_key,
                    ),
                    remaining,
                )

            if expr_type == ExpressionType.BINARY_OP:
                left = current.operands[0] if current.operands else None
                right = current.operands[1] if len(current.operands) > 1 else None
                left_key, remaining = _build(left, remaining)
                right_key, remaining = _build(right, remaining)
                if normalize_commutative and (current.operator or "") in COMMUTATIVE_BINARY_OPS:
                    if right_key < left_key:
                        left_key, right_key = right_key, left_key
                return (
                    (
                        "binary",
                        current.operator or "",
                        int(current.size or 0),
                        left_key,
                        right_key,
                    ),
                    remaining,
                )

            if expr_type == ExpressionType.MEMORY:
                address = current.operands[0] if current.operands else None
                address_key, remaining = _build(address, remaining)
                return (
                    (
                        "memory",
                        int(current.size or 0),
                        address_key,
                        int(current.read_order_key or 0) if include_memory_read_order else 0,
                    ),
                    remaining,
                )

            if expr_type == ExpressionType.CALL:
                arg_keys = []
                for operand in current.operands:
                    arg_key, remaining = _build(operand, remaining)
                    arg_keys.append(arg_key)
                return (
                    (
                        "call",
                        current.name or "",
                        int(current.size or 0),
                        tuple(arg_keys),
                    ),
                    remaining,
                )

            if expr_type == ExpressionType.PHI:
                branches = []
                for condition, value in current.value or []:
                    cond_key: StructuralKey
                    if condition is None:
                        cond_key = ("none",)
                    else:
                        expr_key_value, remaining = _build(condition.expression, remaining)
                        cond_key = ("cond", expr_key_value, bool(condition.negated))
                    value_key, remaining = _build(value, remaining)
                    branches.append((cond_key, value_key))
                return (
                    (
                        "phi",
                        int(current.size or 0),
                        tuple(branches),
                    ),
                    remaining,
                )

            return (
                (
                    "opaque",
                    expr_type.name,
                    current.operator or "",
                    current.name or "",
                    int(current.size or 0),
                ),
                remaining,
            )
        finally:
            visited.discard(node_id)

    key, _remaining = _build(expr, budget)
    return key


def condition_key(
    condition: Optional[Condition],
    *,
    budget: int = 256,
    normalize_commutative: bool = True,
) -> StructuralKey:
    if condition is None:
        return ("none",)
    return (
        "condition",
        expression_key(
            condition.expression,
            budget=budget,
            normalize_commutative=normalize_commutative,
        ),
        bool(condition.negated),
    )


def key_contains_placeholder(key: StructuralKey) -> bool:
    tag = key[0] if key else None
    if tag in {"truncated", "cycle", "opaque"}:
        return True
    for item in key[1:]:
        if isinstance(item, tuple) and item and isinstance(item[0], str):
            if key_contains_placeholder(item):
                return True
    return False
