# -*- coding: utf-8 -*-
"""Lightweight debug rendering helpers."""

from __future__ import annotations

from typing import Optional, Set

from ...model import Condition, Expression, ExpressionType


def summarize_expression(expr: Optional[Expression], max_depth: int = 4) -> str:
    """Render a compact, cycle-safe summary without full pretty-printing."""
    if expr is None:
        return "None"

    visited: Set[int] = set()

    def _render(node: Optional[Expression], depth: int) -> str:
        if node is None:
            return "None"
        if depth <= 0:
            return "..."

        node_id = id(node)
        if node_id in visited:
            return "<cycle>"
        visited.add(node_id)

        try:
            expr_type = getattr(node, "expr_type", None)
            expr_type_name = getattr(expr_type, "name", str(expr_type))

            if expr_type == ExpressionType.CONSTANT:
                try:
                    value = int(node.value)
                except Exception:
                    value = getattr(node, "value", "?")
                return f"CONST({value})"

            if expr_type == ExpressionType.PARAMETER:
                return f"PARAM({node.name or '?'})"

            if expr_type == ExpressionType.VARIABLE:
                return f"VAR({node.name or '?'})"

            if expr_type == ExpressionType.UNKNOWN:
                return f"UNKNOWN({node.name or '?'})"

            if expr_type == ExpressionType.CALL:
                arg_count = len(node.operands or [])
                return f"CALL({node.name or '?'}, argc={arg_count})"

            if expr_type == ExpressionType.MEMORY:
                inner = _render((node.operands or [None])[0], depth - 1)
                return f"MEM[{inner}]"

            if expr_type == ExpressionType.UNARY_OP:
                inner = _render((node.operands or [None])[0], depth - 1)
                return f"{node.operator or 'UNARY'}({inner})"

            if expr_type == ExpressionType.BINARY_OP:
                operands = node.operands or []
                left = _render(operands[0] if len(operands) > 0 else None, depth - 1)
                right = _render(operands[1] if len(operands) > 1 else None, depth - 1)
                return f"{node.operator or 'BINARY'}({left}, {right})"

            if expr_type == ExpressionType.PHI:
                branches = node.value or []
                return f"PHI(branches={len(branches)})"

            return expr_type_name
        finally:
            visited.discard(node_id)

    return _render(expr, max_depth)


def summarize_condition(condition: Optional[Condition], max_depth: int = 4) -> str:
    if condition is None:
        return "None"
    expr_summary = summarize_expression(condition.expression, max_depth=max_depth)
    return f"(not {expr_summary})" if condition.negated else expr_summary
