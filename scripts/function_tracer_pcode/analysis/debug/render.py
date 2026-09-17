# -*- coding: utf-8 -*-
"""Lightweight debug rendering helpers."""

from __future__ import annotations

from typing import Any, Callable, Iterable, List, Optional, Set

from scripts.function_tracer_pcode.core import Condition, Expression, ExpressionType


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

            if expr_type == ExpressionType.INTRINSIC:
                arg_count = len(node.operands or [])
                return f"INTRINSIC({node.name or '?'}, argc={arg_count})"

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


#: debug サマリーに並べる要素数の既定上限。列の長さ自体は打ち切り件数で示す。
DEFAULT_MAX_ITEMS = 8


def _summarize_sequence(
    items: Optional[Iterable[Any]],
    renderer: Callable[..., str],
    max_depth: int,
    max_items: int,
) -> str:
    """列を ``[a, b, +3 more]`` 形式の有界文字列にする。"""

    if items is None:
        return "[]"
    rendered: List[str] = []
    overflow = 0
    for item in items:
        if len(rendered) >= max_items:
            overflow += 1
            continue
        rendered.append(renderer(item, max_depth=max_depth))
    body = ", ".join(rendered)
    if overflow:
        body = f"{body}, +{overflow} more" if body else f"+{overflow} more"
    return f"[{body}]"


def summarize_expressions(
    expressions: Optional[Iterable[Optional[Expression]]],
    max_depth: int = 4,
    max_items: int = DEFAULT_MAX_ITEMS,
) -> str:
    """式列の有界サマリー。full render しないので debug 出力から安全に呼べる。"""

    return _summarize_sequence(expressions, summarize_expression, max_depth, max_items)


def summarize_conditions(
    conditions: Optional[Iterable[Optional[Condition]]],
    max_depth: int = 4,
    max_items: int = DEFAULT_MAX_ITEMS,
) -> str:
    """条件列の有界サマリー。full render しないので debug 出力から安全に呼べる。"""

    return _summarize_sequence(conditions, summarize_condition, max_depth, max_items)
