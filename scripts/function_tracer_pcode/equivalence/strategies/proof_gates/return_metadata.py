"""Width metadata helpers that do not authorize cross-width comparison."""

from __future__ import annotations

import re
from typing import Any, Dict, List, Optional, Sequence, Set

from ....model.render_smt import expression_smt_bit_width


def _impl__collect_condition_width_sign_metadata(
    cls,
    condition: Any,
    bit_widths: Set[int],
    signedness: Set[str],
) -> None:
    expr = getattr(condition, "expression", None)
    for node in cls._iter_expression_nodes_for_metadata(expr):
        try:
            bit_width = int(expression_smt_bit_width(node) or 0)
        except (AttributeError, TypeError, ValueError, RecursionError):
            bit_width = 0
        if bit_width > 0:
            bit_widths.add(bit_width)
        operator = getattr(node, "operator", None)
        if operator in {"INT_SLESS", "INT_SLESSEQUAL"}:
            signedness.add("signed")
        elif operator in {"INT_LESS", "INT_LESSEQUAL"}:
            signedness.add("unsigned")
        elif operator in {"INT_EQUAL", "INT_NOTEQUAL"}:
            signedness.add("equality")


def _impl__expression_bit_width_from_object_key(cls, object_key: Any) -> Optional[int]:
    normalized = cls._normalize_nested_tuple(object_key)
    if not isinstance(normalized, tuple):
        return None
    stack = [normalized]
    seen: Set[int] = set()
    while stack:
        current = stack.pop()
        if id(current) in seen:
            continue
        seen.add(id(current))
        if isinstance(current, tuple):
            if len(current) >= 2 and current[0] in {"size", "size_bytes"}:
                try:
                    value = int(current[1])
                except Exception:
                    value = 0
                if current[0] == "size_bytes":
                    value *= 8
                if value > 0:
                    return value
            if len(current) >= 2 and str(current[0]).endswith("bits"):
                try:
                    value = int(current[1])
                except Exception:
                    value = 0
                if value > 0:
                    return value
            stack.extend(reversed(current))
    return None


def _impl__coerce_return_width(*values: Any) -> Optional[int]:
    for value in values:
        if value is None:
            continue
        try:
            bits = int(value)
        except (TypeError, ValueError):
            continue
        if bits > 0:
            return bits
    return None


def _impl__expression_smt_bit_width_for_object_key(expr: Any) -> Optional[int]:
    if expr is None:
        return None
    try:
        bits = int(expression_smt_bit_width(expr) or 0)
    except (AttributeError, TypeError, ValueError, RecursionError):
        bits = 0
    if bits <= 0:
        try:
            bits = int(getattr(expr, "get_bit_width", lambda: 0)() or 0)
        except (AttributeError, TypeError, ValueError, RecursionError):
            bits = 0
    return bits if bits > 0 else None


def _impl__return_pcode_value_input_width_bits(pcode_op_ref: Any) -> Optional[int]:
    input_sizes = getattr(pcode_op_ref, "input_sizes", None) or ()
    candidates = []
    for size in input_sizes:
        try:
            int_size = int(size)
        except (TypeError, ValueError):
            continue
        if int_size > 0:
            candidates.append(int_size)
    return max(1, candidates[-1]) * 8 if candidates else None


def _impl__normalize_zero_constant_widths_for_declared_symbols(
    cls,
    assertions: Sequence[str],
    header_lines: Sequence[str],
) -> List[str]:
    widths: Dict[str, int] = {}
    for line in header_lines or ():
        match = re.search(
            r"\(declare-(?:fun|const)\s+([^\s()]+)\s+(?:\(\)\s+)?\(_\s+BitVec\s+(\d+)\)\)",
            str(line),
        )
        if match is not None:
            widths[match.group(1)] = int(match.group(2))
    if not widths:
        return list(assertions or ())
    normalized = []
    for assertion in assertions or ():
        text = str(assertion)
        for symbol, width in widths.items():
            escaped = re.escape(symbol)
            text = re.sub(
                rf"(\((?:bvslt|bvult|bvsle|bvule|=|distinct)\s+)\(_ bv0 \d+\)(\s+{escaped}(?=[\s)]))",
                rf"\1(_ bv0 {width})\2",
                text,
            )
            text = re.sub(
                rf"(\((?:bvslt|bvult|bvsle|bvule|=|distinct)\s+{escaped}\s+)\(_ bv0 \d+\)(?=\))",
                rf"\1(_ bv0 {width})",
                text,
            )
        normalized.append(text)
    return normalized
