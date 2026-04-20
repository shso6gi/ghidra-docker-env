# -*- coding: utf-8 -*-
"""SMT-backed reasoning over Condition objects."""

from __future__ import annotations

import importlib
from typing import Any, Dict, Iterable, List, Optional, Sequence, Tuple

from ...model.render_smt import (
    collect_unknown_smt_declarations,
    expression_contains_unsupported_smt_ops,
    expression_smt_bit_width,
)


class ConditionSMTOracle:
    """Direct SMT reachability oracle over object-centric condition ASTs."""

    QUERY_TIMEOUT_MS = 250
    _CACHE_LIMIT = 4096
    _availability_checked = False
    _available = False
    _z3: Any = None
    _unsat_cache: Dict[Tuple[object, ...], Optional[bool]] = {}

    @classmethod
    def is_available(cls) -> bool:
        if cls._availability_checked:
            return cls._available
        cls._availability_checked = True
        try:
            cls._z3 = importlib.import_module("z3")
            cls._available = True
        except Exception:
            cls._z3 = None
            cls._available = False
        return cls._available

    @classmethod
    def conjunction_is_unsat(
        cls,
        conditions: Sequence,
        *,
        cache_key: Optional[Tuple[object, ...]] = None,
    ) -> Optional[bool]:
        usable, script = cls._build_script(conditions)
        if not usable or script is None:
            return None

        query_key = cache_key or ("unsat", tuple(condition.to_smt() for condition in conditions))
        cached = cls._unsat_cache.get(query_key)
        if cached is not None:
            return cached

        z3 = cls._z3
        if z3 is None and not cls.is_available():
            return None
        z3 = cls._z3

        try:
            solver = z3.Solver()
            solver.set("timeout", int(cls.QUERY_TIMEOUT_MS))
            assertions = z3.parse_smt2_string(script)
            solver.add(assertions)
            result = solver.check()
            if result == z3.unsat:
                cls._remember(query_key, True)
                return True
            if result == z3.sat:
                cls._remember(query_key, False)
                return False
            cls._remember(query_key, None)
            return None
        except Exception:
            return None

    @classmethod
    def _remember(cls, key: Tuple[object, ...], value: Optional[bool]) -> None:
        if len(cls._unsat_cache) >= cls._CACHE_LIMIT:
            cls._unsat_cache.clear()
        cls._unsat_cache[key] = value

    @classmethod
    def _build_script(
        cls,
        conditions: Sequence,
    ) -> Tuple[bool, Optional[str]]:
        if not conditions:
            return True, "(set-logic QF_AUFBV)"
        if not cls.is_available():
            return False, None

        var_widths: Dict[str, int] = {}
        memory_widths = set()
        unknown_decls = set()

        for condition in conditions:
            expr = getattr(condition, "expression", None)
            if expr is None:
                return False, None
            if expression_contains_unsupported_smt_ops(expr):
                return False, None
            for node in cls._iter_expression_nodes(expr):
                expr_type = getattr(node, "expr_type", None)
                expr_kind = getattr(expr_type, "__class__", None)
                if expr_type is None or expr_kind is None:
                    continue
                if expr_type in {expr_kind.PARAMETER, expr_kind.VARIABLE}:
                    symbol = cls._symbol_name(node)
                    if not symbol:
                        return False, None
                    bit_width = max(1, int(expression_smt_bit_width(node) or 0))
                    if bit_width <= 0:
                        return False, None
                    existing = var_widths.get(symbol)
                    if existing is not None and existing != bit_width:
                        return False, None
                    var_widths[symbol] = bit_width
                elif expr_type == expr_kind.MEMORY:
                    mem_bits = max(1, int(expression_smt_bit_width(node) or 0))
                    if mem_bits not in {8, 16, 32, 64}:
                        return False, None
                    memory_widths.add(mem_bits)

            for decl in collect_unknown_smt_declarations(expr):
                unknown_decls.add(decl)

        lines: List[str] = ["(set-logic QF_AUFBV)"]
        for name, bit_width in sorted(var_widths.items()):
            lines.append(f"(declare-const {name} (_ BitVec {bit_width}))")
        for mem_bits in sorted(memory_widths):
            lines.append(
                f"(declare-const mem{mem_bits} (Array (_ BitVec 64) (_ BitVec {mem_bits})))"
            )
        for symbol_name, bit_width in sorted(unknown_decls):
            lines.append(f"(declare-const {symbol_name} (_ BitVec {bit_width}))")
        for condition in conditions:
            lines.append(f"(assert {condition.to_smt()})")
        return True, "\n".join(lines)

    @classmethod
    def _symbol_name(cls, expr) -> Optional[str]:
        expr_type = getattr(expr, "expr_type", None)
        expr_kind = getattr(expr_type, "__class__", None)
        if expr_type is None or expr_kind is None:
            return None
        if expr_type == expr_kind.PARAMETER:
            if getattr(expr, "name", None):
                return expr.name
            return f"param_{getattr(expr, 'value', -1)}"
        if expr_type == expr_kind.VARIABLE:
            return getattr(expr, "name", None) or "var"
        return None

    @classmethod
    def _iter_expression_nodes(cls, expr) -> Iterable[Any]:
        pending: List[Any] = [expr]
        while pending:
            current = pending.pop()
            if current is None:
                continue
            yield current

            expr_type = getattr(current, "expr_type", None)
            expr_kind = getattr(expr_type, "__class__", None)
            if expr_type is None or expr_kind is None:
                continue

            if expr_type == expr_kind.PHI and getattr(current, "value", None):
                for cond, value in reversed(current.value):
                    if value is not None:
                        pending.append(value)
                    cond_expr = getattr(cond, "expression", None) if cond is not None else None
                    if cond_expr is not None:
                        pending.append(cond_expr)
                continue

            for operand in reversed(list(getattr(current, "operands", None) or [])):
                if operand is not None:
                    pending.append(operand)
