# -*- coding: utf-8 -*-
"""SMT-backed reasoning over Condition objects."""

from __future__ import annotations

import importlib
from typing import Any, Dict, Iterable, List, Optional, Sequence, Tuple

from scripts.function_tracer_pcode.core import Condition
from scripts.function_tracer_pcode.core.semantic_freeze import freeze_expression
from scripts.function_tracer_pcode.core.semantic_projection import project_runtime_ref
from scripts.function_tracer_pcode.core.semantic_snapshot import semantic_projection
from scripts.function_tracer_pcode.core.structural import condition_key, key_contains_placeholder
from scripts.function_tracer_pcode.core.render_smt import (
    CallDeclarationConflict,
    add_call_smt_declaration,
    call_smt_declaration,
    call_smt_declaration_lines,
    collect_float_predicate_smt_declarations,
    collect_unknown_smt_declarations,
    expression_uses_smt_float_theory,
    normalize_call_symbol_name,
    expression_contains_unsupported_smt_ops,
    expression_returns_bool,
    expression_smt_bit_width,
    smt_logic_name,
)
from scripts.function_tracer_pcode.core.errors import AnalysisLimitation


class ConditionSMTOracle:
    """Direct SMT reachability oracle over object-centric condition ASTs."""

    QUERY_TIMEOUT_MS = 250
    _CACHE_LIMIT = 4096
    _availability_checked = False
    _available = False
    _z3: Any = None
    _unsat_cache: Dict[Tuple[object, ...], Optional[bool]] = {}
    _CACHE_KEY_SCHEMA_VERSION = "condition-smt-cache-v2"
    _RECOVERABLE_KEY_ERRORS = (
        AttributeError,
        IndexError,
        KeyError,
        TypeError,
        ValueError,
        RecursionError,
    )

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
        use_cache: bool = True,
    ) -> Optional[bool]:
        usable, script = cls._build_script(conditions)
        if not usable or script is None:
            return None

        query_key = (cache_key or cls._build_cache_key(conditions)) if use_cache else None
        if query_key is not None:
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
                if query_key is not None:
                    cls._remember(query_key, True)
                return True
            if result == z3.sat:
                if query_key is not None:
                    cls._remember(query_key, False)
                return False
            if query_key is not None:
                cls._remember(query_key, None)
            return None
        except AnalysisLimitation:
            # Issue #106 PR-106-0: 解析の限界は「回復可能な失敗」ではない。ここで
            # 握り潰すと pair の打ち切りが遅れるので、そのまま上へ返す。
            raise
        except Exception:
            return None

    @classmethod
    def _remember(cls, key: Tuple[object, ...], value: Optional[bool]) -> None:
        if len(cls._unsat_cache) >= cls._CACHE_LIMIT:
            cls._unsat_cache.clear()
        cls._unsat_cache[key] = value

    @classmethod
    def _safe_condition_cache_component(cls, condition) -> Optional[Tuple[object, ...]]:
        try:
            key = condition_key(condition, budget=96)
            if key_contains_placeholder(key):
                return None
            return key
        except cls._RECOVERABLE_KEY_ERRORS:
            return None

    @classmethod
    def _build_cache_key(cls, conditions: Sequence) -> Optional[Tuple[object, ...]]:
        keys = [cls._safe_condition_cache_component(condition) for condition in (conditions or ())]
        if any(key is None for key in keys):
            return None
        keys.sort(key=repr)
        return ("unsat", cls._CACHE_KEY_SCHEMA_VERSION, tuple(keys))

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
        float_predicate_decls = set()
        uses_float_theory = False
        call_declarations: Dict[str, Tuple[Tuple[int, ...], int]] = {}
        symbol_names: Dict[Tuple[Any, ...], str] = {}

        for condition in conditions:
            expr = getattr(condition, "expression", None)
            if expr is None:
                return False, None
            if expression_contains_unsupported_smt_ops(expr, allow_call=True):
                return False, None

            for node in cls._iter_expression_nodes(expr):
                expr_type = getattr(node, "expr_type", None)
                expr_kind = getattr(expr_type, "__class__", None)
                if expr_type is None or expr_kind is None:
                    continue
                if expr_type in {expr_kind.PARAMETER, expr_kind.VARIABLE}:
                    identity = cls._expression_identity_key(node)
                    if not cls._identity_is_solver_safe(identity):
                        return False, None
                    bit_width = max(1, int(expression_smt_bit_width(node) or 0))
                    if bit_width <= 0:
                        return False, None
                    existing_symbol = symbol_names.get(identity)
                    if existing_symbol is None:
                        existing_symbol = f"objvar_{len(symbol_names)}"
                        symbol_names[identity] = existing_symbol
                    existing = var_widths.get(existing_symbol)
                    if existing is not None and existing != bit_width:
                        return False, None
                    var_widths[existing_symbol] = bit_width
                elif expr_type == expr_kind.MEMORY:
                    mem_bits = max(1, int(expression_smt_bit_width(node) or 0))
                    if mem_bits not in {8, 16, 32, 64}:
                        return False, None
                    memory_widths.add(mem_bits)
                elif expr_type == expr_kind.CALL:
                    # 宣言規則は core/render_smt の共有 helper が唯一の実装。
                    # 幅が取れない CALL も、同名で signature が食い違う CALL も
                    # fail closed（従来どおり oracle は答えない）。
                    try:
                        if not add_call_smt_declaration(call_declarations, node):
                            return False, None
                    except CallDeclarationConflict:
                        return False, None

            for decl in collect_unknown_smt_declarations(expr):
                unknown_decls.add(decl)
            uses_float_theory = uses_float_theory or expression_uses_smt_float_theory(expr)
            for decl in collect_float_predicate_smt_declarations(expr, float_mode="fp"):
                float_predicate_decls.add(decl)

        lines: List[str] = [
            f"(set-logic {smt_logic_name(uses_float_theory=uses_float_theory, uses_arrays=True, uses_uf=bool(float_predicate_decls))})"
        ]
        for name, bit_width in sorted(var_widths.items()):
            lines.append(f"(declare-const {name} (_ BitVec {bit_width}))")
        for mem_bits in sorted(memory_widths):
            lines.append(
                f"(declare-const mem{mem_bits} (Array (_ BitVec 64) (_ BitVec {mem_bits})))"
            )
        for symbol_name, bit_width in sorted(unknown_decls):
            lines.append(f"(declare-const {symbol_name} (_ BitVec {bit_width}))")
        lines.extend(sorted(float_predicate_decls))
        lines.extend(call_smt_declaration_lines(call_declarations))
        for condition in conditions:
            condition_expr = getattr(condition, "expression", None)
            if condition_expr is None:
                return False, None
            condition_smt = cls._condition_to_smt(condition, symbol_names)
            if not expression_returns_bool(condition_expr):
                bits = max(1, int(expression_smt_bit_width(condition_expr) or 0))
                if bits <= 0:
                    return False, None
                condition_smt = f"(not (= {condition_smt} (_ bv0 {bits})))"
            lines.append(f"(assert {condition_smt})")
        return True, "\n".join(lines)

    @classmethod
    def _symbol_name(cls, expr) -> Optional[str]:
        expr_type = getattr(expr, "expr_type", None)
        expr_kind = getattr(expr_type, "__class__", None)
        if expr_type is None or expr_kind is None:
            return None
        if expr_type == expr_kind.CALL:
            return normalize_call_symbol_name(getattr(expr, "name", None))
        identity = cls._expression_identity_key(expr)
        if identity is None:
            return None
        return str(identity)

    @classmethod
    def _identity_is_solver_safe(cls, identity: Optional[Tuple[Any, ...]]) -> bool:
        if not isinstance(identity, tuple) or not identity:
            return False
        # Name-only parameters are not object identities. They can collide
        # across distinct storage/index/provenance sources, so SMT-backed
        # coverage and implication checks must decline instead of proving.
        if identity[0] == "parameter_name":
            return False
        if identity[0] == "parameter_generated_ordinal":
            return False
        if cls._identity_contains_unsafe_parameter_key(identity):
            return False
        if (
            identity[0] == "runtime_ref"
            and len(identity) >= 3
            and isinstance(identity[2], tuple)
            and identity[2]
            and identity[2][0]
            in {
                "parameter_without_semantic_identity",
                "stable_parameter_without_index",
            }
        ):
            return False
        return True

    @classmethod
    def _identity_contains_unsafe_parameter_key(cls, value: Any) -> bool:
        if isinstance(value, tuple):
            if cls._is_unsafe_parameter_key(value):
                return True
            return any(cls._identity_contains_unsafe_parameter_key(item) for item in value)
        if isinstance(value, (list, set, frozenset)):
            return any(cls._identity_contains_unsafe_parameter_key(item) for item in value)
        return False

    @staticmethod
    def _is_unsafe_parameter_key(value: Tuple[Any, ...]) -> bool:
        if not value or value[0] != "parameter":
            return False
        if len(value) == 1:
            return True
        if len(value) == 2:
            return value[1] is None
        if len(value) == 3:
            return value[1] is None or value[2] is None
        if len(value) >= 4:
            return value[3] is None
        return False

    @classmethod
    def _expression_identity_key(cls, expr) -> Optional[Tuple[Any, ...]]:
        """solver query 用の object identity。

        凍結済みの式では runtime_ref / storage の意味 key を **凍結時に確定した
        投影** から読む。query identity が生 object の後からの変化で動くと、
        同じ query に別の cache 行が当たってしまう。
        """

        expr_type = getattr(expr, "expr_type", None)
        expr_kind = getattr(expr_type, "__class__", None)
        if expr_type is None or expr_kind is None:
            return None
        if expr_type in {expr_kind.PARAMETER, expr_kind.VARIABLE}:
            projection = semantic_projection(expr)
            runtime_identity = cls._runtime_ref_identity_from_projection(projection)
            if runtime_identity is not None:
                return (
                    "runtime_ref",
                    "parameter" if expr_type == expr_kind.PARAMETER else "variable",
                    runtime_identity,
                )
            if expr_type == expr_kind.PARAMETER:
                parameter_name = getattr(expr, "name", None)
                try:
                    parameter_index = int(getattr(expr, "value", -1))
                    if parameter_index >= 0:
                        # Some synthetic/unit-test expressions can carry a
                        # placeholder index for multiple distinct parameters.
                        # Include the name when present to avoid conflating
                        # unrelated parameters in solver-backed condition
                        # implication.
                        if parameter_name:
                            return ("parameter_index_name", parameter_index, str(parameter_name))
                        return ("parameter_index", parameter_index)
                except (TypeError, ValueError):
                    parameter_index = None
                if projection.storage_identity_supported:
                    if projection.storage_identity is None:
                        return None
                    return ("parameter_storage", projection.storage_identity)
                if parameter_name:
                    return ("parameter_name", str(parameter_name))
            return None
        if expr_type == expr_kind.CALL:
            return normalize_call_symbol_name(getattr(expr, "name", None))
        return None

    @classmethod
    def has_object_identity_support(cls, conditions: Sequence) -> bool:
        """Return false when any PARAMETER/VARIABLE cannot be given a stable identity."""
        try:
            for condition in conditions or ():
                expr = getattr(condition, "expression", None)
                if expr is None:
                    return False
                for node in cls._iter_expression_nodes(expr):
                    expr_type = getattr(node, "expr_type", None)
                    expr_kind = getattr(expr_type, "__class__", None)
                    if expr_type is None or expr_kind is None:
                        continue
                    if expr_type in {expr_kind.PARAMETER, expr_kind.VARIABLE}:
                        identity = cls._expression_identity_key(node)
                        if not cls._identity_is_solver_safe(identity):
                            return False
            return True
        except Exception:
            return False

    @classmethod
    def _runtime_ref_identity(cls, runtime_ref: Any) -> Optional[Tuple[Any, ...]]:
        """生の ref から identity を作る（式を持たない直接呼び出し用）。

        生 object を読むのは `core/semantic_projection.py` だけなので、ここでも
        投影を作ってから同じ規則を適用する。
        """

        if runtime_ref is None:
            return None
        return cls._runtime_ref_identity_from_projection(
            project_runtime_ref(None, runtime_ref)
        )

    @classmethod
    def _runtime_ref_identity_from_projection(cls, projection) -> Optional[Tuple[Any, ...]]:
        """投影 1 つから identity を決める（`SemanticSnapshot` でも `RuntimeRefProjection` でも）。"""

        return cls._runtime_ref_identity_from_parts(
            semantic_identity=projection.runtime_semantic_key
            if hasattr(projection, "runtime_semantic_key")
            else projection.semantic_key,
            stable_identity=projection.runtime_stable_key
            if hasattr(projection, "runtime_stable_key")
            else projection.stable_key,
            parameter_ref=projection.runtime_is_parameter_ref
            if hasattr(projection, "runtime_is_parameter_ref")
            else projection.is_parameter_ref,
        )

    @classmethod
    def _runtime_ref_identity_from_parts(
        cls,
        *,
        semantic_identity: Any,
        stable_identity: Any,
        parameter_ref: bool,
    ) -> Optional[Tuple[Any, ...]]:
        """identity の **決め方** はここ 1 箇所（生 object 経由も投影経由も同じ）。"""

        if semantic_identity is not None:
            return ("semantic", semantic_identity)
        if stable_identity is not None:
            if parameter_ref:
                return ("parameter_without_semantic_identity", stable_identity)
            return ("stable", stable_identity)
        if parameter_ref:
            return ("parameter_without_semantic_identity", None)
        return None

    @staticmethod
    def _runtime_ref_is_parameter_ref(runtime_ref: Any) -> bool:
        return project_runtime_ref(None, runtime_ref).is_parameter_ref

    @classmethod
    def _condition_to_smt(
        cls,
        condition,
        symbol_names: Dict[Tuple[Any, ...], str],
    ) -> str:
        expr = getattr(condition, "expression", None)
        if expr is None:
            return "false"
        rewritten = cls._rewrite_expr_with_symbol_names(
            expr,
            symbol_names,
        )
        # symbol 名を差し替えた式は **この query のための新しい意味値**。作った側
        # が公開してから renderer へ渡す（renderer に lifecycle を進めさせない）。
        freeze_expression(rewritten)
        condition_smt = rewritten.to_smt(float_mode="fp")
        if getattr(condition, "negated", False):
            return f"(not {condition_smt})"
        return condition_smt

    @classmethod
    def _rewrite_expr_with_symbol_names(
        cls,
        expr,
        symbol_names: Dict[Tuple[Any, ...], str],
        active: Optional[set[int]] = None,
        memo: Optional[Dict[int, Any]] = None,
    ):
        if expr is None:
            return expr
        if active is None:
            active = set()
        if memo is None:
            memo = {}
        expr_id = id(expr)
        if expr_id in memo:
            return memo[expr_id]
        if expr_id in active:
            memo[expr_id] = expr
            return expr
        active.add(expr_id)

        expr_type = getattr(expr, "expr_type", None)
        expr_kind = getattr(expr_type, "__class__", None)
        if expr_type is None or expr_kind is None:
            memo[expr_id] = expr
            return expr
        if expr_type in {expr_kind.PARAMETER, expr_kind.VARIABLE}:
            identity = cls._expression_identity_key(expr)
            if identity is None:
                memo[expr_id] = expr
                return expr
            symbol = symbol_names.get(identity)
            if symbol is None:
                memo[expr_id] = expr
                return expr
            rewritten_parameter = expr.clone_with(name=symbol)
            memo[expr_id] = rewritten_parameter
            return rewritten_parameter

        cloned_operands = [
                cls._rewrite_expr_with_symbol_names(
                    operand,
                    symbol_names,
                    active,
                    memo,
                )
                for operand in (getattr(expr, "operands", None) or [])
            ]
        cloned_value = None
        if expr_type == expr_kind.PHI and getattr(expr, "value", None):
            cloned_value = []
            for cond, value in expr.value:
                cond_expr = getattr(cond, "expression", None) if cond is not None else None
                if cond is not None and cond_expr is not None:
                    rewritten_cond = cls._rewrite_expr_with_symbol_names(
                        cond_expr,
                        symbol_names,
                        active,
                        memo,
                    )
                    cond = Condition(rewritten_cond, bool(getattr(cond, "negated", False)))
                cloned_value.append(
                    (
                        cond,
                        cls._rewrite_expr_with_symbol_names(
                            value,
                            symbol_names,
                            active,
                            memo,
                        ),
                    )
                )
            if cloned_value is not None:
                cloned_value = tuple(cloned_value)
        rewritten_expr = expr.clone_with(
            operands=tuple(cloned_operands),
            value=cloned_value if cloned_value is not None else expr.value,
        )
        memo[expr_id] = rewritten_expr
        active.discard(expr_id)
        return rewritten_expr

    @classmethod
    def _collect_call_declaration(
        cls,
        node: Any,
        ) -> Optional[Tuple[str, Tuple[int, ...], int]]:
        """共有 helper への薄い委譲（既存呼び出し元・test のための入口）。"""
        return call_smt_declaration(node)

    @classmethod
    def _iter_expression_nodes(cls, expr) -> Iterable[Any]:
        pending: List[Any] = [expr]
        seen: set[int] = set()
        while pending:
            current = pending.pop()
            if current is None:
                continue
            current_id = id(current)
            if current_id in seen:
                continue
            seen.add(current_id)
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
