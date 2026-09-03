"""Unknown-value runtime identities and their SMT symbol declarations."""

from __future__ import annotations

import hashlib
from typing import Any, List, Optional, Tuple
from scripts.function_tracer_pcode.core.runtime_refs import (
    AddressValueRef,
    CanonicalLocation,
    PostStateReadRef,
    PostStateValueRef,
)


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


def _coerce_address_value_ref(expr) -> Optional[AddressValueRef]:
    runtime_ref = getattr(expr, "runtime_ref", None)
    if isinstance(runtime_ref, AddressValueRef):
        return runtime_ref
    return None


# Sibling modules reference each other at call time; import them last to avoid cycles.
from scripts.function_tracer_pcode.core.render_smt.widths import (
    expression_smt_bit_width,
)
