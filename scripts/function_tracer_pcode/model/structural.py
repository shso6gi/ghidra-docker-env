# -*- coding: utf-8 -*-
"""Structural keys for Expression / Condition.

These helpers keep normalization and equivalence internals on the AST/P-code
side instead of round-tripping through rendered strings.
"""

from __future__ import annotations

import hashlib
import json
from dataclasses import fields, is_dataclass
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
    if isinstance(value, bytes):
        return ("bytes", value.hex())
    if isinstance(value, tuple):
        return ("tuple", tuple(_atom_key(item) for item in value))
    if isinstance(value, list):
        return ("list", tuple(_atom_key(item) for item in value))
    if isinstance(value, dict):
        items = [(_atom_key(key), _atom_key(item)) for key, item in value.items()]
        items.sort()
        return ("dict", tuple(items))
    stable_key = getattr(value, "stable_key", None)
    if callable(stable_key):
        try:
            return ("stable", _atom_key(stable_key()))
        except Exception:
            pass
    to_dict = getattr(value, "to_dict", None)
    if callable(to_dict):
        try:
            return ("object_dict", _atom_key(to_dict()))
        except Exception:
            pass
    if is_dataclass(value):
        return (
            "dataclass",
            type(value).__module__,
            type(value).__qualname__,
            tuple((field.name, _atom_key(getattr(value, field.name))) for field in fields(value)),
        )
    obj_dict = getattr(value, "__dict__", None)
    if isinstance(obj_dict, dict) and obj_dict:
        items = [(_atom_key(key), _atom_key(item)) for key, item in obj_dict.items() if not str(key).startswith("_")]
        items.sort()
        return (
            "object_attrs",
            type(value).__module__,
            type(value).__qualname__,
            tuple(items),
        )
    return ("object_id", type(value).__module__, type(value).__qualname__, id(value))


def _semantic_runtime_ref_key(value: Any) -> Optional[StructuralKey]:
    """Return a stable key only for runtime refs that expose semantic identity.

    We intentionally ignore arbitrary object attributes here. Debug-only or
    incidental runtime objects should not perturb structural equality unless
    they provide an explicit stable semantic key.
    """

    if value is None:
        return None
    if isinstance(value, bool):
        return ("bool", int(value))
    if isinstance(value, int):
        return ("int", value)
    if isinstance(value, str):
        return ("str", value)
    if isinstance(value, bytes):
        return ("bytes", value.hex())
    if isinstance(value, tuple):
        items = []
        for item in value:
            item_key = _semantic_runtime_ref_key(item)
            if item_key is None:
                return None
            items.append(item_key)
        return ("tuple", tuple(items))
    if isinstance(value, list):
        items = []
        for item in value:
            item_key = _semantic_runtime_ref_key(item)
            if item_key is None:
                return None
            items.append(item_key)
        return ("list", tuple(items))
    if isinstance(value, dict):
        items = []
        for key, item in value.items():
            key_key = _semantic_runtime_ref_key(key)
            item_key = _semantic_runtime_ref_key(item)
            if key_key is None or item_key is None:
                return None
            items.append((key_key, item_key))
        items.sort()
        return ("dict", tuple(items))
    stable_key = getattr(value, "stable_key", None)
    if callable(stable_key):
        try:
            return ("stable_runtime_ref", _atom_key(stable_key()))
        except Exception:
            return None
    return None


def _expression_runtime_metadata(expr: Expression) -> tuple[StructuralKey, ...]:
    runtime_key = _semantic_runtime_ref_key(getattr(expr, "runtime_ref", None))
    if runtime_key is None:
        return ()
    return (("runtime_ref", runtime_key),)


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
    include_semantic_runtime_refs: bool = True,
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

            if expr_type in {ExpressionType.PARAMETER, ExpressionType.VARIABLE}:
                return (
                    (
                        expr_type.name.lower(),
                        current.name or "",
                        _atom_key(current.value),
                        int(current.size or 0),
                    ),
                    remaining,
                )

            if expr_type == ExpressionType.UNKNOWN:
                runtime_metadata = (
                    _expression_runtime_metadata(current) if include_semantic_runtime_refs else ()
                )
                return (
                    (
                        "unknown",
                        current.name or "",
                        _atom_key(current.value),
                        int(current.size or 0),
                        *runtime_metadata,
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
                runtime_metadata = (
                    _expression_runtime_metadata(current) if include_semantic_runtime_refs else ()
                )
                return (
                    (
                        "memory",
                        int(current.size or 0),
                        address_key,
                        (
                            "read_order",
                            int(current.read_order_key),
                        )
                        if include_memory_read_order and current.read_order_key is not None
                        else ("read_order", None),
                        *runtime_metadata,
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

            if expr_type == ExpressionType.INTRINSIC:
                arg_keys = []
                for operand in current.operands:
                    arg_key, remaining = _build(operand, remaining)
                    arg_keys.append(arg_key)
                return (
                    (
                        "intrinsic",
                        current.name or "",
                        None if getattr(current, "opcode", None) is None else int(current.opcode),
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


def key_is_comparable(key: StructuralKey) -> bool:
    """Return False if the structural key contains placeholders/truncated markers."""

    return not key_contains_placeholder(key)


def expression_key_safe(
    expr: Optional[Expression],
    *,
    budget: int = 256,
    normalize_commutative: bool = True,
    strip_width_adapters: bool = False,
    collapse_full_masks: bool = False,
    include_memory_read_order: bool = True,
    include_semantic_runtime_refs: bool = True,
) -> Optional[StructuralKey]:
    """Return structural key only when it is safe for semantic equality.

    If a bounded traversal is truncated/cycle-detected/opaque, the result is None
    so callers can avoid treating two unrelated deep expressions as equal.
    """

    key = expression_key(
        expr,
        budget=budget,
        normalize_commutative=normalize_commutative,
        strip_width_adapters=strip_width_adapters,
        collapse_full_masks=collapse_full_masks,
        include_memory_read_order=include_memory_read_order,
        include_semantic_runtime_refs=include_semantic_runtime_refs,
    )
    if not key_is_comparable(key):
        return None
    return key


def expression_key_or_identity(
    expr: Optional[Expression],
    *,
    budget: int = 256,
    normalize_commutative: bool = True,
    strip_width_adapters: bool = False,
    collapse_full_masks: bool = False,
    include_memory_read_order: bool = True,
    include_semantic_runtime_refs: bool = True,
) -> StructuralKey:
    """Safe structural key with identity fallback for non-comparable inputs.

    This avoids collapsing semantically unknown/truncated keys into equality.
    """

    safe = expression_key_safe(
        expr,
        budget=budget,
        normalize_commutative=normalize_commutative,
        strip_width_adapters=strip_width_adapters,
        collapse_full_masks=collapse_full_masks,
        include_memory_read_order=include_memory_read_order,
        include_semantic_runtime_refs=include_semantic_runtime_refs,
    )
    if safe is not None:
        return safe
    if expr is None:
        return ("uncomparable_expression", "none")
    return ("uncomparable_expression", type(expr).__name__, id(expr))


def expression_provenance_key(
    expr: Optional[Expression],
    *,
    safe_budget: int = 256,
    max_digest_nodes: int = 8192,
    include_memory_read_order: bool = True,
    include_semantic_runtime_refs: bool = True,
) -> StructuralKey:
    """Stable key for object-target provenance.

    Unlike expression_key_or_identity(), this never falls back to process-local
    object ids. If the semantic structural key is too deep or otherwise
    uncomparable, use a stable digest over a full object-derived expression
    payload and include source atoms for diagnostics.
    """

    if expr is None:
        return ("none",)

    storage_key = _expression_storage_key(expr)
    if storage_key is not None:
        return ("storage", storage_key)

    runtime_key = _raw_stable_key_or_none(getattr(expr, "runtime_ref", None))
    if runtime_key is not None:
        return ("runtime_ref", runtime_key)

    safe = expression_key_safe(
        expr,
        budget=safe_budget,
        include_memory_read_order=include_memory_read_order,
        include_semantic_runtime_refs=include_semantic_runtime_refs,
    )
    if safe is not None:
        return ("expression", safe)

    payload, source_atoms, complete = _expression_provenance_payload(
        expr,
        max_nodes=max_digest_nodes,
    )
    encoded = json.dumps(
        payload,
        sort_keys=True,
        separators=(",", ":"),
    ).encode("utf-8")
    return (
        "expression_digest",
        hashlib.sha256(encoded).hexdigest(),
        ("complete", bool(complete)),
        ("root", _expression_descriptor(expr)),
        ("source_atoms", tuple(sorted(source_atoms, key=repr))),
    )


def _expression_provenance_payload(
    expr: Expression,
    *,
    max_nodes: int,
) -> Tuple[StructuralKey, Tuple[StructuralKey, ...], bool]:
    count = 0
    complete = True
    active: set[int] = set()
    source_atoms: set[StructuralKey] = set()
    digest_by_id: dict[int, str] = {}
    stack: list[Tuple[Optional[Expression], bool]] = [(expr, False)]

    none_digest = _digest_structural_payload(("none",))

    while stack:
        node, exiting = stack.pop()
        if node is None:
            continue

        node_id = id(node)
        if exiting:
            active.discard(node_id)
            operand_digests = []
            for operand in getattr(node, "operands", ()) or ():
                operand_digests.append(
                    none_digest if operand is None else digest_by_id.get(id(operand), none_digest)
                )
            payload = (
                "expr",
                _expression_descriptor(node),
                ("value", _stable_value_key(getattr(node, "value", None))),
                ("data_type", getattr(node, "data_type", None)),
                ("storage", _expression_storage_key(node)),
                (
                    "runtime_ref",
                    _semantic_runtime_ref_key(getattr(node, "runtime_ref", None)),
                ),
                ("read_order", getattr(node, "read_order_key", None)),
                ("opcode", getattr(node, "opcode", None)),
                ("operands", tuple(operand_digests)),
            )
            digest_by_id[node_id] = _digest_structural_payload(payload)
            continue

        if node_id in digest_by_id:
            continue
        if count >= max_nodes:
            complete = False
            tail_digest, tail_source_atoms, tail_complete, tail_count = (
                _expression_subtree_digest_and_source_atoms(node)
            )
            source_atoms.update(tail_source_atoms)
            digest_by_id[node_id] = _digest_structural_payload(
                (
                    "truncated",
                    _expression_descriptor(node),
                    ("tail_digest", tail_digest),
                    ("tail_complete", bool(tail_complete)),
                    ("tail_nodes", int(tail_count)),
                )
            )
            continue

        if node_id in active:
            complete = False
            digest_by_id[node_id] = _digest_structural_payload(
                ("cycle", _expression_descriptor(node))
            )
            continue

        count += 1
        active.add(node_id)
        source_atom = _expression_source_atom(node)
        if source_atom is not None:
            source_atoms.add(source_atom)

        stack.append((node, True))
        for operand in reversed(getattr(node, "operands", ()) or ()):
            if operand is not None:
                stack.append((operand, False))

    root_digest = digest_by_id.get(id(expr), none_digest)
    payload = (
        "digest_payload",
        root_digest,
        ("nodes", int(count)),
    )
    return payload, tuple(source_atoms), bool(complete)


def _expression_subtree_digest_and_source_atoms(
    expr: Expression,
) -> Tuple[str, set[StructuralKey], bool, int]:
    count = 0
    complete = True
    active: set[int] = set()
    source_atoms: set[StructuralKey] = set()
    digest_by_id: dict[int, str] = {}
    stack: list[Tuple[Optional[Expression], bool]] = [(expr, False)]
    none_digest = _digest_structural_payload(("none",))

    while stack:
        node, exiting = stack.pop()
        if node is None:
            continue

        node_id = id(node)
        if exiting:
            active.discard(node_id)
            operand_digests = []
            for operand in getattr(node, "operands", ()) or ():
                operand_digests.append(
                    none_digest if operand is None else digest_by_id.get(id(operand), none_digest)
                )
            payload = (
                "expr",
                _expression_descriptor(node),
                ("value", _stable_value_key(getattr(node, "value", None))),
                ("data_type", getattr(node, "data_type", None)),
                ("storage", _expression_storage_key(node)),
                (
                    "runtime_ref",
                    _semantic_runtime_ref_key(getattr(node, "runtime_ref", None)),
                ),
                ("read_order", getattr(node, "read_order_key", None)),
                ("opcode", getattr(node, "opcode", None)),
                ("operands", tuple(operand_digests)),
            )
            digest_by_id[node_id] = _digest_structural_payload(payload)
            continue

        if node_id in digest_by_id and node_id not in active:
            continue
        if node_id in active:
            complete = False
            digest_by_id.setdefault(
                node_id,
                _digest_structural_payload(("cycle", _expression_descriptor(node))),
            )
            continue

        count += 1
        active.add(node_id)
        source_atom = _expression_source_atom(node)
        if source_atom is not None:
            source_atoms.add(source_atom)

        stack.append((node, True))
        for operand in reversed(getattr(node, "operands", ()) or ()):
            if operand is not None:
                stack.append((operand, False))

    return digest_by_id.get(id(expr), none_digest), source_atoms, bool(complete), int(count)


def _digest_structural_payload(payload: StructuralKey) -> str:
    encoded = json.dumps(
        payload,
        sort_keys=True,
        separators=(",", ":"),
    ).encode("utf-8")
    return hashlib.sha256(encoded).hexdigest()


def _expression_descriptor(expr: Expression) -> StructuralKey:
    expr_type = getattr(expr, "expr_type", None)
    expr_type_name = getattr(expr_type, "name", None) or (
        str(expr_type) if expr_type is not None else None
    )
    return (
        expr_type_name,
        getattr(expr, "operator", None),
        getattr(expr, "name", None),
        int(getattr(expr, "size", 0) or 0),
    )


def _expression_source_atom(expr: Expression) -> Optional[StructuralKey]:
    storage_key = _expression_storage_key(expr)
    if storage_key is not None:
        return ("storage", storage_key)
    runtime_key = _semantic_runtime_ref_key(getattr(expr, "runtime_ref", None))
    if runtime_key is not None:
        return ("runtime_ref", runtime_key)
    expr_type = getattr(expr, "expr_type", None)
    expr_type_name = getattr(expr_type, "name", None)
    if expr_type in {
        ExpressionType.PARAMETER,
        ExpressionType.VARIABLE,
        ExpressionType.UNKNOWN,
        ExpressionType.CONSTANT,
        ExpressionType.LITERAL,
    }:
        return (
            "expr_source",
            expr_type_name,
            getattr(expr, "name", None),
            _stable_value_key(getattr(expr, "value", None)),
            int(getattr(expr, "size", 0) or 0),
        )
    return None


def _expression_storage_key(expr: Expression) -> Optional[StructuralKey]:
    storage_info = getattr(expr, "storage_info", None)
    storage_key_fn = getattr(storage_info, "storage_identity_key", None)
    if callable(storage_key_fn):
        try:
            storage_key = storage_key_fn()
            if storage_key is not None:
                return _stable_value_key(storage_key)
        except Exception:
            return None
    return None


def _raw_stable_key_or_none(value: Any) -> Optional[StructuralKey]:
    stable_key = getattr(value, "stable_key", None)
    if callable(stable_key):
        try:
            key = stable_key()
            if key is not None:
                return key
        except Exception:
            pass
    return None


def _stable_value_key(value: Any) -> StructuralKey:
    if value is None:
        return ("none",)
    if isinstance(value, bool):
        return ("bool", int(value))
    if isinstance(value, int):
        return ("int", value)
    if isinstance(value, float):
        return ("float", repr(value))
    if isinstance(value, str):
        return ("str", value)
    if isinstance(value, bytes):
        return ("bytes", value.hex())
    if isinstance(value, Expression):
        return ("expression_ref", _expression_descriptor(value))
    if isinstance(value, Condition):
        return (
            "condition",
            _stable_value_key(value.expression),
            ("negated", bool(value.negated)),
        )
    if isinstance(value, tuple):
        return ("tuple", tuple(_stable_value_key(item) for item in value))
    if isinstance(value, list):
        return ("list", tuple(_stable_value_key(item) for item in value))
    if isinstance(value, dict):
        items = [
            (_stable_value_key(key), _stable_value_key(item))
            for key, item in value.items()
        ]
        items.sort()
        return ("dict", tuple(items))
    stable_key = getattr(value, "stable_key", None)
    if callable(stable_key):
        try:
            return ("stable", _stable_value_key(stable_key()))
        except Exception:
            pass
    return ("opaque", type(value).__module__, type(value).__qualname__)
