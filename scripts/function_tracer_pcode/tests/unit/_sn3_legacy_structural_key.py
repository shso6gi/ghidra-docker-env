# -*- coding: utf-8 -*-
"""main（`2f30b9f`）の `core/structural.expression_key` の写し（Issue #215 の差分比較用）。

**production では使わない**。`test_sn3_exact_structural_key.py` が「打ち切りの無い key は
main と同じ値」（C-K2(a)）を比べる相手として読むだけ。本体に手を入れないこと。
"""

from __future__ import annotations

from typing import Optional

from scripts.function_tracer_pcode.core.expression import Expression, ExpressionType
from scripts.function_tracer_pcode.core.semantic_projection import canonical_atom as _atom_key
from scripts.function_tracer_pcode.core.semantic_snapshot import COMMUTATIVE_BINARY_OPS
from scripts.function_tracer_pcode.core.semantic_snapshot import semantic_projection
from scripts.function_tracer_pcode.core.structural import (
    StructuralKey,
    WIDTH_ADAPTER_OPS,
    _is_all_ones_mask_for_size,
)


def _expression_runtime_metadata(expr: Expression) -> tuple:
    """main の `_expression_runtime_metadata` の写し（SN3 は識別不能な atom の置き換えを足した）。"""

    runtime_key = semantic_projection(expr).runtime_structural_key
    if runtime_key is None:
        return ()
    return (("runtime_ref", runtime_key),)


def legacy_expression_key(
    expr: Optional[Expression],
    *,
    budget: int = 256,
    normalize_commutative: bool = True,
    strip_width_adapters: bool = False,
    collapse_full_masks: bool = False,
    include_memory_read_order: bool = True,
    include_semantic_runtime_refs: bool = True,
) -> StructuralKey:
    """Return a stable, hashable structural key for an expression tree.

    The traversal is DAG-aware: a node reached twice is built once and its key
    object is reused, so ``budget`` counts *distinct* nodes instead of tree
    positions and a shared subgraph is not re-walked per parent.  Sharing the
    key objects also makes comparing two keys cheap, because tuple comparison
    short-circuits on identical elements.

    A key that carries a placeholder (``truncated`` / ``cycle`` / ``opaque``) is
    deliberately *not* memoised: a placeholder describes the position it was
    produced in -- the remaining budget, or the path that reached the node --
    and reusing it elsewhere would report a node as unresolved when it is not.

    **これは construction-safe な legacy key であって、validated identity API
    ではない**。lifecycle を進めない（`validated()` を呼ばない）し、未検証の
    graph でも答えを返す。閉路も予算切れも `("cycle", …)` / `("truncated", …)`
    の placeholder で表し、consumer は `key_contains_placeholder()` で「どこま
    で見えているか」を判断する。

    意図的にそうしてある理由は 2 つ:

    * 解析の途中（まだ組み立て中の式）を鍵にする consumer が居る。ここで
      検証を要求すると、構築中の graph に identity の契約を持ち込むことになる
    * この key は `object_target_key` 等の preimage に入っていて、reason
      identity として外へ出る。形を変えると判定名が広く動く

    「この graph は identity を計算してよい形か」を要求するのは
    `candidate_hash()` / `structural_equals()` / `structural_identity_digest()`
    の 3 つで、そちらは入口で `validated()` を通し、閉路は typed failure に
    なる（placeholder を作らない）。
    """

    visited: set[int] = set()
    memo: dict[int, StructuralKey] = {}
    # 予算と placeholder 件数は再帰の外で数える（key の memo 可否の判定に使う）。
    state = {"remaining": int(budget), "placeholders": 0}

    def _build(node: Optional[Expression]) -> StructuralKey:
        if node is None:
            return ("none",)
        node_id = id(node)
        cached = memo.get(node_id)
        if cached is not None:
            return cached
        if state["remaining"] <= 0:
            state["placeholders"] += 1
            return (
                "truncated",
                node.expr_type.name,
                node.operator or "",
                node.name or "",
                int(node.size or 0),
            )
        if node_id in visited:
            state["placeholders"] += 1
            return ("cycle", node.expr_type.name, node.name or "", int(node.size or 0))

        visited.add(node_id)
        placeholders_before = state["placeholders"]
        try:
            state["remaining"] -= 1
            key = _build_node(node)
        finally:
            visited.discard(node_id)
        if state["placeholders"] == placeholders_before:
            memo[node_id] = key
        return key

    def _build_node(node: Expression) -> StructuralKey:
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
                return _build(right)
            if _is_all_ones_mask_for_size(right, mask_size):
                return _build(left)

        expr_type = current.expr_type

        if expr_type == ExpressionType.CONSTANT:
            return ("const", _atom_key(current.value), int(current.size or 0))

        if expr_type == ExpressionType.LITERAL:
            return ("literal", _atom_key(current.value), int(current.size or 0))

        if expr_type in {ExpressionType.PARAMETER, ExpressionType.VARIABLE}:
            return (
                expr_type.name.lower(),
                current.name or "",
                _atom_key(current.value),
                int(current.size or 0),
            )

        if expr_type == ExpressionType.UNKNOWN:
            runtime_metadata = (
                _expression_runtime_metadata(current) if include_semantic_runtime_refs else ()
            )
            return (
                "unknown",
                current.name or "",
                _atom_key(current.value),
                int(current.size or 0),
                *runtime_metadata,
            )

        if expr_type == ExpressionType.UNARY_OP:
            operand = current.operands[0] if current.operands else None
            return (
                "unary",
                current.operator or "",
                int(current.size or 0),
                _build(operand),
            )

        if expr_type == ExpressionType.BINARY_OP:
            left = current.operands[0] if current.operands else None
            right = current.operands[1] if len(current.operands) > 1 else None
            left_key = _build(left)
            right_key = _build(right)
            if normalize_commutative and (current.operator or "") in COMMUTATIVE_BINARY_OPS:
                if right_key < left_key:
                    left_key, right_key = right_key, left_key
            return (
                "binary",
                current.operator or "",
                int(current.size or 0),
                left_key,
                right_key,
            )

        if expr_type == ExpressionType.MEMORY:
            address = current.operands[0] if current.operands else None
            address_key = _build(address)
            runtime_metadata = (
                _expression_runtime_metadata(current) if include_semantic_runtime_refs else ()
            )
            return (
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
            )

        if expr_type == ExpressionType.CALL:
            return (
                "call",
                current.name or "",
                int(current.size or 0),
                tuple(_build(operand) for operand in current.operands),
            )

        if expr_type == ExpressionType.INTRINSIC:
            return (
                "intrinsic",
                current.name or "",
                None if getattr(current, "opcode", None) is None else int(current.opcode),
                int(current.size or 0),
                tuple(_build(operand) for operand in current.operands),
            )

        if expr_type == ExpressionType.PHI:
            branches = []
            for condition, value in current.value or []:
                cond_key: StructuralKey
                if condition is None:
                    cond_key = ("none",)
                else:
                    cond_key = ("cond", _build(condition.expression), bool(condition.negated))
                branches.append((cond_key, _build(value)))
            return ("phi", int(current.size or 0), tuple(branches))

        state["placeholders"] += 1
        return (
            "opaque",
            expr_type.name,
            current.operator or "",
            current.name or "",
            int(current.size or 0),
        )

    return _build(expr)
