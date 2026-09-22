# -*- coding: utf-8 -*-
"""Structural keys for Expression / Condition.

These helpers keep normalization and equivalence internals on the AST/P-code
side instead of round-tripping through rendered strings.
"""

from __future__ import annotations

import hashlib
import json
from typing import Any, Optional, Tuple

from scripts.function_tracer_pcode.core.condition import Condition
from scripts.function_tracer_pcode.core.expression import Expression, ExpressionType
from scripts.function_tracer_pcode.core.semantic_lifecycle import is_validated
from scripts.function_tracer_pcode.core.semantic_projection import (
    canonical_atom as _atom_key,
)
from scripts.function_tracer_pcode.core.semantic_snapshot import (
    COMMUTATIVE_BINARY_OPS,
    children_are_commutative,
    local_semantic_payload,
    ordered_semantic_edges,
    semantic_projection,
)


StructuralKey = Tuple[Any, ...]
#: 可換演算の集合は node の意味なので `semantic_snapshot` が owner。
#: `expression_key` の正規化がそれを読む（再 export は既存 import のため）。
WIDTH_ADAPTER_OPS = frozenset({"INT_ZEXT", "INT_SEXT"})


def _expression_runtime_metadata(expr: Expression) -> tuple[StructuralKey, ...]:
    """structural key に載せる runtime ref の意味 key。

    生 object は読まない。`semantic_projection()` は凍結済みなら固定済みの値を、
    未凍結ならその場で作った値を返す（どちらも pure value）。
    """

    runtime_key = semantic_projection(expr).runtime_structural_key
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

    projection = semantic_projection(expr)
    if projection.parameter_runtime_key is not None:
        return ("runtime_ref", projection.parameter_runtime_key)

    if projection.storage_identity is not None:
        return ("storage", projection.storage_identity)

    if projection.runtime_stable_key is not None:
        return ("runtime_ref", projection.runtime_stable_key)

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
                ("storage", semantic_projection(node).storage_identity),
                ("runtime_ref", semantic_projection(node).runtime_structural_key),
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
                ("storage", semantic_projection(node).storage_identity),
                ("runtime_ref", semantic_projection(node).runtime_structural_key),
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
    projection = semantic_projection(expr)
    semantic_runtime_key = projection.runtime_structural_key
    if projection.parameter_runtime_key is not None:
        return ("runtime_ref", semantic_runtime_key)

    if projection.storage_identity is not None:
        return ("storage", projection.storage_identity)
    if semantic_runtime_key is not None:
        return ("runtime_ref", semantic_runtime_key)
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


# ---------------------------------------------------------------------------
# structural identity（Issue #22 PR-22-B）
# ---------------------------------------------------------------------------
#
# ここは **「2 つの式が同じか」だけ** を所有する。node の意味の分解は
# `core/semantic_snapshot.py`（`local_semantic_payload` / `ordered_semantic_edges`）
# にあり、hash・完全比較・graph snapshot の 3 つは同じ分解を共有する。
#
# 3 つの層を混ぜないこと:
#
#   candidate hash        16 byte。bucket / 早期棄却だけ。**等価の確定にも
#                         外部 identity にも使わない**。衝突は設計上あり得る。
#   equivalence digest    32 byte。完全比較と同じ同値関係を持つ安定 digest。
#                         prefilter に使ってよいが hit は確定しない。
#   完全比較              `structural_equals`。distinct な node 組の数に比例し、
#                         共有部分木を親ごとに再走査しない。**唯一の決定者**。
#
# 表現の digest（辺の順と共有の仕方を残す）は別概念で、graph の owner が持つ:
# `semantic_snapshot.graph_representation_digest()`。
#
# PR-105-A の `SolverQueryIdentity` / `RewriteIdentity` が再利用してよいのは
# `walk_dag()` の graph と `graph_representation_digest()` / `candidate_hash()`
# の **prefilter** まで。一致の確定は各々が自分の完全比較で行う（solver 宣言や
# rewrite 文脈は structural identity が見ていないので、ここの digest では
# 足りない）。

#: 完全比較の既定予算（distinct な node 組の数）。従来の `condition_key`
#: （木の訪問回数 256）と同じ桁で、共有 DAG ではより深くまで比較できる。
DEFAULT_STRUCTURAL_COMPARISON_BUDGET = 256

#: candidate hash の長さ。候補の絞り込み専用なので 16 byte で足りる。
CANDIDATE_DIGEST_SIZE = 16

#: equivalence digest の長さ。外へ出す安定 identity なので広く取る。
EQUIVALENCE_DIGEST_SIZE = 32

#: 2 つの digest が **別物であること** を byte 列の段階で担保する domain
#: separation。同じ入力でも値が一致しないので、片方を他方の代わりに使うと
#: すぐ気づく（どちらも Merkle で同じ正規化を使うが、契約が違う）。
_CANDIDATE_PERSON = b"cand-v1"
_EQUIVALENCE_PERSON = b"equiv-v1"

_NULL_CHILD_DIGEST = b"\x00" * CANDIDATE_DIGEST_SIZE
_NULL_EQUIVALENCE_CHILD_DIGEST = b"\x00" * EQUIVALENCE_DIGEST_SIZE

#: memo の「まだ評価していない」を「評価中（None）」と区別するための番兵。
_MISSING = object()

_validate = None


def _validated(expr: Optional[Expression]) -> Optional[Expression]:
    """identity API の入口で graph を検証する（`core/semantic_freeze.py` が owner）。

    検証済みなら費用ゼロ。未検証なら凍らせることで検証し、閉路はそこで typed
    failure になる。ここで各 API ごとに閉路判定を書かないのは、判定が 2 つある
    と片方だけ直るから。

    **identity layer は公開権限を持たない**。ここで進めるのは VALIDATED まで
    で、`publish` にも `mark_published` にも触れない（`test_architecture_
    boundaries.py` が固定している）。candidate hash を取っただけの精錬中の値が
    solver へ渡せるようになってはいけない。
    """

    global _validate
    if expr is None or is_validated(expr):
        return expr
    if _validate is None:
        from scripts.function_tracer_pcode.core.semantic_freeze import validated

        _validate = validated
    return _validate(expr)


def _encode_atoms(value: Any, parts: list) -> None:
    """atom を **型を落とさずに** 決定的な文字列へ符号化する。

    `repr()` を使わないのは、未知の object が混ざると `id()` が入って run 間で
    digest が変わってしまうため。未知の型は型名だけにする（区別できなくなるが、
    hash は候補の絞り込みなので完全比較が正しく不一致にする）。
    """

    if value is None:
        parts.append("n;")
    elif value is True or value is False:
        parts.append("b1;" if value else "b0;")
    elif isinstance(value, int):
        parts.append("i%d;" % value)
    elif isinstance(value, float):
        parts.append("f%r;" % value)
    elif isinstance(value, str):
        parts.append("s%d:%s;" % (len(value), value))
    elif isinstance(value, bytes):
        parts.append("y%s;" % value.hex())
    elif isinstance(value, (tuple, list)):
        parts.append("(t" if isinstance(value, tuple) else "(l")
        parts.append("%d;" % len(value))
        for item in value:
            _encode_atoms(item, parts)
        parts.append(")")
    else:
        parts.append("o%s.%s;" % (type(value).__module__, type(value).__qualname__))


def _atoms_to_bytes(value: Any) -> bytes:
    parts: list = []
    _encode_atoms(value, parts)
    return "".join(parts).encode("utf-8", "surrogatepass")


def _compose_merkle_digest(
    node: Any,
    child_digests: Tuple[Optional[bytes], ...],
    *,
    digest_size: int,
    person: bytes,
    null_child: bytes,
    payload: Any = None,
) -> bytes:
    """local payload と子 digest から Merkle digest を O(1) で合成する。

    `child_digests` は `ordered_semantic_edges(node)` と同じ並びであること。
    可換二項演算は子 digest を整列してから混ぜるので、完全比較が一致とみなす式は
    同じ digest になる。合成規則を 1 本にしてあるのは、candidate hash と
    equivalence digest で正規化が食い違わないようにするため — 値が違うのは
    `person` による domain separation の結果で、規則の違いではない。

    `payload` は検証中の呼び出し（まだ node へ書いていない local payload）で
    渡す。渡さないと組み直しになり、生 object を読み直してしまう。
    """

    if payload is None:
        payload = local_semantic_payload(node)
    digest = hashlib.blake2b(digest_size=digest_size, person=person)
    digest.update(_atoms_to_bytes(payload.identity_atoms))
    resolved = [null_child if child is None else child for child in child_digests]
    if len(resolved) == 2 and children_are_commutative(node):
        resolved.sort()
    digest.update(b"|%d|" % len(resolved))
    for child in resolved:
        digest.update(child)
    return digest.digest()


def compose_candidate_digest(
    node: Any, child_digests: Tuple[Optional[bytes], ...], *, payload: Any = None
) -> bytes:
    """**候補絞り込み専用** の 16 byte hash（freeze が各 node に付ける）。

    用途は bucket と早期棄却だけ。衝突は起こり得るものとして設計してあり、
    一致の確定にも、外へ出す stable identity にも使ってはいけない。
    """

    return _compose_merkle_digest(
        node,
        child_digests,
        digest_size=CANDIDATE_DIGEST_SIZE,
        person=_CANDIDATE_PERSON,
        null_child=_NULL_CHILD_DIGEST,
        payload=payload,
    )


def compose_equivalence_digest(
    node: Any, child_digests: Tuple[Optional[bytes], ...], *, payload: Any = None
) -> bytes:
    """**完全比較と同じ同値関係** を持つ 32 byte digest（freeze が各 node に付ける）。

    `structural_equals(a, b)` が真なら値が一致する。prefilter として使ってよいが、
    一致の確定は完全比較が行う（逆向きは保証しない）。
    """

    return _compose_merkle_digest(
        node,
        child_digests,
        digest_size=EQUIVALENCE_DIGEST_SIZE,
        person=_EQUIVALENCE_PERSON,
        null_child=_NULL_EQUIVALENCE_CHILD_DIGEST,
        payload=payload,
    )


def candidate_hash(expr: Optional[Expression]) -> Optional[bytes]:
    """式の candidate hash（`None` は式が無いとき）。

    validated graph を前提にする: 未凍結なら入口で検証して凍らせるので、閉路は
    ここで typed failure になり、placeholder の hash が出回ることはない。

    **この値だけで等価を確定しないこと**。候補の絞り込み（bucket / 早期棄却）
    専用で、衝突は `structural_equals` が食い止める。
    """

    expr = _validated(expr)
    if expr is None:
        return None
    return expr.__dict__.get("_structural_hash")


class _ComparisonFrame:
    """完全比較 1 組分の作業状態（明示 stack 用）。"""

    __slots__ = ("key", "alternatives", "alt_index", "pair_index")

    def __init__(self, key, alternatives):
        self.key = key
        self.alternatives = alternatives
        self.alt_index = 0
        self.pair_index = 0


def structural_equals(
    left: Optional[Expression],
    right: Optional[Expression],
    *,
    budget: int = DEFAULT_STRUCTURAL_COMPARISON_BUDGET,
) -> bool:
    """2 つの式が構造的に同じか（DAG-aware な完全比較）。

    費用は **distinct な node 組** の数に比例する。同じ組を 2 回評価しないので、
    共有部分木を親ごとに展開しない。candidate hash は凍結済みどうしの早期棄却に
    だけ使い、一致の確定には使わない（hash を定数にしても判定は変わらない）。

    一致としない場合:

    * 予算超過（比較不能 → cache miss。誤って一致としない）
    * 未知の node 種別（`expression_key` の `opaque` 枝と同じ）
    * 閉路（凍結できない graph。内部不整合なので一致としない）

    互換契約: 旧実装が木の予算内で比較できた式は同じ結果になり、旧実装が予算
    超過で比較不能だった式が新しい DAG 予算で比較できるようになった場合だけ、
    一致を認める（判定能力の改善）。
    """

    # 検証が先、identity shortcut が後。逆にすると `structural_equals(x, x)` が
    # 閉路を含む x でも True を返してしまい、壊れた graph が「同じ」として
    # 通過する。
    left = _validated(left)
    right = _validated(right)
    if left is right:
        # 同じ object、または「両方とも無い」。旧実装の key も `("none",)`
        # どうしを一致として扱っていた。
        return True
    if left is None or right is None:
        return False

    memo: dict[tuple, Optional[bool]] = {}
    remaining = [int(budget)]
    exhausted = [False]

    def _quick(x, y) -> Optional[bool]:
        if x is y:
            # 欠けた operand（二項演算の右辺が無い等）は「両方とも無い」なら
            # 一致。片方だけ無いなら下で不一致になる。
            return True
        if x is None or y is None:
            return False
        known = memo.get((id(x), id(y)), _MISSING)
        if known is _MISSING:
            return None
        if known is None:
            # 評価中の組へ戻ってきた = 閉路。一致としない。
            return False
        return known

    def _open(x, y) -> Optional[_ComparisonFrame]:
        """組の局所比較を行い、子の組み合わせ候補を作る（不一致なら `None`）。"""

        key = (id(x), id(y))
        if remaining[0] <= 0:
            exhausted[0] = True
            memo[key] = False
            return None
        remaining[0] -= 1
        memo[key] = None

        left_payload = local_semantic_payload(x)
        right_payload = local_semantic_payload(y)
        if not left_payload.comparable or not right_payload.comparable:
            memo[key] = False
            return None
        if left_payload.compare_atoms != right_payload.compare_atoms:
            memo[key] = False
            return None

        left_digest = x.__dict__.get("_structural_hash") if hasattr(x, "__dict__") else None
        right_digest = y.__dict__.get("_structural_hash") if hasattr(y, "__dict__") else None
        if left_digest is not None and right_digest is not None and left_digest != right_digest:
            memo[key] = False
            return None

        left_edges = ordered_semantic_edges(x)
        right_edges = ordered_semantic_edges(y)
        if len(left_edges) != len(right_edges):
            memo[key] = False
            return None
        straight = [
            (left_edge.child, right_edge.child)
            for left_edge, right_edge in zip(left_edges, right_edges)
        ]
        alternatives = [straight]
        if len(straight) == 2 and children_are_commutative(x):
            # 可換演算は入れ替えた組み合わせも試す。hash で並びを決めないのは、
            # hash が衝突している場合に取り違えて「違う」と言ってしまうため。
            alternatives.append(
                [(straight[0][0], straight[1][1]), (straight[1][0], straight[0][1])]
            )
        return _ComparisonFrame(key, alternatives)

    frame = _open(left, right)
    if frame is None:
        return False
    stack = [frame]
    result: Optional[bool] = None

    while stack:
        if exhausted[0]:
            return False
        frame = stack[-1]
        if result is not None:
            if result:
                frame.pair_index += 1
            else:
                frame.alt_index += 1
                frame.pair_index = 0
            result = None
        if frame.alt_index >= len(frame.alternatives):
            memo[frame.key] = False
            stack.pop()
            result = False
            continue
        alternative = frame.alternatives[frame.alt_index]
        if frame.pair_index >= len(alternative):
            memo[frame.key] = True
            stack.pop()
            result = True
            continue
        child_left, child_right = alternative[frame.pair_index]
        known = _quick(child_left, child_right)
        if known is not None:
            result = known
            continue
        child_frame = _open(child_left, child_right)
        if child_frame is None:
            result = False
            continue
        stack.append(child_frame)

    return bool(result)


def structural_identity_digest(expr: Optional[Expression]) -> Optional[str]:
    """完全比較と **同じ同値関係** を持つ安定 digest（equivalence digest）。

    `structural_equals(a, b)` が真なら `identity_digest(a) == identity_digest(b)`。
    これは「完全比較の前置き（prefilter）として使ってよい」という契約そのもので、
    逆向き（digest 一致 ⇒ 等価）は保証しない。

    candidate hash とは **別の値**（domain separation 済み）で、契約も違う:
    candidate hash は bucket 専用の 16 byte、こちらは外へ出せる 32 byte の
    安定 identity。混同すると「bucket が一致したから同じ式」という誤用が通って
    しまうので、値そのものを分けてある。

    `id()` にも process 状態にも依存しない。graph のどこかが値として固定でき
    ない object を含み digest だけでは区別できない場合は `None` を返す。
    辺の順や共有の仕方が残る **表現** の digest が要るなら
    `semantic_snapshot.graph_representation_digest()`（別の同値関係）。
    """

    expr = _validated(expr)
    if expr is None:
        return None
    if not expr.__dict__.get("_identity_complete", False):
        return None
    digest = expr.__dict__.get("_equivalence_digest")
    return None if digest is None else digest.hex()


class StructuralIdentity:
    """structural identity の安定 interface（この module が唯一の owner）。

    比較方針を変えたいときに触るのはこの class の実装だけで、consumer
    （`Condition.equals` / dedup / cache）は変わらない。solver query identity や
    rewrite identity と **統合しない**: 同じ式でも solver 宣言や rewrite 文脈が
    違えば別物で、片方の都合で他方の一致条件を動かしてはいけない。
    """

    #: bucket / 早期棄却の専用値（16 byte）。等価の確定にも外部 identity にも
    #: 使わない。衝突は設計上あり得る。
    candidate_hash = staticmethod(candidate_hash)
    #: 完全比較（distinct な node 組に比例、可換正規化あり）。**唯一の決定者**。
    equals = staticmethod(structural_equals)
    #: 予算付きの canonical key（placeholder を含むものは比較に使わない）
    key = staticmethod(expression_key)
    #: 完全比較と同じ同値関係を持つ安定 digest（32 byte、prefilter に使える）
    identity_digest = staticmethod(structural_identity_digest)
