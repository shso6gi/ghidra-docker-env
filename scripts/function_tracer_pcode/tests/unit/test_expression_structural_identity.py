# -*- coding: utf-8 -*-
"""structural identity の契約（Issue #22 PR-22-B、計画 B2 / B3 / B4 / B5 / B14）。

3 つの層を混ぜないことを固定する:

* candidate hash は **候補の絞り込み専用**（決定的・衝突しても安全）
* 完全比較は distinct な node 組に比例し、hash を定数にしても結果が変わらない
* graph digest は `id()` に依存しない
"""

from __future__ import annotations

import random
import subprocess
import sys
import time
from pathlib import Path

import pytest

from scripts.function_tracer_pcode.core.condition import Condition
from scripts.function_tracer_pcode.core.expression import Expression, ExpressionType
from scripts.function_tracer_pcode.core import structural
from scripts.function_tracer_pcode.core.semantic_snapshot import (
    local_semantic_payload,
    ordered_semantic_edges,
    walk_dag,
)
from scripts.function_tracer_pcode.core.storage import StorageInfo


REPO_ROOT = Path(__file__).resolve().parents[4]


class _StableRef:
    """`stable_key()` / `semantic_key()` を持つ runtime ref の代役。"""

    def __init__(self, key):
        self._key = key

    def stable_key(self):
        return self._key

    def semantic_key(self):
        return self._key


def _build_random_expression(rng: random.Random, depth: int, pool: list) -> Expression:
    """全 node 種別と共有を含むランダムな式。"""

    if depth <= 0 or (pool and rng.random() < 0.25):
        kind = rng.randrange(6)
        if kind == 0:
            return Expression.constant(rng.randrange(-8, 64), size=rng.choice([1, 4, 8]))
        if kind == 1:
            return Expression.parameter(f"p{rng.randrange(3)}", rng.randrange(3), size=4)
        if kind == 2:
            return Expression.variable(f"v{rng.randrange(3)}", size=4)
        if kind == 3:
            return Expression.unknown(f"u{rng.randrange(3)}")
        if kind == 4:
            return Expression(ExpressionType.LITERAL, value=f"L{rng.randrange(3)}", size=4)
        if pool:
            return rng.choice(pool)
        return Expression.constant(0, size=4)

    choice = rng.randrange(7)
    if choice == 0:
        return Expression.binary_op(
            rng.choice(["INT_ADD", "INT_SUB", "INT_MULT", "INT_LESS"]),
            _register(_build_random_expression(rng, depth - 1, pool), pool),
            _register(_build_random_expression(rng, depth - 1, pool), pool),
        )
    if choice == 1:
        return Expression.unary_op(
            rng.choice(["INT_ZEXT", "INT_SEXT", "BOOL_NEGATE"]),
            _register(_build_random_expression(rng, depth - 1, pool), pool),
        )
    if choice == 2:
        return Expression.memory(
            _register(_build_random_expression(rng, depth - 1, pool), pool),
            size=rng.choice([1, 4, 8]),
            read_order_key=rng.randrange(3),
            runtime_ref=_StableRef(("mem", rng.randrange(3))),
        )
    if choice == 3:
        return Expression.call(
            f"f{rng.randrange(2)}",
            [
                _register(_build_random_expression(rng, depth - 1, pool), pool)
                for _ in range(rng.randrange(1, 3))
            ],
        )
    if choice == 4:
        return Expression.intrinsic(
            f"i{rng.randrange(2)}",
            [
                _register(_build_random_expression(rng, depth - 1, pool), pool)
                for _ in range(rng.randrange(1, 3))
            ],
            size=4,
            opcode=rng.randrange(3),
        )
    if choice == 5:
        guard = Condition(
            _register(_build_random_expression(rng, depth - 1, pool), pool),
            negated=bool(rng.randrange(2)),
        )
        return Expression.phi(
            [
                (guard, _register(_build_random_expression(rng, depth - 1, pool), pool)),
                (None, _register(_build_random_expression(rng, depth - 1, pool), pool)),
            ]
        )
    return Expression.variable(
        f"s{rng.randrange(3)}",
        size=4,
        storage_info=StorageInfo(is_register=True, register_name=f"r{rng.randrange(3)}"),
        runtime_ref=_StableRef(("parameter", rng.randrange(3), "x")),
    )


def _register(expr: Expression, pool: list) -> Expression:
    if len(pool) < 32:
        pool.append(expr)
    return expr


def _corpus(count: int = 60, seed: int = 20260920):
    rng = random.Random(seed)
    expressions = []
    for _ in range(count):
        pool: list = []
        expressions.append(_build_random_expression(rng, 4, pool))
    return expressions


def _shared_dag(depth: int, *, leaf_name: str = "a") -> Expression:
    """深さ ``depth`` で各段を 2 回参照する DAG（木換算は 2**depth）。"""

    node = Expression.parameter(leaf_name, 0, size=4)
    for _ in range(depth):
        node = Expression.binary_op("INT_SUB", node, node)
    return node


# ---------------------------------------------------------------------------
# B2: candidate hash の決定性
# ---------------------------------------------------------------------------


def test_candidate_hash_is_stable_across_repeated_calls_and_rebuilds():
    for expr in _corpus(30):
        first = structural.candidate_hash(expr)
        second = structural.candidate_hash(expr)
        assert first == second
        expr.freeze()
        assert structural.candidate_hash(expr) == first


def test_candidate_hash_normalises_commutative_operands():
    left = Expression.parameter("a", 0, size=4)
    right = Expression.constant(3, size=4)
    straight = Expression.binary_op("INT_ADD", left, right)
    crossed = Expression.binary_op("INT_ADD", right, left)
    assert structural.candidate_hash(straight) == structural.candidate_hash(crossed)

    non_commutative_straight = Expression.binary_op("INT_SUB", left, right)
    non_commutative_crossed = Expression.binary_op("INT_SUB", right, left)
    assert structural.candidate_hash(non_commutative_straight) != structural.candidate_hash(
        non_commutative_crossed
    )


def test_candidate_hash_does_not_depend_on_the_process_hash_seed():
    script = (
        "import sys; sys.path.insert(0, %r)\n"
        "from scripts.function_tracer_pcode.core.expression import Expression\n"
        "from scripts.function_tracer_pcode.core.structural import candidate_hash\n"
        "class R:\n"
        "    def stable_key(self):\n"
        "        return ('mem', 1)\n"
        "    def semantic_key(self):\n"
        "        return ('mem', 1)\n"
        "expr = Expression.binary_op('INT_ADD',\n"
        "    Expression.memory(Expression.parameter('a', 0, size=8), size=4, runtime_ref=R()),\n"
        "    Expression.constant(5, size=4))\n"
        "expr.freeze()\n"
        "print(candidate_hash(expr).hex())\n"
    ) % str(REPO_ROOT)

    digests = set()
    for seed in ("0", "1", "12345"):
        completed = subprocess.run(
            [sys.executable, "-B", "-c", script],
            cwd=str(REPO_ROOT),
            capture_output=True,
            text=True,
            env={"PYTHONHASHSEED": seed, "PATH": "/usr/bin:/bin"},
            check=True,
        )
        digests.add(completed.stdout.strip())
    assert len(digests) == 1, digests


def test_opaque_values_hash_by_tag_only_but_stay_distinguishable_by_comparison():
    class Opaque:
        pass

    first = Expression(ExpressionType.LITERAL, value=Opaque(), size=4)
    second = Expression(ExpressionType.LITERAL, value=Opaque(), size=4)
    assert structural.candidate_hash(first) == structural.candidate_hash(second)
    # hash は同じでも完全比較は別の object を同一視しない。
    assert structural.structural_equals(first, second) is False
    assert structural.structural_equals(first, first) is True


# ---------------------------------------------------------------------------
# B3: I-1（expression_key が一致するなら candidate hash も一致する）
# ---------------------------------------------------------------------------


def test_equal_structural_keys_imply_equal_candidate_hashes():
    corpus = _corpus(80)
    by_key = {}
    collisions = 0
    for expr in corpus:
        key = structural.expression_key_safe(expr, budget=4096)
        if key is None:
            continue
        digest = structural.candidate_hash(expr)
        if key in by_key:
            collisions += 1
            assert by_key[key] == digest, "expression_key matched but candidate hash did not"
        by_key[key] = digest
    assert collisions > 0, "corpus did not produce any structurally equal pair"


def test_local_payload_and_expression_key_react_to_the_same_fields():
    """identity の field 集合が `expression_key` と食い違っていないこと。

    hash / 完全比較 / graph snapshot は `local_semantic_payload` を、`expression_key`
    は自前の分解を見る。片方だけが見る field があると「key は同じなのに hash が
    違う」（または逆）が起きるので、field を 1 つずつ動かして両方が反応することを
    確認する。
    """

    base = Expression.memory(
        Expression.parameter("a", 0, size=8),
        size=4,
        read_order_key=1,
        runtime_ref=_StableRef(("mem", 1)),
    )
    variants = {
        "size": base.clone_with(size=8),
        "read_order_key": base.clone_with(read_order_key=2),
        "runtime_ref": base.clone_with(runtime_ref=_StableRef(("mem", 2))),
    }
    base_key = structural.expression_key(base)
    base_payload = local_semantic_payload(base)
    for label, variant in variants.items():
        assert structural.expression_key(variant) != base_key, label
        assert local_semantic_payload(variant).compare_atoms != base_payload.compare_atoms, label

    named = Expression.variable("v", size=4)
    renamed = named.clone_with(name="w")
    assert structural.expression_key(named) != structural.expression_key(renamed)
    assert (
        local_semantic_payload(named).compare_atoms
        != local_semantic_payload(renamed).compare_atoms
    )

    call = Expression.call("f", [Expression.constant(1, 4)])
    longer = Expression.call("f", [Expression.constant(1, 4), Expression.constant(1, 4)])
    assert structural.expression_key(call) != structural.expression_key(longer)
    assert (
        local_semantic_payload(call).compare_atoms
        != local_semantic_payload(longer).compare_atoms
    )


# ---------------------------------------------------------------------------
# B4: 衝突しても完全比較が食い止める
# ---------------------------------------------------------------------------


def test_forced_hash_collisions_do_not_change_equality_or_dedup(monkeypatch):
    corpus = _corpus(40)
    for expr in corpus:
        expr.freeze()
    pairs = [(a, b) for a in corpus[:12] for b in corpus[:12]]
    before = [structural.structural_equals(a, b) for a, b in pairs]

    constant = b"\x00" * structural.CANDIDATE_DIGEST_SIZE
    monkeypatch.setattr(
        structural, "compose_candidate_digest", lambda node, child_digests: constant
    )
    for expr in corpus:
        expr.__dict__["_structural_hash"] = constant

    after = [structural.structural_equals(a, b) for a, b in pairs]
    assert before == after


def test_commutative_pairing_survives_a_degenerate_hash(monkeypatch):
    left = Expression.parameter("a", 0, size=4)
    right = Expression.constant(3, size=4)
    straight = Expression.binary_op("INT_ADD", left, right)
    crossed = Expression.binary_op("INT_ADD", right, left)
    constant = b"\x01" * structural.CANDIDATE_DIGEST_SIZE
    monkeypatch.setattr(
        structural, "compose_candidate_digest", lambda node, child_digests: constant
    )
    assert structural.structural_equals(straight, crossed) is True


def test_equal_conditions_agree_with_their_hash_bucket():
    left = Expression.parameter("a", 0, size=4)
    right = Expression.constant(3, size=4)
    first = Condition(Expression.binary_op("INT_ADD", left, right))
    second = Condition(Expression.binary_op("INT_ADD", right, left))
    assert first.equals(second) is True
    assert hash(first) == hash(second)
    assert first.negate().equals(second) is False


# ---------------------------------------------------------------------------
# B5: 共有 DAG を木として展開しない
# ---------------------------------------------------------------------------


def test_deeply_shared_dag_is_compared_in_distinct_node_time():
    depth = 40
    left = _shared_dag(depth)
    right = _shared_dag(depth)
    left.freeze()
    right.freeze()
    # 木に展開すると 2**40 node。凍結時の木換算 node 数がそれを示す。
    assert left.tree_size() > 2 ** depth

    started = time.monotonic()
    assert structural.structural_equals(left, right, budget=4096) is True
    assert structural.candidate_hash(left) == structural.candidate_hash(right)
    # key の **生成** も distinct node に比例する（子 key object を共有するため）。
    structural.expression_key(left, budget=4096)
    elapsed = time.monotonic() - started
    assert elapsed < 1.0, elapsed


def test_equality_is_decided_by_full_comparison_not_by_comparing_two_keys():
    """key どうしの比較は DAG 向きではない、という設計上の理由の固定。

    `expression_key` の memo は 1 回の生成の中でしか子 key を共有しないので、
    別々に作った 2 つの key を `==` で比べると、共有部分木が木として展開され
    比較費用が指数になる。だから等価の判定は `structural_equals`（distinct な
    node 組で memo する完全比較）が行い、`Condition.equals` もそれを使う。
    """

    depth = 22
    left = _shared_dag(depth)
    right = _shared_dag(depth)
    started = time.monotonic()
    assert structural.structural_equals(left, right, budget=4096) is True
    full_comparison_seconds = time.monotonic() - started

    started = time.monotonic()
    assert structural.expression_key(left, budget=4096) == structural.expression_key(
        right, budget=4096
    )
    key_comparison_seconds = time.monotonic() - started

    assert full_comparison_seconds < 0.5
    assert key_comparison_seconds > full_comparison_seconds


def test_walk_dag_visits_each_distinct_node_once():
    depth = 40
    root = _shared_dag(depth)
    root.freeze()
    graph = walk_dag(root)
    assert graph.distinct_node_count == depth + 1
    assert graph.edge_count == depth * 2


def test_structural_comparison_budget_counts_distinct_pairs_not_tree_positions():
    depth = 30
    left = _shared_dag(depth)
    right = _shared_dag(depth)
    # distinct な組は depth + 1 個。木の位置で数えていたら足りない予算。
    assert structural.structural_equals(left, right, budget=depth + 1) is True
    assert structural.structural_equals(left, right, budget=depth // 2) is False


# ---------------------------------------------------------------------------
# B14: 互換契約
# ---------------------------------------------------------------------------


def test_previously_truncated_comparisons_may_now_succeed():
    depth = 12
    left = _shared_dag(depth)
    right = _shared_dag(depth)
    # 旧実装は木として走査するので、木換算 4096 node に対して予算 256 では
    # 必ず placeholder になり、比較不能（= 不一致）だった。
    assert left.freeze().tree_size() > 256
    assert structural.structural_equals(left, right) is True


def test_budget_exhaustion_never_reports_equality():
    left = _shared_dag(30, leaf_name="a")
    right = _shared_dag(30, leaf_name="b")
    assert structural.structural_equals(left, right, budget=4) is False
    assert structural.structural_equals(left, left, budget=1) is True


def test_missing_operands_match_only_when_both_sides_are_missing():
    """欠けた operand は「両方とも無い」ときだけ一致（旧 key と同じ扱い）。"""

    complete = Expression.binary_op(
        "INT_SUB", Expression.parameter("a", 0, size=4), Expression.constant(1, size=4)
    )
    truncated = complete.clone_with(operands=[Expression.parameter("a", 0, size=4)])
    other_truncated = complete.clone_with(operands=[Expression.parameter("a", 0, size=4)])

    assert structural.structural_equals(truncated, other_truncated) is True
    assert structural.structural_equals(truncated, complete) is False
    assert structural.structural_equals(None, None) is True
    assert structural.structural_equals(None, complete) is False


def test_unknown_node_kinds_are_never_equal():
    class FakeKind:
        name = "MADE_UP"

    first = Expression.constant(1, 4)
    second = Expression.constant(1, 4)
    first.__dict__["expr_type"] = FakeKind()
    second.__dict__["expr_type"] = FakeKind()
    assert local_semantic_payload(first).comparable is False
    assert structural.structural_equals(first, second) is False


def test_cyclic_graphs_are_never_reported_equal():
    left = Expression.unary_op("BOOL_NEGATE", Expression.constant(1, 1))
    left.__dict__["operands"] = [left]
    right = Expression.unary_op("BOOL_NEGATE", Expression.constant(1, 1))
    right.__dict__["operands"] = [right]
    assert structural.structural_equals(left, right) is False


def test_graph_digest_is_independent_of_object_identity():
    first = _shared_dag(6)
    second = _shared_dag(6)
    first.freeze()
    second.freeze()
    assert structural.structural_identity_digest(first) == structural.structural_identity_digest(
        second
    )
    other = _shared_dag(6, leaf_name="b")
    assert structural.structural_identity_digest(other) != structural.structural_identity_digest(
        first
    )


def test_graph_digest_refuses_incomplete_identity():
    class Opaque:
        pass

    expr = Expression(ExpressionType.LITERAL, value=Opaque(), size=4)
    expr.freeze()
    assert structural.structural_identity_digest(expr) is None


def test_ordered_edges_follow_the_key_traversal_order():
    guard = Condition(Expression.parameter("a", 0, size=4))
    value = Expression.constant(1, 4)
    other = Expression.constant(2, 4)
    phi = Expression.phi([(guard, value), (None, other)])
    labels = [edge.label for edge in ordered_semantic_edges(phi)]
    assert labels == [
        ("phi_condition", 0),
        ("phi_value", 0),
        ("phi_condition", 1),
        ("phi_value", 1),
    ]
