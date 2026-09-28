# -*- coding: utf-8 -*-
"""Issue #215（SN3）: 予算付き構造 key の厳密化（C-K1〜C-K8）。

main（`2f30b9f`）では、予算を使い切った先が ``("truncated", type, op, name, size)``
になり中身を識別しないので、**末尾だけが違う 2 つの式が同じ key** になる。さらに
placeholder の検出は CALL / INTRINSIC / PHI の子を見ない。ここでは key の契約を
`core/structural.py` の側で固定する（consumer 側の test は `test_sn3_consumers.py`、
process 境界は `test_sn3_cross_process_identity.py`）。

記号は Issue #215: o = 5 つの option、T_o(n) = option o の下で n を予算無しに展開した木。
"""

from __future__ import annotations

import itertools
import json
import os
import subprocess
import sys
import threading
from pathlib import Path

import pytest

from scripts.function_tracer_pcode.core.condition import Condition
from scripts.function_tracer_pcode.core.expression import Expression, ExpressionType
from scripts.function_tracer_pcode.core import structural
from scripts.function_tracer_pcode.core.structural import (
    condition_key,
    expression_key,
    expression_key_or_identity,
    expression_key_safe,
    key_contains_placeholder,
    key_is_comparable,
    structural_equals,
)

REPO_ROOT = Path(__file__).resolve().parents[4]
OPTION_NAMES = (
    "normalize_commutative",
    "strip_width_adapters",
    "collapse_full_masks",
    "include_memory_read_order",
    "include_semantic_runtime_refs",
)


# --------------------------------------------------------------------------
# builders
# --------------------------------------------------------------------------

def _param(name="a", index=0, size=4):
    return Expression.parameter(name, index, size=size)


def _const(value, size=4):
    return Expression.constant(value, size=size)


def _binary(operator, left, right, size=4):
    expr = Expression.binary_op(operator, left, right)
    expr.size = size
    return expr


def _unary(operator, operand, size=4):
    expr = Expression.unary_op(operator, operand)
    expr.size = size
    return expr


def _call(name, *operands, size=4):
    return Expression(ExpressionType.CALL, name=name, operands=list(operands), size=size)


def _intrinsic(name, *operands, size=4):
    return Expression(ExpressionType.INTRINSIC, name=name, operands=list(operands), size=size)


def _phi(*branches, size=4):
    return Expression(ExpressionType.PHI, value=list(branches), size=size)


def _chain(tail, depth, *, base=None):
    """``a + 0 + 1 + … + (depth-1) + tail``。末尾の定数だけが違う式を作る。"""

    node = base if base is not None else _param()
    for index in range(depth):
        node = _binary("INT_ADD", node, _const(index))
    return _binary("INT_ADD", node, _const(tail))


def _wrap(kind, inner):
    if kind == "top":
        return inner
    if kind == "call":
        return _call("f", inner)
    if kind == "intrinsic":
        return _intrinsic("g", inner)
    if kind == "phi":
        return _phi((None, inner))
    if kind == "phi_condition":
        return _phi((Condition(inner), _const(0)), (None, _const(1)))
    if kind == "unary":
        return _unary("INT_NEGATE", inner)
    raise AssertionError(kind)


# --------------------------------------------------------------------------
# C-K1: 末尾だけ違う深い式は同じ key にならない
# --------------------------------------------------------------------------

@pytest.mark.parametrize("budget", [32, 48, 96, 256])
@pytest.mark.parametrize("kind", ["top", "call", "intrinsic", "phi", "phi_condition", "unary"])
def test_deep_tail_that_differs_only_beyond_the_budget_gets_a_different_key(kind, budget):
    depth = budget * 2
    left = expression_key(_wrap(kind, _chain(1, depth)), budget=budget)
    right = expression_key(_wrap(kind, _chain(2, depth)), budget=budget)
    same = expression_key(_wrap(kind, _chain(1, depth)), budget=budget)

    assert left != right
    # 打ち切りの先も識別しているので、同じ構造を別 object で組めば等しい（C-K2(b)）
    assert left == same
    assert key_contains_placeholder(left)


def test_deep_conditions_with_a_different_tail_get_different_condition_keys():
    left = Condition(_binary("INT_SLESS", _chain(1, 400), _const(10), size=1))
    right = Condition(_binary("INT_SLESS", _chain(2, 400), _const(10), size=1))
    assert condition_key(left) != condition_key(right)
    assert condition_key(left, budget=96) != condition_key(right, budget=96)


def test_a_different_budget_never_makes_different_structures_equal():
    # 同じ構造でも打ち切り位置が違えば key は違ってよい（C-K2(c)）が、違う構造が
    # budget の組み合わせで等しくなることは無い（C-K1 は budget を問わない）
    a = _wrap("call", _chain(1, 200))
    b = _wrap("call", _chain(2, 200))
    for left_budget, right_budget in itertools.product((4, 32, 96, 256, 10_000), repeat=2):
        assert expression_key(a, budget=left_budget) != expression_key(b, budget=right_budget)


# --------------------------------------------------------------------------
# C-K3: 入れ子の placeholder を見落とさない
# --------------------------------------------------------------------------

@pytest.mark.parametrize("kind", ["call", "intrinsic", "phi", "phi_condition", "unary"])
def test_a_nested_placeholder_is_detected_at_any_depth(kind):
    key = expression_key(_wrap(kind, _chain(1, 200)), budget=96)
    assert key_contains_placeholder(key)
    assert not key_is_comparable(key)
    assert expression_key_safe(_wrap(kind, _chain(1, 200)), budget=96) is None


def test_detection_sees_every_nested_tuple_and_a_shared_tuple_only_once():
    deep = ("truncated", "BINARY_OP", "INT_ADD", "", 4, ("exact_tail", "0" * 64, 0))
    shared = ("binary", "INT_ADD", 4, ("const", ("int", 1), 4), ("const", ("int", 2), 4))
    nested = ("call", "f", 4, ((("x", shared),) * 50, (shared, (deep,))))
    assert key_contains_placeholder(nested)
    assert not key_contains_placeholder(("call", "f", 4, ((("x", shared),) * 50,)))
    # 永続化で list になった key も辿れる
    assert key_contains_placeholder(json.loads(json.dumps(nested)))


def test_a_key_without_placeholders_is_comparable():
    key = expression_key(_chain(1, 10))
    assert key_is_comparable(key)


# --------------------------------------------------------------------------
# C-K2(a): 打ち切りの無い key は main と同じ値
# --------------------------------------------------------------------------

def _legacy_expression_key(expr, **kwargs):
    """main（`2f30b9f`）の `expression_key` そのまま（C-K2(a) の差分比較の相手）。"""

    from scripts.function_tracer_pcode.tests.unit import _sn3_legacy_structural_key as legacy

    return legacy.legacy_expression_key(expr, **kwargs)


def _corpus_without_truncation():
    a, b = _param("a", 0), _param("b", 1)
    shared = _binary("INT_ADD", a, b)
    memory = Expression(ExpressionType.MEMORY, operands=[shared], size=4)
    memory.read_order_key = 7
    items = [
        a,
        _const(0),
        _const(-1),
        _binary("INT_ADD", a, b),
        _binary("INT_ADD", b, a),
        _binary("INT_SUB", b, a),
        _binary("INT_MULT", shared, shared),
        _unary("INT_ZEXT", a, size=8),
        _binary("INT_AND", a, _const(0xFFFFFFFF)),
        memory,
        _call("f", a, _const(3)),
        _intrinsic("g", shared),
        _phi((Condition(_binary("INT_SLESS", a, b, size=1)), a), (None, b)),
        _phi((Condition(_binary("INT_SLESS", a, b, size=1), True), a), (None, b)),
        Expression(ExpressionType.UNKNOWN, name="u", size=4),
        Expression(ExpressionType.LITERAL, value="lit", size=4),
        Expression(ExpressionType.VARIABLE, name="v", size=4),
        _chain(3, 20),
    ]
    return items


@pytest.mark.parametrize("options", [
    dict(zip(OPTION_NAMES, bits)) for bits in itertools.product((False, True), repeat=5)
])
def test_keys_without_placeholders_are_the_same_values_as_main(options):
    for expr in _corpus_without_truncation():
        legacy = _legacy_expression_key(expr, **options)
        if key_contains_placeholder(legacy):
            continue
        assert expression_key(expr, **options) == legacy


def test_the_legacy_relation_is_kept_on_keys_without_placeholders():
    corpus = _corpus_without_truncation()
    for left, right in itertools.product(corpus, repeat=2):
        assert (expression_key(left) == expression_key(right)) == (
            _legacy_expression_key(left) == _legacy_expression_key(right)
        )


# --------------------------------------------------------------------------
# C-K8: DAG の共有に依存しない。打ち切り位置は共有に依存してよい（C-K2(c)）
# --------------------------------------------------------------------------

def _doubling(depth, *, shared):
    if depth == 0:
        return _param()
    if shared:
        child = _doubling(depth - 1, shared=True)
        return _binary("INT_ADD", child, child)
    return _binary("INT_ADD", _doubling(depth - 1, shared=False), _doubling(depth - 1, shared=False))


def test_the_tail_token_does_not_depend_on_dag_sharing():
    shared = _doubling(10, shared=True)
    unshared = _doubling(10, shared=False)
    assert structural.exact_tail_token(shared) == structural.exact_tail_token(unshared)


def test_an_untruncated_key_does_not_depend_on_dag_sharing():
    assert expression_key(_doubling(5, shared=True), budget=10_000) == expression_key(
        _doubling(5, shared=False), budget=10_000
    )


def test_the_truncation_position_may_depend_on_sharing_which_is_not_a_soundness_failure():
    # 共有版は distinct node が 11 個で予算内、非共有版は 63 個で打ち切られる。
    # key は違ってよいが（C-K2(c)）、違う構造を等しくはしない（C-K1）。
    shared = expression_key(_doubling(5, shared=True), budget=16)
    unshared = expression_key(_doubling(5, shared=False), budget=16)
    assert not key_contains_placeholder(shared)
    assert key_contains_placeholder(unshared)
    assert shared != unshared


# --------------------------------------------------------------------------
# C-K8: cycle は現在の path 上の距離（back_ref）で表す
# --------------------------------------------------------------------------

def _cycle(length, *, leaf="a", target_offset=0):
    """長さ length の閉路（葉は param leaf）。target_offset だけ深い node へ戻る。"""

    # node_i = (次の node) + (leaf + i)。最後の node は target_offset 番目へ戻る
    nodes = [
        _binary("INT_ADD", _param("placeholder"), _binary("INT_ADD", _param(leaf), _const(index)))
        for index in range(length)
    ]
    for index in range(length - 1):
        nodes[index].operands[0] = nodes[index + 1]
    nodes[-1].operands[0] = nodes[target_offset]
    return nodes[0]


@pytest.mark.parametrize("budget", [4, 256])
def test_the_same_cycle_gets_the_same_key(budget):
    assert expression_key(_cycle(3), budget=budget) == expression_key(_cycle(3), budget=budget)


@pytest.mark.parametrize("budget", [4, 256])
def test_cycles_with_different_back_references_get_different_keys(budget):
    base = expression_key(_cycle(3), budget=budget)
    assert base != expression_key(_cycle(4), budget=budget)  # 距離が違う
    assert base != expression_key(_cycle(3, target_offset=1), budget=budget)  # 戻り先が違う
    outside = _binary("INT_ADD", _cycle(3), _const(1))
    outside_other = _binary("INT_ADD", _cycle(3), _const(2))
    assert expression_key(outside, budget=budget) != expression_key(outside_other, budget=budget)
    assert key_contains_placeholder(base)


@pytest.mark.parametrize("budget", [1, 2, 3])
def test_a_cycle_inside_a_truncated_tail_is_identified_by_its_back_references(budget):
    # 打ち切った先（tail token の中）に閉路がある: back_ref で識別され、同じ形は等しい
    same = expression_key(_cycle(6), budget=budget)
    assert same == expression_key(_cycle(6), budget=budget)
    assert structural.UNIDENTIFIED_TAG not in json.dumps(same)
    assert same != expression_key(_cycle(7), budget=budget)
    assert same != expression_key(_cycle(6, target_offset=2), budget=budget)
    assert same != expression_key(_cycle(6, leaf="b"), budget=budget)


def test_a_cycle_through_a_collapsed_mask_terminates_and_is_identified():
    # V_o が別 node へ解ける（全 bit の mask を剥がす）閉路も、解いた後の node で止まる
    a = _param()
    inner = _binary("INT_ADD", a, _const(1))
    masked = _binary("INT_AND", inner, _const(0xFFFFFFFF))
    inner.operands[0] = masked
    key = expression_key(_binary("INT_ADD", masked, _const(2)), budget=1, collapse_full_masks=True)
    assert key == expression_key(_binary("INT_ADD", masked, _const(2)), budget=1, collapse_full_masks=True)
    assert structural.UNIDENTIFIED_TAG not in json.dumps(key)


def test_a_cycle_is_never_equal_to_an_acyclic_unfolding():
    cyclic = expression_key(_cycle(2), budget=256)
    unfolded = expression_key(_chain(0, 6), budget=256)
    assert cyclic != unfolded


def test_a_frozen_graph_cannot_contain_a_cycle():
    from scripts.function_tracer_pcode.core.semantic_freeze import freeze_expression

    with pytest.raises(Exception):
        freeze_expression(_cycle(3))


# --------------------------------------------------------------------------
# C-K4: memo は option ごとに分かれる（順序を変えても汚染しない）
# --------------------------------------------------------------------------

def _option_sensitive(name):
    """option `name` の on / off で T_o が変わる式の組。違いは **打ち切られた先** にある。

    DFS は左から辿るので、左の長い chain が予算を使い切り、右の `tail` が
    `("truncated", …, token)` になる。したがって違いは tail token だけが見る。
    """

    a, b = _param("a", 0), _param("b", 1)
    if name == "normalize_commutative":
        pair = (_binary("INT_ADD", b, a), _binary("INT_ADD", a, b))
    elif name == "strip_width_adapters":
        pair = (_unary("INT_ZEXT", a), a)
    elif name == "collapse_full_masks":
        pair = (_binary("INT_AND", a, _const(0xFFFFFFFF)), a)
    elif name == "include_memory_read_order":
        first = Expression(ExpressionType.MEMORY, operands=[a], size=4)
        first.read_order_key = 1
        second = Expression(ExpressionType.MEMORY, operands=[a], size=4)
        second.read_order_key = 2
        pair = (first, second)
    elif name == "include_semantic_runtime_refs":
        from scripts.function_tracer_pcode.core.runtime_refs.locations import AddressValueRef

        pair = tuple(
            Expression(ExpressionType.UNKNOWN, name="u", size=4, runtime_ref=AddressValueRef(address_offset=offset))
            for offset in (0x1000, 0x2000)
        )
    else:
        raise AssertionError(name)
    return tuple(
        _binary("INT_ADD", _chain(0, 30), _binary("INT_ADD", _chain(9, 3, base=tail), _const(1)))
        for tail in pair
    )


def _equal_when(name):
    """option が on のとき等しい（True）か off のとき等しい（False）か。"""

    return name in {"normalize_commutative", "strip_width_adapters", "collapse_full_masks"}


@pytest.mark.parametrize("frozen", [False, True])
@pytest.mark.parametrize("first", [True, False])
@pytest.mark.parametrize("name", OPTION_NAMES)
def test_memo_is_partitioned_by_every_option_in_either_order(name, first, frozen):
    from scripts.function_tracer_pcode.core.semantic_freeze import freeze_expression

    left, right = _option_sensitive(name)
    if frozen:
        left, right = freeze_expression(left), freeze_expression(right)
    equal_when_on = _equal_when(name)
    for value in (first, not first):
        options = {name: value}
        same = expression_key(left, budget=16, **options) == expression_key(right, budget=16, **options)
        assert same == (value == equal_when_on), (name, value)
        tokens = structural.exact_tail_token(left, structural.ExactTailOptions(**options)) == \
            structural.exact_tail_token(right, structural.ExactTailOptions(**options))
        assert tokens == (value == equal_when_on), (name, value)


def test_the_budget_is_not_an_input_of_the_tail_token():
    expr = _chain(1, 300)
    k_small = expression_key(expr, budget=32)
    k_large = expression_key(expr, budget=64)
    assert k_small != k_large  # 打ち切り位置が違う（C-K2(c)）
    assert structural.exact_tail_token(expr) == structural.exact_tail_token(_chain(1, 300))


# --------------------------------------------------------------------------
# C-K5: 識別できないものは何とも等しくならない
# --------------------------------------------------------------------------

class _Opaque:
    """値として固定できない atom（`canonical_atom` が `object_id` にするもの）。"""


def test_an_object_identity_atom_is_never_equal_even_to_itself_recomputed():
    expr = _const(0)
    expr.value = _Opaque()
    first = expression_key(expr)
    assert first != expression_key(expr)
    assert key_contains_placeholder(first)
    assert '"object_id"' not in json.dumps(first)


def test_an_unknown_node_kind_is_never_equal_even_to_itself_recomputed():
    expr = _param()
    expr.expr_type = type("FakeType", (), {"name": "FAKE"})()
    first = expression_key(expr)
    assert first[0] == "opaque"
    assert first != expression_key(expr)
    assert key_contains_placeholder(first)


def test_a_non_canonical_atom_in_a_truncated_tail_makes_the_token_unidentified():
    leaf = _const(0)
    leaf.value = _Opaque()
    left = expression_key(_chain(1, 100, base=leaf), budget=8)
    right = expression_key(_chain(1, 100, base=leaf), budget=8)
    assert left != right
    assert structural.UNIDENTIFIED_TAG in json.dumps(left)


def test_a_float_value_is_identified_by_its_bits():
    assert expression_key(_const(0.5)) == expression_key(_const(0.5))
    assert expression_key(_const(0.0)) != expression_key(_const(-0.0))
    assert key_is_comparable(expression_key(_const(0.5)))


def test_the_identity_fallback_is_the_live_object_and_never_an_id():
    deep = _chain(1, 400)
    first = expression_key_or_identity(deep)
    assert first == expression_key_or_identity(deep)  # 同じ live object
    assert first != expression_key_or_identity(_chain(1, 400))  # 別 object
    assert first[2][0] == structural.PROCESS_OBJECT_TAG
    assert id(deep) not in first[2]


# --------------------------------------------------------------------------
# C-K6 / C-K7: 決定性と衝突
# --------------------------------------------------------------------------

_DETERMINISM_PROBE = r"""
import json, sys
sys.path.insert(0, {root!r})
from scripts.function_tracer_pcode.tests.unit.test_sn3_exact_structural_key import _determinism_corpus
from scripts.function_tracer_pcode.core.structural import expression_key
print(json.dumps([expression_key(e, budget=16) for e in _determinism_corpus()]))
"""


def _determinism_corpus():
    return [
        _chain(1, 60),
        _wrap("call", _chain(2, 60)),
        _wrap("phi_condition", _chain(3, 60)),
        _binary("INT_ADD", _chain(4, 30), _chain(5, 30)),
        _doubling(8, shared=False),
    ]


@pytest.mark.parametrize("seed", ["0", "1", "4242", "random"])
def test_keys_do_not_depend_on_the_hash_seed(seed):
    env = dict(os.environ, PYTHONHASHSEED=seed)
    output = subprocess.run(
        [sys.executable, "-B", "-c", _DETERMINISM_PROBE.format(root=str(REPO_ROOT))],
        env=env, cwd=str(REPO_ROOT), capture_output=True, text=True, check=True,
    ).stdout
    expected = json.loads(json.dumps([expression_key(e, budget=16) for e in _determinism_corpus()]))
    assert json.loads(output) == expected


def test_the_canonical_encoding_is_typed_and_length_prefixed():
    encode = structural._canonical_bytes
    assert encode((1, "1")) != encode(("1", 1))
    assert encode(("ab", "c")) != encode(("a", "bc"))
    assert encode((True,)) != encode((1,))
    assert encode([1]) != encode((1,))
    assert encode(0.0) != encode(-0.0)
    for bad in (object(), {"a": 1}, {1}, _Opaque()):
        with pytest.raises(structural._NotCanonical):
            encode((bad,))


def _colliding_intern_class():
    """すべての record を同じ digest にする test double（SHA-256 の衝突の代わり）。"""

    class _CollidingIntern(structural._ExactTailIntern):
        @staticmethod
        def digest(record):
            return "0" * 64

    return _CollidingIntern


@pytest.fixture
def colliding_intern(monkeypatch):
    intern = _colliding_intern_class()()
    monkeypatch.setattr(structural, "_TAIL_INTERN", intern)
    monkeypatch.setattr(structural, "_VALIDATED_TAIL_MEMO", structural.weakref.WeakKeyDictionary())
    return intern


def test_a_digest_collision_does_not_make_different_tails_equal(colliding_intern):
    left = expression_key(_chain(1, 100), budget=8)
    right = expression_key(_chain(2, 100), budget=8)
    again = expression_key(_chain(1, 100), budget=8)
    assert left != right
    assert left == again
    assert colliding_intern.collisions > 0


def test_option_b_digest_only_identity_would_lose_c_k1_under_a_collision(colliding_intern):
    left = expression_key(_chain(1, 100), budget=8)
    right = expression_key(_chain(2, 100), budget=8)

    def digest_only(key):
        # Option B: token の index を捨てて digest だけで比べる
        import re

        return re.sub(r'("exact_tail", "[0-9a-f]{64}"), \d+\]', r"\1]", json.dumps(key))

    assert digest_only(left) == digest_only(right)  # Option B なら誤って一致する
    assert left != right  # Option A（intern）は区別する


# --------------------------------------------------------------------------
# Gate B: 並行 intern（bucket を見た後・index を決める直前で同期する）
# --------------------------------------------------------------------------

def _RacingIntern(parties):
    """`_decide_index` の入口（bucket 確認後・index 決定直前）で thread を揃える intern。"""

    class _Racing(_colliding_intern_class()):
        def __init__(self):
            super().__init__()
            self.barrier = threading.Barrier(parties)
            self.inside = 0
            self.max_inside = 0
            self._count_lock = threading.Lock()

        def _decide_index(self, bucket, record):
            with self._count_lock:
                self.inside += 1
                self.max_inside = max(self.max_inside, self.inside)
            try:
                # lock が無い実装なら全員がここへ同時に来て揃う。lock があれば 1 つずつ
                # しか来ないので timeout で抜ける（どちらでも下の不変条件は成り立つこと）
                self.barrier.wait(timeout=0.2)
            except threading.BrokenBarrierError:
                pass
            try:
                return super()._decide_index(bucket, record)
            finally:
                with self._count_lock:
                    self.inside -= 1

    return _Racing()


def _race(intern, records):
    results = [None] * len(records)

    def worker(position):
        results[position] = intern.intern(records[position])

    threads = [threading.Thread(target=worker, args=(position,)) for position in range(len(records))]
    for thread in threads:
        thread.start()
    for thread in threads:
        thread.join(10)
    return results


@pytest.mark.parametrize("round_", range(5))
def test_concurrent_intern_of_different_records_with_the_same_digest(round_):
    intern = _RacingIntern(2)
    x, y = b"record-x", b"record-y"
    first_x, first_y = _race(intern, [x, y])
    assert first_x != first_y  # 同じ index が異なる record に割り当てられない
    assert intern.max_inside == 1  # index 決定は 1 つずつ
    # 表が壊れていない: 同じ record を引き直すと同じ identity、重複登録も無い
    assert intern.intern(x) == first_x
    assert intern.intern(y) == first_y
    assert intern.statistics()["records"] == 2


@pytest.mark.parametrize("round_", range(5))
def test_concurrent_intern_of_the_same_record(round_):
    intern = _RacingIntern(2)
    record = b"record-same"
    first, second = _race(intern, [record, record])
    assert first == second
    assert intern.max_inside == 1
    assert intern.statistics()["records"] == 1


def test_many_concurrent_interns_keep_the_table_injective():
    intern = _RacingIntern(8)
    records = [b"r%d" % (index % 5) for index in range(40)]
    results = _race(intern, records)
    by_record = {}
    for record, token in zip(records, results):
        by_record.setdefault(record, set()).add(token)
    assert all(len(tokens) == 1 for tokens in by_record.values())
    assert len({next(iter(tokens)) for tokens in by_record.values()}) == 5
    assert intern.max_inside == 1
    assert intern.statistics()["records"] == 5


def test_unidentified_tokens_are_unique_under_concurrency():
    tokens = []
    lock = threading.Lock()

    def worker():
        mine = [structural.unidentified_identity("race") for _ in range(200)]
        with lock:
            tokens.extend(mine)

    threads = [threading.Thread(target=worker) for _ in range(8)]
    for thread in threads:
        thread.start()
    for thread in threads:
        thread.join(10)
    assert len(tokens) == len(set(tokens)) == 1600


# --------------------------------------------------------------------------
# 完全比較との対応（C-K2(b)）
# --------------------------------------------------------------------------

def test_equal_tail_tokens_agree_with_the_complete_comparison():
    from scripts.function_tracer_pcode.core.semantic_freeze import freeze_expression

    corpus = [_chain(1, 300), _chain(2, 300), _chain(1, 300), _doubling(9, shared=True),
              _doubling(9, shared=False), _wrap("call", _chain(1, 300))]
    for left, right in itertools.product(corpus, repeat=2):
        same_token = structural.exact_tail_token(left) == structural.exact_tail_token(right)
        same_structure = structural_equals(
            freeze_expression(left), freeze_expression(right), budget=10 ** 6
        )
        assert same_token == same_structure
