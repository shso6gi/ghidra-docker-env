# -*- coding: utf-8 -*-
"""witness の等しさが保証すべきこと（Issue #219 PR-219-B、C-RS1 / C-RS5）。

witness が等しい 2 回の呼び出しでは、本体（同じ sealing の状態での通常の build）の結果が同じで
なければならない。比べるのは fingerprint だけではない:

* 返す snapshot の全 field（`snapshot_id` の中の容器の型、参照で持つ object を含む）
* 予算による成功 / 失敗と、失敗の種類（どの予算か）

oracle は再利用の実装ではなく、同じ時点の本体の build（`AnalysisSnapshot._build_from_function_analysis`）。
harness は「先に別の解析で store を温め、次に対象を呼ぶ」形で、hit し得る状況を必ず作る。組み合わせは
closed / open / 混在、共有 DAG / 同じ内容の別 object / 共有関係の変化、scalar の subclass / 組み込み、
予算の境界（直前・一致・超過）、`snapshot_id` の容器の型、同じ object の内容の変更、入れ子の scope・
直列化、失敗の後の store。
"""

from __future__ import annotations

import dataclasses
import itertools
from typing import Any, Callable, List, Tuple

import pytest

from scripts.function_tracer_pcode.core.analysis import ReturnInfo
from scripts.function_tracer_pcode.core.budget_policy import (
    BudgetPolicy,
    budget_policy_scope,
    serialization_scope,
)
from scripts.function_tracer_pcode.core.errors import (
    AnalysisFailureError,
    pair_failure_scope,
    reset_pair_failure_scopes,
)
from scripts.function_tracer_pcode.core.expression import Expression
from scripts.function_tracer_pcode.core.semantic_lifecycle import serialization_closed
from scripts.function_tracer_pcode.proof.obligations import snapshot as snapshot_module
from scripts.function_tracer_pcode.proof.obligations.snapshot import AnalysisSnapshot
from scripts.function_tracer_pcode.proof.obligations.snapshot_reuse import snapshot_reuse_scope
from scripts.function_tracer_pcode.tests.conftest import create_mock_analysis
from scripts.function_tracer_pcode.tests.unit._publication import published
from scripts.function_tracer_pcode.tests.unit import _snapshot_oracle as oracle

_RAW_BUILD = AnalysisSnapshot.__dict__["_build_from_function_analysis"].__func__


@pytest.fixture(autouse=True, params=["hash", "collide"])
def _witness_hash_mode(request, monkeypatch):
    """`collide` は witness の hash を定数にして、比べ方（`_same`）だけで決めさせる（hash の衝突で誤らない）。"""

    if request.param == "collide":
        from scripts.function_tracer_pcode.proof.obligations import snapshot_reuse

        monkeypatch.setattr(snapshot_reuse, "_hash", lambda value, retained=False: 0)
    yield request.param


@pytest.fixture(autouse=True)
def _clean_ledger_stack():
    reset_pair_failure_scopes()
    yield
    reset_pair_failure_scopes()


class _BoxedInt(int):
    """組み込みの `int` の subclass（実 run の JPype の整数と同じく、closed の規則が受けない scalar）。"""


#: 同じ boxed の object を共有する（JPype も同じ値の object を返し得る。identity で比べれば区別されない）
_BOXED_FOUR = _BoxedInt(4)


def _param(name: str = "a", index: int = 0) -> Expression:
    return Expression.parameter(name, index, size=4)


def _closed_root(seed: int = 1) -> Expression:
    return Expression.binary_op("INT_ADD", _param(), Expression.constant(seed, size=4))


def _open_root(child: Expression, *, boxed: bool = True) -> Expression:
    size = _BOXED_FOUR if boxed else 4
    return Expression.binary_op("INT_AND", child, Expression.constant(3, size=size))


def _analysis(values: List[Expression], *, scope_key: Any = None) -> Any:
    analysis = create_mock_analysis(
        "f",
        returns=[ReturnInfo(address="0x%08x" % (0x401000 + 4 * i), conditions=[], value=v) for i, v in enumerate(values)],
    )
    if scope_key is not None:
        analysis.analysis_scope_key = scope_key
    return analysis


def _with_values(base: Any, values: List[Expression]) -> Any:
    """`base` の残りの材料（function_ref・parameter 表・notes）を共有し、return の値だけを替えた派生。"""

    for value in values:
        published(value)
    return dataclasses.replace(
        base,
        returns=[dataclasses.replace(ret, value=value) for ret, value in zip(base.returns, values)],
    )


# ---------------------------------------------------------------------------
# oracle と harness
# ---------------------------------------------------------------------------


def _outcome(call: Callable[[], AnalysisSnapshot]) -> Tuple[Any, ...]:
    return oracle.outcome(call)


def _reuse_matches_the_body(prime: List[Any], target: Any, policy: BudgetPolicy) -> List[str]:
    """`prime` で store を温めてから `target` を呼び、直後の同じ sealing の状態の本体と比べた違い。"""

    with pair_failure_scope(("pair", 1), None), budget_policy_scope(policy), snapshot_reuse_scope():
        for item in prime:
            _outcome(lambda item=item: AnalysisSnapshot.from_function_analysis(item))
        reused = _outcome(lambda: AnalysisSnapshot.from_function_analysis(target))
        built = _outcome(lambda: _RAW_BUILD(AnalysisSnapshot, target))
    return oracle.outcome_problems(reused, built)


def _measured_nodes(analysis: Any) -> int:
    with budget_policy_scope(BudgetPolicy()):
        with serialization_scope(site="probe", target_parts=("p",)) as work:
            snapshot_module.snapshot_material(analysis, work)
            return work.distinct_nodes


def _measured_bytes(analysis: Any) -> int:
    seen = []
    original = snapshot_module.AnalysisSnapshot.__dict__["create"].__func__

    with budget_policy_scope(BudgetPolicy()):
        with serialization_scope(site=snapshot_module.SNAPSHOT_SERIALIZATION_SITE, target_parts=("p",)) as work:
            material = snapshot_module.snapshot_material(analysis, work)
            original(AnalysisSnapshot, material.snapshot_id, material.semantic_fields,
                     diagnostic_refs=material.diagnostic_refs)
            seen.append(work.consumed)
    return seen[0]


# ---------------------------------------------------------------------------
# 形の組み合わせ（prime と target の組）
# ---------------------------------------------------------------------------


def _shapes():
    """(名前, prime の return の値, target の return の値)。

    target は prime の材料（function_ref・表・closed な root の object）を共有し、違うのは名前の
    とおりの部分だけ。closed な root の object を共有したまま、open な式の中の共有関係・object だけを
    変える組み（JSON の値では区別できない違い）を必ず含める。
    """

    shapes = []

    def add(name, make):
        shapes.append((name, make))

    # closed だけ: 共有 / 別 object / 共有関係の変化
    def closed_shared_to_distinct():
        x = _closed_root()
        return [x, x], [x, _closed_root()]

    def closed_distinct_to_shared():
        x, y = _closed_root(), _closed_root()
        return [x, y], [x, x]

    def closed_same_objects():
        x = _closed_root()
        return [x, x], [x, x]

    # open だけ
    def open_shared_child_to_copy():
        c = _closed_root(5)
        return [_open_root(c), _open_root(c)], [_open_root(c), _open_root(_closed_root(5))]

    def open_rebuilt_same_shape():
        c = _closed_root(5)
        return [_open_root(c), _open_root(c)], [_open_root(c2 := _closed_root(5)), _open_root(c2)]

    # 混在: closed な root を open な式の子で共有する（レビューの反例の形）
    def mixed_shared_child_to_copy():
        x = _closed_root()
        return [x, _open_root(x)], [x, _open_root(_closed_root())]

    def mixed_copy_child_to_shared():
        x = _closed_root()
        return [x, _open_root(_closed_root())], [x, _open_root(x)]

    def mixed_same_objects():
        x = _closed_root()
        y = _open_root(x)
        return [x, y], [x, y]

    # 混在で、open にする原因が組み込みの scalar（closed になる）だけの対照
    def mixed_unboxed_shared_child_to_copy():
        x = _closed_root()
        return [x, _open_root(x, boxed=False)], [x, _open_root(_closed_root(), boxed=False)]

    for name, make in list(locals().items()):
        if callable(make) and name not in ("add",):
            add(name, make)
    return shapes


SHAPES = _shapes()


@pytest.mark.parametrize("name, make", SHAPES, ids=[s[0] for s in SHAPES])
@pytest.mark.parametrize("budget", ["nodes", "bytes"])
@pytest.mark.parametrize("offset", [-1, 0, 1])
def test_reuse_has_the_same_fields_and_budget_outcome_as_the_body(name, make, budget, offset):
    prime_values, target_values = make()
    prime = _analysis(prime_values)
    target = _with_values(prime, target_values)
    if budget == "nodes":
        policy = BudgetPolicy(serialization_nodes=max(1, _measured_nodes(target) + offset))
    else:
        policy = BudgetPolicy(serialization_bytes=max(1, _measured_bytes(target) + offset))
    assert _reuse_matches_the_body([prime], target, policy) == [], (name, budget, offset)


def test_the_open_shapes_are_open_and_the_closed_shapes_are_closed():
    """組み合わせの前提: subclass の scalar を持つ式は closed でなく、組み込みだけの式は closed。"""

    with budget_policy_scope(BudgetPolicy()), snapshot_reuse_scope():
        x = _closed_root()
        analysis = _analysis([x, _open_root(x)])
        AnalysisSnapshot.from_function_analysis(analysis)
        assert serialization_closed(analysis.returns[0].value)
        assert not serialization_closed(analysis.returns[1].value)
        unboxed = _analysis([x, _open_root(x, boxed=False)])
        AnalysisSnapshot.from_function_analysis(unboxed)
        assert serialization_closed(unboxed.returns[1].value)


# ---------------------------------------------------------------------------
# snapshot_id の容器の型・同じ object の内容の変更
# ---------------------------------------------------------------------------


@pytest.mark.parametrize(
    "before, after",
    [
        (("scope", ["nested"]), ("scope", ("nested",))),
        (("scope", ("nested",)), ("scope", ["nested"])),
        (("scope", 1), ("scope", True)),
        (("scope", {"k": 1}), ("scope", (("k", 1),))),
        (("scope", frozenset({"a"})), ("scope", ("a",))),
    ],
    ids=["list_to_tuple", "tuple_to_list", "int_to_bool", "dict_to_pairs", "frozenset_to_tuple"],
)
def test_a_snapshot_id_with_other_container_types_is_never_served_from_the_store(before, after):
    prime = _analysis([_closed_root()], scope_key=before)
    target = dataclasses.replace(prime, analysis_scope_key=after)
    assert _reuse_matches_the_body([prime], target, BudgetPolicy()) == []


def test_a_snapshot_id_holding_an_equal_but_other_mutable_object_is_not_served():
    prime = _analysis([_closed_root()], scope_key=("scope", ["nested"]))
    target = dataclasses.replace(prime, analysis_scope_key=("scope", ["nested"]))
    assert _reuse_matches_the_body([prime], target, BudgetPolicy()) == []


def test_the_same_object_changed_in_place_is_rebuilt_with_its_budget_outcome():
    x = _closed_root()
    analysis = _analysis([x, _open_root(x)])
    limit = _measured_nodes(analysis)
    with pair_failure_scope(("pair", 1), None), budget_policy_scope(BudgetPolicy(serialization_nodes=limit)):
        with snapshot_reuse_scope():
            first = _outcome(lambda: AnalysisSnapshot.from_function_analysis(analysis))
            assert first[0] == "ok"
            # open な式の子だけを同じ内容の別 object へ（in-place。node が 1 つ増える）
            replacement = _open_root(_closed_root())
            published(replacement)
            analysis.returns[1].value = replacement
            reused = _outcome(lambda: AnalysisSnapshot.from_function_analysis(analysis))
            built = _outcome(lambda: _RAW_BUILD(AnalysisSnapshot, analysis))
    assert oracle.outcome_problems(reused, built) == []


# ---------------------------------------------------------------------------
# 入れ子の scope・入れ子の直列化・失敗の後の store
# ---------------------------------------------------------------------------


def test_a_nested_scope_with_a_stricter_policy_follows_the_body():
    x = _closed_root()
    analysis = _analysis([x, _open_root(x)])
    limit = _measured_nodes(analysis)
    with pair_failure_scope(("pair", 1), None), budget_policy_scope(BudgetPolicy()), snapshot_reuse_scope():
        AnalysisSnapshot.from_function_analysis(analysis)
        with budget_policy_scope(BudgetPolicy(serialization_nodes=limit - 1)), snapshot_reuse_scope():
            reused = _outcome(lambda: AnalysisSnapshot.from_function_analysis(analysis))
            built = _outcome(lambda: _RAW_BUILD(AnalysisSnapshot, analysis))
    assert oracle.outcome_problems(reused, built) == [] and reused[0] == "raised"


def test_a_call_inside_another_serialization_follows_the_body():
    x = _closed_root()
    analysis = _analysis([x, _open_root(x)])
    with pair_failure_scope(("pair", 1), None), budget_policy_scope(BudgetPolicy()), snapshot_reuse_scope():
        AnalysisSnapshot.from_function_analysis(analysis)
        with serialization_scope(site="outer", target_parts=("o",)):
            reused = _outcome(lambda: AnalysisSnapshot.from_function_analysis(analysis))
        with serialization_scope(site="outer", target_parts=("o",)):
            built = _outcome(lambda: _RAW_BUILD(AnalysisSnapshot, analysis))
    assert oracle.outcome_problems(reused, built) == []


def test_a_failure_stores_nothing_and_a_later_success_does_not_hide_a_later_failure():
    x = _closed_root()
    analysis = _analysis([x, _open_root(x)])
    limit = _measured_nodes(analysis)
    strict, permissive = BudgetPolicy(serialization_nodes=limit - 1), BudgetPolicy()
    with pair_failure_scope(("pair", 1), None), snapshot_reuse_scope() as store:
        with budget_policy_scope(strict):
            assert _outcome(lambda: AnalysisSnapshot.from_function_analysis(analysis))[0] == "raised"
        assert store.metrics()["entries"] == 0
        with budget_policy_scope(permissive):
            assert _outcome(lambda: AnalysisSnapshot.from_function_analysis(analysis))[0] == "ok"
        with budget_policy_scope(strict):
            reused = _outcome(lambda: AnalysisSnapshot.from_function_analysis(analysis))
            built = _outcome(lambda: _RAW_BUILD(AnalysisSnapshot, analysis))
    assert oracle.outcome_problems(reused, built) == [] and reused[0] == "raised"


# ---------------------------------------------------------------------------
# property: ランダムな DAG・共有・scalar・予算の境界
# ---------------------------------------------------------------------------


def _random_value(rng, pool: List[Expression], depth: int) -> Expression:
    if pool and rng.random() < 0.5:
        return rng.choice(pool)
    if depth <= 0:
        size = _BOXED_FOUR if rng.random() < 0.5 else 4
        node = rng.choice((
            lambda: Expression.constant(rng.randrange(8), size=size),
            lambda: Expression.parameter("p%d" % rng.randrange(3), rng.randrange(3), size=4),
        ))()
    else:
        node = Expression.binary_op(
            rng.choice(("INT_ADD", "INT_AND", "INT_SUB")),
            _random_value(rng, pool, depth - 1), _random_value(rng, pool, depth - 1),
        )
    pool.append(node)
    return node


def _rebuild(value: Expression) -> Expression:
    operands = getattr(value, "operands", None) or ()
    if operands:
        return Expression.binary_op(value.operator, *[_rebuild(item) for item in operands])
    if value.expr_type.name == "CONSTANT":
        return Expression.constant(value.value, size=value.size)
    return Expression.parameter(value.name, value.value, size=value.size)


@pytest.mark.parametrize("seed", range(150))
def test_random_shapes_follow_the_body_at_every_budget_boundary(seed):
    """closed な root と、それを子に持ち得る open な root のランダムな組。target は root ごとに、同じ
    object・同じ内容の別 object（共有関係も作り直す）・他の root の object のどれかにする。"""

    import random

    rng = random.Random(seed)
    pool: List[Expression] = []
    closed = []
    for _ in range(rng.randrange(1, 3)):
        root = Expression.binary_op("INT_ADD", _param("p%d" % rng.randrange(2), 0), Expression.constant(rng.randrange(8), size=4))
        pool.append(root)
        closed.append(root)
    opened = [_random_value(rng, pool, rng.randrange(1, 3)) for _ in range(rng.randrange(1, 3))]
    opened = [Expression.binary_op("INT_AND", value, Expression.constant(1, size=_BOXED_FOUR)) for value in opened]
    values = closed + opened
    prime = _analysis(values)
    choices = list(closed)
    for value in opened:
        pick = rng.randrange(3)
        choices.append(value if pick == 0 else _rebuild(value) if pick == 1 else rng.choice(values))
    if all(choice is value for choice, value in zip(choices, values)):
        choices[-1] = _rebuild(values[-1])
    target = _with_values(prime, choices)
    budget = rng.choice(("nodes", "bytes"))
    offset = rng.choice((-1, 0, 1))
    if budget == "nodes":
        policy = BudgetPolicy(serialization_nodes=max(1, _measured_nodes(target) + offset))
    else:
        policy = BudgetPolicy(serialization_bytes=max(1, _measured_bytes(target) + offset))
    assert _reuse_matches_the_body([prime], target, policy) == [], (seed, budget, offset)
