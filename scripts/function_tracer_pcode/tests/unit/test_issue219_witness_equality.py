# -*- coding: utf-8 -*-
"""同じ witness なら同じ snapshot（Issue #219 PR-219-B、C-RS1 / C-RS5）: 値の比べ方と参照の保持。

保証: 同じ safe witness なら、通常の build と同じ snapshot の全 field・参照の保持の意味・予算の
成功 / 失敗を返す。ここでは「値として同一視してよいか」を確かめる（予算は
`test_issue219_witness_fidelity.py`）。

「不変であること」と「値で同一視できること」は別: NaN は不変だが、別の NaN の object どうしは `==` で
ない（容器は要素を `is` か `==` で比べるので、同じ object なら等しい）。oracle は `_snapshot_oracle`
（production の witness・digest を使わない）。
"""

from __future__ import annotations

import dataclasses
import math
import random
from typing import Any, List

import pytest

from scripts.function_tracer_pcode.core.budget_policy import BudgetPolicy, budget_policy_scope
from scripts.function_tracer_pcode.core.errors import pair_failure_scope, reset_pair_failure_scopes
from scripts.function_tracer_pcode.proof.obligations.snapshot import AnalysisSnapshot
from scripts.function_tracer_pcode.proof.obligations.snapshot_reuse import snapshot_reuse_scope
from scripts.function_tracer_pcode.tests.unit import _snapshot_oracle as oracle
from scripts.function_tracer_pcode.tests.unit.test_issue219_witness_fidelity import _analysis, _closed_root

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


def _with_field(base: Any, where: str, value: Any) -> Any:
    if where == "analysis_scope_key":
        return dataclasses.replace(base, analysis_scope_key=("scope", value))
    return dataclasses.replace(base, return_abi_facts={"probe": value})


def _reuse_and_body(prime: Any, target: Any) -> List[str]:
    """store を `prime` で温めてから `target` を呼び、同じ時点の通常の build と比べる。"""

    with pair_failure_scope(("pair", 1), None), budget_policy_scope(BudgetPolicy()), snapshot_reuse_scope():
        oracle.outcome(lambda: AnalysisSnapshot.from_function_analysis(prime))
        reused = oracle.outcome(lambda: AnalysisSnapshot.from_function_analysis(target))
        built = oracle.outcome(lambda: _RAW_BUILD(AnalysisSnapshot, target))
    return oracle.outcome_problems(reused, built)


# ---------------------------------------------------------------------------
# oracle 自身が既知の不一致を見つけること
# ---------------------------------------------------------------------------


def _snapshot(scope_value: Any, *, analysis: Any = None) -> AnalysisSnapshot:
    base = analysis if analysis is not None else _analysis([_closed_root()])
    with budget_policy_scope(BudgetPolicy()):
        return _RAW_BUILD(AnalysisSnapshot, dataclasses.replace(base, analysis_scope_key=("scope", scope_value)))


def test_the_oracle_finds_the_known_kinds_of_difference():
    base = _analysis([_closed_root()])
    nan_a, nan_b = float("nan"), float("nan")
    shared_list = ["nested"]
    same_list = _snapshot(shared_list, analysis=base)
    cases = {
        "list_vs_tuple": (_snapshot(["nested"], analysis=base), _snapshot(("nested",), analysis=base)),
        "another_nan": (_snapshot(nan_a, analysis=base), _snapshot(nan_b, analysis=base)),
        "int_vs_bool": (_snapshot(1, analysis=base), _snapshot(True, analysis=base)),
        "another_equal_list": (same_list, _snapshot(["nested"], analysis=base)),
        "another_function_ref": (
            _snapshot(1, analysis=base),
            _snapshot(1, analysis=dataclasses.replace(base, function_ref=dataclasses.replace(base.function_ref))),
        ),
    }
    for name, (left, right) in cases.items():
        assert oracle.snapshot_problems(left, right), name
    # 同じ値・同じ object なら違いは無い（NaN も同じ object なら等しい）
    assert oracle.snapshot_problems(_snapshot(nan_a, analysis=base), _snapshot(nan_a, analysis=base)) == []
    assert oracle.snapshot_problems(same_list, _snapshot(shared_list, analysis=base)) == []
    assert oracle.snapshot_problems(_snapshot(1.5, analysis=base), _snapshot(1.5, analysis=base)) == []


# ---------------------------------------------------------------------------
# 回帰: store を温めてから入力を変える
# ---------------------------------------------------------------------------

_NAN = float("nan")


def _nan_cases():
    other = float("nan")
    return {
        "nan_replaced": (_NAN, other),
        "nan_in_tuple": ((1, _NAN), (1, other)),
        "nan_in_list": ([_NAN], [other]),
        "nan_in_nested_tuple": ((("a", _NAN),), (("a", other),)),
        "nan_in_dict_value": ({"k": _NAN}, {"k": other}),
        "nan_in_frozenset": (frozenset({_NAN}), frozenset({other})),
        "nan_dict_key": ({_NAN: 1}, {other: 1}),
        "nan_same_object": (_NAN, _NAN),
        "two_nans_to_one": ((_NAN, other), (_NAN, _NAN)),
    }


@pytest.mark.parametrize("where", ["analysis_scope_key", "return_abi_facts"])
@pytest.mark.parametrize("name", sorted(_nan_cases()))
def test_a_non_reflexive_value_is_reused_only_as_the_same_object(where, name):
    before, after = _nan_cases()[name]
    prime = _with_field(_analysis([_closed_root()]), where, before)
    target = _with_field(prime, where, after)
    assert _reuse_and_body(prime, target) == []


@pytest.mark.parametrize("where", ["analysis_scope_key", "return_abi_facts"])
@pytest.mark.parametrize(
    "before, after",
    [
        (0.0, -0.0), (1, 1.0), (1, True), ("1", 1), (["a"], ("a",)), ({"a": 1}, (("a", 1),)),
        (frozenset({"a"}), ("a",)), ((("a",),), (["a"],)), ([["a"]], [("a",)]), (float("inf"), float("inf")),
    ],
    ids=["zero_sign", "int_float", "int_bool", "str_int", "list_tuple", "dict_pairs", "frozenset_tuple",
         "nested_tuple_list", "inner_list_tuple", "inf"],
)
def test_values_that_equality_or_type_tell_apart_follow_the_body(where, before, after):
    prime = _with_field(_analysis([_closed_root()]), where, before)
    target = _with_field(prime, where, after)
    assert _reuse_and_body(prime, target) == []


def test_an_equal_list_held_by_reference_in_snapshot_id_is_another_object():
    prime = _with_field(_analysis([_closed_root()]), "analysis_scope_key", ["nested"])
    target = _with_field(prime, "analysis_scope_key", ["nested"])
    assert _reuse_and_body(prime, target) == []


def test_the_same_scope_key_object_still_hits():
    """値として同一視できない値も、同じ object なら再利用する（hit を全部止める修正ではない）。"""

    from scripts.function_tracer_pcode.proof.obligations.snapshot_reuse import snapshot_reuse_metrics

    key = ("scope", _NAN, ["nested"])
    prime = dataclasses.replace(_analysis([_closed_root()]), analysis_scope_key=key)
    target = dataclasses.replace(prime)
    with budget_policy_scope(BudgetPolicy()), snapshot_reuse_scope():
        AnalysisSnapshot.from_function_analysis(prime)
        reused = AnalysisSnapshot.from_function_analysis(target)
        assert snapshot_reuse_metrics()["counts"]["hits"] == 1
        assert oracle.snapshot_problems(reused, _RAW_BUILD(AnalysisSnapshot, target)) == []


# ---------------------------------------------------------------------------
# property: 値・容器・型・共有・NaN の生成
# ---------------------------------------------------------------------------


def _random_leaf(rng: random.Random, nans: List[float]) -> Any:
    pick = rng.randrange(9)
    if pick == 0:
        if nans and rng.random() < 0.5:
            return rng.choice(nans)
        nans.append(float("nan"))
        return nans[-1]
    return (0.0, -0.0, 1, True, 1.0, "1", None, float("inf"))[pick - 1]


def _random_value(rng: random.Random, nans: List[float], depth: int, *, keys: bool = False) -> Any:
    if depth <= 0 or rng.random() < 0.3:
        leaf = _random_leaf(rng, nans)
        return leaf if not keys else (leaf if leaf is not None else "k")
    kind = rng.randrange(4)
    items = [_random_value(rng, nans, depth - 1) for _ in range(rng.randrange(0, 3))]
    if kind == 0:
        return tuple(items)
    if kind == 1:
        return list(items)
    if kind == 2:
        return {("k%d" % i): item for i, item in enumerate(items)}
    try:
        return frozenset(_random_leaf(rng, nans) for _ in range(rng.randrange(0, 3)))
    except TypeError:
        return ()


def _variant(rng: random.Random, value: Any, nans: List[float]) -> Any:
    """`value` を、同じ object・同じ内容の作り直し・NaN の取り替え・容器の型の取り替えのどれかにする。"""

    pick = rng.randrange(4)
    if pick == 0:
        return value
    if isinstance(value, float) and math.isnan(value):
        return float("nan") if pick != 1 else value
    if isinstance(value, tuple):
        items = [_variant(rng, item, nans) for item in value]
        return list(items) if pick == 3 else tuple(items)
    if isinstance(value, list):
        items = [_variant(rng, item, nans) for item in value]
        return tuple(items) if pick == 3 else list(items)
    if isinstance(value, dict):
        return {key: _variant(rng, item, nans) for key, item in value.items()}
    if isinstance(value, frozenset):
        return frozenset(_variant(rng, item, nans) for item in value) if pick != 3 else tuple(value)
    return value


@pytest.mark.parametrize("seed", range(200))
def test_random_values_follow_the_body(seed):
    rng = random.Random(seed)
    nans: List[float] = []
    where = rng.choice(("analysis_scope_key", "return_abi_facts"))
    before = _random_value(rng, nans, rng.randrange(1, 4))
    after = _variant(rng, before, nans)
    prime = _with_field(_analysis([_closed_root()]), where, before)
    target = _with_field(prime, where, after)
    assert _reuse_and_body(prime, target) == [], (seed, where, before, after)
