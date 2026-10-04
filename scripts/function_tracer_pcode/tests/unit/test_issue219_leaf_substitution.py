# -*- coding: utf-8 -*-
"""直列化の作業量の葉の置き換え（Issue #219 PR-219-B、`core/budget_policy` の汎用の仕組み）。

core は「sized leaf を作る前に、渡された置き換えに尋ねる」ことだけを持ち（`substituting_leaves`）、
何を置き換えるか（snapshot の意味）は知らない。ここでは仕組みの契約を固定する:

* 置き換えを渡さない作業量の挙動は今と同じ（出力・数えた量・観測）
* 置き換えが変えるのは置く値だけ: 数えた byte・distinct な node・上限の超過（terminal な限界を含む）・
  観測値は、置き換えない作業量と同じ（そのため本体の terminal な作業量でも使える）
* 尋ねるのは `substituting_leaves` の間に、walk の外から始めた LEGACY の構築が置く葉だけ（呼ぶ側だけが
  受け取る値）。walk の中の code が読む値・`Expression.to_dict()` の返り値・数えるだけの walk は置き換えない
"""

from __future__ import annotations

from typing import Any, List

import pytest

from scripts.function_tracer_pcode.core import json_encoding
from scripts.function_tracer_pcode.core.budget_policy import (
    NO_SUBSTITUTION,
    LeafSubstitution,
    BudgetPolicy,
    budget_observations,
    budget_policy_scope,
    serialization_scope,
    substituting_leaves,
)
from scripts.function_tracer_pcode.core.errors import (
    ExpressionSizeBudgetExceeded,
    pair_failure_scope,
    reset_pair_failure_scopes,
)
from scripts.function_tracer_pcode.core.expression import Expression
from scripts.function_tracer_pcode.core.json_encoding import RESULT_JSON_POLICY


class _Marker:
    __slots__ = ("leaf",)

    def __init__(self, leaf: Any) -> None:
        self.leaf = leaf


class _Asked(LeafSubstitution):
    __slots__ = ("leaves", "sizes", "answer")

    def __init__(self, answer: Any = None) -> None:
        self.leaves: List[Any] = []
        self.sizes: List[Any] = []
        self.answer = answer

    def __leaf_substitute__(self, leaf: Any, size: Any) -> Any:
        self.leaves.append(leaf)
        self.sizes.append(size)
        return _Marker(leaf) if self.answer is None else self.answer


def _expr(value: int = 3) -> Expression:
    return Expression.binary_op("INT_ADD", Expression.parameter("a", 0, size=4), Expression.constant(value, size=4))


class _Record:
    """walk の中で別の record の表現を作って読む producer（`json_items` が `to_dict()` を呼ぶ）。"""

    def __init__(self, inner: Any) -> None:
        self.inner = inner

    def json_items(self):
        built = json_encoding.materialize(self.inner)
        # producer は作った表現を読む（置き換えた値が来れば壊れる）
        yield "inner_type", built["expr"]["type"]
        yield "expr_dict", self.inner_expr().to_dict()["type"]

    def inner_expr(self) -> Expression:
        return self.inner.expr


class _Inner:
    def __init__(self, expr: Expression) -> None:
        self.expr = expr

    def json_items(self):
        yield "expr", self.expr


class _Fields:
    """walk の外から構築する record（field の値をそのまま置く）。"""

    def __init__(self, **fields: Any) -> None:
        self.fields = fields

    def json_items(self):
        yield from self.fields.items()


@pytest.fixture(autouse=True)
def _clean_ledger_stack():
    reset_pair_failure_scopes()
    yield
    reset_pair_failure_scopes()


def _measured(source: Any, substitution: Any = None, *, terminal: bool = True, site: str = "test.leaf"):
    with serialization_scope(site=site, target_parts=("t",), terminal=terminal) as work:
        with substituting_leaves(work, substitution):
            built = RESULT_JSON_POLICY.materialize(source, budget=work)
        return built, work.consumed, work.distinct_nodes


def test_without_a_substitution_the_work_is_unchanged():
    expr = _expr()
    with budget_policy_scope(BudgetPolicy()):
        plain = _measured(_Fields(a=expr, b=_Fields(k=expr)))
        explicit = _measured(_Fields(a=expr, b=_Fields(k=expr)), None)
    assert plain == explicit
    assert plain[0] == {"a": expr.to_dict(), "b": {"k": expr.to_dict()}}


@pytest.mark.parametrize("terminal", [True, False])
def test_a_substituted_leaf_is_placed_but_counted_and_observed_exactly_like_a_built_one(terminal):
    """置き換えが変えるのは置く値だけ: 数えた byte・distinct な node・観測値は、置き換えない作業量と同じ。"""

    shared = _expr()
    other = _expr(5)
    source = _Fields(a=shared, b=Expression.binary_op("INT_AND", shared, other), c=other)
    asked = _Asked()
    with budget_policy_scope(BudgetPolicy()):
        built, consumed, nodes = _measured(source, asked, terminal=terminal, site="test.leaf.sub")
        substituted_observed = {k.split("@")[0]: v for k, v in budget_observations().items() if k.endswith("@test.leaf.sub")}
    with budget_policy_scope(BudgetPolicy()):
        _plain, plain_bytes, plain_nodes = _measured(source, terminal=terminal, site="test.leaf.sub")
        plain_observed = {k.split("@")[0]: v for k, v in budget_observations().items() if k.endswith("@test.leaf.sub")}
    assert [type(item) for item in built.values()] == [_Marker, _Marker, _Marker]
    assert len(asked.leaves) == 3
    assert (consumed, nodes) == (plain_bytes, plain_nodes)
    assert substituted_observed == plain_observed
    assert bool(plain_observed) == terminal


@pytest.mark.parametrize("offset", [-1, 0, 1])
@pytest.mark.parametrize("terminal", [True, False])
def test_a_substituting_work_stops_at_the_same_node_limit_as_a_plain_work(offset, terminal):
    from scripts.function_tracer_pcode.core.json_encoding import JsonBudgetExhausted

    shared = _expr()
    source = _Fields(a=shared, b=Expression.binary_op("INT_AND", shared, _expr(5)))
    with budget_policy_scope(BudgetPolicy()):
        _built, _bytes, nodes = _measured(source)
    outcomes = []
    for substitution in (_Asked(), None):
        with pair_failure_scope(("pair", 1), None), budget_policy_scope(BudgetPolicy(serialization_nodes=nodes + offset)):
            try:
                _measured(source, substitution, terminal=terminal)
                outcomes.append("ok")
            except (JsonBudgetExhausted, ExpressionSizeBudgetExceeded) as failure:
                outcomes.append(type(failure).__name__)
        reset_pair_failure_scopes()
    expected = ("ExpressionSizeBudgetExceeded" if terminal else "JsonBudgetExhausted") if offset < 0 else "ok"
    assert outcomes[0] == outcomes[1] == expected


def test_no_substitution_answer_keeps_the_leaf():
    expr = _expr()
    with budget_policy_scope(BudgetPolicy()):
        built = _measured(_Fields(a=expr), _Asked(NO_SUBSTITUTION))
        plain = _measured(_Fields(a=expr))
    assert built == plain


def test_values_built_for_code_inside_a_walk_are_never_substituted():
    expr = _expr()
    asked = _Asked()
    record = _Record(_Inner(expr))
    with budget_policy_scope(BudgetPolicy()):
        built, _consumed, _nodes = _measured(_Fields(record=record, outer=expr), asked)
    # producer が読んだ表現は本物（置き換えは walk の外から始めた構築が置いた葉だけ）
    assert built["record"] == {"inner_type": "BINARY_OP", "expr_dict": "BINARY_OP"}
    assert type(built["outer"]) is _Marker
    assert asked.leaves == [expr]


def test_to_dict_and_count_only_walks_are_never_substituted():
    expr = _expr()
    asked = _Asked()
    with budget_policy_scope(BudgetPolicy()):
        with serialization_scope(site="t", target_parts=("t",)) as work:
            with substituting_leaves(work, asked):
                assert expr.to_dict() == Expression.to_dict(expr) and type(expr.to_dict()) is dict
                RESULT_JSON_POLICY.count_into(_Fields(a=expr), work)
    assert asked.leaves == []


def test_only_the_leaves_built_while_substituting_are_asked():
    expr = _expr()
    asked = _Asked()
    with budget_policy_scope(BudgetPolicy()):
        with serialization_scope(site="t", target_parts=("t",)) as work:
            before = RESULT_JSON_POLICY.materialize(_Fields(a=expr), budget=work)
            with substituting_leaves(work, asked):
                during = RESULT_JSON_POLICY.materialize(_Fields(a=expr), budget=work)
            after = RESULT_JSON_POLICY.materialize(_Fields(a=expr), budget=work)
            assert work.active_leaf_substitution() is None
    assert before == after == {"a": expr.to_dict()}
    assert type(during["a"]) is _Marker and asked.leaves == [expr]


def test_a_substitution_must_be_a_leaf_substitution_nests_like_a_context_and_stays_in_its_thread():
    """置き換えは `with` の間だけ、効かせた thread でだけ効く。入れ子は内側が効き、抜けると外側へ戻る（呼ぶ側が
    誰でも同じ規則: 読みの置き換えの中で入力の code が自分の置き換えを効かせても拒まない）。"""

    import threading

    with budget_policy_scope(BudgetPolicy()):
        with serialization_scope(site="t", target_parts=("t",)) as work:
            with pytest.raises(TypeError):
                with substituting_leaves(work, lambda leaf: leaf):
                    pass
            outer, inner = _Asked(), _Asked()
            with substituting_leaves(work, outer):
                assert work.active_leaf_substitution() is outer
                with substituting_leaves(work, inner):
                    assert work.active_leaf_substitution() is inner
                    seen = []
                    thread = threading.Thread(target=lambda: seen.append(work.active_leaf_substitution()))
                    thread.start()
                    thread.join()
                    assert seen == [None]
                assert work.active_leaf_substitution() is outer
            with pytest.raises(RuntimeError):
                with substituting_leaves(work, outer):
                    raise RuntimeError("boom")
            assert work.active_leaf_substitution() is None


def test_the_substitution_is_asked_even_outside_a_budget_scope():
    asked = _Asked()
    built, _consumed, _nodes = _measured(_Fields(a=_expr()), asked)
    assert type(built["a"]) is _Marker


def test_the_substitution_receives_the_size_the_work_charged_for_the_leaf():
    """尋ねるのは見積もりの後で、作業量がその葉に数えた大きさを渡す（数えない作業量では `None`）。"""

    small = _expr()
    large = small
    for index in range(20):
        large = Expression.binary_op("INT_ADD", large, Expression.constant(index, size=4))
    asked = _Asked()
    with budget_policy_scope(BudgetPolicy()):
        _measured(_Fields(a=small), asked)
        _built, small_only, _nodes = _measured(_Fields(a=small))
        _built, large_only, _nodes = _measured(_Fields(a=large))
        _measured(_Fields(a=large), asked)
    wrapper = small_only - asked.sizes[0]
    assert asked.leaves == [small, large]
    assert asked.sizes[0] > 0 and asked.sizes[1] == large_only - wrapper
    outside = _Asked()
    _measured(_Fields(a=small), outside)
    assert outside.sizes == [None]


def test_the_leaf_that_exceeds_the_limit_is_not_asked():
    from scripts.function_tracer_pcode.core.json_encoding import JsonBudgetExhausted

    expr = _expr()
    with budget_policy_scope(BudgetPolicy()):
        _built, _bytes, nodes = _measured(_Fields(a=expr))
    asked = _Asked()
    with budget_policy_scope(BudgetPolicy(serialization_nodes=nodes - 1)):
        with pytest.raises(JsonBudgetExhausted):
            _measured(_Fields(a=expr), asked, terminal=False)
    assert asked.leaves == []
