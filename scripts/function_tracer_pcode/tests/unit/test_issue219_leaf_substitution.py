# -*- coding: utf-8 -*-
"""直列化の作業量の葉の置き換え（Issue #219 PR-219-B、`core/budget_policy` の汎用の仕組み）。

core は「sized leaf を作る前に、walk へ引数で渡された置き換えに尋ねる」ことだけを持ち
（`JsonEncodingPolicy.materialize(..., leaf_substitution=...)`）、
何を置き換えるか（snapshot の意味）は知らない。ここでは仕組みの契約を固定する:

* 置き換えを渡さない作業量の挙動は今と同じ（出力・数えた量・観測）
* 置き換えが変えるのは置く値だけ: 数えた byte・distinct な node・上限の超過（terminal な限界を含む）・
  観測値は、置き換えない作業量と同じ（そのため本体の terminal な作業量でも使える）
* 尋ねるのは置き換えを引数で受け取った walk が自分で置く葉だけ（呼ぶ側だけが受け取る値）。置き換えは
  作業量・thread・context に登録されないので、同じ作業量の前後・中・別 thread・新しい context の walk、walk の
  中の code が読む値・`Expression.to_dict()` の返り値・数えるだけの walk は置き換えない
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
        built = RESULT_JSON_POLICY.materialize(source, budget=work, leaf_substitution=substitution)
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


def test_only_the_walk_given_the_substitution_is_asked():
    """同じ作業量で前後に始めた walk・`to_dict()`・数えるだけの walk は、引数を渡されないので置き換えない。"""

    expr = _expr()
    asked = _Asked()
    with budget_policy_scope(BudgetPolicy()):
        with serialization_scope(site="t", target_parts=("t",)) as work:
            before = RESULT_JSON_POLICY.materialize(_Fields(a=expr), budget=work)
            during = RESULT_JSON_POLICY.materialize(_Fields(a=expr), budget=work, leaf_substitution=asked)
            after = RESULT_JSON_POLICY.materialize(_Fields(a=expr), budget=work)
            assert expr.to_dict() == Expression.to_dict(expr) and type(expr.to_dict()) is dict
            RESULT_JSON_POLICY.count_into(_Fields(a=expr), work)
    assert before == after == {"a": expr.to_dict()}
    assert type(during["a"]) is _Marker and asked.leaves == [expr]


def test_a_substitution_must_be_a_leaf_substitution_and_needs_a_serialization_work():
    with budget_policy_scope(BudgetPolicy()):
        with serialization_scope(site="t", target_parts=("t",)) as work:
            with pytest.raises(TypeError):
                RESULT_JSON_POLICY.materialize(_Fields(a=_expr()), budget=work, leaf_substitution=lambda leaf: leaf)
    with pytest.raises(TypeError):
        RESULT_JSON_POLICY.materialize(_Fields(a=_expr()), leaf_substitution=_Asked())


def test_the_substitution_is_not_reachable_from_the_work_or_the_walk_work():
    """置き換えは作業量にも walk の作業量にも登録されない（公開の属性・引数の無い getter から辿れない）。"""

    asked = _Asked()
    seen: List[Any] = []

    class _Probe:
        def json_items(self):
            for holder in (json_encoding.active_walk_work(),):
                for name in dir(holder):
                    if name.startswith("_"):
                        continue
                    value = getattr(holder, name)
                    if callable(value):
                        try:
                            value = value()
                        except Exception:  # noqa: BLE001 - probe: getters with arguments refuse
                            continue
                    seen.append(value is asked)
            yield "probed", 1

    with budget_policy_scope(BudgetPolicy()):
        with serialization_scope(site="t", target_parts=("t",)) as work:
            RESULT_JSON_POLICY.materialize(_Fields(a=_expr(), p=_Probe()), budget=work, leaf_substitution=asked)
            for name in dir(work):
                if not name.startswith("_") and not callable(getattr(work, name)):
                    seen.append(getattr(work, name) is asked)
    assert seen and not any(seen)


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


# ---------------------------------------------------------------------------
# 置き換えは、それを claim した walk だけが使う（レビュー 5）
# ---------------------------------------------------------------------------


class _NestsAWalk:
    """walk の中の producer: 同じ作業量で値を LEGACY に作る（入れ子の walk。置き換えは渡さない）。"""

    def __init__(self, work: Any, substitution: Any = None) -> None:
        self.work = work
        self.substitution = substitution
        self.built: List[Any] = []

    def json_items(self):
        self.built.append(RESULT_JSON_POLICY.materialize(
            _Fields(a=_expr()), budget=self.work, leaf_substitution=self.substitution))
        yield "nested", 1


def test_a_walk_nested_inside_a_walk_never_uses_the_outer_walks_substitution():
    with budget_policy_scope(BudgetPolicy()):
        with serialization_scope(site="t", target_parts=("t",)) as work:
            asked = _Asked()
            producer = _NestsAWalk(work)
            RESULT_JSON_POLICY.materialize(_Fields(a=producer), budget=work, leaf_substitution=asked)
    assert producer.built == [{"a": _expr().to_dict()}]
    assert asked.leaves == []


def test_a_producer_may_pass_its_own_substitution_to_its_own_walk():
    """入力の code が自分の walk に自分の置き換えを渡すのは main と同じ（外側の置き換えとは混ざらない）。"""

    with budget_policy_scope(BudgetPolicy()):
        with serialization_scope(site="t", target_parts=("t",)) as work:
            outer, own = _Asked(), _Asked("own")
            producer = _NestsAWalk(work, own)
            built = RESULT_JSON_POLICY.materialize(_Fields(a=producer, b=_expr(5)), budget=work, leaf_substitution=outer)
    assert producer.built == [{"a": "own"}] and len(own.leaves) == 1
    assert type(built["b"]) is _Marker and len(outer.leaves) == 1 and outer.leaves[0] is built["b"].leaf


def test_walks_in_another_thread_or_a_fresh_context_never_use_it():
    import contextvars
    import threading

    with budget_policy_scope(BudgetPolicy()):
        with serialization_scope(site="t", target_parts=("t",)) as work:
            asked = _Asked()
            built: List[Any] = []

            class _Elsewhere:
                def json_items(self):
                    thread = threading.Thread(target=lambda: built.append(
                        RESULT_JSON_POLICY.materialize(_Fields(a=_expr()), budget=work)))
                    thread.start()
                    thread.join()
                    built.append(contextvars.Context().run(
                        RESULT_JSON_POLICY.materialize, _Fields(a=_expr()), budget=work))
                    yield "elsewhere", 1

            RESULT_JSON_POLICY.materialize(_Fields(e=_Elsewhere()), budget=work, leaf_substitution=asked)
    assert built == [{"a": _expr().to_dict()}, {"a": _expr().to_dict()}]
    assert asked.leaves == []
