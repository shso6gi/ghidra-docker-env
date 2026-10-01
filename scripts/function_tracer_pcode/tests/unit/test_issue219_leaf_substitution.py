# -*- coding: utf-8 -*-
"""直列化の作業量の葉の置き換え（Issue #219 PR-219-B、`core/budget_policy` の汎用の仕組み）。

core は「sized leaf を作る前に、渡された置き換えに尋ねる」ことと「量を観測値へ残すか」だけを
持ち、何を置き換えるか（snapshot の意味）は知らない。ここでは仕組みの契約を固定する:

* 置き換えを渡さない作業量の挙動は今と同じ（出力・数えた量・観測）
* 尋ねるのは、walk の外から始めた LEGACY の構築が置く葉だけ（呼ぶ側だけが受け取る値）。
  walk の中の code が読む値（producer が作る record の表現）・`Expression.to_dict()` の返り値・
  数えるだけの walk は置き換えない
* 置き換えを持つ作業量は terminal でなく、外側へ合流も合算もしない
* `record_observations=False` は観測値へ残さない
"""

from __future__ import annotations

from typing import Any, List

import pytest

from scripts.function_tracer_pcode.core import json_encoding
from scripts.function_tracer_pcode.core.budget_policy import (
    NO_SUBSTITUTION,
    LeafSubstitution,
    SUBSTITUTED_LEAF_BYTES,
    BudgetPolicy,
    SerializationWork,
    budget_observations,
    budget_policy_scope,
    serialization_scope,
)
from scripts.function_tracer_pcode.core.expression import Expression
from scripts.function_tracer_pcode.core.json_encoding import RESULT_JSON_POLICY


class _Marker:
    __slots__ = ("leaf",)

    def __init__(self, leaf: Any) -> None:
        self.leaf = leaf


class _Asked(LeafSubstitution):
    __slots__ = ("leaves", "answer")

    def __init__(self, answer: Any = None) -> None:
        self.leaves: List[Any] = []
        self.answer = answer

    def __leaf_substitute__(self, leaf: Any) -> Any:
        self.leaves.append(leaf)
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


def _materialized(source: Any, **scope: Any):
    with serialization_scope(site="test.leaf", target_parts=("t",), **scope) as work:
        built = RESULT_JSON_POLICY.materialize(source, budget=work)
        return built, work.consumed


def test_without_a_substitution_the_work_is_unchanged():
    expr = _expr()
    with budget_policy_scope(BudgetPolicy()):
        plain, plain_bytes = _materialized(_Fields(a=expr, b=_Fields(k=expr)))
        explicit, explicit_bytes = _materialized(_Fields(a=expr, b=_Fields(k=expr)), leaf_substitution=None, terminal=True)
    assert plain == explicit == {"a": expr.to_dict(), "b": {"k": expr.to_dict()}}
    assert plain_bytes == explicit_bytes


def test_the_leaves_an_outer_build_places_are_substituted_and_counted_as_one_byte():
    expr = _expr()
    asked = _Asked()
    with budget_policy_scope(BudgetPolicy()):
        built, consumed = _materialized(_Fields(a=expr, b=expr), terminal=False, leaf_substitution=asked)
        _plain, plain_bytes = _materialized(_Fields(a=None, b=None), terminal=False)
    assert [type(item) for item in built.values()] == [_Marker, _Marker]
    assert asked.leaves == [expr, expr]
    # 置き換えた葉は見積もらず 1 byte（`null` の 4 byte から 3 ずつ少ない）
    assert consumed == plain_bytes - 2 * (4 - SUBSTITUTED_LEAF_BYTES)


def test_no_substitution_answer_keeps_the_leaf():
    expr = _expr()
    with budget_policy_scope(BudgetPolicy()):
        built, consumed = _materialized(_Fields(a=expr), terminal=False, leaf_substitution=_Asked(NO_SUBSTITUTION))
        plain, plain_bytes = _materialized(_Fields(a=expr), terminal=False)
    assert built == plain and consumed == plain_bytes


def test_values_built_for_code_inside_a_walk_are_never_substituted():
    expr = _expr()
    asked = _Asked()
    record = _Record(_Inner(expr))
    with budget_policy_scope(BudgetPolicy()):
        built, _consumed = _materialized(_Fields(record=record, outer=expr), terminal=False, leaf_substitution=asked)
    # producer が読んだ表現は本物（置き換えは walk の外から始めた構築が置いた葉だけ）
    assert built["record"] == {"inner_type": "BINARY_OP", "expr_dict": "BINARY_OP"}
    assert type(built["outer"]) is _Marker
    assert asked.leaves == [expr]


def test_to_dict_and_count_only_walks_are_never_substituted():
    expr = _expr()
    asked = _Asked()
    with budget_policy_scope(BudgetPolicy()):
        with serialization_scope(site="t", target_parts=("t",), terminal=False, leaf_substitution=asked) as work:
            assert expr.to_dict() == Expression.to_dict(expr) and type(expr.to_dict()) is dict
            RESULT_JSON_POLICY.count_into(_Fields(a=expr), work)
    assert asked.leaves == []


def test_a_substitution_must_be_a_leaf_substitution():
    with pytest.raises(TypeError):
        with serialization_scope(site="t", target_parts=("t",), terminal=False, leaf_substitution=lambda leaf: leaf):
            pass


def test_a_substitution_needs_a_non_terminal_work_of_its_own():
    with pytest.raises(ValueError):
        with serialization_scope(site="t", target_parts=("t",), leaf_substitution=_Asked()):
            pass
    with budget_policy_scope(BudgetPolicy()):
        with serialization_scope(site="outer", target_parts=("o",)) as outer:
            with pytest.raises(ValueError):
                SerializationWork(site="t", target_parts=("t",), terminal=False, parent=outer, leaf_substitution=_Asked())


def test_a_terminal_substitution_inside_an_outer_work_is_refused_not_merged():
    with budget_policy_scope(BudgetPolicy()):
        with serialization_scope(site="outer", target_parts=("o",)):
            with pytest.raises(ValueError):
                with serialization_scope(site="inner", target_parts=("i",), leaf_substitution=_Asked()):
                    pass


def test_a_substitution_work_is_not_merged_into_or_charged_to_the_outer_work():
    expr = _expr()
    with budget_policy_scope(BudgetPolicy()):
        with serialization_scope(site="outer", target_parts=("o",)) as outer:
            before = outer.consumed
            with serialization_scope(
                site="inner", target_parts=("i",), terminal=False, leaf_substitution=_Asked(),
            ) as inner:
                assert inner is not outer
                RESULT_JSON_POLICY.materialize(_Fields(a=expr), budget=inner)
            assert outer.consumed == before


def test_the_substitution_is_asked_even_outside_a_budget_scope():
    asked = _Asked()
    built, _consumed = _materialized(_Fields(a=_expr()), terminal=False, leaf_substitution=asked)
    assert type(built["a"]) is _Marker


def test_record_observations_false_leaves_no_observation():
    expr = _expr()
    with budget_policy_scope(BudgetPolicy()):
        _materialized(_Fields(a=expr), record_observations=False)
        assert not any(key.endswith("@test.leaf") for key in budget_observations())
        _materialized(_Fields(a=expr))
        assert any(key.endswith("@test.leaf") for key in budget_observations())
