# -*- coding: utf-8 -*-
"""Expander combination guard regressions."""

from unittest.mock import Mock

from scripts.function_tracer_pcode.analysis.condition import ConditionSimplifier
from scripts.function_tracer_pcode.model import Expression
from scripts.function_tracer_pcode.transform.expander import ExpandedValue, ExpressionExpander


def test_combine_input_expansions_deduplicates_duplicate_pairs_before_simplify(monkeypatch):
    expander = ExpressionExpander(Mock(), Mock(), debug=False)

    simplify_calls = {"count": 0}

    monkeypatch.setattr(
        ConditionSimplifier,
        "is_contradiction",
        classmethod(lambda cls, conds: False),
    )

    def _simplify(cls, conds):
        simplify_calls["count"] += 1
        return list(conds)

    monkeypatch.setattr(
        ConditionSimplifier,
        "simplify_conditions",
        classmethod(_simplify),
    )

    left = ExpandedValue(Expression.parameter("x"), [])
    right = ExpandedValue(Expression.constant(4, 4), [])

    result = expander._combine_input_expansions_with_conditions(
        "INT_ADD",
        [[left, left, left], [right, right, right]],
        [],
        depth=0,
    )

    assert len(result) == 1
    assert result[0].value.operator == "INT_ADD"
    assert simplify_calls["count"] == 1


def test_combine_input_expansions_adds_unknown_when_budget_exceeded(monkeypatch):
    expander = ExpressionExpander(Mock(), Mock(), debug=False)
    expander._max_combination_attempts = 2

    monkeypatch.setattr(
        ConditionSimplifier,
        "is_contradiction",
        classmethod(lambda cls, conds: False),
    )
    monkeypatch.setattr(
        ConditionSimplifier,
        "simplify_conditions",
        classmethod(lambda cls, conds: list(conds)),
    )

    left_expansions = [
        ExpandedValue(Expression.parameter("a"), []),
        ExpandedValue(Expression.parameter("b"), []),
    ]
    right_expansions = [
        ExpandedValue(Expression.constant(1, 4), []),
        ExpandedValue(Expression.constant(2, 4), []),
    ]

    result = expander._combine_input_expansions_with_conditions(
        "INT_ADD",
        [left_expansions, right_expansions],
        [],
        depth=0,
    )

    assert any(
        ev.value.expr_type.name == "UNKNOWN" and ev.value.name == "INT_ADD_budget_exceeded"
        for ev in result
    )
