# -*- coding: utf-8 -*-
"""Expander combination guard regressions."""

from unittest.mock import Mock

from scripts.function_tracer_pcode.analysis.condition import ConditionSimplifier
from scripts.function_tracer_pcode.model import Expression, UnknownValueRef
from scripts.function_tracer_pcode.transform.expander import ExpandedValue, ExpressionExpander


def test_combine_input_expansions_deduplicates_duplicate_pairs_before_simplify(monkeypatch):
    expander = ExpressionExpander(Mock(), Mock(), debug=False)

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


def test_combine_input_expansions_counts_unique_results_for_budget(monkeypatch):
    expander = ExpressionExpander(Mock(), Mock(), debug=False)
    expander._max_combination_attempts = 1

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

    a = Expression.parameter("a")
    b = Expression.parameter("b")
    c = Expression.parameter("c")

    left_expansions = [
        ExpandedValue(Expression.binary_op("INT_ADD", a, b), []),
        ExpandedValue(Expression.binary_op("INT_ADD", b, a), []),
    ]
    right_expansions = [
        ExpandedValue(c, []),
        ExpandedValue(c, []),
    ]

    result = expander._combine_input_expansions_with_conditions(
        "INT_ADD",
        [left_expansions, right_expansions],
        [],
        depth=0,
    )

    assert len(result) == 1
    assert all(
        not (ev.value.expr_type.name == "UNKNOWN" and ev.value.name == "INT_ADD_budget_exceeded")
        for ev in result
    )


def test_expand_expression_cases_binary_op_uses_budget_aware_combiner(monkeypatch):
    expander = ExpressionExpander(Mock(), Mock(), debug=False)
    expander._max_combination_attempts = 1

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

    a = Expression.parameter("a")
    b = Expression.parameter("b")
    c = Expression.parameter("c")

    expr = Expression.binary_op(
        "INT_ADD",
        Expression.phi(
            [
                (None, Expression.binary_op("INT_ADD", a, b)),
                (None, Expression.binary_op("INT_ADD", b, a)),
            ]
        ),
        Expression.phi(
            [
                (None, c),
                (None, c),
            ]
        ),
    )

    result = expander._expand_expression_cases(expr, [], depth=0)

    assert len(result) == 1
    assert all(
        not (ev.value.expr_type.name == "UNKNOWN" and ev.value.name == "INT_ADD_budget_exceeded")
        for ev in result
    )


def test_combine_input_expansions_drops_fully_contradictory_pairs(monkeypatch):
    expander = ExpressionExpander(Mock(), Mock(), debug=False)

    monkeypatch.setattr(
        ConditionSimplifier,
        "is_contradiction",
        classmethod(lambda cls, conds: True),
    )

    left = ExpandedValue(Expression.parameter("x"), [])
    right = ExpandedValue(Expression.constant(4, 4), [])

    result = expander._combine_input_expansions_with_conditions(
        "INT_ADD",
        [[left], [right]],
        [],
        depth=0,
    )

    assert result == []


def test_budget_results_use_traced_fallback_when_available(monkeypatch):
    expander = ExpressionExpander(Mock(), Mock(), debug=False)

    monkeypatch.setattr(
        ConditionSimplifier,
        "simplify_conditions",
        classmethod(lambda cls, conds: list(conds)),
    )

    traced = Expression.phi(
        [
            (None, Expression.constant(0, 4)),
            (None, Expression.constant(1, 4)),
        ]
    )

    monkeypatch.setattr(
        expander,
        "_trace_operation_expression",
        lambda pcode_op, conditions, depth, output_size=0: traced,
    )

    class _FakeOp:
        def getMnemonic(self):
            return "INT_ADD"

    original = [
        ExpandedValue(
            Expression.unknown(
                "INT_ADD_budget_exceeded",
                runtime_ref=UnknownValueRef.budget_exceeded(operation="INT_ADD"),
            ),
            [],
        ),
        ExpandedValue(Expression.constant(7, 4), []),
    ]

    result = expander._maybe_replace_budget_results_with_traced_fallback(
        _FakeOp(),
        original,
        [],
        depth=0,
        output_size=4,
    )

    assert len(result) == 1
    assert result[0].value.expr_type.name == "PHI"


def test_budget_results_use_traced_fallback_when_only_non_budget_unknown_remains(monkeypatch):
    expander = ExpressionExpander(Mock(), Mock(), debug=False)

    monkeypatch.setattr(
        ConditionSimplifier,
        "simplify_conditions",
        classmethod(lambda cls, conds: list(conds)),
    )

    monkeypatch.setattr(
        expander,
        "_trace_operation_expression",
        lambda pcode_op, conditions, depth, output_size=0: Expression.binary_op(
            "INT_ADD",
            Expression.unknown("still_unknown"),
            Expression.constant(1, 4),
        ),
    )

    class _FakeOp:
        def getMnemonic(self):
            return "INT_ADD"

    original = [
        ExpandedValue(
            Expression.unknown(
                "INT_ADD_budget_exceeded",
                runtime_ref=UnknownValueRef.budget_exceeded(operation="INT_ADD"),
            ),
            [],
        )
    ]

    result = expander._maybe_replace_budget_results_with_traced_fallback(
        _FakeOp(),
        original,
        [],
        depth=0,
        output_size=4,
    )

    assert len(result) == 1
    assert result[0].value.operator == "INT_ADD"


def test_budget_results_remain_when_traced_fallback_contains_call(monkeypatch):
    expander = ExpressionExpander(Mock(), Mock(), debug=False)

    monkeypatch.setattr(
        expander,
        "_trace_operation_expression",
        lambda pcode_op, conditions, depth, output_size=0: Expression.call(
            "opaque_call",
            [Expression.constant(1, 4)],
        ),
    )

    class _FakeOp:
        def getMnemonic(self):
            return "INT_ADD"

    original = [
        ExpandedValue(
            Expression.unknown(
                "INT_ADD_budget_exceeded",
                runtime_ref=UnknownValueRef.budget_exceeded(operation="INT_ADD"),
            ),
            [],
        )
    ]

    result = expander._maybe_replace_budget_results_with_traced_fallback(
        _FakeOp(),
        original,
        [],
        depth=0,
        output_size=4,
    )

    assert len(result) == 1
    assert result[0].value.expr_type.name == "UNKNOWN"
    assert result[0].value.name == "INT_ADD_budget_exceeded"
