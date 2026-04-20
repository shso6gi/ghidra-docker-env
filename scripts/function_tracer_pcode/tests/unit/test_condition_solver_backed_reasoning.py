# -*- coding: utf-8 -*-
"""Regression tests for solver-backed condition reasoning."""

from scripts.function_tracer_pcode.analysis.condition.simplifier import (
    ConditionConstraintSet,
    ConditionSimplifier,
)
from scripts.function_tracer_pcode.model import Condition, Expression


def _const(value: int, size: int = 4) -> Expression:
    return Expression.constant(value, size=size)


def _param(name: str, size: int = 4) -> Expression:
    return Expression.parameter(name, size=size)


def _deep_selected_branch() -> Expression:
    acc = _param("param_2")
    for value in range(1, 10):
        acc = Expression.binary_op("INT_ADD", acc, _const(value))
    return Expression.binary_op("INT_EQUAL", acc, _const(52))


def test_solver_backed_constraint_set_skips_recursive_context_reduction(monkeypatch):
    selector = Expression.binary_op("INT_EQUAL", _param("param_1"), _const(0))
    unknown_bool = Expression.binary_op("INT_EQUAL", Expression.unknown("phi_circular"), _const(0, 1))
    selected_branch = _deep_selected_branch()
    recursive_phi = Expression.phi(
        [
            (Condition(selector, False), selected_branch),
            (Condition(selector, True), unknown_bool),
        ]
    )
    conditions = [
        Condition(recursive_phi, True),
        Condition(selector, False),
        Condition(selected_branch, False),
    ]

    def _boom(_conditions):
        raise AssertionError("_contextually_reduce_conditions should not run for solver-backed sets")

    monkeypatch.setattr(ConditionSimplifier, "_contextually_reduce_conditions", _boom)

    constraint_set = ConditionConstraintSet.from_conditions(conditions)

    assert constraint_set.solver_backed is True
    assert constraint_set.is_contradictory is True


def test_solver_backed_implication_handles_phi_with_unknown_branch():
    selector = Expression.binary_op("INT_EQUAL", _param("param_1"), _const(0))
    selected_branch = _deep_selected_branch()
    unknown_bool = Expression.binary_op("INT_EQUAL", Expression.unknown("phi_circular"), _const(0, 1))
    recursive_phi = Expression.phi(
        [
            (Condition(selector, False), selected_branch),
            (Condition(selector, True), unknown_bool),
        ]
    )
    constraint_set = ConditionConstraintSet.from_conditions(
        [
            Condition(selector, False),
            Condition(selected_branch, False),
            Condition(recursive_phi, False),
        ]
    )

    assert constraint_set.solver_backed is True
    assert constraint_set.implies_condition(Condition(selected_branch, False)) is True
    assert constraint_set.implies_condition(Condition(selected_branch, True)) is False
