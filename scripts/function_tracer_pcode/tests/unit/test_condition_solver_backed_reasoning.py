# -*- coding: utf-8 -*-
"""Regression tests for solver-backed condition reasoning."""

from scripts.function_tracer_pcode.analysis.condition.simplifier import (
    ConditionConstraintSet,
    ConditionSimplifier,
    ConditionSMTOracle,
)
from scripts.function_tracer_pcode.model import Condition, Expression, ExpressionType
from scripts.function_tracer_pcode.model.render_smt import normalize_call_symbol_name
from scripts.function_tracer_pcode.model.render_smt import expression_contains_unsupported_smt_ops


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


def test_solver_backed_reasoning_activates_for_boolean_connective_structure(monkeypatch):
    cond = Condition(
        Expression.unary_op(
            "BOOL_NEGATE",
            Expression.binary_op(
                "BOOL_AND",
                Expression.binary_op("INT_EQUAL", _param("param_1"), _const(0)),
                Expression.binary_op("INT_EQUAL", _param("param_2"), _const(1)),
            ),
        ),
        False,
    )

    invoked = {"count": 0}

    def _fake_conjunction_is_unsat(conditions, cache_key=None):
        invoked["count"] += 1
        return None

    monkeypatch.setattr(
        ConditionSimplifier,
        "_can_use_solver_reasoning",
        classmethod(lambda _cls, _conditions: True),
    )
    monkeypatch.setattr(ConditionSMTOracle, "conjunction_is_unsat", _fake_conjunction_is_unsat)

    constraint_set = ConditionConstraintSet.from_conditions([cond])

    assert constraint_set.solver_backed is True
    assert invoked["count"] >= 1


def test_solver_backed_reasoning_activates_for_non_connective_comparison(monkeypatch):
    cond = Condition(Expression.binary_op("INT_LESS", _param("param_1"), _const(1)), False)

    invoked = {"count": 0}

    def _fake_conjunction_is_unsat(conditions, cache_key=None):
        invoked["count"] += 1
        return None

    monkeypatch.setattr(
        ConditionSimplifier,
        "_can_use_solver_reasoning",
        classmethod(lambda _cls, _conditions: True),
    )
    monkeypatch.setattr(ConditionSMTOracle, "conjunction_is_unsat", _fake_conjunction_is_unsat)

    constraint_set = ConditionConstraintSet.from_conditions([cond])

    assert constraint_set.solver_backed is True
    assert invoked["count"] >= 1


def test_solver_backed_reasoning_activates_for_call_comparison(monkeypatch):
    cond = Condition(
        Expression.binary_op(
            "INT_EQUAL",
            Expression.call("callee", [_param("param_1")]),
            _const(0),
        ),
        False,
    )

    invoked = {"count": 0}

    def _fake_conjunction_is_unsat(conditions, cache_key=None):
        invoked["count"] += 1
        return None

    monkeypatch.setattr(
        ConditionSimplifier,
        "_can_use_solver_reasoning",
        classmethod(lambda _cls, _conditions: True),
    )
    monkeypatch.setattr(ConditionSMTOracle, "conjunction_is_unsat", _fake_conjunction_is_unsat)

    constraint_set = ConditionConstraintSet.from_conditions([cond])

    assert constraint_set.solver_backed is True
    assert invoked["count"] >= 1


def test_call_expression_supported_when_enabled_in_smt_op_filtering():
    expr = Expression.binary_op(
        "INT_EQUAL",
        Expression.call("callee", [_param("param_1")]),
        _const(0),
    )

    assert expression_contains_unsupported_smt_ops(expr, allow_call=False) is True
    assert expression_contains_unsupported_smt_ops(expr, allow_call=True) is False


def test_reduce_expression_under_conditions_skips_circular_phi_recursion():
    self_condition = Condition(Expression.binary_op("INT_EQUAL", _param("param_1"), _const(1, 4)), False)
    circular_phi = Expression.phi([])
    circular_phi.value = [(self_condition, circular_phi)]

    reduced = ConditionSimplifier._reduce_expression_under_conditions(
        circular_phi,
        [self_condition],
    )

    assert reduced is circular_phi


def test_smt_oracle_iter_expression_nodes_handles_circular_phi():
    self_condition = Condition(
        Expression.binary_op("INT_NOTEQUAL", _param("param_1"), _const(0, 4)),
        False,
    )
    circular_phi = Expression.phi([])
    circular_phi.value = [(self_condition, circular_phi)]

    nodes = list(ConditionSMTOracle._iter_expression_nodes(circular_phi))
    assert len(nodes) >= 1
    assert len(nodes) == len({id(node) for node in nodes})


def test_solver_backed_script_sanitizes_call_symbols():
    cond = Condition(
        Expression.binary_op(
            "INT_EQUAL",
            Expression.call("call-foo*", [_param("param_1")]),
            _const(0),
        ),
        False,
    )

    usable, script = ConditionSMTOracle._build_script([cond])
    assert usable is True
    assert script is not None
    assert normalize_call_symbol_name("call-foo*") in script


def test_object_centric_condition_basis_prunes_negated_compound_implied_by_atomic_branch_facts():
    param_1_nonnull = Condition(
        Expression.binary_op("INT_NOTEQUAL", _param("param_1", size=8), _const(0, size=8)),
        False,
    )
    param_3_nonzero = Condition(
        Expression.binary_op("INT_NOTEQUAL", _param("param_3"), _const(0)),
        False,
    )
    not_add_branch = Condition(
        Expression.unary_op(
            "BOOL_NEGATE",
            Expression.binary_op(
                "BOOL_AND",
                param_1_nonnull.expression,
                Expression.unary_op("BOOL_NEGATE", param_3_nonzero.expression),
            ),
        ),
        False,
    )

    basis = ConditionSimplifier.build_object_centric_condition_basis(
        [not_add_branch, param_1_nonnull, param_3_nonzero]
    )

    assert len(basis) == 2
    assert any(cond.equals(param_1_nonnull) for cond in basis)
    assert any(cond.equals(param_3_nonzero) for cond in basis)
    assert all(not cond.equals(not_add_branch) for cond in basis)


def test_smt_oracle_cache_key_is_structural_and_order_independent():
    cond_a = Condition(
        Expression.binary_op(
            "INT_NOTEQUAL",
            Expression(ExpressionType.PARAMETER, name="param_1", value=0, size=4),
            Expression(ExpressionType.CONSTANT, value=0, size=4),
        )
    )
    cond_b = Condition(
        Expression.binary_op(
            "INT_NOTEQUAL",
            Expression(ExpressionType.PARAMETER, name="param_1", value=0, size=4),
            Expression(ExpressionType.CONSTANT, value=0, size=4),
        )
    )

    key_one = ConditionSMTOracle._build_cache_key((cond_a, cond_b))
    key_two = ConditionSMTOracle._build_cache_key((cond_b, cond_a))
    key_single = ConditionSMTOracle._build_cache_key((cond_a,))
    key_single_negated = ConditionSMTOracle._build_cache_key((Condition(cond_a.expression, True),))

    assert key_one == key_two
    assert key_single != key_single_negated
