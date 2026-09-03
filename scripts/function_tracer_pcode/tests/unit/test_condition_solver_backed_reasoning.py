# -*- coding: utf-8 -*-
"""Regression tests for solver-backed condition reasoning."""

from scripts.function_tracer_pcode.analysis.condition.simplifier import (
    ConditionConstraintSet,
    ConditionSimplifier,
    ConditionSMTOracle,
)
from scripts.function_tracer_pcode.core import (
    CanonicalLocation,
    Condition,
    Expression,
    ExpressionType,
    LocationBaseRef,
    PostStateReadRef,
)
from scripts.function_tracer_pcode.core.storage import StorageInfo
from scripts.function_tracer_pcode.core.render_smt import normalize_call_symbol_name
from scripts.function_tracer_pcode.core.render_smt import expression_contains_unsupported_smt_ops


def _const(value: int, size: int = 4) -> Expression:
    return Expression.constant(value, size=size)


def _param(name: str, size: int = 4) -> Expression:
    return Expression.parameter(name, index=-1, size=size, runtime_ref=None)


def _indexed_param(name: str, index: int, size: int = 4) -> Expression:
    return Expression.parameter(
        name,
        index=index,
        size=size,
        runtime_ref=LocationBaseRef.parameter(name, index=index),
    )


def _deep_selected_branch() -> Expression:
    acc = _indexed_param("param_2", 1)
    for value in range(1, 10):
        acc = Expression.binary_op("INT_ADD", acc, _const(value))
    return Expression.binary_op("INT_EQUAL", acc, _const(52))


def test_solver_backed_constraint_set_skips_recursive_context_reduction(monkeypatch):
    selector = Expression.binary_op("INT_EQUAL", _indexed_param("param_1", 0), _const(0))
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


def test_smt_oracle_declares_float_predicates_for_condition_queries():
    cond_expr = Expression.binary_op(
        "FLOAT_LESS",
        _indexed_param("param_2", 1, size=8),
        _indexed_param("param_1", 0, size=8),
    )
    conditions = [
        Condition(cond_expr, False),
        Condition(cond_expr, True),
    ]

    usable, script = ConditionSMTOracle._build_script(conditions)

    assert usable is True
    assert script is not None
    assert "(set-logic QF_AUFBVFP)" in script
    assert "fp.lt" in script
    assert "float_less" not in script
    assert "Floating-point predicate axioms" not in script
    assert ConditionSMTOracle.conjunction_is_unsat(conditions) is True


def test_smt_oracle_does_not_assume_ordered_float_complement():
    less_expr = Expression.binary_op(
        "FLOAT_LESS",
        _indexed_param("param_1", 0, size=8),
        _indexed_param("param_2", 1, size=8),
    )
    le_expr = Expression.binary_op(
        "FLOAT_LESSEQUAL",
        _indexed_param("param_2", 1, size=8),
        _indexed_param("param_1", 0, size=8),
    )
    conditions = [
        Condition(less_expr, True),
        Condition(le_expr, True),
    ]

    usable, script = ConditionSMTOracle._build_script(conditions)

    assert usable is True
    assert script is not None
    assert "(assert (= " not in script
    assert "fp.lt" in script
    assert "fp.leq" in script
    assert ConditionSMTOracle.conjunction_is_unsat(conditions) is False


def test_smt_oracle_authority_mode_bypasses_boolean_cache(monkeypatch):
    class AlwaysUnsatCache(dict):
        def get(self, _key, _default=None):
            return True

    monkeypatch.setattr(ConditionSMTOracle, "_unsat_cache", AlwaysUnsatCache())
    satisfiable = [Condition(Expression.constant(1, size=1), False)]

    assert ConditionSMTOracle.conjunction_is_unsat(satisfiable) is True
    assert ConditionSMTOracle.conjunction_is_unsat(
        satisfiable, use_cache=False
    ) is False


def test_solver_backed_implication_handles_phi_with_unknown_branch():
    selector = Expression.binary_op("INT_EQUAL", _indexed_param("param_1", 0), _const(0))
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
                Expression.binary_op("INT_EQUAL", _indexed_param("param_1", 0), _const(0)),
                Expression.binary_op("INT_EQUAL", _indexed_param("param_2", 1), _const(1)),
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
    cond = Condition(Expression.binary_op("INT_LESS", _indexed_param("param_1", 0), _const(1)), False)

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
            Expression.call("callee", [_indexed_param("param_1", 0)]),
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
        Expression.call("callee", [_indexed_param("param_1", 0)]),
        _const(0),
    )

    assert expression_contains_unsupported_smt_ops(expr, allow_call=False) is True
    assert expression_contains_unsupported_smt_ops(expr, allow_call=True) is False


def test_reduce_expression_under_conditions_skips_circular_phi_recursion():
    self_condition = Condition(Expression.binary_op("INT_EQUAL", _indexed_param("param_1", 0), _const(1, 4)), False)
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
            Expression.call("call-foo*", [_indexed_param("param_1", 0)]),
            _const(0),
        ),
        False,
    )

    usable, script = ConditionSMTOracle._build_script([cond])
    assert usable is True
    assert script is not None
    assert normalize_call_symbol_name("call-foo*") in script


def test_smt_oracle_keeps_distinct_params_from_same_name_distinct_if_different_runtime_refs():
    p0 = Expression.parameter(
        "count",
        index=0,
        size=4,
        runtime_ref=LocationBaseRef.parameter("count", index=0),
    )
    p1 = Expression.parameter(
        "count",
        index=1,
        size=4,
        runtime_ref=LocationBaseRef.parameter("count", index=1),
    )
    cond0 = Condition(Expression.binary_op("INT_EQUAL", p0, _const(0)), False)
    cond1 = Condition(Expression.binary_op("INT_NOTEQUAL", p1, _const(0)), False)

    usable, script = ConditionSMTOracle._build_script([cond0, cond1])
    assert usable is True
    assert script is not None
    assert ConditionSMTOracle.conjunction_is_unsat([cond0, cond1]) is False

    declare_lines = [line for line in script.splitlines() if line.startswith("(declare-const ")]
    names = []
    for line in declare_lines:
        parts = line.split()
        if len(parts) >= 3:
            names.append(parts[1])
    assert len(set(names)) == len(names)


def test_smt_oracle_declines_object_identity_unsafe_parameters():
    p0 = Expression.parameter("count", index=-1, size=4)
    cond = Condition(Expression.binary_op("INT_EQUAL", p0, _const(0)), False)
    usable, script = ConditionSMTOracle._build_script([cond])
    assert usable is False
    assert script is None
    assert ConditionSMTOracle.conjunction_is_unsat([cond]) is None


def test_smt_oracle_declines_parameter_runtime_ref_without_index():
    p0 = Expression.parameter(
        "count",
        index=-1,
        size=4,
        runtime_ref=LocationBaseRef.parameter("count"),
    )
    cond = Condition(Expression.binary_op("INT_EQUAL", p0, _const(0)), False)

    usable, script = ConditionSMTOracle._build_script([cond])

    assert usable is False
    assert script is None
    assert ConditionSMTOracle.conjunction_is_unsat([cond]) is None


def test_smt_oracle_declines_name_only_parameter_nested_in_canonical_location():
    loc = CanonicalLocation(
        base_ref=LocationBaseRef.parameter("count"),
        offset=0,
        size=4,
    )
    expr = Expression.variable("post_count", size=4, runtime_ref=loc)
    cond = Condition(Expression.binary_op("INT_EQUAL", expr, _const(0)), False)

    assert ConditionSMTOracle._build_script([cond]) == (False, None)
    assert ConditionSMTOracle.conjunction_is_unsat([cond]) is None


def test_smt_oracle_declines_name_only_parameter_nested_in_post_state_read_ref():
    loc = CanonicalLocation(
        base_ref=LocationBaseRef.parameter("count"),
        offset=0,
        size=4,
    )
    ref = PostStateReadRef(location=loc)
    expr = Expression.variable("post_count", size=4, runtime_ref=ref)
    cond = Condition(Expression.binary_op("INT_EQUAL", expr, _const(0)), False)

    assert ConditionSMTOracle._build_script([cond]) == (False, None)
    assert ConditionSMTOracle.conjunction_is_unsat([cond]) is None


def test_smt_oracle_declines_param_pattern_without_object_identity():
    p0 = Expression.parameter("param_1", index=-1, size=4, runtime_ref=None)
    cond = Condition(Expression.binary_op("INT_EQUAL", p0, _const(0)), False)

    usable, script = ConditionSMTOracle._build_script([cond])

    assert usable is False
    assert script is None
    assert ConditionSMTOracle.conjunction_is_unsat([cond]) is None


def test_smt_oracle_proves_subpiece_sext_singleton_bound_contradiction():
    count = _indexed_param("param_2", 1, size=4)
    low = Expression.binary_op("SUBPIECE", count, _const(0, size=4)).clone_with(size=4)
    widened = Expression.unary_op("INT_SEXT", low).clone_with(size=8)
    conditions = [
        Condition(Expression.binary_op("INT_EQUAL", count, _const(2, size=4)), False),
        Condition(Expression.binary_op("INT_SLESS", _const(2, size=8), widened), False),
    ]

    assert ConditionSMTOracle.conjunction_is_unsat(conditions) is True


def test_smt_oracle_reuses_rewritten_shared_expression_nodes():
    p = Expression.parameter(
        "count",
        index=0,
        size=4,
        runtime_ref=LocationBaseRef.parameter("count", index=0),
    )
    shared_eq = Expression.binary_op("INT_EQUAL", p, _const(0))
    shared_ne = Expression.binary_op("INT_NOTEQUAL", p, _const(0))
    cond = Condition(Expression.binary_op("BOOL_AND", shared_eq, shared_ne), False)

    usable, script = ConditionSMTOracle._build_script([cond])
    assert usable is True
    assert script is not None

    declarations = [line for line in script.splitlines() if line.startswith("(declare-const ")]
    declared_names = {line.split()[1] for line in declarations if len(line.split()) >= 3}
    assert len(declared_names) == 1
    assert "count" not in {name for name in declared_names}
    assert any("objvar_" in name for name in declared_names)


def test_smt_oracle_uses_storage_identity_key_for_parameter_without_index():
    storage_info = StorageInfo(
        is_register=False,
        space_id=0,
        offset=0x2000,
        size=4,
        size_bits=32,
    )
    p0 = Expression.parameter(
        "count",
        index=-1,
        size=4,
        storage_info=storage_info,
    )
    p1 = Expression.parameter(
        "count",
        index=-1,
        size=4,
        storage_info=storage_info,
    )
    cond = Condition(Expression.binary_op("INT_EQUAL", p0, _const(0)), False)
    cond2 = Condition(Expression.binary_op("INT_NOTEQUAL", p1, _const(0)), False)

    usable, script = ConditionSMTOracle._build_script([cond, cond2])
    assert usable is True
    assert script is not None

    declarations = [line for line in script.splitlines() if line.startswith("(declare-const ")]
    declared_names = [line.split()[1] for line in declarations if len(line.split()) >= 3]
    assert len(set(declared_names)) == 1


def test_object_centric_condition_basis_prunes_negated_compound_implied_by_atomic_branch_facts():
    param_1_nonnull = Condition(
        Expression.binary_op("INT_NOTEQUAL", _indexed_param("param_1", 0, size=8), _const(0, size=8)),
        False,
    )
    param_3_nonzero = Condition(
        Expression.binary_op("INT_NOTEQUAL", _indexed_param("param_3", 2), _const(0)),
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
    assert key_one[0] == "unsat"
    assert key_one[1] == ConditionSMTOracle._CACHE_KEY_SCHEMA_VERSION


def test_smt_oracle_cache_key_declines_placeholder_components(monkeypatch):
    import scripts.function_tracer_pcode.analysis.condition.smt_oracle as smt_oracle

    cond = Condition(
        Expression.binary_op(
            "INT_NOTEQUAL",
            Expression(ExpressionType.PARAMETER, name="param_1", value=0, size=4),
            Expression(ExpressionType.CONSTANT, value=0, size=4),
        )
    )
    monkeypatch.setattr(smt_oracle, "condition_key", lambda _condition, budget=96: ("placeholder",))
    monkeypatch.setattr(smt_oracle, "key_contains_placeholder", lambda _key: True)

    assert ConditionSMTOracle._build_cache_key((cond,)) is None


def test_smt_oracle_cache_key_declines_unsafe_components(monkeypatch):
    import scripts.function_tracer_pcode.analysis.condition.smt_oracle as smt_oracle

    cond = Condition(
        Expression.binary_op(
            "INT_NOTEQUAL",
            Expression(ExpressionType.PARAMETER, name="param_1", value=0, size=4),
            Expression(ExpressionType.CONSTANT, value=0, size=4),
        )
    )

    def raise_attribute_error(_condition, budget=96):
        raise AttributeError("synthetic structural key failure")

    monkeypatch.setattr(smt_oracle, "condition_key", raise_attribute_error)

    assert ConditionSMTOracle._build_cache_key((cond,)) is None
