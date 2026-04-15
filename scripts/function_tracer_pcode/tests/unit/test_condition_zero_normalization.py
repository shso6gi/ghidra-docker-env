# -*- coding: utf-8 -*-
"""0 比較の条件正規化に関する回帰テスト"""

import sys
from pathlib import Path


workspace_root = Path(__file__).parent.parent.parent.parent
if str(workspace_root) not in sys.path:
    sys.path.insert(0, str(workspace_root))

from scripts.function_tracer_pcode.analysis.condition.normalizer import (
    ConditionNormalizer,
)
from scripts.function_tracer_pcode.analysis.condition.simplifier import (
    ConditionSimplifier,
)
from scripts.function_tracer_pcode.model import Condition, Expression, ExpressionType


def _param(name: str) -> Expression:
    return Expression(ExpressionType.PARAMETER, name=name, size=8)


def _const(value: int) -> Expression:
    return Expression(ExpressionType.CONSTANT, value=value, size=8)


def _neg(expr: Expression) -> Expression:
    return Expression(
        ExpressionType.UNARY_OP,
        operator="INT_2COMP",
        operands=[expr],
        size=8,
    )


def _or(left: Expression, right: Expression) -> Expression:
    return Expression(
        ExpressionType.BINARY_OP,
        operator="BOOL_OR",
        operands=[left, right],
        size=1,
    )


def _and(left: Expression, right: Expression) -> Expression:
    return Expression(
        ExpressionType.BINARY_OP,
        operator="BOOL_AND",
        operands=[left, right],
        size=1,
    )


def test_normalize_zero_comparison_accepts_constant_zero():
    cond = Condition(
        Expression(
            ExpressionType.BINARY_OP,
            operator="INT_EQUAL",
            operands=[_neg(_param("param_2")), _const(0)],
            size=1,
        )
    )

    left, op, right, polarity = ConditionNormalizer.normalize_for_contradiction(cond)

    assert (
        left,
        op,
        right,
        polarity,
    ) == (_param("param_2").structural_key(), "INT_EQUAL", _const(0).structural_key(), True)


def test_negated_zero_comparison_contradicts_nonzero_condition():
    conditions = [
        Condition(
            Expression(
                ExpressionType.BINARY_OP,
                operator="INT_NOTEQUAL",
                operands=[_param("param_2"), _const(0)],
                size=1,
            )
        ),
        Condition(
            Expression(
                ExpressionType.BINARY_OP,
                operator="INT_EQUAL",
                operands=[_neg(_param("param_2")), _const(0)],
                size=1,
            )
        ),
    ]

    assert ConditionSimplifier.is_contradiction(conditions) is True


def test_negated_zero_comparison_matches_zero_condition():
    conditions = [
        Condition(
            Expression(
                ExpressionType.BINARY_OP,
                operator="INT_EQUAL",
                operands=[_param("param_2"), _const(0)],
                size=1,
            )
        ),
        Condition(
            Expression(
                ExpressionType.BINARY_OP,
                operator="INT_EQUAL",
                operands=[_neg(_param("param_2")), _const(0)],
                size=1,
            )
        ),
    ]

    assert ConditionSimplifier.is_contradiction(conditions) is False


def test_or_clause_contradiction_detects_all_literals_ruled_out():
    cond_a = Condition(
        Expression(
            ExpressionType.BINARY_OP,
            operator="INT_EQUAL",
            operands=[_param("param_1"), _const(0)],
            size=1,
        )
    )
    cond_b = Condition(
        Expression(
            ExpressionType.BINARY_OP,
            operator="INT_EQUAL",
            operands=[_param("param_2"), _const(0)],
            size=1,
        )
    )
    conditions = [
        Condition(_or(cond_a.expression, cond_b.expression)),
        cond_a.negate(),
        cond_b.negate(),
    ]

    assert ConditionSimplifier.is_contradiction(conditions) is True


def test_constraint_set_implies_or_clause_from_unit_literal():
    cond_a = Condition(
        Expression(
            ExpressionType.BINARY_OP,
            operator="INT_EQUAL",
            operands=[_param("param_1"), _const(0)],
            size=1,
        )
    )
    cond_b = Condition(
        Expression(
            ExpressionType.BINARY_OP,
            operator="INT_EQUAL",
            operands=[_param("param_2"), _const(0)],
            size=1,
        )
    )
    constraint_set = ConditionSimplifier.build_constraint_set([cond_a])

    assert constraint_set.implies_condition(Condition(_or(cond_a.expression, cond_b.expression))) is True


def test_constraint_set_implies_negated_or_clause_from_all_negated_literals():
    cond_a = Condition(
        Expression(
            ExpressionType.BINARY_OP,
            operator="INT_EQUAL",
            operands=[_param("param_1"), _const(0)],
            size=1,
        )
    )
    cond_b = Condition(
        Expression(
            ExpressionType.BINARY_OP,
            operator="INT_EQUAL",
            operands=[_param("param_2"), _const(0)],
            size=1,
        )
    )
    negated_or = Condition(_or(cond_a.expression, cond_b.expression), negated=True)
    constraint_set = ConditionSimplifier.build_constraint_set(
        [cond_a.negate(), cond_b.negate()]
    )

    assert constraint_set.implies_condition(negated_or) is True


def test_constraint_set_detects_negated_and_overlap_precisely():
    cond_a = Condition(
        Expression(
            ExpressionType.BINARY_OP,
            operator="INT_EQUAL",
            operands=[_param("param_1"), _const(0)],
            size=1,
        )
    )
    cond_b = Condition(
        Expression(
            ExpressionType.BINARY_OP,
            operator="INT_EQUAL",
            operands=[_param("param_2"), _const(0)],
            size=1,
        )
    )
    left = ConditionSimplifier.build_constraint_set(
        [Condition(_and(cond_a.expression, cond_b.expression), negated=True)]
    )
    right = ConditionSimplifier.build_constraint_set([cond_a, cond_b])

    assert left.overlaps_with(right.conditions) is False


def test_constant_false_condition_is_contradiction():
    conditions = [
        Condition(
            Expression(
                ExpressionType.BINARY_OP,
                operator="INT_EQUAL",
                operands=[_neg(_const(2)), _const(0)],
                size=1,
            )
        ),
    ]

    assert ConditionSimplifier.is_contradiction(conditions) is True


def test_simplify_conditions_drops_constant_true_conditions():
    conditions = [
        Condition(
            Expression(
                ExpressionType.BINARY_OP,
                operator="INT_EQUAL",
                operands=[_neg(_const(2)), _const(0)],
                size=1,
            ),
            negated=True,
        ),
        Condition(
            Expression(
                ExpressionType.BINARY_OP,
                operator="INT_NOTEQUAL",
                operands=[_param("param_2"), _const(0)],
                size=1,
            )
        ),
    ]

    simplified = ConditionSimplifier.simplify_conditions(conditions)

    assert [cond.to_string() for cond in simplified] == ["(param_2 != 0)"]


def test_simplify_conditions_preserves_eq_ne_contradiction_witness():
    conditions = [
        Condition(
            Expression(
                ExpressionType.BINARY_OP,
                operator="INT_EQUAL",
                operands=[_param("param_2"), _const(0)],
                size=1,
            )
        ),
        Condition(
            Expression(
                ExpressionType.BINARY_OP,
                operator="INT_NOTEQUAL",
                operands=[_param("param_2"), _const(0)],
                size=1,
            )
        ),
    ]

    simplified = ConditionSimplifier.simplify_conditions(conditions)

    assert {cond.to_string() for cond in simplified} == {"(param_2 == 0)", "(param_2 != 0)"}
    assert ConditionSimplifier.is_contradiction(simplified) is True


def test_interval_contradiction_detects_incompatible_signed_bounds():
    conditions = [
        Condition(
            Expression(
                ExpressionType.BINARY_OP,
                operator="INT_SLESSEQUAL",
                operands=[_const(0), _param("param_1")],
                size=1,
            )
        ),
        Condition(
            Expression(
                ExpressionType.BINARY_OP,
                operator="INT_SLESSEQUAL",
                operands=[_param("param_1"), _const(-1)],
                size=1,
            )
        ),
    ]

    assert ConditionSimplifier.is_contradiction(conditions) is True


def test_interval_contradiction_detects_singleton_excluded_by_nonzero():
    conditions = [
        Condition(
            Expression(
                ExpressionType.BINARY_OP,
                operator="INT_NOTEQUAL",
                operands=[_param("param_2"), _const(0)],
                size=1,
            )
        ),
        Condition(
            Expression(
                ExpressionType.BINARY_OP,
                operator="INT_SLESSEQUAL",
                operands=[_const(0), _param("param_2")],
                size=1,
            )
        ),
        Condition(
            Expression(
                ExpressionType.BINARY_OP,
                operator="INT_SLESS",
                operands=[_param("param_2"), _const(1)],
                size=1,
            )
        ),
    ]

    assert ConditionSimplifier.is_contradiction(conditions) is True


def test_simplify_conditions_keeps_only_strongest_interval_bounds():
    conditions = [
        Condition(
            Expression(
                ExpressionType.BINARY_OP,
                operator="INT_SLESSEQUAL",
                operands=[_const(0), _param("param_2")],
                size=1,
            )
        ),
        Condition(
            Expression(
                ExpressionType.BINARY_OP,
                operator="INT_SLESS",
                operands=[_const(0), _param("param_2")],
                size=1,
            )
        ),
        Condition(
            Expression(
                ExpressionType.BINARY_OP,
                operator="INT_SLESS",
                operands=[_param("param_2"), _const(8)],
                size=1,
            )
        ),
        Condition(
            Expression(
                ExpressionType.BINARY_OP,
                operator="INT_SLESSEQUAL",
                operands=[_param("param_2"), _const(10)],
                size=1,
            )
        ),
    ]

    simplified = ConditionSimplifier.simplify_conditions(conditions)

    assert [ConditionSimplifier.get_simplified_condition_string(cond) for cond in simplified] == [
        "(0 < param_2)",
        "(param_2 < 8)",
    ]


def test_normalize_for_contradiction_skips_full_render_for_large_expression(monkeypatch):
    huge = _param("param_1")
    for _ in range(64):
        huge = Expression.binary_op("INT_ADD", huge, _const(1))

    cond = Condition(
        Expression(
            ExpressionType.BINARY_OP,
            operator="INT_NOTEQUAL",
            operands=[huge, _const(0)],
            size=1,
        )
    )

    def _boom(_self, simplify=True):
        raise AssertionError("to_string should not be used by contradiction normalization")

    monkeypatch.setattr(Expression, "to_string", _boom)

    left, op, right, polarity = ConditionNormalizer.normalize_for_contradiction(cond)

    assert op == "INT_EQUAL"
    assert polarity is False
    assert left or right


def test_normalize_non_comparison_condition_does_not_call_expression_to_string(monkeypatch):
    condition = Condition(
        Expression(
            ExpressionType.BINARY_OP,
            operator="INT_ADD",
            operands=[_param("param_1"), _const(1)],
            size=8,
        )
    )

    def _boom(*_args, **_kwargs):
        raise AssertionError("normalize() should not depend on Expression.to_string")

    monkeypatch.setattr(Expression, "to_string", _boom)

    left, op, right, polarity = ConditionNormalizer.normalize(condition)

    assert op == ""
    assert polarity is False
    assert isinstance(left, tuple)
    assert isinstance(right, tuple)
    assert left and right


def test_is_contradiction_skips_pairwise_check_for_duplicate_comparisons(monkeypatch):
    duplicate_conditions = [
        Condition(
            Expression(
                ExpressionType.BINARY_OP,
                operator="INT_SLESS",
                operands=[_param("param_1"), _const(0)],
                size=1,
            ),
            negated=True,
        ),
        Condition(
            Expression(
                ExpressionType.BINARY_OP,
                operator="INT_LESS",
                operands=[Expression.binary_op("INT_ADD", _param("param_1"), _const(1)), _const(8)],
                size=1,
            ),
            negated=True,
        ),
        Condition(
            Expression(
                ExpressionType.BINARY_OP,
                operator="INT_NOTEQUAL",
                operands=[
                    Expression.binary_op(
                        "INT_SUB",
                        Expression.binary_op(
                            "INT_AND",
                            Expression.binary_op("INT_ADD", _param("param_1"), _const(1)),
                            _const(0xFFFFFFF8),
                        ),
                        _const(8),
                    ),
                    _const(0),
                ],
                size=1,
            )
        ),
    ]
    duplicate_conditions = duplicate_conditions + duplicate_conditions

    def _boom(*_args, **_kwargs):
        raise AssertionError("comparison-only contradiction checks should not reach pairwise fallback")

    monkeypatch.setattr(ConditionNormalizer, "are_contradictory", staticmethod(_boom))

    assert ConditionSimplifier.is_contradiction(duplicate_conditions) is False


def test_condition_simplifier_debug_paths_do_not_require_full_to_string(monkeypatch):
    original_debug = ConditionSimplifier.DEBUG
    original_limit = ConditionSimplifier._DEBUG_MESSAGE_LIMIT
    original_counts = dict(ConditionSimplifier._debug_repeat_counts)
    ConditionSimplifier.DEBUG = True
    ConditionSimplifier._DEBUG_MESSAGE_LIMIT = 100
    ConditionSimplifier._debug_repeat_counts.clear()
    ConditionSimplifier._debug_message_count = 0
    ConditionSimplifier._debug_suppressed = False

    huge = _param("param_1")
    for _ in range(64):
        huge = Expression.binary_op("INT_ADD", huge, _const(1))

    condition = Condition(
        Expression(
            ExpressionType.BINARY_OP,
            operator="INT_NOTEQUAL",
            operands=[huge, _const(0)],
            size=1,
        )
    )

    def _boom(_self, simplify=True):
        raise AssertionError("ConditionSimplifier debug paths should not call Expression.to_string")

    monkeypatch.setattr(Expression, "to_string", _boom)

    try:
        flattened = ConditionSimplifier.flatten_condition(condition)
        assert len(flattened) == 1
        assert ConditionSimplifier.is_contradiction([condition, condition]) is False
    finally:
        ConditionSimplifier.DEBUG = original_debug
        ConditionSimplifier._DEBUG_MESSAGE_LIMIT = original_limit
        ConditionSimplifier._debug_repeat_counts.clear()
        ConditionSimplifier._debug_repeat_counts.update(original_counts)
        ConditionSimplifier._debug_message_count = 0
        ConditionSimplifier._debug_suppressed = False


def test_condition_simplifier_debug_budget_suppresses_heavy_summaries(monkeypatch):
    original_debug = ConditionSimplifier.DEBUG
    original_limit = ConditionSimplifier._DEBUG_MESSAGE_LIMIT
    ConditionSimplifier.DEBUG = True
    ConditionSimplifier._DEBUG_MESSAGE_LIMIT = 0
    ConditionSimplifier._debug_message_count = 0
    ConditionSimplifier._debug_suppressed = False

    huge = _param("param_1")
    for _ in range(64):
        huge = Expression.binary_op("INT_ADD", huge, _const(1))

    def _boom(_self, simplify=True):
        raise AssertionError("suppressed debug summaries should not call Expression.to_string")

    monkeypatch.setattr(Expression, "to_string", _boom)

    try:
        summary = ConditionSimplifier._debug_condition_summary(Condition(huge))
        assert summary == "<debug-suppressed>"
    finally:
        ConditionSimplifier.DEBUG = original_debug
        ConditionSimplifier._DEBUG_MESSAGE_LIMIT = original_limit
        ConditionSimplifier._debug_message_count = 0
        ConditionSimplifier._debug_suppressed = False


def test_simplify_conditions_reduces_phi_guard_under_selector_context():
    selector = Expression.binary_op("INT_SLESS", _param("param_2"), _param("param_1"))
    selector_is_zero = Expression.binary_op("INT_EQUAL", selector, _const(0))
    bool_phi = Expression.phi(
        [
            (
                Condition(selector_is_zero, True),
                Expression.binary_op("INT_SLESS", _param("param_3"), Expression.binary_op("INT_ADD", _param("param_1"), _const(10))),
            ),
            (
                Condition(selector_is_zero, False),
                Expression.binary_op(
                    "INT_SLESS",
                    _param("param_3"),
                    Expression.binary_op("INT_ADD", Expression.binary_op("INT_MULT", _param("param_2"), _const(3)), _const(1)),
                ),
            ),
        ]
    )

    conditions = [
        Condition(bool_phi, True),
        Condition(selector_is_zero, False),
    ]

    simplified = ConditionSimplifier.simplify_conditions(conditions)
    simplified_strings = [cond.to_string() for cond in simplified]

    assert "(not PHI(" not in " ".join(simplified_strings)
    assert "((param_2 < param_1) == 0)" in simplified_strings
    assert "(not (param_3 < ((param_2 * 3) + 1)))" in simplified_strings


def test_phi_guard_and_selected_branch_condition_become_contradiction():
    selector = Expression.binary_op("INT_SLESS", _param("param_2"), _param("param_1"))
    selector_is_zero = Expression.binary_op("INT_EQUAL", selector, _const(0))
    selected_branch = Expression.binary_op(
        "INT_SLESS",
        _param("param_3"),
        Expression.binary_op("INT_ADD", Expression.binary_op("INT_MULT", _param("param_2"), _const(3)), _const(1)),
    )
    bool_phi = Expression.phi(
        [
            (
                Condition(selector_is_zero, True),
                Expression.binary_op("INT_SLESS", _param("param_3"), Expression.binary_op("INT_ADD", _param("param_1"), _const(10))),
            ),
            (
                Condition(selector_is_zero, False),
                selected_branch,
            ),
        ]
    )

    conditions = [
        Condition(bool_phi, True),
        Condition(selector_is_zero, False),
        Condition(selected_branch, False),
    ]

    assert ConditionSimplifier.is_contradiction(conditions) is True
