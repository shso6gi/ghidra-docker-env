# -*- coding: utf-8 -*-
"""Normalization context / fact extraction regression tests."""

import sys
from pathlib import Path


workspace_root = Path(__file__).parent.parent.parent.parent
if str(workspace_root) not in sys.path:
    sys.path.insert(0, str(workspace_root))

from scripts.function_tracer_pcode.semantics.normalize.context import NormalizationContext
from scripts.function_tracer_pcode.semantics.normalize.facts import extract_sign_facts
from scripts.function_tracer_pcode.semantics.normalize.policy import (
    extract_min_excluded_params,
    extract_upper_bound_facts,
)
from scripts.function_tracer_pcode.core import Condition, Expression, ExpressionType
from normalization_helpers import make_const, make_param


def test_normalization_context_fact_queries():
    context = NormalizationContext(
        min_excluded_params={"param_1"},
        nonneg_vars={"param_2"},
        pos_vars={"param_3"},
        neg_vars={"param_4"},
        nonzero_vars={"param_5"},
        nonneg_exprs={Expression(ExpressionType.VARIABLE, name="x", size=8).structural_key()},
        pos_exprs={Expression(ExpressionType.VARIABLE, name="y", size=8).structural_key()},
        neg_exprs={Expression(ExpressionType.VARIABLE, name="z", size=8).structural_key()},
        nonzero_exprs={Expression(ExpressionType.VARIABLE, name="w", size=8).structural_key()},
    )

    assert context.is_min_excluded("param_1") is True
    assert context.is_min_excluded("param_x") is False
    assert context.is_nonneg("param_2") is True
    assert context.is_nonneg("param_3") is True
    assert context.is_nonneg("param_4") is False
    assert context.is_pos("param_3") is True
    assert context.is_pos("param_2") is False
    assert context.is_neg("param_4") is True
    assert context.is_neg("param_3") is False
    assert context.is_nonzero("param_3") is True
    assert context.is_nonzero("param_4") is True
    assert context.is_nonzero("param_5") is True
    assert context.is_nonzero("param_2") is False

    dummy_expr = Expression(ExpressionType.VARIABLE, name="x", size=8)
    assert context.is_expr_nonneg(dummy_expr) is True
    dummy_expr = Expression(ExpressionType.VARIABLE, name="y", size=8)
    assert context.is_expr_pos(dummy_expr) is True
    dummy_expr = Expression(ExpressionType.VARIABLE, name="z", size=8)
    assert context.is_expr_neg(dummy_expr) is True
    dummy_expr = Expression(ExpressionType.VARIABLE, name="w", size=8)
    assert context.is_expr_nonzero(dummy_expr) is True


def test_normalization_context_upper_bound_queries():
    context = NormalizationContext(upper_bounds={"param_1": 64, "param_2": 8})

    assert context.get_upper_bound("param_1") == 64
    assert context.get_upper_bound("param_x") is None
    assert context.has_upper_bound_le("param_1", 64) is True
    assert context.has_upper_bound_le("param_1", 63) is False
    assert context.has_upper_bound_le("param_x", 64) is False


def test_extract_upper_bound_facts_parses_shift_ub_constraints():
    lines = [
        "(assert (bvult param_2_1 (_ bv64 64)))",
        "(assert (bvult ((_ sign_extend 32) param_2_2) (_ bv64 64)))",
        "(assert (bvult ((_ zero_extend 32) param_2_3) (_ bv8 64)))",
    ]

    assert extract_upper_bound_facts(lines) == {
        "param_2_1": 64,
        "param_2_2": 64,
        "param_2_3": 8,
    }


def test_extract_min_excluded_params_parses_32bit_and_64bit_constraints():
    lines = [
        "(assert (not (= param_1_1 (_ bv9223372036854775808 64))))",
        "(assert (distinct tmp_1 (_ bv2147483648 32)))",
        "(assert (not (= ignored (_ bv7 4))))",
    ]

    assert extract_min_excluded_params(lines) == {"param_1_1", "tmp_1"}


def test_extract_sign_facts_recovers_nonneg_from_negated_less_condition():
    conditions = [
        Condition(
            Expression(
                ExpressionType.BINARY_OP,
                operator="INT_SLESS",
                operands=[make_param("param_1"), make_const(0)],
                size=1,
            ),
            negated=True,
        )
    ]

    facts = extract_sign_facts(conditions)
    assert facts.is_nonneg("param_1") is True


def test_extract_sign_facts_recovers_nonzero_from_negated_equality():
    conditions = [
        Condition(
            Expression(
                ExpressionType.BINARY_OP,
                operator="INT_EQUAL",
                operands=[make_param("param_2"), make_const(0)],
                size=1,
            ),
            negated=True,
        )
    ]

    facts = extract_sign_facts(conditions)
    assert facts.is_nonzero("param_2") is True
