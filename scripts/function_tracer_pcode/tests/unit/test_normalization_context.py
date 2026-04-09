# -*- coding: utf-8 -*-
"""NormalizationContext の回帰テスト"""

import sys
from pathlib import Path


workspace_root = Path(__file__).parent.parent.parent.parent
if str(workspace_root) not in sys.path:
    sys.path.insert(0, str(workspace_root))

from scripts.function_tracer_pcode.model import Expression, ExpressionType
from scripts.function_tracer_pcode.equivalence.normalize.context import (
    NormalizationContext,
)
from scripts.function_tracer_pcode.equivalence.normalize.core import (
    normalize_expression,
)
from scripts.function_tracer_pcode.equivalence.normalize.policy import (
    extract_min_excluded_params,
    extract_upper_bound_facts,
)
from scripts.function_tracer_pcode.equivalence.normalize.facts import (
    extract_sign_facts,
)
from scripts.function_tracer_pcode.model import Condition
from scripts.function_tracer_pcode.equivalence.normalize.division import (
    normalize_division_signs,
)
from scripts.function_tracer_pcode.equivalence.normalize.division_signedness import (
    normalize_division_signedness,
)


def _param(name: str) -> Expression:
    return Expression(ExpressionType.PARAMETER, name=name, size=8)


def _neg(expr: Expression) -> Expression:
    return Expression(
        ExpressionType.UNARY_OP,
        operator="INT_2COMP",
        operands=[expr],
        size=8,
    )


def test_normalization_context_fact_queries():
    context = NormalizationContext(
        min_excluded_params={"param_1"},
        nonneg_vars={"param_2"},
        pos_vars={"param_3"},
        neg_vars={"param_4"},
        nonzero_vars={"param_5"},
        nonneg_exprs={"expr_nonneg"},
        pos_exprs={"expr_pos"},
        neg_exprs={"expr_neg"},
        nonzero_exprs={"expr_nz"},
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
    dummy_expr.to_smt = lambda: "expr_nonneg"
    assert context.is_expr_nonneg(dummy_expr) is True
    dummy_expr.to_smt = lambda: "expr_pos"
    assert context.is_expr_pos(dummy_expr) is True
    dummy_expr.to_smt = lambda: "expr_neg"
    assert context.is_expr_neg(dummy_expr) is True
    dummy_expr.to_smt = lambda: "expr_nz"
    assert context.is_expr_nonzero(dummy_expr) is True


def test_normalize_division_signs_uses_min_exclusion_safely():
    expr = Expression(
        ExpressionType.UNARY_OP,
        operator="INT_2COMP",
        operands=[
            Expression(
                ExpressionType.BINARY_OP,
                operator="INT_SDIV",
                operands=[_neg(_param("param_1")), _param("param_2")],
                size=8,
            )
        ],
        size=8,
    )
    context = NormalizationContext(min_excluded_params={"param_1"})

    normalized = normalize_division_signs(expr, context)

    assert normalized is not expr
    assert normalized.operator == "INT_SDIV"
    assert normalized.operands[0].name == "param_1"
    assert normalized.operands[1].name == "param_2"
    assert [rule.rule_name for rule in context.applied_rules] == ["NEG_DIV_NEG_PARAM"]


def test_normalize_division_signedness_uses_sign_fact_helpers():
    expr = Expression(
        ExpressionType.BINARY_OP,
        operator="INT_DIV",
        operands=[_param("param_1"), _param("param_2")],
        size=8,
    )
    context = NormalizationContext(nonneg_vars={"param_1"}, pos_vars={"param_2"})

    normalized = normalize_division_signedness(expr, context)

    assert normalized is not expr
    assert normalized.operator == "INT_SDIV"
    assert [rule.rule_name for rule in context.applied_rules] == [
        "UDIV_TO_SDIV_NONNEG_POS"
    ]


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

    upper_bounds = extract_upper_bound_facts(lines)

    assert upper_bounds == {
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

    excluded = extract_min_excluded_params(lines)

    assert excluded == {"param_1_1", "tmp_1"}


def test_extract_sign_facts_recovers_nonneg_from_negated_less_condition():
    conditions = [
        Condition(
            Expression(
                ExpressionType.BINARY_OP,
                operator="INT_SLESS",
                operands=[_param("param_1"), Expression.constant(0, size=8)],
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
                operands=[_param("param_2"), Expression.constant(0, size=8)],
                size=1,
            ),
            negated=True,
        )
    ]

    facts = extract_sign_facts(conditions)

    assert facts.is_nonzero("param_2") is True


def test_normalize_expression_removes_shift_mask_when_range_proven():
    expr = Expression(
        ExpressionType.BINARY_OP,
        operator="INT_LEFT",
        operands=[
            Expression.constant(1, size=8),
            Expression(
                ExpressionType.BINARY_OP,
                operator="INT_AND",
                operands=[_param("param_1"), Expression.constant(63, size=8)],
                size=8,
            ),
        ],
        size=8,
    )
    context = NormalizationContext(upper_bounds={"param_1": 64})

    normalized = normalize_expression(expr, context)

    assert normalized.operands[1].expr_type == ExpressionType.PARAMETER
    assert normalized.operands[1].name == "param_1"
    assert [rule.rule_name for rule in context.applied_rules] == [
        "SHIFT_AMOUNT_NORMALIZATION"
    ]


def test_normalize_expression_removes_sign_extension_for_nonnegative_shift_count():
    param32 = Expression(ExpressionType.PARAMETER, name="param_2", size=4)
    extended = Expression.unary_op("INT_SEXT", param32)
    extended.size = 8
    expr = Expression(
        ExpressionType.BINARY_OP,
        operator="INT_LEFT",
        operands=[Expression.constant(1, size=8), extended],
        size=8,
    )
    context = NormalizationContext(upper_bounds={"param_2": 64})

    normalized = normalize_expression(expr, context)

    assert normalized.operands[1].expr_type == ExpressionType.PARAMETER
    assert normalized.operands[1].name == "param_2"
    assert normalized.operands[1].size == 4
    assert [rule.rule_name for rule in context.applied_rules] == [
        "SHIFT_AMOUNT_NORMALIZATION"
    ]


def test_normalize_expression_canonicalizes_sub_and_add_neg_to_same_form():
    lhs = _param("param_1")
    rhs = _param("param_2")
    mid = Expression(
        ExpressionType.BINARY_OP,
        operator="INT_SRIGHT",
        operands=[rhs, Expression.constant(1, size=8)],
        size=8,
    )

    expr_sub = Expression(
        ExpressionType.BINARY_OP,
        operator="INT_SDIV",
        operands=[
            Expression(
                ExpressionType.BINARY_OP,
                operator="INT_SUB",
                operands=[lhs, mid],
                size=8,
            ),
            rhs,
        ],
        size=8,
    )
    expr_add_neg = Expression(
        ExpressionType.BINARY_OP,
        operator="INT_SDIV",
        operands=[
            Expression(
                ExpressionType.BINARY_OP,
                operator="INT_ADD",
                operands=[Expression.unary_op("INT_2COMP", mid), lhs],
                size=8,
            ),
            rhs,
        ],
        size=8,
    )

    normalized_sub = normalize_expression(expr_sub, NormalizationContext())
    normalized_add_neg = normalize_expression(expr_add_neg, NormalizationContext())

    assert normalized_sub.to_smt() == normalized_add_neg.to_smt()
    assert "(bvadd param_1" in normalized_sub.to_smt()
    assert "bvneg" in normalized_sub.to_smt()


def test_normalize_expression_removes_add_zero_identity():
    expr = Expression(
        ExpressionType.BINARY_OP,
        operator="INT_ADD",
        operands=[Expression.constant(0, size=8), _param("param_1")],
        size=8,
    )
    context = NormalizationContext()

    normalized = normalize_expression(expr, context)

    assert normalized.expr_type == ExpressionType.PARAMETER
    assert normalized.name == "param_1"
    assert [rule.rule_name for rule in context.applied_rules] == [
        "ARITHMETIC_CANONICALIZATION"
    ]


def test_normalize_expression_flattens_and_sorts_add_tree():
    expr = Expression(
        ExpressionType.BINARY_OP,
        operator="INT_ADD",
        operands=[
            Expression(
                ExpressionType.BINARY_OP,
                operator="INT_ADD",
                operands=[_param("param_2"), _param("param_1")],
                size=8,
            ),
            Expression.constant(0, size=8),
        ],
        size=8,
    )

    normalized = normalize_expression(expr, NormalizationContext())

    assert normalized.to_smt() == "(bvadd param_1 param_2)"


def test_normalize_expression_canonicalizes_modulo_expansion():
    dividend = _param("param_1")
    divisor = _param("param_2")
    div_expr = Expression(
        ExpressionType.BINARY_OP,
        operator="INT_SDIV",
        operands=[dividend, divisor],
        size=8,
    )
    mult_expr = Expression(
        ExpressionType.BINARY_OP,
        operator="INT_MULT",
        operands=[div_expr, divisor],
        size=8,
    )
    expr = Expression(
        ExpressionType.BINARY_OP,
        operator="INT_SUB",
        operands=[dividend, mult_expr],
        size=8,
    )

    context = NormalizationContext()
    normalized = normalize_expression(expr, context)

    assert normalized.operator == "INT_SREM"
    assert normalized.to_smt() == "(bvsrem param_1 param_2)"
    assert [rule.rule_name for rule in context.applied_rules] == [
        "MODULO_CANONICALIZATION"
    ]


def test_normalize_expression_reduces_abs_bit_hack_when_expr_nonnegative():
    value = Expression(
        ExpressionType.BINARY_OP,
        operator="INT_SREM",
        operands=[_param("param_1"), _param("param_2")],
        size=8,
    )
    shift = Expression(
        ExpressionType.BINARY_OP,
        operator="INT_SRIGHT",
        operands=[value, Expression.constant(63, size=8)],
        size=8,
    )
    expr = Expression(
        ExpressionType.BINARY_OP,
        operator="INT_XOR",
        operands=[
            Expression(
                ExpressionType.BINARY_OP,
                operator="INT_ADD",
                operands=[shift, value],
                size=8,
            ),
            shift,
        ],
        size=8,
    )

    context = NormalizationContext(nonneg_exprs={value.to_smt()})
    normalized = normalize_expression(expr, context)

    assert normalized.to_smt() == value.to_smt()
    assert "BITWISE_ABS_CANONICALIZATION" in [
        rule.rule_name for rule in context.applied_rules
    ]


def test_normalize_expression_reduces_abs_bit_hack_when_expr_negative():
    value = Expression(
        ExpressionType.BINARY_OP,
        operator="INT_SREM",
        operands=[_param("param_1"), _param("param_2")],
        size=8,
    )
    shift = Expression(
        ExpressionType.BINARY_OP,
        operator="INT_SRIGHT",
        operands=[value, Expression.constant(63, size=8)],
        size=8,
    )
    expr = Expression(
        ExpressionType.BINARY_OP,
        operator="INT_XOR",
        operands=[
            shift,
            Expression(
                ExpressionType.BINARY_OP,
                operator="INT_ADD",
                operands=[value, shift],
                size=8,
            ),
        ],
        size=8,
    )

    context = NormalizationContext(neg_exprs={value.to_smt()})
    normalized = normalize_expression(expr, context)

    assert normalized.operator == "INT_2COMP"
    assert normalized.operands[0].to_smt() == value.to_smt()
    assert "BITWISE_ABS_CANONICALIZATION" in [
        rule.rule_name for rule in context.applied_rules
    ]
