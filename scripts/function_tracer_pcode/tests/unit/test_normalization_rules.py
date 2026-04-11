# -*- coding: utf-8 -*-
"""Normalization rule regression tests."""

import sys
from pathlib import Path


workspace_root = Path(__file__).parent.parent.parent.parent
if str(workspace_root) not in sys.path:
    sys.path.insert(0, str(workspace_root))

from scripts.function_tracer_pcode.equivalence.normalize.context import (
    NormalizationContext,
)
from scripts.function_tracer_pcode.equivalence.normalize.core import (
    normalize_expression,
)
from scripts.function_tracer_pcode.equivalence.normalize.division import (
    normalize_division_signs,
)
from scripts.function_tracer_pcode.equivalence.normalize.division_signedness import (
    normalize_division_signedness,
)
from scripts.function_tracer_pcode.model import Expression, ExpressionType
from normalization_helpers import (
    make_const,
    make_modulo_expansion,
    make_neg,
    make_param,
)


def test_normalize_division_signs_uses_min_exclusion_safely():
    expr = Expression(
        ExpressionType.UNARY_OP,
        operator="INT_2COMP",
        operands=[
            Expression(
                ExpressionType.BINARY_OP,
                operator="INT_SDIV",
                operands=[make_neg(make_param("param_1")), make_param("param_2")],
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
        operands=[make_param("param_1"), make_param("param_2")],
        size=8,
    )
    context = NormalizationContext(nonneg_vars={"param_1"}, pos_vars={"param_2"})

    normalized = normalize_division_signedness(expr, context)

    assert normalized is not expr
    assert normalized.operator == "INT_SDIV"
    assert [rule.rule_name for rule in context.applied_rules] == [
        "UDIV_TO_SDIV_NONNEG_POS"
    ]


def test_normalize_expression_removes_shift_mask_when_range_proven():
    expr = Expression(
        ExpressionType.BINARY_OP,
        operator="INT_LEFT",
        operands=[
            make_const(1),
            Expression(
                ExpressionType.BINARY_OP,
                operator="INT_AND",
                operands=[make_param("param_1"), make_const(63)],
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
    param32 = make_param("param_2", size=4)
    extended = Expression.unary_op("INT_SEXT", param32)
    extended.size = 8
    expr = Expression(
        ExpressionType.BINARY_OP,
        operator="INT_LEFT",
        operands=[make_const(1), extended],
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
    lhs = make_param("param_1")
    rhs = make_param("param_2")
    mid = Expression(
        ExpressionType.BINARY_OP,
        operator="INT_SRIGHT",
        operands=[rhs, make_const(1)],
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
        operands=[make_const(0), make_param("param_1")],
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
                operands=[make_param("param_2"), make_param("param_1")],
                size=8,
            ),
            make_const(0),
        ],
        size=8,
    )

    normalized = normalize_expression(expr, NormalizationContext())
    assert normalized.to_smt() == "(bvadd param_1 param_2)"


def test_normalize_expression_simplifies_width_adapters():
    param32 = make_param("param_1", size=4)
    widened = Expression.unary_op("INT_ZEXT", param32)
    widened.size = 8
    expr = Expression.binary_op("SUBPIECE", widened, make_const(0))
    expr.size = 4

    normalized = normalize_expression(expr, NormalizationContext())

    assert normalized.expr_type == ExpressionType.PARAMETER
    assert normalized.name == "param_1"
    assert normalized.size == 4


def test_normalize_expression_folds_extended_constants_and_mul_identities():
    param32 = make_param("param_1", size=4)
    one32 = make_const(1, size=4)
    zero32 = make_const(0, size=4)
    wide_one = Expression.unary_op("INT_ZEXT", one32)
    wide_one.size = 8
    wide_zero = Expression.unary_op("INT_ZEXT", zero32)
    wide_zero.size = 8
    wide_param = Expression.unary_op("INT_ZEXT", param32)
    wide_param.size = 8

    expr = Expression(
        ExpressionType.BINARY_OP,
        operator="INT_ADD",
        operands=[
            Expression(
                ExpressionType.BINARY_OP,
                operator="INT_MULT",
                operands=[wide_one, wide_param],
                size=8,
            ),
            Expression(
                ExpressionType.BINARY_OP,
                operator="INT_MULT",
                operands=[wide_zero, wide_param],
                size=8,
            ),
        ],
        size=8,
    )

    normalized = normalize_expression(expr, NormalizationContext())

    assert normalized.expr_type == ExpressionType.UNARY_OP
    assert normalized.operator == "INT_ZEXT"
    assert normalized.operands[0].name == "param_1"
    assert normalized.size == 8


def test_normalize_expression_simplifies_trivial_shifts():
    expr = Expression(
        ExpressionType.BINARY_OP,
        operator="INT_RIGHT",
        operands=[make_const(0, size=8), make_param("param_1", size=8)],
        size=8,
    )
    normalized = normalize_expression(expr, NormalizationContext())
    assert normalized.expr_type == ExpressionType.CONSTANT
    assert normalized.value == 0


def test_normalize_expression_canonicalizes_arithmetic_series_closed_form():
    param = make_param("param_1", size=4)
    nm1 = Expression(
        ExpressionType.BINARY_OP,
        operator="INT_SUB",
        operands=[param, make_const(1, size=4)],
        size=4,
    )
    nm2 = Expression(
        ExpressionType.BINARY_OP,
        operator="INT_SUB",
        operands=[param, make_const(2, size=4)],
        size=4,
    )
    square = Expression(
        ExpressionType.BINARY_OP,
        operator="INT_MULT",
        operands=[nm1, nm1],
        size=4,
    )
    wide_prod = Expression(
        ExpressionType.BINARY_OP,
        operator="INT_MULT",
        operands=[
            Expression.unary_op("INT_ZEXT", nm1),
            Expression.unary_op("INT_ZEXT", nm2),
        ],
        size=8,
    )
    wide_prod.operands[0].size = 8
    wide_prod.operands[1].size = 8
    tri_prev = Expression(
        ExpressionType.BINARY_OP,
        operator="INT_AND",
        operands=[
            Expression(
                ExpressionType.BINARY_OP,
                operator="INT_RIGHT",
                operands=[wide_prod, make_const(1, size=8)],
                size=8,
            ),
            make_const(0xFFFFFFFF, size=8),
        ],
        size=8,
    )
    expr = Expression(
        ExpressionType.BINARY_OP,
        operator="INT_SUB",
        operands=[
            Expression(
                ExpressionType.BINARY_OP,
                operator="INT_ADD",
                operands=[square, param],
                size=4,
            ),
            tri_prev,
        ],
        size=4,
    )

    normalized = normalize_expression(expr, NormalizationContext())

    assert normalized.to_smt() == "((_ extract 31 0) (bvlshr (bvmul ((_ zero_extend 32) param_1) (bvadd ((_ zero_extend 32) param_1) (_ bv1 64))) (_ bv1 64)))"


def test_normalize_expression_canonicalizes_modulo_expansion():
    dividend, divisor, modulo_expansion = make_modulo_expansion()
    expr = modulo_expansion

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
        operands=[make_param("param_1"), make_param("param_2")],
        size=8,
    )
    shift = Expression(
        ExpressionType.BINARY_OP,
        operator="INT_SRIGHT",
        operands=[value, make_const(63)],
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
        operands=[make_param("param_1"), make_param("param_2")],
        size=8,
    )
    shift = Expression(
        ExpressionType.BINARY_OP,
        operator="INT_SRIGHT",
        operands=[value, make_const(63)],
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
