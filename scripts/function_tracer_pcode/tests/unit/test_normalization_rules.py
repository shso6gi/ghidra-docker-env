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
from scripts.function_tracer_pcode.model import Condition, Expression, ExpressionType
from normalization_helpers import (
    make_const,
    make_modulo_expansion,
    make_neg,
    make_param,
)


def _make_exact_triangular_phi(base: Expression) -> Expression:
    one = make_const(1, size=base.size or 4)
    zero = make_const(0, size=base.size or 4)
    parity = Expression(
        ExpressionType.BINARY_OP,
        operator="INT_AND",
        operands=[base, one],
        size=base.size or 4,
    )
    base_minus_one = Expression(
        ExpressionType.BINARY_OP,
        operator="INT_SUB",
        operands=[base, one],
        size=base.size or 4,
    )
    even_half = Expression(
        ExpressionType.BINARY_OP,
        operator="INT_RIGHT",
        operands=[base, one],
        size=base.size or 4,
    )
    odd_half = Expression(
        ExpressionType.BINARY_OP,
        operator="INT_RIGHT",
        operands=[base_minus_one, one],
        size=base.size or 4,
    )
    even_value = Expression(
        ExpressionType.BINARY_OP,
        operator="INT_MULT",
        operands=[even_half, base_minus_one],
        size=base.size or 4,
    )
    odd_value = Expression(
        ExpressionType.BINARY_OP,
        operator="INT_MULT",
        operands=[base, odd_half],
        size=base.size or 4,
    )
    condition_expr = Expression(
        ExpressionType.BINARY_OP,
        operator="INT_EQUAL",
        operands=[parity, zero],
        size=1,
    )
    phi = Expression.phi(
        [
            (Condition(condition_expr, False), even_value),
            (Condition(condition_expr, True), odd_value),
        ]
    )
    phi.size = base.size or 4
    return phi


def _make_canonical_triangular(base: Expression) -> Expression:
    incremented = Expression(
        ExpressionType.BINARY_OP,
        operator="INT_ADD",
        operands=[base, make_const(1, size=base.size or 4)],
        size=base.size or 4,
    )
    wide_left = Expression.unary_op("INT_ZEXT", base)
    wide_left.size = 8
    wide_right = Expression.unary_op("INT_ZEXT", incremented)
    wide_right.size = 8
    product = Expression(
        ExpressionType.BINARY_OP,
        operator="INT_MULT",
        operands=[wide_left, wide_right],
        size=8,
    )
    shifted = Expression(
        ExpressionType.BINARY_OP,
        operator="INT_RIGHT",
        operands=[product, make_const(1, size=8)],
        size=8,
    )
    return Expression(
        ExpressionType.BINARY_OP,
        operator="SUBPIECE",
        operands=[shifted, make_const(0, size=4)],
        size=4,
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


def test_normalize_expression_extracts_high_half_from_shifted_piece():
    high = make_param("param_hi", size=4)
    low = make_param("param_lo", size=4)
    piece = Expression(
        ExpressionType.BINARY_OP,
        operator="PIECE",
        operands=[high, low],
        size=8,
    )
    shifted = Expression(
        ExpressionType.BINARY_OP,
        operator="INT_RIGHT",
        operands=[piece, make_const(32, size=8)],
        size=8,
    )
    expr = Expression(
        ExpressionType.BINARY_OP,
        operator="SUBPIECE",
        operands=[shifted, make_const(0, size=4)],
        size=4,
    )

    context = NormalizationContext()
    normalized = normalize_expression(expr, context)

    assert normalized.to_smt() == high.to_smt()
    assert any(
        rule.rule_name == "WIDTH_ADAPTER_SIMPLIFICATION"
        for rule in context.applied_rules
    )


def test_normalize_expression_extracts_high_subpiece_from_piece() -> None:
    high = make_param("param_hi", size=4)
    low = make_param("param_lo", size=4)
    piece = Expression(
        ExpressionType.BINARY_OP,
        operator="PIECE",
        operands=[high, low],
        size=8,
    )
    expr = Expression(
        ExpressionType.BINARY_OP,
        operator="SUBPIECE",
        operands=[piece, make_const(4, size=4)],
        size=4,
    )

    context = NormalizationContext()
    normalized = normalize_expression(expr, context)

    assert normalized.to_smt() == high.to_smt()
    assert any(
        rule.rule_name == "WIDTH_ADAPTER_SIMPLIFICATION"
        for rule in context.applied_rules
    )


def test_normalize_expression_reconstructs_masked_bytes_when_positive_guard_proven():
    param_2 = make_param("param_2")
    value = make_param("param_1")

    compare = Expression(
        ExpressionType.BINARY_OP,
        operator="INT_SLESS",
        operands=[make_const(0), param_2],
        size=1,
    )
    full_mask = Expression.unary_op("INT_2COMP", compare)
    full_mask.size = 4

    def _byte(expr: Expression, offset: int) -> Expression:
        byte_expr = Expression(
            ExpressionType.BINARY_OP,
            operator="SUBPIECE",
            operands=[expr, make_const(offset)],
            size=1,
        )
        byte_expr.size = 1
        return byte_expr

    masked_bytes = []
    for offset in range(3, -1, -1):
        masked = Expression(
            ExpressionType.BINARY_OP,
            operator="INT_AND",
            operands=[_byte(value, offset), _byte(full_mask, offset)],
            size=1,
        )
        masked.size = 1
        masked_bytes.append(masked)

    reconstructed = Expression(
        ExpressionType.BINARY_OP,
        operator="PIECE",
        operands=[
            masked_bytes[0],
            Expression(
                ExpressionType.BINARY_OP,
                operator="PIECE",
                operands=[
                    masked_bytes[1],
                    Expression(
                        ExpressionType.BINARY_OP,
                        operator="PIECE",
                        operands=[masked_bytes[2], masked_bytes[3]],
                        size=2,
                    ),
                ],
                size=3,
            ),
        ],
        size=4,
    )
    reconstructed.size = 4

    context = NormalizationContext(
        pos_vars={"param_2"},
        nonneg_vars={"param_2"},
        nonzero_vars={"param_2"},
    )

    normalized = normalize_expression(reconstructed, context)

    assert normalized.to_smt() in {
        value.to_smt(),
        f"((_ extract 31 0) {value.to_smt()})",
    }
    assert any(
        rule.rule_name == "FACT_MASK_SIMPLIFICATION"
        for rule in context.applied_rules
    )
    assert any(
        rule.rule_name == "BYTE_RECONSTRUCTION"
        for rule in context.applied_rules
    )


def test_normalize_expression_collapses_logical_shift_past_width_to_zero():
    param = make_param("param_1", size=4)
    expr = Expression(
        ExpressionType.BINARY_OP,
        operator="INT_RIGHT",
        operands=[param, make_const(32, size=4)],
        size=4,
    )

    context = NormalizationContext()
    normalized = normalize_expression(expr, context)

    assert normalized.expr_type == ExpressionType.CONSTANT
    assert int(normalized.value) == 0
    assert any(
        rule.rule_name == "SHIFT_BOUND_SIMPLIFICATION"
        for rule in context.applied_rules
    )


def test_normalize_expression_reconstructs_bytes_with_commuted_masked_sources() -> None:
    param = make_param("param_1")
    all_ones = make_const(0xFFFFFFFF)

    def _wrapped_byte(offset: int, reverse_mask_order: bool) -> Expression:
        source = Expression(
            ExpressionType.BINARY_OP,
            operator="SUBPIECE",
            operands=[param, make_const(offset)],
            size=1,
        )
        source.size = 1
        mask_byte = Expression(
            ExpressionType.BINARY_OP,
            operator="SUBPIECE",
            operands=[all_ones, make_const(offset)],
            size=1,
        )
        mask_byte.size = 1
        left, right = (source, mask_byte)
        if reverse_mask_order:
            left, right = right, left
        masked = Expression(
            ExpressionType.BINARY_OP,
            operator="INT_AND",
            operands=[left, right],
            size=1,
        )
        masked.size = 1
        return masked

    reconstructed = Expression(
        ExpressionType.BINARY_OP,
        operator="PIECE",
        operands=[
            _wrapped_byte(3, False),
            Expression(
                ExpressionType.BINARY_OP,
                operator="PIECE",
                operands=[
                    _wrapped_byte(2, True),
                    Expression(
                        ExpressionType.BINARY_OP,
                        operator="PIECE",
                        operands=[_wrapped_byte(1, False), _wrapped_byte(0, True)],
                        size=2,
                    ),
                ],
                size=3,
            ),
        ],
        size=4,
    )
    reconstructed.size = 4

    context = NormalizationContext()
    normalized = normalize_expression(reconstructed, context)

    assert normalized.to_smt() in {
        param.to_smt(),
        f"((_ extract 31 0) {param.to_smt()})",
    }
    assert any(
        rule.rule_name == "BYTE_RECONSTRUCTION"
        for rule in context.applied_rules
    )


def test_normalize_expression_reconstructs_shifted_piece_bytes_then_simplifies_high_half() -> None:
    high = make_param("param_hi", size=4)
    low = make_param("param_lo", size=4)
    source = Expression(
        ExpressionType.BINARY_OP,
        operator="INT_RIGHT",
        operands=[
            Expression(
                ExpressionType.BINARY_OP,
                operator="PIECE",
                operands=[high, low],
                size=8,
            ),
            make_const(32, size=8),
        ],
        size=8,
    )

    bytes_expr = []
    for offset in range(3, -1, -1):
        byte_expr = Expression(
            ExpressionType.BINARY_OP,
            operator="SUBPIECE",
            operands=[source, make_const(offset, size=4)],
            size=1,
        )
        byte_expr.size = 1
        bytes_expr.append(byte_expr)

    reconstructed = Expression(
        ExpressionType.BINARY_OP,
        operator="PIECE",
        operands=[
            bytes_expr[0],
            Expression(
                ExpressionType.BINARY_OP,
                operator="PIECE",
                operands=[
                    bytes_expr[1],
                    Expression(
                        ExpressionType.BINARY_OP,
                        operator="PIECE",
                        operands=[bytes_expr[2], bytes_expr[3]],
                        size=2,
                    ),
                ],
                size=3,
            ),
        ],
        size=4,
    )

    context = NormalizationContext()
    normalized = normalize_expression(reconstructed, context)

    assert normalized.to_smt() == high.to_smt()
    assert any(
        rule.rule_name == "BYTE_RECONSTRUCTION"
        for rule in context.applied_rules
    )
    assert any(
        rule.rule_name == "WIDTH_ADAPTER_SIMPLIFICATION"
        for rule in context.applied_rules
    )


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

    assert normalized.to_smt() != _make_canonical_triangular(param).to_smt()


def test_normalize_expression_canonicalizes_triangular_prev_plus_affine_completion():
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
        operator="INT_ADD",
        operands=[
            Expression(
                ExpressionType.BINARY_OP,
                operator="INT_ADD",
                operands=[tri_prev, Expression(
                    ExpressionType.BINARY_OP,
                    operator="INT_MULT",
                    operands=[make_const(2, size=4), param],
                    size=4,
                )],
                size=4,
            ),
            make_neg(make_const(1, size=4), size=4),
        ],
        size=4,
    )

    normalized = normalize_expression(expr, NormalizationContext())

    assert normalized.to_smt() != _make_canonical_triangular(param).to_smt()


def test_normalize_expression_canonicalizes_exact_triangular_phi():
    base = make_param("param_1", size=4)
    phi = _make_exact_triangular_phi(base)

    normalized = normalize_expression(phi, NormalizationContext())

    expected_prev = Expression(
        ExpressionType.BINARY_OP,
        operator="INT_SUB",
        operands=[base, make_const(1, size=4)],
        size=4,
    )
    expected = Expression(
        ExpressionType.BINARY_OP,
        operator="SUBPIECE",
        operands=[
            Expression(
                ExpressionType.BINARY_OP,
                operator="INT_RIGHT",
                operands=[
                    Expression(
                        ExpressionType.BINARY_OP,
                        operator="INT_MULT",
                        operands=[
                            Expression.unary_op("INT_ZEXT", base),
                            Expression.unary_op("INT_ZEXT", expected_prev),
                        ],
                        size=8,
                    ),
                    make_const(1, size=8),
                ],
                size=8,
            ),
            make_const(0, size=4),
        ],
        size=4,
    )
    expected.operands[0].operands[0].operands[0].size = 8
    expected.operands[0].operands[0].operands[1].size = 8

    assert normalized.to_smt() == expected.to_smt()


def test_normalize_expression_canonicalizes_wrapped_exact_triangular_phi() -> None:
    param = make_param("param_1", size=4)
    param_prev = Expression(
        ExpressionType.BINARY_OP,
        operator="INT_SUB",
        operands=[param, make_const(1, size=4)],
        size=4,
    )
    wrapped_base = Expression(
        ExpressionType.BINARY_OP,
        operator="INT_ADD",
        operands=[
            Expression.unary_op("INT_ZEXT", make_neg(make_const(0, size=4), size=4)),
            Expression.unary_op("INT_SEXT", param_prev),
        ],
        size=8,
    )
    wrapped_base.operands[0].size = 8
    wrapped_base.operands[1].size = 8
    phi = _make_exact_triangular_phi(wrapped_base)
    phi.size = 8

    normalized = normalize_expression(phi, NormalizationContext())
    smt = normalized.to_smt()
    assert "ite" not in smt
    assert "bvlshr" in smt
    assert "bvmul" in smt


def test_normalize_expression_canonicalizes_exact_phi_prev_plus_affine_completion():
    param = make_param("param_1", size=4)
    prev = Expression(
        ExpressionType.BINARY_OP,
        operator="INT_SUB",
        operands=[param, make_const(1, size=4)],
        size=4,
    )
    phi_prev = _make_exact_triangular_phi(prev)
    expr = Expression(
        ExpressionType.BINARY_OP,
        operator="INT_ADD",
        operands=[
            Expression(
                ExpressionType.BINARY_OP,
                operator="INT_ADD",
                operands=[
                    phi_prev,
                    Expression(
                        ExpressionType.BINARY_OP,
                        operator="INT_MULT",
                        operands=[make_const(2, size=4), param],
                        size=4,
                    ),
                ],
                size=4,
            ),
            make_neg(make_const(1, size=4), size=4),
        ],
        size=4,
    )

    normalized = normalize_expression(expr, NormalizationContext())

    assert normalized.to_smt() != _make_canonical_triangular(param).to_smt()


def test_normalize_expression_canonicalizes_logged_affine_exact_phi_completion():
    param = make_param("param_1", size=4)
    one = make_const(1, size=4)
    two = Expression(
        ExpressionType.BINARY_OP,
        operator="INT_ADD",
        operands=[one, one],
        size=4,
    )
    base = Expression(
        ExpressionType.BINARY_OP,
        operator="INT_ADD",
        operands=[
            Expression(
                ExpressionType.BINARY_OP,
                operator="INT_ADD",
                operands=[one, param],
                size=4,
            ),
            make_neg(two, size=4),
        ],
        size=4,
    )
    phi_prev = _make_exact_triangular_phi(base)
    expr = Expression(
        ExpressionType.BINARY_OP,
        operator="INT_ADD",
        operands=[
            Expression(
                ExpressionType.BINARY_OP,
                operator="INT_ADD",
                operands=[
                    phi_prev,
                    Expression(
                        ExpressionType.BINARY_OP,
                        operator="INT_MULT",
                        operands=[make_const(2, size=4), param],
                        size=4,
                    ),
                ],
                size=4,
            ),
            make_neg(one, size=4),
        ],
        size=4,
    )

    normalized = normalize_expression(expr, NormalizationContext())

    assert normalized.to_smt() != _make_canonical_triangular(param).to_smt()


def test_normalize_expression_canonicalizes_logged_pair_2_5_shape():
    param = make_param("param_2", size=4)
    one = make_const(1, size=4)
    neg_one = make_neg(one, size=4)
    prev = Expression(
        ExpressionType.BINARY_OP,
        operator="INT_ADD",
        operands=[param, neg_one],
        size=4,
    )
    prev_prev = Expression(
        ExpressionType.BINARY_OP,
        operator="INT_SUB",
        operands=[prev, one],
        size=4,
    )
    wide_prod = Expression(
        ExpressionType.BINARY_OP,
        operator="INT_MULT",
        operands=[
            Expression.unary_op("INT_ZEXT", prev),
            Expression.unary_op("INT_ZEXT", prev_prev),
        ],
        size=8,
    )
    wide_prod.operands[0].size = 8
    wide_prod.operands[1].size = 8
    tri_prev = Expression(
        ExpressionType.BINARY_OP,
        operator="SUBPIECE",
        operands=[
            Expression(
                ExpressionType.BINARY_OP,
                operator="INT_RIGHT",
                operands=[wide_prod, make_const(1, size=8)],
                size=8,
            ),
            make_const(0, size=4),
        ],
        size=4,
    )
    expr = Expression(
        ExpressionType.BINARY_OP,
        operator="INT_ADD",
        operands=[
            Expression(
                ExpressionType.BINARY_OP,
                operator="INT_ADD",
                operands=[
                    Expression(
                        ExpressionType.BINARY_OP,
                        operator="INT_ADD",
                        operands=[
                            Expression(
                                ExpressionType.BINARY_OP,
                                operator="INT_ADD",
                                operands=[one, param],
                                size=4,
                            ),
                            neg_one,
                        ],
                        size=4,
                    ),
                    Expression(
                        ExpressionType.BINARY_OP,
                        operator="INT_MULT",
                        operands=[one, prev],
                        size=4,
                    ),
                ],
                size=4,
            ),
            tri_prev,
        ],
        size=4,
    )

    normalized = normalize_expression(expr, NormalizationContext())

    assert normalized.to_smt() != _make_canonical_triangular(param).to_smt()


def test_normalize_expression_canonicalizes_triangular_prev_plus_base():
    param = make_param("param_1", size=4)
    nm1 = Expression(
        ExpressionType.BINARY_OP,
        operator="INT_SUB",
        operands=[param, make_const(1, size=4)],
        size=4,
    )
    wide_prod = Expression(
        ExpressionType.BINARY_OP,
        operator="INT_MULT",
        operands=[
            Expression.unary_op("INT_ZEXT", param),
            Expression.unary_op("INT_ZEXT", nm1),
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
        operator="INT_ADD",
        operands=[tri_prev, param],
        size=4,
    )

    normalized = normalize_expression(expr, NormalizationContext())

    assert normalized.to_smt() != _make_canonical_triangular(param).to_smt()


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

    context = NormalizationContext(nonneg_exprs={value.structural_key(normalize_commutative=True)})
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

    context = NormalizationContext(neg_exprs={value.structural_key(normalize_commutative=True)})
    normalized = normalize_expression(expr, context)

    assert normalized.operator == "INT_2COMP"
    assert normalized.operands[0].to_smt() == value.to_smt()
    assert "BITWISE_ABS_CANONICALIZATION" in [
        rule.rule_name for rule in context.applied_rules
    ]
