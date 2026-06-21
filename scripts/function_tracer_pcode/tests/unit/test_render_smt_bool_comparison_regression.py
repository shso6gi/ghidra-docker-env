# -*- coding: utf-8 -*-

from typing import Optional

from conftest import resolve_mock_data_type
from scripts.function_tracer_pcode.model import Condition, Expression
from scripts.function_tracer_pcode.equivalence.formula.returns import coerce_return_value_to_bitvec
from scripts.function_tracer_pcode.model.render_smt import (
    collect_float_predicate_smt_declarations,
    expression_contains_unsupported_smt_ops,
    expression_uses_smt_uf,
    expression_smt_sort_kind,
    expression_to_smt,
    smt_logic_name,
)


def _param(name: str, size: int = 4, data_type: Optional[str] = None) -> Expression:
    return Expression.parameter(
        name,
        size=size,
        data_type=data_type,
        data_type_obj=resolve_mock_data_type(data_type) if data_type else None,
    )


def _const(value: int, size: int = 4) -> Expression:
    return Expression.constant(value, size=size)


def _binary(op: str, left: Expression, right: Expression) -> Expression:
    return Expression.binary_op(op, left, right)


def test_expression_to_smt_coerces_bool_vs_bitvector_equality_without_sort_error():
    bool_expr = _binary("INT_SLESS", _param("param_2"), _param("param_1"))
    expr = _binary("INT_EQUAL", bool_expr, _const(0, 4))

    smt = expression_to_smt(expr)

    assert "((_ zero_extend 31) (bvslt" not in smt
    assert "(ite (bvslt param_2 param_1) (_ bv1 32) (_ bv0 32))" in smt
    assert smt == "(= (ite (bvslt param_2 param_1) (_ bv1 32) (_ bv0 32)) (_ bv0 32))"


def test_float_binary_arithmetic_is_supported_by_smt_gate():
    expr = _binary(
        "FLOAT_ADD",
        _binary("FLOAT_MULT", _param("param_1", size=8), _param("param_1", size=8)),
        _binary("FLOAT_SUB", _param("param_2", size=8), _param("param_3", size=8)),
    )

    assert expression_contains_unsupported_smt_ops(expr) is False
    smt = expression_to_smt(expr, float_mode="fp")
    assert "(fp.add RNE" in smt
    assert "(fp.mul RNE" in smt
    assert "(fp.sub RNE" in smt


def test_float_binary_arithmetic_declares_uninterpreted_function_for_non_fp_width():
    expr = _binary("FLOAT_MULT", _param("param_2", size=10), _param("param_1", size=10))

    smt = expression_to_smt(expr, float_mode="fp")
    declarations = collect_float_predicate_smt_declarations(expr, float_mode="fp")

    assert smt == "(float_mult param_2 param_1)"
    assert declarations == [
        "(declare-fun float_mult ((_ BitVec 80) (_ BitVec 80)) (_ BitVec 80))",
    ]


def test_float_predicate_smt_declarations_are_collected_for_ufbv_queries():
    expr = _binary("FLOAT_LESS", _param("param_2", size=8), _param("param_1", size=8))

    smt = expression_to_smt(expr)
    declarations = collect_float_predicate_smt_declarations(expr)

    assert smt == "(float_less param_2 param_1)"
    assert declarations == [
        "(declare-fun float_less ((_ BitVec 64) (_ BitVec 64)) Bool)",
    ]


def test_float_predicate_can_render_with_ieee754_fp_theory():
    expr = _binary("FLOAT_LESS", _param("param_2", size=8), _param("param_1", size=8))

    smt = expression_to_smt(expr, float_mode="fp")
    declarations = collect_float_predicate_smt_declarations(expr, float_mode="fp")

    assert smt == "(fp.lt ((_ to_fp 11 53) param_2) ((_ to_fp 11 53) param_1))"
    assert declarations == []


def test_float_mixed_width_binary_skips_fp_arithmetic_path():
    expr = _binary("FLOAT_ADD", _param("param_2", size=10), _param("param_1", size=8))

    smt = expression_to_smt(expr, float_mode="fp")
    declarations = collect_float_predicate_smt_declarations(expr, float_mode="fp")

    assert smt == "(float_add param_2 param_1)"
    assert declarations == [
        "(declare-fun float_add ((_ BitVec 80) (_ BitVec 64)) (_ BitVec 80))",
    ]


def test_float_signed_division_uses_fp_theory_for_non_exceptional_widths():
    expr = _binary("FLOAT_SDIV", _param("param_2", size=8), _param("param_1", size=8))

    smt = expression_to_smt(expr, float_mode="fp")
    declarations = collect_float_predicate_smt_declarations(expr, float_mode="fp")

    assert smt == "(fp.div RNE ((_ to_fp 11 53) param_2) ((_ to_fp 11 53) param_1))"
    assert declarations == []


def test_float_signed_division_known_zero_divisor_falls_back_to_ufbv():
    expr = _binary("FLOAT_SDIV", _param("param_2", size=8), _const(0, size=8))

    smt = expression_to_smt(expr, float_mode="fp")
    declarations = collect_float_predicate_smt_declarations(expr, float_mode="fp")

    assert smt == "(float_div param_2 (_ bv0 64))"
    assert declarations == [
        "(declare-fun float_div ((_ BitVec 64) (_ BitVec 64)) (_ BitVec 64))",
    ]
    assert expression_uses_smt_uf(expr, float_mode="fp") is True


def test_float_signed_remainder_known_nan_operand_falls_back_to_ufbv():
    expr = _binary("FLOAT_SREM", _const(0x7FF8000000000000, size=8), _param("param_1", size=8))

    smt = expression_to_smt(expr, float_mode="fp")
    declarations = collect_float_predicate_smt_declarations(expr, float_mode="fp")

    assert smt == "(float_rem (_ bv9221120237041090560 64) param_1)"
    assert declarations == [
        "(declare-fun float_rem ((_ BitVec 64) (_ BitVec 64)) (_ BitVec 64))",
    ]


def test_unsupported_float_width_keeps_uf_logic_visible():
    expr = _binary("FLOAT_LESS", _param("param_2", size=10), _param("param_1", size=10))

    smt = expression_to_smt(expr, float_mode="fp")
    declarations = collect_float_predicate_smt_declarations(expr, float_mode="fp")

    assert smt == "(float_less param_2 param_1)"
    assert declarations == [
        "(declare-fun float_less ((_ BitVec 80) (_ BitVec 80)) Bool)",
    ]
    assert expression_uses_smt_uf(expr, float_mode="fp") is True
    assert smt_logic_name(uses_uf=True) == "QF_UFBV"
    assert smt_logic_name(uses_float_theory=True, uses_uf=True) == "QF_UFFPBV"


def test_float_notequal_uses_ieee754_not_fp_eq_in_fp_mode():
    expr = _binary("FLOAT_NOTEQUAL", _param("param_2", size=8), _param("param_1", size=8))

    smt = expression_to_smt(expr, float_mode="fp")

    assert smt == "(not (fp.eq ((_ to_fp 11 53) param_2) ((_ to_fp 11 53) param_1)))"


def test_float_neg_lowers_to_bit_preserving_sign_flip():
    expr = Expression.unary_op("FLOAT_NEG", _param("param_1", size=8, data_type="double"))
    expr.size = 8

    smt = expression_to_smt(expr, float_mode="fp")

    assert smt == "(bvxor param_1 (_ bv9223372036854775808 64))"
    assert "float_neg" not in smt


def test_float_abs_lowers_to_bit_preserving_sign_clear():
    expr = Expression.unary_op("FLOAT_ABS", _param("param_1", size=4, data_type="float"))
    expr.size = 4

    smt = expression_to_smt(expr, float_mode="fp")

    assert smt == "(bvand param_1 (_ bv2147483647 32))"
    assert "float_abs" not in smt


def test_float_unary_ops_are_supported_by_smt_gate():
    neg_expr = Expression.unary_op("FLOAT_NEG", _param("param_1", size=8, data_type="double"))
    neg_expr.size = 8
    abs_expr = Expression.unary_op("FLOAT_ABS", _param("param_2", size=4, data_type="float"))
    abs_expr.size = 4
    nan_expr = Expression.unary_op("FLOAT_NAN", _param("param_3", size=8, data_type="double"))
    nan_expr.size = 1

    assert expression_contains_unsupported_smt_ops(neg_expr) is False
    assert expression_contains_unsupported_smt_ops(abs_expr) is False
    assert expression_contains_unsupported_smt_ops(nan_expr) is False


def test_float_nan_uses_ieee754_fp_theory_in_fp_mode():
    expr = Expression.unary_op("FLOAT_NAN", _param("param_1", size=8, data_type="double"))
    expr.size = 1

    smt = expression_to_smt(expr, float_mode="fp")
    declarations = collect_float_predicate_smt_declarations(expr, float_mode="fp")

    assert smt == "(fp.isNaN ((_ to_fp 11 53) param_1))"
    assert declarations == []


def test_float_nan_uses_declared_uf_for_ufbv_queries():
    expr = Expression.unary_op("FLOAT_NAN", _param("param_1", size=10))
    expr.size = 1

    smt = expression_to_smt(expr, float_mode="fp")
    declarations = collect_float_predicate_smt_declarations(expr, float_mode="fp")

    assert smt == "(float_nan param_1)"
    assert declarations == [
        "(declare-fun float_nan ((_ BitVec 80)) Bool)",
    ]
    assert expression_uses_smt_uf(expr, float_mode="fp") is True


def test_expression_to_smt_coerces_bool_before_integer_twos_complement():
    bool_expr = _binary("INT_EQUAL", _binary("INT_AND", _param("param_1", size=1), _const(1, size=1)), _const(0, size=1))
    expr = Expression.unary_op("INT_2COMP", bool_expr)

    smt = expression_to_smt(expr)

    assert "(bvneg (=" not in smt
    assert smt == (
        "(bvneg (ite (= (bvand param_1 (_ bv1 8)) (_ bv0 8)) "
        "(_ bv1 8) (_ bv0 8)))"
    )


def test_expression_to_smt_coerces_bitvector_before_bool_negate():
    low_byte = _binary("SUBPIECE", _param("param_1", size=4), _const(0, size=4))
    low_byte.size = 1
    expr = Expression.unary_op("BOOL_NEGATE", low_byte)

    smt = expression_to_smt(expr)

    assert smt == "(not (not (= ((_ extract 7 0) param_1) (_ bv0 8))))"


def test_condition_to_smt_coerces_bitvector_conditions_to_bool():
    low_byte = _binary("SUBPIECE", _param("param_1", size=4), _const(0, size=4))
    low_byte.size = 1

    assert Condition(low_byte).to_smt() == "(not (= ((_ extract 7 0) param_1) (_ bv0 8)))"
    assert Condition(low_byte, True).to_smt() == (
        "(not (not (= ((_ extract 7 0) param_1) (_ bv0 8))))"
    )


def test_expression_to_smt_respects_explicit_shift_width_inside_piece():
    shifted = _binary("INT_RIGHT", _const(0x100e68, size=8), _const(56, size=4))
    shifted.size = 1
    piece = _binary("PIECE", shifted, _const(0x12, size=1))
    piece.size = 2

    smt = expression_to_smt(piece)

    assert smt == (
        "(concat ((_ extract 7 0) "
        "(bvlshr (_ bv1052264 64) ((_ zero_extend 32) (_ bv56 32)))) (_ bv18 8))"
    )


def test_expression_to_smt_handles_bool_phi_compared_against_zero():
    selector = _binary("INT_SLESS", _param("param_2"), _param("param_1"))
    selector_is_zero = _binary("INT_EQUAL", selector, _const(0, 4))
    neg_selector_is_zero = Condition(selector_is_zero, True)
    selector_is_zero_cond = Condition(selector_is_zero, False)

    bool_phi = Expression.phi(
        [
            (
                neg_selector_is_zero,
                _binary(
                    "INT_SLESS",
                    _param("param_3"),
                    _binary("INT_ADD", _param("param_1"), _const(10, 8)),
                ),
            ),
            (
                selector_is_zero_cond,
                _binary(
                    "INT_SLESS",
                    _param("param_3"),
                    _binary(
                        "INT_ADD",
                        _binary("INT_MULT", _param("param_2"), _const(3, 8)),
                        _const(1, 8),
                    ),
                ),
            ),
        ]
    )

    smt = expression_to_smt(bool_phi)

    assert smt.startswith("(ite ")
    assert "((_ zero_extend 31) (bvslt" not in smt
    assert "(= (ite (bvslt param_2 param_1) (_ bv1 32) (_ bv0 32)) (_ bv0 32))" in smt


def test_expression_to_smt_collapses_unconditional_phi_branch():
    expr = Expression.phi(
        [
            (None, _const(0, 4)),
            (
                Condition(_binary("INT_EQUAL", _param("param_1"), _const(0, 4))),
                _binary("INT_AND", _param("param_1"), _const(0xFFFFFFF8, 4)),
            ),
        ]
    )
    expr.size = 4

    smt = expression_to_smt(expr)

    assert smt == "(_ bv0 32)"


def test_expression_to_smt_sign_extends_narrow_operand_for_signed_width_mismatch_compare():
    expr = _binary(
        "INT_SLESS",
        _param("param_3", size=4, data_type="int"),
        _binary("INT_ADD", _param("param_1", size=4, data_type="int"), _const(10, size=8)),
    )

    smt = expression_to_smt(expr)

    assert "((_ sign_extend 32) param_3)" not in smt
    assert "(bvadd param_1 (_ bv10 32))" in smt
    assert "((_ sign_extend 32) param_1)" not in smt
    assert smt == "(bvslt param_3 (bvadd param_1 (_ bv10 32)))"


def test_expression_to_smt_sign_extends_signed_operands_inside_nested_signed_compare_arithmetic():
    selector = _binary(
        "INT_SLESS",
        _param("param_2", size=4, data_type="int"),
        _param("param_1", size=4, data_type="int"),
    )
    selector_is_zero = _binary("INT_EQUAL", selector, _const(0, 4))
    expr = Expression.phi(
        [
            (
                Condition(selector_is_zero, True),
                _binary(
                    "INT_SLESS",
                    _param("param_3", size=4, data_type="int"),
                    _binary("INT_ADD", _param("param_1", size=4, data_type="int"), _const(10, size=8)),
                ),
            ),
            (
                Condition(selector_is_zero, False),
                _binary(
                    "INT_SLESS",
                    _param("param_3", size=4, data_type="int"),
                    _binary(
                        "INT_ADD",
                        _binary("INT_MULT", _param("param_2", size=4, data_type="int"), _const(3, size=8)),
                        _const(1, size=8),
                    ),
                ),
            ),
        ]
    )

    smt = expression_to_smt(expr)

    assert "(bvadd param_1 (_ bv10 32))" in smt
    assert "(bvmul param_2 (_ bv3 32))" in smt
    assert "((_ zero_extend 32) param_2)" not in smt


def test_expression_to_smt_preserves_32bit_wrap_before_signed_compare_extension():
    expr = _binary(
        "INT_SLESS",
        _param("param_3", size=4, data_type="int"),
        _binary(
            "INT_ADD",
            _const(1, size=8),
            _binary("INT_MULT", _const(3, size=8), _param("param_2", size=4, data_type="int")),
        ),
    )

    smt = expression_to_smt(expr)

    assert "(bvmul (_ bv3 32) param_2)" in smt
    assert "(bvadd (_ bv1 32) (bvmul (_ bv3 32) param_2))" in smt
    assert "(bvmul (_ bv3 64) ((_ sign_extend 32) param_2))" not in smt


def test_expression_to_smt_prefers_signed_extension_from_datatype_object_not_name():
    expr = _binary(
        "INT_SLESS",
        Expression.parameter(
            "param_1",
            size=4,
            data_type="custom_alias",
            data_type_obj=resolve_mock_data_type("int"),
        ),
        _const(0, size=8),
    )

    smt = expression_to_smt(expr)

    assert "((_ sign_extend 32) param_1)" in smt


def test_expression_to_smt_coerces_constant_zero_inside_bool_or():
    expr = _binary(
        "BOOL_OR",
        _binary("INT_EQUAL", _param("param_1", size=8), _const(0, size=8)),
        _const(0, size=1),
    )

    smt = expression_to_smt(expr)

    assert smt == "(or (= param_1 (_ bv0 64)) false)"


def test_expression_to_smt_coerces_bitvector_operand_inside_bool_and():
    expr = _binary(
        "BOOL_AND",
        _param("flag", size=1),
        _binary("INT_EQUAL", _param("param_1", size=8), _const(0, size=8)),
    )

    smt = expression_to_smt(expr)

    assert smt == "(and (not (= flag (_ bv0 8))) (= param_1 (_ bv0 64)))"


def test_float_phi_mixed_fp_and_bitvec_branches_returns_bitvec_ite():
    cond = Condition(_binary("INT_EQUAL", _param("selector", size=4), _const(0, size=4)))
    updated = _binary("FLOAT_ADD", _param("acc", size=8), _param("delta", size=8))
    phi = Expression.phi([(cond, updated), (None, _param("acc", size=8))])
    phi.size = 8

    smt = expression_to_smt(phi, float_mode="fp")

    assert "((_ fp.to_ieee_bv) (fp.add RNE" in smt
    assert "(ite " in smt
    assert "(ite " in smt and " acc)" in smt


def test_float_phi_uf_mode_does_not_wrap_bitvector_float_uf_with_fp_to_bv():
    cond = Condition(_binary("INT_EQUAL", _param("selector", size=4), _const(0, size=4)))
    updated = _binary("FLOAT_ADD", _param("acc", size=8), _param("delta", size=8))
    phi = Expression.phi([(cond, updated), (None, _param("acc", size=8))])
    phi.size = 8

    smt = expression_to_smt(phi)

    assert "fp.to_ieee_bv" not in smt
    assert smt == "(ite (= selector (_ bv0 32)) (float_add acc delta) acc)"


def test_float_phi_all_fp_branches_returns_bitvec_ite_without_double_fp_to_bv():
    cond = Condition(_binary("INT_EQUAL", _param("selector", size=4), _const(0, size=4)))
    left = _binary("FLOAT_ADD", _param("acc", size=8), _param("delta", size=8))
    right = _binary("FLOAT_SUB", _param("acc", size=8), _param("delta", size=8))
    phi = Expression.phi([(cond, left), (None, right)])
    phi.size = 8

    smt = expression_to_smt(phi, float_mode="fp")

    assert smt.startswith("(ite ")
    assert smt.count("((_ fp.to_ieee_bv) (fp.") == 2
    assert "((_ fp.to_ieee_bv) (ite" not in smt


def test_float_phi_all_fp_branches_return_boundary_does_not_double_convert():
    cond = Condition(_binary("INT_EQUAL", _param("selector", size=4), _const(0, size=4)))
    left = _binary("FLOAT_ADD", _param("acc", size=8), _param("delta", size=8))
    right = _binary("FLOAT_SUB", _param("acc", size=8), _param("delta", size=8))
    phi = Expression.phi([(cond, left), (None, right)])
    phi.size = 8

    expr_smt = expression_to_smt(phi, float_mode="fp")
    return_smt = coerce_return_value_to_bitvec(phi, expr_smt, 64)

    assert expression_smt_sort_kind(phi, float_mode="fp") == "BV"
    assert expr_smt.startswith("(ite ")
    assert expr_smt.count("((_ fp.to_ieee_bv) (fp.") == 2
    assert return_smt == expr_smt
    assert "((_ fp.to_ieee_bv) (ite" not in return_smt
