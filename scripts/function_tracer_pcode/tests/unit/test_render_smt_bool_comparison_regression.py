# -*- coding: utf-8 -*-

from typing import Optional

from scripts.function_tracer_pcode.model import Condition, Expression
from scripts.function_tracer_pcode.model.render_smt import expression_to_smt


def _param(name: str, size: int = 4, data_type: Optional[str] = None) -> Expression:
    return Expression.parameter(name, size=size, data_type=data_type)


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
