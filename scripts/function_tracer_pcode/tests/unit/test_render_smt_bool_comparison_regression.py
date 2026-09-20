# -*- coding: utf-8 -*-

from typing import Optional

import pytest

from conftest import resolve_mock_data_type
from scripts.function_tracer_pcode.core import Condition, Expression
from scripts.function_tracer_pcode.proof.formula.returns import coerce_return_value_to_bitvec
from scripts.function_tracer_pcode.core.intrinsics import COUNTED_STATE_TRANSITION_VALUE_OPCODE
from scripts.function_tracer_pcode.core.render_smt import (
    UnsupportedSmtOperatorError,
    collect_float_predicate_smt_declarations,
    expression_contains_unsupported_smt_ops,
    expression_uses_smt_float_theory,
    expression_uses_smt_uf,
    expression_smt_sort_kind,
    expression_to_smt,
    smt_logic_name,
)
from scripts.function_tracer_pcode.core.runtime_refs import (
    CountedStateTransitionLoopSummaryRef,
    LoopSideEffectProfileRef,
)
from scripts.function_tracer_pcode.tests.unit._publication import published


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


def _state_times_const_summary(
    multiplier: int,
    *,
    side_effect_profile=None,
    transition_case_multiplier: Optional[int] = None,
) -> Expression:
    state = Expression.variable("__state", size=4)
    one = _const(1)
    start = _const(1)
    limit = _param("n")
    step = _const(1)
    transition = Expression.binary_op("INT_MULT", state, _const(multiplier))
    transition.size = 4
    case_transition = transition
    if transition_case_multiplier is not None:
        case_transition = Expression.binary_op("INT_MULT", state, _const(transition_case_multiplier))
        case_transition.size = 4
    runtime_ref = CountedStateTransitionLoopSummaryRef(
        initial_state=one,
        start_expr=start,
        limit_expr=limit,
        step_expr=step,
        transition_expr=transition,
        state_placeholder=state,
        transition_cases=(((), case_transition.structural_key()),),
        side_effect_profile=side_effect_profile or LoopSideEffectProfileRef(profile="pure"),
        guard_constraints=(),
        state_size=4,
        result_size=4,
        signed_loop=True,
    )
    return Expression.intrinsic(
        "COUNTED_STATE_TRANSITION_VALUE",
        [one, start, limit],
        size=4,
        runtime_ref=runtime_ref,
        opcode=COUNTED_STATE_TRANSITION_VALUE_OPCODE,
    )


def test_counted_state_transition_pure_multiply_lowers_without_uf():
    expr = _state_times_const_summary(5)

    smt = expression_to_smt(published(expr))

    assert "rt_counted_state_transition_value" not in smt
    assert "(bvmul (_ bv1 32)" in smt
    assert "(ite (= ((_ extract 0 0)" in smt
    assert not expression_uses_smt_uf(expr)


def test_counted_state_transition_effectful_multiply_stays_uf():
    expr = _state_times_const_summary(
        5,
        side_effect_profile=LoopSideEffectProfileRef(
            profile="effectful",
            memory_reads=True,
        ),
    )

    smt = expression_to_smt(published(expr))

    assert "rt_counted_state_transition_value" in smt
    assert expression_uses_smt_uf(expr)


def test_counted_state_transition_mismatched_case_signature_stays_uf():
    expr = _state_times_const_summary(5, transition_case_multiplier=6)

    smt = expression_to_smt(published(expr))

    assert "rt_counted_state_transition_value" in smt
    assert expression_uses_smt_uf(expr)


def test_expression_to_smt_lowers_neon_ext_byte_extract():
    first = _param("v_first", size=16)
    second = _param("v_second", size=16)
    expr = Expression.intrinsic(
        "NEON_ext",
        [first, second, _const(8, 1), _const(1, 1)],
        size=16,
    )

    smt = expression_to_smt(published(expr))

    assert "((_ extract 63 56) v_second)" in smt
    assert "((_ extract 7 0) v_second)" in smt
    assert "((_ extract 127 120) v_first)" in smt
    assert "((_ extract 71 64) v_first)" in smt
    assert not expression_contains_unsupported_smt_ops(expr)


def test_expression_to_smt_rejects_neon_ext_nonconstant_offset():
    expr = Expression.intrinsic(
        "NEON_ext",
        [_param("v_first", size=16), _param("v_second", size=16), _param("offset", size=1), _const(1, 1)],
        size=16,
    )

    assert expression_contains_unsupported_smt_ops(expr)
    try:
        expression_to_smt(published(expr))
    except ValueError as exc:
        assert "constant byte offset" in str(exc)
    else:
        raise AssertionError("NEON_ext with nonconstant offset must remain unlowered")


def test_expression_to_smt_rejects_neon_ext_element_size_other_than_one():
    expr = Expression.intrinsic(
        "NEON_ext",
        [_param("v_first", size=16), _param("v_second", size=16), _const(8, 1), _const(2, 1)],
        size=16,
    )

    assert expression_contains_unsupported_smt_ops(expr)
    try:
        expression_to_smt(published(expr))
    except ValueError as exc:
        assert "element_size operand 1" in str(exc)
    else:
        raise AssertionError("NEON_ext with element_size != 1 must remain unlowered")


def test_expression_to_smt_keeps_raw_callother_id_150_unsupported_without_userop_name():
    expr = Expression.intrinsic(
        "CALLOTHER",
        [_const(150), _param("v_first", size=16), _param("v_second", size=16), _const(8, 1), _const(1, 1)],
        size=16,
        opcode=9,
    )

    assert expression_contains_unsupported_smt_ops(expr)
    try:
        expression_to_smt(published(expr))
    except ValueError as exc:
        assert "Unsupported intrinsic" in str(exc)
    else:
        raise AssertionError("raw CALLOTHER id 150 must not lower without object-derived userop name")


def test_expression_to_smt_coerces_bool_vs_bitvector_equality_without_sort_error():
    bool_expr = _binary("INT_SLESS", _param("param_2"), _param("param_1"))
    expr = _binary("INT_EQUAL", bool_expr, _const(0, 4))

    smt = expression_to_smt(published(expr))

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
    smt = expression_to_smt(published(expr), float_mode="fp")
    assert "(fp.add RNE" in smt
    assert "(fp.mul RNE" in smt
    assert "(fp.sub RNE" in smt


def test_piece_converts_both_fp_operands_before_concat():
    import z3

    left = _binary("FLOAT_ADD", _param("left_a", size=8), _param("left_b", size=8))
    right = _binary("FLOAT_SUB", _param("right_a", size=8), _param("right_b", size=8))
    expr = _binary("PIECE", left, right)

    smt = expression_to_smt(published(expr), float_mode="fp")

    assert smt.count("((_ fp.to_ieee_bv) (fp.") == 2
    assert smt.startswith("(concat ")
    z3.parse_smt2_string(
        "\n".join(
            [
                "(set-logic QF_FPBV)",
                "(declare-const left_a (_ BitVec 64))",
                "(declare-const left_b (_ BitVec 64))",
                "(declare-const right_a (_ BitVec 64))",
                "(declare-const right_b (_ BitVec 64))",
                f"(assert (= {smt} {smt}))",
                "(check-sat)",
            ]
        )
    )


def test_piece_converts_only_fp_operand_in_mixed_fp_bitvector_concat():
    fp_value = _binary("FLOAT_ADD", _param("a", size=8), _param("b", size=8))
    expr = _binary("PIECE", fp_value, _param("tail", size=8))

    smt = expression_to_smt(published(expr), float_mode="fp")

    assert smt.count("fp.to_ieee_bv") == 1
    assert smt.endswith(" tail)")
    assert "(concat (fp." not in smt


def test_subpiece_converts_fp_source_before_extract():
    source = _binary("FLOAT_ADD", _param("a", size=8), _param("b", size=8))
    expr = _binary("SUBPIECE", source, _const(0, size=4))
    expr.size = 4

    smt = expression_to_smt(published(expr), float_mode="fp")

    assert smt.startswith("((_ extract 31 0) ((_ fp.to_ieee_bv) (fp.add RNE")


def test_piece_and_subpiece_width_contracts_fail_closed():
    unknown_operand = Expression.parameter("unknown", size=0)
    piece = _binary("PIECE", unknown_operand, _param("tail", size=8))
    unknown_subpiece = _binary("SUBPIECE", _param("source", size=8), _const(0))
    out_of_range = _binary("SUBPIECE", _param("source", size=8), _const(4))
    out_of_range.size = 8
    mismatched_piece = _binary("PIECE", _param("left", size=8), _param("right", size=8))
    mismatched_piece.size = 8

    for expr, reason in (
        (piece, "PIECE operand width is unavailable"),
        (unknown_subpiece, "SUBPIECE result width is unavailable"),
        (out_of_range, "SUBPIECE extraction range exceeds source width"),
        (mismatched_piece, "PIECE result width does not equal"),
    ):
        assert expression_contains_unsupported_smt_ops(expr)
        with pytest.raises(UnsupportedSmtOperatorError, match=reason):
            expression_to_smt(published(expr), float_mode="fp")


@pytest.mark.parametrize("operator", ["PIECE", "SUBPIECE"])
@pytest.mark.parametrize("bad_size", ["bad", -1])
def test_piece_and_subpiece_malformed_size_is_typed_at_direct_renderer_boundary(
    operator,
    bad_size,
):
    expr = _binary(operator, _param("source", size=8), _param("tail", size=8))
    expr.size = bad_size

    assert expression_contains_unsupported_smt_ops(expr)
    with pytest.raises(UnsupportedSmtOperatorError, match="result width is invalid"):
        expression_to_smt(published(expr), float_mode="fp")


@pytest.mark.parametrize("operator", ["PIECE", "SUBPIECE"])
def test_piece_and_subpiece_bad_arity_is_typed_at_direct_renderer_boundary(operator):
    expr = _binary(operator, _param("source", size=8), _param("tail", size=8))
    expr.operands = expr.operands[:1]

    assert expression_contains_unsupported_smt_ops(expr)
    with pytest.raises(UnsupportedSmtOperatorError, match="requires exactly two operands"):
        expression_to_smt(published(expr), float_mode="fp")


def test_piece_and_subpiece_reject_phi_with_an_unknown_branch_width():
    selector = Condition(
        _binary("INT_EQUAL", _param("selector"), _const(0)),
        True,
    )
    phi = Expression.phi(
        [
            (selector, _param("known", size=8)),
            (None, _param("unknown", size=0)),
        ]
    )
    piece = _binary("PIECE", phi, _param("tail", size=8))
    subpiece = _binary("SUBPIECE", phi, _const(0))
    subpiece.size = 4

    for expr, reason in (
        (piece, "PIECE operand width is unavailable"),
        (subpiece, "SUBPIECE source width is unavailable"),
    ):
        assert expression_contains_unsupported_smt_ops(expr)
        with pytest.raises(UnsupportedSmtOperatorError, match=reason):
            expression_to_smt(published(expr), float_mode="fp")


def test_int2float_signed_i32_to_binary64_uses_exact_fp_theory_lowering():
    import z3

    operand = _param("n", size=4, data_type="int")
    expr = Expression.unary_op("INT2FLOAT", operand)
    expr.size = 8

    smt = expression_to_smt(published(expr), float_mode="fp")

    assert smt == "((_ to_fp 11 53) RNE n)"
    assert "to_fp_unsigned" not in smt
    assert expression_smt_sort_kind(expr, float_mode="fp") == "FP"
    assert expression_uses_smt_float_theory(expr)
    assert not expression_contains_unsupported_smt_ops(expr)
    z3.parse_smt2_string(
        "\n".join(
            [
                "(set-logic QF_FPBV)",
                "(declare-const n (_ BitVec 32))",
                f"(assert (fp.eq {smt} {smt}))",
                "(check-sat)",
            ]
        )
    )


def test_int2float_signed_i32_to_binary32_preserves_output_sort():
    operand = _param("n", size=4, data_type="int")
    expr = Expression.unary_op("INT2FLOAT", operand)
    expr.size = 4

    assert expression_to_smt(published(expr), float_mode="fp") == "((_ to_fp 8 24) RNE n)"
    assert expression_smt_sort_kind(expr, float_mode="fp") == "FP"


def test_int2float_float_div_uf_mode_refuses_before_emitting_mixed_sorts():
    numerator = Expression.unary_op("INT2FLOAT", _param("a", size=4))
    numerator.size = 8
    denominator = Expression.unary_op("INT2FLOAT", _param("b", size=4))
    denominator.size = 8
    expr = Expression.binary_op("FLOAT_DIV", numerator, denominator)
    expr.size = 8

    assert expression_smt_sort_kind(numerator, float_mode="uf") == "BV"
    with pytest.raises(UnsupportedSmtOperatorError) as exc:
        expression_to_smt(published(expr), float_mode="uf")
    assert exc.value.operator == "INT2FLOAT"
    assert (
        exc.value.reason
        == "exact integer-to-float lowering requires FP theory mode"
    )


def test_int2float_negative_input_is_not_unsigned_conversion():
    import z3

    solver = z3.Solver()
    n = z3.BitVec("n", 32)
    signed = z3.fpToFP(z3.RNE(), n, z3.Float64())
    unsigned = z3.fpUnsignedToFP(z3.RNE(), n, z3.Float64())
    solver.add(n == z3.BitVecVal(0xFFFFFFFF, 32))
    solver.add(signed == unsigned)

    assert solver.check() == z3.unsat


def test_int2float_unknown_output_width_fails_closed():
    operand = _param("n", size=4, data_type="int")
    expr = Expression.unary_op("INT2FLOAT", operand)
    expr.size = 0

    assert expression_contains_unsupported_smt_ops(expr)
    with pytest.raises(UnsupportedSmtOperatorError) as exc:
        expression_to_smt(published(expr), float_mode="fp")
    assert exc.value.reason == "output floating-point width is unsupported"


def test_mixed_precision_int2float_division_fails_closed():
    numerator = Expression.unary_op("INT2FLOAT", _param("value", size=4))
    numerator.size = 8
    denominator = Expression.unary_op("INT2FLOAT", _param("count", size=4))
    denominator.size = 4
    expr = Expression.binary_op("FLOAT_DIV", numerator, denominator)
    expr.size = 8

    assert expression_contains_unsupported_smt_ops(expr)
    with pytest.raises(UnsupportedSmtOperatorError) as exc:
        expression_to_smt(published(expr), float_mode="fp")
    assert exc.value.operator == "FLOAT_DIV"
    assert exc.value.reason == "floating-point operand/result precisions do not match"


def test_generic_unsupported_unary_operator_never_becomes_smt_function():
    expr = Expression.unary_op("FLOAT2INT", _param("x", size=8))
    expr.size = 4

    assert expression_contains_unsupported_smt_ops(expr)
    with pytest.raises(UnsupportedSmtOperatorError) as exc:
        expression_to_smt(published(expr), float_mode="fp")
    assert exc.value.operator == "FLOAT2INT"
    assert exc.value.reason == "unsupported unary operator"


def test_generic_unsupported_binary_operator_never_becomes_smt_function():
    expr = Expression.binary_op("ADD", _param("x"), _const(1))

    assert expression_contains_unsupported_smt_ops(expr)
    with pytest.raises(UnsupportedSmtOperatorError) as exc:
        expression_to_smt(published(expr))
    assert exc.value.operator == "ADD"
    assert exc.value.reason == "unsupported binary operator"


def test_float_binary_arithmetic_declares_uninterpreted_function_for_non_fp_width():
    expr = _binary("FLOAT_MULT", _param("param_2", size=10), _param("param_1", size=10))

    smt = expression_to_smt(published(expr), float_mode="fp")
    declarations = collect_float_predicate_smt_declarations(expr, float_mode="fp")

    assert smt == "(float_mult param_2 param_1)"
    assert declarations == [
        "(declare-fun float_mult ((_ BitVec 80) (_ BitVec 80)) (_ BitVec 80))",
    ]


def test_float_predicate_smt_declarations_are_collected_for_ufbv_queries():
    expr = _binary("FLOAT_LESS", _param("param_2", size=8), _param("param_1", size=8))

    smt = expression_to_smt(published(expr))
    declarations = collect_float_predicate_smt_declarations(expr)

    assert smt == "(float_less param_2 param_1)"
    assert declarations == [
        "(declare-fun float_less ((_ BitVec 64) (_ BitVec 64)) Bool)",
    ]


def test_float_predicate_can_render_with_ieee754_fp_theory():
    expr = _binary("FLOAT_LESS", _param("param_2", size=8), _param("param_1", size=8))

    smt = expression_to_smt(published(expr), float_mode="fp")
    declarations = collect_float_predicate_smt_declarations(expr, float_mode="fp")

    assert smt == "(fp.lt ((_ to_fp 11 53) param_2) ((_ to_fp 11 53) param_1))"
    assert declarations == []


def test_float_mixed_width_binary_skips_fp_arithmetic_path():
    expr = _binary("FLOAT_ADD", _param("param_2", size=10), _param("param_1", size=8))

    smt = expression_to_smt(published(expr), float_mode="fp")
    declarations = collect_float_predicate_smt_declarations(expr, float_mode="fp")

    assert smt == "(float_add param_2 param_1)"
    assert declarations == [
        "(declare-fun float_add ((_ BitVec 80) (_ BitVec 64)) (_ BitVec 80))",
    ]


def test_float_signed_division_uses_fp_theory_for_non_exceptional_widths():
    expr = _binary("FLOAT_SDIV", _param("param_2", size=8), _param("param_1", size=8))

    smt = expression_to_smt(published(expr), float_mode="fp")
    declarations = collect_float_predicate_smt_declarations(expr, float_mode="fp")

    assert smt == "(fp.div RNE ((_ to_fp 11 53) param_2) ((_ to_fp 11 53) param_1))"
    assert declarations == []


def test_float_signed_division_known_zero_divisor_falls_back_to_ufbv():
    expr = _binary("FLOAT_SDIV", _param("param_2", size=8), _const(0, size=8))

    smt = expression_to_smt(published(expr), float_mode="fp")
    declarations = collect_float_predicate_smt_declarations(expr, float_mode="fp")

    assert smt == "(float_div param_2 (_ bv0 64))"
    assert declarations == [
        "(declare-fun float_div ((_ BitVec 64) (_ BitVec 64)) (_ BitVec 64))",
    ]
    assert expression_uses_smt_uf(expr, float_mode="fp") is True


def test_float_signed_remainder_known_nan_operand_falls_back_to_ufbv():
    expr = _binary("FLOAT_SREM", _const(0x7FF8000000000000, size=8), _param("param_1", size=8))

    smt = expression_to_smt(published(expr), float_mode="fp")
    declarations = collect_float_predicate_smt_declarations(expr, float_mode="fp")

    assert smt == "(float_rem (_ bv9221120237041090560 64) param_1)"
    assert declarations == [
        "(declare-fun float_rem ((_ BitVec 64) (_ BitVec 64)) (_ BitVec 64))",
    ]


def test_unsupported_float_width_keeps_uf_logic_visible():
    expr = _binary("FLOAT_LESS", _param("param_2", size=10), _param("param_1", size=10))

    smt = expression_to_smt(published(expr), float_mode="fp")
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

    smt = expression_to_smt(published(expr), float_mode="fp")

    assert smt == "(not (fp.eq ((_ to_fp 11 53) param_2) ((_ to_fp 11 53) param_1)))"


def test_float_neg_lowers_to_bit_preserving_sign_flip():
    expr = Expression.unary_op("FLOAT_NEG", _param("param_1", size=8, data_type="double"))
    expr.size = 8

    smt = expression_to_smt(published(expr), float_mode="fp")

    assert smt == "(bvxor param_1 (_ bv9223372036854775808 64))"
    assert "float_neg" not in smt


def test_float_abs_lowers_to_bit_preserving_sign_clear():
    expr = Expression.unary_op("FLOAT_ABS", _param("param_1", size=4, data_type="float"))
    expr.size = 4

    smt = expression_to_smt(published(expr), float_mode="fp")

    assert smt == "(bvand param_1 (_ bv2147483647 32))"
    assert "float_abs" not in smt


def test_float_unary_ops_are_supported_by_smt_gate():
    neg_expr = Expression.unary_op("FLOAT_NEG", _param("param_1", size=8, data_type="double"))
    neg_expr.size = 8
    abs_expr = Expression.unary_op("FLOAT_ABS", _param("param_2", size=4, data_type="float"))
    abs_expr.size = 4
    sqrt_expr = Expression.unary_op("FLOAT_SQRT", _param("param_2", size=4, data_type="float"))
    sqrt_expr.size = 4
    nan_expr = Expression.unary_op("FLOAT_NAN", _param("param_3", size=8, data_type="double"))
    nan_expr.size = 1

    assert expression_contains_unsupported_smt_ops(neg_expr) is False
    assert expression_contains_unsupported_smt_ops(abs_expr) is False
    assert expression_contains_unsupported_smt_ops(sqrt_expr) is False
    assert expression_contains_unsupported_smt_ops(nan_expr) is False


def test_float_nan_of_sqrt_uses_ieee754_fp_theory_in_fp_mode():
    sqrt_expr = Expression.unary_op("FLOAT_SQRT", _param("param_1", size=8, data_type="double"))
    sqrt_expr.size = 8
    expr = Expression.unary_op("FLOAT_NAN", sqrt_expr)
    expr.size = 1

    smt = expression_to_smt(published(expr), float_mode="fp")

    assert smt == (
        "(fp.isNaN ((_ to_fp 11 53) "
        "((_ fp.to_ieee_bv) (fp.sqrt RNE ((_ to_fp 11 53) param_1)))))"
    )


def test_float_sqrt_uses_ieee754_fp_theory_in_fp_mode():
    expr = Expression.unary_op("FLOAT_SQRT", _param("param_1", size=8, data_type="double"))
    expr.size = 8

    smt = expression_to_smt(published(expr), float_mode="fp")
    declarations = collect_float_predicate_smt_declarations(expr, float_mode="fp")

    assert expression_uses_smt_float_theory(expr) is True
    assert smt == "((_ fp.to_ieee_bv) (fp.sqrt RNE ((_ to_fp 11 53) param_1)))"
    assert declarations == []


def test_float_sqrt_uses_declared_uf_for_ufbv_queries():
    expr = Expression.unary_op("FLOAT_SQRT", _param("param_1", size=8, data_type="double"))
    expr.size = 8

    smt = expression_to_smt(published(expr))
    declarations = collect_float_predicate_smt_declarations(expr)

    assert smt == "(float_sqrt param_1)"
    assert declarations == [
        "(declare-fun float_sqrt ((_ BitVec 64)) (_ BitVec 64))",
    ]
    assert expression_uses_smt_uf(expr, float_mode="uf") is True


def test_float_nan_uses_ieee754_fp_theory_in_fp_mode():
    expr = Expression.unary_op("FLOAT_NAN", _param("param_1", size=8, data_type="double"))
    expr.size = 1

    smt = expression_to_smt(published(expr), float_mode="fp")
    declarations = collect_float_predicate_smt_declarations(expr, float_mode="fp")

    assert smt == "(fp.isNaN ((_ to_fp 11 53) param_1))"
    assert declarations == []


def test_float_nan_uses_declared_uf_for_ufbv_queries():
    expr = Expression.unary_op("FLOAT_NAN", _param("param_1", size=10))
    expr.size = 1

    smt = expression_to_smt(published(expr), float_mode="fp")
    declarations = collect_float_predicate_smt_declarations(expr, float_mode="fp")

    assert smt == "(float_nan param_1)"
    assert declarations == [
        "(declare-fun float_nan ((_ BitVec 80)) Bool)",
    ]
    assert expression_uses_smt_uf(expr, float_mode="fp") is True


def test_expression_to_smt_coerces_bool_before_integer_twos_complement():
    bool_expr = _binary("INT_EQUAL", _binary("INT_AND", _param("param_1", size=1), _const(1, size=1)), _const(0, size=1))
    expr = Expression.unary_op("INT_2COMP", bool_expr)

    smt = expression_to_smt(published(expr))

    assert "(bvneg (=" not in smt
    assert smt == (
        "(bvneg (ite (= (bvand param_1 (_ bv1 8)) (_ bv0 8)) "
        "(_ bv1 8) (_ bv0 8)))"
    )


def test_expression_to_smt_coerces_bitvector_before_bool_negate():
    low_byte = _binary("SUBPIECE", _param("param_1", size=4), _const(0, size=4))
    low_byte.size = 1
    expr = Expression.unary_op("BOOL_NEGATE", low_byte)

    smt = expression_to_smt(published(expr))

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

    smt = expression_to_smt(published(piece))

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

    smt = expression_to_smt(published(bool_phi))

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

    smt = expression_to_smt(published(expr))

    assert smt == "(_ bv0 32)"


def test_expression_to_smt_sign_extends_narrow_operand_for_signed_width_mismatch_compare():
    expr = _binary(
        "INT_SLESS",
        _param("param_3", size=4, data_type="int"),
        _binary("INT_ADD", _param("param_1", size=4, data_type="int"), _const(10, size=8)),
    )

    smt = expression_to_smt(published(expr))

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

    smt = expression_to_smt(published(expr))

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

    smt = expression_to_smt(published(expr))

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

    smt = expression_to_smt(published(expr))

    assert "((_ sign_extend 32) param_1)" in smt


def test_expression_to_smt_coerces_constant_zero_inside_bool_or():
    expr = _binary(
        "BOOL_OR",
        _binary("INT_EQUAL", _param("param_1", size=8), _const(0, size=8)),
        _const(0, size=1),
    )

    smt = expression_to_smt(published(expr))

    assert smt == "(or (= param_1 (_ bv0 64)) false)"


def test_expression_to_smt_coerces_bitvector_operand_inside_bool_and():
    expr = _binary(
        "BOOL_AND",
        _param("flag", size=1),
        _binary("INT_EQUAL", _param("param_1", size=8), _const(0, size=8)),
    )

    smt = expression_to_smt(published(expr))

    assert smt == "(and (not (= flag (_ bv0 8))) (= param_1 (_ bv0 64)))"


def test_float_phi_mixed_fp_and_bitvec_branches_returns_bitvec_ite():
    cond = Condition(_binary("INT_EQUAL", _param("selector", size=4), _const(0, size=4)))
    updated = _binary("FLOAT_ADD", _param("acc", size=8), _param("delta", size=8))
    phi = Expression.phi([(cond, updated), (None, _param("acc", size=8))])
    phi.size = 8

    smt = expression_to_smt(published(phi), float_mode="fp")

    assert "((_ fp.to_ieee_bv) (fp.add RNE" in smt
    assert "(ite " in smt
    assert "(ite " in smt and " acc)" in smt


def test_float_phi_uf_mode_does_not_wrap_bitvector_float_uf_with_fp_to_bv():
    cond = Condition(_binary("INT_EQUAL", _param("selector", size=4), _const(0, size=4)))
    updated = _binary("FLOAT_ADD", _param("acc", size=8), _param("delta", size=8))
    phi = Expression.phi([(cond, updated), (None, _param("acc", size=8))])
    phi.size = 8

    smt = expression_to_smt(published(phi))

    assert "fp.to_ieee_bv" not in smt
    assert smt == "(ite (= selector (_ bv0 32)) (float_add acc delta) acc)"


def test_float_phi_all_fp_branches_returns_bitvec_ite_without_double_fp_to_bv():
    cond = Condition(_binary("INT_EQUAL", _param("selector", size=4), _const(0, size=4)))
    left = _binary("FLOAT_ADD", _param("acc", size=8), _param("delta", size=8))
    right = _binary("FLOAT_SUB", _param("acc", size=8), _param("delta", size=8))
    phi = Expression.phi([(cond, left), (None, right)])
    phi.size = 8

    smt = expression_to_smt(published(phi), float_mode="fp")

    assert smt.startswith("(ite ")
    assert smt.count("((_ fp.to_ieee_bv) (fp.") == 2
    assert "((_ fp.to_ieee_bv) (ite" not in smt


def test_float_phi_all_fp_branches_return_boundary_does_not_double_convert():
    cond = Condition(_binary("INT_EQUAL", _param("selector", size=4), _const(0, size=4)))
    left = _binary("FLOAT_ADD", _param("acc", size=8), _param("delta", size=8))
    right = _binary("FLOAT_SUB", _param("acc", size=8), _param("delta", size=8))
    phi = Expression.phi([(cond, left), (None, right)])
    phi.size = 8

    expr_smt = expression_to_smt(published(phi), float_mode="fp")
    return_smt = coerce_return_value_to_bitvec(phi, expr_smt, 64)

    assert expression_smt_sort_kind(phi, float_mode="fp") == "BV"
    assert expr_smt.startswith("(ite ")
    assert expr_smt.count("((_ fp.to_ieee_bv) (fp.") == 2
    assert return_smt == expr_smt
    assert "((_ fp.to_ieee_bv) (ite" not in return_smt
