# -*- coding: utf-8 -*-

from scripts.function_tracer_pcode.proof.loop_template_abstraction import prove_template_equivalence
from scripts.function_tracer_pcode.checker.checker import EquivalenceChecker
from scripts.function_tracer_pcode.checker.result import EquivalenceResult
from scripts.function_tracer_pcode.proof.strategies.loop_template import (
    LoopTemplatePairwiseStrategy,
    _normalize_values_under_exact_conditions,
)
from scripts.function_tracer_pcode.proof.strategies.pairwise_models import ReturnCase
from scripts.function_tracer_pcode.core import Condition, Expression
from scripts.function_tracer_pcode.core.analysis import ReturnInfo
from scripts.function_tracer_pcode.smt import ParallelResult
from scripts.function_tracer_pcode.tests.unit._publication import published


def _const(value: int, size: int = 4) -> Expression:
    # 定数は作った時点で完成しているので、そのまま公開して返す。
    return published(Expression.constant(value, size=size))


def _param(name: str) -> Expression:
    return Expression.parameter(name, size=4)


def _add(left: Expression, right: Expression) -> Expression:
    expr = Expression.binary_op("INT_ADD", left, right)
    expr.size = max(left.size, right.size, 4)
    return expr


def _sub(left: Expression, right: Expression) -> Expression:
    expr = Expression.binary_op("INT_SUB", left, right)
    expr.size = max(left.size, right.size, 4)
    return expr


def _mul(left: Expression, right: Expression, size: int = 4) -> Expression:
    expr = Expression.binary_op("INT_MULT", left, right)
    expr.size = size
    return expr


def _neg(operand: Expression) -> Expression:
    expr = Expression.unary_op("INT_2COMP", operand)
    expr.size = operand.size
    return expr


def _exact_triangular(base: Expression) -> Expression:
    wide_left = Expression.unary_op("INT_ZEXT", base)
    wide_left.size = 8
    wide_right = Expression.unary_op("INT_ZEXT", _add(base, _const(1)))
    wide_right.size = 8
    product = Expression.binary_op("INT_MULT", wide_left, wide_right)
    product.size = 8
    shifted = Expression.binary_op("INT_RIGHT", product, _const(1, size=8))
    shifted.size = 8
    result = Expression.binary_op("SUBPIECE", shifted, _const(0))
    result.size = 4
    return result


def _exact_triangular_prev(base: Expression) -> Expression:
    wide_left = Expression.unary_op("INT_ZEXT", base)
    wide_left.size = 8
    wide_right = Expression.unary_op("INT_ZEXT", _sub(base, _const(1)))
    wide_right.size = 8
    product = Expression.binary_op("INT_MULT", wide_left, wide_right)
    product.size = 8
    shifted = Expression.binary_op("INT_RIGHT", product, _const(1, size=8))
    shifted.size = 8
    result = Expression.binary_op("SUBPIECE", shifted, _const(0))
    result.size = 4
    return result


def _wrapped_exact_triangular_phi(base: Expression) -> Expression:
    one = _const(1, size=base.size or 4)
    zero = _const(0, size=base.size or 4)
    parity = Expression.binary_op("INT_AND", base, one)
    parity.size = base.size or 4
    base_minus_one = Expression.binary_op("INT_SUB", base, one)
    base_minus_one.size = base.size or 4
    even_half = Expression.binary_op("INT_RIGHT", base, one)
    even_half.size = base.size or 4
    odd_half = Expression.binary_op("INT_RIGHT", base_minus_one, one)
    odd_half.size = base.size or 4
    even_value = Expression.binary_op("INT_MULT", even_half, base_minus_one)
    even_value.size = base.size or 4
    odd_value = Expression.binary_op("INT_MULT", base, odd_half)
    odd_value.size = base.size or 4
    condition_expr = Expression.binary_op("INT_EQUAL", parity, zero)
    condition_expr.size = 1
    phi = Expression.phi(
        [
            (Condition(condition_expr, False), even_value),
            (Condition(condition_expr, True), odd_value),
        ]
    )
    phi.size = base.size or 4
    return phi


def test_prove_template_equivalence_handles_triangular_bias_completion() -> None:
    n = _param("param_2")
    lhs = _exact_triangular(n)
    rhs = _add(_exact_triangular(_sub(n, _const(1))), n)

    proved, reason = prove_template_equivalence(lhs, rhs, target_bits=32, debug=True)

    assert not proved


def test_prove_template_equivalence_handles_distributed_products() -> None:
    m = _param("param_1")
    n = _param("param_2")
    tri_m = _exact_triangular(_sub(m, _const(1)))
    tri_n = _exact_triangular(n)

    lhs = _add(_mul(_add(tri_m, _const(1)), tri_n), tri_n)
    rhs = _mul(_add(_add(tri_m, _const(1)), _const(1)), tri_n)

    proved, reason = prove_template_equivalence(lhs, rhs, target_bits=32, debug=True)

    assert proved, reason


def test_prove_template_equivalence_rejects_genuine_difference() -> None:
    n = _param("param_2")
    lhs = _exact_triangular(n)
    rhs = _add(_exact_triangular(n), _const(1))

    proved, _reason = prove_template_equivalence(lhs, rhs, target_bits=32, debug=True)

    assert not proved


def test_prove_template_equivalence_handles_sample_like_nested_completion() -> None:
    p1 = _param("param_1")
    p2 = _param("param_2")
    tri_p2_prev = _exact_triangular(_sub(p2, _const(1)))
    tri_p1_prev = _exact_triangular(_sub(p1, _const(1)))

    inner = _add(_add(_const(1), tri_p2_prev), _sub(p2, _const(1)))
    lhs = _add(inner, _mul(inner, tri_p1_prev))

    tri_p2 = _exact_triangular(p2)
    rhs = _mul(tri_p2, _add(_const(1), tri_p1_prev))

    proved, reason = prove_template_equivalence(lhs, rhs, target_bits=32, debug=True)

    assert not proved


def test_prove_template_equivalence_strips_top_level_width_adapter_before_template_building() -> None:
    p1 = _param("param_1")
    p2 = _param("param_2")
    tri_p2 = _exact_triangular(p2)

    inner32 = _add(tri_p2, _mul(p1, tri_p2))
    wide_inner = Expression.unary_op("INT_ZEXT", inner32)
    wide_inner.size = 8
    lhs = Expression.binary_op("SUBPIECE", wide_inner, _const(0))
    lhs.size = 4

    rhs = _mul(_add(_const(1), p1), tri_p2)

    proved, reason = prove_template_equivalence(lhs, rhs, target_bits=32, debug=True)

    assert proved, reason


def test_prove_template_equivalence_matches_generic_atoms_after_width_normalization() -> None:
    p1 = _param("param_1")
    p2 = _param("param_2")
    tri_p2 = _exact_triangular(p2)

    unsupported = Expression.binary_op("INT_RIGHT", _mul(p1, _add(p1, _const(3))), _const(1))
    unsupported.size = 4
    wide_unsupported = Expression.unary_op("INT_ZEXT", unsupported)
    wide_unsupported.size = 8
    lhs_factor = Expression.binary_op("SUBPIECE", wide_unsupported, _const(0))
    lhs_factor.size = 4

    lhs = _mul(lhs_factor, tri_p2)
    rhs = _mul(unsupported, tri_p2)

    proved, reason = prove_template_equivalence(lhs, rhs, target_bits=32, debug=True)

    assert proved, reason


def test_prove_template_equivalence_extracts_high_half_from_shifted_piece() -> None:
    high = _param("param_hi")
    low = _param("param_lo")
    piece = Expression.binary_op("PIECE", high, low)
    piece.size = 8
    shifted = Expression.binary_op("INT_RIGHT", piece, _const(32, size=8))
    shifted.size = 8
    lhs = Expression.binary_op("SUBPIECE", shifted, _const(0))
    lhs.size = 4
    rhs = high

    proved, reason = prove_template_equivalence(lhs, rhs, target_bits=32, debug=True)

    assert proved, reason


def test_prove_template_equivalence_extracts_high_subpiece_from_piece() -> None:
    high = _param("param_hi")
    low = _param("param_lo")
    piece = Expression.binary_op("PIECE", high, low)
    piece.size = 8
    lhs = Expression.binary_op("SUBPIECE", piece, _const(4))
    lhs.size = 4
    rhs = high

    proved, reason = prove_template_equivalence(lhs, rhs, target_bits=32, debug=True)

    assert proved, reason


def test_prove_template_equivalence_does_not_require_string_rendering(monkeypatch) -> None:
    lhs = _add(_param("param_1"), _const(1))
    rhs = _add(_const(1), _param("param_1"))

    def _boom_to_string(_self, simplify=True):
        raise AssertionError("template abstraction should not depend on Expression.to_string")

    monkeypatch.setattr(Expression, "to_string", _boom_to_string)

    proved, reason = prove_template_equivalence(lhs, rhs, target_bits=32, debug=True)

    assert proved, reason


def test_prove_template_equivalence_recognizes_wrapped_exact_triangular_phi() -> None:
    p1 = _param("param_1")
    prev = _sub(p1, _const(1))
    wide_zero = _neg(_const(0))
    wide_zero.size = 4
    wide_zero_ext = Expression.unary_op("INT_ZEXT", wide_zero)
    wide_zero_ext.size = 8
    wide_prev = Expression.unary_op("INT_SEXT", prev)
    wide_prev.size = 8
    wrapped_base = _add(wide_zero_ext, wide_prev)
    wrapped_base.size = 8
    lhs = _wrapped_exact_triangular_phi(wrapped_base)
    rhs = _exact_triangular_prev(prev)

    proved, reason = prove_template_equivalence(lhs, rhs, target_bits=32, debug=True)

    assert proved, reason


def test_prove_template_equivalence_recognizes_wrapped_phi_completion_inside_product() -> None:
    p1 = _param("param_1")
    p2 = _param("param_2")
    prev = _sub(p1, _const(1))
    wide_zero = _neg(_const(0))
    wide_zero.size = 4
    wide_zero_ext = Expression.unary_op("INT_ZEXT", wide_zero)
    wide_zero_ext.size = 8
    wide_prev = Expression.unary_op("INT_SEXT", prev)
    wide_prev.size = 8
    wrapped = Expression.binary_op("INT_ADD", wide_zero_ext, wide_prev)
    wrapped.size = 8

    lhs = _mul(_exact_triangular(p1), _exact_triangular(p2))
    rhs_factor = _add(
        _add(_wrapped_exact_triangular_phi(wrapped), _mul(_const(2), p1)),
        _const(-1),
    )
    rhs = _mul(rhs_factor, _exact_triangular(p2))

    proved, reason = prove_template_equivalence(lhs, rhs, target_bits=32, debug=True)

    assert not proved


def test_prove_template_equivalence_recognizes_logged_affine_phi_completion_inside_product() -> None:
    p1 = _param("param_1")
    p2 = _param("param_2")
    one = _const(1)
    two = _add(one, one)
    base = _add(_add(one, p1), _neg(two))
    phi = _wrapped_exact_triangular_phi(base)

    lhs = _mul(_exact_triangular(p1), _exact_triangular(p2))
    rhs_factor = _add(_add(phi, _mul(_const(2), p1)), _neg(one))
    rhs = _mul(rhs_factor, _exact_triangular(p2))

    proved, reason = prove_template_equivalence(lhs, rhs, target_bits=32, debug=True)

    assert not proved


def test_loop_template_normalizes_values_under_exact_pair_conditions() -> None:
    p1 = _param("param_1")
    p2 = _param("param_2")
    lhs = _mul(_exact_triangular(p1), _exact_triangular(p2))
    rhs = _exact_triangular(p1)
    cond_expr = Expression.binary_op("INT_EQUAL", p2, _const(1))
    cond_expr.size = 1

    norm_lhs, norm_rhs = _normalize_values_under_exact_conditions(
        lhs,
        rhs,
        [Condition(cond_expr, False)],
    )
    proved, reason = prove_template_equivalence(
        norm_lhs,
        norm_rhs,
        target_bits=32,
        debug=True,
    )

    assert proved, reason


def test_loop_template_normalizes_values_under_constant_expression_equality() -> None:
    p1 = _param("param_1")
    p2 = _param("param_2")
    lhs = _mul(_exact_triangular(p1), _exact_triangular(p2))
    rhs = _exact_triangular(p1)
    equal_one_expr = _add(_const(0), _const(1))
    cond_expr = Expression.binary_op("INT_EQUAL", p2, equal_one_expr)
    cond_expr.size = 1

    norm_lhs, norm_rhs = _normalize_values_under_exact_conditions(
        lhs,
        rhs,
        [Condition(cond_expr, False)],
    )
    proved, reason = prove_template_equivalence(
        norm_lhs,
        norm_rhs,
        target_bits=32,
        debug=True,
    )

    assert proved, reason


def test_loop_template_normalizes_additive_completion_under_exact_pair_conditions() -> None:
    p1 = _param("param_1")
    p2 = _param("param_2")
    lhs = _mul(_exact_triangular(p1), _exact_triangular(p2))
    rhs = _add(_add(_exact_triangular(p1), _exact_triangular(p2)), _neg(_const(1)))
    cond_expr = Expression.binary_op("INT_EQUAL", p2, _const(1))
    cond_expr.size = 1

    norm_lhs, norm_rhs = _normalize_values_under_exact_conditions(
        lhs,
        rhs,
        [Condition(cond_expr, False)],
    )
    proved, reason = prove_template_equivalence(
        norm_lhs,
        norm_rhs,
        target_bits=32,
        debug=True,
    )

    assert proved, reason


def test_loop_template_uses_sign_facts_to_collapse_masked_byte_reconstruction() -> None:
    p2 = _param("param_2")
    tri_p2 = _exact_triangular(p2)

    positive = Expression.binary_op("INT_SLESS", _const(0), p2)
    positive.size = 1
    full_mask = Expression.unary_op("INT_2COMP", positive)
    full_mask.size = 4

    def _byte(expr: Expression, offset: int) -> Expression:
        byte_expr = Expression.binary_op("SUBPIECE", expr, _const(offset))
        byte_expr.size = 1
        return byte_expr

    masked_bytes = []
    for offset in range(3, -1, -1):
        masked = Expression.binary_op("INT_AND", _byte(tri_p2, offset), _byte(full_mask, offset))
        masked.size = 1
        masked_bytes.append(masked)

    rhs = Expression.binary_op(
        "PIECE",
        masked_bytes[0],
        Expression.binary_op(
            "PIECE",
            masked_bytes[1],
            Expression.binary_op("PIECE", masked_bytes[2], masked_bytes[3]),
        ),
    )
    rhs.size = 4

    norm_lhs, norm_rhs = _normalize_values_under_exact_conditions(
        tri_p2,
        rhs,
        [Condition(positive, False)],
    )
    proved, reason = prove_template_equivalence(
        norm_lhs,
        norm_rhs,
        target_bits=32,
        debug=True,
    )

    assert proved, reason


def test_loop_template_derives_exact_parameter_from_mask_and_residual_conditions() -> None:
    p1 = _param("param_1")
    mask_expr = Expression.binary_op("INT_AND", _const(0xFFFFFFF8), p1)
    mask_expr.size = 4
    residual_expr = Expression.binary_op("INT_SUB", p1, mask_expr)
    residual_expr.size = 4

    masked_equals_eight = Expression.binary_op(
        "INT_EQUAL",
        Expression.binary_op("INT_SUB", mask_expr, _const(8)),
        _const(0),
    )
    masked_equals_eight.operands[0].size = 4
    masked_equals_eight.size = 1

    residual_equals_one = Expression.binary_op(
        "INT_EQUAL",
        Expression.binary_op("INT_ADD", _neg(_const(1)), residual_expr),
        _const(0),
    )
    residual_equals_one.operands[0].size = 4
    residual_equals_one.size = 1

    norm_lhs, norm_rhs = _normalize_values_under_exact_conditions(
        p1,
        _const(9),
        [Condition(masked_equals_eight, False), Condition(residual_equals_one, False)],
    )

    assert published(norm_lhs).to_smt() == _const(9).to_smt()
    assert published(norm_rhs).to_smt() == _const(9).to_smt()


def test_loop_template_derives_exact_parameter_from_negated_notequal_conditions() -> None:
    p1 = _param("param_1")
    p2 = _param("param_2")
    mask_expr = Expression.binary_op("INT_AND", _const(0xFFFFFFF8), p1)
    mask_expr.size = 4
    residual_expr = Expression.binary_op("INT_SUB", p1, mask_expr)
    residual_expr.size = 4

    masked_difference = Expression.binary_op("INT_SUB", mask_expr, _const(8))
    masked_difference.size = 4
    masked_equals_eight_expr = Expression.binary_op(
        "INT_NOTEQUAL", masked_difference, _const(0)
    )
    masked_equals_eight_expr.size = 1
    masked_equals_eight = Condition(masked_equals_eight_expr, True)

    residual_difference = Expression.binary_op("INT_ADD", _neg(_const(1)), residual_expr)
    residual_difference.size = 4
    residual_equals_one_expr = Expression.binary_op(
        "INT_NOTEQUAL", residual_difference, _const(0)
    )
    residual_equals_one_expr.size = 1
    residual_equals_one = Condition(residual_equals_one_expr, True)

    norm_lhs, norm_rhs = _normalize_values_under_exact_conditions(
        _mul(_exact_triangular(p1), _exact_triangular(p2)),
        _mul(_const(45), _exact_triangular(p2)),
        [masked_equals_eight, residual_equals_one],
    )

    assert published(norm_lhs).to_smt() == published(norm_rhs).to_smt()


def test_loop_template_derives_exact_parameter_from_mask_equality_chain() -> None:
    p1 = _param("param_1")
    mask_expr = Expression.binary_op("INT_AND", p1, _const(0xFFFFFFF8))
    mask_expr.size = 4

    masked_equals_eight = Expression.binary_op(
        "INT_EQUAL",
        mask_expr,
        _const(8),
    )
    masked_equals_eight.size = 1

    param_equals_mask = Expression.binary_op("INT_EQUAL", p1, mask_expr)
    param_equals_mask.size = 1

    norm_lhs, norm_rhs = _normalize_values_under_exact_conditions(
        _exact_triangular(p1),
        _const(36),
        [Condition(masked_equals_eight, False), Condition(param_equals_mask, False)],
    )

    assert published(norm_lhs).to_smt() == _const(36).to_smt()
    assert published(norm_rhs).to_smt() == _const(36).to_smt()


def test_loop_template_uses_commutatively_normalized_mask_fact_keys() -> None:
    p1 = _param("param_1")
    value_expr = Expression.binary_op("INT_AND", _const(0xFFFFFFF8), p1)
    value_expr.size = 4
    cond_expr = Expression.binary_op(
        "INT_EQUAL",
        Expression.binary_op("INT_AND", p1, _const(0xFFFFFFF8)),
        _const(8),
    )
    cond_expr.operands[0].size = 4
    cond_expr.size = 1

    norm_lhs, norm_rhs = _normalize_values_under_exact_conditions(
        value_expr,
        _const(8),
        [Condition(cond_expr, False)],
    )

    assert published(norm_lhs).to_smt() == _const(8).to_smt()
    assert published(norm_rhs).to_smt() == _const(8).to_smt()


def test_loop_template_strategy_proves_equivalence_after_normalization_unknown() -> None:
    p2 = _param("param_2")
    lhs = _exact_triangular(p2)
    rhs = _add(_exact_triangular(_sub(p2, _const(1))), p2)

    class _DummyResult:
        is_equivalent = None
        results = []

    class _DummyRunner:
        def __init__(self) -> None:
            self.timeout = 5

        def run_sequential(self, _query: str) -> _DummyResult:
            return _DummyResult()

    strategy = LoopTemplatePairwiseStrategy(formula_builder=None, solver_runner=_DummyRunner(), debug=False)
    strategy._active_normalization_stats = {
        "timeout_fallback_attempts": 0,
        "changed_pairs": 0,
        "no_change_pairs": 0,
        "unsat_results": 0,
        "sat_results": 0,
        "unknown_results": 0,
    }
    base_ctx = {
        "header_lines": [],
        "params1": [],
        "params2": [],
        "extra_vars1": [],
        "extra_vars2": [],
        "return_size1": 32,
        "return_size2": 32,
    }
    case1 = ReturnCase(
        index=0,
        conditions=[],
        value_expr=lhs,
        return_info=ReturnInfo(address="0x0", value=lhs, conditions=[]),
        return_type="int",
    )
    case2 = ReturnCase(
        index=0,
        conditions=[],
        value_expr=rhs,
        return_info=ReturnInfo(address="0x1", value=rhs, conditions=[]),
        return_type="int",
    )

    result = strategy._try_normalization_equivalence(
        base_ctx,
        case1,
        case2,
        lambda smt: smt,
        lambda smt: smt,
        "(0,0)",
    )

    assert result.is_equivalent is None


def test_loop_template_strategy_rejects_mismatched_return_widths_before_template_proof() -> None:
    p1 = _param("param_1")
    lhs = _add(p1, _const(1))
    rhs = _add(_const(1), p1)

    class _DummyResult:
        is_equivalent = None
        results = []

    class _DummyRunner:
        def __init__(self) -> None:
            self.timeout = 5

        def run_sequential(self, _query: str) -> _DummyResult:
            return _DummyResult()

    strategy = LoopTemplatePairwiseStrategy(formula_builder=None, solver_runner=_DummyRunner(), debug=False)
    strategy._active_normalization_stats = {
        "timeout_fallback_attempts": 0,
        "changed_pairs": 0,
        "no_change_pairs": 0,
        "unsat_results": 0,
        "sat_results": 0,
        "unknown_results": 0,
    }
    base_ctx = {
        "header_lines": [],
        "params1": [],
        "params2": [],
        "extra_vars1": [],
        "extra_vars2": [],
        "return_size1": 64,
        "return_size2": 32,
    }
    case1 = ReturnCase(
        index=0,
        conditions=[],
        value_expr=lhs,
        return_info=ReturnInfo(address="0x0", value=lhs, conditions=[]),
        return_type="ulong",
    )
    case2 = ReturnCase(
        index=0,
        conditions=[],
        value_expr=rhs,
        return_info=ReturnInfo(address="0x1", value=rhs, conditions=[]),
        return_type="uint",
    )

    result = strategy._try_normalization_equivalence(
        base_ctx,
        case1,
        case2,
        lambda smt: smt,
        lambda smt: smt,
        "(0,0)",
    )

    assert result.is_equivalent is None


def test_checker_enables_loop_template_stage_for_pairwise_timeout_unknown() -> None:
    checker = EquivalenceChecker(
        strategy="pairwise",
        debug=False,
        enable_template_abstraction=True,
    )
    result = EquivalenceResult(
        is_equivalent=None,
        function1_name="f",
        function2_name="g",
        binary1_name="b1",
        binary2_name="b2",
        solver_results=ParallelResult(results=[]),
        pairwise_debug_stats={
            "timeout_fallback_attempts": 5,
            "changed_pairs": 0,
            "no_change_pairs": 0,
            "unsat_results": 0,
            "sat_results": 0,
            "unknown_results": 5,
        },
    )

    assert checker._should_try_loop_template_stage(result) is True
