# -*- coding: utf-8 -*-
"""Composite signedness inference regressions."""

from scripts.function_tracer_pcode.equivalence.arch.mips64 import MIPS64Handler
from scripts.function_tracer_pcode.equivalence.formula.builder import FormulaBuilder
from scripts.function_tracer_pcode.equivalence.param_semantics import (
    infer_parameter_semantics,
)
from scripts.function_tracer_pcode.model import (
    Condition,
    Expression,
    ExpressionType,
    FunctionReturnAnalysis,
    ReturnInfo,
)

from conftest import create_mock_analysis


def _param(name: str, size: int = 8) -> Expression:
    return Expression(ExpressionType.PARAMETER, name=name, size=size)


def _const(value: int, size: int = 8) -> Expression:
    return Expression(ExpressionType.CONSTANT, value=value, size=size)


def _binary(operator: str, left: Expression, right: Expression, size: int) -> Expression:
    return Expression(
        ExpressionType.BINARY_OP,
        operator=operator,
        operands=[left, right],
        size=size,
    )


def _mask32(name: str, source_size: int = 8) -> Expression:
    return _binary("INT_AND", _param(name, source_size), _const(0xFFFFFFFF, source_size), source_size)


def _or_guard_condition(name1: str, name2: str, size: int = 8) -> Condition:
    return Condition(
        _binary(
            "INT_SLESS",
            _const(-1, size),
            _binary("INT_OR", _param(name1, size), _param(name2, size), size),
            1,
        ),
        negated=False,
    )


def _sum_guard_condition(name1: str, name2: str, size: int = 8) -> Condition:
    return Condition(
        _binary(
            "INT_SLESS",
            _const(-1, size),
            _binary("INT_ADD", _param(name1, size), _param(name2, size), size),
            1,
        ),
        negated=False,
    )


def _analysis_with_guard(condition: Condition) -> FunctionReturnAnalysis:
    masked_union = _binary("INT_OR", _mask32("param_1"), _mask32("param_2"), 8)
    return FunctionReturnAnalysis(
        function_name="branch_multi_guard_like",
        entry_point="0x1000",
        parameters=[
            {"name": "param_1", "data_type": "ulong", "size": 8, "index": 0, "is_signed": False},
            {"name": "param_2", "data_type": "ulong", "size": 8, "index": 1, "is_signed": False},
        ],
        returns=[
            ReturnInfo(address="0x1000", conditions=[condition], value=masked_union),
        ],
    )


def test_infer_parameter_semantics_propagates_signedness_through_bitwise_or_compare():
    analysis = _analysis_with_guard(_or_guard_condition("param_1", "param_2"))

    hints = infer_parameter_semantics(analysis)

    assert hints[0].narrow_bits == 32
    assert hints[0].signedness == "signed"
    assert hints[1].narrow_bits == 32
    assert hints[1].signedness == "signed"


def test_infer_parameter_semantics_stays_conservative_for_arithmetic_composites():
    analysis = _analysis_with_guard(_sum_guard_condition("param_1", "param_2"))

    hints = infer_parameter_semantics(analysis)

    assert hints[0].narrow_bits == 32
    assert hints[0].signedness == "unsigned"
    assert hints[1].narrow_bits == 32
    assert hints[1].signedness == "unsigned"


def test_formula_builder_emits_signed_semantic_constraints_for_or_guard():
    builder = FormulaBuilder(debug=False)
    analysis = _analysis_with_guard(_or_guard_condition("param_1", "param_2"))

    formula = builder.build_equivalence_formula_extended(analysis, analysis).formula

    assert "; param_1_1: constrain to signed 32-bit semantic value" in formula
    assert "; param_2_1: constrain to signed 32-bit semantic value" in formula
    assert "; param_1_1: constrain to unsigned 32-bit semantic value" not in formula
    assert "; param_2_1: constrain to unsigned 32-bit semantic value" not in formula


def test_mips64_spurious_detection_uses_signed_or_guard_evidence():
    handler = MIPS64Handler(debug=True)

    analysis_wide = create_mock_analysis(
        function_name="branch_multi_guard_like",
        parameters=[
            {"name": "param_1", "data_type": "long", "size": 8, "index": 0},
            {"name": "param_2", "data_type": "long", "size": 8, "index": 1},
        ],
        returns=[
            ReturnInfo(
                address="0x1000",
                conditions=[_or_guard_condition("param_1", "param_2")],
                value=_binary("INT_OR", _mask32("param_1"), _mask32("param_2"), 8),
            )
        ],
    )
    analysis_narrow = create_mock_analysis(
        function_name="branch_multi_guard_like",
        parameters=[
            {"name": "param_1", "data_type": "uint", "size": 4, "index": 0},
            {"name": "param_2", "data_type": "uint", "size": 4, "index": 1},
        ],
    )

    counterexample = {
        "param_1_1": 0x0000000080000000,
        "param_1_2": 0x80000000,
        "param_2_1": 0x0,
        "param_2_2": 0x0,
    }

    constraints = handler.detect_spurious_counterexample(
        counterexample,
        analysis_wide,
        analysis_narrow,
        is_mips64_1=True,
        is_mips64_2=False,
    )

    assert constraints == {"param_1_1": ("signed", 32)}


def test_mips64_type_mismatch_uses_counterpart_semantic_width_hint_even_when_both_types_are_long():
    handler = MIPS64Handler(debug=True)

    mips_analysis = create_mock_analysis(
        function_name="fc_widen_then_bias_like",
        parameters=[
            {"name": "param_2", "data_type": "long", "size": 8, "index": 0},
        ],
    )
    hinted_peer = create_mock_analysis(
        function_name="fc_widen_then_bias_like",
        parameters=[
            {"name": "param_2", "data_type": "long", "size": 8, "index": 0},
        ],
        returns=[
            ReturnInfo(
                address="0x1000",
                conditions=[
                    Condition(
                        _binary("INT_NOTEQUAL", _mask32("param_2"), _const(0, 8), 1),
                        negated=False,
                    )
                ],
                value=_mask32("param_2"),
            )
        ],
    )

    override_map = handler.detect_param_type_mismatch(mips_analysis, hinted_peer)

    assert override_map == {0: "int"}
