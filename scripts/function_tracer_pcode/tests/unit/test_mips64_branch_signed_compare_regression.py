# -*- coding: utf-8 -*-
"""branch_signed_compare 系の MIPS64 偽反例検出に関する回帰テスト"""

from scripts.function_tracer_pcode.equivalence.arch.mips64 import MIPS64Handler
from scripts.function_tracer_pcode.model import Condition, Expression, ExpressionType, ReturnInfo

from conftest import create_mock_analysis


def _param(name: str, size: int) -> Expression:
    return Expression(ExpressionType.PARAMETER, name=name, size=size)


def _const(value: int, size: int) -> Expression:
    return Expression(ExpressionType.CONSTANT, value=value, size=size)


def _subpiece(name: str, source_size: int = 8) -> Expression:
    return Expression(
        ExpressionType.BINARY_OP,
        operator="SUBPIECE",
        operands=[_param(name, source_size), _const(0, 8)],
        size=4,
    )


def _signed_lt_zero(name: str, size: int = 8) -> Condition:
    return Condition(
        Expression(
            ExpressionType.BINARY_OP,
            operator="INT_SLESS",
            operands=[_param(name, size), _const(0, size)],
            size=1,
        ),
        negated=False,
    )


def _minus_one_lt_param(name: str, size: int = 8) -> Condition:
    return Condition(
        Expression(
            ExpressionType.BINARY_OP,
            operator="INT_SLESS",
            operands=[_const(-1, size), _param(name, size)],
            size=1,
        ),
        negated=False,
    )


def test_width_mismatch_uses_signed_branch_evidence_for_spurious_detection():
    handler = MIPS64Handler(debug=True)

    analysis_wide = create_mock_analysis(
        function_name="branch_signed_compare",
        parameters=[
            {"name": "param_1", "data_type": "long", "size": 8, "index": 0},
        ],
        returns=[
            ReturnInfo(
                address="0x1000",
                conditions=[_signed_lt_zero("param_1", 8)],
                value=_subpiece("param_1", 8),
            )
        ],
    )
    analysis_narrow = create_mock_analysis(
        function_name="branch_signed_compare",
        parameters=[
            {"name": "param_1", "data_type": "uint", "size": 4, "index": 0},
        ],
    )

    # lower 32bit は同じ負値だが、wide 側がゼロ拡張されているため
    # signed 32bit としては偽反例になる。
    counterexample = {
        "param_1_1": 0x00000000FA56E326,
        "param_1_2": 0xFA56E326,
    }

    constraints = handler.detect_spurious_counterexample(
        counterexample,
        analysis_wide,
        analysis_narrow,
        is_mips64_1=True,
        is_mips64_2=False,
    )

    assert constraints == {"param_1_1": ("signed", 32)}


def test_minus_one_comparison_is_also_treated_as_signed_branch_evidence():
    handler = MIPS64Handler(debug=True)

    analysis_wide = create_mock_analysis(
        function_name="branch_signed_compare",
        parameters=[
            {"name": "param_2", "data_type": "long", "size": 8, "index": 1},
        ],
        returns=[
            ReturnInfo(
                address="0x1000",
                conditions=[_minus_one_lt_param("param_2", 8)],
                value=_subpiece("param_2", 8),
            )
        ],
    )
    analysis_narrow = create_mock_analysis(
        function_name="branch_signed_compare",
        parameters=[
            {"name": "param_2", "data_type": "uint", "size": 4, "index": 1},
        ],
    )

    counterexample = {
        "param_2_1": 0x00000000FA56E326,
        "param_2_2": 0xFA56E326,
    }

    constraints = handler.detect_spurious_counterexample(
        counterexample,
        analysis_wide,
        analysis_narrow,
        is_mips64_1=True,
        is_mips64_2=False,
    )

    assert constraints == {"param_2_1": ("signed", 32)}


def test_width_mismatch_without_signed_branch_evidence_keeps_unsigned_fallback():
    handler = MIPS64Handler(debug=True)

    analysis_wide = create_mock_analysis(
        function_name="branch_unsigned_like",
        parameters=[
            {"name": "param_1", "data_type": "long", "size": 8, "index": 0},
        ],
        returns=[
            ReturnInfo(
                address="0x1000",
                conditions=[],
                value=_subpiece("param_1", 8),
            )
        ],
    )
    analysis_narrow = create_mock_analysis(
        function_name="branch_unsigned_like",
        parameters=[
            {"name": "param_1", "data_type": "uint", "size": 4, "index": 0},
        ],
    )

    counterexample = {
        "param_1_1": 0x00000000FA56E326,
        "param_1_2": 0xFA56E326,
    }

    constraints = handler.detect_spurious_counterexample(
        counterexample,
        analysis_wide,
        analysis_narrow,
        is_mips64_1=True,
        is_mips64_2=False,
    )

    assert constraints == {}


def test_width_mismatch_detects_spurious_upper_bits_even_when_non_mips_side_is_wide():
    handler = MIPS64Handler(debug=True)

    analysis_wide_non_mips = create_mock_analysis(
        function_name="pointer_like_compare",
        parameters=[
            {"name": "param_1", "data_type": "long", "size": 8, "index": 0},
        ],
    )
    analysis_narrow_mips = create_mock_analysis(
        function_name="pointer_like_compare",
        parameters=[
            {"name": "param_1", "data_type": "uint", "size": 4, "index": 0},
        ],
        returns=[
            ReturnInfo(
                address="0x1000",
                conditions=[],
                value=_subpiece("param_1", 8),
            )
        ],
    )

    counterexample = {
        "param_1_1": 0x0008000000000000,
        "param_1_2": 0x00000000,
    }

    constraints = handler.detect_spurious_counterexample(
        counterexample,
        analysis_wide_non_mips,
        analysis_narrow_mips,
        is_mips64_1=False,
        is_mips64_2=True,
    )

    assert constraints == {"param_1_1": ("unsigned", 32)}
