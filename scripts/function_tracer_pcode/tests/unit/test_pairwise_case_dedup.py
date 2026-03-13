# -*- coding: utf-8 -*-
"""Pairwise 前の return case 統合に関する回帰テスト"""

import sys
from pathlib import Path


workspace_root = Path(__file__).parent.parent.parent.parent
if str(workspace_root) not in sys.path:
    sys.path.insert(0, str(workspace_root))

from scripts.function_tracer_pcode.equivalence.strategies.pairwise_query_builder import (
    build_normalized_inequality_query,
    build_pair_query,
    extract_return_cases,
)
from scripts.function_tracer_pcode.equivalence.strategies.pairwise_models import ReturnCase
from scripts.function_tracer_pcode.model import (
    Condition,
    Expression,
    ExpressionType,
    FunctionReturnAnalysis,
    ReturnInfo,
)


def _param(name: str) -> Expression:
    return Expression(ExpressionType.PARAMETER, name=name, size=8)


def _const(value: int) -> Expression:
    return Expression(ExpressionType.CONSTANT, value=value, size=8)


def _neg(expr: Expression) -> Expression:
    return Expression(
        ExpressionType.UNARY_OP,
        operator="INT_2COMP",
        operands=[expr],
        size=8,
    )


def _cond(operator: str, left: Expression, right: Expression, negated: bool = False) -> Condition:
    return Condition(
        Expression(
            ExpressionType.BINARY_OP,
            operator=operator,
            operands=[left, right],
            size=1,
        ),
        negated=negated,
    )


def _analysis(returns) -> FunctionReturnAnalysis:
    return FunctionReturnAnalysis(
        function_name="f",
        entry_point="0x1000",
        parameters=[],
        returns=returns,
        return_type="long",
    )


def test_extract_return_cases_deduplicates_same_condition_set():
    cond_eq_zero = _cond("INT_EQUAL", _param("param_1"), _const(0))
    cond_nonzero = _cond("INT_NOTEQUAL", _param("param_2"), _const(0))

    analysis = _analysis(
        [
            ReturnInfo(
                address="0x1001",
                value=_param("param_1"),
                conditions=[cond_eq_zero, cond_nonzero, cond_eq_zero],
            ),
            ReturnInfo(
                address="0x1002",
                value=_param("param_1"),
                conditions=[cond_nonzero, cond_eq_zero],
            ),
        ]
    )

    cases = extract_return_cases(analysis)

    assert len(cases) == 1
    assert cases[0].source_indices == [0, 1]
    assert len(cases[0].conditions) == 2


def test_extract_return_cases_deduplicates_after_safe_value_normalization():
    analysis = _analysis(
        [
            ReturnInfo(
                address="0x1001",
                value=_param("param_1"),
                conditions=[],
            ),
            ReturnInfo(
                address="0x1002",
                value=_neg(_neg(_param("param_1"))),
                conditions=[],
            ),
        ]
    )

    cases = extract_return_cases(analysis)

    assert len(cases) == 1
    assert cases[0].source_indices == [0, 1]
    assert cases[0].value_expr.to_smt() == _param("param_1").to_smt()


def test_extract_return_cases_keeps_distinct_conditions_separate():
    analysis = _analysis(
        [
            ReturnInfo(
                address="0x1001",
                value=_param("param_1"),
                conditions=[_cond("INT_EQUAL", _param("param_1"), _const(0))],
            ),
            ReturnInfo(
                address="0x1002",
                value=_param("param_1"),
                conditions=[_cond("INT_NOTEQUAL", _param("param_1"), _const(0))],
            ),
        ]
    )

    cases = extract_return_cases(analysis)

    assert len(cases) == 2
    assert cases[0].source_indices == [0]
    assert cases[1].source_indices == [1]


def test_build_pair_query_coerces_case_values_to_return_width():
    case1 = ReturnCase(
        index=0,
        conditions=[],
        value_expr=Expression(ExpressionType.PARAMETER, name="param_1", size=8),
        return_info=ReturnInfo(address="0x1001", value=Expression(ExpressionType.PARAMETER, name="param_1", size=8)),
        return_type="ulong",
    )
    case2 = ReturnCase(
        index=1,
        conditions=[],
        value_expr=Expression(ExpressionType.CONSTANT, value=2, size=4),
        return_info=ReturnInfo(address="0x1002", value=Expression(ExpressionType.CONSTANT, value=2, size=4)),
        return_type="ulong",
    )

    query = build_pair_query(
        {"header_lines": [], "return_size1": 64, "return_size2": 64},
        case1,
        case2,
        lambda text: text,
        lambda text: text,
        "(0,1)",
    )

    assert "(assert (not (= param_1 ((_ zero_extend 32) (_ bv2 32)))))" in query


def test_build_normalized_inequality_query_coerces_normalized_values_to_return_width():
    case1 = ReturnCase(
        index=0,
        conditions=[],
        value_expr=Expression(ExpressionType.PARAMETER, name="param_1", size=8),
        return_info=ReturnInfo(address="0x1001", value=Expression(ExpressionType.PARAMETER, name="param_1", size=8)),
        return_type="ulong",
    )
    case2 = ReturnCase(
        index=1,
        conditions=[],
        value_expr=Expression(ExpressionType.CONSTANT, value=2, size=4),
        return_info=ReturnInfo(address="0x1002", value=Expression(ExpressionType.CONSTANT, value=2, size=4)),
        return_type="ulong",
    )

    norm_expr = Expression(ExpressionType.CONSTANT, value=2, size=4)
    query = build_normalized_inequality_query(
        {"header_lines": [], "return_size1": 64, "return_size2": 64},
        case1,
        case2,
        lambda text: text,
        lambda text: text,
        norm_expr,
        norm_expr,
        "(_ bv2 32)",
        "(_ bv2 32)",
        "(0,1)",
    )

    assert "(assert (not (= ((_ zero_extend 32) (_ bv2 32)) ((_ zero_extend 32) (_ bv2 32)))))" in query


def test_build_pair_query_sign_extends_ambiguous_negative_constant_with_signed_evidence():
    signed_case = ReturnCase(
        index=0,
        conditions=[
            Condition(
                Expression(
                    ExpressionType.BINARY_OP,
                    operator="INT_SLESS",
                    operands=[
                        Expression(ExpressionType.PARAMETER, name="param_1", size=8),
                        Expression(ExpressionType.CONSTANT, value=-100, size=8),
                    ],
                    size=1,
                )
            )
        ],
        value_expr=Expression(ExpressionType.CONSTANT, value=0xFFFFFFFD, size=8),
        return_info=ReturnInfo(address="0x1003", value=Expression(ExpressionType.CONSTANT, value=0xFFFFFFFD, size=8)),
        return_type="undefined8",
    )
    other_case = ReturnCase(
        index=1,
        conditions=[],
        value_expr=Expression(ExpressionType.CONSTANT, value=0xFFFFFFFD, size=8),
        return_info=ReturnInfo(address="0x1004", value=Expression(ExpressionType.CONSTANT, value=0xFFFFFFFD, size=8)),
        return_type="undefined8",
    )

    query = build_pair_query(
        {"header_lines": [], "return_size1": 64, "return_size2": 64},
        signed_case,
        other_case,
        lambda text: text,
        lambda text: text,
        "(0,1)",
    )

    assert "(_ bv18446744073709551613 64)" in query
