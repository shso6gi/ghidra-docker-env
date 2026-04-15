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
from scripts.function_tracer_pcode.analysis.effect_summary import (
    CanonicalLocation,
    EffectSummary,
    StoreEffect,
    post_state_read_expression_for_location,
)
from scripts.function_tracer_pcode.analysis.analyzer import ReturnAnalyzer
from scripts.function_tracer_pcode.model import (
    Condition,
    Expression,
    ExpressionType,
    FunctionReturnAnalysis,
    LocationBaseRef,
    ReturnInfo,
)
from conftest import resolve_mock_data_type


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


def _bool_or(left: Condition, right: Condition, negated: bool = False) -> Condition:
    return Condition(
        Expression(
            ExpressionType.BINARY_OP,
            operator="BOOL_OR",
            operands=[left.expression, right.expression],
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


def test_extract_return_cases_skips_contradictory_condition_regions():
    analysis = _analysis(
        [
            ReturnInfo(
                address="0x1001",
                value=_param("param_1"),
                conditions=[
                    _cond("INT_EQUAL", _param("param_1"), _const(0)),
                    _cond("INT_NOTEQUAL", _param("param_1"), _const(0)),
                ],
            ),
            ReturnInfo(
                address="0x1002",
                value=_const(7),
                conditions=[_cond("INT_NOTEQUAL", _param("param_1"), _const(0))],
            ),
        ]
    )

    cases = extract_return_cases(analysis)

    assert len(cases) == 1
    assert cases[0].value_expr.to_smt() == _const(7).to_smt()


def test_extract_return_cases_prunes_impossible_or_region():
    cond_a = _cond("INT_EQUAL", _param("param_1"), _const(0))
    cond_b = _cond("INT_EQUAL", _param("param_2"), _const(0))

    analysis = _analysis(
        [
            ReturnInfo(
                address="0x1001",
                value=_param("param_1"),
                conditions=[_bool_or(cond_a, cond_b), cond_a.negate(), cond_b.negate()],
            ),
            ReturnInfo(
                address="0x1002",
                value=_const(7),
                conditions=[_bool_or(cond_a, cond_b)],
            ),
        ]
    )

    cases = extract_return_cases(analysis)

    assert len(cases) == 1
    assert cases[0].value_expr.to_smt() == _const(7).to_smt()


def test_return_case_value_smt_lowers_symbolic_post_state_reads_with_effect_summary():
    trace = Expression(ExpressionType.PARAMETER, name="trace", value=0, size=8)
    start = Expression(ExpressionType.PARAMETER, name="start", value=1, size=4)
    limit = Expression(ExpressionType.PARAMETER, name="limit", value=2, size=4)

    trace_nonnull = _cond("INT_NOTEQUAL", trace, _const(0))
    loop_active = _cond("INT_SLESS", start, limit)
    final_iter = _cond("INT_EQUAL", limit, Expression.binary_op("INT_ADD", start, _const(1)))
    odd_iteration = _cond(
        "INT_NOTEQUAL",
        Expression.binary_op("INT_AND", start, _const(1)),
        _const(0),
    )
    even_iteration = odd_iteration.negate()

    params = [
        {"name": "trace", "index": 0, "size": 8},
        {"name": "start", "index": 1, "size": 4},
        {"name": "limit", "index": 2, "size": 4},
    ]
    steps_addr = Expression.binary_op("INT_ADD", trace, _const(4))
    value_expr = Expression.binary_op(
        "INT_ADD",
        post_state_read_expression_for_location(
            CanonicalLocation(base_ref=LocationBaseRef.parameter("trace", index=0), offset=4, size=4),
            params,
            symbolic=True,
        ),
        post_state_read_expression_for_location(
            CanonicalLocation(base_ref=LocationBaseRef.parameter("trace", index=0), offset=0, size=4),
            params,
            symbolic=True,
        ),
    )
    effects = [
        StoreEffect(
            location=CanonicalLocation(base_ref=LocationBaseRef.parameter("trace", index=0), offset=0, size=4),
            value=Expression.binary_op("INT_ADD", Expression.memory(trace, size=4), _neg(start)),
            conditions=[trace_nonnull, loop_active, odd_iteration, final_iter],
            order_key=5,
        ),
        StoreEffect(
            location=CanonicalLocation(base_ref=LocationBaseRef.parameter("trace", index=0), offset=0, size=4),
            value=Expression.binary_op("INT_ADD", Expression.memory(trace, size=4), start),
            conditions=[trace_nonnull, loop_active, even_iteration, final_iter],
            order_key=5,
        ),
        StoreEffect(
            location=CanonicalLocation(base_ref=LocationBaseRef.parameter("trace", index=0), offset=4, size=4),
            value=Expression.binary_op("INT_ADD", Expression.memory(steps_addr, size=4), _const(1)),
            conditions=[trace_nonnull, loop_active, final_iter],
            order_key=6,
        ),
    ]
    analysis = FunctionReturnAnalysis(
        function_name="f",
        entry_point="0x1000",
        parameters=params,
        returns=[
            ReturnInfo(
                address="0x1004",
                value=value_expr,
                conditions=[trace_nonnull, loop_active, final_iter],
            )
        ],
        return_type="int",
        effect_summary=EffectSummary(
            parameter_names=["trace", "start", "limit"],
            effects=effects,
        ),
    )

    cases = extract_return_cases(analysis)

    assert len(cases) == 1
    smt = cases[0].get_value_smt(lambda expr: expr)
    assert "__locread__" not in smt
    assert "ite" in smt
    assert "bvneg start" in smt


def test_return_case_value_smt_lowers_nested_symbolic_post_state_reads_with_effect_summary():
    trace = Expression(ExpressionType.PARAMETER, name="trace", size=8)
    start = Expression(ExpressionType.PARAMETER, name="start", size=4)
    limit = Expression(ExpressionType.PARAMETER, name="limit", size=4)

    trace_nonnull = _cond("INT_NOTEQUAL", trace, _const(0))
    loop_active = _cond("INT_SLESS", start, limit)
    final_iter = _cond("INT_EQUAL", limit, Expression.binary_op("INT_ADD", start, _const(1)))
    odd_iteration = _cond(
        "INT_NOTEQUAL",
        Expression.binary_op("INT_AND", start, _const(1)),
        _const(0),
    )
    even_iteration = odd_iteration.negate()

    params = [
        {"name": "trace", "index": 0, "size": 8},
        {"name": "start", "index": 1, "size": 4},
        {"name": "limit", "index": 2, "size": 4},
    ]
    steps_addr = Expression.binary_op("INT_ADD", trace, _const(4))
    value_expr = Expression.binary_op(
        "INT_ADD",
        post_state_read_expression_for_location(
            CanonicalLocation("trace", 0, 4),
            params,
            symbolic=True,
        ),
        Expression.binary_op(
            "INT_SUB",
            Expression.binary_op(
                "INT_ADD",
                limit,
                post_state_read_expression_for_location(
                    CanonicalLocation("trace", 4, 4),
                    params,
                    symbolic=True,
                ),
            ),
            start,
        ),
    )
    effects = [
        StoreEffect(
            location=CanonicalLocation("trace", 0, 4),
            value=Expression.binary_op("INT_ADD", Expression.memory(trace, size=4), _neg(start)),
            conditions=[trace_nonnull, loop_active, odd_iteration, final_iter],
            order_key=5,
        ),
        StoreEffect(
            location=CanonicalLocation("trace", 0, 4),
            value=Expression.binary_op("INT_ADD", Expression.memory(trace, size=4), start),
            conditions=[trace_nonnull, loop_active, even_iteration, final_iter],
            order_key=5,
        ),
        StoreEffect(
            location=CanonicalLocation("trace", 4, 4),
            value=Expression.binary_op(
                "INT_SUB",
                Expression.binary_op("INT_ADD", limit, Expression.memory(steps_addr, size=4)),
                start,
            ),
            conditions=[trace_nonnull, loop_active, final_iter],
            order_key=6,
        ),
    ]
    analysis = FunctionReturnAnalysis(
        function_name="f",
        entry_point="0x1000",
        parameters=params,
        returns=[
            ReturnInfo(
                address="0x1004",
                value=value_expr,
                conditions=[trace_nonnull, loop_active, odd_iteration, final_iter],
            )
        ],
        return_type="int",
        effect_summary=EffectSummary(
            parameter_names=["trace", "start", "limit"],
            effects=effects,
        ),
    )

    cases = extract_return_cases(analysis)

    assert len(cases) == 1
    smt = cases[0].get_value_smt(lambda expr: expr)
    assert "__locread__" not in smt
    assert "select mem32 trace" in smt
    assert "select mem32 (bvadd trace (_ bv4 64))" in smt


def test_return_case_value_smt_does_not_replay_explicit_prestate_expression_again():
    trace = Expression(ExpressionType.PARAMETER, name="param_1", size=8)
    start = Expression(ExpressionType.PARAMETER, name="param_2", size=4)
    limit = Expression(ExpressionType.PARAMETER, name="param_3", size=4)

    trace_nonnull = _cond("INT_NOTEQUAL", trace, _const(0))
    loop_active = _cond("INT_SLESS", start, limit)
    final_iter = _cond("INT_EQUAL", limit, Expression.binary_op("INT_ADD", start, _const(1)))
    odd_iteration = _cond(
        "INT_NOTEQUAL",
        Expression.binary_op("INT_AND", start, _const(1)),
        _const(0),
    )

    params = [
        {"name": "param_1", "index": 0, "size": 8},
        {"name": "param_2", "index": 1, "size": 4},
        {"name": "param_3", "index": 2, "size": 4},
    ]
    steps_addr = Expression.binary_op("INT_ADD", trace, _const(4))
    explicit_expr = Expression.binary_op(
        "INT_ADD",
        Expression.binary_op("INT_ADD", Expression.memory(steps_addr, size=4), _const(1)),
        Expression.binary_op("INT_ADD", _neg(start), Expression.memory(trace, size=4)),
    )
    effects = [
        StoreEffect(
            location=CanonicalLocation("param_1", 0, 4),
            value=Expression.binary_op("INT_ADD", Expression.memory(trace, size=4), _neg(start)),
            conditions=[trace_nonnull, loop_active, odd_iteration, final_iter],
            order_key=5,
        ),
        StoreEffect(
            location=CanonicalLocation("param_1", 4, 4),
            value=Expression.binary_op("INT_ADD", Expression.memory(steps_addr, size=4), _const(1)),
            conditions=[trace_nonnull, loop_active, final_iter],
            order_key=6,
        ),
    ]
    analysis = FunctionReturnAnalysis(
        function_name="f",
        entry_point="0x1000",
        parameters=params,
        returns=[
            ReturnInfo(
                address="0x1004",
                value=explicit_expr,
                conditions=[trace_nonnull, loop_active, odd_iteration, final_iter],
            )
        ],
        return_type="int",
        effect_summary=EffectSummary(
            parameter_names=["param_1", "param_2", "param_3"],
            effects=effects,
        ),
    )

    cases = extract_return_cases(analysis)

    assert len(cases) == 1
    smt = cases[0].get_value_smt(lambda expr: expr)
    assert "__locread__" not in smt
    assert smt.count("(bvneg param_2)") == 1
    assert smt.count("(_ bv1 32)") == 1


def test_return_analyzer_does_not_collapse_complementary_symbolic_post_state_cases():
    params = [{"name": "trace", "index": 0, "size": 8}]
    symbolic_value = post_state_read_expression_for_location(
        CanonicalLocation("trace", 0, 4),
        params,
        symbolic=True,
    )
    assert symbolic_value is not None

    zero = _cond("INT_EQUAL", _param("param_1"), _const(0))
    nonzero = zero.negate()
    infos = [
        ReturnInfo(
            address="0x1001",
            value=symbolic_value,
            conditions=[zero],
        ),
        ReturnInfo(
            address="0x1001",
            value=symbolic_value,
            conditions=[nonzero],
        ),
    ]

    merged = ReturnAnalyzer(program=None, debug=False)._merge_equivalent_return_infos(infos)

    assert len(merged) == 2


def test_build_pair_query_coerces_case_values_to_return_width():
    case1 = ReturnCase(
        index=0,
        conditions=[],
        value_expr=Expression(ExpressionType.PARAMETER, name="param_1", size=8),
        return_info=ReturnInfo(address="0x1001", value=Expression(ExpressionType.PARAMETER, name="param_1", size=8)),
        return_type="ulong",
        return_type_obj=resolve_mock_data_type("ulong"),
    )
    case2 = ReturnCase(
        index=1,
        conditions=[],
        value_expr=Expression(ExpressionType.CONSTANT, value=2, size=4),
        return_info=ReturnInfo(address="0x1002", value=Expression(ExpressionType.CONSTANT, value=2, size=4)),
        return_type="ulong",
        return_type_obj=resolve_mock_data_type("ulong"),
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
        return_type_obj=resolve_mock_data_type("ulong"),
    )
    case2 = ReturnCase(
        index=1,
        conditions=[],
        value_expr=Expression(ExpressionType.CONSTANT, value=2, size=4),
        return_info=ReturnInfo(address="0x1002", value=Expression(ExpressionType.CONSTANT, value=2, size=4)),
        return_type="ulong",
        return_type_obj=resolve_mock_data_type("ulong"),
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


def test_build_pair_query_extracts_rendered_wide_value_back_to_declared_return_width():
    case1 = ReturnCase(
        index=0,
        conditions=[],
        value_expr=Expression(ExpressionType.PARAMETER, name="param_1", size=4),
        return_info=ReturnInfo(address="0x1001", value=Expression(ExpressionType.PARAMETER, name="param_1", size=4)),
        return_type="int",
    )
    wide_add = Expression(
        ExpressionType.BINARY_OP,
        operator="INT_ADD",
        operands=[
            Expression(ExpressionType.PARAMETER, name="param_1", size=4),
            Expression(ExpressionType.CONSTANT, value=7, size=8),
        ],
        size=4,
    )
    case2 = ReturnCase(
        index=1,
        conditions=[],
        value_expr=wide_add,
        return_info=ReturnInfo(address="0x1002", value=wide_add),
        return_type="int",
    )

    query = build_pair_query(
        {"header_lines": [], "return_size1": 32, "return_size2": 32},
        case1,
        case2,
        lambda text: text,
        lambda text: text,
        "(0,1)",
    )

    assert "(assert (not (= param_1 (bvadd param_1 (_ bv7 32)))))" in query


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


def test_nested_zero_extend_uses_rendered_operand_width_without_double_extension():
    param = Expression(ExpressionType.PARAMETER, name="param_1", size=4)
    wide_seven = Expression(ExpressionType.CONSTANT, value=7, size=8)
    inner_add = Expression(
        ExpressionType.BINARY_OP,
        operator="INT_ADD",
        operands=[param, wide_seven],
        size=4,
    )
    inner_zext = Expression(
        ExpressionType.UNARY_OP,
        operator="INT_ZEXT",
        operands=[inner_add],
        size=8,
    )
    mult_expr = Expression(
        ExpressionType.BINARY_OP,
        operator="INT_MULT",
        operands=[
            Expression(ExpressionType.CONSTANT, value=2, size=8),
            inner_zext,
        ],
        size=4,
    )
    outer_zext = Expression(
        ExpressionType.UNARY_OP,
        operator="INT_ZEXT",
        operands=[mult_expr],
        size=8,
    )

    smt = outer_zext.to_smt()

    assert "((_ zero_extend 32) (bvmul" not in smt
    assert smt == "(bvmul (_ bv2 64) ((_ zero_extend 32) (bvadd param_1 (_ bv7 32))))"
