# -*- coding: utf-8 -*-
"""branch_sign_bucket 系の object-centric return-region 回帰テスト"""

from scripts.function_tracer_pcode.analysis.analyzer import ReturnAnalyzer
from scripts.function_tracer_pcode.analysis.condition.simplifier import ConditionSimplifier
from scripts.function_tracer_pcode.model import Condition, Expression, ExpressionType, ReturnInfo

from conftest import create_mock_analysis


def _param(name: str, size: int = 4) -> Expression:
    return Expression(ExpressionType.PARAMETER, name=name, size=size)


def _const(value: int, size: int = 4) -> Expression:
    return Expression(ExpressionType.CONSTANT, value=value, size=size)


def _cond(operator: str, left: Expression, right: Expression, *, negated: bool = False) -> Condition:
    return Condition(
        Expression(
            ExpressionType.BINARY_OP,
            operator=operator,
            operands=[left, right],
            size=1,
        ),
        negated=negated,
    )


def _bool_to_int(expr: Expression, size: int = 4) -> Expression:
    return Expression(
        ExpressionType.UNARY_OP,
        operator="INT_ZEXT",
        operands=[expr],
        size=size,
    )


def _branch_sign_bucket_tail_value(compare_operator: str = "INT_SLESS") -> Expression:
    selector = Expression(
        ExpressionType.BINARY_OP,
        operator=compare_operator,
        operands=[_const(100), _param("value")],
        size=1,
    )
    return Expression(
        ExpressionType.BINARY_OP,
        operator="INT_OR",
        operands=[_bool_to_int(selector), _const(2)],
        size=4,
    )


def test_condition_simplifier_reduces_signed_compare_to_false_under_negative_range():
    value = _param("value")
    expr = Expression.binary_op("INT_SLESS", _const(100), value)
    conditions = [
        _cond("INT_SLESS", _const(-101), value),
        _cond("INT_SLESS", value, _const(0)),
    ]

    reduced = ConditionSimplifier.reduce_expression_under_conditions(expr, conditions)

    assert reduced.expr_type == ExpressionType.CONSTANT
    assert reduced.value == 0


def test_return_analyzer_splits_boolean_or_value_into_exclusive_value_cases():
    analyzer = ReturnAnalyzer(program=None, debug=False)
    conditions = [
        _cond("INT_SLESS", _const(-101), _param("value")),
        _cond("INT_NOTEQUAL", _param("value"), _const(0)),
    ]

    cases = analyzer._split_object_centric_return_case(
        _branch_sign_bucket_tail_value(),
        conditions,
    )

    assert len(cases) == 2
    assert {case_value.value for case_value, _case_conditions in cases} == {2, 3}

    left = ConditionSimplifier.build_constraint_set(cases[0][1])
    right = ConditionSimplifier.build_constraint_set(cases[1][1])
    assert left.overlaps_with(right.conditions) is False


def test_return_analyzer_exclusivizes_shadowed_branch_sign_bucket_regions():
    analyzer = ReturnAnalyzer(program=None, debug=False)
    negative_conditions = [
        _cond("INT_SLESS", _const(-101), _param("value")),
        _cond("INT_SLESS", _param("value"), _const(0)),
    ]
    merged_conditions = [
        _cond("INT_SLESS", _const(-101), _param("value")),
        _cond("INT_NOTEQUAL", _param("value"), _const(0)),
    ]

    split_tail_infos = [
        ReturnInfo(address="0x1008", value=value, conditions=conditions, branch_index=20 + index)
        for index, (value, conditions) in enumerate(
            analyzer._split_object_centric_return_case(
                _branch_sign_bucket_tail_value(),
                merged_conditions,
            )
        )
    ]

    exclusivized = analyzer._exclusivize_return_regions(
        [
            ReturnInfo(
                address="0x1004",
                value=_const(-2),
                conditions=negative_conditions,
                branch_index=10,
            ),
            *split_tail_infos,
        ]
    )

    assert len(exclusivized) == 3
    values = sorted(int(info.value.value) for info in exclusivized)
    assert values == [-2, 2, 3]

    negative_info = next(info for info in exclusivized if int(info.value.value) == -2)
    plus_two_info = next(info for info in exclusivized if int(info.value.value) == 2)
    plus_three_info = next(info for info in exclusivized if int(info.value.value) == 3)

    negative_region = ConditionSimplifier.build_constraint_set(negative_info.conditions)
    plus_two_region = ConditionSimplifier.build_constraint_set(plus_two_info.conditions)
    plus_three_region = ConditionSimplifier.build_constraint_set(plus_three_info.conditions)

    assert negative_region.overlaps_with(plus_two_region.conditions) is False
    assert negative_region.overlaps_with(plus_three_region.conditions) is False
    assert plus_two_region.overlaps_with(plus_three_region.conditions) is False


def test_return_analyzer_repairs_mixed_scalar_signedness_from_scalar_evidence():
    analyzer = ReturnAnalyzer(program=None, debug=False)
    analysis = create_mock_analysis(
        function_name="branch_sign_bucket",
        parameters=[
            {"name": "value", "data_type": "int", "size": 4, "index": 0},
        ],
        returns=[
            ReturnInfo(
                address="0x1004",
                value=_const(-2),
                conditions=[
                    _cond("INT_SLESS", _const(-101), _param("value")),
                    _cond("INT_SLESS", _param("value"), _const(0)),
                ],
                branch_index=10,
            ),
            ReturnInfo(
                address="0x1008",
                value=_branch_sign_bucket_tail_value(compare_operator="INT_LESS"),
                conditions=[
                    _cond("INT_SLESS", _const(-101), _param("value")),
                    _cond("INT_NOTEQUAL", _param("value"), _const(0)),
                ],
                branch_index=20,
            ),
        ],
    )

    analyzer._repair_mixed_scalar_signedness(analysis)

    repaired_value = analysis.returns[1].value
    assert repaired_value.operands[0].operator == "INT_ZEXT"
    assert repaired_value.operands[0].operands[0].operator == "INT_SLESS"
    assert "object_centric_scalar_signedness_repair" in analysis.analysis_notes
