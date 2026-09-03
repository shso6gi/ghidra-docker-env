# -*- coding: utf-8 -*-
"""divide_round 向け object-centric 条件保持の回帰テスト"""

import sys
from pathlib import Path


workspace_root = Path(__file__).parent.parent.parent.parent
if str(workspace_root) not in sys.path:
    sys.path.insert(0, str(workspace_root))

from scripts.function_tracer_pcode.proof.strategies.pairwise import PairwiseStrategy
from scripts.function_tracer_pcode.proof.strategies.pairwise_models import ReturnCase
from scripts.function_tracer_pcode.proof.strategies.pairwise_query_builder import (
    extract_return_cases,
)
from scripts.function_tracer_pcode.core import (
    Condition,
    Expression,
    ExpressionType,
    FunctionReturnAnalysis,
    ReturnInfo,
)


def _param(name: str) -> Expression:
    parameter_index = {"param_1": 0, "param_2": 1}.get(name, -1)
    return Expression.parameter(name, index=parameter_index, size=8)


def _const(value: int) -> Expression:
    return Expression(ExpressionType.CONSTANT, value=value, size=8)


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
        function_name="divide_round",
        entry_point="0x1000",
        parameters=[
            {"name": "param_1", "index": 0, "size": 8},
            {"name": "param_2", "index": 1, "size": 8},
        ],
        returns=returns,
        return_type="long",
    )


def test_extract_return_cases_preserves_mutually_implied_signed_bounds_in_query_basis():
    nonzero_b = _cond("INT_NOTEQUAL", _param("param_2"), _const(0))
    nonnegative_a = _cond("INT_SLESSEQUAL", _const(0), _param("param_1"))
    negative_b = _cond("INT_SLESS", _param("param_2"), _const(1))
    positive_a = _cond("INT_SLESS", _const(-1), _param("param_1"))

    analysis = _analysis(
        [
            ReturnInfo(
                address="0x1001",
                value=Expression.binary_op("INT_SDIV", _param("param_1"), _param("param_2")),
                conditions=[nonzero_b, nonnegative_a, negative_b, positive_a, nonzero_b],
            )
        ]
    )

    cases = extract_return_cases(analysis)

    assert len(cases) == 1
    assert len(cases[0].conditions) == 4
    assert any(
        cond.expression.operator == "INT_SLESSEQUAL"
        and cond.expression.operands[0].value == 0
        and cond.expression.operands[1].name == "param_1"
        for cond in cases[0].conditions
    )
    assert any(
        cond.expression.operator == "INT_SLESS"
        and cond.expression.operands[0].value == -1
        and cond.expression.operands[1].name == "param_1"
        for cond in cases[0].conditions
    )


def test_pairwise_contradiction_precheck_uses_object_centric_condition_basis():
    add_branch = ReturnCase(
        index=0,
        conditions=[
            _cond("INT_SLESS", _param("param_1"), _const(0)),
            _cond("INT_SLESSEQUAL", _param("param_2"), _const(-1)),
        ],
        value_expr=Expression.binary_op("INT_ADD", _param("param_1"), _param("param_2")),
        return_info=ReturnInfo(address="0x1001", value=_param("param_1")),
    )
    subtract_branch = extract_return_cases(
        _analysis(
            [
                ReturnInfo(
                    address="0x1002",
                    value=Expression.binary_op("INT_SUB", _param("param_1"), _param("param_2")),
                    conditions=[
                        _cond("INT_NOTEQUAL", _param("param_2"), _const(0)),
                        _cond("INT_SLESSEQUAL", _const(0), _param("param_1")),
                        _cond("INT_SLESS", _param("param_2"), _const(1)),
                        _cond("INT_SLESS", _const(-1), _param("param_1")),
                    ],
                )
            ]
        )
    )[0]

    strategy = PairwiseStrategy(formula_builder=None, solver_runner=None, debug=False)

    assert strategy._cases_are_contradictory(add_branch, subtract_branch) is True
