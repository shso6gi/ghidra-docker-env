# -*- coding: utf-8 -*-
"""Pairwise 向け条件 rewrite の回帰テスト"""

import sys
from pathlib import Path
from unittest.mock import Mock


workspace_root = Path(__file__).parent.parent.parent.parent
if str(workspace_root) not in sys.path:
    sys.path.insert(0, str(workspace_root))

from scripts.function_tracer_pcode.equivalence.strategies.pairwise import PairwiseStrategy
from scripts.function_tracer_pcode.model import (
    Condition,
    Expression,
    ExpressionType,
    FunctionReturnAnalysis,
    ReturnInfo,
)
from scripts.function_tracer_pcode.transform.rewrite import (
    ExpressionRewriter,
    rewrite_analysis_returns,
)


def _param(name: str) -> Expression:
    return Expression(ExpressionType.PARAMETER, name=name, size=8)


def _const(value: int) -> Expression:
    return Expression(ExpressionType.CONSTANT, value=value, size=8)


def _binary(op: str, left: Expression, right: Expression) -> Expression:
    return Expression.binary_op(op, left, right)


def _signed_modulo_expansion(lhs: Expression, rhs: Expression) -> Expression:
    return _binary(
        "INT_SUB",
        lhs,
        _binary(
            "INT_MULT",
            _binary("INT_SDIV", lhs, rhs),
            rhs,
        ),
    )


def _signed_negative_condition(expr: Expression, negated: bool = False) -> Condition:
    return Condition(_binary("INT_SLESS", expr, _const(0)), negated=negated)


def _analysis(conditions) -> FunctionReturnAnalysis:
    return FunctionReturnAnalysis(
        function_name="ternary_modulo",
        entry_point="0x1000",
        parameters=[],
        returns=[
            ReturnInfo(
                address="0x1001",
                value=_const(1),
                conditions=conditions,
            )
        ],
        return_type="long",
    )


def test_rewrite_analysis_returns_normalizes_condition_expressions():
    rewriter = ExpressionRewriter(direction=ExpressionRewriter.NORMALIZE_TO_MODULO)
    analysis = _analysis(
        [_signed_negative_condition(_signed_modulo_expansion(_param("param_1"), _param("param_2")))]
    )

    rewritten, results = rewrite_analysis_returns(analysis, rewriter)

    condition_expr = rewritten.returns[0].conditions[0].expression

    assert results[0].was_rewritten is True
    assert any(rule.startswith("condition[0]:") for rule, _, _ in results[0].history)
    assert condition_expr.operator == "INT_SLESS"
    assert condition_expr.operands[0].operator == "INT_SREM"


def test_pairwise_strategy_skips_solver_for_rewritten_contradictory_conditions():
    rewriter = ExpressionRewriter(direction=ExpressionRewriter.NORMALIZE_TO_MODULO)
    analysis1 = _analysis(
        [_signed_negative_condition(_signed_modulo_expansion(_param("param_1"), _param("param_2")), negated=True)]
    )
    analysis2 = _analysis(
        [_signed_negative_condition(_binary("INT_SREM", _param("param_1"), _param("param_2")))]
    )

    rewritten1, _ = rewrite_analysis_returns(analysis1, rewriter)
    rewritten2, _ = rewrite_analysis_returns(analysis2, rewriter)

    formula_builder = Mock()
    formula_builder.build_base_context.return_value = {
        "header_lines": [],
        "params1": [],
        "params2": [],
        "extra_vars1": [],
        "extra_vars2": [],
    }
    solver_runner = Mock()
    solver_runner.timeout = 5

    strategy = PairwiseStrategy(formula_builder, solver_runner, debug=False)
    result = strategy.check(rewritten1, rewritten2)

    assert result.is_equivalent is True
    assert result.total_pairs == 1
    assert result.unsat_pairs == 1
    assert result.unknown_pairs == 0
    solver_runner.run_sequential.assert_not_called()

