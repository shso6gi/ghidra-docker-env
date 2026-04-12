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
from scripts.function_tracer_pcode.analysis.effect_summary import (
    CanonicalLocation,
    EffectSummary,
    StoreEffect,
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


def test_rewrite_analysis_returns_preserves_effect_summary_metadata():
    rewriter = ExpressionRewriter(direction=ExpressionRewriter.NORMALIZE_TO_MODULO)
    effect_summary = EffectSummary(
        parameter_names=["param_1"],
        effects=[
            StoreEffect(
                location=CanonicalLocation("param_1", 0, 4),
                value=_const(1),
                conditions=[],
                order_key=1,
            )
        ],
    )
    analysis = FunctionReturnAnalysis(
        function_name="f",
        entry_point="0x1000",
        parameters=[],
        returns=[
            ReturnInfo(
                address="0x1001",
                value=_signed_modulo_expansion(_param("param_1"), _param("param_2")),
                conditions=[],
            )
        ],
        return_type="long",
        unknown_event_count=3,
        unknown_event_reasons=["r1"],
        analysis_notes=["n1"],
        recovered_from_decompiler=True,
        incomplete_control_flow=True,
        deferred_calls={"placeholder": Mock()},
        effect_summary=effect_summary,
    )

    rewritten, _ = rewrite_analysis_returns(analysis, rewriter)

    assert rewritten.effect_summary is effect_summary
    assert rewritten.unknown_event_count == 3
    assert rewritten.unknown_event_reasons == ["r1"]
    assert rewritten.analysis_notes == ["n1"]
    assert rewritten.recovered_from_decompiler is True
    assert rewritten.incomplete_control_flow is True
    assert "placeholder" in rewritten.deferred_calls


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


def test_pairwise_strategy_marks_unresolved_cases_unknown_without_invoking_solver():
    analysis1 = FunctionReturnAnalysis(
        function_name="f1",
        entry_point="0x1000",
        parameters=[],
        returns=[
            ReturnInfo(
                address="0x1001",
                value=_const(1),
                conditions=[
                    Condition(
                        _binary("INT_SLESS", _param("param_1"), Expression.unknown("call_out_of_scope:callee")),
                        False,
                    )
                ],
            )
        ],
        return_type="long",
    )
    analysis2 = _analysis([])

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
    result = strategy.check(analysis1, analysis2)

    assert result.is_equivalent is None
    assert result.total_pairs == 1
    assert result.unknown_pairs == 1
    assert result.unsat_pairs == 0
    assert result.sat_pairs == 0
    solver_runner.run_sequential.assert_not_called()


def test_pairwise_strategy_treats_unsupported_smt_operator_as_unresolved():
    analysis1 = FunctionReturnAnalysis(
        function_name="f1",
        entry_point="0x1000",
        parameters=[],
        returns=[
            ReturnInfo(
                address="0x1001",
                value=_binary("INDIRECT", _const(0), _const(40)),
                conditions=[],
            )
        ],
        return_type="long",
    )
    analysis2 = _analysis([])

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
    result = strategy.check(analysis1, analysis2)

    assert result.is_equivalent is None
    assert result.total_pairs == 1
    assert result.unknown_pairs == 1
    solver_runner.run_sequential.assert_not_called()
