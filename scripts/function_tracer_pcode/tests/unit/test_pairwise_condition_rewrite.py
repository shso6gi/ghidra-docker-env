# -*- coding: utf-8 -*-
"""Pairwise 向け条件 rewrite の回帰テスト"""

import sys
from pathlib import Path
from unittest.mock import Mock


workspace_root = Path(__file__).parent.parent.parent.parent
if str(workspace_root) not in sys.path:
    sys.path.insert(0, str(workspace_root))

from scripts.function_tracer_pcode.equivalence.strategies.pairwise import PairwiseStrategy
from scripts.function_tracer_pcode.equivalence.formula.builder import FormulaBuilder
from scripts.function_tracer_pcode.equivalence.formula.symbol_replace import build_symbol_replacer
from scripts.function_tracer_pcode.equivalence.strategies.pairwise_models import ReturnCase
from scripts.function_tracer_pcode.model import (
    Condition,
    Expression,
    ExpressionType,
    FunctionReturnAnalysis,
    ReturnInfo,
)
from scripts.function_tracer_pcode.analysis.condition.simplifier import ConditionSimplifier
from scripts.function_tracer_pcode.analysis.effect_summary import (
    CanonicalLocation,
    EffectSummary,
    StoreEffect,
)
from scripts.function_tracer_pcode.transform.rewrite import (
    ExpressionRewriter,
    rewrite_analysis_returns,
)
from scripts.function_tracer_pcode.smt import ParallelResult, SolverResult, SolverStatus


def _param(name: str) -> Expression:
    return Expression(ExpressionType.PARAMETER, name=name, size=8)


def _const(value: int) -> Expression:
    return Expression(ExpressionType.CONSTANT, value=value, size=8)


def _binary(op: str, left: Expression, right: Expression) -> Expression:
    return Expression.binary_op(op, left, right)


def _masked_param(name: str) -> Expression:
    return _binary("INT_AND", _param(name), _const(0xFFFFFFFF))


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


def test_pairwise_strategy_reduces_phi_unknown_under_pair_conditions():
    selector = Condition(_binary("INT_SLESS", _const(0), _param("param_1")))
    other_selector = selector.negate()
    phi_value = Expression.phi(
        [
            (selector, _const(1)),
            (other_selector, Expression.unknown("phi_circular")),
        ]
    )
    phi_value.size = 8

    analysis1 = FunctionReturnAnalysis(
        function_name="f1",
        entry_point="0x1000",
        parameters=[],
        returns=[
            ReturnInfo(
                address="0x1001",
                value=phi_value,
                conditions=[selector],
            )
        ],
        return_type="long",
    )
    analysis2 = FunctionReturnAnalysis(
        function_name="f2",
        entry_point="0x2000",
        parameters=[],
        returns=[
            ReturnInfo(
                address="0x2001",
                value=_const(1),
                conditions=[selector],
            )
        ],
        return_type="long",
    )

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

    def _run_sequential(query: str):
        if "Single Case Reachability" in query:
            return ParallelResult(results=[SolverResult("mock", SolverStatus.SAT, elapsed_time=0.01)])
        if "; Value inequality" in query:
            return ParallelResult(results=[SolverResult("mock", SolverStatus.UNSAT, elapsed_time=0.01)])
        return ParallelResult(results=[SolverResult("mock", SolverStatus.SAT, elapsed_time=0.01)])

    solver_runner.run_sequential.side_effect = _run_sequential

    strategy = PairwiseStrategy(formula_builder, solver_runner, debug=False)
    result = strategy.check(analysis1, analysis2)

    assert result.is_equivalent is True
    assert result.total_pairs == 1
    assert result.unsat_pairs == 1
    assert result.unknown_pairs == 0


def test_pairwise_unresolved_check_avoids_condition_simplifier_recursion(monkeypatch):
    analysis1 = FunctionReturnAnalysis(
        function_name="branch_sign_bucket_left",
        entry_point="0x1000",
        parameters=[{"name": "param_1", "size": 4, "data_type": "int", "index": 0}],
        returns=[
            ReturnInfo(
                address="0x1001",
                value=_const(2),
                conditions=[
                    Condition(_binary("INT_EQUAL", _param("param_1"), _const(0)), negated=True),
                    Condition(_binary("INT_LESS", _param("param_1"), _const(101))),
                    Condition(_binary("INT_SLESS", _param("param_1"), _const(0)), negated=True),
                ],
            )
        ],
        return_type="int",
    )
    analysis2 = FunctionReturnAnalysis(
        function_name="branch_sign_bucket_right",
        entry_point="0x2000",
        parameters=[{"name": "param_1", "size": 4, "data_type": "int", "index": 0}],
        returns=[
            ReturnInfo(
                address="0x2001",
                value=_const(2),
                conditions=[
                    Condition(_binary("INT_NOTEQUAL", _masked_param("param_1"), _const(0))),
                    Condition(_binary("INT_LESS", _const(100), _masked_param("param_1")), negated=True),
                    Condition(_binary("INT_LESS", _const(0xFFFFFFFF), _masked_param("param_1"))),
                ],
            )
        ],
        return_type="int",
    )

    formula_builder = FormulaBuilder()
    base_ctx = formula_builder.build_base_context(analysis1, analysis2)
    replace_fn1 = build_symbol_replacer(base_ctx["params1"], base_ctx.get("extra_vars1", []))
    replace_fn2 = build_symbol_replacer(base_ctx["params2"], base_ctx.get("extra_vars2", []))

    strategy = PairwiseStrategy(formula_builder, Mock(), debug=False)
    case1 = ReturnCase(
        index=0,
        conditions=list(analysis1.returns[0].conditions),
        value_expr=analysis1.returns[0].value,
        return_info=analysis1.returns[0],
        return_type="int",
    )
    case2 = ReturnCase(
        index=0,
        conditions=list(analysis2.returns[0].conditions),
        value_expr=analysis2.returns[0].value,
        return_info=analysis2.returns[0],
        return_type="int",
    )

    def _unexpected_simplify(*_args, **_kwargs):
        raise AssertionError("ConditionSimplifier.simplify_conditions should not be used here")

    monkeypatch.setattr(ConditionSimplifier, "simplify_conditions", _unexpected_simplify)

    assert (
        strategy._case_contains_unresolved_expression(
            case1,
            case2.conditions,
            own_render_fn=replace_fn1,
            extra_render_fn=replace_fn2,
            base_ctx=base_ctx,
            query_label="mixed-guard",
        )
        is False
    )


def test_pairwise_strategy_completes_for_mixed_signed_guard_pair():
    analysis1 = FunctionReturnAnalysis(
        function_name="branch_sign_bucket_left",
        entry_point="0x1000",
        parameters=[{"name": "param_1", "size": 4, "data_type": "int", "index": 0}],
        returns=[
            ReturnInfo(
                address="0x1001",
                value=_const(2),
                conditions=[
                    Condition(_binary("INT_EQUAL", _param("param_1"), _const(0)), negated=True),
                    Condition(_binary("INT_LESS", _param("param_1"), _const(101))),
                    Condition(_binary("INT_SLESS", _param("param_1"), _const(0)), negated=True),
                ],
            )
        ],
        return_type="int",
    )
    analysis2 = FunctionReturnAnalysis(
        function_name="branch_sign_bucket_right",
        entry_point="0x2000",
        parameters=[{"name": "param_1", "size": 4, "data_type": "int", "index": 0}],
        returns=[
            ReturnInfo(
                address="0x2001",
                value=_const(2),
                conditions=[
                    Condition(_binary("INT_NOTEQUAL", _masked_param("param_1"), _const(0))),
                    Condition(_binary("INT_LESS", _const(100), _masked_param("param_1")), negated=True),
                    Condition(_binary("INT_SLESS", _masked_param("param_1"), _const(0)), negated=True),
                ],
            )
        ],
        return_type="int",
    )

    solver_runner = Mock()
    solver_runner.timeout = 5

    def _run_sequential(query: str, timeout=None):
        if "Return coverage gap query" in query:
            return ParallelResult(results=[SolverResult("mock", SolverStatus.UNSAT, elapsed_time=0.01)])
        if "; Value inequality" in query:
            return ParallelResult(results=[SolverResult("mock", SolverStatus.UNSAT, elapsed_time=0.01)])
        return ParallelResult(results=[SolverResult("mock", SolverStatus.SAT, elapsed_time=0.01)])

    solver_runner.run_sequential.side_effect = _run_sequential

    strategy = PairwiseStrategy(FormulaBuilder(), solver_runner, debug=False)
    result = strategy.check(analysis1, analysis2)

    assert result.is_equivalent is True
    assert result.total_pairs == 1
    assert result.unsat_pairs == 1
    assert result.unknown_pairs == 0
