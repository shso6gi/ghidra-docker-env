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
from scripts.function_tracer_pcode.equivalence.formula.types import ParameterInfo
from scripts.function_tracer_pcode.equivalence.formula.symbol_replace import build_symbol_replacer
from scripts.function_tracer_pcode.equivalence.strategies.pairwise_models import ReturnCase
from scripts.function_tracer_pcode.model import (
    Condition,
    Expression,
    ExpressionType,
    FunctionReturnAnalysis,
    LocationBaseRef,
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
from scripts.function_tracer_pcode.smt import (
    ParallelResult, ParallelSolverRunner, SolverResult, SolverStatus,
)


def _solver_runner():
    runner = ParallelSolverRunner(timeout=5)
    runner.run_sequential = Mock(wraps=runner.run_sequential)
    return runner


def _param(name: str) -> Expression:
    return _sized_param(name, 8)


def _indexed_param(name: str, index: int) -> Expression:
    return _indexed_sized_param(name, index, 8)


def _indexed_sized_param(name: str, index: int, size: int) -> Expression:
    return Expression.parameter(
        name,
        index=index,
        size=size,
        runtime_ref=LocationBaseRef.parameter(name, index=index),
    )


def _const(value: int) -> Expression:
    return Expression(ExpressionType.CONSTANT, value=value, size=8)


def _binary(op: str, left: Expression, right: Expression) -> Expression:
    return Expression.binary_op(op, left, right)


def _sized_param(name: str, size: int) -> Expression:
    return Expression.parameter(name, index=-1, size=size, runtime_ref=None)


def _sized_const(value: int, size: int) -> Expression:
    return Expression(ExpressionType.CONSTANT, value=value, size=size)


def _masked_param(name: str) -> Expression:
    return _binary("INT_AND", _param(name), _const(0xFFFFFFFF))


def _indexed_masked_param(name: str, index: int) -> Expression:
    return _binary("INT_AND", _indexed_param(name, index), _const(0xFFFFFFFF))


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


def _missing_return_abi_facts():
    """Return the producer-issued schema-v1 envelope for unavailable ABI facts."""
    return {
        "schema_version": 1,
        "calling_convention": {
            "status": "MISSING",
            "value": None,
            "source": "pairwise_fixture",
        },
        "declared_or_effective_return_type": {
            "status": "MISSING",
            "value": None,
            "source": "pairwise_fixture",
        },
        "return_storage_descriptor": {
            "status": "MISSING",
            "value": None,
            "source": "pairwise_fixture",
        },
    }


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
        return_abi_facts=_missing_return_abi_facts(),
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


def test_summary_condition_equivalence_keeps_expression_width_semantic():
    cond32 = Condition(_binary("INT_SLESS", _sized_param("param_1", 4), _sized_const(0, 4)))
    cond64 = Condition(_binary("INT_SLESS", _sized_param("param_1", 8), _sized_const(0, 8)))
    ret32 = ReturnInfo(address="0x1001", value=_const(1), conditions=[cond32])
    ret64 = ReturnInfo(address="0x2001", value=_const(1), conditions=[cond64])
    case32 = ReturnCase(
        index=0,
        conditions=[cond32],
        value_expr=ret32.value,
        return_info=ret32,
        summary_conditions=[cond32],
    )
    case64 = ReturnCase(
        index=0,
        conditions=[cond64],
        value_expr=ret64.value,
        return_info=ret64,
        summary_conditions=[cond64],
    )
    strategy = PairwiseStrategy(FormulaBuilder(), Mock(), debug=False)

    assert strategy._cases_have_equivalent_summary_conditions(case32, case64) is False


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
        return_abi_facts={
            "schema_version": 1,
            "calling_convention": {
                "status": "PRESENT",
                "value": ("ghidra_calling_convention_v1", "default"),
                "source": "getModelName",
            },
            "declared_or_effective_return_type": {
                "status": "PRESENT",
                "value": ("ghidra_return_type_v1", "/int", 8),
                "source": "getReturnType",
            },
            "return_storage_descriptor": {
                "status": "PRESENT",
                "value": (
                    "ghidra_return_storage_v1",
                    (("ghidra_return_storage_member_v1", "register", 0, 8),),
                ),
                "source": "getReturnStorage",
            },
        },
    )

    rewritten, _ = rewrite_analysis_returns(analysis, rewriter)

    assert rewritten.effect_summary is effect_summary
    assert rewritten.unknown_event_count == 3
    assert rewritten.unknown_event_reasons == ["r1"]
    assert rewritten.analysis_notes == ["n1"]
    assert rewritten.recovered_from_decompiler is True
    assert rewritten.incomplete_control_flow is True
    assert "placeholder" in rewritten.deferred_calls
    assert rewritten.return_abi_facts == analysis.return_abi_facts
    assert rewritten.return_abi_facts is not analysis.return_abi_facts
    assert rewritten.return_abi_facts["return_storage_descriptor"] is not analysis.return_abi_facts["return_storage_descriptor"]


def test_pairwise_strategy_skips_solver_for_rewritten_contradictory_conditions():
    rewriter = ExpressionRewriter(direction=ExpressionRewriter.NORMALIZE_TO_MODULO)
    analysis1 = _analysis(
        [
            _signed_negative_condition(
                _signed_modulo_expansion(
                    _indexed_param("param_1", 0),
                    _indexed_param("param_2", 1),
                ),
                negated=True,
            )
        ]
    )
    analysis2 = _analysis(
        [
            _signed_negative_condition(
                _binary(
                    "INT_SREM",
                    _indexed_param("param_1", 0),
                    _indexed_param("param_2", 1),
                )
            )
        ]
    )

    rewritten1, _ = rewrite_analysis_returns(analysis1, rewriter)
    rewritten2, _ = rewrite_analysis_returns(analysis2, rewriter)

    formula_builder = Mock()
    formula_builder.build_base_context.return_value = {
        "header_lines": [
            "(declare-const param_1_1 (_ BitVec 64))",
            "(declare-const param_2_1 (_ BitVec 64))",
            "(declare-const param_1_2 (_ BitVec 64))",
            "(declare-const param_2_2 (_ BitVec 64))",
            "(assert (= param_1_1 param_1_2))",
            "(assert (= param_2_1 param_2_2))",
        ],
        "params1": [
            ParameterInfo("param_1", "param_1_1", 64, 0),
            ParameterInfo("param_2", "param_2_1", 64, 1),
        ],
        "params2": [
            ParameterInfo("param_1", "param_1_2", 64, 0),
            ParameterInfo("param_2", "param_2_2", 64, 1),
        ],
        "extra_vars1": [],
        "extra_vars2": [],
    }
    solver_runner = _solver_runner()
    solver_runner.timeout = 5

    strategy = PairwiseStrategy(formula_builder, solver_runner, debug=False)
    result = strategy.check(rewritten1, rewritten2)

    assert result.is_equivalent is None
    assert result.total_pairs == 1
    assert result.unsat_pairs == 1
    assert result.unknown_pairs == 0
    assert any(
        note in rewritten1.analysis_notes
        for note in ("return_case_coverage_gap", "return_case_coverage_inconclusive")
    )
    assert any(
        note in rewritten2.analysis_notes
        for note in ("return_case_coverage_gap", "return_case_coverage_inconclusive")
    )
    solver_runner.run_sequential.assert_called()


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
        return_abi_facts=_missing_return_abi_facts(),
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
    solver_runner = _solver_runner()
    solver_runner.timeout = 5

    strategy = PairwiseStrategy(formula_builder, solver_runner, debug=False)
    result = strategy.check(analysis1, analysis2)

    assert result.is_equivalent is None
    assert result.total_pairs == 1
    assert result.unknown_pairs == 1
    assert result.unsat_pairs == 0
    assert result.sat_pairs == 0
    solver_runner.run_sequential.assert_called()


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
        return_abi_facts=_missing_return_abi_facts(),
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
    solver_runner = _solver_runner()
    solver_runner.timeout = 5

    strategy = PairwiseStrategy(formula_builder, solver_runner, debug=False)
    result = strategy.check(analysis1, analysis2)

    assert result.is_equivalent is None
    assert result.total_pairs == 1
    assert result.unknown_pairs == 1
    solver_runner.run_sequential.assert_called()


def test_pairwise_strategy_reduces_phi_unknown_under_pair_conditions():
    selector = Condition(_binary("INT_SLESS", _const(0), _indexed_param("param_1", 0)))
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
        return_abi_facts=_missing_return_abi_facts(),
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
        return_abi_facts=_missing_return_abi_facts(),
    )

    formula_builder = Mock()
    formula_builder.build_base_context.return_value = {
        "header_lines": [],
        "params1": [],
        "params2": [],
        "extra_vars1": [],
        "extra_vars2": [],
    }
    solver_runner = _solver_runner()
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

    assert result.is_equivalent is None
    assert result.total_pairs == 1
    assert result.unsat_pairs == 1
    assert result.unknown_pairs == 0
    assert any(
        note in analysis1.analysis_notes
        for note in ("return_case_coverage_gap", "return_case_coverage_inconclusive")
    )
    assert any(
        note in analysis2.analysis_notes
        for note in ("return_case_coverage_gap", "return_case_coverage_inconclusive")
    )


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
                    Condition(_binary("INT_EQUAL", _indexed_param("param_1", 0), _const(0)), negated=True),
                    Condition(_binary("INT_LESS", _indexed_param("param_1", 0), _const(101))),
                    Condition(_binary("INT_SLESS", _indexed_param("param_1", 0), _const(0)), negated=True),
                ],
            )
        ],
        return_type="int",
        return_abi_facts=_missing_return_abi_facts(),
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
                    Condition(_binary("INT_NOTEQUAL", _indexed_masked_param("param_1", 0), _const(0))),
                    Condition(_binary("INT_LESS", _const(100), _indexed_masked_param("param_1", 0)), negated=True),
                    Condition(_binary("INT_LESS", _const(0xFFFFFFFF), _indexed_masked_param("param_1", 0))),
                ],
            )
        ],
        return_type="int",
        return_abi_facts=_missing_return_abi_facts(),
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
                    Condition(_binary("INT_EQUAL", _indexed_param("param_1", 0), _const(0)), negated=True),
                    Condition(_binary("INT_LESS", _indexed_param("param_1", 0), _const(101))),
                    Condition(_binary("INT_SLESS", _indexed_param("param_1", 0), _const(0)), negated=True),
                ],
            ),
            ReturnInfo(
                address="0x1002",
                value=_const(2),
                conditions=[],
            ),
        ],
        return_type="int",
        return_abi_facts=_missing_return_abi_facts(),
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
                    Condition(_binary("INT_NOTEQUAL", _indexed_masked_param("param_1", 0), _const(0))),
                    Condition(_binary("INT_LESS", _const(100), _indexed_masked_param("param_1", 0)), negated=True),
                    Condition(_binary("INT_SLESS", _indexed_masked_param("param_1", 0), _const(0)), negated=True),
                ],
            ),
            ReturnInfo(
                address="0x2002",
                value=_const(2),
                conditions=[],
            ),
        ],
        return_type="int",
        return_abi_facts=_missing_return_abi_facts(),
    )

    solver_runner = _solver_runner()
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
    assert result.total_pairs == 4
    assert result.unsat_pairs == 4
    assert result.unknown_pairs == 0
