# -*- coding: utf-8 -*-

from unittest.mock import Mock

from scripts.function_tracer_pcode.analysis.effect_summary import (
    CanonicalLocation,
    EffectSummary,
    StoreEffect,
    post_state_read_expression_for_location,
)
from scripts.function_tracer_pcode.equivalence.formula.builder import FormulaBuilderResult
from scripts.function_tracer_pcode.equivalence.formula.types import ParameterInfo
from scripts.function_tracer_pcode.equivalence.strategies.monolithic import MonolithicStrategy
from scripts.function_tracer_pcode.equivalence.strategies.pairwise import PairwiseStrategy
from scripts.function_tracer_pcode.equivalence.strategies.pairwise_models import (
    QueryResult,
    ReturnCase,
)
from scripts.function_tracer_pcode.model import Condition, Expression, FunctionReturnAnalysis, ReturnInfo
from scripts.function_tracer_pcode.model.runtime_refs import LocationBaseRef
from scripts.function_tracer_pcode.smt import ParallelResult, SolverResult, SolverStatus


def _param(name: str, index: int = 0, size: int = 4, data_type: str = "int"):
    return {
        "name": name,
        "index": index,
        "size": size,
        "data_type": data_type,
        "is_signed": "unsigned" not in data_type,
    }


def _const(value: int, size: int = 4) -> Expression:
    return Expression.constant(value, size)


def _eq(lhs: Expression, rhs: Expression) -> Condition:
    return Condition(Expression.binary_op("INT_EQUAL", lhs, rhs), False)


def _build_symbolic_post_state_analysis(name: str) -> FunctionReturnAnalysis:
    params = [_param("trace", index=0, size=8, data_type="int *")]
    value = post_state_read_expression_for_location(
        CanonicalLocation("trace", 0, 4),
        params,
        symbolic=True,
    )
    return FunctionReturnAnalysis(
        function_name=name,
        entry_point="0x1000",
        parameters=params,
        returns=[ReturnInfo(address="0x1000", value=value, conditions=[])],
        return_type="int",
    )


def test_function_return_analysis_marks_symbolic_post_state_reads_as_sat_unsafe():
    analysis = _build_symbolic_post_state_analysis("with_locread")

    assert analysis.has_symbolic_post_state_reads() is True
    assert "symbolic_post_state_reads" in analysis.get_decisive_sat_unsafety_reasons()


def test_function_return_analysis_treats_lowerable_post_state_reads_as_sat_safe():
    params = [
        _param("trace", index=0, size=8, data_type="int *"),
        _param("delta", index=1, size=4, data_type="int"),
    ]
    trace = Expression.parameter("trace", 0, size=8)
    delta = Expression.parameter("delta", 1, size=4)
    location = CanonicalLocation(
        base_ref=LocationBaseRef.parameter("trace", index=0),
        offset=0,
        size=4,
    )
    analysis = FunctionReturnAnalysis(
        function_name="lowerable",
        entry_point="0x1000",
        parameters=params,
        returns=[
            ReturnInfo(
                address="0x1000",
                value=post_state_read_expression_for_location(
                    location,
                    params,
                    symbolic=True,
                ),
                conditions=[],
            )
        ],
        return_type="int",
        effect_summary=EffectSummary(
            parameter_names=["trace", "delta"],
            effects=[
                StoreEffect(
                    location=location,
                    value=Expression.binary_op("INT_ADD", Expression.memory(trace, size=4), delta),
                    conditions=[],
                    order_key=1,
                )
            ],
        ),
    )

    assert analysis.has_symbolic_post_state_reads() is False
    assert "symbolic_post_state_reads" not in analysis.get_decisive_sat_unsafety_reasons()


def test_pairwise_strategy_downgrades_sat_when_analysis_retains_symbolic_post_state_reads(monkeypatch):
    formula_builder = Mock()
    formula_builder.build_base_context.return_value = {
        "header_lines": [],
        "params1": [],
        "params2": [],
        "extra_vars1": [],
        "extra_vars2": [],
        "constrained_fragments": [],
        "return_size1": 32,
        "return_size2": 32,
    }
    solver_runner = Mock()
    solver_runner.timeout = 5
    strategy = PairwiseStrategy(formula_builder, solver_runner, debug=False)

    analysis1 = _build_symbolic_post_state_analysis("f1")
    analysis2 = FunctionReturnAnalysis(
        function_name="f2",
        entry_point="0x2000",
        parameters=[_param("trace", index=0, size=8, data_type="int *")],
        returns=[ReturnInfo(address="0x2000", value=_const(0), conditions=[])],
        return_type="int",
    )

    trace = Expression.parameter("trace", 0, size=8)
    symbolic_case = ReturnCase(
        index=0,
        conditions=[],
        value_expr=post_state_read_expression_for_location(
            CanonicalLocation("trace", 0, 4),
            analysis1.parameters,
            symbolic=True,
        ),
        return_info=analysis1.returns[0],
        return_type="int",
        parameters=analysis1.parameters,
    )
    const_case = ReturnCase(
        index=0,
        conditions=[],
        value_expr=_const(0),
        return_info=analysis2.returns[0],
        return_type="int",
        parameters=analysis2.parameters,
    )

    monkeypatch.setattr(
        strategy,
        "_extract_return_cases",
        lambda analysis: [symbolic_case] if analysis.function_name == "f1" else [const_case],
    )
    monkeypatch.setattr(strategy, "_prune_unreachable_cases", lambda cases, *_args, **_kwargs: cases)
    monkeypatch.setattr(strategy, "_cases_are_contradictory", lambda *_args, **_kwargs: False)
    monkeypatch.setattr(strategy, "_case_contains_unresolved_expression", lambda *_args, **_kwargs: False)
    monkeypatch.setattr(
        "scripts.function_tracer_pcode.equivalence.strategies.pairwise.validate_counterexample_across_cases",
        lambda *_args, **_kwargs: (_ for _ in ()).throw(
            AssertionError("ambiguous-model validation should not run for SAT-unsafe analyses")
        ),
    )
    strategy._solve_query_twostage = Mock(
        return_value=QueryResult(
            is_equivalent=False,
            counterexample_raw={"trace_1": 1, "trace_2": 1},
        )
    )

    result = strategy.check(analysis1, analysis2)

    assert result.is_equivalent is None
    assert result.sat_pairs == 0
    assert result.unknown_pairs == 1


def test_monolithic_strategy_downgrades_ambiguous_sat_counterexample_to_unknown():
    class _ValidationSolverRunner:
        def __init__(self):
            self.timeout = 5

        def run_parallel(self, _query: str):
            return ParallelResult(
                results=[
                    SolverResult(
                        "fake",
                        SolverStatus.SAT,
                        elapsed_time=0.01,
                        model={"x_1": 5, "x_2": 5},
                    )
                ]
            )

        def run_sequential(self, query: str):
            if "(assert (= (_ bv7 32) (_ bv7 32)))" in query:
                return ParallelResult(
                    results=[SolverResult("fake", SolverStatus.SAT, model={"x_1": 5, "x_2": 5})]
                )
            if "(assert (= x_1 (bvadd x_2 (_ bv1 32))))" in query:
                return ParallelResult(results=[SolverResult("fake", SolverStatus.UNSAT)])
            return ParallelResult(
                results=[SolverResult("fake", SolverStatus.SAT, model={"x_1": 5, "x_2": 5})]
            )

    x1 = Expression.parameter("x", 0, size=4)
    x2 = Expression.parameter("x", 0, size=4)
    cond1 = _eq(x1, _const(5))
    cond2 = _eq(x2, _const(5))

    analysis1 = FunctionReturnAnalysis(
        function_name="func1",
        entry_point="0x1",
        parameters=[_param("x")],
        returns=[
            ReturnInfo(address="0x1", value=x1, conditions=[]),
            ReturnInfo(address="0x2", value=_const(7), conditions=[cond1]),
        ],
        return_type="int",
    )
    analysis2 = FunctionReturnAnalysis(
        function_name="func2",
        entry_point="0x2",
        parameters=[_param("x")],
        returns=[
            ReturnInfo(
                address="0x3",
                value=Expression.binary_op("INT_ADD", x2, _const(1)),
                conditions=[],
            ),
            ReturnInfo(address="0x4", value=_const(7), conditions=[cond2]),
        ],
        return_type="int",
    )

    params1 = [ParameterInfo(original_name="x", smt_name="x_1", bit_width=32, index=0)]
    params2 = [ParameterInfo(original_name="x", smt_name="x_2", bit_width=32, index=0)]
    formula_builder = Mock()
    formula_builder.build_equivalence_formula_extended.return_value = FormulaBuilderResult(
        formula="(set-logic QF_BV)\n(check-sat)",
        return_var1="return_1",
        return_var2="return_2",
        constrained_fragments=[],
        extra_vars1=[],
        extra_vars2=[],
        param_fragment_constrained=[],
    )
    formula_builder.build_base_context.return_value = {
        "header_lines": [
            "(declare-const x_1 (_ BitVec 32))",
            "(declare-const x_2 (_ BitVec 32))",
            "(assert (= x_1 x_2))",
        ],
        "params1": params1,
        "params2": params2,
        "extra_vars1": [],
        "extra_vars2": [],
        "constrained_fragments": [],
        "return_size1": 32,
        "return_size2": 32,
    }

    strategy = MonolithicStrategy(formula_builder, _ValidationSolverRunner(), debug=False)

    result = strategy.check(analysis1, analysis2)

    assert result.is_equivalent is None
    assert result.counterexample_raw is None


def test_pairwise_strategy_downgrades_sat_when_return_cases_leave_coverage_gap(monkeypatch):
    formula_builder = Mock()
    formula_builder.build_base_context.return_value = {
        "header_lines": [
            "(declare-const x_1 (_ BitVec 32))",
            "(declare-const x_2 (_ BitVec 32))",
            "(assert (= x_1 x_2))",
        ],
        "params1": [ParameterInfo(original_name="x", smt_name="x_1", bit_width=32, index=0)],
        "params2": [ParameterInfo(original_name="x", smt_name="x_2", bit_width=32, index=0)],
        "extra_vars1": [],
        "extra_vars2": [],
        "constrained_fragments": [],
        "return_size1": 32,
        "return_size2": 32,
    }
    solver_runner = Mock()
    solver_runner.timeout = 5
    solver_runner.run_sequential.return_value = ParallelResult(
        results=[SolverResult("fake", SolverStatus.SAT, model={"x_1": 7, "x_2": 7})]
    )
    strategy = PairwiseStrategy(formula_builder, solver_runner, debug=False)

    x = Expression.parameter("x", 0, size=4)
    analysis1 = FunctionReturnAnalysis(
        function_name="func1",
        entry_point="0x1",
        parameters=[_param("x")],
        returns=[ReturnInfo(address="0x1", value=_const(1), conditions=[_eq(x, _const(0))])],
        return_type="int",
    )
    analysis2 = FunctionReturnAnalysis(
        function_name="func2",
        entry_point="0x2",
        parameters=[_param("x")],
        returns=[ReturnInfo(address="0x2", value=_const(2), conditions=[])],
        return_type="int",
    )

    case1 = ReturnCase(
        index=0,
        conditions=[_eq(Expression.parameter("x", 0, size=4), _const(0))],
        value_expr=_const(1),
        return_info=analysis1.returns[0],
        return_type="int",
        parameters=analysis1.parameters,
    )
    case2 = ReturnCase(
        index=0,
        conditions=[],
        value_expr=_const(2),
        return_info=analysis2.returns[0],
        return_type="int",
        parameters=analysis2.parameters,
    )

    monkeypatch.setattr(
        strategy,
        "_extract_return_cases",
        lambda analysis: [case1] if analysis.function_name == "func1" else [case2],
    )
    monkeypatch.setattr(strategy, "_prune_unreachable_cases", lambda cases, *_args, **_kwargs: cases)
    monkeypatch.setattr(strategy, "_cases_are_contradictory", lambda *_args, **_kwargs: False)
    monkeypatch.setattr(strategy, "_case_contains_unresolved_expression", lambda *_args, **_kwargs: False)
    monkeypatch.setattr(
        "scripts.function_tracer_pcode.equivalence.strategies.pairwise.validate_counterexample_across_cases",
        lambda *_args, **_kwargs: (_ for _ in ()).throw(
            AssertionError("pairwise counterexample validation should not run when coverage is incomplete")
        ),
    )
    strategy._solve_query_twostage = Mock(
        return_value=QueryResult(
            is_equivalent=False,
            counterexample_raw={"x_1": 7, "x_2": 7},
        )
    )

    result = strategy.check(analysis1, analysis2)

    assert result.is_equivalent is None
    assert result.sat_pairs == 0
    assert result.unknown_pairs == 1
    assert "return_case_coverage_gap" in analysis1.analysis_notes
    assert analysis2.analysis_notes == []


def test_monolithic_strategy_downgrades_sat_when_return_cases_leave_coverage_gap():
    class _CoverageGapSolverRunner:
        def __init__(self):
            self.timeout = 5

        def run_parallel(self, _query: str):
            return ParallelResult(
                results=[SolverResult("fake", SolverStatus.SAT, model={"x_1": 7, "x_2": 7})]
            )

        def run_sequential(self, query: str):
            if "Return coverage gap query: function1" in query:
                return ParallelResult(
                    results=[SolverResult("fake", SolverStatus.SAT, model={"x_1": 7, "x_2": 7})]
                )
            return ParallelResult(results=[SolverResult("fake", SolverStatus.UNSAT)])

    x1 = Expression.parameter("x", 0, size=4)
    x2 = Expression.parameter("x", 0, size=4)
    analysis1 = FunctionReturnAnalysis(
        function_name="func1",
        entry_point="0x1",
        parameters=[_param("x")],
        returns=[ReturnInfo(address="0x1", value=_const(1), conditions=[_eq(x1, _const(0))])],
        return_type="int",
    )
    analysis2 = FunctionReturnAnalysis(
        function_name="func2",
        entry_point="0x2",
        parameters=[_param("x")],
        returns=[ReturnInfo(address="0x2", value=x2, conditions=[])],
        return_type="int",
    )

    params1 = [ParameterInfo(original_name="x", smt_name="x_1", bit_width=32, index=0)]
    params2 = [ParameterInfo(original_name="x", smt_name="x_2", bit_width=32, index=0)]
    formula_builder = Mock()
    formula_builder.build_equivalence_formula_extended.return_value = FormulaBuilderResult(
        formula="(set-logic QF_BV)\n(check-sat)",
        return_var1="return_1",
        return_var2="return_2",
        constrained_fragments=[],
        extra_vars1=[],
        extra_vars2=[],
        param_fragment_constrained=[],
    )
    formula_builder.build_base_context.return_value = {
        "header_lines": [
            "(declare-const x_1 (_ BitVec 32))",
            "(declare-const x_2 (_ BitVec 32))",
            "(assert (= x_1 x_2))",
        ],
        "params1": params1,
        "params2": params2,
        "extra_vars1": [],
        "extra_vars2": [],
        "constrained_fragments": [],
        "return_size1": 32,
        "return_size2": 32,
    }

    strategy = MonolithicStrategy(formula_builder, _CoverageGapSolverRunner(), debug=False)

    result = strategy.check(analysis1, analysis2)

    assert result.is_equivalent is None
    assert result.counterexample_raw is None


def test_function_return_analysis_skips_monolithic_fallback_when_coverage_gap_note_is_present():
    analysis = FunctionReturnAnalysis(
        function_name="func1",
        entry_point="0x1",
        parameters=[_param("x")],
        returns=[ReturnInfo(address="0x1", value=_const(1), conditions=[_eq(Expression.parameter("x", 0, size=4), _const(0))])],
        return_type="int",
        analysis_notes=["return_case_coverage_gap"],
    )

    assert analysis.should_skip_monolithic_fallback() is True
    assert "return_case_coverage_gap" in analysis.get_decisive_sat_unsafety_reasons()
