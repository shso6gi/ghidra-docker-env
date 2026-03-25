# -*- coding: utf-8 -*-

from unittest.mock import Mock, patch

from scripts.function_tracer_pcode.analysis.analyzer import ReturnAnalyzer
from scripts.function_tracer_pcode.equivalence.formula.symbol_replace import build_symbol_replacer
from scripts.function_tracer_pcode.equivalence.formula.types import ParameterInfo
from scripts.function_tracer_pcode.equivalence.strategies.pairwise_models import ReturnCase
from scripts.function_tracer_pcode.equivalence.strategies.pairwise_query_executor import (
    validate_counterexample_across_cases,
)
from scripts.function_tracer_pcode.model import Condition, Expression, FunctionReturnAnalysis, ReturnInfo
from scripts.function_tracer_pcode.smt import ParallelResult, SolverResult, SolverStatus
from scripts.function_tracer_pcode.transform.expander import ExpandedValue, ExpressionExpander


def _param_expr(name: str, index: int = 0, size: int = 4) -> Expression:
    return Expression.parameter(name, index=index, size=size)


def _cond_eq(left: Expression, right: Expression) -> Condition:
    return Condition(Expression.binary_op("INT_EQUAL", left, right), False)


def _cond_ne(left: Expression, right: Expression) -> Condition:
    return Condition(Expression.binary_op("INT_NOTEQUAL", left, right), False)


def test_return_analyzer_resolves_call_summary_with_argument_substitution():
    analyzer = ReturnAnalyzer(program=Mock(), debug=False)
    callee_analysis = FunctionReturnAnalysis(
        function_name="callee",
        entry_point="0x401000",
        parameters=[{"name": "x", "size": 4, "index": 0}],
        returns=[
            ReturnInfo(
                address="0x401010",
                value=Expression.binary_op(
                    "INT_ADD",
                    Expression.parameter("x", 0, size=4),
                    Expression.constant(2, 4),
                ),
                conditions=[
                    _cond_ne(
                        Expression.parameter("x", 0, size=4),
                        Expression.constant(0, 4),
                    )
                ],
                branch_index=0,
            )
        ],
        return_type="int",
    )

    with patch.object(analyzer, "_get_or_analyze_call_target", return_value=callee_analysis):
        expanded = analyzer._resolve_call_expansions(
            "callee",
            [_param_expr("arg0", 0, size=4)],
            active_functions=set(),
        )

    assert expanded is not None
    assert len(expanded) == 1
    assert expanded[0].value.to_string() == "(arg0 + 2)"
    assert [cond.to_string() for cond in expanded[0].conditions] == ["(arg0 != 0)"]


def test_expression_expander_inlines_direct_call_results():
    class _FakeVarnode:
        def __init__(self, name, size=4):
            self.name = name
            self._size = size

        def getDef(self):
            return None

        def getSize(self):
            return self._size

    class _FakeOutput:
        def __init__(self, size):
            self._size = size

        def getSize(self):
            return self._size

    class _FakeCallOp:
        def __init__(self, target, arg):
            self._inputs = [target, arg]
            self._output = _FakeOutput(4)

        def getMnemonic(self):
            return "CALL"

        def getNumInputs(self):
            return len(self._inputs)

        def getInput(self, index):
            return self._inputs[index]

        def getOutput(self):
            return self._output

    target_varnode = _FakeVarnode("callee_addr", size=8)
    arg_varnode = _FakeVarnode("arg0", size=4)

    class _FakeTracer:
        debug = False

        def _get_function_name(self, _varnode):
            return "callee"

        def trace_varnode(self, varnode, depth=0, use_cache=False):
            if varnode is target_varnode:
                return Expression.constant(0x401000, 8)
            if varnode is arg_varnode:
                return _param_expr("arg0", 0, size=4)
            raise AssertionError(f"unexpected varnode: {varnode}")

        def emit_unknown_event(self, **kwargs):
            raise AssertionError(f"call should have been resolved: {kwargs}")

        def _trace_pcode_op(self, *_args, **_kwargs):
            raise AssertionError("recursive tracing fallback should not run")

    def _resolve_call(function_name, args):
        assert function_name == "callee"
        assert len(args) == 1
        return [
            ExpandedValue(
                Expression.binary_op("INT_ADD", args[0], Expression.constant(1, 4)),
                [_cond_ne(args[0], Expression.constant(0, 4))],
            )
        ]

    expander = ExpressionExpander(
        _FakeTracer(),
        condition_tracker=None,
        debug=False,
        call_resolver=_resolve_call,
    )
    base_conditions = [_cond_eq(_param_expr("arg0", 0, size=4), Expression.constant(7, 4))]

    expanded = expander._expand_call_operation(
        _FakeCallOp(target_varnode, arg_varnode),
        base_conditions,
        depth=0,
        output_size=4,
    )

    assert len(expanded) == 1
    assert expanded[0].value.to_string() == "(arg0 + 1)"
    assert [cond.to_string() for cond in expanded[0].conditions] == [
        "(arg0 == 7)",
        "(arg0 != 0)",
    ]


def test_counterexample_validation_rejects_ambiguous_sat_model():
    class _Strategy:
        def __init__(self):
            self.solver_runner = _FakeSolverRunner()
            self.per_query_timeout = 5
            self.messages = []

        def _debug_print(self, msg: str):
            self.messages.append(msg)

    class _FakeSolverRunner:
        def __init__(self):
            self.timeout = 5

        def run_sequential(self, query: str):
            if "(assert (= (_ bv7 32) (_ bv7 32)))" in query:
                return ParallelResult(
                    results=[SolverResult("fake", SolverStatus.SAT, model={"x_1": 5, "x_2": 5})]
                )
            if "(assert (= x_1 (bvadd x_2 (_ bv1 32))))" in query:
                return ParallelResult(
                    results=[SolverResult("fake", SolverStatus.UNSAT)]
                )
            return ParallelResult(
                results=[SolverResult("fake", SolverStatus.SAT, model={"x_1": 5, "x_2": 5})]
            )

    strategy = _Strategy()
    params1 = [ParameterInfo(original_name="x", smt_name="x_1", bit_width=32, index=0)]
    params2 = [ParameterInfo(original_name="x", smt_name="x_2", bit_width=32, index=0)]
    replace1 = build_symbol_replacer(params1, [])
    replace2 = build_symbol_replacer(params2, [])
    x1 = _param_expr("x", 0, size=4)
    x2 = _param_expr("x", 0, size=4)

    cases1 = [
        ReturnCase(
            index=0,
            conditions=[],
            value_expr=x1,
            return_info=ReturnInfo(address="0x1", value=x1, conditions=[]),
            return_type="int",
        ),
        ReturnCase(
            index=1,
            conditions=[_cond_eq(x1, Expression.constant(5, 4))],
            value_expr=Expression.constant(7, 4),
            return_info=ReturnInfo(
                address="0x2",
                value=Expression.constant(7, 4),
                conditions=[_cond_eq(x1, Expression.constant(5, 4))],
            ),
            return_type="int",
        ),
    ]
    cases2 = [
        ReturnCase(
            index=0,
            conditions=[],
            value_expr=Expression.binary_op("INT_ADD", x2, Expression.constant(1, 4)),
            return_info=ReturnInfo(
                address="0x3",
                value=Expression.binary_op("INT_ADD", x2, Expression.constant(1, 4)),
                conditions=[],
            ),
            return_type="int",
        ),
        ReturnCase(
            index=1,
            conditions=[_cond_eq(x2, Expression.constant(5, 4))],
            value_expr=Expression.constant(7, 4),
            return_info=ReturnInfo(
                address="0x4",
                value=Expression.constant(7, 4),
                conditions=[_cond_eq(x2, Expression.constant(5, 4))],
            ),
            return_type="int",
        ),
    ]
    base_ctx = {
        "header_lines": [
            "(declare-const x_1 (_ BitVec 32))",
            "(declare-const x_2 (_ BitVec 32))",
            "(assert (= x_1 x_2))",
        ],
        "params1": params1,
        "params2": params2,
        "extra_vars1": [],
        "extra_vars2": [],
        "return_size1": 32,
        "return_size2": 32,
    }

    is_decisive = validate_counterexample_across_cases(
        strategy,
        base_ctx,
        cases1,
        cases2,
        replace1,
        replace2,
        sat_case_indices=(0, 0),
        counterexample_raw={"x_1": 5, "x_2": 5},
    )

    assert not is_decisive
    assert any("ambiguous" in message for message in strategy.messages)
