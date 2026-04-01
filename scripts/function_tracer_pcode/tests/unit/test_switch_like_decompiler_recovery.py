# -*- coding: utf-8 -*-

from types import SimpleNamespace
from unittest.mock import Mock

from scripts.function_tracer_pcode.analysis.analyzer import ReturnAnalyzer
from scripts.function_tracer_pcode.equivalence.checker import EquivalenceChecker
from scripts.function_tracer_pcode.equivalence.result import EquivalenceResult
from scripts.function_tracer_pcode.model import Expression, ExpressionType, FunctionReturnAnalysis, ReturnInfo
from scripts.function_tracer_pcode.smt import ParallelResult, SolverResult, SolverStatus


def _param(name: str, index: int = 0, size: int = 4, data_type: str = "int"):
    return {"name": name, "index": index, "size": size, "data_type": data_type, "is_signed": True}


def _const_return(value: int, address: str = "0x1000", conditions=None):
    return ReturnInfo(
        address=address,
        value=Expression(ExpressionType.CONSTANT, value=value, size=4),
        conditions=list(conditions or []),
    )


def test_parse_switch_like_returns_from_decompiler_text_recovers_dense_cases():
    analyzer = ReturnAnalyzer(program=Mock(), debug=False)
    c_text = """
int branch_switch_dense(int param_1)
{
  switch ((int)param_1) {
  case 0:
    return 1000;
  case 1:
    return 1001;
  case 2:
    return 1002;
  case 3:
    return 1003;
  default:
    return -1000;
  }
}
"""

    recovered = analyzer._parse_switch_returns_from_c_text(
        c_text,
        [_param("param_1")],
        "int",
        "0x1000",
    )

    assert recovered is not None
    assert len(recovered) == 5
    assert [ret.value.value for ret in recovered] == [1000, 1001, 1002, 1003, -1000]
    assert recovered[0].conditions[0].to_string() == "(param_1 == 0)"
    assert recovered[3].conditions[0].to_string() == "(param_1 == 3)"
    assert [cond.to_string() for cond in recovered[4].conditions] == [
        "(param_1 != 0)",
        "(param_1 != 1)",
        "(param_1 != 2)",
        "(param_1 != 3)",
    ]


def test_parse_switch_like_returns_splits_fallthrough_labels_into_distinct_cases():
    analyzer = ReturnAnalyzer(program=Mock(), debug=False)
    c_text = """
int branch_switch_fallthrough(int value)
{
  switch (value)
  {
  case 0:
  case 1:
    return 1;
  case 2:
  case 3:
    return 2;
  default:
    return 9;
  }
}
"""

    recovered = analyzer._parse_switch_returns_from_c_text(
        c_text,
        [_param("value")],
        "int",
        "0x2000",
    )

    assert recovered is not None
    assert len(recovered) == 5
    assert [ret.value.value for ret in recovered] == [1, 1, 2, 2, 9]
    assert [ret.conditions[0].to_string() for ret in recovered[:4]] == [
        "(value == 0)",
        "(value == 1)",
        "(value == 2)",
        "(value == 3)",
    ]


def test_parse_switch_like_returns_recovers_shared_return_variable_pattern():
    analyzer = ReturnAnalyzer(program=Mock(), debug=False)
    c_text = """
int branch_switch_dense(int param_1)
{
  int local_4;

  switch ((int)param_1) {
  case 0:
    local_4 = 1000;
    break;
  case 1:
    local_4 = 1001;
    break;
  case 2:
    local_4 = 1002;
    break;
  case 3:
    local_4 = 1003;
    break;
  default:
    local_4 = -1000;
  }
  return local_4;
}
"""

    recovered = analyzer._parse_switch_returns_from_c_text(
        c_text,
        [_param("param_1")],
        "int",
        "0x2100",
    )

    assert recovered is not None
    assert len(recovered) == 5
    assert [ret.value.value for ret in recovered] == [1000, 1001, 1002, 1003, -1000]
    assert recovered[0].conditions[0].to_string() == "(param_1 == 0)"
    assert [cond.to_string() for cond in recovered[4].conditions] == [
        "(param_1 != 0)",
        "(param_1 != 1)",
        "(param_1 != 2)",
        "(param_1 != 3)",
    ]


def test_recover_switch_like_returns_from_decompiler_for_suspicious_analysis():
    analyzer = ReturnAnalyzer(program=Mock(), debug=False)
    decompile_results = SimpleNamespace(
        getDecompiledFunction=lambda: SimpleNamespace(
            getC=lambda: """
int branch_switch_dense(int param_1)
{
  switch (param_1) {
  case 0:
    return 1000;
  case 1:
    return 1001;
  default:
    return -1000;
  }
}
"""
        )
    )
    analysis = FunctionReturnAnalysis(
        function_name="branch_switch_dense",
        entry_point="0x3000",
        parameters=[_param("param_1")],
        returns=[
            ReturnInfo(
                address="0x3000",
                value=Expression.unknown("call_out_of_scope:UNKNOWN_FUNC"),
                conditions=[],
            )
        ],
        return_type="int",
        unknown_event_reasons=["call_out_of_scope"],
        unknown_event_count=1,
    )

    recovered = analyzer._recover_switch_like_returns_from_decompiler(
        decompile_results,
        analysis,
    )

    assert recovered is not None
    assert [ret.value.value for ret in recovered] == [1000, 1001, -1000]


def test_checker_skips_monolithic_fallback_for_incomplete_control_flow_summary():
    checker = EquivalenceChecker(debug=False, strategy="pairwise")

    analysis1 = FunctionReturnAnalysis(
        function_name="f1",
        entry_point="0x1",
        parameters=[_param("x")],
        returns=[_const_return(1000), _const_return(1001)],
        return_type="int",
        incomplete_control_flow=True,
        analysis_notes=["overlapping_unconditional_returns"],
    )
    analysis2 = FunctionReturnAnalysis(
        function_name="f2",
        entry_point="0x2",
        parameters=[_param("x")],
        returns=[_const_return(1000, address="0x2000")],
        return_type="int",
    )

    unknown_result = EquivalenceResult(
        is_equivalent=None,
        function1_name="f1",
        function2_name="f2",
        binary1_name="b1",
        binary2_name="b2",
        solver_results=ParallelResult(
            results=[SolverResult("mock", SolverStatus.UNKNOWN, elapsed_time=0.01)]
        ),
    )

    calls = []

    def _fake_check(*args, **kwargs):
        calls.append(kwargs.get("force_strategy").__class__.__name__)
        return unknown_result

    checker.check = _fake_check

    result = checker._run_stage_plan(
        analysis1,
        analysis2,
        "b1",
        "b2",
        save_formula=False,
        type_fix_result=None,
        retry_count=0,
        original_signature1=None,
        original_signature2=None,
    )

    assert result is unknown_result
    assert calls == ["PairwiseStrategy"]
