# -*- coding: utf-8 -*-

from types import MethodType
from unittest.mock import Mock

from scripts.function_tracer_pcode.equivalence.checker import EquivalenceChecker, StageID
from scripts.function_tracer_pcode.equivalence.recursive_abstraction import abstract_recursive_calls
from scripts.function_tracer_pcode.equivalence.result import EquivalenceResult
from scripts.function_tracer_pcode.equivalence.typing.fixer import TypeFixResult
from scripts.function_tracer_pcode.model import DeferredCallInfo, Expression, ReturnInfo
from scripts.function_tracer_pcode.smt import ParallelResult
from scripts.function_tracer_pcode.tests.conftest import create_mock_analysis, create_mock_result


def _param(name: str = "n", index: int = 0, size: int = 4):
    return Expression.parameter(name, index=index, data_type="int", size=size)


def _const(value: int, size: int = 4):
    return Expression.constant(value, size=size)


def test_recursive_abstraction_rewrites_matching_self_recursive_placeholders_to_shared_params():
    n1 = _param("n", 0)
    n2 = _param("m", 0)
    placeholder1 = "call_out_of_scope:left#0"
    placeholder2 = "call_out_of_scope:right#0"

    analysis1 = create_mock_analysis(
        "left",
        parameters=[{"name": "n", "index": 0, "data_type": "int", "size": 4}],
        returns=[
            ReturnInfo(
                address="0x1000",
                value=Expression.binary_op("INT_ADD", Expression.unknown(placeholder1), _const(1)),
                conditions=[],
            )
        ],
    )
    analysis2 = create_mock_analysis(
        "right",
        parameters=[{"name": "m", "index": 0, "data_type": "int", "size": 4}],
        returns=[
            ReturnInfo(
                address="0x2000",
                value=Expression.binary_op("INT_ADD", Expression.unknown(placeholder2), _const(1)),
                conditions=[],
            )
        ],
    )
    analysis1.deferred_calls = {
        placeholder1: DeferredCallInfo(placeholder1, "left", [Expression.binary_op("INT_SUB", n1, _const(1))])
    }
    analysis2.deferred_calls = {
        placeholder2: DeferredCallInfo(placeholder2, "right", [Expression.binary_op("INT_SUB", n2, _const(1))])
    }

    result = abstract_recursive_calls(analysis1, analysis2, debug=False)

    assert result.applied is True
    assert len(result.matches) == 1
    left_expr = result.analysis1.returns[0].value.to_string()
    right_expr = result.analysis2.returns[0].value.to_string()
    assert "summary_rec_" in left_expr
    assert left_expr == right_expr
    assert any(param.get("synthetic_recursive_summary") for param in result.analysis1.parameters)
    assert any(param.get("synthetic_recursive_summary") for param in result.analysis2.parameters)


def test_checker_uses_recursive_abstraction_stage_after_pairwise_unknown():
    checker = EquivalenceChecker(debug=False)
    analysis1 = create_mock_analysis("left")
    analysis2 = create_mock_analysis("right")

    pairwise_unknown = create_mock_result(None)
    pairwise_unknown.stage_path = []
    pairwise_unknown.type_fix_result = TypeFixResult()
    abstract_equiv = create_mock_result(True)
    abstract_equiv.stage_path = []
    abstract_equiv.type_fix_result = TypeFixResult()

    calls = []

    def fake_check(self, a1, a2, *args, force_strategy=None, **kwargs):
        calls.append((a1, a2, force_strategy))
        if len(calls) == 1:
            return pairwise_unknown
        return abstract_equiv

    checker.check = MethodType(fake_check, checker)

    def fake_recursive_stage(*args, **kwargs):
        return abstract_equiv

    checker._run_recursive_abstraction_stage = Mock(side_effect=fake_recursive_stage)

    result = checker._run_stage_plan(
        analysis1,
        analysis2,
        "bin1",
        "bin2",
        False,
        type_fix_result=TypeFixResult(),
        retry_count=0,
        original_signature1=None,
        original_signature2=None,
    )

    assert result is abstract_equiv
    checker._run_recursive_abstraction_stage.assert_called_once()
    assert StageID.S_ABSTRACT_RECURSIVE_SUMMARY.value in result.stage_path


def test_checker_skips_recursive_abstraction_stage_when_no_match_exists():
    checker = EquivalenceChecker(debug=False)
    analysis1 = create_mock_analysis("left")
    analysis2 = create_mock_analysis("right")

    pairwise_unknown = create_mock_result(None)
    pairwise_unknown.stage_path = []
    pairwise_unknown.type_fix_result = TypeFixResult()
    monolithic_unknown = create_mock_result(None)
    monolithic_unknown.stage_path = []
    monolithic_unknown.type_fix_result = TypeFixResult()

    sequence = [pairwise_unknown, monolithic_unknown]

    def fake_check(self, a1, a2, *args, force_strategy=None, **kwargs):
        return sequence.pop(0)

    checker.check = MethodType(fake_check, checker)
    checker._run_recursive_abstraction_stage = Mock(return_value=None)

    result = checker._run_stage_plan(
        analysis1,
        analysis2,
        "bin1",
        "bin2",
        False,
        type_fix_result=TypeFixResult(),
        retry_count=0,
        original_signature1=None,
        original_signature2=None,
    )

    assert result is monolithic_unknown
    assert StageID.S_ABSTRACT_RECURSIVE_SUMMARY.value not in result.stage_path
    assert result.stage_path == [
        StageID.S_PAIRWISE.value,
        StageID.S_MONOLITHIC_FALLBACK.value,
    ]
