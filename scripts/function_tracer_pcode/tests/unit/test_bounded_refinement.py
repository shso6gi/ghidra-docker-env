# -*- coding: utf-8 -*-

from scripts.function_tracer_pcode.analysis.bounded_refinement import BoundedCallRefiner
from scripts.function_tracer_pcode.model import Condition, DeferredCallInfo, Expression, ReturnInfo
from scripts.function_tracer_pcode.tests.conftest import create_mock_analysis


def _param(name: str = "n", index: int = 0, size: int = 4) -> Expression:
    return Expression.parameter(name, index=index, data_type="int", size=size)


def _const(value: int, size: int = 4) -> Expression:
    return Expression.constant(value, size=size)


def _cond(operator: str, left: Expression, right: Expression) -> Condition:
    return Condition(Expression.binary_op(operator, left, right), negated=False)


def test_bounded_call_refiner_unrolls_direct_self_recursion_without_diverging():
    n = _param()
    recursive_placeholder = "call_out_of_scope:sum#0"
    recursive_value = Expression.binary_op(
        "INT_ADD",
        Expression.unknown(recursive_placeholder),
        n,
    )

    analysis = create_mock_analysis(
        "sum",
        parameters=[{"name": "n", "index": 0, "data_type": "int", "size": 4}],
        returns=[
            ReturnInfo(address="0x1000", value=_const(0), conditions=[_cond("INT_SLESSEQUAL", n, _const(0))]),
            ReturnInfo(address="0x1004", value=recursive_value, conditions=[_cond("INT_SLESS", _const(0), n)]),
        ],
    )
    analysis.deferred_calls = {
        recursive_placeholder: DeferredCallInfo(
            placeholder_name=recursive_placeholder,
            target_name="sum",
            arguments=[Expression.binary_op("INT_SUB", n, _const(1))],
        )
    }

    refiner = BoundedCallRefiner(
        lambda function_name: analysis if function_name == "sum" else None,
        max_unroll=2,
        max_cases=32,
        debug=False,
    )

    changed = refiner.refine_analysis(analysis)

    assert changed is True
    assert len(analysis.returns) > 2
    assert any("call_out_of_scope" not in ret.value.to_string() for ret in analysis.returns)
    assert any("call_out_of_scope" in ret.value.to_string() for ret in analysis.returns)
    assert len(analysis.returns) <= 32


def test_bounded_call_refiner_handles_mutual_recursion_with_fuel_cap():
    n = _param()
    a_placeholder = "call_out_of_scope:A#0"
    b_placeholder = "call_out_of_scope:B#0"

    analysis_a = create_mock_analysis(
        "A",
        parameters=[{"name": "n", "index": 0, "data_type": "int", "size": 4}],
        returns=[
            ReturnInfo(address="0x2000", value=_const(0), conditions=[_cond("INT_SLESSEQUAL", n, _const(0))]),
            ReturnInfo(
                address="0x2004",
                value=Expression.binary_op("INT_ADD", Expression.unknown(b_placeholder), _const(1)),
                conditions=[_cond("INT_SLESS", _const(0), n)],
            ),
        ],
    )
    analysis_b = create_mock_analysis(
        "B",
        parameters=[{"name": "n", "index": 0, "data_type": "int", "size": 4}],
        returns=[
            ReturnInfo(address="0x3000", value=_const(0), conditions=[_cond("INT_SLESSEQUAL", n, _const(0))]),
            ReturnInfo(
                address="0x3004",
                value=Expression.binary_op("INT_ADD", Expression.unknown(a_placeholder), _const(2)),
                conditions=[_cond("INT_SLESS", _const(0), n)],
            ),
        ],
    )
    analysis_a.deferred_calls = {
        b_placeholder: DeferredCallInfo(
            placeholder_name=b_placeholder,
            target_name="B",
            arguments=[Expression.binary_op("INT_SUB", n, _const(1))],
        )
    }
    analysis_b.deferred_calls = {
        a_placeholder: DeferredCallInfo(
            placeholder_name=a_placeholder,
            target_name="A",
            arguments=[Expression.binary_op("INT_SUB", n, _const(1))],
        )
    }

    analyses = {"A": analysis_a, "B": analysis_b}
    refiner = BoundedCallRefiner(
        lambda function_name: analyses.get(function_name),
        max_unroll=3,
        max_cases=24,
        debug=False,
    )

    changed = refiner.refine_analysis(analysis_a)

    assert changed is True
    assert len(analysis_a.returns) <= 24
    assert any("call_out_of_scope" in ret.value.to_string() for ret in analysis_a.returns)
    assert any("call_out_of_scope" not in ret.value.to_string() for ret in analysis_a.returns)


def test_bounded_call_refiner_respects_case_cap():
    n = _param()
    placeholder = "call_out_of_scope:fanout#0"
    analysis = create_mock_analysis(
        "fanout",
        parameters=[{"name": "n", "index": 0, "data_type": "int", "size": 4}],
        returns=[
            ReturnInfo(
                address="0x4000",
                value=Expression.unknown(placeholder),
                conditions=[_cond("INT_SLESS", _const(0), n)],
            )
        ],
    )
    analysis.deferred_calls = {
        placeholder: DeferredCallInfo(
            placeholder_name=placeholder,
            target_name="callee",
            arguments=[n],
        )
    }

    callee = create_mock_analysis(
        "callee",
        parameters=[{"name": "n", "index": 0, "data_type": "int", "size": 4}],
        returns=[
            ReturnInfo(address=f"0x500{i}", value=_const(i), conditions=[_cond("INT_SLESS", _const(i), n)])
            for i in range(6)
        ],
    )

    refiner = BoundedCallRefiner(
        lambda function_name: callee if function_name == "callee" else None,
        max_unroll=1,
        max_cases=3,
        debug=False,
    )

    changed = refiner.refine_analysis(analysis)

    assert changed is True
    assert len(analysis.returns) == 3
