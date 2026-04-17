# -*- coding: utf-8 -*-

from scripts.function_tracer_pcode.analysis.bounded_refinement import BoundedCallRefiner
from scripts.function_tracer_pcode.analysis.effect_summary import (
    CanonicalLocation,
    EffectSummary,
    StoreEffect,
    expression_contains_post_state_reads,
    post_state_read_expression_for_location,
)
from scripts.function_tracer_pcode.model import (
    CallTargetRef,
    Condition,
    DeferredCallInfo,
    Expression,
    ReturnInfo,
    UnknownValueRef,
)
from scripts.function_tracer_pcode.tests.conftest import create_mock_analysis


def _param(name: str = "n", index: int = 0, size: int = 4) -> Expression:
    return Expression.parameter(name, index=index, data_type="int", size=size)


def _const(value: int, size: int = 4) -> Expression:
    return Expression.constant(value, size=size)


def _cond(operator: str, left: Expression, right: Expression) -> Condition:
    return Condition(Expression.binary_op(operator, left, right), negated=False)


def _deferred_unknown(info: DeferredCallInfo) -> Expression:
    return Expression.unknown(
        info.placeholder_name,
        runtime_ref=UnknownValueRef.deferred_call(
            placeholder_name=info.placeholder_name,
            target_ref=info.target_ref,
            sequence=info.sequence,
            deferred_key=info.identity_key(),
        ),
    )


def test_bounded_call_refiner_runtime_dedup_does_not_require_to_string(monkeypatch):
    value = Expression.binary_op("INT_ADD", _param(), _const(1))
    cond = _cond("INT_EQUAL", _param(), _const(0))
    refiner = BoundedCallRefiner(lambda _target_ref: None, debug=False)

    def _boom_expr(_self, simplify=True):
        raise AssertionError("bounded refinement should not depend on Expression.to_string")

    def _boom_cond(_self):
        raise AssertionError("bounded refinement should not depend on Condition.to_string")

    monkeypatch.setattr(Expression, "to_string", _boom_expr)
    monkeypatch.setattr(Condition, "to_string", _boom_cond)

    signature = refiner._analysis_signature([ReturnInfo(address="0x1000", value=value, conditions=[cond])])
    deduped = refiner._deduplicate_return_infos(
        [
            ReturnInfo(address="0x1000", value=value, conditions=[cond]),
            ReturnInfo(address="0x1000", value=value, conditions=[cond]),
        ]
    )

    assert len(signature) == 1
    assert len(deduped) == 1


def test_bounded_call_refiner_unrolls_direct_self_recursion_without_diverging():
    n = _param()
    recursive_placeholder = "call_out_of_scope:sum#0"
    recursive_info = DeferredCallInfo(
        placeholder_name=recursive_placeholder,
        target_ref=CallTargetRef.from_name("sum"),
        arguments=[Expression.binary_op("INT_SUB", n, _const(1))],
        sequence=0,
    )
    recursive_value = Expression.binary_op(
        "INT_ADD",
        _deferred_unknown(recursive_info),
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
        recursive_placeholder: recursive_info
    }

    refiner = BoundedCallRefiner(
        lambda target_ref: analysis if target_ref == CallTargetRef.from_name("sum") else None,
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
    b_info = DeferredCallInfo(
        placeholder_name=b_placeholder,
        target_ref=CallTargetRef.from_name("B"),
        arguments=[Expression.binary_op("INT_SUB", n, _const(1))],
        sequence=0,
    )
    a_info = DeferredCallInfo(
        placeholder_name=a_placeholder,
        target_ref=CallTargetRef.from_name("A"),
        arguments=[Expression.binary_op("INT_SUB", n, _const(1))],
        sequence=0,
    )

    analysis_a = create_mock_analysis(
        "A",
        parameters=[{"name": "n", "index": 0, "data_type": "int", "size": 4}],
        returns=[
            ReturnInfo(address="0x2000", value=_const(0), conditions=[_cond("INT_SLESSEQUAL", n, _const(0))]),
            ReturnInfo(
                address="0x2004",
                value=Expression.binary_op("INT_ADD", _deferred_unknown(b_info), _const(1)),
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
                value=Expression.binary_op("INT_ADD", _deferred_unknown(a_info), _const(2)),
                conditions=[_cond("INT_SLESS", _const(0), n)],
            ),
        ],
    )
    analysis_a.deferred_calls = {
        b_placeholder: b_info
    }
    analysis_b.deferred_calls = {
        a_placeholder: a_info
    }

    analyses = {
        CallTargetRef.from_name("A"): analysis_a,
        CallTargetRef.from_name("B"): analysis_b,
    }
    refiner = BoundedCallRefiner(
        lambda target_ref: analyses.get(target_ref),
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
    fanout_info = DeferredCallInfo(
        placeholder_name=placeholder,
        target_ref=CallTargetRef.from_name("callee"),
        arguments=[n],
        sequence=0,
    )
    analysis = create_mock_analysis(
        "fanout",
        parameters=[{"name": "n", "index": 0, "data_type": "int", "size": 4}],
        returns=[
            ReturnInfo(
                address="0x4000",
                value=_deferred_unknown(fanout_info),
                conditions=[_cond("INT_SLESS", _const(0), n)],
            )
        ],
    )
    analysis.deferred_calls = {
        placeholder: fanout_info
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
        lambda target_ref: callee if target_ref == CallTargetRef.from_name("callee") else None,
        max_unroll=1,
        max_cases=3,
        debug=False,
    )

    changed = refiner.refine_analysis(analysis)

    assert changed is True
    assert len(analysis.returns) == 3


def test_bounded_call_refiner_resolves_object_centric_indirect_targets():
    selector = _param("selector", 0)
    lhs = _param("lhs", 1)
    rhs = _param("rhs", 2)
    placeholder = "call_out_of_scope:UNKNOWN_FUNC#0"
    deferred_info = DeferredCallInfo(
        placeholder_name=placeholder,
        target_ref=CallTargetRef.unknown(),
        arguments=[lhs, rhs],
        call_target_expr=Expression.phi(
            [
                (
                    _cond(
                        "INT_EQUAL",
                        Expression.binary_op("INT_AND", selector, _const(1)),
                        _const(0),
                    ),
                    Expression.constant(0x401100, size=8),
                ),
                (
                    _cond(
                        "INT_NOTEQUAL",
                        Expression.binary_op("INT_AND", selector, _const(1)),
                        _const(0),
                    ),
                    Expression.constant(0x401200, size=8),
                ),
            ]
        ),
        sequence=0,
    )
    caller = create_mock_analysis(
        "wrapper",
        parameters=[
            {"name": "selector", "index": 0, "data_type": "int", "size": 4},
            {"name": "lhs", "index": 1, "data_type": "int", "size": 4},
            {"name": "rhs", "index": 2, "data_type": "int", "size": 4},
        ],
        returns=[ReturnInfo(address="0x6000", value=_deferred_unknown(deferred_info), conditions=[])],
        return_type="int",
    )
    caller.deferred_calls = {placeholder: deferred_info}

    add_analysis = create_mock_analysis(
        "ptr_op_add",
        parameters=[{"name": "a", "index": 0, "data_type": "int", "size": 4}, {"name": "b", "index": 1, "data_type": "int", "size": 4}],
        returns=[
            ReturnInfo(
                address="0x401110",
                value=Expression.binary_op("INT_ADD", _param("a", 0), _param("b", 1)),
                conditions=[],
            )
        ],
    )
    xor_analysis = create_mock_analysis(
        "ptr_op_xor",
        parameters=[{"name": "a", "index": 0, "data_type": "int", "size": 4}, {"name": "b", "index": 1, "data_type": "int", "size": 4}],
        returns=[
            ReturnInfo(
                address="0x401210",
                value=Expression.binary_op("INT_XOR", _param("a", 0), _param("b", 1)),
                conditions=[],
            )
        ],
    )

    def provide_analysis(target_ref):
        if target_ref.address_offset == 0x401100:
            return add_analysis
        if target_ref.address_offset == 0x401200:
            return xor_analysis
        return None

    refiner = BoundedCallRefiner(
        provide_analysis,
        max_unroll=1,
        max_cases=8,
        debug=False,
    )

    changed = refiner.refine_analysis(caller)

    assert changed is True
    assert sorted(ret.value.to_string() for ret in caller.returns) == ["(lhs + rhs)", "(lhs ^ rhs)"]


def test_bounded_call_refiner_lowers_substituted_symbolic_post_state_reads():
    trace = Expression.parameter("trace", 0, size=8)
    start = Expression.parameter("start", 1, size=4)
    limit = Expression.parameter("limit", 2, size=4)
    steps_addr = Expression.binary_op("INT_ADD", trace, _const(4, size=8))
    callee_parameters = [
        {"name": "trace", "index": 0, "size": 8},
        {"name": "start", "index": 1, "size": 4},
        {"name": "limit", "index": 2, "size": 4},
    ]

    trace_nonnull = _cond("INT_NOTEQUAL", trace, Expression.constant(0, size=8))
    loop_active = _cond("INT_SLESS", start, limit)
    final_iter = _cond("INT_EQUAL", limit, Expression.binary_op("INT_ADD", start, _const(1)))
    odd_iteration = _cond(
        "INT_NOTEQUAL",
        Expression.binary_op("INT_AND", start, _const(1)),
        _const(0),
    )

    callee = create_mock_analysis(
        "callee",
        parameters=[
            {"name": "trace", "index": 0, "data_type": "int *", "size": 8},
            {"name": "start", "index": 1, "data_type": "int", "size": 4},
            {"name": "limit", "index": 2, "data_type": "int", "size": 4},
        ],
        returns=[
            ReturnInfo(
                address="0x5000",
                value=Expression.binary_op(
                    "INT_ADD",
                    post_state_read_expression_for_location(
                        CanonicalLocation("trace", 0, 4),
                        callee_parameters,
                        symbolic=True,
                    ),
                    post_state_read_expression_for_location(
                        CanonicalLocation("trace", 4, 4),
                        callee_parameters,
                        symbolic=True,
                    ),
                ),
                conditions=[trace_nonnull, loop_active, odd_iteration, final_iter],
            )
        ],
        return_type="int",
    )
    callee.effect_summary = EffectSummary(
        parameter_names=["trace", "start", "limit"],
        effects=[
            StoreEffect(
                location=CanonicalLocation("trace", 0, 4),
                value=Expression.binary_op("INT_ADD", Expression.memory(trace, size=4), Expression.unary_op("INT_2COMP", start)),
                conditions=[trace_nonnull, loop_active, odd_iteration, final_iter],
                order_key=1,
            ),
            StoreEffect(
                location=CanonicalLocation("trace", 4, 4),
                value=Expression.binary_op("INT_ADD", Expression.memory(steps_addr, size=4), _const(1)),
                conditions=[trace_nonnull, loop_active, final_iter],
                order_key=2,
            ),
        ],
    )

    placeholder = "call_out_of_scope:callee#0"
    deferred_info = DeferredCallInfo(
        placeholder_name=placeholder,
        target_ref=CallTargetRef.from_name("callee"),
        arguments=[
            _param("param_1", 0, size=8),
            _param("param_2", 1, size=4),
            _param("param_3", 2, size=4),
        ],
        sequence=0,
    )
    caller = create_mock_analysis(
        "wrapper",
        parameters=[
            {"name": "param_1", "index": 0, "data_type": "int *", "size": 8},
            {"name": "param_2", "index": 1, "data_type": "int", "size": 4},
            {"name": "param_3", "index": 2, "data_type": "int", "size": 4},
        ],
        returns=[
            ReturnInfo(
                address="0x4000",
                value=_deferred_unknown(deferred_info),
                conditions=[_cond("INT_NOTEQUAL", _param("param_1", 0, size=8), Expression.constant(0, size=8))],
            )
        ],
        return_type="int",
    )
    caller.deferred_calls = {
        placeholder: deferred_info
    }

    refiner = BoundedCallRefiner(
        lambda target_ref: callee if target_ref == CallTargetRef.from_name("callee") else None,
        max_unroll=1,
        max_cases=16,
        debug=False,
    )

    changed = refiner.refine_analysis(caller)

    assert changed is True
    assert all(
        not expression_contains_post_state_reads(ret.value)
        for ret in caller.returns
    )
