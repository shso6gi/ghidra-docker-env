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
    DeferredCallRef,
    DeferredCallInfo,
    Expression,
    LocationBaseRef,
    PcodeOpRef,
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


def _loc(name: str, offset: int, size: int) -> CanonicalLocation:
    return CanonicalLocation(
        base_ref=LocationBaseRef.parameter(name, index=0),
        offset=offset,
        size=size,
    )


def _reg_storage(name: str, size: int = 8) -> dict:
    return {
        "is_register": True,
        "space_name": "register",
        "offset": 0,
        "size": size,
        "size_bits": size * 8,
        "register_name": name,
        "base_register_name": name,
        "base_register_offset": 0,
        "base_register_size": size,
        "base_register_size_bits": size * 8,
        "bit_offset_in_base": 0,
    }


def _deferred_unknown(info: DeferredCallInfo) -> Expression:
    return Expression.unknown(info.placeholder_name, runtime_ref=info.unknown_ref)


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


def test_bounded_call_refiner_prefers_argument_specialized_callee_lookup():
    deferred = DeferredCallInfo(
        placeholder_name="call_out_of_scope:callee#0",
        target_ref=CallTargetRef.from_name("callee"),
        arguments=[Expression.binary_op("INT_ADD", _param(), _const(4))],
        sequence=0,
    )
    caller = create_mock_analysis(
        "caller",
        parameters=[{"name": "n", "index": 0, "data_type": "int", "size": 4}],
        returns=[ReturnInfo(address="0x1000", value=_deferred_unknown(deferred), conditions=[])],
    )
    caller.deferred_calls = {
        deferred.deferred_call_ref.stable_key(): deferred,
    }
    callee = create_mock_analysis(
        "callee",
        parameters=[{"name": "x", "index": 0, "data_type": "int", "size": 4}],
        returns=[ReturnInfo(address="0x2000", value=_param("x", 0), conditions=[])],
    )
    captured = []

    def _provider(target_ref, args=None):
        captured.append((target_ref, list(args or [])))
        if target_ref == CallTargetRef.from_name("callee"):
            return callee
        return None

    refiner = BoundedCallRefiner(_provider, max_unroll=1, max_cases=8, debug=False)

    changed = refiner.refine_analysis(caller)

    assert changed is True
    assert captured
    assert captured[0][1] == deferred.arguments
    assert caller.returns[0].value.to_string() == "(n + 4)"


def test_bounded_call_refiner_does_not_rebind_fully_specialized_callee_analysis():
    caller_a = Expression.parameter("caller_a", index=1, data_type="int", size=4)
    caller_b = Expression.parameter("caller_b", index=2, data_type="int", size=4)
    deferred = DeferredCallInfo(
        placeholder_name="call_out_of_scope:callee#0",
        target_ref=CallTargetRef.from_name("callee"),
        arguments=[caller_a, caller_b],
        sequence=0,
    )
    caller = create_mock_analysis(
        "caller",
        parameters=[
            {"name": "target", "index": 0, "data_type": "int *", "size": 8},
            {"name": "caller_a", "index": 1, "data_type": "int", "size": 4},
            {"name": "caller_b", "index": 2, "data_type": "int", "size": 4},
        ],
        returns=[ReturnInfo(address="0x1000", value=_deferred_unknown(deferred), conditions=[])],
    )
    caller.deferred_calls = {deferred.deferred_call_ref.stable_key(): deferred}
    callee = create_mock_analysis(
        "callee",
        parameters=[
            {"name": "x", "index": 0, "data_type": "int", "size": 4},
            {"name": "y", "index": 1, "data_type": "int", "size": 4},
        ],
        returns=[
            ReturnInfo(
                address="0x2000",
                value=Expression.binary_op("INT_XOR", caller_a, caller_b),
                conditions=[],
            )
        ],
    )
    callee.analysis_scope_key = (
        "analysis_scope",
        ("function", "callee"),
        ((0, ("bound", "caller_a")), (1, ("bound", "caller_b"))),
        (),
    )

    refiner = BoundedCallRefiner(
        lambda target_ref, args=None: callee
        if target_ref == CallTargetRef.from_name("callee") and list(args or []) == deferred.arguments
        else None,
        max_unroll=1,
        max_cases=8,
        debug=False,
    )

    assert refiner.refine_analysis(caller) is True
    value = caller.returns[0].value
    assert value.operator == "INT_XOR"
    assert value.operands[0].name == "caller_a"
    assert value.operands[1].name == "caller_b"


def test_bounded_call_refiner_realigns_noisy_deferred_arguments_to_callee_parameters():
    base = Expression.parameter("param_1", index=0, data_type="int *", size=8)
    count = Expression.parameter("param_2", index=1, data_type="int", size=4)
    noisy_count = Expression.binary_op("INT_ADD", count, _const(0xFFFFFFFD))
    deferred = DeferredCallInfo(
        placeholder_name="call_out_of_scope:lmb_sum_prefix_loop#0",
        target_ref=CallTargetRef.from_name("lmb_sum_prefix_loop"),
        arguments=[noisy_count, base, count],
        sequence=0,
    )
    caller = create_mock_analysis(
        "lmb_sum_prefix_wrong_tail",
        parameters=[
            {"name": "param_1", "index": 0, "data_type": "int *", "size": 8, "storage": _reg_storage("x0", size=8)},
            {"name": "param_2", "index": 1, "data_type": "int", "size": 4, "storage": _reg_storage("w1", size=4)},
        ],
        returns=[ReturnInfo(address="0x1000", value=_deferred_unknown(deferred), conditions=[])],
    )
    caller.deferred_calls = {deferred.deferred_call_ref.stable_key(): deferred}
    callee = create_mock_analysis(
        "lmb_sum_prefix_loop",
        parameters=[
            {"name": "param_1", "index": 0, "data_type": "int *", "size": 8, "storage": _reg_storage("x0", size=8)},
            {"name": "param_2", "index": 1, "data_type": "int", "size": 4, "storage": _reg_storage("w1", size=4)},
        ],
        returns=[
            ReturnInfo(
                address="0x2000",
                value=Expression.binary_op(
                    "INT_ADD",
                    Expression.parameter("param_1", index=0, data_type="int *", size=8),
                    Expression.parameter("param_2", index=1, data_type="int", size=4),
                ),
                conditions=[],
            )
        ],
    )

    refiner = BoundedCallRefiner(
        lambda target_ref, _args=None: callee if target_ref == CallTargetRef.from_name("lmb_sum_prefix_loop") else None,
        max_unroll=1,
        max_cases=8,
        debug=False,
    )

    changed = refiner.refine_analysis(caller)

    assert changed is True
    assert caller.returns[0].value.to_string() == "(param_1 + param_2)"


def test_bounded_call_refiner_realigns_same_arity_misordered_arguments():
    base = Expression.parameter("param_1", index=0, data_type="int *", size=8)
    count = Expression.parameter("param_2", index=1, data_type="int", size=4)
    deferred = DeferredCallInfo(
        placeholder_name="call_out_of_scope:lmb_sum_prefix_loop#0",
        target_ref=CallTargetRef.from_name("lmb_sum_prefix_loop"),
        arguments=[count, base],
        sequence=0,
    )
    caller = create_mock_analysis(
        "caller",
        parameters=[
            {"name": "param_1", "index": 0, "data_type": "int *", "size": 8, "storage": _reg_storage("x0", size=8)},
            {"name": "param_2", "index": 1, "data_type": "int", "size": 4, "storage": _reg_storage("w1", size=4)},
        ],
        returns=[ReturnInfo(address="0x1000", value=_deferred_unknown(deferred), conditions=[])],
    )
    caller.deferred_calls = {deferred.deferred_call_ref.stable_key(): deferred}
    callee = create_mock_analysis(
        "lmb_sum_prefix_loop",
        parameters=[
            {"name": "param_1", "index": 0, "data_type": "int *", "size": 8, "storage": _reg_storage("x0", size=8)},
            {"name": "param_2", "index": 1, "data_type": "int", "size": 4, "storage": _reg_storage("w1", size=4)},
        ],
        returns=[
            ReturnInfo(
                address="0x2000",
                value=Expression.binary_op(
                    "INT_ADD",
                    Expression.parameter("param_1", index=0, data_type="int *", size=8),
                    Expression.parameter("param_2", index=1, data_type="int", size=4),
                ),
                conditions=[],
            )
        ],
    )
    refiner = BoundedCallRefiner(
        lambda target_ref, _args=None: callee if target_ref == CallTargetRef.from_name("lmb_sum_prefix_loop") else None,
        max_unroll=1,
        max_cases=8,
        debug=False,
    )

    changed = refiner.refine_analysis(caller)

    assert changed is True
    assert caller.returns[0].value.to_string() == "(param_1 + param_2)"


def test_bounded_call_refiner_rejects_positional_only_same_arity_alignment():
    deferred = DeferredCallInfo(
        placeholder_name="call_out_of_scope:callee#0",
        target_ref=CallTargetRef.from_name("callee"),
        arguments=[_const(10), _const(20)],
        sequence=0,
    )
    caller = create_mock_analysis(
        "caller",
        parameters=[
            {"name": "lhs", "index": 0, "data_type": "int", "size": 4},
            {"name": "rhs", "index": 1, "data_type": "int", "size": 4},
        ],
        returns=[ReturnInfo(address="0x1000", value=_deferred_unknown(deferred), conditions=[])],
    )
    caller.deferred_calls = {deferred.deferred_call_ref.stable_key(): deferred}
    callee = create_mock_analysis(
        "callee",
        parameters=[
            {"name": "x", "index": 0, "data_type": "int", "size": 4},
            {"name": "y", "index": 1, "data_type": "int", "size": 4},
        ],
        returns=[ReturnInfo(address="0x2000", value=_param("x", 0), conditions=[])],
    )
    refiner = BoundedCallRefiner(
        lambda target_ref, _args=None: callee if target_ref == CallTargetRef.from_name("callee") else None,
        max_unroll=1,
        max_cases=8,
        debug=False,
    )

    changed = refiner.refine_analysis(caller)

    assert changed is False
    assert caller.returns[0].value.to_string() == "call_out_of_scope:callee#0"
    assert "bounded_call_refinement_argument_alignment_failed" in caller.analysis_notes


def test_bounded_call_refiner_rejects_non_pcode_name_index_only_alignment():
    deferred = DeferredCallInfo(
        placeholder_name="call_out_of_scope:callee#0",
        target_ref=CallTargetRef.from_name("callee"),
        arguments=[_param("x", 0), _param("y", 1)],
        sequence=0,
    )
    caller = create_mock_analysis(
        "caller",
        parameters=[
            {"name": "x", "index": 0, "data_type": "int", "size": 4},
            {"name": "y", "index": 1, "data_type": "int", "size": 4},
        ],
        returns=[ReturnInfo(address="0x1000", value=_deferred_unknown(deferred), conditions=[])],
    )
    caller.deferred_calls = {deferred.deferred_call_ref.stable_key(): deferred}
    callee = create_mock_analysis(
        "callee",
        parameters=[
            {"name": "x", "index": 0, "data_type": "int", "size": 4},
            {"name": "y", "index": 1, "data_type": "int", "size": 4},
        ],
        returns=[ReturnInfo(address="0x2000", value=_param("x", 0), conditions=[])],
    )
    refiner = BoundedCallRefiner(
        lambda target_ref, _args=None: callee if target_ref == CallTargetRef.from_name("callee") else None,
        max_unroll=1,
        max_cases=8,
        debug=False,
    )

    changed = refiner.refine_analysis(caller)

    assert changed is False
    assert caller.returns[0].value.to_string() == "call_out_of_scope:callee#0"
    assert "bounded_call_refinement_argument_alignment_failed" in caller.analysis_notes


def test_bounded_call_refiner_does_not_synthesize_missing_arg_from_formal_storage():
    deferred = DeferredCallInfo(
        placeholder_name="call_out_of_scope:callee#0",
        target_ref=CallTargetRef.from_name("callee"),
        arguments=[],
        sequence=0,
    )
    caller = create_mock_analysis(
        "caller",
        parameters=[
            {
                "name": "live_in",
                "index": 0,
                "data_type": "int",
                "size": 4,
                "storage": _reg_storage("a0", size=4),
            }
        ],
        returns=[ReturnInfo(address="0x1000", value=_deferred_unknown(deferred), conditions=[])],
    )
    caller.deferred_calls = {deferred.deferred_call_ref.stable_key(): deferred}
    callee = create_mock_analysis(
        "callee",
        parameters=[
            {
                "name": "x",
                "index": 0,
                "data_type": "int",
                "size": 4,
                "storage": _reg_storage("a0", size=4),
            }
        ],
        returns=[ReturnInfo(address="0x2000", value=Expression.parameter("x", index=0, data_type="int", size=4), conditions=[])],
    )
    refiner = BoundedCallRefiner(
        lambda target_ref, _args=None: callee if target_ref == CallTargetRef.from_name("callee") else None,
        max_unroll=1,
        max_cases=8,
        debug=False,
    )

    changed = refiner.refine_analysis(caller)

    assert changed is False
    assert caller.returns[0].value.to_string() == "call_out_of_scope:callee#0"
    assert "bounded_call_refinement_argument_alignment_failed" in caller.analysis_notes


def test_bounded_call_refiner_records_unresolved_target_reason():
    deferred = DeferredCallInfo(
        placeholder_name="call_out_of_scope:callee#0",
        target_ref=CallTargetRef.from_name("callee"),
        arguments=[_const(10)],
        sequence=0,
    )
    caller = create_mock_analysis(
        "caller",
        parameters=[],
        returns=[ReturnInfo(address="0x1000", value=_deferred_unknown(deferred), conditions=[])],
    )
    caller.deferred_calls = {deferred.deferred_call_ref.stable_key(): deferred}
    refiner = BoundedCallRefiner(
        lambda _target_ref, _args=None: None,
        max_unroll=1,
        max_cases=8,
        debug=False,
    )

    changed = refiner.refine_analysis(caller)

    assert changed is False
    assert "bounded_call_refinement_deferred_target_unresolved" in caller.analysis_notes


def test_bounded_call_refinement_failure_notes_are_decisive_sat_unsafe():
    analysis = create_mock_analysis(
        "caller",
        parameters=[],
        returns=[ReturnInfo(address="0x1000", value=_const(1), conditions=[])],
    )

    for note in (
        "bounded_call_refinement_argument_alignment_failed",
        "bounded_call_refinement_deferred_target_unresolved",
        "bounded_call_refinement_return_summary_unusable",
    ):
        analysis.analysis_notes = [note]
        assert note in analysis.get_decisive_sat_unsafety_reasons()


def test_bounded_call_refiner_allows_single_argument_expression_binding():
    count = Expression.parameter("param_2", index=1, data_type="int", size=4)
    deferred = DeferredCallInfo(
        placeholder_name="call_out_of_scope:callee#0",
        target_ref=CallTargetRef.from_name("callee"),
        arguments=[Expression.binary_op("INT_SUB", count, _const(1))],
        sequence=0,
    )
    caller = create_mock_analysis(
        "caller",
        parameters=[{"name": "param_2", "index": 1, "data_type": "int", "size": 4}],
        returns=[ReturnInfo(address="0x1000", value=_deferred_unknown(deferred), conditions=[])],
    )
    caller.deferred_calls = {deferred.deferred_call_ref.stable_key(): deferred}
    callee = create_mock_analysis(
        "callee",
        parameters=[{"name": "param_2", "index": 1, "data_type": "int", "size": 4}],
        returns=[ReturnInfo(address="0x2000", value=count, conditions=[])],
    )
    refiner = BoundedCallRefiner(
        lambda target_ref, _args=None: callee if target_ref == CallTargetRef.from_name("callee") else None,
        max_unroll=1,
        max_cases=8,
        debug=False,
    )

    changed = refiner.refine_analysis(caller)

    assert changed is True
    assert caller.returns[0].value.to_string() == "(param_2 - 1)"


def test_bounded_call_refiner_synthesizes_deferred_call_inside_phi():
    n = _param("n", 0)
    deferred = DeferredCallInfo(
        placeholder_name="call_out_of_scope:callee#0",
        target_ref=CallTargetRef.from_name("callee"),
        arguments=[n],
        sequence=0,
    )
    phi_value = Expression.phi(
        [
            (_cond("INT_EQUAL", n, _const(0)), _const(0)),
            (None, _deferred_unknown(deferred)),
        ]
    )
    caller = create_mock_analysis(
        "caller",
        parameters=[{"name": "n", "index": 0, "data_type": "int", "size": 4}],
        returns=[ReturnInfo(address="0x1000", value=phi_value, conditions=[])],
    )
    caller.deferred_calls = {deferred.deferred_call_ref.stable_key(): deferred}
    callee = create_mock_analysis(
        "callee",
        parameters=[{"name": "n", "index": 0, "data_type": "int", "size": 4}],
        returns=[ReturnInfo(address="0x2000", value=Expression.binary_op("INT_ADD", n, _const(1)), conditions=[])],
    )
    refiner = BoundedCallRefiner(
        lambda target_ref, _args=None: callee if target_ref == CallTargetRef.from_name("callee") else None,
        max_unroll=1,
        max_cases=8,
        debug=False,
    )

    changed = refiner.refine_analysis(caller)

    assert changed is True
    assert caller.deferred_calls == {}
    assert "call_out_of_scope" not in caller.returns[0].value.to_string()


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
            {
                "name": "lhs",
                "index": 1,
                "data_type": "int",
                "size": 4,
                "storage": {"is_register": True, "register_name": "r1", "size": 4, "size_bits": 32},
            },
            {
                "name": "rhs",
                "index": 2,
                "data_type": "int",
                "size": 4,
                "storage": {"is_register": True, "register_name": "r2", "size": 4, "size_bits": 32},
            },
        ],
        returns=[ReturnInfo(address="0x6000", value=_deferred_unknown(deferred_info), conditions=[])],
        return_type="int",
    )
    caller.deferred_calls = {placeholder: deferred_info}

    add_analysis = create_mock_analysis(
        "ptr_op_add",
        parameters=[
            {
                "name": "a",
                "index": 0,
                "data_type": "int",
                "size": 4,
                "storage": {"is_register": True, "register_name": "r1", "size": 4, "size_bits": 32},
            },
            {
                "name": "b",
                "index": 1,
                "data_type": "int",
                "size": 4,
                "storage": {"is_register": True, "register_name": "r2", "size": 4, "size_bits": 32},
            },
        ],
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
        parameters=[
            {
                "name": "a",
                "index": 0,
                "data_type": "int",
                "size": 4,
                "storage": {"is_register": True, "register_name": "r1", "size": 4, "size_bits": 32},
            },
            {
                "name": "b",
                "index": 1,
                "data_type": "int",
                "size": 4,
                "storage": {"is_register": True, "register_name": "r2", "size": 4, "size_bits": 32},
            },
        ],
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


def test_bounded_call_refiner_preserves_pcode_callsite_argument_order_for_indirect_targets():
    selector = _param("selector", 0)
    lhs = _param("lhs", 1)
    rhs = _param("rhs", 2)
    deferred_info = DeferredCallInfo(
        placeholder_name="call_out_of_scope:UNKNOWN_FUNC#0",
        target_ref=CallTargetRef.unknown(),
        arguments=[lhs, rhs],
        call_target_expr=Expression.phi(
            [
                (
                    _cond("INT_EQUAL", Expression.binary_op("INT_AND", selector, _const(1)), _const(0)),
                    Expression.constant(0x401100, size=8),
                ),
                (
                    _cond("INT_NOTEQUAL", Expression.binary_op("INT_AND", selector, _const(1)), _const(0)),
                    Expression.constant(0x401200, size=8),
                ),
            ]
        ),
        deferred_call_ref=DeferredCallRef(
            pcode_op_ref=PcodeOpRef(address_offset=0x6000, seq_time=9, seq_order=0, mnemonic="CALLIND"),
            target_ref=CallTargetRef.unknown(),
            sequence=0,
        ),
    )
    caller = create_mock_analysis(
        "ptr_apply_callback.specialized",
        parameters=[
            {
                "name": "op",
                "index": 0,
                "data_type": "int (*)(int,int)",
                "size": 8,
                "storage": {"is_register": True, "register_name": "x0", "base_register_name": "x0", "size": 8, "size_bits": 64},
            },
            {
                "name": "lhs",
                "index": 1,
                "data_type": "int",
                "size": 4,
                "storage": {"is_register": True, "register_name": "w1", "base_register_name": "x1", "size": 4, "size_bits": 32},
            },
            {
                "name": "rhs",
                "index": 2,
                "data_type": "int",
                "size": 4,
                "storage": {"is_register": True, "register_name": "w2", "base_register_name": "x2", "size": 4, "size_bits": 32},
            },
        ],
        returns=[ReturnInfo(address="0x6000", value=_deferred_unknown(deferred_info), conditions=[])],
        return_type="int",
    )
    caller.deferred_calls = {deferred_info.deferred_call_ref.stable_key(): deferred_info}

    add_analysis = create_mock_analysis(
        "ptr_op_add",
        parameters=[
            {
                "name": "a",
                "index": 0,
                "data_type": "int",
                "size": 4,
                "storage": {"is_register": True, "register_name": "w0", "base_register_name": "x0", "size": 4, "size_bits": 32},
            },
            {
                "name": "b",
                "index": 1,
                "data_type": "int",
                "size": 4,
                "storage": {"is_register": True, "register_name": "w1", "base_register_name": "x1", "size": 4, "size_bits": 32},
            },
        ],
        returns=[ReturnInfo(address="0x401110", value=Expression.binary_op("INT_ADD", _param("a", 0), _param("b", 1)), conditions=[])],
    )
    xor_analysis = create_mock_analysis(
        "ptr_op_xor",
        parameters=[
            {
                "name": "a",
                "index": 0,
                "data_type": "int",
                "size": 4,
                "storage": {"is_register": True, "register_name": "w0", "base_register_name": "x0", "size": 4, "size_bits": 32},
            },
            {
                "name": "b",
                "index": 1,
                "data_type": "int",
                "size": 4,
                "storage": {"is_register": True, "register_name": "w1", "base_register_name": "x1", "size": 4, "size_bits": 32},
            },
        ],
        returns=[ReturnInfo(address="0x401210", value=Expression.binary_op("INT_XOR", _param("a", 0), _param("b", 1)), conditions=[])],
    )

    def provide_analysis(target_ref):
        if target_ref.address_offset == 0x401100:
            return add_analysis
        if target_ref.address_offset == 0x401200:
            return xor_analysis
        return None

    refiner = BoundedCallRefiner(provide_analysis, max_unroll=1, max_cases=8, debug=False)

    changed = refiner.refine_analysis(caller)

    assert changed is True
    assert sorted(ret.value.to_string() for ret in caller.returns) == ["(lhs + rhs)", "(lhs ^ rhs)"]


def test_bounded_call_refiner_missing_pcode_mnemonic_is_not_ordered_callsite_evidence():
    lhs = _param("lhs", 0)
    rhs = _param("rhs", 1)
    deferred_info = DeferredCallInfo(
        placeholder_name="call_out_of_scope:callee#0",
        target_ref=CallTargetRef.from_name("callee"),
        arguments=[lhs, rhs],
        deferred_call_ref=DeferredCallRef(
            pcode_op_ref=PcodeOpRef(address_offset=0x6100, seq_time=3, seq_order=0, mnemonic=None),
            target_ref=CallTargetRef.from_name("callee"),
            sequence=0,
        ),
    )
    caller_parameters = [
        {"name": "lhs", "index": 0, "data_type": "int", "size": 4},
        {"name": "rhs", "index": 1, "data_type": "int", "size": 4},
    ]
    callee_parameters = [
        {"name": "a", "index": 0, "data_type": "int", "size": 4},
        {"name": "b", "index": 1, "data_type": "int", "size": 4},
    ]
    refiner = BoundedCallRefiner(lambda _target_ref: None, max_unroll=1, max_cases=8, debug=False)

    aligned = refiner._align_deferred_arguments_to_callee(
        deferred_info,
        caller_parameters,
        callee_parameters,
    )

    assert aligned == []


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
            {
                "name": "trace",
                "index": 0,
                "data_type": "int *",
                "size": 8,
                "storage": {"is_register": True, "register_name": "r0", "size": 8, "size_bits": 64},
            },
            {
                "name": "start",
                "index": 1,
                "data_type": "int",
                "size": 4,
                "storage": {"is_register": True, "register_name": "r1", "size": 4, "size_bits": 32},
            },
            {
                "name": "limit",
                "index": 2,
                "data_type": "int",
                "size": 4,
                "storage": {"is_register": True, "register_name": "r2", "size": 4, "size_bits": 32},
            },
        ],
        returns=[
            ReturnInfo(
                address="0x5000",
                value=Expression.binary_op(
                    "INT_ADD",
                    post_state_read_expression_for_location(
                        _loc("trace", 0, 4),
                        callee_parameters,
                        symbolic=True,
                    ),
                    post_state_read_expression_for_location(
                        _loc("trace", 4, 4),
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
                location=_loc("trace", 0, 4),
                value=Expression.binary_op("INT_ADD", Expression.memory(trace, size=4), Expression.unary_op("INT_2COMP", start)),
                conditions=[trace_nonnull, loop_active, odd_iteration, final_iter],
                order_key=1,
            ),
            StoreEffect(
                location=_loc("trace", 4, 4),
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
            {
                "name": "param_1",
                "index": 0,
                "data_type": "int *",
                "size": 8,
                "storage": {"is_register": True, "register_name": "r0", "size": 8, "size_bits": 64},
            },
            {
                "name": "param_2",
                "index": 1,
                "data_type": "int",
                "size": 4,
                "storage": {"is_register": True, "register_name": "r1", "size": 4, "size_bits": 32},
            },
            {
                "name": "param_3",
                "index": 2,
                "data_type": "int",
                "size": 4,
                "storage": {"is_register": True, "register_name": "r2", "size": 4, "size_bits": 32},
            },
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
