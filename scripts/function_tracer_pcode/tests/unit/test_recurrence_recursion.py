from scripts.function_tracer_pcode.tests.unit._recurrence_fixtures import *

def test_structural_recurrence_summarizer_recovers_linear_self_recursion():
    param = _param()
    unknown = Expression.unknown(
        "call_out_of_scope:fc_recursive_sum",
        runtime_ref=UnknownValueRef.out_of_scope_call(
            reason="call_out_of_scope",
            target_ref=CallTargetRef.from_name("fc_recursive_sum"),
            display_hint="fc_recursive_sum",
        ),
    )
    recursive_value = Expression.binary_op("INT_ADD", unknown, param)
    analysis = create_mock_analysis(
        "fc_recursive_sum",
        return_type="int",
        parameters=[{"name": "param_1", "index": 0, "data_type": "int", "size": 4}],
        returns=[
            ReturnInfo(address="0x1000", value=_const(0), conditions=[]),
            ReturnInfo(
                address="0x1004",
                value=recursive_value,
                conditions=[_cond("INT_SLESS", _const(0), param)],
            ),
        ],
    )
    summarizer = StructuralRecurrenceSummarizer(
        _FakeTracer(
            "fc_recursive_sum",
            Expression.binary_op("INT_SUB", param, _const(1)),
        ),
        debug=False,
    )

    summary = summarizer.try_summarize_function(
        _FakeFunction("fc_recursive_sum"),
        _FakeHighFunction([
            _FakeCallOp("fc_recursive_sum", Expression.binary_op("INT_SUB", param, _const(1))),
        ]),
        analysis,
    )

    assert summary is not None
    summarized_returns, note = summary
    assert note == "linear_self_recursion_summary"
    assert len(summarized_returns) == 2
    assert all("call_out_of_scope" not in ret.value.to_string() for ret in summarized_returns)
    base_case = next(ret for ret in summarized_returns if ret.value.to_string() == "0")
    assert base_case.retained_exact_return_ref[0] == "retained_exact_return_v1"
    assert any(">> 1" in ret.value.to_string() for ret in summarized_returns if ret.value.to_string() != "0")
    recursive_case = next(ret for ret in summarized_returns if ret.value.to_string() != "0")
    assert recursive_case.retained_exact_return_ref is None
    assert recursive_case.conditions[0].to_string() == "(0 < param_1)"

def test_structural_recurrence_summarizer_accepts_masked_counter_recursion():
    param = _param(size=8)
    masked_param = Expression.binary_op("INT_AND", param, _const(0xFFFFFFFF, size=8))
    unknown = Expression.unknown(
        "call_out_of_scope:fc_recursive_sum",
        runtime_ref=UnknownValueRef.out_of_scope_call(
            reason="call_out_of_scope",
            target_ref=CallTargetRef.from_name("fc_recursive_sum"),
            display_hint="fc_recursive_sum",
        ),
    )
    recursive_value = Expression.binary_op("INT_ADD", unknown, masked_param)
    analysis = create_mock_analysis(
        "fc_recursive_sum",
        return_type="int",
        parameters=[{"name": "param_1", "index": 0, "data_type": "int", "size": 8}],
        returns=[
            ReturnInfo(address="0x1000", value=_const(0), conditions=[]),
            ReturnInfo(
                address="0x1004",
                value=recursive_value,
                conditions=[_cond("INT_SLESS", _const(0), param)],
            ),
        ],
    )
    summarizer = StructuralRecurrenceSummarizer(
        _FakeTracer(
            "fc_recursive_sum",
            Expression.binary_op("INT_ADD", masked_param, _const(0xFFFFFFFF, size=8)),
        ),
        debug=False,
    )

    summary = summarizer.try_summarize_function(
        _FakeFunction("fc_recursive_sum"),
        _FakeHighFunction([
            _FakeCallOp(
                "fc_recursive_sum",
                Expression.binary_op("INT_ADD", masked_param, _const(0xFFFFFFFF, size=8)),
            ),
        ]),
        analysis,
    )

    assert summary is not None
    summarized_returns, note = summary
    assert note == "linear_self_recursion_summary"
    assert all("call_out_of_scope" not in ret.value.to_string() for ret in summarized_returns)
    recursive_case = next(ret for ret in summarized_returns if ret.value.to_string() != "0")
    assert "param_1" in recursive_case.value.to_string()
