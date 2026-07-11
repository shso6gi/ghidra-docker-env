from scripts.function_tracer_pcode.tests.unit._recurrence_fixtures import *

def test_readonly_reduction_summary_accepts_sign_extended_load_when_return_width_is_low_lane():
    params = [
        {"name": "param_1", "index": 0, "data_type": "int *", "size": 8},
        {"name": "param_2", "index": 1, "data_type": "int", "size": 4, "is_signed": True},
    ]
    pointer_expr = Expression.parameter("param_1", index=0, data_type="int *", size=8)
    count_expr = Expression.parameter("param_2", index=1, data_type="int", size=4)
    analysis = create_mock_analysis(
        "signed_load_prefix",
        return_type="int",
        parameters=params,
        returns=[
            ReturnInfo(
                address="0x1000",
                value=_const(-300),
                conditions=[_cond("INT_EQUAL", pointer_expr, Expression.constant(0, size=8))],
            ),
            ReturnInfo(
                address="0x1004",
                value=_const(-300),
                conditions=[
                    _cond("INT_NOTEQUAL", pointer_expr, Expression.constant(0, size=8)),
                    _cond("INT_SLESSEQUAL", count_expr, _const(0)),
                ],
            ),
            ReturnInfo(
                address="0x1008",
                value=Expression.unknown("phi_circular"),
                conditions=[
                    _cond("INT_NOTEQUAL", pointer_expr, Expression.constant(0, size=8)),
                    _cond("INT_SLESS", _const(0), count_expr),
                ],
            ),
        ],
    )
    analysis.returns[2].value.size = 4

    ptr_param = _FakeVarnode("param_1", size=8, expr=pointer_expr)
    count_param = _FakeVarnode("param_2", size=4, expr=count_expr)
    zero32 = _FakeVarnode("zero32", size=4, expr=Expression.constant(0, 4))
    one32 = _FakeVarnode("one32", size=4, expr=Expression.constant(1, 4))
    four64 = _FakeVarnode("four64", size=8, expr=Expression.constant(4, 8))
    ram_space = _FakeVarnode("ram", size=8, expr=Expression.constant(0, 8))

    idx_phi = _FakeVarnode("idx_phi", size=4, high=_FakeHighVar("idx"))
    idx_next = _FakeVarnode("idx_next", size=4)
    idx_add_op = _FakePcodeOp("INT_ADD", [idx_phi, one32], idx_next)
    idx_phi_op = _FakePcodeOp("MULTIEQUAL", [zero32, idx_next], idx_phi)

    idx_sext = _FakeVarnode("idx_sext", size=8)
    idx_sext_op = _FakePcodeOp("INT_SEXT", [idx_phi], idx_sext)
    scaled_idx = _FakeVarnode("scaled_idx", size=8)
    scale_op = _FakePcodeOp("INT_MULT", [idx_sext, four64], scaled_idx)
    addr = _FakeVarnode("addr", size=8)
    addr_op = _FakePcodeOp("INT_ADD", [ptr_param, scaled_idx], addr)
    load_value = _FakeVarnode("load_value", size=4)
    load_op = _FakePcodeOp("LOAD", [ram_space, addr], load_value)
    signed_load = _FakeVarnode("signed_load", size=8)
    signed_load_op = _FakePcodeOp("INT_SEXT", [load_value], signed_load)

    acc_phi = _FakeVarnode("acc_phi", size=8, high=_FakeHighVar("acc"))
    acc_next = _FakeVarnode("acc_next", size=8)
    acc_add_op = _FakePcodeOp("INT_ADD", [acc_phi, signed_load], acc_next)
    acc_phi_op = _FakePcodeOp("MULTIEQUAL", [zero32, acc_next], acc_phi)

    high_function = _FakeHighFunction(
        [
            idx_add_op,
            idx_phi_op,
            idx_sext_op,
            scale_op,
            addr_op,
            load_op,
            signed_load_op,
            acc_add_op,
            acc_phi_op,
        ]
    )
    tracer = _FakeTracer("unused", _const(0))
    tracer.trace_varnode = lambda varnode, *args, **kwargs: getattr(varnode, "_expr", None)

    summarizer = StructuralRecurrenceSummarizer(tracer, debug=False)
    summary = summarizer.try_summarize_function(
        _FakeFunction("signed_load_prefix"),
        high_function,
        analysis,
    )

    assert summary is not None
    summarized_returns, note = summary
    assert note == "readonly_pointer_reduction_summary"
    readonly_return = next(ret for ret in summarized_returns if ret.value.expr_type == ExpressionType.INTRINSIC)
    proof = readonly_return.value.runtime_ref.accumulator_proof
    assert proof is not None
    assert proof.result_size == 4
    assert proof.element_size == 4
    assert proof.start_index == 0
    assert tuple(term.byte_offset for term in (proof.full_terms_for_count_value(2) or ())) == (0, 4)

def test_structural_recurrence_summarizer_candidate_probe_accepts_readonly_reduction_shape():
    params = [
        {"name": "param_1", "index": 0, "data_type": "int *", "size": 8},
        {"name": "param_2", "index": 1, "data_type": "int", "size": 4, "is_signed": True},
    ]
    analysis = create_mock_analysis(
        "ptr_sum_window",
        return_type="int",
        parameters=params,
        returns=[
            ReturnInfo(
                address="0x1000",
                value=_const(-300),
                conditions=[
                    _cond(
                        "INT_EQUAL",
                        Expression.parameter("param_1", index=0, data_type="int *", size=8),
                        Expression.constant(0, size=8),
                    )
                ],
            ),
            ReturnInfo(
                address="0x1004",
                value=_const(-300),
                conditions=[
                    _cond(
                        "INT_NOTEQUAL",
                        Expression.parameter("param_1", index=0, data_type="int *", size=8),
                        Expression.constant(0, size=8),
                    ),
                    _cond("INT_SLESSEQUAL", _param("param_2"), _const(0)),
                ],
            ),
            ReturnInfo(
                address="0x1008",
                value=Expression.unknown("phi_circular"),
                conditions=[
                    _cond(
                        "INT_NOTEQUAL",
                        Expression.parameter("param_1", index=0, data_type="int *", size=8),
                        Expression.constant(0, size=8),
                    ),
                    _cond("INT_SLESS", _const(0), _param("param_2")),
                ],
            ),
        ],
    )

    ptr_param = _FakeVarnode(
        "param_1",
        size=8,
        expr=Expression.parameter("param_1", index=0, data_type="int *", size=8),
    )
    zero32 = _FakeVarnode("zero32", size=4, expr=Expression.constant(0, 4))
    one32 = _FakeVarnode("one32", size=4, expr=Expression.constant(1, 4))
    four64 = _FakeVarnode("four64", size=8, expr=Expression.constant(4, 8))
    ram_space = _FakeVarnode("ram", size=8, expr=Expression.constant(0, 8))

    idx_high = _FakeHighVar("idx")
    idx_phi = _FakeVarnode("idx_phi", size=4, high=idx_high)
    idx_next = _FakeVarnode("idx_next", size=4)
    _FakePcodeOp("INT_ADD", [idx_phi, one32], idx_next)
    idx_phi_op = _FakePcodeOp("MULTIEQUAL", [zero32, idx_next], idx_phi)

    addr = _FakeVarnode("addr", size=8)
    ptradd_op = _FakePcodeOp("PTRADD", [ptr_param, idx_phi, four64], addr)
    load_value = _FakeVarnode("load_value", size=4)
    load_op = _FakePcodeOp("LOAD", [ram_space, addr], load_value)

    acc_high = _FakeHighVar("acc")
    acc_phi = _FakeVarnode("acc_phi", size=4, high=acc_high)
    acc_next = _FakeVarnode("acc_next", size=4)
    acc_add_op = _FakePcodeOp("INT_ADD", [acc_phi, load_value], acc_next)
    acc_phi_op = _FakePcodeOp("MULTIEQUAL", [zero32, acc_next], acc_phi)

    high_function = _FakeHighFunction([idx_phi_op, ptradd_op, load_op, acc_add_op, acc_phi_op])
    tracer = _FakeTracer("unused", _const(0))
    tracer.trace_varnode = lambda varnode, *args, **kwargs: getattr(varnode, "_expr", None)

    summarizer = StructuralRecurrenceSummarizer(tracer, debug=False)

    assert summarizer.has_summary_candidate(_FakeFunction("ptr_sum_window"), high_function, analysis) is True

def test_structural_recurrence_summarizer_declines_readonly_reduction_from_exact_count_only():
    params = [
        {"name": "param_1", "index": 0, "data_type": "long", "size": 8},
        {"name": "param_2", "index": 1, "data_type": "uint", "size": 4, "is_signed": False},
    ]
    count_param = Expression.parameter("param_2", index=1, data_type="uint", size=4)
    widened_count = Expression.unary_op("INT_ZEXT", count_param)
    widened_count.size = 8
    exact_one_expr = Expression.binary_op(
        "INT_EQUAL",
        Expression.binary_op("INT_SUB", widened_count, Expression.constant(1, size=8)),
        Expression.constant(0, size=8),
    )
    analysis = create_mock_analysis(
        "ptr_sum_window",
        return_type="int",
        parameters=params,
        returns=[
            ReturnInfo(
                address="0x1000",
                value=_const(-300),
                conditions=[
                    _cond(
                        "INT_EQUAL",
                        Expression.parameter("param_1", index=0, data_type="long", size=8),
                        Expression.constant(0, size=8),
                    )
                ],
            ),
            ReturnInfo(
                address="0x1004",
                value=_const(-300),
                conditions=[
                    _cond(
                        "INT_NOTEQUAL",
                        Expression.parameter("param_1", index=0, data_type="long", size=8),
                        Expression.constant(0, size=8),
                    ),
                    _cond("INT_SLESSEQUAL", count_param, _const(0)),
                ],
            ),
            ReturnInfo(
                address="0x1008",
                value=Expression.binary_op("INT_ADD", _mem("param_1", 0), _const(0)),
                conditions=[
                    _cond(
                        "INT_NOTEQUAL",
                        Expression.parameter("param_1", index=0, data_type="long", size=8),
                        Expression.constant(0, size=8),
                    ),
                    _cond("INT_SLESS", _const(0), count_param),
                    _cond("INT_SLESS", count_param, _const(8)),
                    Condition(exact_one_expr, False),
                ],
            ),
        ],
    )

    summarizer = StructuralRecurrenceSummarizer(_FakeTracer("unused", _const(0)), debug=False)
    summary = summarizer.try_summarize_function(
        _FakeFunction("ptr_sum_window"),
        _FakeHighFunction([]),
        analysis,
    )

    assert summary is None

def test_readonly_reduction_summary_preserves_nonzero_start_offset_object_centrically():
    params = [
        {"name": "param_1", "index": 0, "data_type": "int *", "size": 8},
        {"name": "param_2", "index": 1, "data_type": "int", "size": 4, "is_signed": True},
    ]
    ptr_param = Expression.parameter("param_1", index=0, data_type="int *", size=8)
    count_param = Expression.parameter("param_2", index=1, data_type="int", size=4)
    analysis = create_mock_analysis(
        "ptr_sum_window",
        return_type="int",
        parameters=params,
        returns=[
            ReturnInfo(
                address="0x1000",
                value=_const(0),
                conditions=[_cond("INT_EQUAL", ptr_param, Expression.constant(0, size=8))],
            ),
            ReturnInfo(
                address="0x1004",
                value=_const(0),
                conditions=[
                    _cond("INT_NOTEQUAL", ptr_param, Expression.constant(0, size=8)),
                    _cond("INT_SLESSEQUAL", count_param, _const(1)),
                ],
            ),
            ReturnInfo(
                address="0x1008",
                value=Expression.unknown("phi_circular"),
                conditions=[
                    _cond("INT_NOTEQUAL", ptr_param, Expression.constant(0, size=8)),
                    _cond("INT_SLESS", _const(1), count_param),
                ],
            ),
        ],
    )

    ptr_varnode = _FakeVarnode(
        "param_1",
        size=8,
        expr=Expression.parameter("param_1", index=0, data_type="int *", size=8),
    )
    one32 = _FakeVarnode("one32", size=4, expr=Expression.constant(1, 4))
    four64 = _FakeVarnode("four64", size=8, expr=Expression.constant(4, 8))
    ram_space = _FakeVarnode("ram", size=8, expr=Expression.constant(0, 8))

    idx_high = _FakeHighVar("idx")
    idx_phi = _FakeVarnode("idx_phi", size=4, high=idx_high)
    idx_next = _FakeVarnode("idx_next", size=4)
    idx_add_op = _FakePcodeOp("INT_ADD", [idx_phi, one32], idx_next)
    idx_phi_op = _FakePcodeOp("MULTIEQUAL", [one32, idx_next], idx_phi)

    addr = _FakeVarnode("addr", size=8)
    ptradd_op = _FakePcodeOp("PTRADD", [ptr_varnode, idx_phi, four64], addr)
    load_value = _FakeVarnode("load_value", size=4)
    load_op = _FakePcodeOp("LOAD", [ram_space, addr], load_value)

    acc_high = _FakeHighVar("acc")
    acc_phi = _FakeVarnode("acc_phi", size=4, high=acc_high)
    acc_next = _FakeVarnode("acc_next", size=4)
    zero32 = _FakeVarnode("zero32", size=4, expr=Expression.constant(0, 4))
    acc_add_op = _FakePcodeOp("INT_ADD", [acc_phi, load_value], acc_next)
    acc_phi_op = _FakePcodeOp("MULTIEQUAL", [zero32, acc_next], acc_phi)

    high_function = _FakeHighFunction([idx_add_op, idx_phi_op, ptradd_op, load_op, acc_add_op, acc_phi_op])
    tracer = _FakeTracer("unused", _const(0))
    tracer.trace_varnode = lambda varnode, *args, **kwargs: getattr(varnode, "_expr", None)
    summarizer = StructuralRecurrenceSummarizer(tracer, debug=False)
    summary = summarizer.try_summarize_function(
        _FakeFunction("ptr_sum_window"),
        high_function,
        analysis,
    )

    assert summary is not None
    summarized_returns, note = summary
    assert note == "readonly_pointer_reduction_summary"
    positive_case = next(ret for ret in summarized_returns if ret.value.expr_type == ExpressionType.INTRINSIC)
    runtime_ref = positive_case.value.runtime_ref
    assert isinstance(runtime_ref, ReadonlyReductionRef)
    assert runtime_ref.reduction_kind == "memory_sum"
    assert runtime_ref.start_offset == 4
    assert runtime_ref.stride == 4
    assert isinstance(runtime_ref.loop_summary, LoopSummaryRef)
    assert runtime_ref.loop_summary.loop_var_unit == "element_index"
    assert runtime_ref.loop_summary.start_expr.equals(Expression.constant(1, size=4))
    assert runtime_ref.loop_summary.step_expr.equals(Expression.constant(1, size=4))
    assert runtime_ref.loop_summary.term_descriptor.start_offset == 0
    assert runtime_ref.loop_summary.term_descriptor.stride == 4
    assert runtime_ref.loop_summary.seed_terms == ()
    assert runtime_ref.loop_summary.witnesses == runtime_ref.semantic_witnesses
    assert loop_summary_method_b_key(runtime_ref.loop_summary) is not None
    assert runtime_ref.semantic_key() is not None
    assert runtime_ref.semantic_witnesses[:2] == (
        ReadonlyReductionWitness(
            exact_count=1,
            terms=(),
        ),
        ReadonlyReductionWitness(
            exact_count=2,
            terms=(ReadonlyReductionTermRef(byte_offset=4, access_size=4),),
        ),
    )
    assert [cond.to_string() for cond in positive_case.conditions] == ["(param_1 != 0)", "(1 < param_2)"]

def test_readonly_reduction_summary_records_prefix_seed_terms_from_accumulator_init():
    params = [
        {"name": "param_1", "index": 0, "data_type": "int *", "size": 8},
        {"name": "param_2", "index": 1, "data_type": "int", "size": 4, "is_signed": True},
    ]
    ptr_param = Expression.parameter("param_1", index=0, data_type="int *", size=8)
    count_param = Expression.parameter("param_2", index=1, data_type="int", size=4)
    analysis = create_mock_analysis(
        "ptr_sum_window",
        return_type="int",
        parameters=params,
        returns=[
            ReturnInfo(
                address="0x1000",
                value=_const(0),
                conditions=[_cond("INT_EQUAL", ptr_param, Expression.constant(0, size=8))],
            ),
            ReturnInfo(
                address="0x1004",
                value=_mem("param_1", 0),
                conditions=[
                    _cond("INT_NOTEQUAL", ptr_param, Expression.constant(0, size=8)),
                    _cond("INT_SLESSEQUAL", count_param, _const(1)),
                ],
            ),
            ReturnInfo(
                address="0x1008",
                value=Expression.unknown("phi_circular"),
                conditions=[
                    _cond("INT_NOTEQUAL", ptr_param, Expression.constant(0, size=8)),
                    _cond("INT_SLESS", _const(1), count_param),
                ],
            ),
        ],
    )

    ptr_varnode = _FakeVarnode(
        "param_1",
        size=8,
        expr=Expression.parameter("param_1", index=0, data_type="int *", size=8),
    )
    one32 = _FakeVarnode("one32", size=4, expr=Expression.constant(1, 4))
    four64 = _FakeVarnode("four64", size=8, expr=Expression.constant(4, 8))
    ram_space = _FakeVarnode("ram", size=8, expr=Expression.constant(0, 8))

    idx_high = _FakeHighVar("idx")
    idx_phi = _FakeVarnode("idx_phi", size=4, high=idx_high)
    idx_next = _FakeVarnode("idx_next", size=4)
    idx_add_op = _FakePcodeOp("INT_ADD", [idx_phi, one32], idx_next)
    idx_phi_op = _FakePcodeOp("MULTIEQUAL", [one32, idx_next], idx_phi)

    addr = _FakeVarnode("addr", size=8)
    ptradd_op = _FakePcodeOp("PTRADD", [ptr_varnode, idx_phi, four64], addr)
    load_value = _FakeVarnode("load_value", size=4)
    load_op = _FakePcodeOp("LOAD", [ram_space, addr], load_value)

    acc_high = _FakeHighVar("acc")
    acc_phi = _FakeVarnode("acc_phi", size=4, high=acc_high)
    acc_next = _FakeVarnode("acc_next", size=4)
    acc_seed = _FakeVarnode("acc_seed", size=4, expr=_mem("param_1", 0))
    acc_add_op = _FakePcodeOp("INT_ADD", [acc_phi, load_value], acc_next)
    acc_phi_op = _FakePcodeOp("MULTIEQUAL", [acc_seed, acc_next], acc_phi)

    high_function = _FakeHighFunction([idx_add_op, idx_phi_op, ptradd_op, load_op, acc_add_op, acc_phi_op])
    tracer = _FakeTracer("unused", _const(0))
    tracer.trace_varnode = lambda varnode, *args, **kwargs: getattr(varnode, "_expr", None)
    summarizer = StructuralRecurrenceSummarizer(tracer, debug=False)
    summary = summarizer.try_summarize_function(
        _FakeFunction("ptr_sum_window"),
        high_function,
        analysis,
    )

    assert summary is not None
    summarized_returns, note = summary
    assert note == "readonly_pointer_reduction_summary"
    positive_case = next(ret for ret in summarized_returns if ret.value.expr_type == ExpressionType.INTRINSIC)
    runtime_ref = positive_case.value.runtime_ref
    loop_summary = runtime_ref.loop_summary
    assert loop_summary.seed_terms == (ReadonlyReductionTermRef(byte_offset=0, access_size=4),)

    full_summary = LoopSummaryRef(
        start_expr=Expression.constant(0, size=4),
        limit_expr=loop_summary.limit_expr,
        step_expr=loop_summary.step_expr,
        term_descriptor=loop_summary.term_descriptor,
        side_effect_profile=loop_summary.side_effect_profile,
        loop_var_unit=loop_summary.loop_var_unit,
    )
    assert loop_summary_method_b_key(loop_summary) == loop_summary_method_b_key(full_summary)

def test_readonly_reduction_summary_preserves_non_prefix_pre_loop_seed_terms():
    params = [
        {"name": "param_1", "index": 0, "data_type": "int *", "size": 8},
        {"name": "param_2", "index": 1, "data_type": "int", "size": 4, "is_signed": True},
    ]
    ptr_param = Expression.parameter("param_1", index=0, data_type="int *", size=8)
    count_param = Expression.parameter("param_2", index=1, data_type="int", size=4)
    analysis = create_mock_analysis(
        "ptr_sum_wrong_tail",
        return_type="int",
        parameters=params,
        returns=[
            ReturnInfo(
                address="0x1000",
                value=_const(-300),
                conditions=[_cond("INT_EQUAL", ptr_param, Expression.constant(0, size=8))],
            ),
            ReturnInfo(
                address="0x1004",
                value=Expression.unknown("phi_circular"),
                conditions=[
                    _cond("INT_NOTEQUAL", ptr_param, Expression.constant(0, size=8)),
                    _cond("INT_SLESS", _const(3), count_param),
                ],
            ),
        ],
    )

    ptr_varnode = _FakeVarnode(
        "param_1",
        size=8,
        expr=Expression.parameter("param_1", index=0, data_type="int *", size=8),
    )
    one32 = _FakeVarnode("one32", size=4, expr=Expression.constant(1, 4))
    three32 = _FakeVarnode("three32", size=4, expr=Expression.constant(3, 4))
    four64 = _FakeVarnode("four64", size=8, expr=Expression.constant(4, 8))
    ram_space = _FakeVarnode("ram", size=8, expr=Expression.constant(0, 8))

    idx_high = _FakeHighVar("idx")
    idx_phi = _FakeVarnode("idx_phi", size=4, high=idx_high)
    idx_next = _FakeVarnode("idx_next", size=4)
    idx_add_op = _FakePcodeOp("INT_ADD", [idx_phi, one32], idx_next)
    idx_phi_op = _FakePcodeOp("MULTIEQUAL", [three32, idx_next], idx_phi)

    addr = _FakeVarnode("addr", size=8)
    ptradd_op = _FakePcodeOp("PTRADD", [ptr_varnode, idx_phi, four64], addr)
    load_value = _FakeVarnode("load_value", size=4)
    load_op = _FakePcodeOp("LOAD", [ram_space, addr], load_value)

    acc_high = _FakeHighVar("acc")
    acc_phi = _FakeVarnode("acc_phi", size=4, high=acc_high)
    acc_next = _FakeVarnode("acc_next", size=4)
    acc_seed_expr = Expression.binary_op("INT_ADD", _mem("param_1", 0), _mem("param_1", 8))
    acc_seed = _FakeVarnode("acc_seed", size=4, expr=acc_seed_expr)
    acc_add_op = _FakePcodeOp("INT_ADD", [acc_phi, load_value], acc_next)
    acc_phi_op = _FakePcodeOp("MULTIEQUAL", [acc_seed, acc_next], acc_phi)

    high_function = _FakeHighFunction([idx_add_op, idx_phi_op, ptradd_op, load_op, acc_add_op, acc_phi_op])
    tracer = _FakeTracer("unused", _const(0))
    tracer.trace_varnode = lambda varnode, *args, **kwargs: getattr(varnode, "_expr", None)
    summarizer = StructuralRecurrenceSummarizer(tracer, debug=False)
    summary = summarizer.try_summarize_function(
        _FakeFunction("ptr_sum_wrong_tail"),
        high_function,
        analysis,
    )

    assert summary is not None
    summarized_returns, note = summary
    assert note == "readonly_pointer_reduction_summary"
    positive_case = next(ret for ret in summarized_returns if ret.value.expr_type == ExpressionType.INTRINSIC)
    runtime_ref = positive_case.value.runtime_ref
    proof = runtime_ref.accumulator_proof
    assert tuple(term.byte_offset for term in proof.seed_terms) == (0, 8)
    assert tuple(term.byte_offset for term in (proof.full_terms_for_count_value(4) or ())) == (0, 8, 12)
    assert tuple(term.byte_offset for term in runtime_ref.loop_summary.seed_terms) == (0, 8)

    prefix_summary = LoopSummaryRef(
        start_expr=Expression.constant(0, size=4),
        limit_expr=runtime_ref.loop_summary.limit_expr,
        step_expr=runtime_ref.loop_summary.step_expr,
        term_descriptor=runtime_ref.loop_summary.term_descriptor,
        side_effect_profile=runtime_ref.loop_summary.side_effect_profile,
        loop_var_unit=runtime_ref.loop_summary.loop_var_unit,
    )
    assert loop_summary_method_b_key(runtime_ref.loop_summary) != loop_summary_method_b_key(prefix_summary)

def test_vectorized_readonly_seed_recovery_uses_exact_wrong_tail_terms():
    pointer_param = {"name": "param_1", "index": 0, "data_type": "int *", "size": 8}
    count_param = {"name": "param_2", "index": 1, "data_type": "int", "size": 4, "is_signed": True}
    ptr_expr = Expression.parameter("param_1", index=0, data_type="int *", size=8)
    count_expr = Expression.parameter("param_2", index=1, data_type="int", size=4)
    vector_region = [
        _cond("INT_NOTEQUAL", ptr_expr, _const(0, size=8)),
        _cond("INT_SLESS", _const(0), count_expr),
    ]
    exact_four = ReturnInfo(
        address="0x2000",
        value=Expression.binary_op(
            "INT_ADD",
            _mem("param_1", 12),
            Expression.binary_op("INT_ADD", _mem("param_1", 8), _mem("param_1", 0)),
        ),
        conditions=vector_region + [_cond("INT_EQUAL", count_expr, _const(4))],
    )
    analysis = create_mock_analysis(
        "vectorized_wrong_tail_seed",
        return_type="int",
        parameters=[pointer_param, count_param],
        returns=[exact_four],
    )
    summarizer = StructuralRecurrenceSummarizer(_FakeTracer("unused", _const(0)), debug=False)

    seed_terms = summarizer._vector_prefix_seed_terms_from_exact_returns(
        analysis,
        pointer_param,
        count_param,
        vector_region,
        start_index=3,
        element_size=4,
    )

    assert seed_terms is not None
    assert tuple(term.byte_offset for term in seed_terms) == (0, 8)

def test_proof_backed_readonly_summary_subsumes_same_site_unresolved_artifact():
    count_expr = Expression.parameter("param_2", index=1, data_type="int", size=4)
    ptr_expr = Expression.parameter("param_1", index=0, data_type="int *", size=8)
    return_ref = PcodeOpRef(address_offset=0x1004, seq_time=47, seq_order=0, mnemonic="RETURN")
    conditions = [
        _cond("INT_NOTEQUAL", ptr_expr, Expression.constant(0, size=8)),
        _cond("INT_SLESS", _const(3), count_expr),
    ]
    proof = _readonly_accumulator_proof(
        base_ref=LocationBaseRef.parameter("param_1", index=0),
        count_expr=count_expr,
        stride=4,
        element_size=4,
        start_offset=12,
        start_index=3,
        seed_terms=(
            ReadonlyReductionTermRef(byte_offset=0, access_size=4),
            ReadonlyReductionTermRef(byte_offset=8, access_size=4),
        ),
        return_op_refs=(return_ref,),
        return_region_value_proven=True,
    )
    replacement_ref = proof.to_readonly_reduction_ref()
    assert replacement_ref is not None
    unresolved_ret = ReturnInfo(
        address="0x1004",
        value=Expression.binary_op(
            "INT_ADD",
            _mem("param_1", 12),
            Expression.unknown("phi_circular"),
        ),
        conditions=list(conditions),
        pcode_op_ref=return_ref,
    )
    different_region_ret = ReturnInfo(
        address="0x1004",
        value=unresolved_ret.value,
        conditions=list(conditions) + [_cond("INT_EQUAL", count_expr, _const(4))],
        pcode_op_ref=return_ref,
    )
    summary_excluding_count4 = list(conditions) + [_cond("INT_EQUAL", count_expr, _const(4), negated=True)]
    unproven_proof = replace(proof, return_region_value_proven=False)
    unproven_ref = unproven_proof.to_readonly_reduction_ref()
    summarizer = StructuralRecurrenceSummarizer(_FakeTracer("unused", _const(0)), debug=False)

    assert summarizer._readonly_unresolved_preserved_return_is_subsumed_by_replacement(
        unresolved_ret,
        conditions,
        proof,
        replacement_ref,
    )
    assert not summarizer._readonly_unresolved_preserved_return_is_subsumed_by_replacement(
        different_region_ret,
        summary_excluding_count4,
        proof,
        replacement_ref,
    )
    assert not summarizer._readonly_unresolved_preserved_return_is_subsumed_by_replacement(
        unresolved_ret,
        conditions,
        unproven_proof,
        unproven_ref,
    )

def test_vectorized_region_proof_subsumes_broad_materialized_return_shape():
    pointer_param = {
        "name": "param_1",
        "index": 0,
        "data_type": "int *",
        "size": 8,
    }
    count_param = {
        "name": "param_2",
        "index": 1,
        "data_type": "int",
        "size": 4,
        "is_signed": True,
    }
    ptr_expr = Expression.parameter("param_1", index=0, data_type="int *", size=8)
    count_expr = Expression.parameter("param_2", index=1, data_type="int", size=4)
    ret = ReturnInfo(
        address="0x1004",
        pcode_time=10,
        pcode_order=1,
        pcode_op_ref=PcodeOpRef(address_offset=0x1004, seq_time=10, seq_order=1, mnemonic="RETURN"),
        value=Expression.binary_op(
            "INT_ADD",
            _mem("param_1", 0),
            _mem("param_1", 4),
        ),
        conditions=[
            _cond("INT_NOTEQUAL", ptr_expr, Expression.constant(0, size=8)),
            _cond("INT_SLESS", _const(3), count_expr),
        ],
    )
    analysis = create_mock_analysis(
        "vectorized_region_contract_like",
        return_type="int",
        parameters=[pointer_param, count_param],
        returns=[ret],
    )
    proof = _readonly_accumulator_proof(
        base_ref=LocationBaseRef.parameter("param_1", index=0),
        count_expr=count_expr,
        stride=4,
        element_size=4,
        start_offset=12,
        start_index=3,
        seed_terms=(
            ReadonlyReductionTermRef(byte_offset=0, access_size=4),
            ReadonlyReductionTermRef(byte_offset=8, access_size=4),
        ),
        return_op_refs=(PcodeOpRef(address_offset=0x1004, seq_time=10, seq_order=1, mnemonic="RETURN"),),
        return_region_value_proven=True,
        source="vectorized_readonly_prefix_sum",
    )
    broad_positive_conditions = [
        _cond("INT_NOTEQUAL", ptr_expr, Expression.constant(0, size=8)),
        _cond("INT_SLESS", _const(0), count_expr),
    ]
    positive_conditions = [
        _cond("INT_NOTEQUAL", ptr_expr, Expression.constant(0, size=8)),
        _cond("INT_SLESS", _const(3), count_expr),
    ]
    summarizer = StructuralRecurrenceSummarizer(_FakeTracer("unused", _const(0)), debug=False)

    assert summarizer._readonly_reduction_replaceable_positive_returns(
        analysis,
        pointer_param,
        count_param,
        broad_positive_conditions,
        positive_conditions,
        expected_signed=True,
        accumulator_proof=proof,
    ) == [ret]

def test_readonly_witness_synthesis_does_not_override_existing_exact_return():
    pointer_param = {
        "name": "param_1",
        "index": 0,
        "data_type": "int *",
        "size": 8,
    }
    count_param = {
        "name": "param_2",
        "index": 1,
        "data_type": "int",
        "size": 4,
        "is_signed": True,
    }
    ptr_expr = Expression.parameter("param_1", index=0, data_type="int *", size=8)
    count_expr = Expression.parameter("param_2", index=1, data_type="int", size=4)
    wrong_tail_four = ReturnInfo(
        address="0x1004",
        value=Expression.binary_op(
            "INT_ADD",
            _mem("param_1", 12),
            Expression.binary_op("INT_ADD", _mem("param_1", 8), _mem("param_1", 0)),
        ),
        conditions=[
            _cond("INT_NOTEQUAL", ptr_expr, Expression.constant(0, size=8)),
            _cond("INT_EQUAL", count_expr, _const(4)),
        ],
    )
    analysis = create_mock_analysis(
        "witness_synthesis_conflict",
        return_type="int",
        parameters=[pointer_param, count_param],
        returns=[wrong_tail_four],
    )
    reduction_ref = ReadonlyReductionRef(
        reduction_kind="memory_sum",
        pointer_base_ref=LocationBaseRef.parameter("param_1", index=0),
        count_parameter_name="param_2",
        count_parameter_index=1,
        stride=4,
        element_size=4,
        result_size=4,
        semantic_witnesses=(
            ReadonlyReductionWitness(
                exact_count=4,
                terms=(
                    ReadonlyReductionTermRef(byte_offset=0, access_size=4),
                    ReadonlyReductionTermRef(byte_offset=4, access_size=4),
                    ReadonlyReductionTermRef(byte_offset=8, access_size=4),
                    ReadonlyReductionTermRef(byte_offset=12, access_size=4),
                ),
            ),
        ),
    )
    summarizer = StructuralRecurrenceSummarizer(_FakeTracer("unused", _const(0)), debug=False)

    synthesized = summarizer._synthesize_exact_returns_from_readonly_witnesses(
        analysis,
        pointer_param,
        count_param,
        broad_positive_conditions=[
            _cond("INT_NOTEQUAL", ptr_expr, Expression.constant(0, size=8)),
            _cond("INT_SLESS", _const(0), count_expr),
        ],
        summary_positive_conditions=[
            _cond("INT_NOTEQUAL", ptr_expr, Expression.constant(0, size=8)),
            _cond("INT_SLESS", _const(3), count_expr),
        ],
        existing_returns=[wrong_tail_four],
        reduction_ref=reduction_ref,
        result_size=4,
    )

    assert synthesized == [wrong_tail_four]

def test_readonly_candidate_selection_prefers_seeded_contract_over_declared_signedness():
    pointer_param = {
        "name": "param_1",
        "index": 0,
        "data_type": "int *",
        "size": 8,
        "is_signed": False,
    }
    count_param = {
        "name": "param_2",
        "index": 1,
        "data_type": "ulong",
        "size": 8,
        "is_signed": False,
    }
    ptr_expr = Expression.parameter("param_1", index=0, data_type="int *", size=8)
    count_expr = Expression.parameter("param_2", index=1, data_type="ulong", size=8)
    masked_count = Expression.binary_op(
        "INT_AND",
        Expression.constant(0xFFFFFFFF, size=8),
        count_expr,
    )
    masked_count.size = 8
    exact_four_expr = Expression.binary_op(
        "INT_ADD",
        Expression.binary_op(
            "INT_SUB",
            masked_count,
            Expression.constant(3, size=8),
        ),
        Expression.constant(-1, size=8),
    )
    exact_four_expr.size = 8
    exact_four = ReturnInfo(
        address="0x100cb4",
        pcode_time=35,
        pcode_order=2,
        pcode_op_ref=PcodeOpRef(address_offset=0x100CB4, seq_time=35, seq_order=2, mnemonic="RETURN"),
        value=Expression.binary_op(
            "INT_ADD",
            _mem("param_1", 12),
            Expression.binary_op("INT_ADD", _mem("param_1", 8), _mem("param_1", 0)),
        ),
        conditions=[
            _cond("INT_NOTEQUAL", ptr_expr, Expression.constant(0, size=8)),
            _cond("INT_SLESS", Expression.constant(0, size=8), count_expr),
            _cond("INT_SLESSEQUAL", Expression.constant(4, size=8), count_expr),
            _cond("INT_EQUAL", exact_four_expr, Expression.constant(0, size=8)),
        ],
    )
    analysis = FunctionReturnAnalysis(
        function_name="readonly_wrong_tail_seeded_candidate_like",
        entry_point="0x100c80",
        parameters=[pointer_param, count_param],
        returns=[exact_four],
    )
    prefix_proof = _readonly_accumulator_proof(
        base_ref=LocationBaseRef.parameter("param_1", index=0),
        count_expr=count_expr,
        stride=4,
        element_size=4,
        start_offset=0,
        start_index=0,
        return_op_refs=(PcodeOpRef(address_offset=0x100CB4, seq_time=35, seq_order=2, mnemonic="RETURN"),),
        return_region_value_proven=True,
    )
    seeded_proof = _readonly_accumulator_proof(
        base_ref=LocationBaseRef.parameter("param_1", index=0),
        count_expr=count_expr,
        stride=4,
        element_size=4,
        start_offset=12,
        start_index=3,
        seed_terms=(
            ReadonlyReductionTermRef(byte_offset=0, access_size=4),
            ReadonlyReductionTermRef(byte_offset=8, access_size=4),
        ),
        return_op_refs=(PcodeOpRef(address_offset=0x100CB4, seq_time=35, seq_order=2, mnemonic="RETURN"),),
        return_region_value_proven=True,
    )
    broad_positive_conditions = [
        _cond("INT_NOTEQUAL", ptr_expr, Expression.constant(0, size=8)),
        _cond("INT_SLESS", Expression.constant(0, size=8), count_expr),
    ]
    positive_conditions = [
        _cond("INT_NOTEQUAL", ptr_expr, Expression.constant(0, size=8)),
        _cond("INT_SLESS", Expression.constant(3, size=8), count_expr),
    ]
    summarizer = StructuralRecurrenceSummarizer(_FakeTracer("unused", _const(0)), debug=False)

    assert summarizer._readonly_reduction_replaceable_positive_returns(
        analysis,
        pointer_param,
        count_param,
        broad_positive_conditions,
        positive_conditions,
        expected_signed=True,
        declared_signedness=False,
        accumulator_proof=seeded_proof,
    ) == [exact_four]
    assert summarizer._readonly_reduction_replaceable_positive_returns(
        analysis,
        pointer_param,
        count_param,
        broad_positive_conditions,
        positive_conditions,
        expected_signed=False,
        declared_signedness=False,
        accumulator_proof=prefix_proof,
    ) == []

    selected = summarizer._select_readonly_reduction_candidate(
        analysis,
        pointer_param,
        count_param,
        [
            (False, broad_positive_conditions, prefix_proof, positive_conditions, [exact_four]),
            (True, broad_positive_conditions, seeded_proof, positive_conditions, [exact_four]),
        ],
    )

    assert selected is not None
    assert selected[2] is seeded_proof

def test_preserved_readonly_summary_is_dropped_when_return_site_proof_replaces_contract():
    pointer_param = {
        "name": "param_1",
        "index": 0,
        "data_type": "int *",
        "size": 8,
        "is_signed": False,
    }
    count_expr = Expression.parameter("param_2", index=1, data_type="int", size=4)
    ptr_expr = Expression.parameter("param_1", index=0, data_type="int *", size=8)
    site_ref = PcodeOpRef(address_offset=0x1004, seq_time=35, seq_order=2, mnemonic="RETURN")
    prefix_proof = _readonly_accumulator_proof(
        base_ref=LocationBaseRef.parameter("param_1", index=0),
        count_expr=count_expr,
        stride=4,
        element_size=4,
        start_offset=0,
        start_index=0,
        return_op_refs=(site_ref,),
        return_region_value_proven=True,
    )
    seeded_tail_proof = _readonly_accumulator_proof(
        base_ref=LocationBaseRef.parameter("param_1", index=0),
        count_expr=count_expr,
        stride=4,
        element_size=4,
        start_offset=12,
        start_index=3,
        seed_terms=(
            ReadonlyReductionTermRef(byte_offset=0, access_size=4),
            ReadonlyReductionTermRef(byte_offset=8, access_size=4),
        ),
        return_op_refs=(site_ref,),
        return_region_value_proven=True,
    )
    prefix_ref = prefix_proof.lower_to_readonly_reduction_ref()
    seeded_ref = seeded_tail_proof.lower_to_readonly_reduction_ref()
    assert prefix_ref is not None
    assert seeded_ref is not None
    conditions = [
        _cond("INT_NOTEQUAL", ptr_expr, Expression.constant(0, size=8)),
        _cond("INT_SLESS", _const(3), count_expr),
        _cond("INT_EQUAL", count_expr, _const(4), negated=True),
    ]
    preserved_summary = ReturnInfo(
        address="0x1004",
        pcode_time=35,
        pcode_order=2,
        pcode_op_ref=site_ref,
        value=Expression.intrinsic(
            "READONLY_SUM",
            [ptr_expr, count_expr],
            size=4,
            runtime_ref=prefix_ref,
            opcode=READONLY_SUM_OPCODE,
        ),
        conditions=conditions,
    )
    seeded_summary = replace(
        preserved_summary,
        value=Expression.intrinsic(
            "READONLY_SUM",
            [ptr_expr, count_expr],
            size=4,
            runtime_ref=seeded_ref,
            opcode=READONLY_SUM_OPCODE,
        ),
    )
    unrelated_site = replace(
        preserved_summary,
        pcode_op_ref=PcodeOpRef(address_offset=0x2000, seq_time=35, seq_order=2, mnemonic="RETURN"),
    )
    summarizer = StructuralRecurrenceSummarizer(_FakeTracer("unused", _const(0)), debug=False)
    analysis = FunctionReturnAnalysis(
        function_name="readonly_preserved_summary_replacement_like",
        entry_point="0x1000",
        parameters=[pointer_param, {"name": "param_2", "index": 1, "data_type": "int", "size": 4}],
        returns=[preserved_summary],
    )

    assert summarizer._readonly_preserved_summary_is_subsumed_by_replacement(
        analysis,
        pointer_param,
        {"name": "param_2", "index": 1, "data_type": "int", "size": 4},
        preserved_summary,
        conditions,
        conditions,
        seeded_tail_proof,
        seeded_ref,
    )
    assert not summarizer._readonly_preserved_summary_is_subsumed_by_replacement(
        analysis,
        pointer_param,
        {"name": "param_2", "index": 1, "data_type": "int", "size": 4},
        seeded_summary,
        conditions,
        conditions,
        prefix_proof,
        prefix_ref,
    )
    assert not summarizer._readonly_preserved_summary_is_subsumed_by_replacement(
        analysis,
        pointer_param,
        {"name": "param_2", "index": 1, "data_type": "int", "size": 4},
        unrelated_site,
        conditions,
        conditions,
        seeded_tail_proof,
        seeded_ref,
    )

def test_proof_backed_specific_readonly_summary_precedes_broader_preserved_summary():
    pointer_param = {"name": "param_1", "index": 0, "data_type": "int *", "size": 8}
    ptr_expr = Expression.parameter("param_1", index=0, data_type="int *", size=8)
    count_expr = Expression.parameter("param_2", index=1, data_type="int", size=4)
    prefix_proof = _readonly_accumulator_proof(
        base_ref=LocationBaseRef.parameter("param_1", index=0),
        count_expr=count_expr,
        stride=4,
        element_size=4,
        start_offset=0,
        start_index=0,
    )
    seeded_tail_proof = _readonly_accumulator_proof(
        base_ref=LocationBaseRef.parameter("param_1", index=0),
        count_expr=count_expr,
        stride=4,
        element_size=4,
        start_offset=12,
        start_index=3,
        seed_terms=(
            ReadonlyReductionTermRef(byte_offset=0, access_size=4),
            ReadonlyReductionTermRef(byte_offset=8, access_size=4),
        ),
    )
    prefix_ref = prefix_proof.lower_to_readonly_reduction_ref()
    seeded_ref = seeded_tail_proof.lower_to_readonly_reduction_ref()
    assert prefix_ref is not None
    assert seeded_ref is not None
    broad_conditions = [
        _cond("INT_NOTEQUAL", ptr_expr, Expression.constant(0, size=8)),
        _cond("INT_SLESS", _const(0), count_expr),
        _cond("INT_EQUAL", count_expr, _const(1), negated=True),
        _cond("INT_EQUAL", count_expr, _const(2), negated=True),
        _cond("INT_EQUAL", count_expr, _const(3), negated=True),
        _cond("INT_EQUAL", count_expr, _const(4), negated=True),
    ]
    specific_conditions = [
        _cond("INT_NOTEQUAL", ptr_expr, Expression.constant(0, size=8)),
        _cond("INT_SLESS", _const(3), count_expr),
        _cond("INT_EQUAL", count_expr, _const(4), negated=True),
    ]
    preserved_broad = ReturnInfo(
        address="0x1004",
        value=Expression.intrinsic(
            "READONLY_SUM",
            [ptr_expr, count_expr],
            size=4,
            runtime_ref=prefix_ref,
            opcode=READONLY_SUM_OPCODE,
        ),
        conditions=broad_conditions,
    )
    summary_specific = ReturnInfo(
        address="0x1004",
        value=Expression.intrinsic(
            "READONLY_SUM",
            [ptr_expr, count_expr],
            size=4,
            runtime_ref=seeded_ref,
            opcode=READONLY_SUM_OPCODE,
        ),
        conditions=specific_conditions,
    )
    summarizer = StructuralRecurrenceSummarizer(_FakeTracer("unused", _const(0)), debug=False)

    assert summarizer._readonly_summary_return_should_precede_preserved_return(
        summary_specific,
        preserved_broad,
        seeded_ref,
    )
    assert not summarizer._readonly_summary_return_should_precede_preserved_return(
        preserved_broad,
        summary_specific,
        prefix_ref,
    )

def test_readonly_reduction_summary_records_non_unit_step_prefix_seed_terms():
    params = [
        {"name": "param_1", "index": 0, "data_type": "int *", "size": 8},
        {"name": "param_2", "index": 1, "data_type": "int", "size": 4, "is_signed": True},
    ]
    ptr_param = Expression.parameter("param_1", index=0, data_type="int *", size=8)
    count_param = Expression.parameter("param_2", index=1, data_type="int", size=4)
    analysis = create_mock_analysis(
        "ptr_sum_window",
        return_type="int",
        parameters=params,
        returns=[
            ReturnInfo(
                address="0x1000",
                value=_const(0),
                conditions=[_cond("INT_EQUAL", ptr_param, Expression.constant(0, size=8))],
            ),
            ReturnInfo(
                address="0x1004",
                value=_mem("param_1", 4),
                conditions=[
                    _cond("INT_NOTEQUAL", ptr_param, Expression.constant(0, size=8)),
                    _cond("INT_SLESSEQUAL", count_param, _const(3)),
                ],
            ),
            ReturnInfo(
                address="0x1008",
                value=Expression.unknown("phi_circular"),
                conditions=[
                    _cond("INT_NOTEQUAL", ptr_param, Expression.constant(0, size=8)),
                    _cond("INT_SLESS", _const(3), count_param),
                ],
            ),
        ],
    )

    ptr_varnode = _FakeVarnode(
        "param_1",
        size=8,
        expr=Expression.parameter("param_1", index=0, data_type="int *", size=8),
    )
    two32 = _FakeVarnode("two32", size=4, expr=Expression.constant(2, 4))
    three32 = _FakeVarnode("three32", size=4, expr=Expression.constant(3, 4))
    four64 = _FakeVarnode("four64", size=8, expr=Expression.constant(4, 8))
    ram_space = _FakeVarnode("ram", size=8, expr=Expression.constant(0, 8))

    idx_high = _FakeHighVar("idx")
    idx_phi = _FakeVarnode("idx_phi", size=4, high=idx_high)
    idx_next = _FakeVarnode("idx_next", size=4)
    idx_add_op = _FakePcodeOp("INT_ADD", [idx_phi, two32], idx_next)
    idx_phi_op = _FakePcodeOp("MULTIEQUAL", [three32, idx_next], idx_phi)

    addr = _FakeVarnode("addr", size=8)
    ptradd_op = _FakePcodeOp("PTRADD", [ptr_varnode, idx_phi, four64], addr)
    load_value = _FakeVarnode("load_value", size=4)
    load_op = _FakePcodeOp("LOAD", [ram_space, addr], load_value)

    acc_high = _FakeHighVar("acc")
    acc_phi = _FakeVarnode("acc_phi", size=4, high=acc_high)
    acc_next = _FakeVarnode("acc_next", size=4)
    acc_seed = _FakeVarnode("acc_seed", size=4, expr=_mem("param_1", 4))
    acc_add_op = _FakePcodeOp("INT_ADD", [acc_phi, load_value], acc_next)
    acc_phi_op = _FakePcodeOp("MULTIEQUAL", [acc_seed, acc_next], acc_phi)

    high_function = _FakeHighFunction([idx_add_op, idx_phi_op, ptradd_op, load_op, acc_add_op, acc_phi_op])
    tracer = _FakeTracer("unused", _const(0))
    tracer.trace_varnode = lambda varnode, *args, **kwargs: getattr(varnode, "_expr", None)
    summarizer = StructuralRecurrenceSummarizer(tracer, debug=False)
    summary = summarizer.try_summarize_function(
        _FakeFunction("ptr_sum_window"),
        high_function,
        analysis,
    )

    assert summary is not None
    summarized_returns, note = summary
    assert note == "readonly_pointer_reduction_summary"
    positive_case = next(ret for ret in summarized_returns if ret.value.expr_type == ExpressionType.INTRINSIC)
    runtime_ref = positive_case.value.runtime_ref
    loop_summary = runtime_ref.loop_summary
    assert runtime_ref.start_offset == 12
    assert runtime_ref.stride == 8
    assert loop_summary.start_expr.equals(Expression.constant(3, size=4))
    assert loop_summary.step_expr.equals(Expression.constant(2, size=4))
    assert loop_summary.seed_terms == (ReadonlyReductionTermRef(byte_offset=4, access_size=4),)

    full_summary = LoopSummaryRef(
        start_expr=Expression.constant(1, size=4),
        limit_expr=loop_summary.limit_expr,
        step_expr=loop_summary.step_expr,
        term_descriptor=loop_summary.term_descriptor,
        side_effect_profile=loop_summary.side_effect_profile,
        loop_var_unit=loop_summary.loop_var_unit,
    )
    assert loop_summary_method_b_key(loop_summary) == loop_summary_method_b_key(full_summary)

def test_readonly_reduction_detects_vector_pointer_loop_with_ptradd_tail(monkeypatch):
    params = [
        {"name": "param_1", "index": 0, "data_type": "int *", "size": 8},
        {"name": "param_2", "index": 1, "data_type": "int", "size": 4, "is_signed": True},
    ]
    ptr_expr = Expression.parameter("param_1", index=0, data_type="int *", size=8)
    count_expr = Expression.parameter("param_2", index=1, data_type="int", size=4)
    vector_body_value = _mem("param_1", 0)
    for byte_offset in range(4, 32, 4):
        vector_body_value = Expression.binary_op(
            "INT_ADD",
            vector_body_value,
            _mem("param_1", byte_offset),
        )
    analysis = create_mock_analysis(
        "vector_prefix_sum",
        return_type="int",
        parameters=params,
        returns=[
            ReturnInfo(
                address="0x1000",
                value=vector_body_value,
                conditions=[
                    _cond("INT_NOTEQUAL", ptr_expr, Expression.constant(0, size=8)),
                    _cond("INT_SLESS", Expression.constant(0, size=4), count_expr),
                    _cond("INT_SLESSEQUAL", Expression.constant(8, size=4), count_expr),
                ],
            )
        ],
    )

    ptr_vn = _FakeVarnode("param_1", size=8, expr=ptr_expr)
    count_vn = _FakeVarnode("param_2", size=4, expr=count_expr)
    mask_vn = _FakeVarnode("mask", size=4, expr=Expression.constant(0xFFFFFFF8, size=4))
    rounded_vn = _FakeVarnode("rounded", size=4)
    round_op = _FakePcodeOp("INT_AND", [count_vn, mask_vn], rounded_vn)

    four_vn = _FakeVarnode("four", size=4, expr=Expression.constant(4, size=4))
    eight_vn = _FakeVarnode("eight", size=4, expr=Expression.constant(8, size=4))
    base_bias_vn = _FakeVarnode("base_bias", size=4, expr=Expression.constant(4, size=4))
    vector_init = _FakeVarnode("vector_init", size=8)
    vector_phi = _FakeVarnode("vector_phi", size=8, high=_FakeHighVar("vector_phi"))
    vector_next = _FakeVarnode("vector_next", size=8)
    vector_end_base = _FakeVarnode("vector_end_base", size=8)
    vector_end = _FakeVarnode("vector_end", size=8)
    vector_cond = _FakeVarnode("vector_cond", size=1)

    init_op = _FakePcodeOp("PTRADD", [ptr_vn, base_bias_vn, four_vn], vector_init)
    next_op = _FakePcodeOp("PTRADD", [vector_phi, eight_vn, four_vn], vector_next)
    vector_phi_op = _FakePcodeOp("MULTIEQUAL", [vector_init, vector_next], vector_phi)
    end_base_op = _FakePcodeOp("PTRADD", [ptr_vn, rounded_vn, four_vn], vector_end_base)
    end_op = _FakePcodeOp("INT_ADD", [vector_end_base, _FakeVarnode("sixteen", size=8, expr=Expression.constant(16, size=8))], vector_end)
    vector_cmp_op = _FakePcodeOp("INT_NOTEQUAL", [vector_phi, vector_end], vector_cond)

    ram_space = _FakeVarnode("ram", size=8, expr=Expression.constant(0, size=8))
    load_ops = []
    sum_ops = []
    running_sum = _FakeVarnode("sum_zero", size=4, expr=Expression.constant(0, size=4))
    for lane, index_value in enumerate(range(-4, 4)):
        index_vn = _FakeVarnode(f"lane_index_{lane}", size=4, expr=Expression.constant(index_value, size=4))
        addr_vn = _FakeVarnode(f"lane_addr_{lane}", size=8)
        value_vn = _FakeVarnode(f"lane_value_{lane}", size=4)
        next_sum = _FakeVarnode(f"sum_after_lane_{lane}", size=4)
        addr_op = _FakePcodeOp("PTRADD", [vector_phi, index_vn, four_vn], addr_vn)
        load_op = _FakePcodeOp("LOAD", [ram_space, addr_vn], value_vn)
        add_op = _FakePcodeOp("INT_ADD", [running_sum, value_vn], next_sum)
        load_ops.extend([addr_op, load_op])
        sum_ops.append(add_op)
        running_sum = next_sum

    tail_start = _FakeVarnode("tail_start", size=8)
    tail_next = _FakeVarnode("tail_next", size=8)
    tail_phi = _FakeVarnode("tail_phi", size=8, high=_FakeHighVar("tail_phi"))
    tail_load = _FakeVarnode("tail_load", size=4)
    tail_sum = _FakeVarnode("tail_sum", size=4)
    remaining_init = _FakeVarnode("remaining_init", size=8)
    remaining_phi = _FakeVarnode("remaining_phi", size=8, high=_FakeHighVar("remaining"))
    remaining_next = _FakeVarnode("remaining_next", size=8)
    remaining_cond = _FakeVarnode("remaining_cond", size=1)
    tail_start_op = _FakePcodeOp("PTRADD", [ptr_vn, rounded_vn, four_vn], tail_start)
    tail_next_op = _FakePcodeOp("PTRADD", [tail_phi, _FakeVarnode("one", size=4, expr=Expression.constant(1, size=4)), four_vn], tail_next)
    tail_phi_op = _FakePcodeOp("MULTIEQUAL", [tail_start, tail_next], tail_phi)
    tail_load_op = _FakePcodeOp("LOAD", [ram_space, tail_phi], tail_load)
    tail_add_op = _FakePcodeOp("INT_ADD", [running_sum, tail_load], tail_sum)
    return_op = _FakePcodeOp("RETURN", [_FakeVarnode("return_target", size=8), tail_sum], None)
    remaining_init_op = _FakePcodeOp("INT_SUB", [count_vn, rounded_vn], remaining_init)
    remaining_phi_op = _FakePcodeOp("MULTIEQUAL", [remaining_init, remaining_next], remaining_phi)
    remaining_next_op = _FakePcodeOp(
        "INT_ADD",
        [remaining_phi, _FakeVarnode("minus_one", size=8, expr=Expression.constant(-1, size=8))],
        remaining_next,
    )
    remaining_cmp_op = _FakePcodeOp(
        "INT_NOTEQUAL",
        [remaining_next, _FakeVarnode("zero64", size=8, expr=Expression.constant(0, size=8))],
        remaining_cond,
    )

    high_function = _FakeHighFunction(
        [
            round_op,
            init_op,
            next_op,
            vector_phi_op,
            end_base_op,
            end_op,
            vector_cmp_op,
            *load_ops,
            *sum_ops,
            tail_start_op,
            tail_next_op,
            tail_phi_op,
            tail_load_op,
            tail_add_op,
            return_op,
            remaining_init_op,
            remaining_phi_op,
            remaining_next_op,
            remaining_cmp_op,
        ]
    )
    tracer = _FakeTracer("unused", _const(0))
    tracer.trace_varnode = lambda varnode, *args, **kwargs: getattr(varnode, "_expr", None)
    summarizer = StructuralRecurrenceSummarizer(tracer, debug=False)
    monkeypatch.setattr(
        summarizer,
        "_vector_prefix_unit_term_positive_return_refs",
        lambda *_args, **_kwargs: (PcodeOpRef(address_offset=0x1000, seq_time=10, mnemonic="RETURN"),),
    )
    monkeypatch.setattr(
        summarizer,
        "_vector_prefix_lane_return_refs",
        lambda *_args, **_kwargs: (
            (PcodeOpRef(address_offset=0x1000, seq_time=10, mnemonic="RETURN"),),
            (PcodeOpRef(address_offset=0x1000, seq_time=9, mnemonic="INT_ADD"),),
        ),
    )

    proof = summarizer._detect_readonly_sum_accumulator_proof(
        high_function,
        analysis,
        params[0],
        params[1],
        counter_signed=True,
    )

    assert proof is not None
    assert proof.stride == 4
    assert proof.element_size == 4
    assert proof.start_index == 0
    assert proof.index_step == 1
    assert proof.stable_key() is not None

def test_readonly_addend_proof_rejects_nonzero_constant_sibling():
    pointer_param = {"name": "param_1", "index": 0, "data_type": "int *", "size": 8}
    phi_vn = _FakeVarnode("ptr_phi", size=8)
    ram_space = _FakeVarnode("ram", size=8, expr=Expression.constant(0, size=8))
    load_vn = _FakeVarnode("load", size=4)
    const_five = _FakeVarnode("five", size=4, expr=Expression.constant(5, size=4))
    add_vn = _FakeVarnode("load_plus_five", size=4)
    _FakePcodeOp("LOAD", [ram_space, phi_vn], load_vn)
    _FakePcodeOp("INT_ADD", [load_vn, const_five], add_vn)
    tracer = _FakeTracer("unused", Expression.unknown("unknown"))
    tracer.trace_varnode = lambda varnode, *args, **kwargs: getattr(varnode, "_expr", None)
    summarizer = StructuralRecurrenceSummarizer(tracer, debug=False)

    progressions = summarizer._collect_load_progressions_from_varnode(
        add_vn,
        pointer_param,
        [
            {
                "phi_op": _FakePcodeOp("MULTIEQUAL", [], phi_vn),
                "phi_output": phi_vn,
                "stride": 4,
                "start_offset": 0,
                "start_index": 0,
                "index_step": 1,
                "index_scale": 4,
            }
        ],
        [],
    )

    assert progressions is None

def test_readonly_addend_proof_rejects_duplicate_load_terms():
    pointer_param = {"name": "param_1", "index": 0, "data_type": "int *", "size": 8}
    phi_vn = _FakeVarnode("ptr_phi", size=8)
    ram_space = _FakeVarnode("ram", size=8, expr=Expression.constant(0, size=8))
    load_vn = _FakeVarnode("load", size=4)
    doubled_vn = _FakeVarnode("load_plus_load", size=4)
    _FakePcodeOp("LOAD", [ram_space, phi_vn], load_vn)
    _FakePcodeOp("INT_ADD", [load_vn, load_vn], doubled_vn)
    tracer = _FakeTracer("unused", Expression.unknown("unknown"))
    tracer.trace_varnode = lambda varnode, *args, **kwargs: getattr(varnode, "_expr", None)
    summarizer = StructuralRecurrenceSummarizer(tracer, debug=False)
    load_progressions = summarizer._collect_load_progressions_from_varnode(
        doubled_vn,
        pointer_param,
        [
            {
                "phi_op": _FakePcodeOp("MULTIEQUAL", [], phi_vn),
                "phi_output": phi_vn,
                "stride": 4,
                "start_offset": 0,
                "start_index": 0,
                "index_step": 1,
                "index_scale": 4,
            }
        ],
        [],
    )

    assert load_progressions is not None
    assert summarizer._readonly_load_progression_term_counter(load_progressions, result_size=4) == {
        (0, 4): 2,
    }

def test_readonly_addend_proof_rejects_signed_extension_until_mode_is_represented():
    pointer_param = {"name": "param_1", "index": 0, "data_type": "char *", "size": 8}
    phi_vn = _FakeVarnode("ptr_phi", size=8)
    ram_space = _FakeVarnode("ram", size=8, expr=Expression.constant(0, size=8))
    load_vn = _FakeVarnode("load", size=1)
    sext_vn = _FakeVarnode("sext_load", size=4)
    _FakePcodeOp("LOAD", [ram_space, phi_vn], load_vn)
    _FakePcodeOp("INT_SEXT", [load_vn], sext_vn)
    tracer = _FakeTracer("unused", Expression.unknown("unknown"))
    tracer.trace_varnode = lambda varnode, *args, **kwargs: getattr(varnode, "_expr", None)
    summarizer = StructuralRecurrenceSummarizer(tracer, debug=False)

    progressions = summarizer._collect_load_progressions_from_varnode(
        sext_vn,
        pointer_param,
        [
            {
                "phi_op": _FakePcodeOp("MULTIEQUAL", [], phi_vn),
                "phi_output": phi_vn,
                "stride": 1,
                "start_offset": 0,
                "start_index": 0,
                "index_step": 1,
                "index_scale": 1,
            }
        ],
        [],
    )

    assert progressions is None

def test_readonly_exact_expression_extracts_terms_and_constant_bias_object_centrically():
    pointer_param = {"name": "param_1", "index": 0, "data_type": "int *", "size": 8}
    expr = Expression.binary_op("INT_ADD", _mem("param_1", 0), Expression.constant(5, size=4))
    summarizer = StructuralRecurrenceSummarizer(_FakeTracer("unused", Expression.unknown("unknown")), debug=False)

    extracted = summarizer._extract_readonly_reduction_terms_and_bias(
        expr,
        [pointer_param],
        pointer_param,
    )

    assert extracted == (
        (ReadonlyReductionTermRef(byte_offset=0, access_size=4),),
        5,
    )
    assert summarizer._extract_readonly_reduction_terms(expr, [pointer_param], pointer_param) is None

def test_readonly_exact_return_witness_rejects_bias_width_mismatch():
    pointer_param = {"name": "param_1", "index": 0, "data_type": "int *", "size": 8}
    count_param = {"name": "param_2", "index": 1, "data_type": "int", "size": 4, "is_signed": True}
    count_expr = Expression.parameter("param_2", index=1, data_type="int", size=4)
    proof = ReductionAccumulatorProof(
        reduction_kind="memory_sum",
        pointer_base_ref=LocationBaseRef.parameter("param_1", index=0),
        count_parameter_name="param_2",
        count_parameter_index=1,
        limit_expr=count_expr,
        result_size=4,
        stride=4,
        element_size=4,
    )
    wide_bias = Expression.constant(1 << 32, size=8)
    wide_return = Expression.binary_op("INT_ADD", _mem("param_1", 0), wide_bias)
    wide_return.size = 8
    ret = ReturnInfo(
        address="0x2000",
        value=wide_return,
        conditions=[_cond("INT_EQUAL", count_expr, _const(1))],
    )
    analysis = create_mock_analysis(
        "readonly_wide_bias",
        return_type="long",
        parameters=[pointer_param, count_param],
        returns=[ret],
    )
    summarizer = StructuralRecurrenceSummarizer(_FakeTracer("unused", Expression.unknown("unknown")), debug=False)

    witnesses = summarizer._extract_readonly_reduction_exact_witnesses(
        analysis,
        pointer_param,
        count_param,
        [ret],
        proof,
    )

    assert witnesses == ()

def test_readonly_exact_return_witness_canonicalizes_proven_vectorized_prefix_completion(monkeypatch):
    pointer_param = {"name": "param_1", "index": 0, "data_type": "int *", "size": 8}
    count_param = {"name": "param_2", "index": 1, "data_type": "int", "size": 4, "is_signed": True}
    count_expr = Expression.parameter("param_2", index=1, data_type="int", size=4)
    proof = _readonly_accumulator_proof(
        base_ref=LocationBaseRef.parameter("param_1", index=0),
        count_expr=count_expr,
        stride=4,
        element_size=4,
        start_offset=12,
        start_index=3,
        seed_terms=(
            ReadonlyReductionTermRef(byte_offset=0, access_size=4),
            ReadonlyReductionTermRef(byte_offset=4, access_size=4),
            ReadonlyReductionTermRef(byte_offset=8, access_size=4),
        ),
    )
    value = Expression.binary_op(
        "INT_ADD",
        _mem("param_1", 12),
        Expression.binary_op(
            "INT_ADD",
            _mem("param_1", 0),
            Expression.binary_op(
                "INT_ADD",
                _mem("param_1", 4),
                Expression.binary_op(
                    "INT_ADD",
                    _mem("param_1", 8),
                    _mem("param_1", 16),
                ),
            ),
        ),
    )
    ret = ReturnInfo(
        address="0x2000",
        value=value,
        conditions=[_cond("INT_EQUAL", count_expr, _const(5))],
    )
    analysis = create_mock_analysis(
        "readonly_vector_prefix_completion",
        return_type="int",
        parameters=[pointer_param, count_param],
        returns=[ret],
    )
    summarizer = StructuralRecurrenceSummarizer(_FakeTracer("unused", Expression.unknown("unknown")), debug=False)

    monkeypatch.setattr(
        summarizer,
        "_extract_readonly_return_terms_and_bias",
        lambda *_args, **_kwargs: (
            (
                ReadonlyReductionTermRef(byte_offset=12, access_size=4),
                ReadonlyReductionTermRef(byte_offset=16, access_size=4),
            ),
            0,
        ),
    )

    witnesses = summarizer._extract_readonly_reduction_exact_witnesses(
        analysis,
        pointer_param,
        count_param,
        [ret],
        proof,
    )

    assert len(witnesses) == 1
    assert witnesses[0].exact_count == 5
    assert tuple(term.byte_offset for term in witnesses[0].terms) == (0, 4, 8, 12, 16)

def test_readonly_exact_return_witness_accepts_commuted_sum_terms():
    pointer_param = {"name": "param_1", "index": 0, "data_type": "int *", "size": 8}
    count_param = {"name": "param_2", "index": 1, "data_type": "int", "size": 4, "is_signed": True}
    count_expr = Expression.parameter("param_2", index=1, data_type="int", size=4)
    proof = _readonly_accumulator_proof(
        base_ref=LocationBaseRef.parameter("param_1", index=0),
        count_expr=count_expr,
        stride=4,
        element_size=4,
        start_offset=12,
        start_index=3,
        seed_terms=(
            ReadonlyReductionTermRef(byte_offset=0, access_size=4),
            ReadonlyReductionTermRef(byte_offset=8, access_size=4),
        ),
    )
    ret = ReturnInfo(
        address="0x2008",
        value=Expression.binary_op(
            "INT_ADD",
            _mem("param_1", 12),
            Expression.binary_op("INT_ADD", _mem("param_1", 8), _mem("param_1", 0)),
        ),
        conditions=[_cond("INT_EQUAL", count_expr, _const(4))],
    )
    analysis = create_mock_analysis(
        "readonly_commuted_wrong_tail_exact",
        return_type="int",
        parameters=[pointer_param, count_param],
        returns=[ret],
    )
    summarizer = StructuralRecurrenceSummarizer(_FakeTracer("unused", Expression.unknown("unknown")), debug=False)

    witnesses = summarizer._extract_readonly_reduction_exact_witnesses(
        analysis,
        pointer_param,
        count_param,
        [ret],
        proof,
    )

    assert len(witnesses) == 1
    assert witnesses[0].exact_count == 4
    assert tuple(term.byte_offset for term in witnesses[0].terms) == (0, 8, 12)

def test_readonly_exact_return_witness_accepts_self_consistent_scalar_prefix_when_proof_geometry_differs():
    summarizer = StructuralRecurrenceSummarizer(tracer=None, debug=False)
    pointer_param = {"name": "param_1", "index": 0, "data_type": "int *", "size": 8}
    count_param = {"name": "param_2", "index": 1, "data_type": "int", "size": 4, "is_signed": True}
    count_expr = Expression.parameter("param_2", index=1, data_type="int", size=4)
    proof = _readonly_accumulator_proof(
        base_ref=LocationBaseRef.parameter("param_1", index=0),
        count_expr=count_expr,
        stride=16,
        element_size=8,
        result_size=4,
        start_offset=12,
        start_index=3,
        index_scale=16,
    )
    ret = ReturnInfo(
        address="0x2004",
        value=Expression.binary_op(
            "INT_ADD",
            _mem("param_1", 0),
            Expression.binary_op(
                "INT_ADD",
                _mem("param_1", 4),
                _mem("param_1", 8),
            ),
        ),
        conditions=[_cond("INT_EQUAL", count_expr, _const(3))],
    )
    analysis = create_mock_analysis(
        "readonly_scalar_prefix_geometry_mismatch",
        return_type="int",
        parameters=[pointer_param, count_param],
        returns=[ret],
    )

    witnesses = summarizer._extract_readonly_reduction_exact_witnesses(
        analysis,
        pointer_param,
        count_param,
        [ret],
        proof,
    )

    assert len(witnesses) == 1
    assert witnesses[0].exact_count == 3
    assert tuple(term.byte_offset for term in witnesses[0].terms) == (0, 4, 8)

def test_reduction_accumulator_proof_normalizes_scalar_prefix_from_exact_witnesses():
    proof = _readonly_accumulator_proof(
        base_ref=LocationBaseRef.parameter("param_1", index=0),
        count_expr=Expression.parameter("param_2", index=1, data_type="int", size=4),
        stride=16,
        element_size=8,
        result_size=4,
        start_offset=12,
        start_index=3,
        index_scale=16,
    )
    exact_witnesses = tuple(
        ReadonlyReductionWitness(
            exact_count=count_value,
            terms=tuple(
                ReadonlyReductionTermRef(byte_offset=index * 4, access_size=4)
                for index in range(count_value)
            ),
        )
        for count_value in (1, 2, 3, 5, 6)
    )

    normalized = proof.with_runtime_evidence(
        limit_expr=Expression.parameter("param_2", index=1, data_type="int", size=4),
        result_size=4,
        loop_body_witnesses=(),
        exact_return_witnesses=exact_witnesses,
        guard_constraints=(),
        signed_counter=True,
    )

    assert normalized.stride == 4
    assert normalized.element_size == 4
    assert normalized.index_scale == 4
    assert normalized.start_offset == 0
    assert normalized.start_index == 0
