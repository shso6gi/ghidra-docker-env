from scripts.function_tracer_pcode.tests.unit._recurrence_fixtures import *


def _phi_with_cfg_edge_condition(*, condition_depends_on_phi: bool):
    seed = _FakeVarnode(
        "seed",
        expr=Expression.constant(0, size=4),
        storage_offset=0x10,
    )
    update = _FakeVarnode(
        "update",
        expr=Expression.constant(1, size=4),
        storage_offset=0x14,
    )
    phi_output = _FakeVarnode("phi", size=4, storage_offset=0x18)
    phi_op = _FakePcodeOp("MULTIEQUAL", [seed, update], phi_output)

    independent = _FakeVarnode(
        "limit",
        expr=Expression.parameter("param_1", index=0, data_type="int", size=4),
        storage_offset=0x20,
    )
    zero = _FakeVarnode(
        "zero",
        expr=Expression.constant(0, size=4),
        storage_offset=0,
        storage_space="const",
    )
    condition_output = _FakeVarnode(
        "condition",
        size=1,
        storage_offset=0x24,
    )
    _FakePcodeOp(
        "INT_NOTEQUAL",
        [phi_output if condition_depends_on_phi else independent, zero],
        condition_output,
    )
    branch_target = _FakeVarnode(
        "branch_target",
        expr=Expression.constant(0, size=8),
        storage_offset=0x100,
    )
    branch_op = _FakePcodeOp("CBRANCH", [branch_target, condition_output])

    preheader = _FakeCfgBlock(0)
    header = _FakeCfgBlock(1, [phi_op])
    latch = _FakeCfgBlock(2, [branch_op])
    exit_block = _FakeCfgBlock(3)
    preheader.add_edge(header)
    latch.add_edge(header, truth=True)
    latch.add_edge(exit_block, truth=False)

    summarizer = StructuralRecurrenceSummarizer(_IdentityTracer(), debug=False)
    return summarizer, phi_output


def test_pcode_expression_marks_phi_edge_condition_cycle_unavailable():
    summarizer, phi_output = _phi_with_cfg_edge_condition(
        condition_depends_on_phi=True
    )

    assert summarizer._build_pcode_expression(phi_output, placeholders={}) is None


def test_pcode_expression_builds_noncyclic_phi_edge_condition():
    summarizer, phi_output = _phi_with_cfg_edge_condition(
        condition_depends_on_phi=False
    )

    expression = summarizer._build_pcode_expression(phi_output, placeholders={})

    assert expression is not None
    assert expression.expr_type == ExpressionType.PHI
    assert len(expression.value) == 2
    assert expression.value[0][0] is None
    assert expression.value[1][0].expression.operator == "INT_NOTEQUAL"


def test_pcode_expression_does_not_approximate_cyclic_phi_as_unconditional_seed():
    summarizer, phi_output = _phi_with_cfg_edge_condition(
        condition_depends_on_phi=True
    )

    first = summarizer._build_pcode_expression(phi_output, placeholders={})
    second = summarizer._build_pcode_expression(phi_output, placeholders={})

    assert first is None
    assert second is None


def test_phi_input_resolution_keeps_cross_storage_parameter_seed_over_later_def():
    pointer_high = _FakeHighVar("param_1")
    end_high = _FakeHighVar("end_pointer")
    raw_param = _FakeVarnode("a0_param", size=8, high=pointer_high, storage_offset=0x20)
    end_pointer = _FakeVarnode("a0_end", size=8, high=end_high, storage_offset=0x20)
    cursor_phi = _FakeVarnode("cursor_phi", size=8, high=pointer_high, storage_offset=0x18)
    cursor_next = _FakeVarnode("cursor_next", size=8, high=pointer_high, storage_offset=0x18)
    one_vn = _FakeVarnode("one", size=8, expr=Expression.constant(1, size=8))
    four_vn = _FakeVarnode("four", size=8, expr=Expression.constant(4, size=8))

    end_def = _FakePcodeOp("PTRADD", [raw_param, one_vn, four_vn], end_pointer)
    phi_op = _FakePcodeOp("MULTIEQUAL", [raw_param, cursor_phi], cursor_phi)
    cursor_step = _FakePcodeOp("PTRADD", [cursor_phi, one_vn, four_vn], cursor_next)
    preheader = _FakeCfgBlock(0, [end_def])
    loop = _FakeCfgBlock(1, [phi_op, cursor_step])
    preheader.add_edge(loop)
    loop.add_edge(loop)
    summarizer = StructuralRecurrenceSummarizer(_FakeTracer("unused", _const(0)), debug=False)

    assert summarizer._phi_input_value_varnode(phi_op, 0) is raw_param
    assert summarizer._phi_input_value_varnode(phi_op, 1) is cursor_next

def test_structural_recurrence_summarizer_synthesizes_linear_semantic_witnesses_for_simple_loop():
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
                value=Expression.binary_op(
                    "INT_ADD",
                    _mem("param_1", 0),
                    Expression.unknown("phi_circular"),
                ),
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
    idx_add_op = _FakePcodeOp("INT_ADD", [idx_phi, one32], idx_next)
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
    positive_case = next(ret for ret in summarized_returns if ret.value.expr_type == ret.value.expr_type.__class__.INTRINSIC)
    assert positive_case.value.runtime_ref.semantic_witnesses[:2] == (
        ReadonlyReductionWitness(
            exact_count=1,
            terms=(ReadonlyReductionTermRef(byte_offset=0, access_size=4),),
        ),
        ReadonlyReductionWitness(
            exact_count=2,
            terms=(
                ReadonlyReductionTermRef(byte_offset=0, access_size=4),
                ReadonlyReductionTermRef(byte_offset=4, access_size=4),
            ),
        ),
    )

def test_structural_recurrence_positive_guard_uses_unsigned_compare_for_unsigned_count():
    summarizer = StructuralRecurrenceSummarizer(tracer=None, debug=False)
    pointer_param = {"name": "param_1", "index": 0, "data_type": "int *", "size": 8, "is_signed": False}
    count_param = {"name": "param_2", "index": 1, "data_type": "uint", "size": 4, "is_signed": False}

    conditions = summarizer._readonly_reduction_positive_conditions(
        analysis=None,
        pointer_param=pointer_param,
        count_param=count_param,
        loop_start_index=3,
    )

    assert len(conditions) == 2
    assert conditions[1].expression.operator == "INT_LESS"
    assert conditions[1].to_string() == "(3 < param_2)"
    assert (
        summarizer._readonly_reduction_count_compare_op(
            count_param,
            inclusive=True,
        )
        == "INT_LESSEQUAL"
    )

def test_structural_recurrence_leaves_counter_signedness_ambiguous_when_guards_conflict():
    summarizer = StructuralRecurrenceSummarizer(tracer=None, debug=False)
    analysis = FunctionReturnAnalysis(
        function_name="readonly_ambiguous_counter_like",
        entry_point="0x1000",
        parameters=[
            {"name": "param_1", "index": 0, "data_type": "int *", "size": 8, "is_signed": False},
            {"name": "param_2", "index": 1, "data_type": "uint", "size": 4, "is_signed": False},
        ],
        returns=[
            ReturnInfo(
                address="0x1000",
                conditions=[
                    _cond("INT_SLESS", _const(0), _param("param_2")),
                    _cond("INT_LESS", _const(3), _param("param_2")),
                ],
                value=_const(1),
            )
        ],
    )

    assert (
        summarizer._readonly_reduction_counter_is_signed(
            analysis.returns,
            analysis.parameters[1],
        )
        is None
    )

def test_structural_recurrence_declines_loop_anchor_residual_when_only_single_count_is_covered():
    summarizer = StructuralRecurrenceSummarizer(tracer=None, debug=False)
    pointer_param = {"name": "param_1", "index": 0, "data_type": "int *", "size": 8, "is_signed": False}
    count_param = {"name": "param_2", "index": 1, "data_type": "long", "size": 8, "is_signed": False}
    count_expr = Expression.parameter("param_2", index=1, data_type="long", size=8)
    extra_counter_guard = _cond(
        "INT_NOTEQUAL",
        count_expr,
        _const(4, size=8),
    )
    broad_return = ReturnInfo(
        address="0x1010",
        conditions=[
            _cond("INT_NOTEQUAL", Expression.parameter("param_1", index=0, data_type="int *", size=8), _const(0, size=8)),
            _cond("INT_SLESS", _const(0, size=8), count_expr),
            _cond("INT_SLESS", _const(3, size=8), count_expr),
            extra_counter_guard,
        ],
        value=Expression.binary_op(
            "INT_ADD",
            _mem("param_1", 12),
            Expression.binary_op(
                "INT_ADD",
                _mem("param_1", 0),
                Expression.binary_op(
                    "INT_ADD",
                    _mem("param_1", 4),
                    _mem("param_1", 8),
                ),
            ),
        ),
    )
    exact_count_four_return = ReturnInfo(
        address="0x1014",
        conditions=[
            _cond("INT_NOTEQUAL", Expression.parameter("param_1", index=0, data_type="int *", size=8), _const(0, size=8)),
            _cond("INT_EQUAL", count_expr, _const(4, size=8)),
        ],
        value=broad_return.value,
    )
    analysis = FunctionReturnAnalysis(
        function_name="readonly_loop_anchor_mask_guard_like",
        entry_point="0x1000",
        parameters=[pointer_param, count_param],
        returns=[broad_return, exact_count_four_return],
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
            ReadonlyReductionTermRef(byte_offset=4, access_size=4),
            ReadonlyReductionTermRef(byte_offset=8, access_size=4),
        ),
        return_region_value_proven=False,
    )
    broad_positive_conditions = [
        _cond("INT_NOTEQUAL", Expression.parameter("param_1", index=0, data_type="int *", size=8), _const(0, size=8)),
        _cond("INT_SLESS", _const(0, size=8), count_expr),
    ]
    positive_conditions = broad_positive_conditions[:-1] + [
        _cond("INT_SLESS", _const(3, size=8), count_expr),
    ]

    replaceable = summarizer._readonly_reduction_replaceable_positive_returns(
        analysis,
        pointer_param,
        count_param,
        broad_positive_conditions,
        positive_conditions,
        expected_signed=True,
        accumulator_proof=proof,
    )

    assert replaceable == []

def test_structural_recurrence_declines_loop_anchor_when_prefix_region_is_uncovered():
    summarizer = StructuralRecurrenceSummarizer(tracer=None, debug=False)
    pointer_param = {"name": "param_1", "index": 0, "data_type": "int *", "size": 8, "is_signed": False}
    count_param = {"name": "param_2", "index": 1, "data_type": "int", "size": 4, "is_signed": True}
    count_expr = Expression.parameter("param_2", index=1, data_type="int", size=4)
    broad_return = ReturnInfo(
        address="0x1018",
        conditions=[
            _cond("INT_NOTEQUAL", Expression.parameter("param_1", index=0, data_type="int *", size=8), _const(0, size=8)),
            _cond("INT_SLESS", _const(0), count_expr),
            _cond("INT_NOTEQUAL", count_expr, _const(3)),
        ],
        value=Expression.binary_op(
            "INT_ADD",
            _mem("param_1", 12),
            Expression.binary_op(
                "INT_ADD",
                _mem("param_1", 0),
                Expression.binary_op(
                    "INT_ADD",
                    _mem("param_1", 4),
                    _mem("param_1", 8),
                ),
            ),
        ),
    )
    analysis = FunctionReturnAnalysis(
        function_name="readonly_loop_anchor_uncovered_prefix_like",
        entry_point="0x1000",
        parameters=[pointer_param, count_param],
        returns=[broad_return],
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
            ReadonlyReductionTermRef(byte_offset=4, access_size=4),
            ReadonlyReductionTermRef(byte_offset=8, access_size=4),
        ),
    )
    broad_positive_conditions = [
        _cond("INT_NOTEQUAL", Expression.parameter("param_1", index=0, data_type="int *", size=8), _const(0, size=8)),
        _cond("INT_SLESS", _const(0), count_expr),
    ]
    positive_conditions = broad_positive_conditions[:-1] + [
        _cond("INT_SLESS", _const(3), count_expr),
    ]

    replaceable = summarizer._readonly_reduction_replaceable_positive_returns(
        analysis,
        pointer_param,
        count_param,
        broad_positive_conditions,
        positive_conditions,
        expected_signed=True,
        accumulator_proof=proof,
    )

    assert replaceable == []

def test_structural_recurrence_prefix_coverage_requires_matching_non_count_guards(monkeypatch):
    summarizer = StructuralRecurrenceSummarizer(tracer=None, debug=False)
    pointer_param = {"name": "param_1", "index": 0, "data_type": "int *", "size": 8, "is_signed": False}
    count_param = {"name": "param_2", "index": 1, "data_type": "int", "size": 4, "is_signed": True}
    analysis = FunctionReturnAnalysis(
        function_name="readonly_prefix_guard_mismatch_like",
        entry_point="0x1200",
        parameters=[pointer_param, count_param],
        returns=[],
    )
    proof = _readonly_accumulator_proof(
        base_ref=LocationBaseRef.parameter("param_1", index=0),
        count_expr=_param("param_2"),
        stride=4,
        element_size=4,
        start_index=3,
    )
    broad_ret = ReturnInfo(
        address="0x1200",
        conditions=[
            _cond("INT_NOTEQUAL", _param("param_1", size=8), _const(0, size=8)),
            _cond("INT_SLESS", _const(0), _param("param_2")),
            _cond("INT_NOTEQUAL", _param("flag"), _const(0)),
        ],
        value=_const(1),
    )
    wrong_witness = ReturnInfo(
        address="0x1201",
        conditions=[
            _cond("INT_NOTEQUAL", _param("param_1", size=8), _const(0, size=8)),
            _cond("INT_EQUAL", _param("param_2"), _const(1)),
            _cond("INT_EQUAL", _param("flag"), _const(0)),
        ],
        value=_const(2),
    )
    analysis.returns = [broad_ret, wrong_witness]
    monkeypatch.setattr(
        summarizer,
        "_readonly_positive_return_matches_accumulator_proof",
        lambda *_args, **_kwargs: True,
    )

    assert summarizer._readonly_positive_prefix_is_exactly_covered(
        analysis,
        pointer_param,
        count_param,
        broad_ret,
        proof,
    ) is False

def test_exact_count_region_accepts_masked_negated_notequal_singleton_guard():
    summarizer = StructuralRecurrenceSummarizer(_FakeTracer("unused", _const(0)), debug=False)
    count_param = {"name": "param_1", "index": 0, "data_type": "int", "size": 4, "is_signed": True}
    count_expr = Expression.parameter("param_1", index=0, data_type="int", size=4)
    positive = _cond("INT_SLESS", _const(0), count_expr)
    masked_count = Expression.binary_op(
        "INT_AND",
        count_expr,
        Expression.constant(0xFFFFFFFF, size=4),
    )
    masked_count.size = 4
    selector_expr = Expression.binary_op(
        "INT_NOTEQUAL",
        Expression.binary_op("INT_SUB", masked_count, _const(1)),
        _const(0),
    )
    selector_expr.size = 1
    singleton_selector = Condition(selector_expr, negated=True)
    ret = ReturnInfo(
        address="0x1000",
        value=_const(0, size=8),
        conditions=[positive, singleton_selector],
    )

    assert summarizer._exact_counter_value_from_conditions(ret.conditions, "param_1") == 1
    assert summarizer._readonly_exact_count_region_is_fully_covered_by_return(
        ret,
        [positive],
        count_param,
        1,
    )

def test_exact_count_region_accepts_positive_noncount_guard_plus_masked_singleton():
    summarizer = StructuralRecurrenceSummarizer(_FakeTracer("unused", _const(0)), debug=False)
    pointer_expr = _param("param_1", size=8)
    count_expr = Expression.parameter("param_2", index=1, data_type="int", size=4)
    count_param = {"name": "param_2", "index": 1, "data_type": "int", "size": 4, "is_signed": True}
    pointer_nonnull = _cond("INT_NOTEQUAL", pointer_expr, _const(0, size=8))
    positive = _cond("INT_SLESS", _const(0), count_expr)
    masked_count = Expression.binary_op(
        "INT_AND",
        count_expr,
        Expression.constant(0xFFFFFFFF, size=4),
    )
    masked_count.size = 4
    selector_expr = Expression.binary_op(
        "INT_NOTEQUAL",
        Expression.binary_op("INT_SUB", masked_count, _const(1)),
        _const(0),
    )
    selector_expr.size = 1
    singleton_selector = Condition(selector_expr, negated=True)
    ret = ReturnInfo(
        address="0x1000",
        value=_mem("param_1", 0),
        conditions=[pointer_nonnull, positive, singleton_selector],
    )

    assert summarizer._readonly_exact_count_region_is_fully_covered_by_return(
        ret,
        [pointer_nonnull, positive],
        count_param,
        1,
    )

def test_exact_count_region_rejects_uncovered_noncount_guard_with_masked_singleton():
    summarizer = StructuralRecurrenceSummarizer(_FakeTracer("unused", _const(0)), debug=False)
    pointer_expr = _param("param_1", size=8)
    count_expr = Expression.parameter("param_2", index=1, data_type="int", size=4)
    count_param = {"name": "param_2", "index": 1, "data_type": "int", "size": 4, "is_signed": True}
    pointer_nonnull = _cond("INT_NOTEQUAL", pointer_expr, _const(0, size=8))
    positive = _cond("INT_SLESS", _const(0), count_expr)
    flag_guard = _cond("INT_NOTEQUAL", _param("flag"), _const(0))
    masked_count = Expression.binary_op(
        "INT_AND",
        count_expr,
        Expression.constant(0xFFFFFFFF, size=4),
    )
    masked_count.size = 4
    selector_expr = Expression.binary_op(
        "INT_NOTEQUAL",
        Expression.binary_op("INT_SUB", masked_count, _const(1)),
        _const(0),
    )
    selector_expr.size = 1
    singleton_selector = Condition(selector_expr, negated=True)
    ret = ReturnInfo(
        address="0x1000",
        value=_mem("param_1", 0),
        conditions=[pointer_nonnull, positive, singleton_selector, flag_guard],
    )

    assert not summarizer._readonly_exact_count_region_is_fully_covered_by_return(
        ret,
        [pointer_nonnull, positive],
        count_param,
        1,
    )
