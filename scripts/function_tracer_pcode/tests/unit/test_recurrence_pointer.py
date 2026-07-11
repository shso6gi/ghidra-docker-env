from scripts.function_tracer_pcode.tests.unit._recurrence_fixtures import *

def test_return_region_summary_coverage_accepts_pointer_guard_plus_count_partition():
    summarizer = StructuralRecurrenceSummarizer(tracer=None, debug=False)
    pointer = Expression.parameter("param_1", index=0, data_type="int *", size=8)
    count_wide = Expression.parameter("param_2", index=1, data_type="long", size=8)
    count_narrow = Expression.parameter("param_2", index=1, data_type="int", size=4)
    parameters = [
        {"name": "param_1", "index": 0, "size": 8, "data_type": "int *", "is_signed": False},
        {"name": "param_2", "index": 1, "size": 4, "data_type": "int", "is_signed": True},
    ]
    pointer_nonnull = _cond("INT_NOTEQUAL", pointer, Expression.constant(0, size=8))
    pointer_null = _cond("INT_EQUAL", pointer, Expression.constant(0, size=8))
    count_positive_wide = _cond("INT_SLESS", Expression.constant(0, size=8), count_wide)
    count_nonpositive_narrow = _cond("INT_SLESS", Expression.constant(0, size=4), count_narrow).negate()
    exact_pointer_null = ReturnInfo(
        address="0x1000",
        value=_const(-300),
        conditions=[pointer_null],
    )
    exact_count_nonpositive = ReturnInfo(
        address="0x1004",
        value=_const(-300),
        conditions=[pointer_nonnull, count_nonpositive_narrow],
    )

    coverage_key = summarizer._prove_summary_conditions_plus_exact_returns_cover_active_precondition(
        summary_conditions=[pointer_nonnull, count_positive_wide],
        exact_returns=[exact_pointer_null, exact_count_nonpositive],
        parameters=parameters,
    )

    assert coverage_key is not None

def test_counter_parameter_normalization_rejects_same_name_different_index():
    summarizer = StructuralRecurrenceSummarizer(PcodeTracer.__new__(PcodeTracer), debug=False)
    primary_counter = Expression.parameter("param_1", index=0, data_type="int", size=4)
    same_name_other_index = Expression.parameter("param_1", index=1, data_type="int", size=4)
    expr = Expression.binary_op("INT_SLESS", same_name_other_index, _const(1))

    normalized = summarizer._normalize_counter_parameter_expression(
        expr,
        {"name": "param_1", "index": 0, "size": 4, "data_type": "int"},
        primary_counter,
    )

    assert normalized is expr
    assert normalized.operands[0] is same_name_other_index

def test_counted_scalar_declines_address_like_constant_iteration_bias_without_context(monkeypatch):
    summarizer = StructuralRecurrenceSummarizer(PcodeTracer.__new__(PcodeTracer), debug=False)

    monkeypatch.setattr(summarizer, "_constant_resolves_to_executable_address", lambda value: value == 0x100278)

    assert summarizer._residue_cases_contain_readonly_affine_literal_address(
        (
            ResidueLoopCase(
                modulus=1,
                residue=0,
                affine=(0, 0x100278),
                affine_from_readonly_literal=False,
                affine_from_address_literal=False,
            ),
        )
    )

def test_extract_residue_case_marks_address_literal_access_provenance(monkeypatch):
    summarizer = StructuralRecurrenceSummarizer(PcodeTracer.__new__(PcodeTracer), debug=False)
    counter = _param("__loop_iv")
    address_lane = Expression.binary_op("SUBPIECE", Expression.constant(0x100278, size=8), _const(0))
    delta = Expression.binary_op("INT_ADD", counter, address_lane)

    monkeypatch.setattr(summarizer, "_constant_resolves_to_executable_address", lambda value: value == 0x100278)
    residue_cases = summarizer._extract_residue_loop_cases(
        (CountedLoopUpdateCase(conditions=(), update_expr=delta, delta_expr=delta),),
        "__loop_iv",
    )

    assert residue_cases is not None
    assert residue_cases[0].affine_from_address_literal is True
    assert summarizer._residue_cases_contain_readonly_affine_literal_address(residue_cases)

def test_extract_residue_case_does_not_mark_plain_function_body_immediate_as_address_literal_provenance():
    summarizer = StructuralRecurrenceSummarizer(PcodeTracer.__new__(PcodeTracer), debug=False)
    counter = _param("__loop_iv")
    delta = Expression.binary_op("INT_ADD", counter, Expression.constant(0x100278, size=4))

    residue_cases = summarizer._extract_residue_loop_cases(
        (CountedLoopUpdateCase(conditions=(), update_expr=delta, delta_expr=delta),),
        "__loop_iv",
        function_body_ranges=((0x100000, 0x100300),),
    )

    assert residue_cases is not None
    assert residue_cases[0].affine == (1, 0x100278)
    assert residue_cases[0].affine_from_address_literal is False
    assert not summarizer._residue_cases_contain_readonly_affine_literal_address(residue_cases)

def test_extract_residue_case_marks_function_body_address_literal_provenance_in_subpiece_context():
    summarizer = StructuralRecurrenceSummarizer(PcodeTracer.__new__(PcodeTracer), debug=False)
    counter = _param("__loop_iv")
    address_lane = Expression.binary_op("SUBPIECE", Expression.constant(0x100278, size=8), _const(0))
    delta = Expression.binary_op("INT_ADD", counter, address_lane)

    residue_cases = summarizer._extract_residue_loop_cases(
        (CountedLoopUpdateCase(conditions=(), update_expr=delta, delta_expr=delta),),
        "__loop_iv",
        function_body_ranges=((0x100000, 0x100300),),
    )

    assert residue_cases is not None
    assert residue_cases[0].affine_from_address_literal is True
    assert summarizer._residue_cases_contain_readonly_affine_literal_address(residue_cases)

def test_varnode_matches_parameter_accepts_parameter_index_or_storage_identity():
    index_symbol = _FakeHighSymbol(category_index=1)
    indexed_varnode = _FakeVarnode("renamed", high=_FakeHighVar("renamed", symbol=index_symbol))
    storage = _register_storage("x0", offset=0x4000, size=8)
    storage_varnode = _FakeVarnode("local_alias")
    parameter_by_index = {"name": "count", "index": 1, "size": 4}
    parameter_by_storage = {
        "name": "base",
        "index": -1,
        "size": 8,
        "storage": storage.to_dict(),
    }
    summarizer = StructuralRecurrenceSummarizer(
        _IdentityTracer(storages={storage_varnode: storage}),
        debug=False,
    )

    assert summarizer._varnode_matches_parameter(indexed_varnode, parameter_by_index) is True
    assert summarizer._varnode_matches_parameter(storage_varnode, parameter_by_storage) is True

def test_extract_index_step_accepts_subtractive_phi_updates():
    phi_output = _FakeVarnode("loop_aux")
    one_vn = _FakeVarnode("one", expr=_const(1))
    next_vn = _FakeVarnode("loop_aux_next")
    _FakePcodeOp("INT_SUB", [phi_output, one_vn], next_vn)

    tracer = _FakeTracer("unused", Expression.unknown("untraced"))
    tracer.trace_varnode = lambda varnode, *args, **kwargs: getattr(varnode, "_expr", None)
    summarizer = StructuralRecurrenceSummarizer(tracer, debug=False)

    assert summarizer._extract_index_step(next_vn, phi_output) == -1

def test_counted_loop_accumulator_extraction_rejects_executable_address_seed():
    header = _FakeCfgBlock(1)
    body = _FakeCfgBlock(2)
    header.add_edge(body)
    body.add_edge(header)

    text_space = _FakeAddressSpace("ram", space_id=1, is_memory=True)
    program = _FakeProgram(
        _FakeAddressFactory({1: text_space}, default_space=text_space),
        memory=_FakeMemory([_FakeMemoryBlock(0x100000, 0x101000, execute=False)]),
    )
    summarizer = StructuralRecurrenceSummarizer(
        _FakeTracer("unused", _const(0), program=program),
        debug=False,
    )

    zero_vn = _FakeVarnode("zero", expr=_const(0))
    one_vn = _FakeVarnode("one", expr=_const(1))
    twenty_vn = _FakeVarnode("twenty", expr=_const(20))
    param_2_vn = _FakeVarnode("param_2", expr=_param("param_2"))
    address_seed_vn = _FakeVarnode(
        "address_seed",
        expr=Expression.binary_op("INT_ADD", _param("param_2"), _const(0x100100)),
    )

    iv_phi_vn = _FakeVarnode("iv_phi")
    iv_next_vn = _FakeVarnode("iv_next")
    _FakePcodeOp("INT_ADD", [iv_phi_vn, one_vn], iv_next_vn).setParent(body)
    iv_phi_op = _FakePcodeOp("MULTIEQUAL", [zero_vn, iv_next_vn], iv_phi_vn)

    bad_phi_vn = _FakeVarnode("bad_acc")
    bad_next_vn = _FakeVarnode("bad_next")
    _FakePcodeOp("INT_ADD", [bad_phi_vn, twenty_vn], bad_next_vn).setParent(body)
    bad_phi_op = _FakePcodeOp("MULTIEQUAL", [address_seed_vn, bad_next_vn], bad_phi_vn)

    good_phi_vn = _FakeVarnode("good_acc")
    good_next_vn = _FakeVarnode("good_next")
    _FakePcodeOp("INT_ADD", [good_phi_vn, twenty_vn], good_next_vn).setParent(body)
    good_phi_op = _FakePcodeOp("MULTIEQUAL", [param_2_vn, good_next_vn], good_phi_vn)

    induction = CountedLoopInduction(
        phi_op=iv_phi_op,
        phi_output=iv_phi_vn,
        init_expr=_const(0),
        backedge_index=1,
        step=1,
        placeholder=Expression.parameter("__loop_iv", index=-10000, size=4),
        signed_guard=False,
        init_index=0,
        backedge_indices=(1,),
    )

    accumulators = summarizer._match_counted_loop_accumulators(
        [iv_phi_op, bad_phi_op, good_phi_op],
        induction,
        body,
        function_body_ranges=((0x100000, 0x101000),),
    )

    assert [accumulator.phi_output for accumulator in accumulators] == [good_phi_vn]

def test_loop_side_effect_profile_records_pcode_store_address_and_value():
    address = Expression.parameter("out", index=0, data_type="int *", size=8)
    value = Expression.binary_op("INT_ADD", _param("param_1"), _const(1))
    body = _FakeCfgBlock(
        1,
        ops=[
            _FakePcodeOp(
                "STORE",
                [_FakeVarnode("ram"), _FakeArgVarnode(address), _FakeArgVarnode(value)],
                None,
            ),
        ],
    )
    summarizer = StructuralRecurrenceSummarizer(_FakeTracer("unused", _const(0)), debug=False)

    profile = summarizer._build_loop_side_effect_profile(loop_blocks=[body])

    assert profile.profile == "effect_aware"
    assert profile.memory_writes is True
    assert len(profile.effect_descriptors) == 1
    effect = profile.effect_descriptors[0]
    assert effect.kind == "memory_write"
    assert effect.keyable is True
    assert effect.address_space["space_name"] == "ram"
    assert effect.location.equals(address)
    assert effect.value_expr.equals(value)
    assert effect.stable_key() is not None

def test_loop_store_address_space_uses_program_address_factory_target_space():
    address = Expression.parameter("out", index=0, data_type="int *", size=8)
    value = _const(7)
    store_space = _FakeStoreSpaceVarnode(target_space_id=1)
    body = _FakeCfgBlock(
        1,
        ops=[
            _FakePcodeOp(
                "STORE",
                [store_space, _FakeArgVarnode(address), _FakeArgVarnode(value)],
                None,
            ),
        ],
    )
    tracer = _FakeTracer("unused", _const(0))
    tracer.program = _FakeProgram(
        _FakeAddressFactory({
            1: _FakeAddressSpace(
                "ram",
                space_id=1,
                space_type=17,
                is_memory=True,
                is_register=False,
                is_stack=False,
            ),
        })
    )
    summarizer = StructuralRecurrenceSummarizer(tracer, debug=False)

    profile = summarizer._build_loop_side_effect_profile(loop_blocks=[body])

    effect = profile.effect_descriptors[0]
    assert effect.address_space["encoding"] == "ghidra_store_space_id"
    assert effect.address_space["space_name"] == "ram"
    assert effect.address_space["space_id"] == 1
    assert effect.address_space["is_memory_space"] is True
    assert effect.address_space["pcode_space_id_constant"] == 1
    assert effect.address_space["pcode_input_space"]["space_name"] == "const"
    assert effect.stable_key() is not None

def test_tail_start_from_peeled_rounded_count_accepts_low_bit_or_index():
    pointer_expr = Expression.parameter("param_1", index=0, data_type="int *", size=8)
    pointer_vn = _FakeVarnode("param_1", size=8, expr=pointer_expr)
    count_expr = Expression.parameter("param_2", index=1, data_type="int", size=4)
    count_vn = _FakeVarnode("param_2", size=4, expr=count_expr)
    three_vn = _FakeVarnode("three", size=8, expr=Expression.constant(3, size=8))
    peeled_vn = _FakeVarnode("peeled", size=8)
    peeled_op = _FakePcodeOp("INT_SUB", [count_vn, three_vn], peeled_vn)
    mask_vn = _FakeVarnode("mask", size=8, expr=Expression.constant(0xFFFFFFFFFFFFFFF8, size=8))
    rounded_vn = _FakeVarnode("rounded", size=8)
    rounded_op = _FakePcodeOp("INT_AND", [peeled_vn, mask_vn], rounded_vn)
    rounded_or_three = _FakeVarnode("rounded_or_three", size=8)
    or_op = _FakePcodeOp("INT_OR", [rounded_vn, three_vn], rounded_or_three)
    four_vn = _FakeVarnode("four", size=8, expr=Expression.constant(4, size=8))
    tail_start_vn = _FakeVarnode("tail_start", size=8)
    tail_start_op = _FakePcodeOp("PTRADD", [pointer_vn, rounded_or_three, four_vn], tail_start_vn)
    summarizer = StructuralRecurrenceSummarizer(_FakeTracer("unused", _const(0)), debug=False)

    assert summarizer._tail_start_varnodes_from_rounded_count(
        [peeled_op, rounded_op, or_op, tail_start_op],
        {"name": "param_1", "index": 0, "data_type": "int *", "size": 8},
        rounded_vn,
        element_size=4,
        start_offset=12,
    ) == (tail_start_vn,)

def test_tail_start_from_peeled_rounded_count_accepts_tail_index_phi():
    pointer_expr = Expression.parameter("param_1", index=0, data_type="int *", size=8)
    pointer_vn = _FakeVarnode("param_1", size=8, expr=pointer_expr)
    count_expr = Expression.parameter("param_2", index=1, data_type="int", size=4)
    count_vn = _FakeVarnode("param_2", size=4, expr=count_expr)
    three_vn = _FakeVarnode("three", size=8, expr=Expression.constant(3, size=8))
    peeled_vn = _FakeVarnode("peeled", size=8)
    peeled_op = _FakePcodeOp("INT_SUB", [count_vn, three_vn], peeled_vn)
    mask_vn = _FakeVarnode("mask", size=8, expr=Expression.constant(0xFFFFFFFFFFFFFFF8, size=8))
    rounded_vn = _FakeVarnode("rounded", size=8)
    rounded_op = _FakePcodeOp("INT_AND", [peeled_vn, mask_vn], rounded_vn)
    rounded_or_three = _FakeVarnode("rounded_or_three", size=8)
    or_op = _FakePcodeOp("INT_OR", [rounded_vn, three_vn], rounded_or_three)
    tail_index_phi = _FakeVarnode("tail_index_phi", size=8)
    phi_op = _FakePcodeOp("MULTIEQUAL", [three_vn, rounded_or_three], tail_index_phi)
    four_vn = _FakeVarnode("four", size=8, expr=Expression.constant(4, size=8))
    tail_start_vn = _FakeVarnode("tail_start", size=8)
    tail_start_op = _FakePcodeOp("PTRADD", [pointer_vn, tail_index_phi, four_vn], tail_start_vn)
    summarizer = StructuralRecurrenceSummarizer(_FakeTracer("unused", _const(0)), debug=False)

    assert summarizer._tail_start_varnodes_from_rounded_count(
        [peeled_op, rounded_op, or_op, phi_op, tail_start_op],
        {"name": "param_1", "index": 0, "data_type": "int *", "size": 8},
        rounded_vn,
        element_size=4,
        start_offset=12,
    ) == (tail_start_vn,)

def test_count_minus_rounded_accepts_tail_index_phi():
    count_expr = Expression.parameter("param_2", index=1, data_type="int", size=4)
    count_vn = _FakeVarnode("param_2", size=4, expr=count_expr)
    three_vn = _FakeVarnode("three", size=8, expr=Expression.constant(3, size=8))
    peeled_vn = _FakeVarnode("peeled", size=8)
    peeled_op = _FakePcodeOp("INT_SUB", [count_vn, three_vn], peeled_vn)
    mask_vn = _FakeVarnode("mask", size=8, expr=Expression.constant(0xFFFFFFFFFFFFFFF8, size=8))
    rounded_vn = _FakeVarnode("rounded", size=8)
    rounded_op = _FakePcodeOp("INT_AND", [peeled_vn, mask_vn], rounded_vn)
    rounded_or_three = _FakeVarnode("rounded_or_three", size=8)
    or_op = _FakePcodeOp("INT_OR", [rounded_vn, three_vn], rounded_or_three)
    tail_index_phi = _FakeVarnode("tail_index_phi", size=8)
    phi_op = _FakePcodeOp("MULTIEQUAL", [three_vn, rounded_or_three], tail_index_phi)
    remaining_vn = _FakeVarnode("remaining", size=8)
    remaining_op = _FakePcodeOp("INT_SUB", [count_vn, tail_index_phi], remaining_vn)
    summarizer = StructuralRecurrenceSummarizer(_FakeTracer("unused", _const(0)), debug=False)

    assert summarizer._varnode_is_count_minus_rounded(
        remaining_vn,
        {"name": "param_2", "index": 1, "data_type": "int", "size": 4},
        rounded_vn,
        start_index=3,
    )

def test_structural_recurrence_summarizer_infers_pointer_parameter_object_centrically():
    params = [
        {"name": "param_1", "index": 0, "data_type": "long", "size": 8},
        {"name": "param_2", "index": 1, "data_type": "uint", "size": 4, "is_signed": False},
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
                    _cond("INT_SLESSEQUAL", Expression.parameter("param_2", index=1, data_type="uint", size=4), _const(0)),
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
                        Expression.parameter("param_1", index=0, data_type="long", size=8),
                        Expression.constant(0, size=8),
                    ),
                    _cond("INT_SLESS", _const(0), Expression.parameter("param_2", index=1, data_type="uint", size=4)),
                ],
            ),
        ],
    )

    ptr_param = _FakeVarnode(
        "param_1",
        size=8,
        expr=Expression.parameter("param_1", index=0, data_type="long", size=8),
    )
    count_param = _FakeVarnode(
        "param_2",
        size=4,
        expr=Expression.parameter("param_2", index=1, data_type="uint", size=4),
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
    assert positive_case.value.runtime_ref.pointer_base_ref.parameter_index == 0
    assert positive_case.value.runtime_ref.count_parameter_index == 1
    assert [cond.to_string() for cond in positive_case.conditions] == ["(param_1 != 0)", "(0 < param_2)"]

def test_structural_recurrence_matches_address_space_qualified_pcode_identity():
    summarizer = StructuralRecurrenceSummarizer(tracer=None, debug=False)
    ret = ReturnInfo(
        address="ram:00001000",
        pcode_identity="ram:00001000:t23:o1",
        conditions=[],
        value=_const(0),
    )
    ref = PcodeOpRef(address_offset=0x1000, seq_time=23, seq_order=1, mnemonic="RETURN")

    assert summarizer._return_info_matches_pcode_op_ref(ret, ref) is True

def test_structural_recurrence_builds_ref_from_address_space_qualified_identity():
    summarizer = StructuralRecurrenceSummarizer(tracer=None, debug=False)
    ret = ReturnInfo(
        address="unknown",
        pcode_identity="ram:00001000:t23:o1",
        conditions=[],
        value=_const(0),
    )

    ref = summarizer._pcode_op_ref_from_return_info(ret)

    assert ref == PcodeOpRef(address_offset=0x1000, seq_time=23, seq_order=1, mnemonic=None)

def test_structural_recurrence_rejects_address_only_region_value_site():
    summarizer = StructuralRecurrenceSummarizer(tracer=None, debug=False)
    ret = ReturnInfo(
        address="0x1008",
        conditions=[],
        value=_const(0),
    )
    ref = PcodeOpRef(address_offset=0x1008, mnemonic="RETURN")

    assert summarizer._return_info_matches_pcode_op_ref(ret, ref) is False
