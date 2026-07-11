from scripts.function_tracer_pcode.tests.unit._recurrence_fixtures import *

def test_counted_loop_affine_case_preserves_parameter_bias_expression():
    summarizer = StructuralRecurrenceSummarizer(PcodeTracer.__new__(PcodeTracer), debug=False)
    counter = _param("__loop_iv")
    bias = _param("param_2")
    scaled = Expression.binary_op("INT_MULT", Expression.constant(5, size=4), counter)
    scaled.size = 4
    delta = Expression.binary_op("INT_ADD", scaled, bias)
    delta.size = 4

    affine_case = summarizer._extract_affine_loop_case(delta, "__loop_iv")

    assert affine_case is not None
    affine, bias_expr = affine_case
    assert affine == (5, 0)
    assert bias_expr is not None
    assert bias_expr.structural_key() == bias.structural_key()

def test_counted_loop_affine_case_rejects_loop_carried_variable_bias_expression():
    summarizer = StructuralRecurrenceSummarizer(PcodeTracer.__new__(PcodeTracer), debug=False)
    counter = _param("__loop_iv")
    loop_carried = Expression.variable("__other_loop_state", size=4)
    scaled = Expression.binary_op("INT_MULT", Expression.constant(5, size=4), counter)
    scaled.size = 4
    delta = Expression.binary_op("INT_ADD", scaled, loop_carried)
    delta.size = 4

    affine_case = summarizer._extract_affine_loop_case(delta, "__loop_iv")

    assert affine_case is None

def test_counted_loop_update_validation_rejects_non_affine_update_semantics():
    summarizer = StructuralRecurrenceSummarizer(PcodeTracer.__new__(PcodeTracer), debug=False)
    loop_iv = Expression.parameter("__loop_iv", index=-10000, size=4)
    loop_acc = Expression.variable("__loop_acc", size=4)
    induction = CountedLoopInduction(
        phi_op=object(),
        phi_output=object(),
        init_expr=_const(0),
        backedge_index=1,
        step=1,
        placeholder=loop_iv,
        signed_guard=False,
    )
    accumulator = CountedLoopAccumulator(
        phi_op=None,
        phi_output=None,
        init_expr=_const(0),
        backedge_index=1,
        placeholder=loop_acc,
    )
    actual_update = Expression.binary_op("INT_ADD", loop_acc, loop_iv)
    actual_update.size = 4
    wrong_delta = Expression.constant(-1, 4)
    case = CountedLoopUpdateCase(
        conditions=(),
        update_expr=actual_update,
        delta_expr=wrong_delta,
    )

    assert not summarizer._validate_counted_loop_update_cases(
        cases=(case,),
        residue_cases=(ResidueLoopCase(modulus=1, residue=0, affine=(0, -1)),),
        induction=induction,
        accumulator=accumulator,
    )

def test_counted_loop_update_validation_accepts_solver_proven_affine_update():
    summarizer = StructuralRecurrenceSummarizer(PcodeTracer.__new__(PcodeTracer), debug=False)
    loop_iv = Expression.parameter("__loop_iv", index=-10000, size=4)
    loop_acc = Expression.variable("__loop_acc", size=4)
    even_condition = _cond(
        "INT_EQUAL",
        Expression.binary_op("INT_AND", loop_iv, _const(1)),
        _const(0),
    )
    update_expr = Expression.binary_op("INT_ADD", loop_acc, loop_iv)
    update_expr.size = 4
    case = CountedLoopUpdateCase(
        conditions=(even_condition,),
        update_expr=update_expr,
        delta_expr=loop_iv,
    )
    induction = CountedLoopInduction(
        phi_op=object(),
        phi_output=object(),
        init_expr=_const(0),
        backedge_index=1,
        step=1,
        placeholder=loop_iv,
        signed_guard=False,
    )
    accumulator = CountedLoopAccumulator(
        phi_op=None,
        phi_output=None,
        init_expr=_const(0),
        backedge_index=1,
        placeholder=loop_acc,
    )

    assert summarizer._validate_counted_loop_update_cases(
        cases=(case,),
        residue_cases=(ResidueLoopCase(modulus=2, residue=0, affine=(1, 0)),),
        induction=induction,
        accumulator=accumulator,
    )

def test_counted_scalar_keeps_plain_affine_bias_equal_to_executable_address_without_provenance(monkeypatch):
    summarizer = StructuralRecurrenceSummarizer(PcodeTracer.__new__(PcodeTracer), debug=False)

    monkeypatch.setattr(summarizer, "_constant_resolves_to_executable_address", lambda value: value == 0x100278)

    assert not summarizer._residue_cases_contain_readonly_affine_literal_address(
        (
            ResidueLoopCase(
                modulus=1,
                residue=0,
                affine=(1, 0x100278),
                affine_from_readonly_literal=False,
                affine_from_address_literal=False,
            ),
        )
    )

def test_counted_scalar_declines_affine_bias_with_address_literal_provenance(monkeypatch):
    summarizer = StructuralRecurrenceSummarizer(PcodeTracer.__new__(PcodeTracer), debug=False)

    monkeypatch.setattr(summarizer, "_constant_resolves_to_executable_address", lambda value: value == 0x100278)

    assert summarizer._residue_cases_contain_readonly_affine_literal_address(
        (
            ResidueLoopCase(
                modulus=1,
                residue=0,
                affine=(0, 0x100278),
                affine_from_readonly_literal=False,
                affine_from_address_literal=True,
            ),
        )
    )

def test_structural_recurrence_summarizer_rejects_non_affine_recursion():
    param = _param()
    unknown = Expression.unknown(
        "call_out_of_scope:fc_recursive_sum",
        runtime_ref=UnknownValueRef.out_of_scope_call(
            reason="call_out_of_scope",
            target_ref=CallTargetRef.from_name("fc_recursive_sum"),
            display_hint="fc_recursive_sum",
        ),
    )
    recursive_value = Expression.binary_op(
        "INT_ADD",
        unknown,
        Expression.binary_op("INT_MULT", param, param),
    )
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

    assert summary is None

def test_match_index_progression_phi_accepts_positive_non_unit_step():
    phi_output = _FakeVarnode("loop_index")
    init_vn = _FakeVarnode("zero", expr=_const(0))
    two_vn = _FakeVarnode("two", expr=_const(2))
    next_vn = _FakeVarnode("loop_index_next")
    _FakePcodeOp("INT_ADD", [phi_output, two_vn], next_vn)
    phi_op = _FakePcodeOp("MULTIEQUAL", [init_vn, next_vn], phi_output)
    summarizer = StructuralRecurrenceSummarizer(_FakeTracer("unused", _const(0)), debug=False)

    match = summarizer._match_index_progression_phi(phi_op)

    assert match is not None
    assert match["start"] == 0
    assert match["step"] == 2

def test_dynamic_index_step_is_parsed_but_not_accepted_as_constant_progression():
    phi_output = _FakeVarnode("loop_index")
    init_vn = _FakeVarnode("zero", expr=_const(0))
    step_expr = Expression.parameter("step", index=1, data_type="int", size=4)
    step_vn = _FakeVarnode("step", expr=step_expr)
    next_vn = _FakeVarnode("loop_index_next")
    _FakePcodeOp("INT_ADD", [phi_output, step_vn], next_vn)
    phi_op = _FakePcodeOp("MULTIEQUAL", [init_vn, next_vn], phi_output)
    summarizer = StructuralRecurrenceSummarizer(_FakeTracer("unused", _const(0)), debug=False)

    extracted_step = summarizer._extract_index_step_expression(next_vn, phi_output)

    assert extracted_step is not None
    assert extracted_step.equals(step_expr)
    assert summarizer._extract_index_step(next_vn, phi_output) is None
    assert summarizer._match_index_progression_phi(phi_op) is None

def test_affine_loop_state_phi_uses_entry_counter_placeholder():
    start_expr = Expression.binary_op("INT_AND", _param("param_1"), _const(0xFFFFFFF8))
    one_vn = _FakeVarnode("one", expr=_const(1))
    iv_entry_vn = _FakeVarnode("iv_entry", expr=start_expr)

    header = _FakeCfgBlock(0)
    latch = _FakeCfgBlock(1)
    header.add_edge(latch)
    latch.add_edge(header)

    iv_phi_vn = _FakeVarnode("iv_phi")
    iv_next_vn = _FakeVarnode("iv_next")
    aux_init_vn = _FakeVarnode("aux_init")
    aux_phi_vn = _FakeVarnode("aux_phi")
    aux_next_vn = _FakeVarnode("aux_next")

    iv_phi_op = _FakePcodeOp("MULTIEQUAL", [iv_entry_vn, iv_next_vn], iv_phi_vn)
    aux_init_op = _FakePcodeOp("INT_2COMP", [iv_entry_vn], aux_init_vn)
    aux_phi_op = _FakePcodeOp("MULTIEQUAL", [aux_init_vn, aux_next_vn], aux_phi_vn)
    header._ops[:] = [aux_phi_op, iv_phi_op]
    for op in header._ops:
        op.setParent(header)

    iv_next_op = _FakePcodeOp("INT_ADD", [iv_phi_vn, one_vn], iv_next_vn)
    aux_next_op = _FakePcodeOp("INT_SUB", [aux_phi_vn, one_vn], aux_next_vn)
    latch._ops[:] = [iv_next_op, aux_next_op]
    for op in latch._ops:
        op.setParent(latch)

    summarizer = StructuralRecurrenceSummarizer(_FakeTracer("unused", _const(0)), debug=False)
    induction = summarizer._match_counted_loop_induction(iv_phi_op)

    assert induction is not None
    aux_expr = summarizer._summarize_affine_loop_state_phi(aux_phi_op, induction)

    assert aux_expr is not None
    assert summarizer._extract_affine_term(aux_expr, "__loop_iv") == (-1, 0)

def test_multiplicative_accumulator_delta_accepts_left_shift_multiplier():
    summarizer = StructuralRecurrenceSummarizer(_FakeTracer("unused", _const(0)), debug=False)
    accumulator = Expression.variable("__state", size=4)
    shifted = Expression.binary_op("INT_LEFT", accumulator, _const(1))
    shifted.size = 4
    reversed_shift = Expression.binary_op("INT_LEFT", _const(1), accumulator)
    reversed_shift.size = 4
    huge_shift = Expression.binary_op("INT_LEFT", accumulator, _const(31))
    huge_shift.size = 4

    assert summarizer._multiplicative_accumulator_delta_multiplier(shifted, accumulator) == 2
    assert summarizer._multiplicative_accumulator_delta_multiplier(reversed_shift, accumulator) is None
    assert summarizer._multiplicative_accumulator_delta_multiplier(huge_shift, accumulator) is None

def test_multiplicative_phi_return_region_recovers_direct_state_value():
    phi_value = Expression.unknown("phi_circular")
    recursive_value = Expression.binary_op("INT_MULT", phi_value, _const(2))
    recursive_value.size = 4
    analysis = create_mock_analysis(
        "multiplicative_phi_region",
        return_type="int",
        parameters=[{"name": "param_1", "index": 0, "data_type": "int", "size": 4, "is_signed": True}],
        returns=[
            ReturnInfo(
                address="0x1000",
                value=_const(0),
                conditions=[_cond("INT_SLESSEQUAL", _param("param_1"), _const(0))],
            ),
            ReturnInfo(
                address="0x1004",
                value=_const(1),
                conditions=[_cond("INT_SLESS", _const(0), _param("param_1"))],
                return_kind="phi_expansion",
            ),
            ReturnInfo(
                address="0x1008",
                value=recursive_value,
                conditions=[_cond("INT_SLESS", _const(0), _param("param_1"))],
                return_kind="phi_expansion",
            ),
        ],
    )

    summarizer = StructuralRecurrenceSummarizer(_FakeTracer("unused", _const(0)), debug=False)
    summary = summarizer._try_summarize_multiplicative_phi_return_region(
        _FakeFunction("multiplicative_phi_region"),
        _build_decrement_accumulator_sum_cfg(),
        analysis,
    )

    assert summary is not None
    summarized_returns, note = summary
    assert note == "multiplicative_phi_return_region_summary"
    assert len(summarized_returns) == 2
    positive_case = next(
        ret
        for ret in summarized_returns
        if ret.value.opcode == COUNTED_STATE_TRANSITION_VALUE_OPCODE
    )
    assert positive_case.conditions[0].to_string() == "(0 < param_1)"
    assert positive_case.value.opcode == COUNTED_STATE_TRANSITION_VALUE_OPCODE
    assert isinstance(positive_case.value.runtime_ref, CountedStateTransitionLoopSummaryRef)
    assert expression_has_unresolved_value(positive_case.value) is False
    positive_smt = expression_to_smt(positive_case.value)
    assert "rt_counted_state_transition_value_" not in positive_smt
    assert "pow_acc" in positive_smt
    assert positive_case.summary_transition_evidence_key is not None

def test_multiplicative_phi_return_region_rejects_mixed_recursive_multipliers():
    phi_value = Expression.unknown("phi_circular")
    recursive_value_2 = Expression.binary_op("INT_MULT", phi_value, _const(2))
    recursive_value_2.size = 4
    recursive_value_3 = Expression.binary_op("INT_MULT", phi_value, _const(3))
    recursive_value_3.size = 4
    analysis = create_mock_analysis(
        "multiplicative_phi_region",
        return_type="int",
        parameters=[{"name": "param_1", "index": 0, "data_type": "int", "size": 4, "is_signed": True}],
        returns=[
            ReturnInfo(
                address="0x1000",
                value=_const(0),
                conditions=[_cond("INT_SLESSEQUAL", _param("param_1"), _const(0))],
            ),
            ReturnInfo(
                address="0x1004",
                value=_const(1),
                conditions=[_cond("INT_SLESS", _const(0), _param("param_1"))],
                return_kind="phi_expansion",
            ),
            ReturnInfo(
                address="0x1008",
                value=recursive_value_2,
                conditions=[_cond("INT_SLESS", _const(0), _param("param_1"))],
                return_kind="phi_expansion",
            ),
            ReturnInfo(
                address="0x100c",
                value=recursive_value_3,
                conditions=[_cond("INT_SLESS", _const(0), _param("param_1"))],
                return_kind="phi_expansion",
            ),
        ],
    )

    summarizer = StructuralRecurrenceSummarizer(_FakeTracer("unused", _const(0)), debug=False)

    assert summarizer._try_summarize_multiplicative_phi_return_region(
        _FakeFunction("multiplicative_phi_region"),
        _build_decrement_accumulator_sum_cfg(),
        analysis,
    ) is None

def test_multiplicative_phi_return_region_keeps_nonzero_base_exact_return():
    phi_value = Expression.unknown("phi_circular")
    recursive_value = Expression.binary_op("INT_MULT", phi_value, _const(2))
    recursive_value.size = 4
    analysis = create_mock_analysis(
        "multiplicative_phi_region",
        return_type="int",
        parameters=[{"name": "param_1", "index": 0, "data_type": "int", "size": 4, "is_signed": True}],
        returns=[
            ReturnInfo(
                address="0x1000",
                value=_const(1),
                conditions=[_cond("INT_SLESSEQUAL", _param("param_1"), _const(0))],
            ),
            ReturnInfo(
                address="0x1004",
                value=_const(1),
                conditions=[_cond("INT_SLESS", _const(0), _param("param_1"))],
                return_kind="phi_expansion",
            ),
            ReturnInfo(
                address="0x1008",
                value=recursive_value,
                conditions=[_cond("INT_SLESS", _const(0), _param("param_1"))],
                return_kind="phi_expansion",
            ),
        ],
    )

    summarizer = StructuralRecurrenceSummarizer(_FakeTracer("unused", _const(0)), debug=False)

    summary = summarizer._try_summarize_multiplicative_phi_return_region(
        _FakeFunction("multiplicative_phi_region"),
        _build_decrement_accumulator_sum_cfg(),
        analysis,
    )

    assert summary is not None
    summarized_returns, _note = summary
    assert len(summarized_returns) == 1
    assert summarized_returns[0].value.opcode == COUNTED_STATE_TRANSITION_VALUE_OPCODE

def test_multiplicative_phi_return_region_rejects_unconditional_conflicting_zero_return():
    phi_value = Expression.unknown("phi_circular")
    recursive_value = Expression.binary_op("INT_MULT", phi_value, _const(2))
    recursive_value.size = 4
    analysis = create_mock_analysis(
        "multiplicative_phi_region",
        return_type="int",
        parameters=[{"name": "param_1", "index": 0, "data_type": "int", "size": 4, "is_signed": True}],
        returns=[
            ReturnInfo(address="0x1000", value=_const(0), conditions=[]),
            ReturnInfo(
                address="0x1004",
                value=_const(1),
                conditions=[_cond("INT_SLESS", _const(0), _param("param_1"))],
                return_kind="phi_expansion",
            ),
            ReturnInfo(
                address="0x1008",
                value=recursive_value,
                conditions=[_cond("INT_SLESS", _const(0), _param("param_1"))],
                return_kind="phi_expansion",
            ),
        ],
    )

    summarizer = StructuralRecurrenceSummarizer(_FakeTracer("unused", _const(0)), debug=False)
    summary = summarizer._try_summarize_multiplicative_phi_return_region(
        _FakeFunction("multiplicative_phi_region"),
        _build_decrement_accumulator_sum_cfg(),
        analysis,
    )

    assert summary is None

def test_multiplicative_phi_return_region_uses_common_bounded_guard_and_keeps_outer_zero():
    n = _param("param_1")
    n_minus_one = Expression.binary_op("INT_SUB", n, _const(1))
    n_minus_one.size = 4
    bounded_guard = _cond("INT_LESS", n_minus_one, _const(4))
    seed_guard = _cond("INT_EQUAL", n_minus_one, _const(0))
    recursive_guard = _cond("INT_NOTEQUAL", n_minus_one, _const(0))
    outer_zero_guard = _cond("INT_LESSEQUAL", _const(4), n_minus_one)
    phi_value = Expression.unknown("phi_circular")
    recursive_value = Expression.binary_op("INT_MULT", phi_value, _const(2))
    recursive_value.size = 4
    zero_return = ReturnInfo(
        address="0x1000",
        value=_const(0),
        conditions=[outer_zero_guard],
    )
    analysis = create_mock_analysis(
        "multiplicative_phi_region",
        return_type="int",
        parameters=[{"name": "param_1", "index": 0, "data_type": "int", "size": 4, "is_signed": True}],
        returns=[
            zero_return,
            ReturnInfo(
                address="0x1004",
                value=_const(1),
                conditions=[bounded_guard, seed_guard],
            ),
            ReturnInfo(
                address="0x1008",
                value=recursive_value,
                conditions=[bounded_guard, recursive_guard],
                return_kind="phi_expansion",
            ),
        ],
    )

    summarizer = StructuralRecurrenceSummarizer(_FakeTracer("unused", _const(0)), debug=False)
    summary = summarizer._try_summarize_multiplicative_phi_return_region(
        _FakeFunction("multiplicative_phi_region"),
        _build_decrement_accumulator_sum_cfg(),
        analysis,
    )

    assert summary is not None
    summarized_returns, note = summary
    assert note == "multiplicative_phi_return_region_summary"
    assert len(summarized_returns) == 1
    positive_case = summarized_returns[0]
    assert [condition.to_string() for condition in positive_case.conditions] == [
        "((param_1 - 1) < 4)",
        "(0 < param_1)",
    ]
    proof_target = positive_case.summary_transition_evidence_key[2]
    superseded_keys = proof_target[6][1]
    assert summarizer._return_info_summary_identity_key(zero_return) not in superseded_keys

def test_multiplicative_phi_return_region_keeps_common_negated_bounded_guard():
    n = _param("param_1")
    n_minus_one = Expression.binary_op("INT_SUB", n, _const(1))
    n_minus_one.size = 4
    outer_zero_guard = _cond("INT_LESSEQUAL", _const(4), n_minus_one)
    bounded_guard = outer_zero_guard.negate()
    seed_guard = _cond("INT_EQUAL", n_minus_one, _const(0))
    recursive_guard = _cond("INT_NOTEQUAL", n_minus_one, _const(0))
    phi_value = Expression.unknown("phi_circular")
    recursive_value = Expression.binary_op("INT_MULT", phi_value, _const(2))
    recursive_value.size = 4
    zero_return = ReturnInfo(
        address="0x1000",
        value=_const(0),
        conditions=[outer_zero_guard],
    )
    analysis = create_mock_analysis(
        "multiplicative_phi_region",
        return_type="int",
        parameters=[{"name": "param_1", "index": 0, "data_type": "int", "size": 4, "is_signed": True}],
        returns=[
            zero_return,
            ReturnInfo(
                address="0x1004",
                value=_const(1),
                conditions=[bounded_guard, seed_guard],
            ),
            ReturnInfo(
                address="0x1008",
                value=recursive_value,
                conditions=[bounded_guard, recursive_guard],
                return_kind="phi_expansion",
            ),
        ],
    )

    summarizer = StructuralRecurrenceSummarizer(_FakeTracer("unused", _const(0)), debug=False)
    summary = summarizer._try_summarize_multiplicative_phi_return_region(
        _FakeFunction("multiplicative_phi_region"),
        _build_decrement_accumulator_sum_cfg(),
        analysis,
    )

    assert summary is not None
    summarized_returns, note = summary
    assert note == "multiplicative_phi_return_region_summary"
    assert len(summarized_returns) == 1
    positive_case = summarized_returns[0]
    assert [condition.to_string() for condition in positive_case.conditions] == [
        "(not (4 <= (param_1 - 1)))",
        "(0 < param_1)",
    ]
    proof_target = positive_case.summary_transition_evidence_key[2]
    superseded_keys = proof_target[6][1]
    assert summarizer._return_info_summary_identity_key(zero_return) not in superseded_keys

def test_multiplicative_phi_return_region_ignores_unrelated_high_function_multiplier():
    analysis = create_mock_analysis(
        "multiplicative_phi_region",
        return_type="int",
        parameters=[{"name": "param_1", "index": 0, "data_type": "int", "size": 4, "is_signed": True}],
        returns=[
            ReturnInfo(
                address="0x1000",
                value=_const(0),
                conditions=[_cond("INT_SLESSEQUAL", _param("param_1"), _const(0))],
            ),
            ReturnInfo(
                address="0x1004",
                value=_const(1),
                conditions=[_cond("INT_SLESS", _const(0), _param("param_1"))],
                return_kind="phi_expansion",
            ),
        ],
    )
    high_function = _build_decrement_accumulator_sum_cfg()
    unrelated_phi = _FakeVarnode("unrelated_phi")
    unrelated_next = _FakeVarnode("unrelated_next")
    _FakePcodeOp("MULTIEQUAL", [_FakeVarnode("seed", expr=_const(1)), unrelated_next], unrelated_phi)
    unrelated_mult = _FakePcodeOp(
        "INT_MULT",
        [unrelated_phi, _FakeConstantVarnode(2)],
        unrelated_next,
    )
    block = high_function.getBasicBlocks()[1]
    block._ops.append(unrelated_mult)
    unrelated_mult.setParent(block)

    summarizer = StructuralRecurrenceSummarizer(_FakeTracer("unused", _const(0)), debug=False)

    assert summarizer._try_summarize_multiplicative_phi_return_region(
        _FakeFunction("multiplicative_phi_region"),
        high_function,
        analysis,
    ) is None

def test_multiplicative_phi_return_region_rejects_high_function_multiplier_without_recursive_witness():
    analysis = create_mock_analysis(
        "multiplicative_phi_region",
        return_type="int",
        parameters=[{"name": "param_1", "index": 0, "data_type": "int", "size": 4, "is_signed": True}],
        returns=[
            ReturnInfo(
                address="0x1000",
                value=_const(0),
                conditions=[_cond("INT_SLESSEQUAL", _param("param_1"), _const(0))],
            ),
            ReturnInfo(
                address="0x1004",
                value=_const(1),
                conditions=[_cond("INT_SLESS", _const(0), _param("param_1"))],
                return_kind="phi_expansion",
            ),
        ],
    )
    high_function = _build_decrement_accumulator_sum_cfg()
    phi = _FakeVarnode("return_reaching_phi")
    next_value = _FakeVarnode("return_reaching_next")
    _FakePcodeOp("MULTIEQUAL", [_FakeVarnode("seed", expr=_const(1)), next_value], phi)
    mult = _FakePcodeOp("INT_MULT", [phi, _FakeConstantVarnode(2)], next_value)
    return_op = _FakePcodeOp("RETURN", [_FakeVarnode("return_target"), next_value], None)
    block = high_function.getBasicBlocks()[1]
    block._ops.extend([mult, return_op])
    mult.setParent(block)
    return_op.setParent(block)

    summarizer = StructuralRecurrenceSummarizer(_FakeTracer("unused", _const(0)), debug=False)

    assert summarizer._try_summarize_multiplicative_phi_return_region(
        _FakeFunction("multiplicative_phi_region"),
        high_function,
        analysis,
    ) is None

def test_multiplicative_phi_return_region_rejects_high_function_multiplier_without_recursive_value_proof():
    recursive_value = Expression.unknown("phi_circular")
    recursive_value.size = 4
    analysis = create_mock_analysis(
        "multiplicative_phi_region",
        return_type="int",
        parameters=[{"name": "param_1", "index": 0, "data_type": "int", "size": 4, "is_signed": True}],
        returns=[
            ReturnInfo(
                address="0x1000",
                value=_const(0),
                conditions=[_cond("INT_SLESSEQUAL", _param("param_1"), _const(0))],
            ),
            ReturnInfo(
                address="0x1004",
                value=_const(1),
                conditions=[_cond("INT_SLESS", _const(0), _param("param_1"))],
                return_kind="phi_expansion",
            ),
            ReturnInfo(
                address="0x1008",
                value=recursive_value,
                conditions=[_cond("INT_SLESS", _const(0), _param("param_1"))],
                return_kind="phi_expansion",
            ),
        ],
    )
    high_function = _build_decrement_accumulator_sum_cfg()
    phi = _FakeVarnode("return_reaching_phi")
    next_value = _FakeVarnode("return_reaching_next")
    _FakePcodeOp("MULTIEQUAL", [_FakeVarnode("seed", expr=_const(1)), next_value], phi)
    mult = _FakePcodeOp("INT_MULT", [phi, _FakeConstantVarnode(2)], next_value)
    return_op = _FakePcodeOp("RETURN", [_FakeVarnode("return_target"), next_value], None)
    block = high_function.getBasicBlocks()[1]
    block._ops.extend([mult, return_op])
    mult.setParent(block)
    return_op.setParent(block)

    summarizer = StructuralRecurrenceSummarizer(_FakeTracer("unused", _const(0)), debug=False)

    assert summarizer._try_summarize_multiplicative_phi_return_region(
        _FakeFunction("multiplicative_phi_region"),
        high_function,
        analysis,
    ) is None

def test_affine_loop_state_phi_supports_nonunit_induction_step():
    tracer = _FakeTracer("unused", _const(0))
    summarizer = StructuralRecurrenceSummarizer(tracer, debug=False)

    iv_phi_vn = _FakeVarnode("__loop_iv", size=4, high=_FakeHighVar("__loop_iv"))
    iv_next_vn = _FakeVarnode("iv_next", size=4)
    eight_vn = _FakeVarnode("eight", size=4, expr=_const(8))
    iv_init_vn = _FakeVarnode("iv_init", size=4, expr=_const(16))
    iv_step_op = _FakePcodeOp("INT_SUB", [iv_phi_vn, eight_vn], iv_next_vn)
    iv_phi_op = _FakePcodeOp("MULTIEQUAL", [iv_init_vn, iv_next_vn], iv_phi_vn)

    state_phi_vn = _FakeVarnode("lane", size=4, high=_FakeHighVar("lane"))
    state_next_vn = _FakeVarnode("lane_next", size=4)
    state_init_vn = _FakeVarnode("lane_init", size=4, expr=_const(0))
    state_delta_op = _FakePcodeOp("INT_ADD", [state_phi_vn, eight_vn], state_next_vn)
    state_phi_op = _FakePcodeOp("MULTIEQUAL", [state_init_vn, state_next_vn], state_phi_vn)

    induction = CountedLoopInduction(
        phi_op=iv_phi_op,
        phi_output=iv_phi_vn,
        init_expr=_const(16),
        backedge_index=1,
        step=-8,
        placeholder=Expression.parameter("__loop_iv", index=-10000, size=4),
        signed_guard=False,
    )

    expr = summarizer._summarize_affine_loop_state_phi(state_phi_op, induction)

    assert expr is not None
    assert summarizer._extract_affine_term(expr, "__loop_iv") == (-1, 16)

def test_pointer_progression_phi_tracks_peeled_pointer_seed_offset():
    pointer_expr = Expression.parameter("param_1", index=0, data_type="int *", size=8)
    pointer_vn = _FakeVarnode("param_1", size=8, expr=pointer_expr)
    three_vn = _FakeVarnode("three", size=8, expr=Expression.constant(3, size=8))
    four_vn = _FakeVarnode("four", size=8, expr=Expression.constant(4, size=8))
    init_vn = _FakeVarnode("init", size=8)
    init_op = _FakePcodeOp("PTRADD", [pointer_vn, three_vn, four_vn], init_vn)
    phi_vn = _FakeVarnode("ptr_phi", size=8, high=_FakeHighVar("ptr_phi"))
    next_vn = _FakeVarnode("next", size=8)
    next_op = _FakePcodeOp("PTRADD", [phi_vn, _FakeVarnode("one", size=8, expr=Expression.constant(1, size=8)), four_vn], next_vn)
    phi_op = _FakePcodeOp("MULTIEQUAL", [init_vn, next_vn], phi_vn)
    summarizer = StructuralRecurrenceSummarizer(_FakeTracer("unused", _const(0)), debug=False)

    assert init_op.getOutput() is init_vn
    assert next_op.getOutput() is next_vn
    assert summarizer._match_pointer_progression_phi(
        phi_op,
        {"name": "param_1", "index": 0, "data_type": "int *", "size": 8},
    ) == {
        "phi_op": phi_op,
        "phi_output": phi_vn,
        "stride": 4,
        "start_offset": 12,
        "start_index": 3,
        "index_step": 1,
        "index_scale": 4,
    }

def test_pointer_progression_phi_tracks_peeled_pointer_seed_offset_with_same_high():
    pointer_high = _FakeHighVar("param_1")
    pointer_expr = Expression.parameter("param_1", index=0, data_type="int *", size=8)
    pointer_vn = _FakeVarnode("param_1", size=8, expr=pointer_expr, high=pointer_high)
    three_vn = _FakeVarnode("three", size=8, expr=Expression.constant(3, size=8))
    four_vn = _FakeVarnode("four", size=8, expr=Expression.constant(4, size=8))
    init_vn = _FakeVarnode("init", size=8, high=pointer_high)
    init_op = _FakePcodeOp("PTRADD", [pointer_vn, three_vn, four_vn], init_vn)
    phi_vn = _FakeVarnode("ptr_phi", size=8, high=_FakeHighVar("ptr_phi"))
    next_vn = _FakeVarnode("next", size=8)
    next_op = _FakePcodeOp(
        "PTRADD",
        [phi_vn, _FakeVarnode("one", size=8, expr=Expression.constant(1, size=8)), four_vn],
        next_vn,
    )
    phi_op = _FakePcodeOp("MULTIEQUAL", [init_vn, next_vn], phi_vn)
    summarizer = StructuralRecurrenceSummarizer(_FakeTracer("unused", _const(0)), debug=False)

    assert init_op.getOutput() is init_vn
    assert next_op.getOutput() is next_vn
    assert summarizer._match_pointer_progression_phi(
        phi_op,
        {"name": "param_1", "index": 0, "data_type": "int *", "size": 8},
    ) == {
        "phi_op": phi_op,
        "phi_output": phi_vn,
        "stride": 4,
        "start_offset": 12,
        "start_index": 3,
        "index_step": 1,
        "index_scale": 4,
    }

def test_exact_counter_value_recovers_widened_affine_equality_selector():
    summarizer = StructuralRecurrenceSummarizer(_FakeTracer("unused", _const(0)), debug=False)
    count_expr = Expression.parameter("param_2", index=1, data_type="uint", size=4)
    widened_minus_start = Expression.binary_op(
        "INT_SUB",
        Expression.unary_op("INT_ZEXT", count_expr),
        Expression.constant(3, size=8),
    )
    selector = Condition(
        Expression.binary_op(
            "INT_NOTEQUAL",
            Expression.binary_op(
                "INT_ADD",
                widened_minus_start,
                Expression.constant(-1, size=8),
            ),
            Expression.constant(0, size=8),
        ),
        negated=True,
    )

    exact = summarizer._exact_counter_value_from_conditions(
        [
            _cond("INT_SLESS", _const(0), count_expr),
            _cond("INT_SLESS", widened_minus_start, Expression.constant(8, size=8)),
            _cond("INT_SLESS", count_expr, _const(4), negated=True),
            selector,
        ],
        "param_2",
    )

    assert exact == 4
