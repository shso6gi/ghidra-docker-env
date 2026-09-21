from scripts.function_tracer_pcode.tests.unit._recurrence_fixtures import *
from scripts.function_tracer_pcode.tests.unit._publication import published

def test_return_region_summary_coverage_rejects_positive_guard_with_one_gap():
    summarizer = StructuralRecurrenceSummarizer(tracer=None, debug=False)
    n = _param()
    exact_nonpositive = ReturnInfo(
        address="0x1000",
        value=_const(1),
        conditions=[_cond("INT_SLESS", n, _const(1))],
    )

    coverage_key = summarizer._prove_summary_conditions_plus_exact_returns_cover_active_precondition(
        summary_conditions=[_cond("INT_SLESS", _const(1), n)],
        exact_returns=[exact_nonpositive],
    )

    assert coverage_key is None

def test_return_region_summary_coverage_rejects_duplicate_name_only_guard_canonicalization():
    summarizer = StructuralRecurrenceSummarizer(tracer=None, debug=False)
    indexed_n = Expression.parameter("n", index=1, data_type="int", size=4)
    name_only_n = Expression.parameter("n", index=-1, data_type="int", size=4)
    parameters = [
        {"name": "n", "index": 0, "size": 4, "data_type": "int", "is_signed": True},
        {"name": "n", "index": 1, "size": 4, "data_type": "int", "is_signed": True},
    ]
    exact_nonpositive = ReturnInfo(
        address="0x1000",
        value=_const(1),
        conditions=[_cond("INT_SLESS", indexed_n, _const(1))],
    )
    summary_conditions = [_cond("INT_SLESSEQUAL", _const(1), name_only_n)]

    normalized_summary = summarizer._canonicalize_condition_parameters_for_analysis(
        summary_conditions,
        parameters,
    )
    coverage_key = summarizer._prove_summary_conditions_plus_exact_returns_cover_active_precondition(
        summary_conditions=summary_conditions,
        exact_returns=[exact_nonpositive],
        parameters=parameters,
    )

    assert normalized_summary[0].expression.operands[1].value == -1
    assert coverage_key is None

def test_counter_guard_signedness_ignores_name_only_parameter_alias():
    summarizer = StructuralRecurrenceSummarizer(PcodeTracer.__new__(PcodeTracer), debug=False)
    name_only_param = {"name": "count", "size": 4, "data_type": "int"}
    return_counter = Expression.parameter("count", index=-1, data_type="int", size=4)
    analysis = type(
        "Analysis",
        (),
        {
            "returns": [
                ReturnInfo(
                    address="00100000",
                    value=_const(1),
                    conditions=[_cond("INT_SLESS", _const(0), return_counter)],
                )
            ]
        },
    )()

    assert summarizer._vectorized_affine_counter_guard_signedness(analysis, name_only_param) is None

def test_counted_loop_summary_canonicalizes_zero_contribution_prefix():
    summarizer = StructuralRecurrenceSummarizer(PcodeTracer.__new__(PcodeTracer), debug=False)
    residue_cases = (
        ResidueLoopCase(modulus=2, residue=0, affine=(1, 0)),
        ResidueLoopCase(modulus=2, residue=1, affine=(-1, 0)),
    )
    value = summarizer._build_counted_loop_summary_intrinsic(
        base_expr=_const(0),
        start_expr=_const(1),
        limit_expr=_param(),
        induction_step=1,
        residue_cases=residue_cases,
        result_size=4,
        signed_loop=True,
    )

    assert value is not None
    assert isinstance(value.runtime_ref.loop_summary, LoopSummaryRef)
    assert loop_summary_method_b_key(value.runtime_ref.loop_summary) is not None
    assert value.runtime_ref.semantic_key() is not None

    canonical = summarizer._canonicalize_zero_prefix_counted_loop_value(
        value,
        base_expr=_const(0),
        limit_expr=_param(),
        induction_step=1,
        residue_cases=residue_cases,
        result_size=4,
        signed_loop=True,
    )

    assert canonical is not None
    assert canonical.expr_type == ExpressionType.INTRINSIC
    assert canonical.operands[1].equals(_const(0))

def test_counted_loop_summary_keeps_nonzero_prefix_start():
    summarizer = StructuralRecurrenceSummarizer(PcodeTracer.__new__(PcodeTracer), debug=False)
    residue_cases = (ResidueLoopCase(modulus=1, residue=0, affine=(1, 1)),)
    value = summarizer._build_counted_loop_summary_intrinsic(
        base_expr=_const(0),
        start_expr=_const(1),
        limit_expr=_param(),
        induction_step=1,
        residue_cases=residue_cases,
        result_size=4,
        signed_loop=True,
    )

    canonical = summarizer._canonicalize_zero_prefix_counted_loop_value(
        value,
        base_expr=_const(0),
        limit_expr=_param(),
        induction_step=1,
        residue_cases=residue_cases,
        result_size=4,
        signed_loop=True,
    )

    assert canonical is value

def test_counted_loop_summary_intrinsic_preserves_effect_aware_profile():
    summarizer = StructuralRecurrenceSummarizer(PcodeTracer.__new__(PcodeTracer), debug=False)
    effect_profile = LoopSideEffectProfileRef(
        profile="effect_aware",
        memory_writes=True,
        effect_count=1,
        effect_descriptors=(
            LoopBodyEffectRef(
                kind="memory_write",
                location=CanonicalLocation(
                    base_ref=LocationBaseRef.parameter("out", index=0),
                    offset=0,
                    size=4,
                ),
                value_expr=_param("param_1"),
                guard_constraints=(_cond("INT_SLESS", _const(0), _param("param_1")),),
                order_key=7,
            ),
        ),
    )
    value = summarizer._build_counted_loop_summary_intrinsic(
        base_expr=_const(0),
        start_expr=_const(0),
        limit_expr=_param("param_1"),
        induction_step=1,
        residue_cases=(ResidueLoopCase(modulus=1, residue=0, affine=(1, 0)),),
        result_size=4,
        signed_loop=True,
        side_effect_profile=effect_profile,
        guard_constraints=[_cond("INT_SLESS", _const(0), _param("param_1"))],
    )

    assert value is not None
    loop_summary = value.runtime_ref.loop_summary
    assert loop_summary.side_effect_profile.profile == "effect_aware"
    assert loop_summary.side_effect_profile.memory_writes is True
    assert loop_summary.guard_constraints
    assert loop_summary.stable_key() is not None

def test_counted_loop_update_validation_query_uses_object_identity_aux_symbols():
    summarizer = StructuralRecurrenceSummarizer(PcodeTracer.__new__(PcodeTracer), debug=False)
    loop_iv = Expression.parameter("__loop_iv", index=-10000, size=4)
    loop_acc = Expression.variable("__loop_acc", size=4)
    condition = _cond("INT_EQUAL", Expression.binary_op("INT_AND", loop_iv, _const(1)), _const(0))
    query = summarizer._build_expression_equivalence_query(
        Expression.binary_op("INT_ADD", loop_acc, loop_iv),
        Expression.binary_op("INT_ADD", loop_acc, loop_iv),
        [condition],
        [{"name": "param_1", "index": 0, "size": 4, "data_type": "int"}],
    )

    assert query is not None
    assert "(declare-const aux_sym_0 (_ BitVec 32))" in query
    assert "(declare-const aux_sym_1 (_ BitVec 32))" in query
    assert "aux_sym_0" in query
    assert "aux_sym_1" in query
    assert " __loop_iv)" not in query
    assert " __loop_acc)" not in query

def test_counted_loop_accumulator_extraction_assigns_distinct_binder_ordinals():
    header = _FakeCfgBlock(1)
    body = _FakeCfgBlock(2)
    header.add_edge(body)
    body.add_edge(header)

    zero_vn = _FakeVarnode("zero", expr=_const(0))
    one_vn = _FakeVarnode("one", expr=_const(1))
    iv_phi_vn = _FakeVarnode("iv_phi")
    iv_next_vn = _FakeVarnode("iv_next")
    iv_next_op = _FakePcodeOp("INT_ADD", [iv_phi_vn, one_vn], iv_next_vn)
    iv_phi_op = _FakePcodeOp("MULTIEQUAL", [zero_vn, iv_next_vn], iv_phi_vn)

    acc_a_phi_vn = _FakeVarnode("acc_a_phi")
    acc_a_next_vn = _FakeVarnode("acc_a_next")
    acc_a_next_op = _FakePcodeOp("INT_ADD", [acc_a_phi_vn, one_vn], acc_a_next_vn)
    acc_a_phi_op = _FakePcodeOp("MULTIEQUAL", [zero_vn, acc_a_next_vn], acc_a_phi_vn)

    acc_b_phi_vn = _FakeVarnode("acc_b_phi")
    acc_b_next_vn = _FakeVarnode("acc_b_next")
    acc_b_next_op = _FakePcodeOp("INT_ADD", [acc_b_phi_vn, one_vn], acc_b_next_vn)
    acc_b_phi_op = _FakePcodeOp("MULTIEQUAL", [zero_vn, acc_b_next_vn], acc_b_phi_vn)

    header._ops[:] = [iv_phi_op, acc_a_phi_op, acc_b_phi_op]
    body._ops[:] = [iv_next_op, acc_a_next_op, acc_b_next_op]
    for op in header._ops:
        op.setParent(header)
    for op in body._ops:
        op.setParent(body)

    induction = CountedLoopInduction(
        phi_op=iv_phi_op,
        phi_output=iv_phi_vn,
        init_expr=_const(0),
        backedge_index=1,
        step=1,
        placeholder=Expression.parameter("__loop_iv", index=-10_000, size=4),
        signed_guard=False,
        init_index=0,
        backedge_indices=(1,),
    )
    summarizer = StructuralRecurrenceSummarizer(_FakeTracer("unused", _const(0)), debug=False)

    accumulators = summarizer._match_counted_loop_accumulators(
        [iv_phi_op, acc_a_phi_op, acc_b_phi_op],
        induction,
        body,
    )

    ordinals = sorted(
        int(accumulator.placeholder.runtime_ref.binder_ordinal)
        for accumulator in accumulators
    )
    assert ordinals == [0, 1]
    ordinal_by_output = {
        accumulator.phi_output._name: int(accumulator.placeholder.runtime_ref.binder_ordinal)
        for accumulator in accumulators
    }
    reversed_accumulators = summarizer._match_counted_loop_accumulators(
        [iv_phi_op, acc_b_phi_op, acc_a_phi_op],
        induction,
        body,
    )
    reversed_ordinal_by_output = {
        accumulator.phi_output._name: int(accumulator.placeholder.runtime_ref.binder_ordinal)
        for accumulator in reversed_accumulators
    }
    assert reversed_ordinal_by_output == ordinal_by_output

    loop_summary = LoopSummaryRef(
        start_expr=_const(0),
        limit_expr=_param("param_1"),
        step_expr=_const(1),
        term_descriptor=LoopTermDescriptorRef(kind="affine_residue"),
        seed_terms=tuple(accumulator.placeholder for accumulator in accumulators),
        side_effect_profile=LoopSideEffectProfileRef(profile="pure"),
    )
    assert loop_summary_method_b_key(loop_summary) is not None

def test_counted_loop_induction_preserves_positive_non_unit_step_in_loop_summary():
    phi_output = _FakeVarnode("loop_iv")
    init_vn = _FakeVarnode("zero", expr=_const(0))
    two_vn = _FakeVarnode("two", expr=_const(2))
    next_vn = _FakeVarnode("loop_iv_next")
    _FakePcodeOp("INT_ADD", [phi_output, two_vn], next_vn)
    phi_op = _FakePcodeOp("MULTIEQUAL", [init_vn, next_vn], phi_output)
    summarizer = StructuralRecurrenceSummarizer(_FakeTracer("unused", _const(0)), debug=False)

    induction = summarizer._match_counted_loop_induction(phi_op)
    value = summarizer._build_counted_loop_summary_intrinsic(
        base_expr=_const(0),
        start_expr=_const(0),
        limit_expr=_param("param_1"),
        induction_step=2,
        residue_cases=(ResidueLoopCase(modulus=1, residue=0, affine=(1, 0)),),
        result_size=4,
        signed_loop=True,
    )

    assert induction is not None
    assert induction.step == 2
    assert value is not None
    assert value.runtime_ref.induction_step == 2
    assert value.runtime_ref.loop_summary.step_expr.value == 2

def test_counted_loop_induction_preserves_decrement_step_in_loop_summary():
    phi_output = _FakeVarnode("loop_iv")
    init_vn = _FakeVarnode("start", expr=_const(7))
    one_vn = _FakeVarnode("one", expr=_const(1))
    next_vn = _FakeVarnode("loop_iv_next")
    _FakePcodeOp("INT_SUB", [phi_output, one_vn], next_vn)
    phi_op = _FakePcodeOp("MULTIEQUAL", [init_vn, next_vn], phi_output)
    summarizer = StructuralRecurrenceSummarizer(_FakeTracer("unused", _const(0)), debug=False)

    induction = summarizer._match_counted_loop_induction(phi_op)
    value = summarizer._build_counted_loop_summary_intrinsic(
        base_expr=_const(0),
        start_expr=_const(7),
        limit_expr=_const(0),
        induction_step=-1,
        residue_cases=(ResidueLoopCase(modulus=1, residue=0, affine=(1, 0)),),
        result_size=4,
        signed_loop=True,
    )

    assert induction is not None
    assert induction.step == -1
    assert value is not None
    assert value.runtime_ref.induction_step == -1
    assert value.runtime_ref.loop_summary.step_expr.value == -1

def test_counted_loop_continue_guard_accepts_decrementing_counter():
    summarizer = StructuralRecurrenceSummarizer(_FakeTracer("unused", _const(0)), debug=False)
    counter = Expression.parameter("__loop_iv", index=-10000, size=4)
    raw_guard = Expression.binary_op("INT_SLESS", _const(0), counter)
    raw_guard.size = 1

    normalized = summarizer._normalize_loop_continue_guard(
        raw_guard,
        counter,
        body_on_true=True,
        step=-1,
    )

    assert normalized is not None
    condition_expr, entry_condition_expr, bound_expr, signed = normalized
    assert signed is True
    assert bound_expr.equals(_const(0))
    assert condition_expr.operator == "INT_SLESS"
    assert condition_expr.operands[0].equals(_const(0))
    assert condition_expr.operands[1].equals(counter)
    assert entry_condition_expr.operator == "INT_SLESS"
    assert entry_condition_expr.operands[0].equals(_const(0))
    assert entry_condition_expr.operands[1].equals(counter)

def test_structural_recurrence_summarizer_recovers_counted_scalar_loop_from_pcode_cfg():
    limit_expr = _param("param_1")
    zero_expr = _const(0)
    one_expr = _const(1)

    preheader = _FakeCfgBlock(0)
    header = _FakeCfgBlock(1)
    body = _FakeCfgBlock(2)
    even_block = _FakeCfgBlock(3)
    odd_block = _FakeCfgBlock(4)
    latch = _FakeCfgBlock(5)
    exit_block = _FakeCfgBlock(6)

    preheader.add_edge(header)
    header.add_edge(body, truth=True)
    header.add_edge(exit_block, truth=False)
    body.add_edge(odd_block, truth=True)
    body.add_edge(even_block, truth=False)
    even_block.add_edge(latch)
    odd_block.add_edge(latch)
    latch.add_edge(header)

    limit_vn = _FakeVarnode("limit", expr=limit_expr)
    zero_vn = _FakeVarnode("zero", expr=zero_expr)
    one_vn = _FakeVarnode("one", expr=one_expr)

    iv_phi_vn = _FakeVarnode("iv_phi")
    iv_next_vn = _FakeVarnode("iv_next")
    acc_phi_vn = _FakeVarnode("acc_phi")
    acc_merge_vn = _FakeVarnode("acc_merge")
    acc_even_vn = _FakeVarnode("acc_even")
    acc_odd_vn = _FakeVarnode("acc_odd")
    header_cond_vn = _FakeVarnode("header_cond", size=1)
    parity_and_vn = _FakeVarnode("parity_and")
    parity_cond_vn = _FakeVarnode("parity_cond", size=1)

    iv_phi_op = _FakePcodeOp("MULTIEQUAL", [zero_vn, iv_next_vn], iv_phi_vn)
    acc_phi_op = _FakePcodeOp("MULTIEQUAL", [zero_vn, acc_merge_vn], acc_phi_vn)
    header_cmp_op = _FakePcodeOp("INT_SLESS", [iv_phi_vn, limit_vn], header_cond_vn)
    header_branch = _FakePcodeOp("CBRANCH", [_FakeVarnode("header_target"), header_cond_vn], None)
    header._ops[:] = [iv_phi_op, acc_phi_op, header_cmp_op, header_branch]
    for op in header._ops:
        op.setParent(header)

    parity_and_op = _FakePcodeOp("INT_AND", [iv_phi_vn, one_vn], parity_and_vn)
    parity_cmp_op = _FakePcodeOp("INT_NOTEQUAL", [parity_and_vn, zero_vn], parity_cond_vn)
    body_branch = _FakePcodeOp("CBRANCH", [_FakeVarnode("body_target"), parity_cond_vn], None)
    body._ops[:] = [parity_and_op, parity_cmp_op, body_branch]
    for op in body._ops:
        op.setParent(body)

    acc_even_op = _FakePcodeOp("INT_ADD", [acc_phi_vn, iv_phi_vn], acc_even_vn)
    even_block._ops[:] = [acc_even_op]
    acc_even_op.setParent(even_block)

    acc_odd_op = _FakePcodeOp("INT_SUB", [acc_phi_vn, iv_phi_vn], acc_odd_vn)
    odd_block._ops[:] = [acc_odd_op]
    acc_odd_op.setParent(odd_block)

    acc_merge_op = _FakePcodeOp("MULTIEQUAL", [acc_even_vn, acc_odd_vn], acc_merge_vn)
    iv_next_op = _FakePcodeOp("INT_ADD", [iv_phi_vn, one_vn], iv_next_vn)
    latch._ops[:] = [acc_merge_op, iv_next_op]
    for op in latch._ops:
        op.setParent(latch)

    analysis = create_mock_analysis(
        "branch_for_accumulate",
        return_type="int",
        parameters=[{"name": "param_1", "index": 0, "data_type": "int", "size": 4, "is_signed": True}],
        returns=[
            ReturnInfo(
                address="0x1000",
                value=_const(0),
                conditions=[_cond("INT_SLESS", _const(0), _param("param_1"), negated=True)],
            ),
            ReturnInfo(
                address="0x1004",
                value=Expression.binary_op("INT_ADD", Expression.unknown("phi_circular"), _const(0)),
                conditions=[_cond("INT_SLESS", _const(0), _param("param_1"))],
            ),
        ],
    )

    summarizer = StructuralRecurrenceSummarizer(_FakeTracer("unused", _const(0)), debug=False)
    summary = summarizer.try_summarize_function(
        _FakeFunction("branch_for_accumulate"),
        _FakeCfgHighFunction([preheader, header, body, even_block, odd_block, latch, exit_block]),
        analysis,
    )

    assert summary is not None
    summarized_returns, note = summary
    assert note == "counted_scalar_loop_summary"
    assert len(summarized_returns) == 2
    assert all(expression_has_unresolved_value(ret.value) is False for ret in summarized_returns)
    loop_case = next(ret for ret in summarized_returns if ret.conditions and ret.conditions[0].to_string() == "(0 < param_1)")
    assert loop_case.summary_candidate_source_key is not None
    assert loop_case.summary_transition_evidence_key is not None
    loop_smt = expression_to_smt(published(loop_case.value))
    assert "rtunk_" not in loop_smt
    assert "rt_counted_loop_sum_" not in loop_smt
    assert "(ite " in loop_smt
    loop_summary = loop_case.value.runtime_ref.loop_summary
    assert len(loop_summary.cases) == 2
    assert all(case.case_kind == "accumulator_delta" for case in loop_summary.cases)
    assert all(case.path_conditions for case in loop_summary.cases)
    assert all(case.body_effect.kind == "accumulator_update" for case in loop_summary.cases)
    assert all(case.term_expr is not None for case in loop_summary.cases)
    assert all(case.stable_key() is not None for case in loop_summary.cases)

def test_generated_loop_alias_substitution_requires_exact_name():
    summarizer = StructuralRecurrenceSummarizer(_FakeTracer("unused", _const(0)), debug=False)
    replacement = _param("param_1")
    placeholder = Expression.variable("__loop_state_1", size=4)
    same_kind_different_alias = Expression.variable("__loop_state_2", size=4)
    exact_alias = Expression.variable("__loop_state_1", size=4)

    unchanged = summarizer._substitute_generated_loop_variable_aliases(
        same_kind_different_alias,
        placeholder,
        replacement,
    )
    replaced = summarizer._substitute_generated_loop_variable_aliases(
        exact_alias,
        placeholder,
        replacement,
    )

    assert unchanged.structural_key() == same_kind_different_alias.structural_key()
    assert replaced.structural_key() == replacement.structural_key()

def test_pre_return_counted_loop_summary_requires_single_covered_return(monkeypatch):
    header = _FakeCfgBlock(0)
    ret_block = _FakeCfgBlock(1)
    header.add_edge(ret_block)
    iv_phi = _FakePcodeOp("MULTIEQUAL", [], _FakeVarnode("iv_phi"))
    acc_phi_vn = _FakeVarnode("acc_phi")
    acc_phi = _FakePcodeOp("MULTIEQUAL", [], acc_phi_vn)
    branch = _FakeBranchOp(_cond("INT_SLESS", _const(0), _param()).expression)
    header._ops[:] = [iv_phi, acc_phi, branch]
    for op in header._ops:
        op.setParent(header)
    return_op = _FakePcodeOp("RETURN", [_FakeVarnode("target"), acc_phi_vn], None)
    ret_block._ops[:] = [return_op]
    return_op.setParent(ret_block)

    summarizer = StructuralRecurrenceSummarizer(_FakeTracer("unused", _const(0)), debug=False)
    induction = CountedLoopInduction(
        phi_op=iv_phi,
        phi_output=iv_phi.getOutput(),
        init_expr=_const(0),
        backedge_index=0,
        step=1,
        placeholder=Expression.parameter("__loop_iv", index=-1, size=4),
        signed_guard=True,
    )
    accumulator = CountedLoopAccumulator(
        phi_op=acc_phi,
        phi_output=acc_phi_vn,
        init_expr=_const(0),
        backedge_index=0,
        placeholder=Expression.variable("__loop_acc", size=4),
        member_outputs=(acc_phi_vn,),
    )
    guard = CountedLoopGuard(
        condition_expr=Expression.binary_op("INT_SLESS", induction.placeholder, _param()),
        bound_expr=_param(),
        continue_on_true=True,
        body_block=header,
        exit_block=ret_block,
        signed_comparison=True,
    )
    monkeypatch.setattr(
        summarizer,
        "_extract_counted_scalar_loop_model",
        lambda *_args, **_kwargs: (
            induction,
            accumulator,
            guard,
            (ResidueLoopCase(modulus=1, residue=0, affine=(1, 0)),),
        ),
    )
    monkeypatch.setattr(summarizer, "_count_counted_scalar_loop_models", lambda *_args, **_kwargs: 1)
    monkeypatch.setattr(summarizer, "_derive_direct_counted_loop_conditions", lambda *_args, **_kwargs: None)
    analysis = create_mock_analysis(
        "branch_for_accumulate",
        return_type="int",
        parameters=[{"name": "param_1", "index": 0, "data_type": "int", "size": 4}],
        returns=[ReturnInfo(address="0x1000", value=Expression.unknown("pre_return"), conditions=[])],
    )

    summary = summarizer.try_summarize_pre_return_counted_scalar_loop(
        _FakeFunction("branch_for_accumulate"),
        _FakeCfgHighFunction([header, ret_block]),
        analysis,
        [return_op],
    )

    assert summary is not None
    monkeypatch.setattr(summarizer, "_count_counted_scalar_loop_models", lambda *_args, **_kwargs: 2)
    assert summarizer.try_summarize_pre_return_counted_scalar_loop(
        _FakeFunction("branch_for_accumulate"),
        _FakeCfgHighFunction([header, ret_block]),
        analysis,
        [return_op],
    ) is None

    monkeypatch.setattr(summarizer, "_count_counted_scalar_loop_models", lambda *_args, **_kwargs: 1)
    extra_ret_block = _FakeCfgBlock(2)
    assert summarizer.try_summarize_pre_return_counted_scalar_loop(
        _FakeFunction("branch_for_accumulate"),
        _FakeCfgHighFunction([header, ret_block, extra_ret_block]),
        analysis,
        [return_op],
    ) is None

def test_counted_loop_model_count_includes_latch_guard_without_header_cbranch(monkeypatch):
    summarizer = StructuralRecurrenceSummarizer(_FakeTracer("unused", _const(0)), debug=False)
    iv_phi_vn = _FakeVarnode("iv_phi")
    acc_phi_vn = _FakeVarnode("acc_phi")
    iv_phi = _FakePcodeOp("MULTIEQUAL", [_FakeVarnode("iv_init"), _FakeVarnode("iv_next")], iv_phi_vn)
    acc_phi = _FakePcodeOp("MULTIEQUAL", [_FakeVarnode("acc_init"), _FakeVarnode("acc_next")], acc_phi_vn)
    header = _FakeCfgBlock(1, ops=[iv_phi, acc_phi])
    induction = CountedLoopInduction(
        phi_op=iv_phi,
        phi_output=iv_phi_vn,
        init_expr=_const(0),
        backedge_index=1,
        step=1,
        placeholder=Expression.parameter("__loop_iv", index=-1, size=4),
        signed_guard=True,
    )
    accumulator = CountedLoopAccumulator(
        phi_op=acc_phi,
        phi_output=acc_phi_vn,
        init_expr=_const(0),
        backedge_index=1,
        placeholder=Expression.variable("__loop_acc", size=4),
    )
    guard = CountedLoopGuard(
        condition_expr=Expression.binary_op("INT_SLESS", induction.placeholder, _param()),
        bound_expr=_param(),
        continue_on_true=True,
        body_block=header,
        exit_block=_FakeCfgBlock(2),
        signed_comparison=True,
        latch_block=_FakeCfgBlock(3),
    )

    monkeypatch.setattr(summarizer, "_find_cbranch_op", lambda block: None)
    monkeypatch.setattr(summarizer, "_match_counted_loop_induction", lambda phi_op: induction if phi_op is iv_phi else None)

    def fake_guards(candidate_header, cbranch, candidate_induction):
        assert candidate_header is header
        assert cbranch is None
        assert candidate_induction is induction
        return [guard]

    monkeypatch.setattr(summarizer, "_candidate_counted_loop_guards", fake_guards)
    monkeypatch.setattr(summarizer, "_match_counted_loop_accumulators", lambda *_args, **_kwargs: [accumulator])

    analysis = create_mock_analysis(
        "branch_for_accumulate",
        return_type="int",
        parameters=[{"name": "param_1", "index": 0, "data_type": "int", "size": 4}],
        returns=[],
    )

    assert summarizer._count_counted_scalar_loop_models(_FakeCfgHighFunction([header]), analysis) == 1

def test_structural_recurrence_summarizer_recovers_multi_backedge_counted_loop_cfg():
    limit_expr = _param("param_1")
    zero_expr = _const(0)
    one_expr = _const(1)

    entry = _FakeCfgBlock(0)
    ret_zero = _FakeCfgBlock(1)
    preheader = _FakeCfgBlock(2)
    header = _FakeCfgBlock(3)
    even_block = _FakeCfgBlock(4)
    even_exit = _FakeCfgBlock(5)
    odd_block = _FakeCfgBlock(6)
    odd_exit = _FakeCfgBlock(7)

    entry.add_edge(ret_zero, truth=True)
    entry.add_edge(preheader, truth=False)
    odd_block.add_edge(header, truth=True)
    odd_block.add_edge(odd_exit, truth=False)
    preheader.add_edge(header)
    even_block.add_edge(even_exit, truth=True)
    even_block.add_edge(header, truth=False)
    header.add_edge(even_block, truth=True)
    header.add_edge(odd_block, truth=False)

    limit_vn = _FakeVarnode("limit", expr=limit_expr)
    zero_vn = _FakeVarnode("zero", expr=zero_expr)
    one_vn = _FakeVarnode("one", expr=one_expr)

    signed_limit_vn = _FakeVarnode("signed_limit")
    entry_cond_vn = _FakeVarnode("entry_cond", size=1)
    iv_phi_vn = _FakeVarnode("iv_phi")
    acc_phi_vn = _FakeVarnode("acc_phi")
    parity_vn = _FakeVarnode("parity")
    parity_cond_vn = _FakeVarnode("parity_cond", size=1)
    even_acc_vn = _FakeVarnode("even_acc")
    even_next_vn = _FakeVarnode("even_next")
    even_exit_cond_vn = _FakeVarnode("even_exit_cond", size=1)
    odd_acc_vn = _FakeVarnode("odd_acc")
    odd_next_vn = _FakeVarnode("odd_next")
    odd_continue_cond_vn = _FakeVarnode("odd_continue_cond", size=1)

    entry_cast_op = _FakePcodeOp("CAST", [limit_vn], signed_limit_vn)
    entry_cmp_op = _FakePcodeOp("INT_SLESS", [signed_limit_vn, one_vn], entry_cond_vn)
    entry_branch = _FakePcodeOp("CBRANCH", [_FakeVarnode("entry_target"), entry_cond_vn], None)
    entry._ops[:] = [entry_cast_op, entry_cmp_op, entry_branch]
    for op in entry._ops:
        op.setParent(entry)

    iv_phi_op = _FakePcodeOp("MULTIEQUAL", [odd_next_vn, zero_vn, even_next_vn], iv_phi_vn)
    acc_phi_op = _FakePcodeOp("MULTIEQUAL", [odd_acc_vn, zero_vn, even_acc_vn], acc_phi_vn)
    parity_and_op = _FakePcodeOp("INT_AND", [iv_phi_vn, one_vn], parity_vn)
    parity_cmp_op = _FakePcodeOp("INT_EQUAL", [parity_vn, zero_vn], parity_cond_vn)
    parity_branch = _FakePcodeOp("CBRANCH", [_FakeVarnode("parity_target"), parity_cond_vn], None)
    header._ops[:] = [iv_phi_op, acc_phi_op, parity_and_op, parity_cmp_op, parity_branch]
    for op in header._ops:
        op.setParent(header)

    even_acc_op = _FakePcodeOp("INT_ADD", [acc_phi_vn, iv_phi_vn], even_acc_vn)
    even_next_op = _FakePcodeOp("INT_ADD", [iv_phi_vn, one_vn], even_next_vn)
    even_cmp_op = _FakePcodeOp("INT_EQUAL", [limit_vn, even_next_vn], even_exit_cond_vn)
    even_branch = _FakePcodeOp("CBRANCH", [_FakeVarnode("even_target"), even_exit_cond_vn], None)
    even_block._ops[:] = [even_acc_op, even_next_op, even_cmp_op, even_branch]
    for op in even_block._ops:
        op.setParent(even_block)

    odd_acc_op = _FakePcodeOp("INT_SUB", [acc_phi_vn, iv_phi_vn], odd_acc_vn)
    odd_next_op = _FakePcodeOp("INT_ADD", [iv_phi_vn, one_vn], odd_next_vn)
    odd_cmp_op = _FakePcodeOp("INT_NOTEQUAL", [limit_vn, odd_next_vn], odd_continue_cond_vn)
    odd_branch = _FakePcodeOp("CBRANCH", [_FakeVarnode("odd_target"), odd_continue_cond_vn], None)
    odd_block._ops[:] = [odd_acc_op, odd_next_op, odd_cmp_op, odd_branch]
    for op in odd_block._ops:
        op.setParent(odd_block)

    summarizer = StructuralRecurrenceSummarizer(_FakeTracer("unused", _const(0)), debug=False)
    analysis = create_mock_analysis(
        "branch_for_accumulate",
        return_type="int",
        parameters=[{"name": "param_1", "index": 0, "data_type": "int", "size": 4}],
        returns=[
            ReturnInfo(
                address="0x401000",
                value=Expression.unknown("phi_circular"),
                conditions=[],
            )
        ],
    )
    summary = summarizer.try_summarize_function(
        _FakeFunction("branch_for_accumulate"),
        _FakeCfgHighFunction([entry, ret_zero, preheader, header, even_block, even_exit, odd_block, odd_exit]),
        analysis,
    )

    assert summary is not None
    summarized_returns, note = summary
    assert note == "counted_scalar_loop_summary"
    assert len(summarized_returns) == 2
    assert all(expression_has_unresolved_value(ret.value) is False for ret in summarized_returns)
    loop_case = next(ret for ret in summarized_returns if ret.value.to_string() != "0")
    assert any("param_1" in condition.to_string() for condition in loop_case.conditions)
    loop_smt = expression_to_smt(published(loop_case.value))
    assert "rtunk_" not in loop_smt
    assert "rt_counted_loop_sum_" not in loop_smt
    assert "(ite " in loop_smt

def test_structural_recurrence_summarizer_accepts_reconstructed_guard_counter():
    param = _param(size=4)
    high_fragment = Expression.variable("in_a0_hi", size=4)
    reconstructed_param = Expression.binary_op(
        "INT_OR",
        Expression.binary_op("INT_LEFT", high_fragment, _const(32)),
        param,
    )
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
            ReturnInfo(
                address="0x1004",
                value=recursive_value,
                conditions=[_cond("INT_SLESS", reconstructed_param, _const(1), negated=True)],
            ),
            ReturnInfo(
                address="0x1000",
                value=_const(0),
                conditions=[_cond("INT_SLESS", reconstructed_param, _const(1))],
            ),
        ],
    )
    summarizer = StructuralRecurrenceSummarizer(
        _FakeTracer(
            "fc_recursive_sum",
            Expression.binary_op("INT_ADD", param, _const(0xFFFFFFFF)),
        ),
        debug=False,
    )

    summary = summarizer.try_summarize_function(
        _FakeFunction("fc_recursive_sum"),
        _FakeHighFunction([
            _FakeCallOp("fc_recursive_sum", Expression.binary_op("INT_ADD", param, _const(0xFFFFFFFF))),
        ]),
        analysis,
    )

    assert summary is not None
    summarized_returns, note = summary
    assert note == "linear_self_recursion_summary"
    assert all("call_out_of_scope" not in ret.value.to_string() for ret in summarized_returns)
    recursive_case = next(ret for ret in summarized_returns if ret.value.to_string() != "0")
    assert recursive_case.conditions[0].to_string() == "(0 < param_1)"

def test_counted_loop_summary_value_uses_intrinsic_for_negative_step_single_residue():
    summarizer = StructuralRecurrenceSummarizer(_FakeTracer("unused", _const(0)), debug=False)
    expr = summarizer._build_counted_loop_summary_value(
        base_expr=_const(0),
        start_expr=_const(16),
        limit_expr=_const(0),
        induction_step=-8,
        residue_cases=(ResidueLoopCase(modulus=1, residue=0, affine=(0, -4)),),
        result_size=4,
        signed_loop=True,
    )

    assert expr is not None
    assert expr.expr_type == ExpressionType.INTRINSIC
    assert expr.opcode == COUNTED_LOOP_SUM_OPCODE
    assert expression_has_unresolved_value(expr) is False
    assert "rt_counted_loop_sum_" not in expression_to_smt(published(expr))

def test_counted_loop_latch_guard_rejects_boolean_bound_expression():
    summarizer = StructuralRecurrenceSummarizer(_FakeTracer("unused", _const(0)), debug=False)
    counter = Expression.parameter("__loop_iv", index=-10000, size=4)
    bool_bound = Expression.binary_op(
        "INT_EQUAL",
        Expression.binary_op("INT_AND", _const(0), _const(1)),
        _const(0),
    )
    bool_bound.size = 1
    counter_next = Expression.binary_op("INT_ADD", counter, _const(1))
    counter_next.size = 4
    raw_guard = Expression.binary_op("INT_NOTEQUAL", bool_bound, counter_next)
    raw_guard.size = 1

    assert summarizer._normalize_latch_continue_guard(
        raw_guard,
        counter,
        continue_on_true=True,
        step=1,
    ) is None

def test_extract_counted_scalar_loop_model_evaluates_multiple_accumulator_candidates(monkeypatch):
    header = _FakeCfgBlock(1)
    phi_bad = _FakePcodeOp("MULTIEQUAL", [], _FakeVarnode("bad_acc", size=4))
    phi_good = _FakePcodeOp("MULTIEQUAL", [], _FakeVarnode("good_acc", size=4))
    phi_iv = _FakePcodeOp("MULTIEQUAL", [], _FakeVarnode("iv", size=4))
    branch = _FakeBranchOp(_cond("INT_SLESS", _const(0), _param()).expression)
    header._ops[:] = [phi_iv, phi_bad, phi_good, branch]
    for op in header._ops:
        op.setParent(header)

    summarizer = StructuralRecurrenceSummarizer(_FakeTracer("unused", _const(0)), debug=False)
    induction = CountedLoopInduction(
        phi_op=phi_iv,
        phi_output=phi_iv.getOutput(),
        init_expr=_const(0),
        backedge_index=1,
        step=1,
        placeholder=Expression.parameter("__loop_iv", index=-10000, size=4),
        signed_guard=False,
    )
    guard = CountedLoopGuard(
        condition_expr=Expression.binary_op("INT_SLESS", induction.placeholder, _param()),
        bound_expr=_param(),
        continue_on_true=True,
        body_block=header,
        exit_block=header,
        signed_comparison=True,
        entry_condition_expr=Expression.binary_op("INT_SLESS", induction.placeholder, _param()),
    )
    bad_acc = CountedLoopAccumulator(
        phi_op=phi_bad,
        phi_output=phi_bad.getOutput(),
        init_expr=_const(0),
        backedge_index=1,
        placeholder=Expression.variable("__loop_acc_bad", size=4),
        member_outputs=(phi_bad.getOutput(),),
        member_placeholders=(Expression.variable("__loop_acc_bad", size=4),),
    )
    good_acc = CountedLoopAccumulator(
        phi_op=phi_good,
        phi_output=phi_good.getOutput(),
        init_expr=_const(0),
        backedge_index=1,
        placeholder=Expression.variable("__loop_acc_good", size=4),
        member_outputs=(phi_good.getOutput(),),
        member_placeholders=(Expression.variable("__loop_acc_good", size=4),),
    )

    monkeypatch.setattr(summarizer, "_match_counted_loop_induction", lambda op: induction if op is phi_iv else None)
    monkeypatch.setattr(summarizer, "_candidate_counted_loop_guards", lambda *_args, **_kwargs: [guard])
    monkeypatch.setattr(summarizer, "_match_counted_loop_accumulators", lambda *_args, **_kwargs: [bad_acc, good_acc])

    def _fake_cases(accumulator, *_args, **_kwargs):
        if accumulator is bad_acc:
            return []
        return [
            CountedLoopUpdateCase(
                conditions=(),
                update_expr=Expression.binary_op("INT_ADD", accumulator.placeholder, induction.placeholder),
                delta_expr=induction.placeholder,
            )
        ]

    monkeypatch.setattr(summarizer, "_extract_counted_loop_update_cases", _fake_cases)
    monkeypatch.setattr(
        summarizer,
        "_extract_residue_loop_cases",
        lambda cases, _counter_name, **_kwargs: (
            ResidueLoopCase(modulus=1, residue=0, affine=(1, 0)),
        ) if cases else None,
    )
    model = summarizer._extract_counted_scalar_loop_model(
        _FakeCfgHighFunction([header]),
        analysis=None,
    )

    assert model is not None
    _, accumulator, _, residue_cases = model
    assert accumulator is good_acc
    assert residue_cases == (ResidueLoopCase(modulus=1, residue=0, affine=(1, 0)),)

def test_counted_loop_model_prefers_return_reaching_accumulator_over_larger_coeff(monkeypatch):
    header = _FakeCfgBlock(1)
    phi_bad = _FakePcodeOp("MULTIEQUAL", [], _FakeVarnode("bad_acc", size=4))
    phi_good = _FakePcodeOp("MULTIEQUAL", [], _FakeVarnode("good_acc", size=4))
    phi_iv = _FakePcodeOp("MULTIEQUAL", [], _FakeVarnode("iv", size=4))
    branch = _FakeBranchOp(_cond("INT_SLESS", _const(0), _param()).expression)
    header._ops[:] = [phi_iv, phi_bad, phi_good, branch]
    for op in header._ops:
        op.setParent(header)

    summarizer = StructuralRecurrenceSummarizer(_FakeTracer("unused", _const(0)), debug=False)
    induction = CountedLoopInduction(
        phi_op=phi_iv,
        phi_output=phi_iv.getOutput(),
        init_expr=_const(0),
        backedge_index=1,
        step=1,
        placeholder=Expression.parameter("__loop_iv", index=-10000, size=4),
        signed_guard=False,
    )
    guard = CountedLoopGuard(
        condition_expr=Expression.binary_op("INT_SLESS", induction.placeholder, _param()),
        bound_expr=_param(),
        continue_on_true=True,
        body_block=header,
        exit_block=header,
        signed_comparison=True,
        entry_condition_expr=Expression.binary_op("INT_SLESS", induction.placeholder, _param()),
    )
    bad_acc = CountedLoopAccumulator(
        phi_op=phi_bad,
        phi_output=phi_bad.getOutput(),
        init_expr=_const(0),
        backedge_index=1,
        placeholder=Expression.variable("__loop_acc_bad", size=4),
        member_outputs=(phi_bad.getOutput(),),
        member_placeholders=(Expression.variable("__loop_acc_bad", size=4),),
    )
    good_acc = CountedLoopAccumulator(
        phi_op=phi_good,
        phi_output=phi_good.getOutput(),
        init_expr=_const(0),
        backedge_index=1,
        placeholder=Expression.variable("__loop_acc_good", size=4),
        member_outputs=(phi_good.getOutput(),),
        member_placeholders=(Expression.variable("__loop_acc_good", size=4),),
    )

    monkeypatch.setattr(summarizer, "_match_counted_loop_induction", lambda op: induction if op is phi_iv else None)
    monkeypatch.setattr(summarizer, "_candidate_counted_loop_guards", lambda *_args, **_kwargs: [guard])
    monkeypatch.setattr(summarizer, "_match_counted_loop_accumulators", lambda *_args, **_kwargs: [bad_acc, good_acc])
    monkeypatch.setattr(
        summarizer,
        "_varnode_reaches_return",
        lambda varnode, **_kwargs: varnode is good_acc.phi_output,
    )

    def _fake_cases(accumulator, *_args, **_kwargs):
        coeff = 8 if accumulator is bad_acc else 1
        return [
            CountedLoopUpdateCase(
                conditions=(),
                update_expr=Expression.binary_op("INT_ADD", accumulator.placeholder, induction.placeholder),
                delta_expr=Expression.binary_op("INT_MULT", induction.placeholder, _const(coeff)),
            )
        ]

    monkeypatch.setattr(summarizer, "_extract_counted_loop_update_cases", _fake_cases)
    monkeypatch.setattr(
        summarizer,
        "_extract_residue_loop_cases",
        lambda cases, _counter_name, **_kwargs: (
            ResidueLoopCase(
                modulus=1,
                residue=0,
                affine=(int(cases[0].delta_expr.operands[1].value), 0),
            ),
        ) if cases else None,
    )

    model = summarizer._extract_counted_scalar_loop_model(
        _FakeCfgHighFunction([header]),
        analysis=None,
    )

    assert model is not None
    _, accumulator, _, residue_cases = model
    assert accumulator is good_acc
    assert residue_cases == (ResidueLoopCase(modulus=1, residue=0, affine=(1, 0)),)

def test_counted_scalar_loop_summary_keeps_function_memory_writes_as_context():
    analysis = create_mock_analysis(
        "counted_loop_effectful",
        return_type="int",
        parameters=[{"name": "param_1", "index": 0, "data_type": "int", "size": 4}],
        returns=[
            ReturnInfo(
                address="0x1000",
                value=_const(0),
                conditions=[_cond("INT_SLESS", _const(0), _param("param_1"), negated=True)],
            ),
            ReturnInfo(
                address="0x1004",
                value=Expression.unknown("phi_circular"),
                conditions=[_cond("INT_SLESS", _const(0), _param("param_1"))],
            ),
        ],
    )
    analysis.effect_summary = EffectSummary(
        parameter_names=["param_1"],
        effects=[
            StoreEffect(
                location=CanonicalLocation(
                    base_ref=LocationBaseRef.parameter("param_1", index=0),
                    offset=0,
                    size=4,
                ),
                value=_const(1),
                conditions=[],
                order_key=0,
            )
        ],
    )

    summarizer = StructuralRecurrenceSummarizer(_FakeTracer("unused", _const(0)), debug=False)
    profile = summarizer._build_loop_side_effect_profile(analysis=analysis)

    assert summarizer._analysis_is_safe_for_counted_scalar_summary(analysis) is True
    assert profile.profile == "pure"
    assert profile.memory_writes is False
    assert profile.context_memory_writes is True
    assert profile.calls is False
    assert profile.escapes is False
    assert profile.effect_descriptors == ()
    assert len(profile.context_descriptors) == 1
    assert profile.context_descriptors[0].kind == "memory_write"
    assert profile.context_descriptors[0].source == "function_effect_summary"
    assert profile.context_descriptors[0].scope == "function"

def test_counted_scalar_loop_summary_declines_unsupported_call_effect():
    analysis = create_mock_analysis(
        "counted_loop_call",
        return_type="int",
        parameters=[{"name": "param_1", "index": 0, "data_type": "int", "size": 4}],
        returns=[],
    )
    analysis.effect_summary = EffectSummary(
        parameter_names=["param_1"],
        effects=[],
        has_unsupported_call=True,
    )

    summarizer = StructuralRecurrenceSummarizer(_FakeTracer("unused", _const(0)), debug=False)

    assert summarizer._analysis_is_safe_for_counted_scalar_summary(analysis) is False

def test_loop_side_effect_profile_classifies_body_guards_calls_and_escapes():
    guard_expr = Expression.binary_op("INT_EQUAL", _param("param_1"), _const(0))
    body = _FakeCfgBlock(
        1,
        ops=[
            _FakePcodeOp("CBRANCH", [_FakeVarnode("target"), _FakeArgVarnode(guard_expr)], None),
            _FakePcodeOp("STORE", [], None),
            _FakePcodeOp("CALL", [_FakeVarnode("direct_target")], None),
            _FakePcodeOp("CALLIND", [_FakeVarnode("indirect_target")], None),
            _FakePcodeOp("BRANCHIND", [_FakeVarnode("escape_target")], None),
        ],
    )
    summarizer = StructuralRecurrenceSummarizer(_FakeTracer("callee", _const(0)), debug=False)

    profile = summarizer._build_loop_side_effect_profile(loop_blocks=[body])

    assert profile.profile == "effect_unknown"
    assert profile.memory_writes is True
    assert profile.calls is True
    assert profile.escapes is True
    assert profile.conditional_guards is True
    assert any(effect.kind == "conditional_guard" for effect in profile.effect_descriptors)
    assert any(effect.kind == "memory_write" for effect in profile.effect_descriptors)
    assert any(effect.kind == "call" for effect in profile.effect_descriptors)
    assert any(effect.kind == "escape" for effect in profile.effect_descriptors)
    assert any(
        effect.kind == "memory_write" and effect.keyable is False
        for effect in profile.effect_descriptors
    )
    assert all(
        effect.source == "pcode_scan" and effect.scope == "loop"
        for effect in profile.effect_descriptors
    )

def test_loop_effect_profile_keeps_function_and_loop_effect_origins_separate():
    analysis = create_mock_analysis(
        "loop_effect_origins",
        return_type="int",
        parameters=[{"name": "param_1", "index": 0, "data_type": "int *", "size": 8}],
        returns=[],
    )
    analysis.effect_summary = EffectSummary(
        parameter_names=["param_1"],
        effects=[
            StoreEffect(
                location=CanonicalLocation(
                    base_ref=LocationBaseRef.parameter("param_1", index=0),
                    offset=4,
                    size=4,
                ),
                value=_const(11),
                conditions=[],
                order_key=3,
            ),
        ],
    )
    body = _FakeCfgBlock(1, ops=[_FakePcodeOp("STORE", [], None)])
    summarizer = StructuralRecurrenceSummarizer(_FakeTracer("unused", _const(0)), debug=False)

    profile = summarizer._build_loop_side_effect_profile(analysis=analysis, loop_blocks=[body])

    loop_sources = [(effect.source, effect.scope) for effect in profile.effect_descriptors]
    context_sources = [(effect.source, effect.scope) for effect in profile.context_descriptors]
    assert ("function_effect_summary", "function") in context_sources
    assert ("pcode_scan", "loop") in loop_sources

def test_loop_body_block_collection_includes_header_and_latch_effects():
    summarizer = StructuralRecurrenceSummarizer(_FakeTracer("unused", _const(0)), debug=False)
    guard_expr = Expression.binary_op("INT_SLESS", _param("param_1"), _const(8))
    header_branch = _FakePcodeOp("CBRANCH", [_FakeVarnode("header_target"), _FakeArgVarnode(guard_expr)], None)
    header = _FakeCfgBlock(0, ops=[header_branch, _FakePcodeOp("STORE", [], None)])
    body = _FakeCfgBlock(1)
    latch = _FakeCfgBlock(2, ops=[_FakePcodeOp("STORE", [], None)])
    exit_block = _FakeCfgBlock(3)
    header.add_edge(body, truth=True)
    header.add_edge(exit_block, truth=False)
    body.add_edge(latch)
    latch.add_edge(header)
    guard = CountedLoopGuard(
        condition_expr=guard_expr,
        bound_expr=_const(8),
        continue_on_true=True,
        body_block=body,
        exit_block=exit_block,
        signed_comparison=True,
        latch_block=latch,
    )

    loop_blocks = summarizer._collect_loop_body_blocks(header_block=header, guard=guard)
    profile = summarizer._build_loop_side_effect_profile(
        loop_blocks=loop_blocks,
        ignored_branch_ops=[header_branch],
    )

    assert {block.getIndex() for block in loop_blocks} == {0, 1, 2}
    assert profile.memory_writes is True
    assert profile.conditional_guards is False
    assert sum(1 for effect in profile.effect_descriptors if effect.kind == "memory_write") == 2

def test_loop_body_block_collection_uses_natural_loop_boundary():
    summarizer = StructuralRecurrenceSummarizer(_FakeTracer("unused", _const(0)), debug=False)
    guard_expr = Expression.binary_op("INT_SLESS", _param("param_1"), _const(8))
    header = _FakeCfgBlock(0)
    body = _FakeCfgBlock(1)
    latch = _FakeCfgBlock(2)
    cleanup = _FakeCfgBlock(3, ops=[_FakePcodeOp("STORE", [], None)])
    exit_block = _FakeCfgBlock(4)
    header.add_edge(body, truth=True)
    header.add_edge(exit_block, truth=False)
    body.add_edge(latch)
    body.add_edge(cleanup)
    latch.add_edge(header)
    cleanup.add_edge(exit_block)
    guard = CountedLoopGuard(
        condition_expr=guard_expr,
        bound_expr=_const(8),
        continue_on_true=True,
        body_block=body,
        exit_block=exit_block,
        signed_comparison=True,
        latch_block=latch,
    )

    loop_blocks = summarizer._collect_loop_body_blocks(header_block=header, guard=guard)

    assert {block.getIndex() for block in loop_blocks} == {0, 1, 2}

def test_loop_store_effect_carries_block_control_guard():
    summarizer = StructuralRecurrenceSummarizer(_FakeTracer("unused", _const(0)), debug=False)
    guard_expr = Expression.binary_op("INT_EQUAL", Expression.binary_op("INT_AND", _param("param_1"), _const(1)), _const(0))
    header = _FakeCfgBlock(0)
    body_branch = _FakePcodeOp("CBRANCH", [_FakeVarnode("body_target"), _FakeArgVarnode(guard_expr)], None)
    body = _FakeCfgBlock(1, ops=[body_branch])
    store_block = _FakeCfgBlock(
        2,
        ops=[
            _FakePcodeOp(
                "STORE",
                [
                    _FakeVarnode("ram"),
                    _FakeArgVarnode(Expression.parameter("out", index=0, data_type="int *", size=8)),
                    _FakeArgVarnode(_param("param_1")),
                ],
                None,
            )
        ],
    )
    latch = _FakeCfgBlock(3)
    exit_block = _FakeCfgBlock(4)
    header.add_edge(body, truth=True)
    header.add_edge(exit_block, truth=False)
    body.add_edge(store_block, truth=True)
    body.add_edge(latch, truth=False)
    store_block.add_edge(latch)
    latch.add_edge(header)
    guard = CountedLoopGuard(
        condition_expr=Expression.binary_op("INT_SLESS", _param("param_1"), _const(8)),
        bound_expr=_const(8),
        continue_on_true=True,
        body_block=body,
        exit_block=exit_block,
        signed_comparison=True,
        latch_block=latch,
    )
    loop_blocks = summarizer._collect_loop_body_blocks(header_block=header, guard=guard)
    block_guard_info = summarizer._loop_block_guard_effect_info(
        header_block=header,
        guard=guard,
        loop_blocks=loop_blocks,
    )

    profile = summarizer._build_loop_side_effect_profile(
        loop_blocks=loop_blocks,
        ignored_branch_ops=[],
        block_guard_info=block_guard_info,
    )

    store_effect = next(effect for effect in profile.effect_descriptors if effect.kind == "memory_write")
    assert len(store_effect.guard_constraints) == 1
    assert store_effect.guard_constraints[0].expression.equals(guard_expr)
    assert len(store_effect.path_condition_sets) == 1
    assert len(store_effect.path_condition_sets[0]) == 1
    assert store_effect.path_condition_sets[0][0].expression.equals(guard_expr)
    assert store_effect.guard_paths_incomplete is False

def test_store_effect_with_incomplete_guard_paths_is_unkeyable():
    summarizer = StructuralRecurrenceSummarizer(_FakeTracer("unused", _const(0)), debug=False)
    store_op = _FakePcodeOp(
        "STORE",
        [
            _FakeVarnode("ram"),
            _FakeArgVarnode(Expression.parameter("out", index=0, data_type="int *", size=8)),
            _FakeArgVarnode(_param("param_1")),
        ],
        None,
    )

    effect = summarizer._store_effect_ref_for_op(
        store_op,
        scope="loop",
        guard_paths_incomplete=True,
    )

    assert effect.keyable is False
    assert effect.guard_paths_incomplete is True
    assert "store_guard_paths_incomplete" in effect.unkeyable_reason
    assert effect.stable_key() is None

def test_counted_scalar_loop_summary_rejects_unresolved_operands():
    summarizer = StructuralRecurrenceSummarizer(_FakeTracer("unused", _const(0)), debug=False)
    summary_value = summarizer._build_counted_loop_summary_value(
        base_expr=_const(0),
        start_expr=Expression.unknown("phi_circular"),
        limit_expr=_param("param_1"),
        induction_step=1,
        residue_cases=(
            ResidueLoopCase(modulus=2, residue=0, affine=(1, 0)),
            ResidueLoopCase(modulus=2, residue=1, affine=(-1, 0)),
        ),
        result_size=4,
        signed_loop=True,
    )

    assert summary_value is None

def test_canonicalize_peeled_counted_loop_value_rewrites_proven_phi_start(monkeypatch):
    summarizer = StructuralRecurrenceSummarizer(_FakeTracer("unused", _const(0)), debug=False)
    start_expr = Expression.phi(
        [
            (None, _const(0)),
            (
                _cond("INT_NOTEQUAL", Expression.binary_op("INT_AND", _param(), _const(0xFFFFFFF8)), _param()),
                Expression.binary_op("INT_AND", _param(), _const(0xFFFFFFF8)),
            ),
        ]
    )
    original = Expression.intrinsic(
        "COUNTED_LOOP_SUM",
        [_const(0), start_expr, _param()],
        size=4,
        runtime_ref=CountedLoopSummaryRef(
            induction_step=1,
            result_size=4,
            signed_loop=True,
            residue_cases=((2, 0, 1, 0), (2, 1, -1, 0)),
        ),
        opcode=COUNTED_LOOP_SUM_OPCODE,
    )
    monkeypatch.setattr(
        summarizer,
        "_prove_expression_equivalence_under_conditions",
        lambda *_args, **_kwargs: True,
    )

    rewritten = summarizer._canonicalize_peeled_counted_loop_value(
        original,
        continue_conditions=[_cond("INT_SLESS", _const(0), _param())],
        parameters=[{"name": "param_1", "index": 0, "size": 4, "data_type": "int"}],
        base_expr=_const(0),
        limit_expr=_param(),
        induction_step=1,
        residue_cases=(
            ResidueLoopCase(modulus=2, residue=0, affine=(1, 0)),
            ResidueLoopCase(modulus=2, residue=1, affine=(-1, 0)),
        ),
        result_size=4,
        signed_loop=True,
    )

    assert rewritten is not None
    assert rewritten.expr_type == ExpressionType.INTRINSIC
    assert rewritten.operands[1].expr_type == ExpressionType.CONSTANT
    assert rewritten.operands[1].value == 0

def test_canonicalize_peeled_counted_loop_value_keeps_original_when_unproved(monkeypatch):
    summarizer = StructuralRecurrenceSummarizer(_FakeTracer("unused", _const(0)), debug=False)
    start_expr = Expression.phi(
        [
            (None, _const(0)),
            (_cond("INT_SLESS", _const(0), _param()), Expression.binary_op("INT_AND", _param(), _const(0xFFFFFFF8))),
        ]
    )
    original = Expression.intrinsic(
        "COUNTED_LOOP_SUM",
        [_const(0), start_expr, _param()],
        size=4,
        runtime_ref=CountedLoopSummaryRef(
            induction_step=1,
            result_size=4,
            signed_loop=True,
            residue_cases=((2, 0, 1, 0), (2, 1, -1, 0)),
        ),
        opcode=COUNTED_LOOP_SUM_OPCODE,
    )
    monkeypatch.setattr(
        summarizer,
        "_prove_expression_equivalence_under_conditions",
        lambda *_args, **_kwargs: False,
    )

    rewritten = summarizer._canonicalize_peeled_counted_loop_value(
        original,
        continue_conditions=[_cond("INT_SLESS", _const(0), _param())],
        parameters=[{"name": "param_1", "index": 0, "size": 4, "data_type": "int"}],
        base_expr=_const(0),
        limit_expr=_param(),
        induction_step=1,
        residue_cases=(
            ResidueLoopCase(modulus=2, residue=0, affine=(1, 0)),
            ResidueLoopCase(modulus=2, residue=1, affine=(-1, 0)),
        ),
        result_size=4,
        signed_loop=True,
    )

    assert rewritten is original

def test_counted_scalar_loop_summary_recovers_when_analysis_erases_loop_effect(monkeypatch):
    analysis = create_mock_analysis(
        "branch_for_accumulate",
        return_type="int",
        parameters=[{"name": "param_1", "index": 0, "data_type": "int", "size": 4}],
        returns=[
            ReturnInfo(
                address="0x1000",
                value=_const(0),
                conditions=[],
            ),
            ReturnInfo(
                address="0x1004",
                value=_const(0),
                conditions=[_cond("INT_SLESS", _const(0), _param("param_1"))],
            ),
        ],
    )
    analysis.effect_summary = EffectSummary(parameter_names=["param_1"], effects=[])

    summarizer = StructuralRecurrenceSummarizer(_FakeTracer("unused", _const(0)), debug=False)
    induction = CountedLoopInduction(
        phi_op=_FakePcodeOp("MULTIEQUAL", [], _FakeVarnode("iv_phi")),
        phi_output=_FakeVarnode("iv_phi"),
        init_expr=_const(0),
        backedge_index=0,
        step=1,
        placeholder=Expression.parameter("__loop_iv", index=-1, size=4),
        signed_guard=True,
        init_index=1,
        backedge_indices=(0,),
    )
    accumulator = CountedLoopAccumulator(
        phi_op=_FakePcodeOp("MULTIEQUAL", [], _FakeVarnode("acc_phi")),
        phi_output=_FakeVarnode("acc_phi"),
        init_expr=_const(0),
        backedge_index=0,
        placeholder=Expression.variable("__loop_acc", size=4),
        init_index=1,
        backedge_indices=(0,),
    )
    guard = CountedLoopGuard(
        condition_expr=Expression.binary_op("INT_SLESS", induction.placeholder, _param("param_1")),
        bound_expr=_param("param_1"),
        continue_on_true=True,
        body_block=object(),
        exit_block=object(),
        signed_comparison=True,
    )

    monkeypatch.setattr(
        summarizer,
        "_extract_counted_scalar_loop_model",
        lambda *_args, **_kwargs: (
            induction,
            accumulator,
            guard,
            (
                ResidueLoopCase(modulus=2, residue=0, affine=(1, 0)),
                ResidueLoopCase(modulus=2, residue=1, affine=(-1, 0)),
            ),
        ),
    )
    monkeypatch.setattr(
        summarizer,
        "_derive_direct_counted_loop_conditions",
        lambda *_args, **_kwargs: (
            [_cond("INT_SLESS", _const(0), _param("param_1"), negated=True)],
            [_cond("INT_SLESS", _const(0), _param("param_1"))],
        ),
    )

    summary = summarizer._build_counted_scalar_loop_summary(
        _FakeFunction("branch_for_accumulate"),
        _FakeCfgHighFunction([]),
        analysis,
    )

    assert summary is not None
    summarized_returns, note = summary
    assert note == "counted_scalar_loop_summary"
    assert any(ret.value.expr_type == ExpressionType.INTRINSIC for ret in summarized_returns)
    base_case = next(ret for ret in summarized_returns if ret.value.expr_type != ExpressionType.INTRINSIC)
    loop_case = next(ret for ret in summarized_returns if ret.value.expr_type == ExpressionType.INTRINSIC)
    assert ConditionSimplifier.get_simplified_condition_string(base_case.conditions[0]) == "(param_1 <= 0)"
    assert ConditionSimplifier.get_simplified_condition_string(loop_case.conditions[0]) == "(0 < param_1)"

def test_structural_recurrence_summarizer_recovers_branch_accumulator_loop_summary():
    params = [
        {"name": "trace", "index": 0, "data_type": "int *", "size": 8},
        {"name": "start", "index": 1, "data_type": "int", "size": 4, "is_signed": True},
        {"name": "limit", "index": 2, "data_type": "int", "size": 4, "is_signed": True},
    ]
    base_expr = Expression.binary_op("INT_ADD", _mem("trace", 0), _mem("trace", 4))
    null_case = ReturnInfo(
        address="0x1000",
        value=Expression.constant(-100, size=4),
        conditions=[_cond("INT_EQUAL", Expression.parameter("trace", 0, size=8), Expression.constant(0, size=8))],
    )
    base_case = ReturnInfo(
        address="0x1004",
        value=base_expr,
        conditions=[
            _cond("INT_NOTEQUAL", Expression.parameter("trace", 0, size=8), Expression.constant(0, size=8)),
            _cond("INT_SLESS", _param("start"), _param("limit"), negated=True),
        ],
    )
    even_step = ReturnInfo(
        address="0x1008",
        value=Expression.binary_op("INT_ADD", base_expr, Expression.binary_op("INT_ADD", _param("start"), _const(1))),
        conditions=[
            _cond("INT_NOTEQUAL", Expression.parameter("trace", 0, size=8), Expression.constant(0, size=8)),
            _cond("INT_SLESS", _param("start"), _param("limit")),
            _cond("INT_EQUAL", Expression.binary_op("INT_AND", _param("start"), _const(1)), _const(0)),
            _cond("INT_EQUAL", _param("limit"), Expression.binary_op("INT_ADD", _param("start"), _const(1))),
        ],
    )
    odd_step = ReturnInfo(
        address="0x100c",
        value=Expression.binary_op("INT_ADD", base_expr, Expression.binary_op("INT_ADD", Expression.unary_op("INT_2COMP", _param("start")), _const(1))),
        conditions=[
            _cond("INT_NOTEQUAL", Expression.parameter("trace", 0, size=8), Expression.constant(0, size=8)),
            _cond("INT_SLESS", _param("start"), _param("limit")),
            _cond("INT_EQUAL", Expression.binary_op("INT_AND", _param("start"), _const(1)), _const(0), negated=True),
            _cond("INT_EQUAL", _param("limit"), Expression.binary_op("INT_ADD", _param("start"), _const(1))),
        ],
    )
    analysis = create_mock_analysis(
        "lr_loop_with_side_effect",
        return_type="int",
        parameters=params,
        returns=[null_case, base_case, even_step, odd_step],
    )
    analysis.effect_summary = EffectSummary(parameter_names=["trace", "start", "limit"], effects=[])

    summarizer = StructuralRecurrenceSummarizer(_FakeTracer("unused", _const(0)), debug=False)
    summary = summarizer.try_summarize_function(
        _FakeFunction("lr_loop_with_side_effect"),
        _FakeHighFunction([]),
        analysis,
    )

    assert summary is not None
    summarized_returns, note = summary
    assert note == "counted_loop_branch_accumulator_summary"
    assert len(summarized_returns) == 4
    loop_cases = [
        ret
        for ret in summarized_returns
        if any(cond.to_string() == "(start < limit)" for cond in ret.conditions)
    ]
    assert len(loop_cases) == 2
    assert any("((start & 1) == 0)" in cond.to_string() for ret in loop_cases for cond in ret.conditions)
    assert any("not ((start & 1) == 0)" in cond.to_string() for ret in loop_cases for cond in ret.conditions)

def test_structural_recurrence_summarizer_infers_loop_pair_from_negated_lessequal_progress_guard():
    params = [
        {"name": "trace", "index": 0, "data_type": "int *", "size": 8},
        {"name": "start", "index": 1, "data_type": "int", "size": 4, "is_signed": True},
        {"name": "limit", "index": 2, "data_type": "int", "size": 4, "is_signed": True},
    ]
    base_expr = Expression.binary_op("INT_ADD", _mem("trace", 0), _mem("trace", 4))
    analysis = create_mock_analysis(
        "lr_loop_with_side_effect.part.0",
        return_type="int",
        parameters=params,
        returns=[
            ReturnInfo(
                address="0x1000",
                value=base_expr,
                conditions=[
                    _cond("INT_SLESSEQUAL", _param("limit"), _param("start")),
                ],
            ),
            ReturnInfo(
                address="0x1004",
                value=Expression.binary_op(
                    "INT_ADD",
                    Expression.binary_op("INT_ADD", _mem("trace", 4), _const(1)),
                    Expression.binary_op("INT_ADD", _mem("trace", 0), _param("start")),
                ),
                conditions=[
                    _cond("INT_SLESSEQUAL", _param("limit"), _param("start"), negated=True),
                    _cond("INT_EQUAL", Expression.binary_op("INT_AND", _param("start"), _const(1)), _const(0)),
                    _cond("INT_EQUAL", Expression.binary_op("INT_ADD", _param("start"), _const(1)), _param("limit")),
                ],
            ),
            ReturnInfo(
                address="0x1008",
                value=Expression.binary_op(
                    "INT_ADD",
                    Expression.binary_op("INT_ADD", _mem("trace", 4), _const(1)),
                    Expression.binary_op("INT_ADD", _mem("trace", 0), Expression.unary_op("INT_2COMP", _param("start"))),
                ),
                conditions=[
                    _cond("INT_SLESSEQUAL", _param("limit"), _param("start"), negated=True),
                    _cond("INT_EQUAL", Expression.binary_op("INT_AND", _param("start"), _const(1)), _const(0), negated=True),
                    _cond("INT_EQUAL", Expression.binary_op("INT_ADD", _param("start"), _const(1)), _param("limit")),
                ],
            ),
        ],
    )

    summarizer = StructuralRecurrenceSummarizer(_FakeTracer("unused", _const(0)), debug=False)
    assert summarizer._infer_loop_parameter_pair(analysis) == ("start", "limit")

def test_structural_recurrence_summarizer_accepts_wrapper_guarded_helper_without_local_nonnull_check():
    params = [
        {"name": "param_1", "index": 0, "data_type": "int *", "size": 8},
        {"name": "param_2", "index": 1, "data_type": "int", "size": 4, "is_signed": True},
        {"name": "param_3", "index": 2, "data_type": "int", "size": 4, "is_signed": True},
    ]
    base_expr = Expression.binary_op("INT_ADD", _mem("param_1", 0), _mem("param_1", 4))
    analysis = create_mock_analysis(
        "lr_loop_with_side_effect.part.0",
        return_type="int",
        parameters=params,
        returns=[
            ReturnInfo(
                address="0x1004",
                value=base_expr,
                conditions=[
                    _cond("INT_SLESSEQUAL", _param("param_3"), _param("param_2")),
                ],
            ),
        ],
    )
    odd_conditions = [
        _cond("INT_SLESS", _param("param_2"), _param("param_3")),
        _cond("INT_EQUAL", Expression.binary_op("INT_AND", _param("param_2"), _const(1)), _const(0), negated=True),
    ]
    even_conditions = [
        _cond("INT_SLESS", _param("param_2"), _param("param_3")),
        _cond("INT_EQUAL", Expression.binary_op("INT_AND", _param("param_2"), _const(1)), _const(0)),
    ]
    analysis.effect_summary = EffectSummary(
        parameter_names=["param_1", "param_2", "param_3"],
        effects=[
            StoreEffect(
                _loc("param_1", 0, 4),
                Expression.binary_op("INT_ADD", _mem("param_1", 0), Expression.unary_op("INT_2COMP", _param("param_2"))),
                odd_conditions,
                1,
            ),
            StoreEffect(
                _loc("param_1", 4, 4),
                Expression.binary_op("INT_ADD", _mem("param_1", 4), _const(1)),
                odd_conditions,
                2,
            ),
            StoreEffect(
                _loc("param_1", 0, 4),
                Expression.binary_op("INT_ADD", _mem("param_1", 0), _param("param_2")),
                even_conditions,
                3,
            ),
            StoreEffect(
                _loc("param_1", 4, 4),
                Expression.binary_op("INT_ADD", _mem("param_1", 4), _const(1)),
                even_conditions,
                4,
            ),
        ],
    )

    summarizer = StructuralRecurrenceSummarizer(_FakeTracer("unused", _const(0)), debug=False)
    summary = summarizer.try_summarize_function(
        _FakeFunction("lr_loop_with_side_effect.part.0"),
        _FakeHighFunction([]),
        analysis,
    )

    assert summary is not None
    summarized_returns, note = summary
    assert note == "counted_loop_branch_accumulator_summary"
    assert len(summarized_returns) == 3
    assert any(
        any(cond.to_string() == "(param_2 < param_3)" for cond in ret.conditions)
        for ret in summarized_returns
    )

def test_structural_recurrence_summarizer_reduces_phi_wrapped_store_effects_before_delta_extraction():
    params = [
        {"name": "param_1", "index": 0, "data_type": "int *", "size": 8},
        {"name": "param_2", "index": 1, "data_type": "int", "size": 4, "is_signed": True},
        {"name": "param_3", "index": 2, "data_type": "int", "size": 4, "is_signed": True},
    ]
    base_expr = Expression.binary_op("INT_ADD", _mem("param_1", 0), _mem("param_1", 4))
    analysis = create_mock_analysis(
        "lr_loop_with_side_effect.part.0",
        return_type="int",
        parameters=params,
        returns=[
            ReturnInfo(
                address="0x1004",
                value=base_expr,
                conditions=[
                    _cond("INT_SLESSEQUAL", _param("param_3"), _param("param_2")),
                ],
            ),
        ],
    )

    odd_conditions = [
        _cond("INT_SLESS", _param("param_2"), _param("param_3")),
        Condition(
            Expression.binary_op(
                "INT_NOTEQUAL",
                Expression.binary_op("INT_AND", _param("param_2"), _const(1)),
                _const(0),
            ),
            False,
        ),
    ]
    even_conditions = [
        _cond("INT_SLESS", _param("param_2"), _param("param_3")),
        _cond("INT_EQUAL", Expression.binary_op("INT_AND", _param("param_2"), _const(1)), _const(0)),
    ]
    step_notequal = Condition(
        Expression.binary_op(
            "INT_NOTEQUAL",
            Expression.binary_op("INT_ADD", _param("param_2"), _const(1)),
            _param("param_3"),
        ),
        False,
    )

    odd_phi_base = Expression.phi(
        [
            (_cond("INT_SLESS", _param("param_2"), _param("param_3")), _mem("param_1", 0)),
            (step_notequal, Expression.unknown("phi_circular_odd")),
        ]
    )
    odd_phi_base.size = 4
    even_phi_base = Expression.phi(
        [
            (_cond("INT_SLESS", _param("param_2"), _param("param_3")), _mem("param_1", 0)),
            (step_notequal, Expression.unknown("phi_circular_even")),
        ]
    )
    even_phi_base.size = 4

    analysis.effect_summary = EffectSummary(
        parameter_names=["param_1", "param_2", "param_3"],
        effects=[
            StoreEffect(
                _loc("param_1", 0, 4),
                Expression.binary_op(
                    "INT_ADD",
                    odd_phi_base,
                    Expression.unary_op("INT_2COMP", _param("param_2")),
                ),
                odd_conditions,
                1,
            ),
            StoreEffect(
                _loc("param_1", 4, 4),
                Expression.binary_op("INT_ADD", _mem_mul_offset("param_1", 4), _const(1)),
                odd_conditions,
                2,
            ),
            StoreEffect(
                _loc("param_1", 0, 4),
                Expression.binary_op("INT_ADD", even_phi_base, _param("param_2")),
                even_conditions,
                3,
            ),
            StoreEffect(
                _loc("param_1", 4, 4),
                Expression.binary_op("INT_ADD", _mem_mul_offset("param_1", 4), _const(1)),
                even_conditions,
                4,
            ),
        ],
    )

    summarizer = StructuralRecurrenceSummarizer(_FakeTracer("unused", _const(0)), debug=False)
    summary = summarizer.try_summarize_function(
        _FakeFunction("lr_loop_with_side_effect.part.0"),
        _FakeHighFunction([]),
        analysis,
    )

    assert summary is not None
    summarized_returns, note = summary
    assert note == "counted_loop_branch_accumulator_summary"
    assert len(summarized_returns) == 3
