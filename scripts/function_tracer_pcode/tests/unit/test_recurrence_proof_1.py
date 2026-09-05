from unittest.mock import Mock
from scripts.function_tracer_pcode.tests.unit._recurrence_fixtures import *

def test_condition_implication_keeps_named_parameters_with_placeholder_indices_distinct():
    param_2_placeholder = Expression.parameter("param_2", index=0, data_type="int", size=4)
    param_3_placeholder = Expression.parameter("param_3", index=0, data_type="int", size=4)
    less_condition = _cond("INT_SLESS", param_2_placeholder, param_3_placeholder)
    parity_condition = _cond(
        "INT_EQUAL",
        Expression.binary_op("INT_AND", param_2_placeholder, _const(1)),
        _const(0),
    )

    assert ConditionSimplifier._condition_is_implied(
        parity_condition,
        [less_condition],
        prefer_solver=True,
    ) is False
    assert [condition.to_string() for condition in ConditionSimplifier.simplify_conditions_object_centric(
        [less_condition, parity_condition]
    )] == ["(param_2 < param_3)", "((param_2 & 1) == 0)"]

def test_return_region_summary_coverage_proves_positive_and_nonpositive_partition():
    summarizer = StructuralRecurrenceSummarizer(tracer=None, debug=False)
    n = _param()
    exact_nonpositive = ReturnInfo(
        address="0x1000",
        value=_const(1),
        conditions=[_cond("INT_SLESS", n, _const(1))],
    )

    coverage_key = summarizer._prove_summary_conditions_plus_exact_returns_cover_active_precondition(
        summary_conditions=[_cond("INT_SLESSEQUAL", _const(1), n)],
        exact_returns=[exact_nonpositive],
    )

    assert coverage_key is not None

def test_return_region_summary_coverage_uses_active_preconditions():
    summarizer = StructuralRecurrenceSummarizer(tracer=None, debug=False)
    n = _param()
    exact_nonpositive = ReturnInfo(
        address="0x1000",
        value=_const(1),
        conditions=[_cond("INT_SLESS", n, _const(1))],
    )

    coverage_key = summarizer._prove_summary_conditions_plus_exact_returns_cover_active_precondition(
        active_preconditions=[_cond("INT_NOTEQUAL", n, _const(1))],
        summary_conditions=[_cond("INT_SLESS", _const(1), n)],
        exact_returns=[exact_nonpositive],
    )

    assert coverage_key is not None

def test_return_region_summary_coverage_accepts_masked_singleton_carve_out():
    summarizer = StructuralRecurrenceSummarizer(tracer=None, debug=False)
    pointer = Expression.parameter("param_1", index=0, data_type="int *", size=8)
    count = Expression.parameter("param_2", index=1, data_type="int", size=4)
    parameters = [
        {"name": "param_1", "index": 0, "size": 8, "data_type": "int *", "is_signed": False},
        {"name": "param_2", "index": 1, "size": 4, "data_type": "int", "is_signed": True},
    ]
    pointer_nonnull = _cond("INT_NOTEQUAL", pointer, Expression.constant(0, size=8))
    pointer_null = _cond("INT_EQUAL", pointer, Expression.constant(0, size=8))
    count_positive = _cond("INT_SLESS", Expression.constant(0, size=4), count)
    count_nonpositive = count_positive.negate()
    count_not_one = Condition(Expression.binary_op("INT_EQUAL", count, _const(1)), negated=True)
    masked_count = Expression.binary_op("INT_AND", count, Expression.constant(0xFFFFFFFF, size=4))
    masked_count.size = 4
    masked_selector = Expression.binary_op(
        "INT_NOTEQUAL",
        Expression.binary_op("INT_SUB", masked_count, _const(1)),
        _const(0),
    )
    masked_selector.size = 1
    exact_count_one = ReturnInfo(
        address="0x1000",
        value=_mem("param_1", 0),
        conditions=[pointer_nonnull, count_positive, Condition(masked_selector, negated=True)],
    )
    exact_pointer_null = ReturnInfo(
        address="0x1004",
        value=_const(-300),
        conditions=[pointer_null],
    )
    exact_count_nonpositive = ReturnInfo(
        address="0x1008",
        value=_const(-300),
        conditions=[pointer_nonnull, count_nonpositive],
    )

    coverage_key = summarizer._prove_summary_conditions_plus_exact_returns_cover_active_precondition(
        summary_conditions=[pointer_nonnull, count_positive, count_not_one],
        exact_returns=[exact_count_one, exact_pointer_null, exact_count_nonpositive],
        parameters=parameters,
    )

    assert coverage_key is not None

def test_accepted_return_partition_view_does_not_mutate_seed_analysis():
    seed_return = ReturnInfo(address="0x1000", value=_const(0), conditions=[])
    accepted_return = ReturnInfo(
        address="0x1010",
        value=_const(1),
        conditions=[_cond("INT_SLESS", _const(0), _param())],
        return_kind="summary_derived",
    )
    seed = FunctionReturnAnalysis(
        function_name="pure_loop",
        entry_point="0x1000",
        parameters=[{"name": "param_1", "index": 0, "type": "int", "size": 4}],
        returns=[seed_return],
        analysis_scope_key=("function", "pure_loop"),
        return_type="int",
    )
    seed.analysis_notes.append("seed_note")

    view = seed.with_accepted_return_partition(
        [seed_return, accepted_return],
        reason="pure_return_coverage_completion",
    )
    other_view = seed.with_accepted_return_partition(
        [
            seed_return,
            ReturnInfo(
                address="0x1010",
                value=_const(2),
                conditions=[_cond("INT_SLESS", _const(0), _param())],
                return_kind="summary_derived",
            ),
        ],
        reason="pure_return_coverage_completion",
    )
    view.analysis_notes.append("view_note")

    assert seed.returns == [seed_return]
    assert "view_note" not in seed.analysis_notes
    assert view.returns == [seed_return, accepted_return]
    assert view.partition_revision == seed.partition_revision + 1
    assert view.analysis_view_identity is not None
    assert view.analysis_view_identity[0] == "accepted_return_partition_view"
    assert other_view.analysis_view_identity != view.analysis_view_identity
    assert view.to_dict()["analysis_view_identity"][0] == "accepted_return_partition_view"
    assert view.to_dict()["partition_revision"] == view.partition_revision

def test_phase1_high_function_visible_scan_allows_integer_no_effect_body():
    analyzer = ReturnAnalyzer.__new__(ReturnAnalyzer)
    high_function = _Phase1FakeHighFunction([
        ["COPY", "INT_ADD", "INT_SLESS", "CBRANCH"],
        ["MULTIEQUAL", "INT_MULT", "RETURN"],
    ])

    assert analyzer._high_function_has_phase1_pure_return_forbidden_ops(high_function) is False

def test_phase1_high_function_visible_scan_rejects_memory_call_control_and_fp_ops():
    analyzer = ReturnAnalyzer.__new__(ReturnAnalyzer)

    for mnemonic in (
        "LOAD",
        "STORE",
        "CALL",
        "CALLIND",
        "BRANCHIND",
        "CALLOTHER",
        "FLOAT_ADD",
        "FLOAT_LESSEQUAL",
        "INT2FLOAT",
        "FLOAT2INT",
    ):
        high_function = _Phase1FakeHighFunction([["COPY", mnemonic, "RETURN"]])
        assert analyzer._high_function_has_phase1_pure_return_forbidden_ops(high_function) is True

def test_phase1_function_body_scan_rejects_forbidden_ops_not_seen_in_high_function():
    analyzer = ReturnAnalyzer(program=Mock(), debug=False)  # 通常の生成; collaborator を揃える（program は各テストが後から差し替える）
    analyzer.program = _Phase1FakeProgram([
        _Phase1FakeInstruction(["COPY", "INT_ADD"]),
        _Phase1FakeInstruction(["LOAD", "RETURN"]),
    ])
    function = _Phase1FakeFunction()
    high_function = _Phase1FakeHighFunction([["COPY", "INT_ADD", "RETURN"]])
    effect_summary = EffectSummary(parameter_names=[], effects=[])

    assert analyzer._function_body_has_phase1_pure_return_forbidden_ops(function) is True
    assert analyzer._effect_summary_allows_pre_return_structural_summary(
        effect_summary,
        function=function,
        high_function=high_function,
    ) is False

def test_phase1_function_body_scan_still_rejects_forbidden_high_function_ops():
    analyzer = ReturnAnalyzer(program=Mock(), debug=False)  # 通常の生成; collaborator を揃える（program は各テストが後から差し替える）
    analyzer.program = _Phase1FakeProgram([
        _Phase1FakeInstruction(["COPY", "INT_ADD", "CBRANCH"]),
        _Phase1FakeInstruction(["MULTIEQUAL", "INT_MULT", "RETURN"]),
    ])
    function = _Phase1FakeFunction()
    high_function = _Phase1FakeHighFunction([["LOAD"]])
    effect_summary = EffectSummary(parameter_names=[], effects=[])

    assert analyzer._function_body_has_phase1_pure_return_forbidden_ops(function) is False
    assert analyzer._effect_summary_allows_pre_return_structural_summary(
        effect_summary,
        function=function,
        high_function=high_function,
    ) is False

def test_phase1_function_body_and_high_function_scan_allow_integer_no_effect_body():
    analyzer = ReturnAnalyzer(program=Mock(), debug=False)  # 通常の生成; collaborator を揃える（program は各テストが後から差し替える）
    analyzer.program = _Phase1FakeProgram([
        _Phase1FakeInstruction(["COPY", "INT_ADD", "CBRANCH"]),
        _Phase1FakeInstruction(["MULTIEQUAL", "INT_MULT", "RETURN"]),
    ])
    function = _Phase1FakeFunction()
    high_function = _Phase1FakeHighFunction([["COPY", "INT_ADD", "RETURN"]])
    effect_summary = EffectSummary(parameter_names=[], effects=[])

    assert analyzer._function_body_has_phase1_pure_return_forbidden_ops(function) is False
    assert analyzer._high_function_has_phase1_pure_return_forbidden_ops(high_function) is False
    assert analyzer._effect_summary_allows_pre_return_structural_summary(
        effect_summary,
        function=function,
        high_function=high_function,
    ) is True

def test_phase1_function_body_scan_failure_is_conservative():
    analyzer = ReturnAnalyzer(program=Mock(), debug=False)  # 通常の生成; collaborator を揃える（program は各テストが後から差し替える）
    analyzer.program = Mock()
    analyzer.program.getListing.side_effect = RuntimeError("listing unavailable")

    assert analyzer._function_body_has_phase1_pure_return_forbidden_ops(_Phase1FakeFunction()) is True

def test_phase1_function_body_pcode_iterator_failure_after_safe_op_is_conservative():
    analyzer = ReturnAnalyzer(program=Mock(), debug=False)  # 通常の生成; collaborator を揃える（program は各テストが後から差し替える）
    analyzer.program = _Phase1FakeProgram([_Phase1BrokenInstruction()])

    assert analyzer._function_body_has_phase1_pure_return_forbidden_ops(_Phase1FakeFunction()) is True

def test_phase1_function_body_scan_rejects_direct_branch_outside_body():
    analyzer = ReturnAnalyzer(program=Mock(), debug=False)  # 通常の生成; collaborator を揃える（program は各テストが後から差し替える）
    analyzer.program = _Phase1FakeProgram([
        _Phase1FakeInstruction(["COPY", "BRANCH"], flows=[_Phase1FakeAddress(0x2000)]),
    ])

    assert analyzer._function_body_has_phase1_pure_return_forbidden_ops(_Phase1FakeFunction()) is True

def test_phase1_function_body_scan_allows_direct_branch_inside_body():
    analyzer = ReturnAnalyzer(program=Mock(), debug=False)  # 通常の生成; collaborator を揃える（program は各テストが後から差し替える）
    analyzer.program = _Phase1FakeProgram([
        _Phase1FakeInstruction(["COPY", "BRANCH"], flows=[_Phase1FakeAddress(0x1010)]),
        _Phase1FakeInstruction(["RETURN"]),
    ])

    assert analyzer._function_body_has_phase1_pure_return_forbidden_ops(_Phase1FakeFunction()) is False

def test_phase1_pre_return_effect_gate_rejects_impure_high_function():
    analyzer = ReturnAnalyzer(program=Mock(), debug=False)  # 通常の生成; collaborator を揃える（program は各テストが後から差し替える）
    high_function = _Phase1FakeHighFunction([["COPY", "LOAD", "RETURN"]])
    effect_summary = EffectSummary(parameter_names=[], effects=[])

    assert analyzer._effect_summary_allows_pre_return_structural_summary(
        effect_summary,
        high_function=high_function,
    ) is False

def test_phase1_pre_return_effect_gate_rejects_float_return_type():
    analyzer = ReturnAnalyzer(program=Mock(), debug=False)  # 通常の生成; collaborator を揃える（program は各テストが後から差し替える）
    high_function = _Phase1FakeHighFunction([["COPY", "INT_ADD", "RETURN"]])
    effect_summary = EffectSummary(parameter_names=[], effects=[])

    assert analyzer._effect_summary_allows_pre_return_structural_summary(
        effect_summary,
        high_function=high_function,
        return_type="double",
    ) is False

def test_counter_parameter_candidate_selection_rejects_name_only_parameter():
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

    assert summarizer._vectorized_affine_counter_expression(name_only_param, analysis) is None

def test_same_counter_expression_rejects_name_only_parameter_alias():
    summarizer = StructuralRecurrenceSummarizer(PcodeTracer.__new__(PcodeTracer), debug=False)
    left = Expression.parameter("count", index=-1, data_type="int", size=4)
    right = Expression.parameter("count", index=-1, data_type="int", size=4)

    assert not summarizer._same_counter_expression(left, right)

def test_counter_parameter_normalization_requires_storage_match_when_present():
    storage_a = StorageInfo(
        is_register=True,
        space_name="register",
        register_name="w0",
        base_register_name="x0",
        size=4,
        size_bits=32,
    )
    storage_b = StorageInfo(
        is_register=True,
        space_name="register",
        register_name="w1",
        base_register_name="x1",
        size=4,
        size_bits=32,
    )
    summarizer = StructuralRecurrenceSummarizer(PcodeTracer.__new__(PcodeTracer), debug=False)
    primary_counter = Expression.parameter("param_1", index=-1, data_type="int", size=4, storage_info=storage_a)
    same_name_other_storage = Expression.parameter("param_1", index=-1, data_type="int", size=4, storage_info=storage_b)
    expr = Expression.binary_op("INT_SLESS", same_name_other_storage, _const(1))

    normalized = summarizer._normalize_counter_parameter_expression(
        expr,
        {"name": "param_1", "size": 4, "data_type": "int", "storage_info": storage_a},
        primary_counter,
    )

    assert normalized is expr
    assert normalized.operands[0] is same_name_other_storage

def test_excluded_counter_value_coverage_requires_storage_identity_match():
    storage_a = StorageInfo(
        is_register=True,
        space_name="register",
        register_name="w0",
        base_register_name="x0",
        size=4,
        size_bits=32,
    )
    storage_b = StorageInfo(
        is_register=True,
        space_name="register",
        register_name="w1",
        base_register_name="x1",
        size=4,
        size_bits=32,
    )
    summarizer = StructuralRecurrenceSummarizer(PcodeTracer.__new__(PcodeTracer), debug=False)
    summary_counter = Expression.parameter("n", index=0, data_type="int", size=4, storage_info=storage_a)
    exact_counter = Expression.parameter("n", index=0, data_type="int", size=4, storage_info=storage_b)
    summary_conditions = [
        Condition(Expression.binary_op("INT_EQUAL", summary_counter, _const(1)), negated=True)
    ]
    exact_conditions = [_cond("INT_EQUAL", exact_counter, _const(1))]
    same_storage_exact_conditions = [_cond("INT_EQUAL", summary_counter, _const(1))]

    excluded = summarizer._summary_excluded_counter_values(summary_conditions)

    assert excluded
    assert not summarizer._conditions_cover_summary_excluded_counter_value(exact_conditions, excluded)
    assert summarizer._conditions_cover_summary_excluded_counter_value(
        same_storage_exact_conditions,
        excluded,
    )

def test_counter_parameter_normalization_allows_same_register_slot_storage_variant():
    storage_descriptor = StorageInfo(
        is_register=True,
        space_name="register",
        space_id=0,
        offset=0x4000,
        register_offset=0x4000,
        register_name="w0",
        base_register_name="x0",
        base_register_offset=0x3D98,
        base_register_size=8,
        base_register_size_bits=64,
        size=4,
        size_bits=32,
        bit_offset_in_base=0,
    )
    storage_runtime = StorageInfo(
        is_register=True,
        space_name="register",
        space_id=548,
        offset=0x4000,
        register_offset=0x4000,
        register_name="w0",
        base_register_name="x0",
        base_register_offset=0x4000,
        base_register_size=8,
        base_register_size_bits=64,
        size=4,
        size_bits=32,
        bit_offset_in_base=0,
    )
    summarizer = StructuralRecurrenceSummarizer(PcodeTracer.__new__(PcodeTracer), debug=False)
    primary_counter = Expression.parameter("param_1", index=0, data_type="int", size=4, storage_info=storage_descriptor)
    runtime_counter = Expression.parameter("param_1", index=0, data_type="int", size=4, storage_info=storage_runtime)
    expr = Expression.binary_op("INT_SLESS", runtime_counter, _const(1))

    normalized = summarizer._normalize_counter_parameter_expression(
        expr,
        {"name": "param_1", "index": 0, "size": 4, "data_type": "int", "storage_info": storage_descriptor},
        primary_counter,
    )

    assert normalized is not expr
    assert normalized.operands[0] is primary_counter

def test_recurrence_terms_equivalent_does_not_require_to_string(monkeypatch):
    summarizer = StructuralRecurrenceSummarizer(PcodeTracer.__new__(PcodeTracer), debug=False)
    left = Expression.binary_op(
        "INT_ADD",
        Expression.parameter("param_1", index=0, size=4),
        Expression.constant(1, 4),
    )
    right = Expression.binary_op(
        "INT_ADD",
        Expression.constant(1, 4),
        Expression.parameter("param_1", index=0, size=4),
    )

    def _boom_expr(_self, simplify=True):
        raise AssertionError("recurrence equivalence should not depend on Expression.to_string")

    monkeypatch.setattr(Expression, "to_string", _boom_expr)

    assert summarizer._terms_equivalent(left, right, []) is True

def test_summary_auxiliary_symbols_are_reassigned_after_descriptor_merge():
    summarizer = StructuralRecurrenceSummarizer(PcodeTracer.__new__(PcodeTracer), debug=False)

    assigned = summarizer._assign_summary_auxiliary_symbols(
        [
            {
                "identity": ("synthetic_parameter_index", -10000),
                "size": 4,
                "aux_name": "aux_sym_0",
            },
            {
                "identity": ("parameter_index", 0),
                "size": 4,
            },
        ]
    )

    names = [spec["aux_name"] for spec in assigned]
    assert names == ["aux_sym_0", "aux_sym_1"]
    assert len(names) == len(set(names))

def test_summary_expression_equivalence_query_refuses_name_only_parameter_symbol():
    summarizer = StructuralRecurrenceSummarizer(PcodeTracer.__new__(PcodeTracer), debug=False)
    name_only = Expression.parameter("count", data_type="int", size=4)

    query = summarizer._build_expression_equivalence_query(
        name_only,
        name_only,
        [],
        [{"name": "count", "size": 4, "data_type": "int"}],
    )

    assert query is None

def test_summary_expression_equivalence_query_rejects_unsupported_intrinsic_without_error():
    summarizer = StructuralRecurrenceSummarizer(PcodeTracer.__new__(PcodeTracer), debug=False)
    unsupported = Expression.intrinsic(
        "CALLOTHER",
        [_const(1)],
        size=4,
        opcode=0,
    )

    query = summarizer._build_expression_equivalence_query(
        unsupported,
        _const(1),
        [],
        [],
    )

    assert query is None


def test_summary_expression_equivalence_query_rejects_unsupported_operator_without_error():
    summarizer = StructuralRecurrenceSummarizer(PcodeTracer.__new__(PcodeTracer), debug=False)
    unsupported = Expression.unary_op(
        "FLOAT2INT",
        Expression.parameter("value", index=0, data_type="double", size=8),
    )
    unsupported.size = 4

    query = summarizer._build_expression_equivalence_query(
        unsupported,
        _const(1),
        [],
        [{"name": "value", "index": 0, "size": 8, "data_type": "double"}],
    )

    assert query is None


def test_summary_expression_equivalence_query_does_not_alias_duplicate_variable_names():
    summarizer = StructuralRecurrenceSummarizer(PcodeTracer.__new__(PcodeTracer), debug=False)
    left = Expression.variable("tmp", size=4)
    right = Expression.variable("tmp", size=4)

    query = summarizer._build_expression_equivalence_query(left, right, [], [])

    assert query is not None
    assert "(declare-const aux_sym_0 (_ BitVec 32))" in query
    assert "(declare-const aux_sym_1 (_ BitVec 32))" in query
    assert "(assert (not (= aux_sym_0 aux_sym_1)))" in query or "(assert (not (= aux_sym_1 aux_sym_0)))" in query
    assert "tmp_aux" not in query

def test_expression_equivalence_query_coerces_mixed_width_values():
    summarizer = StructuralRecurrenceSummarizer(PcodeTracer.__new__(PcodeTracer), debug=False)
    wide_zero = Expression.unary_op("INT_ZEXT", _const(0))
    wide_zero.size = 16
    query = summarizer._build_expression_equivalence_query(
        wide_zero,
        _const(0),
        [],
        [],
    )

    assert query is not None
    assert "(assert (not (= ((_ zero_extend 96) (_ bv0 32)) ((_ zero_extend 96) (_ bv0 32)))))" in query

def test_zero_base_canonicalization_handles_wide_zero_expression():
    summarizer = StructuralRecurrenceSummarizer(PcodeTracer.__new__(PcodeTracer), debug=False)
    wide_zero = Expression.unary_op("INT_ZEXT", _const(0))
    wide_zero.size = 16
    canonical = summarizer._canonicalize_zero_value_under_conditions(wide_zero, [])

    assert canonical.expr_type == ExpressionType.CONSTANT
    assert canonical.value == 0
    assert canonical.size == 16

def test_same_high_variable_rejects_name_only_alias():
    summarizer = StructuralRecurrenceSummarizer(_IdentityTracer(), debug=False)
    left = _FakeVarnode("left", high=_FakeHighVar("loop_state"))
    right = _FakeVarnode("right", high=_FakeHighVar("loop_state"))

    assert summarizer._same_high_variable(left, right) is False

def test_same_high_variable_accepts_shared_symbol_object():
    summarizer = StructuralRecurrenceSummarizer(_IdentityTracer(), debug=False)
    symbol = _FakeHighSymbol(category_index=1)
    left = _FakeVarnode("left", high=_FakeHighVar("left_state", symbol=symbol))
    right = _FakeVarnode("right", high=_FakeHighVar("right_state", symbol=symbol))

    assert summarizer._same_high_variable(left, right) is True

def test_varnode_matches_parameter_rejects_name_only_high_variable():
    summarizer = StructuralRecurrenceSummarizer(_IdentityTracer(), debug=False)
    varnode = _FakeVarnode("param_1", high=_FakeHighVar("param_1"))
    parameter = {"name": "param_1", "index": 0, "size": 4}

    assert summarizer._varnode_matches_parameter(varnode, parameter) is False

def test_peeled_decrement_accumulator_sum_keeps_state_width_until_return_truncation():
    summarizer = StructuralRecurrenceSummarizer(_FakeTracer("unused", _const(0)), debug=False)
    value = summarizer._build_peeled_decrement_accumulator_sum_value(
        _param("param_1", size=8),
        result_size=4,
    )

    assert value is not None
    assert value.size == 4
    n_value = 0x100000001
    expected_low_sum = ((n_value * (n_value + 1)) // 2) & 0xFFFFFFFF
    assert expected_low_sum == 0x80000001
    assert _eval_bv_expression(value, {"param_1": n_value}) == expected_low_sum

def test_path_enumeration_no_path_is_not_unconditional_success():
    start = _FakeCfgBlock(0)
    target = _FakeCfgBlock(1)
    header = _FakeCfgBlock(2)
    summarizer = StructuralRecurrenceSummarizer(_FakeTracer("unused", _const(0)), debug=False)

    assert summarizer._enumerate_paths_with_conditions(
        start_block=start,
        target_block=target,
        header_block=header,
        placeholders={},
    ) == []

def test_structural_recurrence_summary_uses_widened_closed_form():
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
    summarized_returns, _ = summary
    recursive_case = next(ret for ret in summarized_returns if ret.value.to_string() != "0")
    recursive_smt = recursive_case.value.to_smt()
    assert "zero_extend" in recursive_smt
    assert "extract 31 0" in recursive_smt
    assert "(bvmul ((_ zero_extend" in recursive_smt

def test_path_enumeration_reports_incomplete_when_limit_is_reached():
    summarizer = StructuralRecurrenceSummarizer(_FakeTracer("unused", _const(0)), debug=False)
    header = _FakeCfgBlock(0)
    body = _FakeCfgBlock(1)
    left = _FakeCfgBlock(2)
    right = _FakeCfgBlock(3)
    target = _FakeCfgBlock(4)
    exit_block = _FakeCfgBlock(5)
    body.add_edge(left)
    body.add_edge(right)
    left.add_edge(target)
    right.add_edge(target)
    target.add_edge(header)

    paths, incomplete = summarizer._enumerate_paths_with_conditions_result(
        start_block=body,
        target_block=target,
        header_block=header,
        placeholders={},
        stop_block=exit_block,
        limit=1,
    )

    assert len(paths) == 1
    assert incomplete is True

def test_repair_two_way_partition_conditions_preserves_existing_continue_conditions():
    summarizer = StructuralRecurrenceSummarizer(_FakeTracer("unused", _const(0)), debug=False)

    base_conditions = [_cond("INT_SLESS", _const(0), _param("param_1"), negated=True)]
    continue_conditions = [
        _cond("INT_SLESS", _const(0), _param("param_1")),
        _cond("INT_NOTEQUAL", Expression.binary_op("INT_AND", _param("param_1"), _const(1)), _const(0)),
    ]

    repaired_base, repaired_continue = summarizer._repair_two_way_partition_conditions(
        base_conditions,
        continue_conditions,
    )

    assert [cond.to_string() for cond in repaired_base] == ["(not (0 < param_1))"]
    assert [cond.to_string() for cond in repaired_continue] == [
        "(0 < param_1)",
        "((param_1 & 1) != 0)",
    ]

def test_pcode_op_ref_stable_key_collapses_distinct_wrappers_for_same_logical_pcode():
    tracer = object.__new__(PcodeTracer)

    class _FakeOp:
        def __init__(self):
            self._seq = _FakeSeqNum("ram:00001000", 0)
            self._output = _FakeOutput(offset=0x24, size=4)

        def getSeqnum(self):
            return self._seq

        def getMnemonic(self):
            return "MULTIEQUAL"

        def getOutput(self):
            return self._output

    op1 = _FakeOp()
    op2 = _FakeOp()
    ref1 = PcodeOpRef.from_pcode_op(op1)
    ref2 = PcodeOpRef.from_pcode_op(op2)

    assert ref1 is not None
    assert ref2 is not None
    assert ref1.stable_key() == ref2.stable_key()
    assert not hasattr(tracer, "_get_" + "stable_op_key")
    assert tracer._get_op_key(op1) != tracer._get_op_key(op2)

def test_structural_recurrence_summarizer_synthesizes_missing_one_step_cases_from_effects():
    params = [
        {"name": "trace", "index": 0, "data_type": "int *", "size": 8},
        {"name": "start", "index": 1, "data_type": "int", "size": 4, "is_signed": True},
        {"name": "limit", "index": 2, "data_type": "int", "size": 4, "is_signed": True},
    ]
    trace_param = Expression.parameter("trace", index=0, data_type="int *", size=8)
    base_expr = Expression.binary_op("INT_ADD", _mem("trace", 0), _mem("trace", 4))
    analysis = create_mock_analysis(
        "lr_loop_with_side_effect",
        return_type="int",
        parameters=params,
        returns=[
            ReturnInfo(
                address="0x1000",
                value=Expression.constant(-100, size=4),
                conditions=[_cond("INT_EQUAL", trace_param, Expression.constant(0, size=8))],
            ),
            ReturnInfo(
                address="0x1004",
                value=base_expr,
                conditions=[
                    _cond("INT_NOTEQUAL", trace_param, Expression.constant(0, size=8)),
                    _cond("INT_SLESS", _param("start"), _param("limit"), negated=True),
                ],
            ),
        ],
    )
    even_conditions = [
        _cond("INT_NOTEQUAL", trace_param, Expression.constant(0, size=8)),
        _cond("INT_SLESS", _param("start"), _param("limit")),
        _cond("INT_EQUAL", Expression.binary_op("INT_AND", _param("start"), _const(1)), _const(0)),
    ]
    odd_conditions = [
        _cond("INT_NOTEQUAL", trace_param, Expression.constant(0, size=8)),
        _cond("INT_SLESS", _param("start"), _param("limit")),
        _cond("INT_EQUAL", Expression.binary_op("INT_AND", _param("start"), _const(1)), _const(0), negated=True),
    ]
    analysis.effect_summary = EffectSummary(
        parameter_names=["trace", "start", "limit"],
        effects=[
            StoreEffect(_loc("trace", 0, 4), Expression.binary_op("INT_ADD", _mem("trace", 0), _param("start")), even_conditions, 1),
            StoreEffect(_loc("trace", 4, 4), Expression.binary_op("INT_ADD", _mem("trace", 4), _const(1)), even_conditions, 2),
            StoreEffect(_loc("trace", 0, 4), Expression.binary_op("INT_ADD", _mem("trace", 0), Expression.unary_op("INT_2COMP", _param("start"))), odd_conditions, 3),
            StoreEffect(_loc("trace", 4, 4), Expression.binary_op("INT_ADD", _mem("trace", 4), _const(1)), odd_conditions, 4),
        ],
    )

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

def test_structural_recurrence_summarizer_accepts_swapped_lessequal_base_case():
    params = [
        {"name": "trace", "index": 0, "data_type": "int *", "size": 8},
        {"name": "start", "index": 1, "data_type": "int", "size": 4, "is_signed": True},
        {"name": "limit", "index": 2, "data_type": "int", "size": 4, "is_signed": True},
    ]
    trace_param = Expression.parameter("trace", index=0, data_type="int *", size=8)
    base_expr = Expression.binary_op("INT_ADD", _mem("trace", 0), _mem("trace", 4))
    analysis = create_mock_analysis(
        "lr_loop_with_side_effect",
        return_type="int",
        parameters=params,
        returns=[
            ReturnInfo(
                address="0x1000",
                value=Expression.constant(-100, size=4),
                conditions=[_cond("INT_EQUAL", trace_param, Expression.constant(0, size=8))],
            ),
            ReturnInfo(
                address="0x1004",
                value=base_expr,
                conditions=[
                    _cond("INT_NOTEQUAL", trace_param, Expression.constant(0, size=8)),
                    _cond("INT_SLESSEQUAL", _param("limit"), _param("start")),
                ],
            ),
        ],
    )
    even_conditions = [
        _cond("INT_NOTEQUAL", trace_param, Expression.constant(0, size=8)),
        _cond("INT_SLESS", _param("start"), _param("limit")),
        _cond("INT_EQUAL", Expression.binary_op("INT_AND", _param("start"), _const(1)), _const(0)),
    ]
    odd_conditions = [
        _cond("INT_NOTEQUAL", trace_param, Expression.constant(0, size=8)),
        _cond("INT_SLESS", _param("start"), _param("limit")),
        _cond("INT_EQUAL", Expression.binary_op("INT_AND", _param("start"), _const(1)), _const(0), negated=True),
    ]
    analysis.effect_summary = EffectSummary(
        parameter_names=["trace", "start", "limit"],
        effects=[
            StoreEffect(_loc("trace", 0, 4), Expression.binary_op("INT_ADD", _mem("trace", 0), _param("start")), even_conditions, 1),
            StoreEffect(_loc("trace", 4, 4), Expression.binary_op("INT_ADD", _mem("trace", 4), _const(1)), even_conditions, 2),
            StoreEffect(_loc("trace", 0, 4), Expression.binary_op("INT_ADD", _mem("trace", 0), Expression.unary_op("INT_2COMP", _param("start"))), odd_conditions, 3),
            StoreEffect(_loc("trace", 4, 4), Expression.binary_op("INT_ADD", _mem("trace", 4), _const(1)), odd_conditions, 4),
        ],
    )

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
    assert any(
        any(cond.to_string() == "(start < limit)" for cond in ret.conditions)
        for ret in summarized_returns
    )

def test_structural_recurrence_summarizer_synthesizes_effects_with_mul_wrapped_memory_offsets():
    params = [
        {"name": "param_1", "index": 0, "data_type": "int *", "size": 8},
        {"name": "param_2", "index": 1, "data_type": "int", "size": 4, "is_signed": True},
        {"name": "param_3", "index": 2, "data_type": "int", "size": 4, "is_signed": True},
    ]
    base_expr = Expression.binary_op("INT_ADD", _mem("param_1", 0), _mem("param_1", 4))
    trace_param = Expression.parameter("param_1", index=0, data_type="int *", size=8)
    analysis = create_mock_analysis(
        "lr_loop_with_side_effect",
        return_type="int",
        parameters=params,
        returns=[
            ReturnInfo(
                address="0x1000",
                value=Expression.constant(-100, size=4),
                conditions=[_cond("INT_EQUAL", trace_param, Expression.constant(0, size=8))],
            ),
            ReturnInfo(
                address="0x1004",
                value=base_expr,
                conditions=[
                    _cond("INT_NOTEQUAL", trace_param, Expression.constant(0, size=8)),
                    _cond("INT_SLESSEQUAL", _param("param_3"), _param("param_2")),
                ],
            ),
        ],
    )
    odd_conditions = [
        _cond("INT_NOTEQUAL", trace_param, Expression.constant(0, size=8)),
        _cond("INT_SLESS", _param("param_2"), _param("param_3")),
        _cond("INT_EQUAL", Expression.binary_op("INT_AND", _param("param_2"), _const(1)), _const(0), negated=True),
    ]
    even_conditions = [
        _cond("INT_NOTEQUAL", trace_param, Expression.constant(0, size=8)),
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
                Expression.binary_op("INT_ADD", _mem_mul_offset("param_1", 4), _const(1)),
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
                Expression.binary_op("INT_ADD", _mem_mul_offset("param_1", 4), _const(1)),
                even_conditions,
                4,
            ),
        ],
    )

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

def test_structural_recurrence_summarizer_accepts_direct_notequal_odd_parity_conditions():
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
        Condition(
            Expression.binary_op(
                "INT_EQUAL",
                Expression.parameter("param_1", index=0, data_type="int *", size=8),
                Expression.constant(0, size=8),
            ),
            True,
        ),
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
        Condition(
            Expression.binary_op(
                "INT_EQUAL",
                Expression.parameter("param_1", index=0, data_type="int *", size=8),
                Expression.constant(0, size=8),
            ),
            True,
        ),
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
                Expression.binary_op("INT_ADD", _mem_mul_offset("param_1", 4), _const(1)),
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
    assert any(
        any(cond.to_string() == "((param_2 & 1) != 0)" for cond in ret.conditions)
        or any(cond.to_string() == "(not ((param_2 & 1) == 0))" for cond in ret.conditions)
        for ret in summarized_returns
    )

def test_structural_recurrence_summarizer_candidate_probe_rejects_plain_memory_return():
    analysis = create_mock_analysis(
        "plain_load",
        return_type="int",
        parameters=[
            {"name": "param_1", "index": 0, "data_type": "int *", "size": 8},
            {"name": "param_2", "index": 1, "data_type": "int", "size": 4, "is_signed": True},
        ],
        returns=[
            ReturnInfo(
                address="0x1000",
                value=Expression.memory(
                    Expression.parameter("param_1", index=0, data_type="int *", size=8),
                    size=4,
                ),
                conditions=[],
            ),
        ],
    )

    summarizer = StructuralRecurrenceSummarizer(_FakeTracer("unused", _const(0)), debug=False)

    assert (
        summarizer.has_summary_candidate(
            _FakeFunction("plain_load"),
            _FakeHighFunction([]),
            analysis,
        )
        is False
    )

def test_materialized_wrong_tail_return_rejects_prefix_region_proof_only():
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
        value=Expression.binary_op(
            "INT_ADD",
            Expression.binary_op("INT_ADD", _mem("param_1", 0), _mem("param_1", 8)),
            _mem("param_1", 12),
        ),
        conditions=[
            _cond("INT_NOTEQUAL", ptr_expr, Expression.constant(0, size=8)),
            _cond("INT_SLESS", _const(3), count_expr),
        ],
    )
    analysis = create_mock_analysis(
        "ptr_sum_wrong_tail",
        return_type="int",
        parameters=[pointer_param, count_param],
        returns=[ret],
    )
    proof = _readonly_accumulator_proof(
        base_ref=LocationBaseRef.parameter("param_1", index=0),
        count_expr=count_expr,
        stride=4,
        element_size=4,
        start_offset=0,
        start_index=0,
        return_op_refs=(PcodeOpRef(address_offset=0x1004, seq_time=1, mnemonic="RETURN"),),
        return_region_value_proven=True,
    )
    summarizer = StructuralRecurrenceSummarizer(_FakeTracer("unused", _const(0)), debug=False)

    assert not summarizer._readonly_materialized_positive_return_matches_accumulator_contract(
        analysis,
        pointer_param,
        count_param,
        ret,
        proof,
    )

def test_materialized_wrong_tail_return_accepts_seeded_tail_contract():
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
        value=Expression.binary_op(
            "INT_ADD",
            Expression.binary_op("INT_ADD", _mem("param_1", 0), _mem("param_1", 8)),
            _mem("param_1", 12),
        ),
        conditions=[
            _cond("INT_NOTEQUAL", ptr_expr, Expression.constant(0, size=8)),
            _cond("INT_SLESS", _const(3), count_expr),
        ],
    )
    analysis = create_mock_analysis(
        "ptr_sum_wrong_tail",
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
        return_op_refs=(PcodeOpRef(address_offset=0x1004, seq_time=1, mnemonic="RETURN"),),
        return_region_value_proven=True,
    )
    summarizer = StructuralRecurrenceSummarizer(_FakeTracer("unused", _const(0)), debug=False)

    assert summarizer._readonly_materialized_positive_return_matches_accumulator_contract(
        analysis,
        pointer_param,
        count_param,
        ret,
        proof,
    )

def test_materialized_wrong_tail_anchor_count_accounts_for_explicit_seed_terms():
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
    value = _mem("param_1", 0)
    for offset in (8, 12, 16, 20, 24, 28, 32, 36, 40):
        value = Expression.binary_op("INT_ADD", value, _mem("param_1", offset))
    ret = ReturnInfo(
        address="0x1004",
        value=value,
        conditions=[
            _cond("INT_NOTEQUAL", ptr_expr, Expression.constant(0, size=8)),
            _cond("INT_SLESS", _const(10), count_expr),
        ],
    )
    analysis = create_mock_analysis(
        "ptr_sum_wrong_tail_vector_anchor",
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
        return_op_refs=(PcodeOpRef(address_offset=0x1004, seq_time=1, mnemonic="RETURN"),),
        return_region_value_proven=True,
    )
    summarizer = StructuralRecurrenceSummarizer(_FakeTracer("unused", _const(0)), debug=False)

    assert summarizer._readonly_positive_return_accumulator_anchor_count(
        analysis,
        pointer_param,
        count_param,
        ret,
        proof,
    ) == 11
    assert summarizer._readonly_materialized_positive_return_matches_accumulator_contract(
        analysis,
        pointer_param,
        count_param,
        ret,
        proof,
    )

def test_exact_materialized_return_rejects_conflicting_broad_prefix_proof():
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
        "data_type": "int",
        "size": 4,
        "is_signed": True,
    }
    ptr_expr = Expression.parameter("param_1", index=0, data_type="int *", size=8)
    count_expr = Expression.parameter("param_2", index=1, data_type="int", size=4)
    exact_four = ReturnInfo(
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
    analysis = FunctionReturnAnalysis(
        function_name="readonly_exact_conflicts_with_prefix_contract_like",
        entry_point="0x1000",
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
    broad_positive_conditions = [
        _cond("INT_NOTEQUAL", ptr_expr, Expression.constant(0, size=8)),
        _cond("INT_SLESS", _const(0), count_expr),
    ]
    tail_positive_conditions = [
        _cond("INT_NOTEQUAL", ptr_expr, Expression.constant(0, size=8)),
        _cond("INT_SLESS", _const(3), count_expr),
    ]
    summarizer = StructuralRecurrenceSummarizer(_FakeTracer("unused", _const(0)), debug=False)

    assert summarizer._readonly_exact_materialized_returns_conflict_with_accumulator_proof(
        analysis,
        pointer_param,
        count_param,
        broad_positive_conditions,
        prefix_proof,
    )
    assert not summarizer._readonly_exact_materialized_returns_conflict_with_accumulator_proof(
        analysis,
        pointer_param,
        count_param,
        tail_positive_conditions,
        seeded_tail_proof,
    )

def test_round_down_mask_requires_high_bits_preserved_for_counter_width():
    summarizer = StructuralRecurrenceSummarizer(_FakeTracer("unused", _const(0)), debug=False)

    assert summarizer._power_of_two_rounding_from_mask(0xFFFFFFF8, count_width_bits=32) == 8
    assert summarizer._power_of_two_rounding_from_mask(0xF8, count_width_bits=32) is None
    assert summarizer._power_of_two_rounding_from_mask(0xFFFFFFFFFFFFFFF8, count_width_bits=64) == 8

def test_round_down_candidate_uses_counter_semantic_width_through_zext():
    count_expr = Expression.parameter("param_2", index=1, data_type="int", size=4)
    count_vn = _FakeVarnode("param_2", size=4, expr=count_expr)
    zext_vn = _FakeVarnode("count_zext", size=8, expr=Expression.unary_op("INT_ZEXT", count_expr))
    zext_op = _FakePcodeOp("INT_ZEXT", [count_vn], zext_vn)
    mask_vn = _FakeVarnode("mask", size=8, expr=Expression.constant(0xFFFFFFF8, size=8))
    rounded_vn = _FakeVarnode("rounded", size=8)
    round_op = _FakePcodeOp("INT_AND", [zext_vn, mask_vn], rounded_vn)
    summarizer = StructuralRecurrenceSummarizer(_FakeTracer("unused", _const(0)), debug=False)

    assert summarizer._readonly_round_down_candidates(
        [zext_op, round_op],
        {"name": "param_2", "index": 1, "data_type": "int", "size": 4},
    ) == [ReadonlyRoundedCountCandidate(rounded_vn, 8, 0)]

def test_round_down_candidate_tracks_peeled_prefix_through_count_minus_constant():
    count_expr = Expression.parameter("param_2", index=1, data_type="int", size=4)
    count_vn = _FakeVarnode("param_2", size=4, expr=count_expr)
    zext_vn = _FakeVarnode("count_zext", size=8, expr=Expression.unary_op("INT_ZEXT", count_expr))
    zext_op = _FakePcodeOp("INT_ZEXT", [count_vn], zext_vn)
    three_vn = _FakeVarnode("three", size=8, expr=Expression.constant(3, size=8))
    peeled_vn = _FakeVarnode(
        "peeled_count",
        size=8,
        expr=Expression.binary_op(
            "INT_SUB",
            Expression.unary_op("INT_ZEXT", count_expr),
            Expression.constant(3, size=8),
        ),
    )
    sub_op = _FakePcodeOp("INT_SUB", [zext_vn, three_vn], peeled_vn)
    mask_vn = _FakeVarnode("mask", size=8, expr=Expression.constant(0xFFFFFFF8, size=8))
    rounded_vn = _FakeVarnode("rounded", size=8)
    round_op = _FakePcodeOp("INT_AND", [peeled_vn, mask_vn], rounded_vn)
    summarizer = StructuralRecurrenceSummarizer(_FakeTracer("unused", _const(0)), debug=False)

    assert summarizer._readonly_round_down_candidates(
        [zext_op, sub_op, round_op],
        {"name": "param_2", "index": 1, "data_type": "int", "size": 4},
    ) == [ReadonlyRoundedCountCandidate(rounded_vn, 8, 3)]

def test_round_down_candidate_accepts_divide_multiply_form():
    count_expr = Expression.parameter("param_2", index=1, data_type="int", size=4)
    count_vn = _FakeVarnode("param_2", size=4, expr=count_expr)
    three_vn = _FakeVarnode("three", size=4, expr=Expression.constant(3, size=4))
    peeled_vn = _FakeVarnode(
        "peeled_count",
        size=4,
        expr=Expression.binary_op("INT_SUB", count_expr, Expression.constant(3, size=4)),
    )
    sub_op = _FakePcodeOp("INT_SUB", [count_vn, three_vn], peeled_vn)
    four_vn = _FakeVarnode("four", size=4, expr=Expression.constant(4, size=4))
    quotient_vn = _FakeVarnode("quotient", size=4)
    div_op = _FakePcodeOp("INT_DIV", [peeled_vn, four_vn], quotient_vn)
    rounded_vn = _FakeVarnode("rounded", size=4)
    mul_op = _FakePcodeOp("INT_MULT", [quotient_vn, four_vn], rounded_vn)
    summarizer = StructuralRecurrenceSummarizer(_FakeTracer("unused", _const(0)), debug=False)

    assert summarizer._readonly_round_down_candidates(
        [sub_op, div_op, mul_op],
        {"name": "param_2", "index": 1, "data_type": "int", "size": 4},
    ) == [ReadonlyRoundedCountCandidate(rounded_vn, 4, 3)]

def test_round_down_candidate_accepts_preadvanced_divide_multiply_form():
    count_expr = Expression.parameter("param_2", index=1, data_type="int", size=4)
    count_vn = _FakeVarnode("param_2", size=4, expr=count_expr)
    three_vn = _FakeVarnode("three", size=4, expr=Expression.constant(3, size=4))
    peeled_vn = _FakeVarnode(
        "peeled_count",
        size=4,
        expr=Expression.binary_op("INT_SUB", count_expr, Expression.constant(3, size=4)),
    )
    sub_op = _FakePcodeOp("INT_SUB", [count_vn, three_vn], peeled_vn)
    shift_vn = _FakeVarnode("shift", size=4, expr=Expression.constant(2, size=4))
    quotient_vn = _FakeVarnode("quotient", size=4)
    right_op = _FakePcodeOp("INT_RIGHT", [peeled_vn, shift_vn], quotient_vn)
    one_vn = _FakeVarnode("one", size=4, expr=Expression.constant(1, size=4))
    quotient_minus_one_vn = _FakeVarnode("quotient_minus_one", size=4)
    minus_one_op = _FakePcodeOp("INT_SUB", [quotient_vn, one_vn], quotient_minus_one_vn)
    four_vn = _FakeVarnode("four", size=4, expr=Expression.constant(4, size=4))
    rounded_vn = _FakeVarnode("rounded_preadvanced", size=4)
    mul_op = _FakePcodeOp("INT_MULT", [quotient_minus_one_vn, four_vn], rounded_vn)
    summarizer = StructuralRecurrenceSummarizer(_FakeTracer("unused", _const(0)), debug=False)

    assert summarizer._readonly_round_down_candidates(
        [sub_op, right_op, minus_one_op, mul_op],
        {"name": "param_2", "index": 1, "data_type": "int", "size": 4},
    ) == [ReadonlyRoundedCountCandidate(rounded_vn, 4, 3, 4, peeled_vn)]

def test_round_down_candidate_accepts_shift_pair_form():
    count_expr = Expression.parameter("param_2", index=1, data_type="int", size=4)
    count_vn = _FakeVarnode("param_2", size=4, expr=count_expr)
    three_vn = _FakeVarnode("three", size=4, expr=Expression.constant(3, size=4))
    peeled_vn = _FakeVarnode(
        "peeled_count",
        size=4,
        expr=Expression.binary_op("INT_SUB", count_expr, Expression.constant(3, size=4)),
    )
    sub_op = _FakePcodeOp("INT_SUB", [count_vn, three_vn], peeled_vn)
    shift_vn = _FakeVarnode("shift", size=4, expr=Expression.constant(2, size=4))
    quotient_vn = _FakeVarnode("quotient", size=4)
    right_op = _FakePcodeOp("INT_RIGHT", [peeled_vn, shift_vn], quotient_vn)
    rounded_vn = _FakeVarnode("rounded", size=4)
    left_op = _FakePcodeOp("INT_LEFT", [quotient_vn, shift_vn], rounded_vn)
    summarizer = StructuralRecurrenceSummarizer(_FakeTracer("unused", _const(0)), debug=False)

    assert summarizer._readonly_round_down_candidates(
        [sub_op, right_op, left_op],
        {"name": "param_2", "index": 1, "data_type": "int", "size": 4},
    ) == [ReadonlyRoundedCountCandidate(rounded_vn, 4, 3)]

def test_tail_start_from_peeled_rounded_count_accepts_object_offset():
    pointer_expr = Expression.parameter("param_1", index=0, data_type="int *", size=8)
    pointer_vn = _FakeVarnode("param_1", size=8, expr=pointer_expr)
    rounded_vn = _FakeVarnode("rounded", size=8)
    four_vn = _FakeVarnode("four", size=8, expr=Expression.constant(4, size=8))
    tail_start_vn = _FakeVarnode("tail_start", size=8)
    tail_start_op = _FakePcodeOp("PTRADD", [pointer_vn, rounded_vn, four_vn], tail_start_vn)
    twelve_vn = _FakeVarnode("twelve", size=8, expr=Expression.constant(12, size=8))
    peeled_tail_start_vn = _FakeVarnode("peeled_tail_start", size=8)
    add_op = _FakePcodeOp("INT_ADD", [tail_start_vn, twelve_vn], peeled_tail_start_vn)
    summarizer = StructuralRecurrenceSummarizer(_FakeTracer("unused", _const(0)), debug=False)

    assert summarizer._tail_start_varnodes_from_rounded_count(
        [tail_start_op, add_op],
        {"name": "param_1", "index": 0, "data_type": "int *", "size": 8},
        rounded_vn,
        element_size=4,
        start_offset=12,
    ) == (peeled_tail_start_vn,)

def test_tail_start_from_peeled_rounded_count_accepts_scaled_low_bit_or_offset():
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
    two_vn = _FakeVarnode("two", size=8, expr=Expression.constant(2, size=8))
    scaled_vn = _FakeVarnode("scaled", size=8)
    scale_op = _FakePcodeOp("INT_LEFT", [rounded_or_three, two_vn], scaled_vn)
    tail_start_vn = _FakeVarnode("tail_start", size=8)
    tail_start_op = _FakePcodeOp("INT_ADD", [pointer_vn, scaled_vn], tail_start_vn)
    summarizer = StructuralRecurrenceSummarizer(_FakeTracer("unused", _const(0)), debug=False)

    assert summarizer._tail_start_varnodes_from_rounded_count(
        [peeled_op, rounded_op, or_op, scale_op, tail_start_op],
        {"name": "param_1", "index": 0, "data_type": "int *", "size": 8},
        rounded_vn,
        element_size=4,
        start_offset=12,
    ) == (tail_start_vn,)

def test_rounded_count_source_accepts_large_peel_offsets():
    count_expr = Expression.parameter("param_2", index=1, data_type="int", size=4)
    count_vn = _FakeVarnode("param_2", size=8, expr=count_expr)
    large_peeled = 257
    peeled_sub_vn = _FakeVarnode("peeled", size=8)
    peeled_sub_op = _FakePcodeOp(
        "INT_SUB",
        [count_vn, _FakeVarnode("large_const", size=8, expr=Expression.constant(large_peeled, size=8))],
        peeled_sub_vn,
    )
    large_added = -257
    peeled_add_vn = _FakeVarnode("peeled_add", size=8)
    peeled_add_op = _FakePcodeOp(
        "INT_ADD",
        [count_vn, _FakeVarnode("large_neg", size=8, expr=Expression.constant(large_added, size=8))],
        peeled_add_vn,
    )
    summarizer = StructuralRecurrenceSummarizer(_FakeTracer("unused", _const(0)), debug=False)

    assert summarizer._rounded_count_source(
        peeled_sub_vn,
        {"name": "param_2", "index": 1, "data_type": "int", "size": 4},
    ) == (count_vn, large_peeled)
    assert summarizer._rounded_count_source(
        peeled_add_vn,
        {"name": "param_2", "index": 1, "data_type": "int", "size": 4},
    ) == (count_vn, abs(large_added))

def test_varnode_is_base_plus_scaled_counter_rejects_unlinked_tail_start_constant():
    pointer_expr = Expression.parameter("param_1", index=0, data_type="int *", size=8)
    pointer_vn = _FakeVarnode("param_1", size=8, expr=pointer_expr)
    rounded_vn = _FakeVarnode("rounded", size=8)
    three_vn = _FakeVarnode("three", size=8, expr=Expression.constant(3, size=8))
    four_vn = _FakeVarnode("four", size=8, expr=Expression.constant(4, size=8))
    tail_start_vn = _FakeVarnode("tail_start", size=8)
    _FakePcodeOp("PTRADD", [pointer_vn, three_vn, four_vn], tail_start_vn)
    summarizer = StructuralRecurrenceSummarizer(_FakeTracer("unused", _const(0)), debug=False)

    assert summarizer._varnode_is_base_plus_scaled_counter(
        tail_start_vn,
        {"name": "param_1", "index": 0, "data_type": "int *", "size": 8},
        rounded_vn,
        element_size=4,
        byte_offset=12,
    ) is False

def test_counter_low_bits_clear_allows_large_or_delta_without_heuristic_cap():
    count_expr = Expression.parameter("param_2", index=1, data_type="int", size=4)
    count_vn = _FakeVarnode("param_2", size=8, expr=count_expr)
    clear_bit = 1 << 8
    mask_value = (1 << 64) - 1 - clear_bit
    and_op = _FakePcodeOp(
        "INT_AND",
        [count_vn, _FakeVarnode("mask", size=8, expr=Expression.constant(mask_value, size=8))],
        _FakeVarnode("rounded", size=8),
    )
    rounded_vn = and_op.getOutput()
    summarizer = StructuralRecurrenceSummarizer(_FakeTracer("unused", _const(0)), debug=False)

    assert summarizer._counter_low_bits_clear_for_or_delta(rounded_vn, 256) is True

def test_counter_low_bits_clear_rejects_high_bit_or_delta_with_zext_counter():
    count_expr = Expression.parameter("param_2", index=1, data_type="int", size=4)
    count_vn = _FakeVarnode("param_2", size=4, expr=count_expr)
    zext_vn = _FakeVarnode("param_2_zext", size=8, expr=Expression.unary_op("INT_ZEXT", count_expr))
    zext_op = _FakePcodeOp("INT_ZEXT", [count_vn], zext_vn)
    clear_bit = 1 << 40
    mask_value = (1 << 64) - 1 - (clear_bit)
    mask_vn = _FakeVarnode("mask", size=8, expr=Expression.constant(mask_value, size=8))
    and_vn = _FakeVarnode("rounded", size=8)
    _FakePcodeOp("INT_AND", [zext_vn, mask_vn], and_vn)
    summarizer = StructuralRecurrenceSummarizer(_FakeTracer("unused", _const(0)), debug=False)

    assert summarizer._counter_low_bits_clear_for_or_delta(and_vn, clear_bit) is False

def test_structural_recurrence_summarizer_merges_exact_and_synthesized_semantic_witnesses():
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
                value=_mem("param_1", 0),
                conditions=[
                    _cond(
                        "INT_NOTEQUAL",
                        Expression.parameter("param_1", index=0, data_type="int *", size=8),
                        Expression.constant(0, size=8),
                    ),
                    _cond("INT_EQUAL", _param("param_2"), _const(1)),
                ],
            ),
            ReturnInfo(
                address="0x100C",
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
    assert [w.exact_count for w in positive_case.value.runtime_ref.semantic_witnesses] == [1, 2, 3, 4]

def test_structural_recurrence_prefers_local_signed_counter_evidence_over_declared_unsigned():
    summarizer = StructuralRecurrenceSummarizer(tracer=None, debug=False)
    analysis = FunctionReturnAnalysis(
        function_name="readonly_signed_counter_like",
        entry_point="0x1000",
        parameters=[
            {"name": "param_1", "index": 0, "data_type": "int *", "size": 8, "is_signed": False},
            {"name": "param_2", "index": 1, "data_type": "uint", "size": 4, "is_signed": False},
        ],
        returns=[
            ReturnInfo(
                address="0x1000",
                conditions=[_cond("INT_SLESS", _const(0), _param("param_2"))],
                value=_const(1),
            )
        ],
    )
    count_param = analysis.parameters[1]

    assert summarizer._readonly_reduction_counter_is_signed(analysis.returns, count_param) is True
    assert (
        summarizer._readonly_reduction_count_compare_op(
            count_param,
            signed_counter=True,
            inclusive=True,
        )
        == "INT_SLESSEQUAL"
    )

def test_structural_recurrence_counter_signedness_uses_only_relevant_returns():
    summarizer = StructuralRecurrenceSummarizer(tracer=None, debug=False)
    count_param = {"name": "param_2", "index": 1, "data_type": "uint", "size": 4, "is_signed": False}
    unrelated_signed = ReturnInfo(
        address="0x1000",
        conditions=[_cond("INT_SLESS", _const(0), _param("param_2"))],
        value=_const(1),
    )
    relevant_unsigned = ReturnInfo(
        address="0x1001",
        conditions=[_cond("INT_LESS", _const(3), _param("param_2"))],
        value=_const(2),
    )

    assert (
        summarizer._readonly_reduction_counter_is_signed(
            [unrelated_signed, relevant_unsigned],
            count_param,
        )
        is None
    )
    assert (
        summarizer._readonly_reduction_counter_is_signed(
            [relevant_unsigned],
            count_param,
        )
        is False
    )

def test_structural_recurrence_region_returns_require_per_return_signedness_evidence():
    summarizer = StructuralRecurrenceSummarizer(tracer=None, debug=False)
    count_param = {"name": "param_2", "index": 1, "data_type": "uint", "size": 4, "is_signed": False}
    analysis = FunctionReturnAnalysis(
        function_name="readonly_region_filter_like",
        entry_point="0x1000",
        parameters=[
            {"name": "param_1", "index": 0, "data_type": "int *", "size": 8, "is_signed": False},
            count_param,
        ],
        returns=[
            ReturnInfo(
                address="0x1000",
                conditions=[
                    _cond("INT_NOTEQUAL", _param("param_1", size=8), _const(0, size=8)),
                    _cond("INT_LESS", _const(0), _param("param_2")),
                ],
                value=_const(1),
            ),
            ReturnInfo(
                address="0x1001",
                conditions=[
                    _cond("INT_NOTEQUAL", _param("param_1", size=8), _const(0, size=8)),
                ],
                value=_const(2),
            ),
        ],
    )
    positive_conditions = [
        _cond("INT_NOTEQUAL", _param("param_1", size=8), _const(0, size=8)),
        _cond("INT_LESS", _const(0), _param("param_2")),
    ]

    relevant = summarizer._readonly_reduction_region_returns_with_signedness(
        analysis,
        count_param,
        positive_conditions,
        expected_signed=False,
    )

    assert [ret.address for ret in relevant] == ["0x1000"]
