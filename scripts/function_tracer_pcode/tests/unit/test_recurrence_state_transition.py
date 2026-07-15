from scripts.function_tracer_pcode.tests.unit._recurrence_fixtures import *
from scripts.function_tracer_pcode.analysis.recurrence import state_transition_1
from scripts.function_tracer_pcode.analysis.recurrence.models import StateTransitionLoopModel


def test_small_modulus_state_transition_lowers_bitand_delta_to_residue_summary():
    summarizer = StructuralRecurrenceSummarizer(_FakeTracer("unused", _const(0)), debug=False)
    state = Expression.variable("__loop_state", size=4)
    accumulator = Expression.variable("__loop_acc", size=4)
    model = StateTransitionLoopModel(
        None, None, None, None, None, _const(0), state,
        Expression.binary_op("INT_SLESS", state, _param()),
        Expression.binary_op("INT_ADD", state, _const(1)),
        None, None, _const(0),
        Expression.binary_op(
            "INT_ADD", Expression.binary_op("INT_AND", state, _const(1)), _const(1)
        ),
        accumulator, True, (),
    )
    value = state_transition_1._build_small_residue_state_transition_value(
        summarizer,
        model=model,
        side_effect_profile=LoopSideEffectProfileRef(),
        result_size=4,
    )
    assert value is not None
    assert tuple(value.runtime_ref.residue_cases) == (
        (2, 0, 0, 1),
        (2, 1, 0, 2),
    )


def test_small_modulus_state_transition_rejects_modulus_eight():
    summarizer = StructuralRecurrenceSummarizer(_FakeTracer("unused", _const(0)), debug=False)
    state = Expression.variable("__loop_state", size=4)
    model = StateTransitionLoopModel(
        None, None, None, None, None, _const(0), state,
        Expression.binary_op("INT_SLESS", state, _param()),
        Expression.binary_op("INT_ADD", state, _const(1)),
        None, None, _const(0), Expression.binary_op("INT_AND", state, _const(7)),
        Expression.variable("__loop_acc", size=4), True, (),
    )
    assert state_transition_1._build_small_residue_state_transition_value(
        summarizer,
        model=model,
        side_effect_profile=LoopSideEffectProfileRef(),
        result_size=4,
    ) is None

def test_state_transition_runtime_ref_supplies_summary_transition_evidence():
    state = Expression.variable("__loop_state", size=4)
    transition = Expression.binary_op("INT_SUB", state, _const(1))
    transition.size = 4
    accumulator_init = _const(0)
    accumulator_delta = _const(1)
    runtime_ref = StateTransitionLoopSummaryRef(
        state_guard=Expression.binary_op("INT_SLESS", _const(0), state),
        transition_expr=transition,
        accumulator_init=accumulator_init,
        accumulator_delta=accumulator_delta,
        transition_cases=(((), transition),),
        side_effect_profile=LoopSideEffectProfileRef(),
        state_size=4,
        result_size=4,
    )
    value = Expression.intrinsic(
        "STATE_TRANSITION_LOOP_COUNT",
        [state],
        size=4,
        runtime_ref=runtime_ref,
        opcode=STATE_TRANSITION_LOOP_COUNT_OPCODE,
    )
    ret = ReturnInfo(
        address="0x2000",
        value=value,
        conditions=[_cond("INT_SLESS", _const(0), _param())],
        return_kind="summary_derived",
    )
    analysis = FunctionReturnAnalysis(
        function_name="state_loop",
        entry_point="0x1000",
        parameters=[{"name": "param_1", "index": 0, "type": "int", "size": 4}],
        returns=[ReturnInfo(address="0x1000", value=_const(0), conditions=[])],
        return_type="int",
    )

    evidence = _summary_transition_evidence_key(ret)

    assert evidence is not None
    assert evidence[0] == "state_transition_loop_evidence"
    assert _transition_evidence_has_required_parts(
        evidence,
        analysis,
        enable_completed_recovery_proofs=True,
    )

def test_state_transition_evidence_allows_uniform_transition_cases():
    state = Expression.variable("__loop_state", size=4)
    transition = Expression.binary_op("INT_SUB", state, _const(1))
    transition.size = 4
    runtime_ref = StateTransitionLoopSummaryRef(
        state_guard=Expression.binary_op("INT_SLESS", _const(0), state),
        transition_expr=transition,
        accumulator_init=_const(0),
        accumulator_delta=_const(1),
        transition_cases=(),
        side_effect_profile=LoopSideEffectProfileRef(),
        state_size=4,
        result_size=4,
    )
    summarizer = StructuralRecurrenceSummarizer(PcodeTracer.__new__(PcodeTracer), debug=False)

    evidence = summarizer._state_transition_loop_transition_evidence_key(runtime_ref)

    assert evidence is not None
    assert (
        "transition_cases_key",
        ("transition_cases", "uniform_transition_expr", ("expression", transition.structural_key())),
    ) in evidence

def test_state_transition_loop_summary_recovers_branch_driven_trip_count():
    analysis = create_mock_analysis(
        "branch_while_state",
        return_type="int",
        parameters=[{"name": "param_1", "index": 0, "data_type": "int", "size": 4, "is_signed": True}],
        returns=[
            ReturnInfo(address="0x1000", value=_const(0), conditions=[]),
            ReturnInfo(
                address="0x1004",
                value=Expression.binary_op("INT_ADD", Expression.unknown("phi_circular"), _const(1)),
                conditions=[_cond("INT_SLESS", _const(0), _param("param_1"))],
            ),
        ],
    )

    summarizer = StructuralRecurrenceSummarizer(_FakeTracer("unused", _const(0)), debug=False)
    summary = summarizer.try_summarize_function(
        _FakeFunction("branch_while_state"),
        _build_branch_while_state_cfg(),
        analysis,
    )

    assert summary is not None
    summarized_returns, note = summary
    assert note == "state_transition_loop_summary"
    assert len(summarized_returns) == 2
    assert all(expression_has_unresolved_value(ret.value) is False for ret in summarized_returns)

    loop_case = next(ret for ret in summarized_returns if ret.value.expr_type == ExpressionType.INTRINSIC)
    assert loop_case.value.opcode == STATE_TRANSITION_LOOP_COUNT_OPCODE
    assert isinstance(loop_case.value.runtime_ref, StateTransitionLoopSummaryRef)
    loop_smt = expression_to_smt(loop_case.value)
    assert "rt_state_transition_loop_count_" in loop_smt
    assert "rtunk_" not in loop_smt

def test_state_transition_loop_summary_preserves_nonzero_accumulator_seed():
    analysis = create_mock_analysis(
        "branch_while_state_seeded",
        return_type="int",
        parameters=[{"name": "param_1", "index": 0, "data_type": "int", "size": 4, "is_signed": True}],
        returns=[
            ReturnInfo(address="0x1000", value=_const(5), conditions=[]),
            ReturnInfo(
                address="0x1004",
                value=Expression.binary_op("INT_ADD", _const(5), Expression.unknown("phi_circular")),
                conditions=[_cond("INT_SLESS", _const(0), _param("param_1"))],
            ),
        ],
    )

    summarizer = StructuralRecurrenceSummarizer(_FakeTracer("unused", _const(0)), debug=False)
    summary = summarizer.try_summarize_function(
        _FakeFunction("branch_while_state_seeded"),
        _build_branch_while_state_cfg(accumulator_init_expr=_const(5)),
        analysis,
    )

    assert summary is not None
    summarized_returns, note = summary
    assert note == "state_transition_loop_summary"
    base_case = next(ret for ret in summarized_returns if ret.conditions[0].negated is True)
    positive_case = next(ret for ret in summarized_returns if ret.conditions[0].negated is False)
    assert base_case.value.structural_key() == _const(5).structural_key()
    assert expression_has_unresolved_value(positive_case.value) is False
    positive_smt = expression_to_smt(positive_case.value)
    assert "rt_state_transition_loop_count_" in positive_smt
    assert "(bvadd (_ bv5 32)" in positive_smt

def test_state_transition_loop_summary_recovers_latch_guarded_state_loop():
    analysis = create_mock_analysis(
        "branch_while_state",
        return_type="int",
        parameters=[{"name": "param_1", "index": 0, "data_type": "int", "size": 4, "is_signed": True}],
        returns=[
            ReturnInfo(address="0x1000", value=_const(0), conditions=[]),
            ReturnInfo(address="0x1004", value=_const(1), conditions=[_cond("INT_SLESS", _const(0), _param("param_1"))]),
        ],
    )

    summarizer = StructuralRecurrenceSummarizer(_FakeTracer("unused", _const(0)), debug=False)
    summary = summarizer.try_summarize_function(
        _FakeFunction("branch_while_state"),
        _build_branch_while_state_latch_guarded_cfg(),
        analysis,
    )

    assert summary is not None
    summarized_returns, note = summary
    assert note == "state_transition_loop_summary"
    loop_case = next(ret for ret in summarized_returns if ret.value.expr_type == ExpressionType.INTRINSIC)
    assert loop_case.conditions[0].to_string() == "(0 < param_1)"
    assert loop_case.value.runtime_ref.semantic_key() is not None

def test_state_transition_loop_summary_recovers_state_affine_accumulator_sum():
    analysis = create_mock_analysis(
        "decrement_sum_state",
        return_type="int",
        parameters=[{"name": "param_1", "index": 0, "data_type": "int", "size": 4, "is_signed": True}],
        returns=[
            ReturnInfo(address="0x1000", value=_const(0), conditions=[]),
            ReturnInfo(address="0x1004", value=Expression.unknown("phi_circular"), conditions=[]),
        ],
    )

    summarizer = StructuralRecurrenceSummarizer(_FakeTracer("unused", _const(0)), debug=False)
    summary = summarizer._try_summarize_state_transition_loop(
        _FakeFunction("decrement_sum_state"),
        _build_decrement_accumulator_sum_cfg(),
        analysis,
    )

    assert summary is not None
    summarized_returns, note = summary
    assert note == "state_transition_loop_summary"
    positive_case = next(ret for ret in summarized_returns if ret.conditions[0].negated is False)
    assert positive_case.conditions[0].to_string() == "(0 < param_1)"
    assert expression_has_unresolved_value(positive_case.value) is False
    assert positive_case.value.expr_type != ExpressionType.INTRINSIC
    positive_smt = expression_to_smt(positive_case.value)
    assert "rt_state_transition_loop_count_" not in positive_smt
    assert "zero_extend" in positive_smt
    assert "(bvmul ((_ zero_extend" in positive_smt
    assert "extract 31 0" in positive_smt

def test_state_transition_loop_summary_recovers_progress_guarded_unit_step():
    analysis = create_mock_analysis(
        "progress_guarded_state",
        return_type="int",
        parameters=[
            {"name": "param_1", "index": 0, "data_type": "int", "size": 4, "is_signed": True},
            {"name": "param_2", "index": 1, "data_type": "int", "size": 4, "is_signed": True},
        ],
        returns=[
            ReturnInfo(address="0x1000", value=_const(0), conditions=[_cond("INT_SLESSEQUAL", _param("param_2"), _const(0))]),
            ReturnInfo(
                address="0x1004",
                value=Expression.binary_op("INT_ADD", Expression.unknown("phi_circular"), _const(1)),
                conditions=[
                    _cond("INT_SLESS", _const(0), _param("param_2")),
                    _cond("INT_SLESS", _const(0), _param("param_1")),
                ],
            ),
        ],
    )

    summarizer = StructuralRecurrenceSummarizer(_FakeTracer("unused", _const(0)), debug=False)
    summary = summarizer._try_summarize_state_transition_loop(
        _FakeFunction("progress_guarded_state"),
        _build_progress_guarded_unit_state_transition_cfg(),
        analysis,
    )

    assert summary is not None
    summarized_returns, note = summary
    assert note == "state_transition_loop_summary"
    assert len(summarized_returns) == 2
    positive_case = next(ret for ret in summarized_returns if ret.branch_index == 10_200)
    assert [condition.to_string() for condition in positive_case.conditions] == [
        "(0 < param_2)",
        "(0 < param_1)",
    ]
    assert positive_case.value.structural_key() == _param("param_2").structural_key()
    assert expression_has_unresolved_value(positive_case.value) is False
    positive_smt = expression_to_smt(positive_case.value)
    assert "rt_state_transition_loop_count_" not in positive_smt
    assert "rtunk_" not in positive_smt

def test_state_transition_loop_summary_recovers_latch_progress_guarded_unit_step_with_anchor():
    c_minus_one = Expression.binary_op("INT_SUB", _param("param_2"), _const(1))
    analysis = create_mock_analysis(
        "latch_progress_guarded_state",
        return_type="int",
        parameters=[
            {"name": "param_1", "index": 0, "data_type": "int", "size": 4, "is_signed": True},
            {"name": "param_2", "index": 1, "data_type": "int", "size": 4, "is_signed": True},
        ],
        returns=[
            ReturnInfo(address="0x1000", value=_const(0), conditions=[_cond("INT_SLESSEQUAL", _param("param_2"), _const(0))]),
            ReturnInfo(
                address="0x1004",
                value=_const(1),
                conditions=[
                    _cond("INT_SLESS", _const(0), _param("param_2")),
                    _cond("INT_SLESS", _const(0), _param("param_1")),
                    Condition(Expression.binary_op("INT_SLESS", _const(0), c_minus_one), True),
                ],
            ),
        ],
    )

    summarizer = StructuralRecurrenceSummarizer(_FakeTracer("unused", _const(0)), debug=False)
    summary = summarizer._try_summarize_state_transition_loop(
        _FakeFunction("latch_progress_guarded_state"),
        _build_latch_progress_guarded_unit_state_transition_cfg(),
        analysis,
    )

    assert summary is not None
    summarized_returns, note = summary
    assert note == "state_transition_loop_summary"
    positive_case = next(ret for ret in summarized_returns if ret.branch_index == 10_200)
    assert [condition.to_string() for condition in positive_case.conditions] == [
        "(0 < param_2)",
        "(0 < param_1)",
    ]
    assert positive_case.value.structural_key() == _param("param_2").structural_key()

def test_state_loop_accumulator_delta_accepts_left_shift_transition():
    summarizer = StructuralRecurrenceSummarizer(_FakeTracer("unused", _const(0)), debug=False)
    accumulator = Expression.variable("__state", size=4)
    shifted = Expression.binary_op("INT_LEFT", accumulator, _const(1))
    shifted.size = 4

    deltas = summarizer._extract_delta_from_possible_phi(
        shifted,
        accumulator,
        parameters=[],
    )

    assert len(deltas) == 1
    assert deltas[0].structural_key() == shifted.structural_key()

def test_multiplicative_state_transition_start_requires_proved_zero_stop():
    summarizer = StructuralRecurrenceSummarizer(_FakeTracer("unused", _const(0)), debug=False)
    state = Expression.variable("__loop_state", size=4)
    zero_stop_guard = Expression.binary_op("INT_NOTEQUAL", state, _const(0))
    zero_stop_guard.size = 1
    nonzero_stop_guard = Expression.binary_op(
        "INT_NOTEQUAL",
        Expression.binary_op("INT_ADD", state, Expression.constant(0xFFFFFFFF, size=4)),
        _const(0),
    )
    nonzero_stop_guard.size = 1
    greater_than_one_guard = Expression.binary_op("INT_SLESS", _const(1), state)
    greater_than_one_guard.size = 1
    compound_stricter_guard = Expression.binary_op(
        "BOOL_AND",
        zero_stop_guard,
        greater_than_one_guard,
    )
    compound_stricter_guard.size = 1
    state_not_one_guard = Expression.binary_op("INT_NOTEQUAL", state, _const(1))
    state_not_one_guard.size = 1
    compound_nonzero_stop_guard = Expression.binary_op(
        "BOOL_AND",
        zero_stop_guard,
        state_not_one_guard,
    )
    compound_nonzero_stop_guard.size = 1

    start = summarizer._state_transition_iteration_start_expr(
        zero_stop_guard,
        state,
        size=4,
    )

    assert start is not None
    assert start.structural_key() == _const(0).structural_key()
    assert summarizer._state_transition_iteration_start_expr(
        nonzero_stop_guard,
        state,
        size=4,
    ) is None
    assert summarizer._state_transition_iteration_start_expr(
        greater_than_one_guard,
        state,
        size=4,
    ) is None
    assert summarizer._state_transition_iteration_start_expr(
        compound_stricter_guard,
        state,
        size=4,
    ) is None
    assert summarizer._state_transition_iteration_start_expr(
        compound_nonzero_stop_guard,
        state,
        size=4,
    ) is None

def test_multiplicative_state_transition_start_accepts_one_stop_with_exact_anchor():
    summarizer = StructuralRecurrenceSummarizer(_FakeTracer("unused", _const(0)), debug=False)
    state = Expression.variable("__loop_state", size=4)
    n = _param("param_1")
    guard = Expression.binary_op(
        "INT_NOTEQUAL",
        state,
        _const(1),
    )
    guard.size = 1
    model = StateTransitionLoopModel(
        header_block=None,
        body_block=None,
        exit_block=None,
        state_phi_op=None,
        state_phi_output=None,
        state_init_expr=n,
        state_placeholder=state,
        state_guard_expr=guard,
        state_transition_expr=Expression.binary_op("INT_ADD", state, Expression.constant(0xFFFFFFFF, size=4)),
        accumulator_phi_op=None,
        accumulator_phi_output=None,
        accumulator_init_expr=_const(1),
        accumulator_delta_expr=Expression.binary_op(
            "INT_LEFT",
            Expression.variable("__loop_acc", size=4),
            _const(1),
        ),
        accumulator_placeholder=Expression.variable("__loop_acc", size=4),
        continue_on_true=True,
        loop_blocks=(),
    )
    analysis = create_mock_analysis(
        "multiplicative_state_transition",
        parameters=[{"name": "param_1", "index": 0, "data_type": "int", "size": 4, "is_signed": True}],
        returns=[
            ReturnInfo(
                address="0x1000",
                value=_const(1),
                conditions=[_cond("INT_EQUAL", Expression.binary_op("INT_ADD", n, Expression.constant(0xFFFFFFFF, size=4)), _const(0))],
            ),
        ],
    )

    start = summarizer._multiplicative_state_transition_iteration_start_expr(
        model=model,
        analysis=analysis,
        result_size=4,
        size=4,
    )

    assert start is not None
    assert start.structural_key() == _const(1).structural_key()

def test_multiplicative_state_transition_start_rejects_one_stop_without_exact_anchor():
    summarizer = StructuralRecurrenceSummarizer(_FakeTracer("unused", _const(0)), debug=False)
    state = Expression.variable("__loop_state", size=4)
    n = _param("param_1")
    guard = Expression.binary_op(
        "INT_NOTEQUAL",
        state,
        _const(1),
    )
    guard.size = 1
    model = StateTransitionLoopModel(
        header_block=None,
        body_block=None,
        exit_block=None,
        state_phi_op=None,
        state_phi_output=None,
        state_init_expr=n,
        state_placeholder=state,
        state_guard_expr=guard,
        state_transition_expr=Expression.binary_op("INT_ADD", state, Expression.constant(0xFFFFFFFF, size=4)),
        accumulator_phi_op=None,
        accumulator_phi_output=None,
        accumulator_init_expr=_const(1),
        accumulator_delta_expr=Expression.binary_op(
            "INT_LEFT",
            Expression.variable("__loop_acc", size=4),
            _const(1),
        ),
        accumulator_placeholder=Expression.variable("__loop_acc", size=4),
        continue_on_true=True,
        loop_blocks=(),
    )
    missing_anchor = create_mock_analysis(
        "multiplicative_state_transition",
        parameters=[{"name": "param_1", "index": 0, "data_type": "int", "size": 4, "is_signed": True}],
        returns=[],
    )
    wrong_value_anchor = create_mock_analysis(
        "multiplicative_state_transition",
        parameters=[{"name": "param_1", "index": 0, "data_type": "int", "size": 4, "is_signed": True}],
        returns=[
            ReturnInfo(
                address="0x1000",
                value=_const(2),
                conditions=[_cond("INT_EQUAL", Expression.binary_op("INT_ADD", n, Expression.constant(0xFFFFFFFF, size=4)), _const(0))],
            ),
        ],
    )

    assert summarizer._multiplicative_state_transition_iteration_start_expr(
        model=model,
        analysis=missing_anchor,
        result_size=4,
        size=4,
    ) is None
    assert summarizer._multiplicative_state_transition_iteration_start_expr(
        model=model,
        analysis=wrong_value_anchor,
        result_size=4,
        size=4,
    ) is None

def test_multiplicative_state_transition_start_rejects_partial_one_anchor():
    summarizer = StructuralRecurrenceSummarizer(_FakeTracer("unused", _const(0)), debug=False)
    state = Expression.variable("__loop_state", size=4)
    n = _param("param_1")
    flag = _param("param_2")
    guard = Expression.binary_op(
        "INT_NOTEQUAL",
        Expression.binary_op("INT_ADD", state, Expression.constant(0xFFFFFFFF, size=4)),
        _const(0),
    )
    guard.size = 1
    model = StateTransitionLoopModel(
        header_block=None,
        body_block=None,
        exit_block=None,
        state_phi_op=None,
        state_phi_output=None,
        state_init_expr=n,
        state_placeholder=state,
        state_guard_expr=guard,
        state_transition_expr=Expression.binary_op("INT_ADD", state, Expression.constant(0xFFFFFFFF, size=4)),
        accumulator_phi_op=None,
        accumulator_phi_output=None,
        accumulator_init_expr=_const(1),
        accumulator_delta_expr=Expression.binary_op(
            "INT_LEFT",
            Expression.variable("__loop_acc", size=4),
            _const(1),
        ),
        accumulator_placeholder=Expression.variable("__loop_acc", size=4),
        continue_on_true=True,
        loop_blocks=(),
    )
    partial_anchor = create_mock_analysis(
        "multiplicative_state_transition",
        parameters=[
            {"name": "param_1", "index": 0, "data_type": "int", "size": 4, "is_signed": True},
            {"name": "param_2", "index": 1, "data_type": "int", "size": 4, "is_signed": True},
        ],
        returns=[
            ReturnInfo(
                address="0x1000",
                value=_const(1),
                conditions=[
                    _cond("INT_EQUAL", n, _const(1)),
                    _cond("INT_SLESS", _const(0), flag),
                ],
            ),
        ],
    )

    assert summarizer._multiplicative_state_transition_iteration_start_expr(
        model=model,
        analysis=partial_anchor,
        result_size=4,
        size=4,
    ) is None

def test_multiplicative_state_transition_start_rejects_contradictory_one_anchor():
    summarizer = StructuralRecurrenceSummarizer(_FakeTracer("unused", _const(0)), debug=False)
    state = Expression.variable("__loop_state", size=4)
    n = _param("param_1")
    flag = _param("param_2")
    guard = Expression.binary_op(
        "INT_NOTEQUAL",
        Expression.binary_op("INT_ADD", state, Expression.constant(0xFFFFFFFF, size=4)),
        _const(0),
    )
    guard.size = 1
    model = StateTransitionLoopModel(
        header_block=None,
        body_block=None,
        exit_block=None,
        state_phi_op=None,
        state_phi_output=None,
        state_init_expr=n,
        state_placeholder=state,
        state_guard_expr=guard,
        state_transition_expr=Expression.binary_op("INT_ADD", state, Expression.constant(0xFFFFFFFF, size=4)),
        accumulator_phi_op=None,
        accumulator_phi_output=None,
        accumulator_init_expr=_const(1),
        accumulator_delta_expr=Expression.binary_op(
            "INT_LEFT",
            Expression.variable("__loop_acc", size=4),
            _const(1),
        ),
        accumulator_placeholder=Expression.variable("__loop_acc", size=4),
        continue_on_true=True,
        loop_blocks=(),
    )
    contradictory_anchor = create_mock_analysis(
        "multiplicative_state_transition",
        parameters=[
            {"name": "param_1", "index": 0, "data_type": "int", "size": 4, "is_signed": True},
            {"name": "param_2", "index": 1, "data_type": "int", "size": 4, "is_signed": True},
        ],
        returns=[
            ReturnInfo(
                address="0x1000",
                value=_const(1),
                conditions=[
                    _cond("INT_EQUAL", n, _const(1)),
                    _cond("INT_SLESS", _const(0), flag),
                    _cond("INT_SLESSEQUAL", flag, _const(0)),
                ],
            ),
        ],
    )

    assert summarizer._multiplicative_state_transition_iteration_start_expr(
        model=model,
        analysis=contradictory_anchor,
        result_size=4,
        size=4,
    ) is None

def test_multiplicative_state_transition_start_rejects_phi_expansion_one_anchor():
    summarizer = StructuralRecurrenceSummarizer(_FakeTracer("unused", _const(0)), debug=False)
    state = Expression.variable("__loop_state", size=4)
    n = _param("param_1")
    guard = Expression.binary_op(
        "INT_NOTEQUAL",
        Expression.binary_op("INT_ADD", state, Expression.constant(0xFFFFFFFF, size=4)),
        _const(0),
    )
    guard.size = 1
    model = StateTransitionLoopModel(
        header_block=None,
        body_block=None,
        exit_block=None,
        state_phi_op=None,
        state_phi_output=None,
        state_init_expr=n,
        state_placeholder=state,
        state_guard_expr=guard,
        state_transition_expr=Expression.binary_op("INT_ADD", state, Expression.constant(0xFFFFFFFF, size=4)),
        accumulator_phi_op=None,
        accumulator_phi_output=None,
        accumulator_init_expr=_const(1),
        accumulator_delta_expr=Expression.binary_op(
            "INT_LEFT",
            Expression.variable("__loop_acc", size=4),
            _const(1),
        ),
        accumulator_placeholder=Expression.variable("__loop_acc", size=4),
        continue_on_true=True,
        loop_blocks=(),
    )
    phi_expansion_anchor = create_mock_analysis(
        "multiplicative_state_transition",
        parameters=[{"name": "param_1", "index": 0, "data_type": "int", "size": 4, "is_signed": True}],
        returns=[
            ReturnInfo(
                address="0x1000",
                value=_const(1),
                conditions=[_cond("INT_EQUAL", n, _const(1))],
                return_kind="phi_expansion",
            ),
        ],
    )

    assert summarizer._multiplicative_state_transition_iteration_start_expr(
        model=model,
        analysis=phi_expansion_anchor,
        result_size=4,
        size=4,
    ) is None

def test_multiplicative_state_transition_start_accepts_stable_resolved_phi_anchor():
    summarizer = StructuralRecurrenceSummarizer(_FakeTracer("unused", _const(0)), debug=False)
    state = Expression.variable("__loop_state", size=4)
    n = _param("param_1")
    guard = Expression.binary_op(
        "INT_NOTEQUAL",
        Expression.binary_op("INT_ADD", state, Expression.constant(0xFFFFFFFF, size=4)),
        _const(0),
    )
    guard.size = 1
    model = StateTransitionLoopModel(
        header_block=None,
        body_block=None,
        exit_block=None,
        state_phi_op=None,
        state_phi_output=None,
        state_init_expr=n,
        state_placeholder=state,
        state_guard_expr=guard,
        state_transition_expr=Expression.binary_op("INT_ADD", state, Expression.constant(0xFFFFFFFF, size=4)),
        accumulator_phi_op=None,
        accumulator_phi_output=None,
        accumulator_init_expr=_const(1),
        accumulator_delta_expr=Expression.binary_op(
            "INT_LEFT",
            Expression.variable("__loop_acc", size=4),
            _const(1),
        ),
        accumulator_placeholder=Expression.variable("__loop_acc", size=4),
        continue_on_true=True,
        loop_blocks=(),
    )
    stable_phi_anchor = create_mock_analysis(
        "multiplicative_state_transition",
        parameters=[{"name": "param_1", "index": 0, "data_type": "int", "size": 4, "is_signed": True}],
        returns=[
            ReturnInfo(
                address="0x1000",
                value=_const(1),
                conditions=[_cond("INT_EQUAL", n, _const(1))],
                return_kind="phi_expansion",
                pcode_identity="00100054:t22",
            ),
        ],
    )

    start = summarizer._multiplicative_state_transition_iteration_start_expr(
        model=model,
        analysis=stable_phi_anchor,
        result_size=4,
        size=4,
    )

    assert start is not None
    assert start.structural_key() == _const(1).structural_key()

def test_multiplicative_state_transition_start_rejects_model_only_zero_iteration_anchor(monkeypatch):
    summarizer = StructuralRecurrenceSummarizer(_FakeTracer("unused", _const(0)), debug=False)
    monkeypatch.setattr(summarizer, "_varnode_reaches_return", lambda _varnode: True)
    state = Expression.variable("__loop_state", size=4)
    n = _param("param_1")
    accumulator_output = object()
    guard = Expression.binary_op(
        "INT_NOTEQUAL",
        Expression.binary_op("INT_ADD", state, Expression.constant(0xFFFFFFFF, size=4)),
        _const(0),
    )
    guard.size = 1
    model = StateTransitionLoopModel(
        header_block=None,
        body_block=None,
        exit_block=None,
        state_phi_op=None,
        state_phi_output=None,
        state_init_expr=n,
        state_placeholder=state,
        state_guard_expr=guard,
        state_transition_expr=Expression.binary_op("INT_ADD", state, Expression.constant(0xFFFFFFFF, size=4)),
        accumulator_phi_op=None,
        accumulator_phi_output=accumulator_output,
        accumulator_init_expr=_const(1),
        accumulator_delta_expr=Expression.binary_op(
            "INT_LEFT",
            Expression.variable("__loop_acc", size=4),
            _const(1),
        ),
        accumulator_placeholder=Expression.variable("__loop_acc", size=4),
        continue_on_true=True,
        loop_blocks=(),
    )
    no_exact_anchor = create_mock_analysis(
        "multiplicative_state_transition",
        parameters=[{"name": "param_1", "index": 0, "data_type": "int", "size": 4, "is_signed": True}],
        returns=[],
    )

    assert summarizer._multiplicative_state_transition_iteration_start_expr(
        model=model,
        analysis=no_exact_anchor,
        result_size=4,
        size=4,
    ) is None

def test_multiplicative_state_transition_start_accepts_object_zero_iteration_anchor():
    summarizer = StructuralRecurrenceSummarizer(_FakeTracer("unused", _const(1)), debug=False)
    state = Expression.variable("__loop_state", size=4)
    n = _param("param_1")
    guard = Expression.binary_op(
        "INT_NOTEQUAL",
        Expression.binary_op("INT_ADD", state, Expression.constant(0xFFFFFFFF, size=4)),
        _const(0),
    )
    guard.size = 1
    cbranch = _FakeBranchOp(guard)
    header = _FakeCfgBlock(1, [cbranch])
    body = _FakeCfgBlock(2, [])
    exit_block = _FakeCfgBlock(3, [])
    header.add_edge(body, truth=True)
    header.add_edge(exit_block, truth=False)
    body.add_edge(header)

    init_vn = _FakeVarnode("acc_init", expr=_const(1))
    next_vn = _FakeVarnode("acc_next", expr=_const(2))
    acc_phi_vn = _FakeVarnode("acc_phi")
    acc_phi_op = _FakePcodeOp("MULTIEQUAL", [init_vn, next_vn], acc_phi_vn)
    return_op = _FakePcodeOp("RETURN", [_FakeVarnode("return_target"), acc_phi_vn], None)
    exit_block._ops[:] = [return_op]
    return_op.setParent(exit_block)
    model = StateTransitionLoopModel(
        header_block=header,
        body_block=body,
        exit_block=exit_block,
        state_phi_op=None,
        state_phi_output=None,
        state_init_expr=n,
        state_placeholder=state,
        state_guard_expr=guard,
        state_transition_expr=Expression.binary_op("INT_ADD", state, Expression.constant(0xFFFFFFFF, size=4)),
        accumulator_phi_op=acc_phi_op,
        accumulator_phi_output=acc_phi_vn,
        accumulator_init_expr=_const(1),
        accumulator_delta_expr=Expression.binary_op(
            "INT_LEFT",
            Expression.variable("__loop_acc", size=4),
            _const(1),
        ),
        accumulator_placeholder=Expression.variable("__loop_acc", size=4),
        continue_on_true=True,
        loop_blocks=(header, body),
        accumulator_phi_init_index=0,
        accumulator_phi_backedge_indices=(1,),
    )
    no_exact_anchor = create_mock_analysis(
        "multiplicative_state_transition",
        parameters=[{"name": "param_1", "index": 0, "data_type": "int", "size": 4, "is_signed": True}],
        returns=[],
    )
    anchor_key = summarizer._state_transition_object_zero_iteration_anchor_key(
        model=model,
        result_size=4,
    )

    start = summarizer._multiplicative_state_transition_iteration_start_expr(
        model=model,
        analysis=no_exact_anchor,
        result_size=4,
        size=4,
    )

    assert anchor_key is not None
    anchor_fields = {
        item[0]: item[1]
        for item in anchor_key[1:]
        if isinstance(item, tuple) and len(item) == 2
    }
    assert anchor_fields["exit_region_purity_policy"] == (
        "state_transition_zero_iteration_exit_region_purity",
        1,
        "reject_effect_memory_call_indirect_control_fp_unknown",
    )
    assert anchor_fields["accumulator_phi_output_key"] is not None
    assert anchor_fields["exit_region_scan_refs"]
    assert start is not None
    assert start.structural_key() == _const(1).structural_key()

def test_multiplicative_state_transition_start_rejects_object_anchor_wrong_return_operand():
    summarizer = StructuralRecurrenceSummarizer(_FakeTracer("unused", _const(1)), debug=False)
    state = Expression.variable("__loop_state", size=4)
    n = _param("param_1")
    guard = Expression.binary_op(
        "INT_NOTEQUAL",
        Expression.binary_op("INT_ADD", state, Expression.constant(0xFFFFFFFF, size=4)),
        _const(0),
    )
    guard.size = 1
    cbranch = _FakeBranchOp(guard)
    header = _FakeCfgBlock(1, [cbranch])
    body = _FakeCfgBlock(2, [])
    exit_block = _FakeCfgBlock(3, [])
    header.add_edge(body, truth=True)
    header.add_edge(exit_block, truth=False)
    body.add_edge(header)

    init_vn = _FakeVarnode("acc_init", expr=_const(1))
    wrong_vn = _FakeVarnode("wrong_return", expr=_const(2))
    next_vn = _FakeVarnode("acc_next", expr=_const(2))
    acc_phi_vn = _FakeVarnode("acc_phi")
    acc_phi_op = _FakePcodeOp("MULTIEQUAL", [init_vn, next_vn], acc_phi_vn)
    return_op = _FakePcodeOp("RETURN", [_FakeVarnode("return_target"), wrong_vn], None)
    exit_block._ops[:] = [return_op]
    return_op.setParent(exit_block)
    model = StateTransitionLoopModel(
        header_block=header,
        body_block=body,
        exit_block=exit_block,
        state_phi_op=None,
        state_phi_output=None,
        state_init_expr=n,
        state_placeholder=state,
        state_guard_expr=guard,
        state_transition_expr=Expression.binary_op("INT_ADD", state, Expression.constant(0xFFFFFFFF, size=4)),
        accumulator_phi_op=acc_phi_op,
        accumulator_phi_output=acc_phi_vn,
        accumulator_init_expr=_const(1),
        accumulator_delta_expr=Expression.binary_op(
            "INT_LEFT",
            Expression.variable("__loop_acc", size=4),
            _const(1),
        ),
        accumulator_placeholder=Expression.variable("__loop_acc", size=4),
        continue_on_true=True,
        loop_blocks=(header, body),
        accumulator_phi_init_index=0,
        accumulator_phi_backedge_indices=(1,),
    )
    no_exact_anchor = create_mock_analysis(
        "multiplicative_state_transition",
        parameters=[{"name": "param_1", "index": 0, "data_type": "int", "size": 4, "is_signed": True}],
        returns=[],
    )

    assert summarizer._multiplicative_state_transition_iteration_start_expr(
        model=model,
        analysis=no_exact_anchor,
        result_size=4,
        size=4,
    ) is None

def test_multiplicative_state_transition_start_rejects_object_anchor_exit_region_effects():
    for forbidden_mnemonic in (
        "CALL",
        "CALLIND",
        "STORE",
        "LOAD",
        "BRANCH",
        "CBRANCH",
        "BRANCHIND",
        "CALLOTHER",
        "FLOAT_ADD",
        "INT2FLOAT",
        "UNKNOWN_OP",
    ):
        summarizer = StructuralRecurrenceSummarizer(_FakeTracer("unused", _const(1)), debug=False)
        state = Expression.variable("__loop_state", size=4)
        n = _param("param_1")
        guard = Expression.binary_op(
            "INT_NOTEQUAL",
            Expression.binary_op("INT_ADD", state, Expression.constant(0xFFFFFFFF, size=4)),
            _const(0),
        )
        guard.size = 1
        cbranch = _FakeBranchOp(guard)
        header = _FakeCfgBlock(1, [cbranch])
        body = _FakeCfgBlock(2, [])
        exit_block = _FakeCfgBlock(3, [])
        header.add_edge(body, truth=True)
        header.add_edge(exit_block, truth=False)
        body.add_edge(header)

        init_vn = _FakeVarnode("acc_init", expr=_const(1))
        next_vn = _FakeVarnode("acc_next", expr=_const(2))
        acc_phi_vn = _FakeVarnode("acc_phi")
        acc_phi_op = _FakePcodeOp("MULTIEQUAL", [init_vn, next_vn], acc_phi_vn)
        forbidden_op = _FakePcodeOp(forbidden_mnemonic, [_FakeVarnode("effect_arg")], None)
        return_op = _FakePcodeOp("RETURN", [_FakeVarnode("return_target"), init_vn], None)
        exit_block._ops[:] = [forbidden_op, return_op]
        forbidden_op.setParent(exit_block)
        return_op.setParent(exit_block)
        model = StateTransitionLoopModel(
            header_block=header,
            body_block=body,
            exit_block=exit_block,
            state_phi_op=None,
            state_phi_output=None,
            state_init_expr=n,
            state_placeholder=state,
            state_guard_expr=guard,
            state_transition_expr=Expression.binary_op("INT_ADD", state, Expression.constant(0xFFFFFFFF, size=4)),
            accumulator_phi_op=acc_phi_op,
            accumulator_phi_output=acc_phi_vn,
            accumulator_init_expr=_const(1),
            accumulator_delta_expr=Expression.binary_op(
                "INT_LEFT",
                Expression.variable("__loop_acc", size=4),
                _const(1),
            ),
            accumulator_placeholder=Expression.variable("__loop_acc", size=4),
            continue_on_true=True,
            loop_blocks=(header, body),
            accumulator_phi_init_index=0,
            accumulator_phi_backedge_indices=(1,),
        )
        no_exact_anchor = create_mock_analysis(
            "multiplicative_state_transition",
            parameters=[{"name": "param_1", "index": 0, "data_type": "int", "size": 4, "is_signed": True}],
            returns=[],
        )

        assert summarizer._state_transition_object_zero_iteration_anchor_key(
            model=model,
            result_size=4,
        ) is None
        assert summarizer._multiplicative_state_transition_iteration_start_expr(
            model=model,
            analysis=no_exact_anchor,
            result_size=4,
            size=4,
        ) is None

def test_multiplicative_state_transition_start_rejects_object_anchor_unscannable_exit_block():
    summarizer = StructuralRecurrenceSummarizer(_FakeTracer("unused", _const(1)), debug=False)
    state = Expression.variable("__loop_state", size=4)
    n = _param("param_1")
    guard = Expression.binary_op(
        "INT_NOTEQUAL",
        Expression.binary_op("INT_ADD", state, Expression.constant(0xFFFFFFFF, size=4)),
        _const(0),
    )
    guard.size = 1
    cbranch = _FakeBranchOp(guard)
    header = _FakeCfgBlock(1, [cbranch])
    body = _FakeCfgBlock(2, [])
    unscannable_exit = _FakeCfgBlockWithoutIterator(3, [])
    return_block = _FakeCfgBlock(4, [])
    header.add_edge(body, truth=True)
    header.add_edge(unscannable_exit, truth=False)
    body.add_edge(header)
    unscannable_exit.add_edge(return_block)

    init_vn = _FakeVarnode("acc_init", expr=_const(1))
    next_vn = _FakeVarnode("acc_next", expr=_const(2))
    acc_phi_vn = _FakeVarnode("acc_phi")
    acc_phi_op = _FakePcodeOp("MULTIEQUAL", [init_vn, next_vn], acc_phi_vn)
    return_op = _FakePcodeOp("RETURN", [_FakeVarnode("return_target"), init_vn], None)
    return_block._ops[:] = [return_op]
    return_op.setParent(return_block)
    model = StateTransitionLoopModel(
        header_block=header,
        body_block=body,
        exit_block=unscannable_exit,
        state_phi_op=None,
        state_phi_output=None,
        state_init_expr=n,
        state_placeholder=state,
        state_guard_expr=guard,
        state_transition_expr=Expression.binary_op("INT_ADD", state, Expression.constant(0xFFFFFFFF, size=4)),
        accumulator_phi_op=acc_phi_op,
        accumulator_phi_output=acc_phi_vn,
        accumulator_init_expr=_const(1),
        accumulator_delta_expr=Expression.binary_op(
            "INT_LEFT",
            Expression.variable("__loop_acc", size=4),
            _const(1),
        ),
        accumulator_placeholder=Expression.variable("__loop_acc", size=4),
        continue_on_true=True,
        loop_blocks=(header, body),
        accumulator_phi_init_index=0,
        accumulator_phi_backedge_indices=(1,),
    )
    no_exact_anchor = create_mock_analysis(
        "multiplicative_state_transition",
        parameters=[{"name": "param_1", "index": 0, "data_type": "int", "size": 4, "is_signed": True}],
        returns=[],
    )

    assert summarizer._state_transition_object_zero_iteration_anchor_key(
        model=model,
        result_size=4,
    ) is None
    assert summarizer._multiplicative_state_transition_iteration_start_expr(
        model=model,
        analysis=no_exact_anchor,
        result_size=4,
        size=4,
    ) is None

def test_state_transition_loop_summary_recovers_latch_exit_decrement_sum_without_triangular_proof():
    state_equals_one = Expression.binary_op(
        "INT_NOTEQUAL",
        Expression.binary_op("INT_SUB", _param("param_1"), _const(1)),
        _const(0),
    )
    state_equals_one.size = 1
    analysis = create_mock_analysis(
        "latch_exit_decrement_sum",
        return_type="int",
        parameters=[{"name": "param_1", "index": 0, "data_type": "int", "size": 4, "is_signed": True}],
        returns=[
            ReturnInfo(address="0x1000", value=_const(0), conditions=[_cond("INT_SLESSEQUAL", _param("param_1"), _const(0))]),
            ReturnInfo(
                address="0x1004",
                value=Expression.binary_op("INT_ADD", _param("param_1"), _const(0)),
                conditions=[
                    _cond("INT_SLESS", _const(0), _param("param_1")),
                    Condition(state_equals_one, negated=True),
                ],
            ),
        ],
    )

    summarizer = StructuralRecurrenceSummarizer(_FakeTracer("unused", _const(0)), debug=False)
    summary = summarizer._try_summarize_state_transition_loop(
        _FakeFunction("latch_exit_decrement_sum"),
        _build_latch_exit_decrement_accumulator_sum_cfg(),
        analysis,
    )

    assert summary is not None
    summarized_returns, note = summary
    assert note == "state_transition_loop_summary"
    assert len(summarized_returns) == 2
    positive_case = next(ret for ret in summarized_returns if ret.branch_index == 10_300)
    assert positive_case.conditions[0].to_string() == "(0 < param_1)"
    assert expression_has_unresolved_value(positive_case.value) is False
    assert positive_case.value.expr_type != ExpressionType.INTRINSIC
    positive_smt = expression_to_smt(positive_case.value)
    assert "rt_state_transition_loop_count_" not in positive_smt
    assert "(bvmul (bvsub param_1 (_ bv1 32)) (bvsub param_1 (_ bv1 32)))" in positive_smt
    assert "bvlshr" in positive_smt

def test_state_transition_loop_summary_rejects_latch_exit_decrement_sum_without_one_case_witness():
    analysis = create_mock_analysis(
        "latch_exit_decrement_sum",
        return_type="int",
        parameters=[{"name": "param_1", "index": 0, "data_type": "int", "size": 4, "is_signed": True}],
        returns=[
            ReturnInfo(address="0x1000", value=_const(0), conditions=[_cond("INT_SLESSEQUAL", _param("param_1"), _const(0))]),
            ReturnInfo(
                address="0x1004",
                value=Expression.binary_op("INT_ADD", _param("param_1"), _const(0)),
                conditions=[_cond("INT_SLESS", _const(0), _param("param_1"))],
            ),
        ],
    )

    summarizer = StructuralRecurrenceSummarizer(_FakeTracer("unused", _const(0)), debug=False)

    assert summarizer._try_summarize_state_transition_loop(
        _FakeFunction("latch_exit_decrement_sum"),
        _build_latch_exit_decrement_accumulator_sum_cfg(),
        analysis,
    ) is None

def test_state_transition_loop_summary_key_is_object_centric_across_branch_order():
    analysis = create_mock_analysis(
        "branch_while_state",
        return_type="int",
        parameters=[{"name": "param_1", "index": 0, "data_type": "int", "size": 4, "is_signed": True}],
        returns=[ReturnInfo(address="0x1000", value=Expression.unknown("phi_circular"), conditions=[])],
    )
    summarizer = StructuralRecurrenceSummarizer(_FakeTracer("unused", _const(0)), debug=False)

    left_returns, _ = summarizer.try_summarize_function(
        _FakeFunction("branch_while_state"),
        _build_branch_while_state_cfg(swap_transition_inputs=False),
        analysis,
    )
    right_returns, _ = summarizer.try_summarize_function(
        _FakeFunction("branch_while_state"),
        _build_branch_while_state_cfg(swap_transition_inputs=True),
        analysis,
    )

    left_intrinsic = next(ret.value for ret in left_returns if ret.value.expr_type == ExpressionType.INTRINSIC)
    right_intrinsic = next(ret.value for ret in right_returns if ret.value.expr_type == ExpressionType.INTRINSIC)
    assert left_intrinsic.runtime_ref.semantic_key() == right_intrinsic.runtime_ref.semantic_key()

def test_state_transition_loop_summary_key_matches_header_and_latch_guards():
    analysis = create_mock_analysis(
        "branch_while_state",
        return_type="int",
        parameters=[{"name": "param_1", "index": 0, "data_type": "int", "size": 4, "is_signed": True}],
        returns=[ReturnInfo(address="0x1000", value=Expression.unknown("phi_circular"), conditions=[])],
    )
    summarizer = StructuralRecurrenceSummarizer(_FakeTracer("unused", _const(0)), debug=False)

    header_returns, _ = summarizer.try_summarize_function(
        _FakeFunction("branch_while_state"),
        _build_branch_while_state_cfg(),
        analysis,
    )
    latch_returns, _ = summarizer.try_summarize_function(
        _FakeFunction("branch_while_state"),
        _build_branch_while_state_latch_guarded_cfg(),
        analysis,
    )

    header_intrinsic = next(ret.value for ret in header_returns if ret.value.expr_type == ExpressionType.INTRINSIC)
    latch_intrinsic = next(ret.value for ret in latch_returns if ret.value.expr_type == ExpressionType.INTRINSIC)
    assert header_intrinsic.runtime_ref.semantic_key() == latch_intrinsic.runtime_ref.semantic_key()

def test_state_transition_loop_summary_key_unifies_unsigned_shift_under_positive_guard():
    analysis = create_mock_analysis(
        "branch_while_state",
        return_type="int",
        parameters=[{"name": "param_1", "index": 0, "data_type": "int", "size": 4, "is_signed": True}],
        returns=[ReturnInfo(address="0x1000", value=Expression.unknown("phi_circular"), conditions=[])],
    )
    summarizer = StructuralRecurrenceSummarizer(_FakeTracer("unused", _const(0)), debug=False)

    signed_returns, _ = summarizer.try_summarize_function(
        _FakeFunction("branch_while_state"),
        _build_branch_while_state_latch_guarded_cfg(shift_mnemonic="INT_SRIGHT"),
        analysis,
    )
    unsigned_returns, _ = summarizer.try_summarize_function(
        _FakeFunction("branch_while_state"),
        _build_branch_while_state_latch_guarded_cfg(shift_mnemonic="INT_RIGHT"),
        analysis,
    )

    signed_intrinsic = next(ret.value for ret in signed_returns if ret.value.expr_type == ExpressionType.INTRINSIC)
    unsigned_intrinsic = next(ret.value for ret in unsigned_returns if ret.value.expr_type == ExpressionType.INTRINSIC)
    assert signed_intrinsic.runtime_ref.semantic_key() == unsigned_intrinsic.runtime_ref.semantic_key()

def test_state_transition_loop_summary_cases_drop_post_state_guard():
    analysis = create_mock_analysis(
        "branch_while_state",
        return_type="int",
        parameters=[{"name": "param_1", "index": 0, "data_type": "int", "size": 4, "is_signed": True}],
        returns=[ReturnInfo(address="0x1000", value=Expression.unknown("phi_circular"), conditions=[])],
    )
    summarizer = StructuralRecurrenceSummarizer(_FakeTracer("unused", _const(0)), debug=False)
    returns, _ = summarizer.try_summarize_function(
        _FakeFunction("branch_while_state"),
        _build_branch_while_state_latch_guarded_cfg(),
        analysis,
    )

    intrinsic = next(ret.value for ret in returns if ret.value.expr_type == ExpressionType.INTRINSIC)
    cases = intrinsic.runtime_ref.transition_cases
    assert len(cases) == 2
    for condition_expr, _negated, _value in cases:
        assert condition_expr is not None
        condition_operators = _expression_operators(condition_expr)
        assert "INT_AND" in condition_operators
        assert "INT_SLESS" not in condition_operators

def test_state_transition_loop_summary_completes_default_case_as_complement():
    state = Expression.variable("__loop_state", size=4)
    parity = Expression.binary_op("INT_EQUAL", Expression.binary_op("INT_AND", state, _const(1)), _const(0))
    shift = Expression.binary_op("INT_SRIGHT", state, _const(1))
    subtract = Expression.binary_op("INT_SUB", state, _const(3))
    guard = Expression.binary_op("INT_SLESS", _const(0), state)
    summarizer = StructuralRecurrenceSummarizer(_FakeTracer("unused", _const(0)), debug=False)
    parity, _ = summarizer._normalize_state_transition_condition_term(parity, False)

    default_cases = summarizer._complete_default_state_transition_cases(
        ((parity, False, shift, False), (None, False, subtract, True))
    )
    default_cases = tuple(
        (condition, negated, value)
        for condition, negated, value, _is_source_default in default_cases
    )
    explicit_ref = StateTransitionLoopSummaryRef(
        state_guard=guard,
        transition_expr=None,
        transition_cases=((parity, False, shift), (parity, True, subtract)),
        accumulator_init=_const(0),
        accumulator_delta=_const(1),
        state_size=4,
        result_size=4,
    )
    default_ref = StateTransitionLoopSummaryRef(
        state_guard=guard,
        transition_expr=None,
        transition_cases=default_cases,
        accumulator_init=_const(0),
        accumulator_delta=_const(1),
        state_size=4,
        result_size=4,
    )

    assert default_ref.semantic_key() == explicit_ref.semantic_key()

def test_state_transition_loop_summary_does_not_rewrite_shifted_negative_candidate():
    state = Expression.variable("__loop_state", size=4)
    signed_guard = Expression.binary_op("INT_SLESS", _const(0), state)
    unsigned_guard = Expression.binary_op("INT_LESS", _const(0), state)
    unsigned_prechecked_guard = Expression.binary_op("INT_LESSEQUAL", _const(1), state)
    unsigned_negated_exit_guard = Expression.unary_op(
        "BOOL_NEGATE",
        Expression.binary_op("INT_LESS", state, _const(1)),
    )
    unsigned_negated_exit_guard.size = 1
    one = _const(1)
    three = _const(3)
    summarizer = StructuralRecurrenceSummarizer(_FakeTracer("unused", _const(0)), debug=False)

    direct_shift = Expression.binary_op("INT_RIGHT", state, one)
    canonical_direct = summarizer._canonicalize_state_transition_value(
        direct_shift,
        state_placeholder=state,
        state_guard=signed_guard,
    )
    assert canonical_direct.operator == "INT_SRIGHT"

    unsigned_guard_shift = summarizer._canonicalize_state_transition_value(
        direct_shift,
        state_placeholder=state,
        state_guard=unsigned_guard,
    )
    assert unsigned_guard_shift.operator == "INT_RIGHT"

    normalized_unsigned_precheck = summarizer._normalize_state_transition_state_guard(
        unsigned_prechecked_guard,
        state,
    )
    assert not summarizer._state_guard_proves_signed_positive_placeholder(normalized_unsigned_precheck, state)
    unsigned_precheck_shift = summarizer._canonicalize_state_transition_value(
        direct_shift,
        state_placeholder=state,
        state_guard=normalized_unsigned_precheck,
    )
    assert unsigned_precheck_shift.operator == "INT_RIGHT"

    normalized_unsigned_exit = summarizer._normalize_state_transition_state_guard(
        unsigned_negated_exit_guard,
        state,
    )
    assert not summarizer._state_guard_proves_signed_positive_placeholder(normalized_unsigned_exit, state)
    unsigned_exit_shift = summarizer._canonicalize_state_transition_value(
        direct_shift,
        state_placeholder=state,
        state_guard=normalized_unsigned_exit,
    )
    assert unsigned_exit_shift.operator == "INT_RIGHT"

    shifted_subtract = Expression.binary_op("INT_RIGHT", Expression.binary_op("INT_SUB", state, three), one)
    canonical_shifted_subtract = summarizer._canonicalize_state_transition_value(
        shifted_subtract,
        state_placeholder=state,
        state_guard=signed_guard,
    )
    assert canonical_shifted_subtract.operator == "INT_RIGHT"

def test_multiplicative_state_transition_base_recovery_proves_chunked_constant_case():
    summarizer = StructuralRecurrenceSummarizer(_FakeTracer("unused", _const(0)), debug=False)
    n = _param("param_1")
    start = _const(1)
    limit = Expression.binary_op("INT_ADD", n, _const(1))
    condition = _cond("INT_EQUAL", n, _const(4))

    recovered = summarizer._recover_proved_multiplicative_state_transition_base(
        loop_base_expr=_const(625),
        continue_conditions=[condition],
        start_expr=start,
        limit_expr=limit,
        result_size=4,
        signed_loop=True,
    )

    assert recovered is not None
    assert recovered.opcode == COUNTED_STATE_TRANSITION_VALUE_OPCODE
    assert isinstance(recovered.runtime_ref, CountedStateTransitionLoopSummaryRef)
    assert recovered.runtime_ref.initial_state.equals(_const(1))
    assert recovered.runtime_ref.start_expr.equals(start)
    assert recovered.runtime_ref.limit_expr.equals(limit)

def test_multiplicative_state_transition_base_recovery_rejects_near_misses():
    summarizer = StructuralRecurrenceSummarizer(_FakeTracer("unused", _const(0)), debug=False)
    n = _param("param_1")
    start = _const(1)
    limit = Expression.binary_op("INT_ADD", n, _const(1))

    assert summarizer._recover_proved_multiplicative_state_transition_base(
        loop_base_expr=_const(1295),
        continue_conditions=[_cond("INT_EQUAL", n, _const(4))],
        start_expr=start,
        limit_expr=limit,
        result_size=4,
        signed_loop=True,
    ) is None
    assert summarizer._recover_proved_multiplicative_state_transition_base(
        loop_base_expr=_const(125),
        continue_conditions=[_cond("INT_EQUAL", n, _const(4))],
        start_expr=start,
        limit_expr=limit,
        result_size=4,
        signed_loop=True,
    ) is None
    assert summarizer._recover_proved_multiplicative_state_transition_base(
        loop_base_expr=_const(625),
        continue_conditions=[_cond("INT_EQUAL", n, _const(3))],
        start_expr=start,
        limit_expr=limit,
        result_size=4,
        signed_loop=True,
    ) is None
    assert summarizer._recover_proved_multiplicative_state_transition_base(
        loop_base_expr=Expression.unknown("chunked_state"),
        continue_conditions=[_cond("INT_EQUAL", n, _const(4))],
        start_expr=start,
        limit_expr=limit,
        result_size=4,
        signed_loop=True,
    ) is None

def test_state_transition_loop_summary_rejects_non_state_transition_condition():
    state = Expression.variable("__loop_state", size=4)
    selector = Expression.parameter("param_2", index=1, data_type="int", size=4)
    guard = Expression.binary_op("INT_SLESS", _const(0), state)
    selector_condition = Condition(Expression.binary_op("INT_SLESS", _const(0), selector), False)
    transition_expr = Expression.phi((
        (selector_condition, Expression.binary_op("INT_SUB", state, _const(1))),
        (None, Expression.binary_op("INT_SUB", state, _const(2))),
    ))
    transition_expr.size = 4
    summarizer = StructuralRecurrenceSummarizer(_FakeTracer("unused", _const(0)), debug=False)

    assert summarizer._state_transition_summary_cases(
        transition_expr=transition_expr,
        state_guard=guard,
        state_placeholder=state,
    ) is None

def test_state_transition_loop_summary_drops_non_state_condition_when_values_match():
    state = Expression.variable("__loop_state", size=4)
    selector = Expression.parameter("param_2", index=1, data_type="int", size=4)
    guard = Expression.binary_op("INT_SLESS", _const(0), state)
    selector_condition = Condition(Expression.binary_op("INT_SLESS", _const(0), selector), False)
    same_value = Expression.binary_op("INT_SUB", state, _const(1))
    transition_expr = Expression.phi((
        (selector_condition, same_value),
        (None, same_value),
    ))
    transition_expr.size = 4
    summarizer = StructuralRecurrenceSummarizer(_FakeTracer("unused", _const(0)), debug=False)

    cases = summarizer._state_transition_summary_cases(
        transition_expr=transition_expr,
        state_guard=guard,
        state_placeholder=state,
    )

    assert cases is not None
    assert len(cases) == 1
    condition_expr, negated, value = cases[0]
    assert condition_expr is None
    assert negated is False
    assert value.structural_key() == same_value.structural_key()

def test_state_transition_loop_summary_recovers_multi_latch_rotated_loop():
    analysis = create_mock_analysis(
        "branch_while_state",
        return_type="int",
        parameters=[{"name": "param_1", "index": 0, "data_type": "int", "size": 4, "is_signed": True}],
        returns=[ReturnInfo(address="0x1000", value=Expression.unknown("phi_circular"), conditions=[])],
    )
    summarizer = StructuralRecurrenceSummarizer(_FakeTracer("unused", _const(0)), debug=False)

    header_returns, _ = summarizer.try_summarize_function(
        _FakeFunction("branch_while_state"),
        _build_branch_while_state_cfg(),
        analysis,
    )
    multi_latch_returns, _ = summarizer.try_summarize_function(
        _FakeFunction("branch_while_state"),
        _build_branch_while_state_multi_latch_cfg(),
        analysis,
    )

    header_intrinsic = next(ret.value for ret in header_returns if ret.value.expr_type == ExpressionType.INTRINSIC)
    multi_latch_intrinsic = next(ret.value for ret in multi_latch_returns if ret.value.expr_type == ExpressionType.INTRINSIC)
    assert multi_latch_intrinsic.runtime_ref.semantic_key() == header_intrinsic.runtime_ref.semantic_key()
