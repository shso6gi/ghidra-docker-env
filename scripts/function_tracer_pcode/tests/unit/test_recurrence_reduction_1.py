from scripts.function_tracer_pcode.tests.unit._recurrence_fixtures import *

def test_readonly_parameter_helpers_preserve_storage_backed_identity_without_fabricated_index():
    storage = StorageInfo(
        is_register=True,
        space_name="register",
        register_name="a1",
        base_register_name="a1",
        size=4,
        size_bits=32,
    )
    summarizer = StructuralRecurrenceSummarizer(PcodeTracer.__new__(PcodeTracer), debug=False)
    param = {
        "name": "renamed_count",
        "size": 4,
        "data_type": "int",
        "storage_info": storage,
    }

    expr = summarizer._parameter_expression(param)
    base_ref = summarizer._location_base_ref_from_parameter(param, default_name="count")

    assert expr.value == -1
    assert expr.storage_info is storage
    assert summarizer._parameter_storage_identity_key(param) == storage.storage_identity_key()
    assert base_ref.is_storage()
    assert base_ref.semantic_key() == ("storage_identity", storage.storage_identity_key())

def test_vector_zero_base_coverage_normalizes_counter_parameter_identity():
    summarizer = StructuralRecurrenceSummarizer(PcodeTracer.__new__(PcodeTracer), debug=False)
    counter_param = {
        "name": "renamed_count",
        "index": 0,
        "size": 4,
        "data_type": "int",
    }
    primary_counter = summarizer._parameter_expression(counter_param)
    return_counter = Expression.parameter("param_1", index=0, data_type="int", size=4)
    positive_guard = _cond("INT_SLESS", _const(0), primary_counter)
    zero_case = ReturnInfo(
        address="00100000",
        value=_const(0),
        conditions=[_cond("INT_SLESS", return_counter, _const(1))],
    )
    positive_case = ReturnInfo(
        address="00100004",
        value=_const(1),
        conditions=[_cond("INT_SLESS", _const(0), return_counter)],
    )
    analysis = type("Analysis", (), {"returns": [zero_case, positive_case]})()

    base_guard = summarizer._zero_base_guard_cover_for_positive_counter_guard(
        analysis,
        counter_param,
        primary_counter,
        positive_guard,
    )

    assert base_guard is not None
    assert summarizer._nonzero_returns_are_disjoint_from_base_guard(
        analysis,
        base_guard,
        counter_param,
        primary_counter,
    )

def test_try_summarize_prefers_vector_affine_before_counted_scalar(monkeypatch):
    summarizer = StructuralRecurrenceSummarizer(PcodeTracer.__new__(PcodeTracer), debug=False)
    calls = []

    monkeypatch.setattr(
        summarizer,
        "_try_summarize_linear_self_recursion",
        lambda *_args: None,
    )
    monkeypatch.setattr(
        summarizer,
        "_try_summarize_readonly_pointer_reduction",
        lambda *_args: None,
    )

    def vector_summary(*_args):
        calls.append("vector")
        return ([], "vectorized_affine_progression_sum_summary")

    def scalar_summary(*_args):
        calls.append("scalar")
        return ([], "counted_scalar_loop_summary")

    monkeypatch.setattr(summarizer, "_try_summarize_vectorized_affine_progression_sum", vector_summary)
    monkeypatch.setattr(summarizer, "_try_summarize_counted_scalar_loop", scalar_summary)

    analysis = type("Analysis", (), {"parameters": [{"name": "param_1"}]})()
    summary = summarizer.try_summarize_function(object(), object(), analysis)

    assert summary == ([], "vectorized_affine_progression_sum_summary")
    assert calls == ["vector"]

def test_counted_scalar_declines_residue_readonly_vector_literal_address(monkeypatch):
    summarizer = StructuralRecurrenceSummarizer(PcodeTracer.__new__(PcodeTracer), debug=False)

    monkeypatch.setattr(summarizer, "_address_points_to_readonly_data", lambda value: value == 0x100278)

    def fake_lanes(value, lane_count):
        if value == 0x100278 and lane_count == 4:
            return (1, 2, 3, 4)
        return None

    monkeypatch.setattr(summarizer, "_read_readonly_int32_lanes", fake_lanes)

    assert summarizer._residue_cases_contain_readonly_affine_literal_address(
        (
            ResidueLoopCase(
                modulus=1,
                residue=0,
                affine=(0, 0x100278),
                affine_from_readonly_literal=True,
            ),
        )
    )
    assert not summarizer._residue_cases_contain_readonly_affine_literal_address(
        (ResidueLoopCase(modulus=1, residue=0, affine=(1, 0)),)
    )

def test_counted_scalar_keeps_plain_affine_coefficient_equal_to_readonly_address(monkeypatch):
    summarizer = StructuralRecurrenceSummarizer(PcodeTracer.__new__(PcodeTracer), debug=False)

    monkeypatch.setattr(summarizer, "_address_points_to_readonly_data", lambda value: value == 0x100278)

    def fake_lanes(value, lane_count):
        if value == 0x100278 and lane_count == 4:
            return (1, 2, 3, 4)
        return None

    monkeypatch.setattr(summarizer, "_read_readonly_int32_lanes", fake_lanes)

    assert not summarizer._residue_cases_contain_readonly_affine_literal_address(
        (
            ResidueLoopCase(
                modulus=1,
                residue=0,
                affine=(0x100278, 0),
                affine_from_readonly_literal=False,
            ),
        )
    )

def test_counted_scalar_declines_plain_affine_bias_equal_to_readonly_progression(monkeypatch):
    summarizer = StructuralRecurrenceSummarizer(PcodeTracer.__new__(PcodeTracer), debug=False)

    def fake_lanes(value, lane_count):
        if value == 0x100278 and lane_count == 4:
            return (1, 2, 3, 4)
        return None

    monkeypatch.setattr(summarizer, "_read_readonly_int32_lanes", fake_lanes)

    assert summarizer._residue_cases_contain_readonly_affine_literal_address(
        (
            ResidueLoopCase(
                modulus=1,
                residue=0,
                affine=(0, 0x100278),
                affine_from_readonly_literal=False,
            ),
        )
    )

def test_extract_residue_case_marks_readonly_literal_access_provenance(monkeypatch):
    summarizer = StructuralRecurrenceSummarizer(PcodeTracer.__new__(PcodeTracer), debug=False)
    counter = _param("__loop_iv")
    readonly_addr = Expression.constant(0x100278, size=8)
    low_lane = Expression.binary_op("SUBPIECE", readonly_addr, _const(0))
    delta = Expression.binary_op("INT_ADD", counter, low_lane)

    monkeypatch.setattr(summarizer, "_address_points_to_readonly_data", lambda value: value == 0x100278)
    residue_cases = summarizer._extract_residue_loop_cases(
        (CountedLoopUpdateCase(conditions=(), update_expr=delta, delta_expr=delta),),
        "__loop_iv",
    )

    assert residue_cases is not None
    assert residue_cases[0].affine_from_readonly_literal is True

def test_counted_scalar_declines_extracted_bias_readonly_literal_access(monkeypatch):
    summarizer = StructuralRecurrenceSummarizer(PcodeTracer.__new__(PcodeTracer), debug=False)
    counter = _param("__loop_iv")
    readonly_addr = Expression.constant(0x100278, size=8)
    low_lane = Expression.binary_op("SUBPIECE", readonly_addr, _const(0))
    delta = Expression.binary_op("INT_ADD", counter, low_lane)

    monkeypatch.setattr(summarizer, "_address_points_to_readonly_data", lambda value: value == 0x100278)
    residue_cases = summarizer._extract_residue_loop_cases(
        (CountedLoopUpdateCase(conditions=(), update_expr=delta, delta_expr=delta),),
        "__loop_iv",
    )

    assert residue_cases is not None
    assert residue_cases[0].affine == (1, 0)
    assert residue_cases[0].bias_expr is not None
    assert summarizer._residue_cases_contain_readonly_affine_literal_address(residue_cases)

def test_expression_equivalence_query_declares_memory_arrays_for_readonly_witness_proof():
    summarizer = StructuralRecurrenceSummarizer(PcodeTracer.__new__(PcodeTracer), debug=False)
    left = Expression.binary_op("INT_ADD", _mem("param_1", 0), _mem("param_1", 4))
    right = Expression.binary_op("INT_ADD", _mem("param_1", 4), _mem("param_1", 0))

    query = summarizer._build_expression_equivalence_query(
        left,
        right,
        [],
        [{"name": "param_1", "index": 0, "size": 8, "data_type": "int *"}],
    )

    assert query is not None
    assert "(set-logic QF_AUFBV)" in query
    assert "(declare-const mem32 (Array (_ BitVec 64) (_ BitVec 32)))" in query

def test_readonly_index_progression_declines_negative_step():
    phi_output = _FakeVarnode("loop_index")
    init_vn = _FakeVarnode("limit_minus_one", expr=_const(7))
    one_vn = _FakeVarnode("one", expr=_const(1))
    next_vn = _FakeVarnode("loop_index_next")
    _FakePcodeOp("INT_SUB", [phi_output, one_vn], next_vn)
    phi_op = _FakePcodeOp("MULTIEQUAL", [init_vn, next_vn], phi_output)
    summarizer = StructuralRecurrenceSummarizer(_FakeTracer("unused", _const(0)), debug=False)

    assert summarizer._extract_index_step(next_vn, phi_output) == -1
    assert summarizer._match_index_progression_phi(phi_op) is None

def test_vectorized_affine_progression_literal_summary_builds_counted_loop_sum():
    ram_space = _FakeAddressSpace("ram", space_id=1, is_memory=True)
    literal_base = 0x100120
    literal_bytes = bytes(
        byte
        for value in (0, 5, 10, 15)
        for byte in int(value).to_bytes(4, "little", signed=True)
    )
    program = _FakeProgram(
        _FakeAddressFactory({1: ram_space}, default_space=ram_space),
        memory=_FakeMemory(
            [_FakeMemoryBlock(literal_base, literal_base + len(literal_bytes) - 1, execute=False)],
            bytes_by_address={
                literal_base + offset: byte
                for offset, byte in enumerate(literal_bytes)
            },
        ),
    )
    tracer = _FakeTracer("f", _const(0), program=program)
    summarizer = StructuralRecurrenceSummarizer(tracer, debug=False)
    n_expr = Expression.parameter("param_1", index=0, data_type="int", size=4)
    bias_expr = Expression.parameter("param_2", index=1, data_type="int", size=4)
    positive_value = summarizer._build_affine_progression_sum_closed_expression(
        count_expr=n_expr,
        step=5,
        bias_expr=bias_expr,
        result_size=4,
    )
    assert positive_value is not None
    zero_case = ReturnInfo(
        address="00100104",
        value=_const(0),
        conditions=[
            Condition(
                Expression.binary_op("INT_SLESS", n_expr, _const(1)),
                False,
            )
        ],
        branch_index=0,
    )
    literal_case = ReturnInfo(
        address="00100104",
        value=positive_value,
        conditions=[Condition(Expression.binary_op("INT_SLESS", _const(0), n_expr), False)],
        branch_index=1,
    )
    literal_probe_case = ReturnInfo(
        address="00100104",
        value=Expression.binary_op("SUBPIECE", Expression.constant(literal_base, size=8), _const(0)),
        conditions=[
            Condition(Expression.binary_op("INT_EQUAL", n_expr, _const(0)), False),
            Condition(Expression.binary_op("INT_SLESS", _const(0), n_expr), False),
        ],
        branch_index=2,
    )
    analysis = type("FakeAnalysis", (), {})()
    int_type = _FakeIntDataType()
    analysis.parameters = [
        {"name": "param_1", "index": 0, "data_type": "uint", "data_type_obj": int_type, "size": 4},
        {"name": "param_2", "index": 1, "data_type": "int", "data_type_obj": int_type, "size": 4},
    ]
    analysis.returns = [zero_case, literal_case, literal_probe_case]
    analysis.incomplete_control_flow = False
    analysis.effect_summary = None

    summary = summarizer._try_summarize_vectorized_affine_progression_sum(
        _FakeFunction("f"),
        _FakeCfgHighFunction([]),
        analysis,
    )

    assert summary is not None
    returns, note = summary
    assert note == "vectorized_affine_progression_sum_summary"
    assert len(returns) == 2
    assert returns[0].value.equals(_const(0))
    loop_value = returns[1].value
    assert getattr(loop_value, "opcode", None) == COUNTED_LOOP_SUM_OPCODE
    runtime_ref = getattr(loop_value, "runtime_ref", None)
    assert runtime_ref is not None
    assert runtime_ref.residue_cases == ((1, 0, 5, 0),)
    assert runtime_ref.residue_bias_terms

def test_vectorized_affine_summary_preserves_side_effect_profile():
    ram_space = _FakeAddressSpace("ram", space_id=1, is_memory=True)
    literal_base = 0x100120
    literal_bytes = bytes(
        byte
        for value in (0, 5, 10, 15)
        for byte in int(value).to_bytes(4, "little", signed=True)
    )
    program = _FakeProgram(
        _FakeAddressFactory({1: ram_space}, default_space=ram_space),
        memory=_FakeMemory(
            [_FakeMemoryBlock(literal_base, literal_base + len(literal_bytes) - 1, execute=False)],
            bytes_by_address={
                literal_base + offset: byte
                for offset, byte in enumerate(literal_bytes)
            },
        ),
    )
    tracer = _FakeTracer("f", _const(0), program=program)
    summarizer = StructuralRecurrenceSummarizer(tracer, debug=False)
    n_expr = Expression.parameter("param_1", index=0, data_type="int", size=4)
    bias_expr = Expression.parameter("param_2", index=1, data_type="int", size=4)
    positive_value = summarizer._build_affine_progression_sum_closed_expression(
        count_expr=n_expr,
        step=5,
        bias_expr=bias_expr,
        result_size=4,
    )
    assert positive_value is not None
    analysis = type("FakeAnalysis", (), {})()
    int_type = _FakeIntDataType()
    analysis.parameters = [
        {"name": "param_1", "index": 0, "data_type": "int", "data_type_obj": int_type, "size": 4},
        {"name": "param_2", "index": 1, "data_type": "int", "data_type_obj": int_type, "size": 4},
    ]
    analysis.returns = [
        ReturnInfo(
            address="00100104",
            value=_const(0),
            conditions=[Condition(Expression.binary_op("INT_SLESS", n_expr, _const(1)), False)],
            branch_index=0,
        ),
        ReturnInfo(
            address="00100104",
            value=positive_value,
            conditions=[Condition(Expression.binary_op("INT_SLESS", _const(0), n_expr), False)],
            branch_index=1,
        ),
        ReturnInfo(
            address="00100104",
            value=Expression.binary_op("SUBPIECE", Expression.constant(literal_base, size=8), _const(0)),
            conditions=[
                Condition(Expression.binary_op("INT_EQUAL", n_expr, _const(0)), False),
                Condition(Expression.binary_op("INT_SLESS", _const(0), n_expr), False),
            ],
            branch_index=2,
        ),
    ]
    analysis.incomplete_control_flow = False
    analysis.effect_summary = None
    guard_block = _FakeCfgBlock(
        1,
        ops=[_FakeBranchOp(Expression.binary_op("INT_NOTEQUAL", n_expr, _const(0)))],
    )

    summary = summarizer._try_summarize_vectorized_affine_progression_sum(
        _FakeFunction("f"),
        _FakeCfgHighFunction([guard_block]),
        analysis,
    )

    assert summary is not None
    returns, _note = summary
    runtime_ref = getattr(returns[1].value, "runtime_ref", None)
    assert runtime_ref is not None
    profile = runtime_ref.loop_summary.side_effect_profile
    assert profile.profile == "pure"
    assert profile.conditional_guards is False
    assert profile.context_conditional_guards is True
    assert profile.guard_count == 0
    assert profile.effect_descriptors == ()
    assert len(profile.context_descriptors) == 1
    assert profile.context_descriptors[0].kind == "conditional_guard"

def test_vectorized_affine_progression_literal_summary_infers_constant_bias_for_single_parameter():
    ram_space = _FakeAddressSpace("ram", space_id=1, is_memory=True)
    literal_base = 0x100120
    literal_bytes = bytes(
        byte
        for value in (1, 2, 3, 4)
        for byte in int(value).to_bytes(4, "little", signed=True)
    )
    program = _FakeProgram(
        _FakeAddressFactory({1: ram_space}, default_space=ram_space),
        memory=_FakeMemory(
            [_FakeMemoryBlock(literal_base, literal_base + len(literal_bytes) - 1, execute=False)],
            bytes_by_address={
                literal_base + offset: byte
                for offset, byte in enumerate(literal_bytes)
            },
        ),
    )
    tracer = _FakeTracer("f", _const(0), program=program)
    summarizer = StructuralRecurrenceSummarizer(tracer, debug=False)
    n_expr = Expression.parameter("param_1", index=0, data_type="int", size=4)
    positive_value = summarizer._build_affine_progression_sum_closed_expression(
        count_expr=n_expr,
        step=1,
        bias_expr=_const(1),
        result_size=4,
    )
    assert positive_value is not None
    zero_case = ReturnInfo(
        address="00100104",
        value=_const(0),
        conditions=[
            Condition(
                Expression.binary_op("INT_SLESS", n_expr, _const(1)),
                False,
            )
        ],
        branch_index=0,
    )
    positive_case = ReturnInfo(
        address="00100104",
        value=positive_value,
        conditions=[Condition(Expression.binary_op("INT_SLESS", _const(0), n_expr), False)],
        branch_index=1,
    )
    literal_probe_case = ReturnInfo(
        address="00100104",
        value=Expression.binary_op("SUBPIECE", Expression.constant(literal_base, size=8), _const(0)),
        conditions=[
            Condition(Expression.binary_op("INT_EQUAL", n_expr, _const(0)), False),
            Condition(Expression.binary_op("INT_SLESS", _const(0), n_expr), False),
        ],
        branch_index=2,
    )
    analysis = type("FakeAnalysis", (), {})()
    int_type = _FakeIntDataType()
    analysis.parameters = [
        {"name": "param_1", "index": 0, "data_type": "int", "data_type_obj": int_type, "size": 4},
    ]
    analysis.returns = [zero_case, positive_case, literal_probe_case]
    analysis.incomplete_control_flow = False
    analysis.effect_summary = None

    summary = summarizer._try_summarize_vectorized_affine_progression_sum(
        _FakeFunction("f"),
        _FakeCfgHighFunction([]),
        analysis,
    )

    assert summary is not None
    returns, note = summary
    assert note == "vectorized_affine_progression_sum_summary"
    runtime_ref = getattr(returns[1].value, "runtime_ref", None)
    assert runtime_ref is not None
    assert runtime_ref.residue_cases == ((1, 0, 1, 0),)
    assert runtime_ref.residue_bias_terms
    assert runtime_ref.residue_bias_terms[0][2].equals(_const(1))

def test_vectorized_affine_progression_literal_summary_uses_nonzero_lane_base_for_single_parameter():
    ram_space = _FakeAddressSpace("ram", space_id=1, is_memory=True)
    literal_base = 0x100120
    literal_bytes = bytes(
        byte
        for value in (2, 7, 12, 17)
        for byte in int(value).to_bytes(4, "little", signed=True)
    )
    program = _FakeProgram(
        _FakeAddressFactory({1: ram_space}, default_space=ram_space),
        memory=_FakeMemory(
            [_FakeMemoryBlock(literal_base, literal_base + len(literal_bytes) - 1, execute=False)],
            bytes_by_address={
                literal_base + offset: byte
                for offset, byte in enumerate(literal_bytes)
            },
        ),
    )
    tracer = _FakeTracer("f", _const(0), program=program)
    summarizer = StructuralRecurrenceSummarizer(tracer, debug=False)
    n_expr = Expression.parameter("param_1", index=0, data_type="int", size=4)
    positive_value = summarizer._build_affine_progression_sum_closed_expression(
        count_expr=n_expr,
        step=5,
        bias_expr=_const(2),
        result_size=4,
    )
    assert positive_value is not None
    analysis = type("FakeAnalysis", (), {})()
    int_type = _FakeIntDataType()
    analysis.parameters = [
        {"name": "param_1", "index": 0, "data_type": "int", "data_type_obj": int_type, "size": 4},
    ]
    analysis.returns = [
        ReturnInfo(
            address="00100104",
            value=_const(0),
            conditions=[Condition(Expression.binary_op("INT_SLESS", n_expr, _const(1)), False)],
            branch_index=0,
        ),
        ReturnInfo(
            address="00100104",
            value=positive_value,
            conditions=[Condition(Expression.binary_op("INT_SLESS", _const(0), n_expr), False)],
            branch_index=1,
        ),
        ReturnInfo(
            address="00100104",
            value=Expression.binary_op("SUBPIECE", Expression.constant(literal_base, size=8), _const(0)),
            conditions=[
                Condition(Expression.binary_op("INT_EQUAL", n_expr, _const(0)), False),
                Condition(Expression.binary_op("INT_SLESS", _const(0), n_expr), False),
            ],
            branch_index=2,
        ),
    ]
    analysis.incomplete_control_flow = False
    analysis.effect_summary = None

    summary = summarizer._try_summarize_vectorized_affine_progression_sum(
        _FakeFunction("f"),
        _FakeCfgHighFunction([]),
        analysis,
    )

    assert summary is not None
    returns, note = summary
    assert note == "vectorized_affine_progression_sum_summary"
    runtime_ref = getattr(returns[1].value, "runtime_ref", None)
    assert runtime_ref is not None
    assert runtime_ref.residue_cases == ((1, 0, 5, 0),)
    assert runtime_ref.residue_bias_terms
    assert runtime_ref.residue_bias_terms[0][2].equals(_const(2))

def test_vectorized_affine_progression_literal_summary_adds_lane_base_to_parameter_bias():
    ram_space = _FakeAddressSpace("ram", space_id=1, is_memory=True)
    literal_base = 0x100120
    literal_bytes = bytes(
        byte
        for value in (2, 7, 12, 17)
        for byte in int(value).to_bytes(4, "little", signed=True)
    )
    program = _FakeProgram(
        _FakeAddressFactory({1: ram_space}, default_space=ram_space),
        memory=_FakeMemory(
            [_FakeMemoryBlock(literal_base, literal_base + len(literal_bytes) - 1, execute=False)],
            bytes_by_address={
                literal_base + offset: byte
                for offset, byte in enumerate(literal_bytes)
            },
        ),
    )
    tracer = _FakeTracer("f", _const(0), program=program)
    summarizer = StructuralRecurrenceSummarizer(tracer, debug=False)
    n_expr = Expression.parameter("param_1", index=0, data_type="int", size=4)
    bias_expr = Expression.parameter("param_2", index=1, data_type="int", size=4)
    bias_plus_lane_base = Expression.binary_op("INT_ADD", bias_expr, _const(2))
    bias_plus_lane_base.size = 4
    positive_value = summarizer._build_affine_progression_sum_closed_expression(
        count_expr=n_expr,
        step=5,
        bias_expr=bias_plus_lane_base,
        result_size=4,
    )
    assert positive_value is not None
    analysis = type("FakeAnalysis", (), {})()
    int_type = _FakeIntDataType()
    analysis.parameters = [
        {"name": "param_1", "index": 0, "data_type": "int", "data_type_obj": int_type, "size": 4},
        {"name": "param_2", "index": 1, "data_type": "int", "data_type_obj": int_type, "size": 4},
    ]
    analysis.returns = [
        ReturnInfo(
            address="00100104",
            value=_const(0),
            conditions=[Condition(Expression.binary_op("INT_SLESS", n_expr, _const(1)), False)],
            branch_index=0,
        ),
        ReturnInfo(
            address="00100104",
            value=positive_value,
            conditions=[Condition(Expression.binary_op("INT_SLESS", _const(0), n_expr), False)],
            branch_index=1,
        ),
        ReturnInfo(
            address="00100104",
            value=Expression.binary_op("SUBPIECE", Expression.constant(literal_base, size=8), _const(0)),
            conditions=[
                Condition(Expression.binary_op("INT_EQUAL", n_expr, _const(0)), False),
                Condition(Expression.binary_op("INT_SLESS", _const(0), n_expr), False),
            ],
            branch_index=2,
        ),
    ]
    analysis.incomplete_control_flow = False
    analysis.effect_summary = None

    summary = summarizer._try_summarize_vectorized_affine_progression_sum(
        _FakeFunction("f"),
        _FakeCfgHighFunction([]),
        analysis,
    )

    assert summary is not None
    returns, note = summary
    assert note == "vectorized_affine_progression_sum_summary"
    runtime_ref = getattr(returns[1].value, "runtime_ref", None)
    assert runtime_ref is not None
    assert runtime_ref.residue_cases == ((1, 0, 5, 0),)
    assert runtime_ref.residue_bias_terms
    assert runtime_ref.residue_bias_terms[0][2].equals(bias_plus_lane_base)

def test_vectorized_affine_progression_literal_summary_rejects_parameter_bias_without_lane_base():
    ram_space = _FakeAddressSpace("ram", space_id=1, is_memory=True)
    literal_base = 0x100120
    literal_bytes = bytes(
        byte
        for value in (2, 7, 12, 17)
        for byte in int(value).to_bytes(4, "little", signed=True)
    )
    program = _FakeProgram(
        _FakeAddressFactory({1: ram_space}, default_space=ram_space),
        memory=_FakeMemory(
            [_FakeMemoryBlock(literal_base, literal_base + len(literal_bytes) - 1, execute=False)],
            bytes_by_address={
                literal_base + offset: byte
                for offset, byte in enumerate(literal_bytes)
            },
        ),
    )
    tracer = _FakeTracer("f", _const(0), program=program)
    summarizer = StructuralRecurrenceSummarizer(tracer, debug=False)
    n_expr = Expression.parameter("param_1", index=0, data_type="int", size=4)
    bias_expr = Expression.parameter("param_2", index=1, data_type="int", size=4)
    positive_value = summarizer._build_affine_progression_sum_closed_expression(
        count_expr=n_expr,
        step=5,
        bias_expr=bias_expr,
        result_size=4,
    )
    assert positive_value is not None
    analysis = type("FakeAnalysis", (), {})()
    int_type = _FakeIntDataType()
    analysis.parameters = [
        {"name": "param_1", "index": 0, "data_type": "int", "data_type_obj": int_type, "size": 4},
        {"name": "param_2", "index": 1, "data_type": "int", "data_type_obj": int_type, "size": 4},
    ]
    analysis.returns = [
        ReturnInfo(
            address="00100104",
            value=_const(0),
            conditions=[Condition(Expression.binary_op("INT_SLESS", n_expr, _const(1)), False)],
            branch_index=0,
        ),
        ReturnInfo(
            address="00100104",
            value=positive_value,
            conditions=[Condition(Expression.binary_op("INT_SLESS", _const(0), n_expr), False)],
            branch_index=1,
        ),
        ReturnInfo(
            address="00100104",
            value=Expression.binary_op("SUBPIECE", Expression.constant(literal_base, size=8), _const(0)),
            conditions=[
                Condition(Expression.binary_op("INT_EQUAL", n_expr, _const(0)), False),
                Condition(Expression.binary_op("INT_SLESS", _const(0), n_expr), False),
            ],
            branch_index=2,
        ),
    ]
    analysis.incomplete_control_flow = False
    analysis.effect_summary = None

    assert summarizer._try_summarize_vectorized_affine_progression_sum(
        _FakeFunction("f"),
        _FakeCfgHighFunction([]),
        analysis,
    ) is None

def test_vectorized_affine_progression_literal_summary_uses_negative_lane_base_for_single_parameter():
    ram_space = _FakeAddressSpace("ram", space_id=1, is_memory=True)
    literal_base = 0x100120
    literal_bytes = bytes(
        byte
        for value in (-2, 3, 8, 13)
        for byte in int(value).to_bytes(4, "little", signed=True)
    )
    program = _FakeProgram(
        _FakeAddressFactory({1: ram_space}, default_space=ram_space),
        memory=_FakeMemory(
            [_FakeMemoryBlock(literal_base, literal_base + len(literal_bytes) - 1, execute=False)],
            bytes_by_address={
                literal_base + offset: byte
                for offset, byte in enumerate(literal_bytes)
            },
        ),
    )
    tracer = _FakeTracer("f", _const(0), program=program)
    summarizer = StructuralRecurrenceSummarizer(tracer, debug=False)
    n_expr = Expression.parameter("param_1", index=0, data_type="int", size=4)
    lane_base_expr = Expression.constant(-2, size=4)
    positive_value = summarizer._build_affine_progression_sum_closed_expression(
        count_expr=n_expr,
        step=5,
        bias_expr=lane_base_expr,
        result_size=4,
    )
    assert positive_value is not None
    analysis = type("FakeAnalysis", (), {})()
    int_type = _FakeIntDataType()
    analysis.parameters = [
        {"name": "param_1", "index": 0, "data_type": "int", "data_type_obj": int_type, "size": 4},
    ]
    analysis.returns = [
        ReturnInfo(
            address="00100104",
            value=_const(0),
            conditions=[Condition(Expression.binary_op("INT_SLESS", n_expr, _const(1)), False)],
            branch_index=0,
        ),
        ReturnInfo(
            address="00100104",
            value=positive_value,
            conditions=[Condition(Expression.binary_op("INT_SLESS", _const(0), n_expr), False)],
            branch_index=1,
        ),
        ReturnInfo(
            address="00100104",
            value=Expression.binary_op("SUBPIECE", Expression.constant(literal_base, size=8), _const(0)),
            conditions=[
                Condition(Expression.binary_op("INT_EQUAL", n_expr, _const(0)), False),
                Condition(Expression.binary_op("INT_SLESS", _const(0), n_expr), False),
            ],
            branch_index=2,
        ),
    ]
    analysis.incomplete_control_flow = False
    analysis.effect_summary = None

    summary = summarizer._try_summarize_vectorized_affine_progression_sum(
        _FakeFunction("f"),
        _FakeCfgHighFunction([]),
        analysis,
    )

    assert summary is not None
    returns, note = summary
    assert note == "vectorized_affine_progression_sum_summary"
    runtime_ref = getattr(returns[1].value, "runtime_ref", None)
    assert runtime_ref is not None
    assert runtime_ref.residue_cases == ((1, 0, 5, 0),)
    assert runtime_ref.residue_bias_terms
    assert runtime_ref.residue_bias_terms[0][2].equals(lane_base_expr)

def test_vectorized_affine_progression_literal_summary_rejects_parameter_bias_without_negative_lane_base():
    ram_space = _FakeAddressSpace("ram", space_id=1, is_memory=True)
    literal_base = 0x100120
    literal_bytes = bytes(
        byte
        for value in (-2, 3, 8, 13)
        for byte in int(value).to_bytes(4, "little", signed=True)
    )
    program = _FakeProgram(
        _FakeAddressFactory({1: ram_space}, default_space=ram_space),
        memory=_FakeMemory(
            [_FakeMemoryBlock(literal_base, literal_base + len(literal_bytes) - 1, execute=False)],
            bytes_by_address={
                literal_base + offset: byte
                for offset, byte in enumerate(literal_bytes)
            },
        ),
    )
    tracer = _FakeTracer("f", _const(0), program=program)
    summarizer = StructuralRecurrenceSummarizer(tracer, debug=False)
    n_expr = Expression.parameter("param_1", index=0, data_type="int", size=4)
    bias_expr = Expression.parameter("param_2", index=1, data_type="int", size=4)
    positive_value = summarizer._build_affine_progression_sum_closed_expression(
        count_expr=n_expr,
        step=5,
        bias_expr=bias_expr,
        result_size=4,
    )
    assert positive_value is not None
    analysis = type("FakeAnalysis", (), {})()
    int_type = _FakeIntDataType()
    analysis.parameters = [
        {"name": "param_1", "index": 0, "data_type": "int", "data_type_obj": int_type, "size": 4},
        {"name": "param_2", "index": 1, "data_type": "int", "data_type_obj": int_type, "size": 4},
    ]
    analysis.returns = [
        ReturnInfo(
            address="00100104",
            value=_const(0),
            conditions=[Condition(Expression.binary_op("INT_SLESS", n_expr, _const(1)), False)],
            branch_index=0,
        ),
        ReturnInfo(
            address="00100104",
            value=positive_value,
            conditions=[Condition(Expression.binary_op("INT_SLESS", _const(0), n_expr), False)],
            branch_index=1,
        ),
        ReturnInfo(
            address="00100104",
            value=Expression.binary_op("SUBPIECE", Expression.constant(literal_base, size=8), _const(0)),
            conditions=[
                Condition(Expression.binary_op("INT_EQUAL", n_expr, _const(0)), False),
                Condition(Expression.binary_op("INT_SLESS", _const(0), n_expr), False),
            ],
            branch_index=2,
        ),
    ]
    analysis.incomplete_control_flow = False
    analysis.effect_summary = None

    assert summarizer._try_summarize_vectorized_affine_progression_sum(
        _FakeFunction("f"),
        _FakeCfgHighFunction([]),
        analysis,
    ) is None

def test_vectorized_affine_progression_literal_summary_builds_unsigned_counted_loop_sum():
    ram_space = _FakeAddressSpace("ram", space_id=1, is_memory=True)
    literal_base = 0x100120
    literal_bytes = bytes(
        byte
        for value in (0, 5, 10, 15)
        for byte in int(value).to_bytes(4, "little", signed=True)
    )
    program = _FakeProgram(
        _FakeAddressFactory({1: ram_space}, default_space=ram_space),
        memory=_FakeMemory(
            [_FakeMemoryBlock(literal_base, literal_base + len(literal_bytes) - 1, execute=False)],
            bytes_by_address={
                literal_base + offset: byte
                for offset, byte in enumerate(literal_bytes)
            },
        ),
    )
    tracer = _FakeTracer("f", _const(0), program=program)
    summarizer = StructuralRecurrenceSummarizer(tracer, debug=False)
    n_expr = Expression.parameter("param_1", index=0, data_type="uint", size=4)
    bias_expr = Expression.parameter("param_2", index=1, data_type="int", size=4)
    positive_value = summarizer._build_affine_progression_sum_closed_expression(
        count_expr=n_expr,
        step=5,
        bias_expr=bias_expr,
        result_size=4,
        signed_count=False,
    )
    assert positive_value is not None
    zero_case = ReturnInfo(
        address="00100104",
        value=_const(0),
        conditions=[Condition(Expression.binary_op("INT_LESS", n_expr, _const(1)), False)],
        branch_index=0,
    )
    positive_case = ReturnInfo(
        address="00100104",
        value=positive_value,
        conditions=[Condition(Expression.binary_op("INT_LESS", _const(0), n_expr), False)],
        branch_index=1,
    )
    literal_probe_case = ReturnInfo(
        address="00100104",
        value=Expression.binary_op("SUBPIECE", Expression.constant(literal_base, size=8), _const(0)),
        conditions=[
            Condition(Expression.binary_op("INT_EQUAL", n_expr, _const(0)), False),
            Condition(Expression.binary_op("INT_LESS", _const(0), n_expr), False),
        ],
        branch_index=2,
    )
    analysis = type("FakeAnalysis", (), {})()
    int_type = _FakeIntDataType()
    analysis.parameters = [
        {"name": "param_1", "index": 0, "data_type": "uint", "data_type_obj": int_type, "size": 4},
        {"name": "param_2", "index": 1, "data_type": "int", "data_type_obj": int_type, "size": 4},
    ]
    analysis.returns = [zero_case, positive_case, literal_probe_case]
    analysis.incomplete_control_flow = False
    analysis.effect_summary = None

    summary = summarizer._try_summarize_vectorized_affine_progression_sum(
        _FakeFunction("f"),
        _FakeCfgHighFunction([]),
        analysis,
    )

    assert summary is not None
    returns, _note = summary
    positive_guard = returns[1].conditions[0]
    assert positive_guard.expression.operator == "INT_LESS"
    runtime_ref = getattr(returns[1].value, "runtime_ref", None)
    assert runtime_ref is not None
    assert runtime_ref.signed_loop is False

def test_vectorized_affine_progression_literal_summary_rejects_signed_local_bias_candidate_mismatch():
    ram_space = _FakeAddressSpace("ram", space_id=1, is_memory=True)
    literal_base = 0x100120
    literal_bytes = bytes(
        byte
        for value in (0, 5, 10, 15)
        for byte in int(value).to_bytes(4, "little", signed=True)
    )
    program = _FakeProgram(
        _FakeAddressFactory({1: ram_space}, default_space=ram_space),
        memory=_FakeMemory(
            [_FakeMemoryBlock(literal_base, literal_base + len(literal_bytes) - 1, execute=False)],
            bytes_by_address={
                literal_base + offset: byte
                for offset, byte in enumerate(literal_bytes)
            },
        ),
    )
    tracer = _FakeTracer("f", _const(0), program=program)
    summarizer = StructuralRecurrenceSummarizer(tracer, debug=False)
    n_expr = Expression.parameter("param_1", index=0, data_type="int", size=4)
    primary_unsigned_bias = Expression.parameter("param_2", index=1, data_type="uint16_t", size=2)
    signed_local_bias = Expression.parameter("param_2", index=1, data_type="short", size=2)
    positive_value = summarizer._build_affine_progression_sum_closed_expression(
        count_expr=n_expr,
        step=5,
        bias_expr=signed_local_bias,
        result_size=4,
    )
    assert positive_value is not None
    analysis = type("FakeAnalysis", (), {})()
    int_type = _FakeIntDataType()
    analysis.parameters = [
        {"name": "param_1", "index": 0, "data_type": "int", "data_type_obj": int_type, "size": 4},
        {"name": "param_2", "index": 1, "data_type": "uint16_t", "data_type_obj": int_type, "size": 2},
    ]
    analysis.returns = [
        ReturnInfo(
            address="00100104",
            value=_const(0),
            conditions=[Condition(Expression.binary_op("INT_SLESS", n_expr, _const(1)), False)],
            branch_index=0,
        ),
        ReturnInfo(
            address="00100104",
            value=positive_value,
            conditions=[Condition(Expression.binary_op("INT_SLESS", _const(0), n_expr), False)],
            branch_index=1,
        ),
        ReturnInfo(
            address="00100104",
            value=Expression.binary_op("SUBPIECE", Expression.constant(literal_base, size=8), _const(0)),
            conditions=[
                Condition(Expression.binary_op("INT_EQUAL", n_expr, _const(0)), False),
                Condition(Expression.binary_op("INT_SLESS", _const(0), n_expr), False),
            ],
            branch_index=2,
        ),
    ]
    analysis.incomplete_control_flow = False
    analysis.effect_summary = None

    assert summarizer._try_summarize_vectorized_affine_progression_sum(
        _FakeFunction("f"),
        _FakeCfgHighFunction([]),
        analysis,
    ) is None
    assert not primary_unsigned_bias.equals(signed_local_bias) or (
        primary_unsigned_bias.data_type != signed_local_bias.data_type
    )

def test_vectorized_affine_progression_literal_summary_rejects_unproved_positive_return():
    ram_space = _FakeAddressSpace("ram", space_id=1, is_memory=True)
    literal_base = 0x100120
    literal_bytes = bytes(
        byte
        for value in (0, 5, 10, 15)
        for byte in int(value).to_bytes(4, "little", signed=True)
    )
    program = _FakeProgram(
        _FakeAddressFactory({1: ram_space}, default_space=ram_space),
        memory=_FakeMemory(
            [_FakeMemoryBlock(literal_base, literal_base + len(literal_bytes) - 1, execute=False)],
            bytes_by_address={
                literal_base + offset: byte
                for offset, byte in enumerate(literal_bytes)
            },
        ),
    )
    tracer = _FakeTracer("f", _const(0), program=program)
    summarizer = StructuralRecurrenceSummarizer(tracer, debug=False)
    n_expr = Expression.parameter("param_1", index=0, data_type="int", size=4)
    analysis = type("FakeAnalysis", (), {})()
    int_type = _FakeIntDataType()
    analysis.parameters = [
        {"name": "param_1", "index": 0, "data_type": "uint", "data_type_obj": int_type, "size": 4},
        {"name": "param_2", "index": 1, "data_type": "int", "data_type_obj": int_type, "size": 4},
    ]
    analysis.returns = [
        ReturnInfo(
            address="00100104",
            value=_const(0),
            conditions=[Condition(Expression.binary_op("INT_LESS", n_expr, _const(1)), False)],
            branch_index=0,
        ),
        ReturnInfo(
            address="00100104",
            value=Expression.binary_op(
                "INT_ADD",
                Expression.parameter("param_2", index=1, data_type="int", size=4),
                Expression.binary_op("SUBPIECE", Expression.constant(literal_base, size=8), _const(0)),
            ),
            conditions=[Condition(Expression.binary_op("INT_SLESS", _const(0), n_expr), False)],
            branch_index=1,
        ),
    ]
    analysis.incomplete_control_flow = False
    analysis.effect_summary = None

    assert summarizer._try_summarize_vectorized_affine_progression_sum(
        _FakeFunction("f"),
        _FakeCfgHighFunction([]),
        analysis,
    ) is None

def test_vectorized_affine_progression_literal_summary_rejects_unknown_positive_overlap():
    ram_space = _FakeAddressSpace("ram", space_id=1, is_memory=True)
    literal_base = 0x100120
    literal_bytes = bytes(
        byte
        for value in (0, 5, 10, 15)
        for byte in int(value).to_bytes(4, "little", signed=True)
    )
    program = _FakeProgram(
        _FakeAddressFactory({1: ram_space}, default_space=ram_space),
        memory=_FakeMemory(
            [_FakeMemoryBlock(literal_base, literal_base + len(literal_bytes) - 1, execute=False)],
            bytes_by_address={
                literal_base + offset: byte
                for offset, byte in enumerate(literal_bytes)
            },
        ),
    )
    tracer = _FakeTracer("f", _const(0), program=program)
    summarizer = StructuralRecurrenceSummarizer(tracer, debug=False)
    n_expr = Expression.parameter("param_1", index=0, data_type="int", size=4)
    bias_expr = Expression.parameter("param_2", index=1, data_type="int", size=4)
    positive_value = summarizer._build_affine_progression_sum_closed_expression(
        count_expr=n_expr,
        step=5,
        bias_expr=bias_expr,
        result_size=4,
    )
    assert positive_value is not None
    opaque_guard = Expression.binary_op(
        "INT_SLESS",
        Expression.constant(0, size=4),
        Expression.variable("opaque_positive_guard", size=4),
    )
    analysis = type("FakeAnalysis", (), {})()
    int_type = _FakeIntDataType()
    analysis.parameters = [
        {"name": "param_1", "index": 0, "data_type": "int", "data_type_obj": int_type, "size": 4},
        {"name": "param_2", "index": 1, "data_type": "int", "data_type_obj": int_type, "size": 4},
    ]
    analysis.returns = [
        ReturnInfo(
            address="00100104",
            value=_const(0),
            conditions=[Condition(Expression.binary_op("INT_LESS", n_expr, _const(1)), False)],
            branch_index=0,
        ),
        ReturnInfo(
            address="00100104",
            value=positive_value,
            conditions=[Condition(Expression.binary_op("INT_SLESS", _const(0), n_expr), False)],
            branch_index=1,
        ),
        ReturnInfo(
            address="00100104",
            value=_const(123),
            conditions=[Condition(opaque_guard, False)],
            branch_index=2,
        ),
        ReturnInfo(
            address="00100104",
            value=Expression.binary_op("SUBPIECE", Expression.constant(literal_base, size=8), _const(0)),
            conditions=[
                Condition(Expression.binary_op("INT_EQUAL", n_expr, _const(0)), False),
                Condition(Expression.binary_op("INT_SLESS", _const(0), n_expr), False),
            ],
            branch_index=3,
        ),
    ]
    analysis.incomplete_control_flow = False
    analysis.effect_summary = None

    assert summarizer._try_summarize_vectorized_affine_progression_sum(
        _FakeFunction("f"),
        _FakeCfgHighFunction([]),
        analysis,
    ) is None

def test_vectorized_affine_progression_literal_summary_rejects_incomplete_zero_base_cover():
    ram_space = _FakeAddressSpace("ram", space_id=1, is_memory=True)
    literal_base = 0x100120
    literal_bytes = bytes(
        byte
        for value in (0, 5, 10, 15)
        for byte in int(value).to_bytes(4, "little", signed=True)
    )
    program = _FakeProgram(
        _FakeAddressFactory({1: ram_space}, default_space=ram_space),
        memory=_FakeMemory(
            [_FakeMemoryBlock(literal_base, literal_base + len(literal_bytes) - 1, execute=False)],
            bytes_by_address={
                literal_base + offset: byte
                for offset, byte in enumerate(literal_bytes)
            },
        ),
    )
    tracer = _FakeTracer("f", _const(0), program=program)
    summarizer = StructuralRecurrenceSummarizer(tracer, debug=False)
    n_expr = Expression.parameter("param_1", index=0, data_type="int", size=4)
    bias_expr = Expression.parameter("param_2", index=1, data_type="int", size=4)
    positive_value = summarizer._build_affine_progression_sum_closed_expression(
        count_expr=n_expr,
        step=5,
        bias_expr=bias_expr,
        result_size=4,
    )
    assert positive_value is not None
    analysis = type("FakeAnalysis", (), {})()
    int_type = _FakeIntDataType()
    analysis.parameters = [
        {"name": "param_1", "index": 0, "data_type": "int", "data_type_obj": int_type, "size": 4},
        {"name": "param_2", "index": 1, "data_type": "int", "data_type_obj": int_type, "size": 4},
    ]
    analysis.returns = [
        ReturnInfo(
            address="00100104",
            value=_const(0),
            conditions=[Condition(Expression.binary_op("INT_EQUAL", n_expr, _const(0)), False)],
            branch_index=0,
        ),
        ReturnInfo(
            address="00100104",
            value=_const(7),
            conditions=[Condition(Expression.binary_op("INT_SLESS", n_expr, _const(0)), False)],
            branch_index=1,
        ),
        ReturnInfo(
            address="00100104",
            value=positive_value,
            conditions=[Condition(Expression.binary_op("INT_SLESS", _const(0), n_expr), False)],
            branch_index=2,
        ),
    ]
    analysis.incomplete_control_flow = False
    analysis.effect_summary = None

    assert summarizer._try_summarize_vectorized_affine_progression_sum(
        _FakeFunction("f"),
        _FakeCfgHighFunction([]),
        analysis,
    ) is None

def test_vectorized_affine_progression_literal_summary_rejects_nonzero_base_overlap():
    ram_space = _FakeAddressSpace("ram", space_id=1, is_memory=True)
    literal_base = 0x100120
    literal_bytes = bytes(
        byte
        for value in (0, 5, 10, 15)
        for byte in int(value).to_bytes(4, "little", signed=True)
    )
    program = _FakeProgram(
        _FakeAddressFactory({1: ram_space}, default_space=ram_space),
        memory=_FakeMemory(
            [_FakeMemoryBlock(literal_base, literal_base + len(literal_bytes) - 1, execute=False)],
            bytes_by_address={
                literal_base + offset: byte
                for offset, byte in enumerate(literal_bytes)
            },
        ),
    )
    tracer = _FakeTracer("f", _const(0), program=program)
    summarizer = StructuralRecurrenceSummarizer(tracer, debug=False)
    n_expr = Expression.parameter("param_1", index=0, data_type="int", size=4)
    bias_expr = Expression.parameter("param_2", index=1, data_type="int", size=4)
    positive_value = summarizer._build_affine_progression_sum_closed_expression(
        count_expr=n_expr,
        step=5,
        bias_expr=bias_expr,
        result_size=4,
    )
    assert positive_value is not None
    analysis = type("FakeAnalysis", (), {})()
    int_type = _FakeIntDataType()
    analysis.parameters = [
        {"name": "param_1", "index": 0, "data_type": "int", "data_type_obj": int_type, "size": 4},
        {"name": "param_2", "index": 1, "data_type": "int", "data_type_obj": int_type, "size": 4},
    ]
    analysis.returns = [
        ReturnInfo(
            address="00100104",
            value=_const(0),
            conditions=[Condition(Expression.binary_op("INT_SLESS", n_expr, _const(1)), False)],
            branch_index=0,
        ),
        ReturnInfo(
            address="00100104",
            value=_const(7),
            conditions=[Condition(Expression.binary_op("INT_SLESS", n_expr, _const(0)), False)],
            branch_index=1,
        ),
        ReturnInfo(
            address="00100104",
            value=positive_value,
            conditions=[Condition(Expression.binary_op("INT_SLESS", _const(0), n_expr), False)],
            branch_index=2,
        ),
    ]
    analysis.incomplete_control_flow = False
    analysis.effect_summary = None

    assert summarizer._try_summarize_vectorized_affine_progression_sum(
        _FakeFunction("f"),
        _FakeCfgHighFunction([]),
        analysis,
    ) is None

def test_vectorized_affine_progression_literal_summary_rejects_memory_effects():
    ram_space = _FakeAddressSpace("ram", space_id=1, is_memory=True)
    literal_base = 0x100120
    literal_bytes = bytes(
        byte
        for value in (0, 5, 10, 15)
        for byte in int(value).to_bytes(4, "little", signed=True)
    )
    program = _FakeProgram(
        _FakeAddressFactory({1: ram_space}, default_space=ram_space),
        memory=_FakeMemory(
            [_FakeMemoryBlock(literal_base, literal_base + len(literal_bytes) - 1, execute=False)],
            bytes_by_address={
                literal_base + offset: byte
                for offset, byte in enumerate(literal_bytes)
            },
        ),
    )
    summarizer = StructuralRecurrenceSummarizer(
        _FakeTracer("f", _const(0), program=program),
        debug=False,
    )
    n_expr = Expression.parameter("param_1", index=0, data_type="int", size=4)
    bias_expr = Expression.parameter("param_2", index=1, data_type="int", size=4)
    positive_value = summarizer._build_affine_progression_sum_closed_expression(
        count_expr=n_expr,
        step=5,
        bias_expr=bias_expr,
        result_size=4,
    )
    assert positive_value is not None
    analysis = type("FakeAnalysis", (), {})()
    int_type = _FakeIntDataType()
    analysis.parameters = [
        {"name": "param_1", "index": 0, "data_type": "int", "data_type_obj": int_type, "size": 4},
        {"name": "param_2", "index": 1, "data_type": "int", "data_type_obj": int_type, "size": 4},
    ]
    analysis.returns = [
        ReturnInfo(
            address="00100104",
            value=_const(0),
            conditions=[Condition(Expression.binary_op("INT_LESS", n_expr, _const(1)), False)],
            branch_index=0,
        ),
        ReturnInfo(
            address="00100104",
            value=positive_value,
            conditions=[Condition(Expression.binary_op("INT_SLESS", _const(0), n_expr), False)],
            branch_index=1,
        ),
    ]
    analysis.incomplete_control_flow = False
    analysis.effect_summary = EffectSummary(
        parameter_names=["param_1", "param_2"],
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

    assert summarizer._try_summarize_vectorized_affine_progression_sum(
        _FakeFunction("f"),
        _FakeCfgHighFunction([]),
        analysis,
    ) is None

def test_vectorized_affine_progression_literal_summary_rejects_high_function_effects():
    ram_space = _FakeAddressSpace("ram", space_id=1, is_memory=True)
    literal_base = 0x100120
    literal_bytes = bytes(
        byte
        for value in (0, 5, 10, 15)
        for byte in int(value).to_bytes(4, "little", signed=True)
    )
    program = _FakeProgram(
        _FakeAddressFactory({1: ram_space}, default_space=ram_space),
        memory=_FakeMemory(
            [_FakeMemoryBlock(literal_base, literal_base + len(literal_bytes) - 1, execute=False)],
            bytes_by_address={
                literal_base + offset: byte
                for offset, byte in enumerate(literal_bytes)
            },
        ),
    )
    summarizer = StructuralRecurrenceSummarizer(
        _FakeTracer("f", _const(0), program=program),
        debug=False,
    )
    n_expr = Expression.parameter("param_1", index=0, data_type="int", size=4)
    bias_expr = Expression.parameter("param_2", index=1, data_type="int", size=4)
    positive_value = summarizer._build_affine_progression_sum_closed_expression(
        count_expr=n_expr,
        step=5,
        bias_expr=bias_expr,
        result_size=4,
    )
    assert positive_value is not None
    analysis = type("FakeAnalysis", (), {})()
    int_type = _FakeIntDataType()
    analysis.parameters = [
        {"name": "param_1", "index": 0, "data_type": "int", "data_type_obj": int_type, "size": 4},
        {"name": "param_2", "index": 1, "data_type": "int", "data_type_obj": int_type, "size": 4},
    ]
    analysis.returns = [
        ReturnInfo(
            address="00100104",
            value=_const(0),
            conditions=[Condition(Expression.binary_op("INT_LESS", n_expr, _const(1)), False)],
            branch_index=0,
        ),
        ReturnInfo(
            address="00100104",
            value=positive_value,
            conditions=[Condition(Expression.binary_op("INT_SLESS", _const(0), n_expr), False)],
            branch_index=1,
        ),
        ReturnInfo(
            address="00100104",
            value=Expression.binary_op("SUBPIECE", Expression.constant(literal_base, size=8), _const(0)),
            conditions=[
                Condition(Expression.binary_op("INT_EQUAL", n_expr, _const(0)), False),
                Condition(Expression.binary_op("INT_SLESS", _const(0), n_expr), False),
            ],
            branch_index=2,
        ),
    ]
    analysis.incomplete_control_flow = False
    analysis.effect_summary = None
    store_op = _FakePcodeOp(
        "STORE",
        [
            _FakeStoreSpaceVarnode(target_space_id=1),
            _FakeVarnode("store_addr", expr=n_expr),
            _FakeVarnode("store_value", expr=_const(1)),
        ],
    )
    call_op = _FakePcodeOp("CALL", [_FakeVarnode("call_target")])
    branchind_op = _FakePcodeOp("BRANCHIND", [_FakeVarnode("branch_target")])

    for op in (store_op, call_op, branchind_op):
        assert summarizer._try_summarize_vectorized_affine_progression_sum(
            _FakeFunction("f"),
            _FakeCfgHighFunction([_FakeCfgBlock(1, [op])]),
            analysis,
        ) is None

def test_vectorized_affine_progression_literal_summary_rejects_missing_zero_base_case():
    ram_space = _FakeAddressSpace("ram", space_id=1, is_memory=True)
    literal_base = 0x100120
    literal_bytes = bytes(
        byte
        for value in (0, 5, 10, 15)
        for byte in int(value).to_bytes(4, "little", signed=True)
    )
    program = _FakeProgram(
        _FakeAddressFactory({1: ram_space}, default_space=ram_space),
        memory=_FakeMemory(
            [_FakeMemoryBlock(literal_base, literal_base + len(literal_bytes) - 1, execute=False)],
            bytes_by_address={
                literal_base + offset: byte
                for offset, byte in enumerate(literal_bytes)
            },
        ),
    )
    tracer = _FakeTracer("f", _const(0), program=program)
    summarizer = StructuralRecurrenceSummarizer(tracer, debug=False)
    analysis = type("FakeAnalysis", (), {})()
    int_type = _FakeIntDataType()
    analysis.parameters = [
        {"name": "param_1", "index": 0, "data_type": "int", "data_type_obj": int_type, "size": 4},
        {"name": "param_2", "index": 1, "data_type": "int", "data_type_obj": int_type, "size": 4},
    ]
    analysis.returns = [
        ReturnInfo(
            address="00100104",
            value=Expression.binary_op(
                "INT_ADD",
                Expression.parameter("param_2", index=1, data_type="int", size=4),
                Expression.binary_op("SUBPIECE", Expression.constant(literal_base, size=8), _const(0)),
            ),
            conditions=[],
            branch_index=0,
        )
    ]
    analysis.incomplete_control_flow = False
    analysis.effect_summary = None

    assert summarizer._try_summarize_vectorized_affine_progression_sum(
        _FakeFunction("f"),
        _FakeCfgHighFunction([]),
        analysis,
    ) is None

def test_readonly_loop_summary_preserves_non_unit_index_step_object_centrically():
    summarizer = StructuralRecurrenceSummarizer(_FakeTracer("unused", _const(0)), debug=False)
    count_expr = Expression.parameter("count", index=1, data_type="int", size=4)
    pointer_base_ref = LocationBaseRef.parameter("ptr", index=0)
    proof = _readonly_accumulator_proof(
        base_ref=pointer_base_ref,
        count_expr=count_expr,
        stride=8,
        element_size=4,
        start_index=0,
        index_step=2,
        index_scale=4,
    )

    summary = proof.with_runtime_evidence(
        limit_expr=count_expr,
        result_size=4,
        loop_body_witnesses=(),
        exact_return_witnesses=(),
        guard_constraints=(),
        signed_counter=True,
    ).lower_to_loop_summary_ref()
    witnesses = summarizer._synthesize_linear_readonly_reduction_witnesses(
        {"name": "ptr", "index": 0},
        proof,
        result_size=4,
    )

    assert summary is not None
    assert summary.start_expr.value == 0
    assert summary.step_expr.value == 2
    assert summary.term_descriptor.stride == 4
    assert summarizer._readonly_loop_trip_count_for_count_value(proof, 5) == 3
    count_five = next(witness for witness in witnesses if witness.exact_count == 5)
    assert [term.byte_offset for term in count_five.terms] == [0, 8, 16]

def test_readonly_exact_positive_return_order_prefers_self_consistent_prefix_terms():
    summarizer = StructuralRecurrenceSummarizer(PcodeTracer.__new__(PcodeTracer), debug=False)
    pointer_param = {"name": "param_1", "index": 0, "data_type": "int *", "size": 8}
    count_param = {"name": "param_2", "index": 1, "data_type": "int", "size": 4}
    analysis = create_mock_analysis(
        function_name="lmb_sum_prefix_wrong_tail",
        parameters=[pointer_param, count_param],
        returns=[],
    )
    count_expr = Expression.parameter("param_2", index=1, data_type="int", size=4)
    proof = _readonly_accumulator_proof(
        base_ref=LocationBaseRef.parameter("param_1", index=0),
        count_expr=count_expr,
        stride=4,
        element_size=4,
        result_size=4,
        witnesses=(
            ReadonlyReductionWitness(
                exact_count=3,
                terms=(
                    ReadonlyReductionTermRef(byte_offset=0, access_size=4),
                    ReadonlyReductionTermRef(byte_offset=4, access_size=4),
                    ReadonlyReductionTermRef(byte_offset=8, access_size=4),
                ),
            ),
        ),
    )
    conditions = [_cond("INT_EQUAL", count_expr, _const(3))]
    wrong_tail_artifact = ReturnInfo(
        address="0x3000",
        value=_sum_terms(
            _mem_ptradd_index("param_1", 0),
            _mem_ptradd_index("param_1", 2),
            _mem_ptradd_index("param_1", 3),
        ),
        conditions=conditions,
        branch_index=10,
    )
    exact_prefix = ReturnInfo(
        address="0x3000",
        value=_sum_terms(
            _mem_ptradd_index("param_1", 1),
            _mem_ptradd_index("param_1", 0),
            _mem_ptradd_index("param_1", 2),
        ),
        conditions=conditions,
        branch_index=11,
    )

    ordered = summarizer._order_readonly_exact_positive_returns(
        [wrong_tail_artifact, exact_prefix],
        analysis,
        pointer_param,
        count_param,
        proof,
    )

    assert ordered[0] is exact_prefix
    assert summarizer._readonly_exact_positive_return_prefix_score(
        analysis,
        pointer_param,
        exact_prefix,
        proof,
        exact_count=3,
    ) > summarizer._readonly_exact_positive_return_prefix_score(
        analysis,
        pointer_param,
        wrong_tail_artifact,
        proof,
        exact_count=3,
    )

def test_readonly_witness_synthesis_materializes_excluded_exact_prefix_count():
    summarizer = StructuralRecurrenceSummarizer(PcodeTracer.__new__(PcodeTracer), debug=False)
    pointer_param = {"name": "param_1", "index": 0, "data_type": "int *", "size": 8}
    count_param = {"name": "param_2", "index": 1, "data_type": "int", "size": 4}
    analysis = create_mock_analysis(
        function_name="lmb_sum_prefix_wrong_tail",
        parameters=[pointer_param, count_param],
        returns=[],
    )
    count_expr = Expression.parameter("param_2", index=1, data_type="int", size=4)
    witnesses = (
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
        ReadonlyReductionWitness(
            exact_count=3,
            terms=(
                ReadonlyReductionTermRef(byte_offset=0, access_size=4),
                ReadonlyReductionTermRef(byte_offset=4, access_size=4),
                ReadonlyReductionTermRef(byte_offset=8, access_size=4),
            ),
        ),
        ReadonlyReductionWitness(
            exact_count=4,
            terms=(
                ReadonlyReductionTermRef(byte_offset=0, access_size=4),
                ReadonlyReductionTermRef(byte_offset=4, access_size=4),
                ReadonlyReductionTermRef(byte_offset=8, access_size=4),
                ReadonlyReductionTermRef(byte_offset=12, access_size=4),
            ),
        ),
    )
    reduction_ref = ReadonlyReductionRef(
        reduction_kind="memory_sum",
        pointer_base_ref=LocationBaseRef.parameter("param_1", index=0),
        count_parameter_name="param_2",
        count_parameter_index=1,
        stride=4,
        element_size=4,
        result_size=4,
        semantic_witnesses=witnesses,
    )
    existing = [
        ReturnInfo(
            address="0x3000",
            value=_sum_terms(_mem_ptradd_index("param_1", 0), _mem_ptradd_index("param_1", 1)),
            conditions=[
                _cond("INT_EQUAL", count_expr, _const(2)),
            ],
            branch_index=20,
        )
    ]

    synthesized = summarizer._synthesize_exact_returns_from_readonly_witnesses(
        analysis,
        pointer_param,
        count_param,
        broad_positive_conditions=[_cond("INT_SLESSEQUAL", _const(1), count_expr)],
        summary_positive_conditions=[
            _cond("INT_SLESS", _const(3), count_expr),
        ],
        existing_returns=existing,
        reduction_ref=reduction_ref,
        result_size=4,
    )

    exact_count_values = [
        summarizer._exact_counter_value_from_conditions(ret.conditions or [], "param_2")
        for ret in synthesized
    ]
    assert 3 in exact_count_values
    assert 4 not in exact_count_values

def test_structural_recurrence_summarizer_recovers_readonly_pointer_reduction_summary():
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
    count_param = _FakeVarnode(
        "param_2",
        size=4,
        expr=Expression.parameter("param_2", index=1, data_type="int", size=4),
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
    assert len(summarized_returns) == 3
    positive_case = next(ret for ret in summarized_returns if ret.value.expr_type == ret.value.expr_type.__class__.INTRINSIC)
    assert positive_case.value.opcode == READONLY_SUM_OPCODE
    assert isinstance(positive_case.value.runtime_ref, ReadonlyReductionRef)
    assert positive_case.value.runtime_ref.stride == 4
    assert positive_case.value.runtime_ref.element_size == 4
    assert positive_case.conditions[0].to_string() == "(param_1 != 0)"
    assert positive_case.conditions[1].to_string() == "(0 < param_2)"
