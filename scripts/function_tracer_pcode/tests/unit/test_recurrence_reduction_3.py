from scripts.function_tracer_pcode.tests.unit._recurrence_fixtures import *

def test_readonly_reduction_candidate_normalizes_until_true_fixpoint(monkeypatch):
    summarizer = StructuralRecurrenceSummarizer(tracer=None, debug=False)
    pointer_param = {"name": "param_1", "index": 0, "data_type": "int *", "size": 8, "is_signed": False}
    count_param = {"name": "param_2", "index": 1, "data_type": "int", "size": 4, "is_signed": True}
    count_expr = Expression.parameter("param_2", index=1, data_type="int", size=4)
    broad_ret = ReturnInfo(
        address="0x1400",
        conditions=[
            _cond("INT_NOTEQUAL", _param("param_1", size=8), _const(0, size=8)),
            _cond("INT_SLESS", _const(0), count_expr),
        ],
        value=Expression.unknown("phi_circular"),
    )
    analysis = FunctionReturnAnalysis(
        function_name="readonly_fixpoint_normalization_like",
        entry_point="0x1400",
        parameters=[pointer_param, count_param],
        returns=[broad_ret],
    )
    proof = _readonly_accumulator_proof(
        base_ref=LocationBaseRef.parameter("param_1", index=0),
        count_expr=count_expr,
        stride=4,
        element_size=4,
        start_offset=16,
        start_index=4,
    )

    def fake_with_runtime_evidence(
        self,
        *,
        limit_expr,
        result_size,
        loop_body_witnesses,
        exact_return_witnesses,
        guard_constraints,
        signed_counter,
    ):
        next_start = max(0, int(self.start_index) - 1)
        return replace(
            self,
            limit_expr=limit_expr,
            result_size=result_size,
            loop_body_witnesses=tuple(loop_body_witnesses),
            exact_return_witnesses=tuple(exact_return_witnesses),
            guard_constraints=tuple(guard_constraints),
            signed_counter=bool(signed_counter),
            start_index=next_start,
            start_offset=next_start * 4,
        )

    monkeypatch.setattr(ReductionAccumulatorProof, "with_runtime_evidence", fake_with_runtime_evidence)
    monkeypatch.setattr(
        summarizer,
        "_extract_readonly_reduction_exact_witnesses",
        lambda *_args, **_kwargs: (),
    )
    monkeypatch.setattr(
        summarizer,
        "_build_readonly_reduction_semantic_witnesses",
        lambda *_args, **_kwargs: (),
    )
    monkeypatch.setattr(
        summarizer,
        "_readonly_reduction_positive_conditions",
        lambda _analysis, _pointer_param, _count_param, loop_start_index=0, signed_counter=True: [
            _cond("INT_NOTEQUAL", _param("param_1", size=8), _const(0, size=8)),
            _cond("INT_SLESS", _const(int(loop_start_index)), count_expr),
        ],
    )
    monkeypatch.setattr(
        summarizer,
        "_readonly_reduction_replaceable_positive_returns",
        lambda *_args, **_kwargs: [broad_ret],
    )

    normalized = summarizer._normalize_readonly_reduction_candidate(
        analysis,
        pointer_param,
        count_param,
        broad_positive_conditions=[
            _cond("INT_NOTEQUAL", _param("param_1", size=8), _const(0, size=8)),
            _cond("INT_SLESS", _const(0), count_expr),
        ],
        positive_conditions=[
            _cond("INT_NOTEQUAL", _param("param_1", size=8), _const(0, size=8)),
            _cond("INT_SLESS", _const(4), count_expr),
        ],
        counter_signed=True,
        accumulator_proof=proof,
        overlapping_positive_returns=[broad_ret],
    )

    assert normalized is not None
    normalized_proof, normalized_conditions, normalized_returns, *_rest = normalized
    assert normalized_proof.start_index == 0
    assert [condition.to_string() for condition in normalized_conditions] == [
        "(param_1 != 0)",
        "(0 < param_2)",
    ]
    assert normalized_returns == [broad_ret]

def test_readonly_reduction_candidate_declines_non_convergent_normalization(monkeypatch):
    summarizer = StructuralRecurrenceSummarizer(tracer=None, debug=False)
    pointer_param = {"name": "param_1", "index": 0, "data_type": "int *", "size": 8, "is_signed": False}
    count_param = {"name": "param_2", "index": 1, "data_type": "int", "size": 4, "is_signed": True}
    count_expr = Expression.parameter("param_2", index=1, data_type="int", size=4)
    broad_ret = ReturnInfo(
        address="0x1410",
        conditions=[
            _cond("INT_NOTEQUAL", _param("param_1", size=8), _const(0, size=8)),
            _cond("INT_SLESS", _const(0), count_expr),
        ],
        value=Expression.unknown("phi_circular"),
    )
    analysis = FunctionReturnAnalysis(
        function_name="readonly_fixpoint_cycle_like",
        entry_point="0x1410",
        parameters=[pointer_param, count_param],
        returns=[broad_ret],
    )
    proof = _readonly_accumulator_proof(
        base_ref=LocationBaseRef.parameter("param_1", index=0),
        count_expr=count_expr,
        stride=4,
        element_size=4,
        start_offset=8,
        start_index=2,
    )

    def fake_with_runtime_evidence(
        self,
        *,
        limit_expr,
        result_size,
        loop_body_witnesses,
        exact_return_witnesses,
        guard_constraints,
        signed_counter,
    ):
        next_start = 1 if int(self.start_index) == 2 else 2
        return replace(
            self,
            limit_expr=limit_expr,
            result_size=result_size,
            loop_body_witnesses=tuple(loop_body_witnesses),
            exact_return_witnesses=tuple(exact_return_witnesses),
            guard_constraints=tuple(guard_constraints),
            signed_counter=bool(signed_counter),
            start_index=next_start,
            start_offset=next_start * 4,
        )

    monkeypatch.setattr(ReductionAccumulatorProof, "with_runtime_evidence", fake_with_runtime_evidence)
    monkeypatch.setattr(
        summarizer,
        "_extract_readonly_reduction_exact_witnesses",
        lambda *_args, **_kwargs: (),
    )
    monkeypatch.setattr(
        summarizer,
        "_build_readonly_reduction_semantic_witnesses",
        lambda *_args, **_kwargs: (),
    )
    monkeypatch.setattr(
        summarizer,
        "_readonly_reduction_positive_conditions",
        lambda _analysis, _pointer_param, _count_param, loop_start_index=0, signed_counter=True: [
            _cond("INT_NOTEQUAL", _param("param_1", size=8), _const(0, size=8)),
            _cond("INT_SLESS", _const(int(loop_start_index)), count_expr),
        ],
    )
    monkeypatch.setattr(
        summarizer,
        "_readonly_reduction_replaceable_positive_returns",
        lambda *_args, **_kwargs: [broad_ret],
    )

    assert summarizer._normalize_readonly_reduction_candidate(
        analysis,
        pointer_param,
        count_param,
        broad_positive_conditions=[
            _cond("INT_NOTEQUAL", _param("param_1", size=8), _const(0, size=8)),
            _cond("INT_SLESS", _const(0), count_expr),
        ],
        positive_conditions=[
            _cond("INT_NOTEQUAL", _param("param_1", size=8), _const(0, size=8)),
            _cond("INT_SLESS", _const(2), count_expr),
        ],
        counter_signed=True,
        accumulator_proof=proof,
        overlapping_positive_returns=[broad_ret],
    ) is None

def test_readonly_addend_proof_rejects_signed_extension_behind_copy():
    pointer_param = {"name": "param_1", "index": 0, "data_type": "char *", "size": 8}
    phi_vn = _FakeVarnode("ptr_phi", size=8)
    ram_space = _FakeVarnode("ram", size=8, expr=Expression.constant(0, size=8))
    load_vn = _FakeVarnode("load", size=1)
    sext_vn = _FakeVarnode("sext_load", size=4)
    copy_vn = _FakeVarnode("copy_sext_load", size=4)
    _FakePcodeOp("LOAD", [ram_space, phi_vn], load_vn)
    _FakePcodeOp("INT_SEXT", [load_vn], sext_vn)
    _FakePcodeOp("COPY", [sext_vn], copy_vn)
    tracer = _FakeTracer("unused", Expression.unknown("unknown"))
    tracer.trace_varnode = lambda varnode, *args, **kwargs: getattr(varnode, "_expr", None)
    summarizer = StructuralRecurrenceSummarizer(tracer, debug=False)

    progressions = summarizer._collect_load_progressions_from_varnode(
        copy_vn,
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

def test_readonly_addend_proof_preserves_subpiece_behind_copy():
    pointer_param = {"name": "param_1", "index": 0, "data_type": "int *", "size": 8}
    phi_vn = _FakeVarnode("ptr_phi", size=8)
    ram_space = _FakeVarnode("ram", size=8, expr=Expression.constant(0, size=8))
    load_vn = _FakeVarnode("load", size=4)
    offset_vn = _FakeVarnode("offset", size=4, expr=Expression.constant(1, size=4))
    subpiece_vn = _FakeVarnode("subpiece", size=2)
    copy_vn = _FakeVarnode("copy_subpiece", size=2)
    mask_vn = _FakeVarnode("mask", size=4, expr=Expression.constant(0xFF, size=4))
    masked_copy_vn = _FakeVarnode("masked_copy_subpiece", size=2)
    _FakePcodeOp("LOAD", [ram_space, phi_vn], load_vn)
    _FakePcodeOp("SUBPIECE", [load_vn, offset_vn], subpiece_vn)
    _FakePcodeOp("COPY", [subpiece_vn], copy_vn)
    _FakePcodeOp("INT_AND", [copy_vn, mask_vn], masked_copy_vn)
    tracer = _FakeTracer("unused", Expression.unknown("unknown"))
    tracer.trace_varnode = lambda varnode, *args, **kwargs: getattr(varnode, "_expr", None)
    summarizer = StructuralRecurrenceSummarizer(tracer, debug=False)
    pointer_phis = [
        {
            "phi_op": _FakePcodeOp("MULTIEQUAL", [], phi_vn),
            "phi_output": phi_vn,
            "stride": 4,
            "start_offset": 0,
            "start_index": 0,
            "index_step": 1,
            "index_scale": 4,
        }
    ]

    progressions = summarizer._collect_load_progressions_from_varnode(
        copy_vn,
        pointer_param,
        pointer_phis,
        [],
    )
    masked_progressions = summarizer._collect_load_progressions_from_varnode(
        masked_copy_vn,
        pointer_param,
        pointer_phis,
        [],
    )

    assert progressions is not None
    assert progressions[0]["start_offset"] == 1
    assert progressions[0]["element_size"] == 2
    assert masked_progressions is not None
    assert masked_progressions[0]["start_offset"] == 1
    assert masked_progressions[0]["element_size"] == 1

def test_readonly_addend_proof_reflects_mask_and_subpiece_access_size():
    pointer_param = {"name": "param_1", "index": 0, "data_type": "int *", "size": 8}
    phi_vn = _FakeVarnode("ptr_phi", size=8)
    ram_space = _FakeVarnode("ram", size=8, expr=Expression.constant(0, size=8))
    load_vn = _FakeVarnode("load", size=4)
    mask_vn = _FakeVarnode("mask", size=4, expr=Expression.constant(0xFF, size=4))
    masked_vn = _FakeVarnode("masked", size=4)
    offset_vn = _FakeVarnode("offset", size=4, expr=Expression.constant(1, size=4))
    subpiece_vn = _FakeVarnode("subpiece", size=2)
    _FakePcodeOp("LOAD", [ram_space, phi_vn], load_vn)
    _FakePcodeOp("INT_AND", [load_vn, mask_vn], masked_vn)
    _FakePcodeOp("SUBPIECE", [load_vn, offset_vn], subpiece_vn)
    pointer_phis = [
        {
            "phi_op": _FakePcodeOp("MULTIEQUAL", [], phi_vn),
            "phi_output": phi_vn,
            "stride": 4,
            "start_offset": 0,
            "start_index": 0,
            "index_step": 1,
            "index_scale": 4,
        }
    ]
    tracer = _FakeTracer("unused", Expression.unknown("unknown"))
    tracer.trace_varnode = lambda varnode, *args, **kwargs: getattr(varnode, "_expr", None)
    summarizer = StructuralRecurrenceSummarizer(tracer, debug=False)

    masked_progressions = summarizer._collect_load_progressions_from_varnode(
        masked_vn,
        pointer_param,
        pointer_phis,
        [],
    )
    subpiece_progressions = summarizer._collect_load_progressions_from_varnode(
        subpiece_vn,
        pointer_param,
        pointer_phis,
        [],
    )

    assert masked_progressions is not None
    assert masked_progressions[0]["start_offset"] == 0
    assert masked_progressions[0]["element_size"] == 1
    assert subpiece_progressions is not None
    assert subpiece_progressions[0]["start_offset"] == 1
    assert subpiece_progressions[0]["element_size"] == 2

def test_vector_prefix_lanes_must_flow_additively_to_return():
    ptr_expr = Expression.parameter("param_1", index=0, data_type="int *", size=8)
    ptr_vn = _FakeVarnode("param_1", size=8, expr=ptr_expr)
    four_vn = _FakeVarnode("four", size=8, expr=Expression.constant(4, size=8))
    vector_phi = _FakeVarnode("vector_phi", size=8, high=_FakeHighVar("vector_phi"))
    ram_space = _FakeVarnode("ram", size=8, expr=Expression.constant(0, size=8))
    ops = []
    for lane, index_value in enumerate(range(4)):
        index_vn = _FakeVarnode(f"lane_index_{lane}", size=8, expr=Expression.constant(index_value, size=8))
        addr_vn = _FakeVarnode(f"lane_addr_{lane}", size=8)
        value_vn = _FakeVarnode(f"lane_value_{lane}", size=4)
        product_vn = _FakeVarnode(f"product_{lane}", size=4)
        addr_op = _FakePcodeOp("PTRADD", [vector_phi, index_vn, four_vn], addr_vn)
        load_op = _FakePcodeOp("LOAD", [ram_space, addr_vn], value_vn)
        mul_op = _FakePcodeOp("INT_MULT", [value_vn, _FakeVarnode("two", size=4, expr=Expression.constant(2, size=4))], product_vn)
        ops.extend([addr_op, load_op, mul_op])
    return_op = _FakePcodeOp("RETURN", [_FakeVarnode("return_target", size=8), product_vn], None)
    ops.append(return_op)

    tracer = _FakeTracer("unused", Expression.unknown("untraced"))
    tracer.trace_varnode = lambda varnode, *args, **kwargs: getattr(varnode, "_expr", None)
    summarizer = StructuralRecurrenceSummarizer(tracer, debug=False)

    assert not summarizer._vector_prefix_lanes_contribute_additively_to_return(
        ops,
        vector_phi,
        base_offset=0,
        vector_stride=16,
        element_size=4,
    )

def test_vector_prefix_lanes_must_contribute_with_coefficient_one():
    vector_phi = _FakeVarnode("vector_phi", size=8, high=_FakeHighVar("vector_phi"))
    four_vn = _FakeVarnode("four", size=8, expr=Expression.constant(4, size=8))
    ram_space = _FakeVarnode("ram", size=8, expr=Expression.constant(0, size=8))
    running_sum = _FakeVarnode("sum_zero", size=4, expr=Expression.constant(0, size=4))
    ops = []
    for lane, index_value in enumerate(range(4)):
        index_vn = _FakeVarnode(f"lane_index_{lane}", size=8, expr=Expression.constant(index_value, size=8))
        addr_vn = _FakeVarnode(f"lane_addr_{lane}", size=8)
        value_vn = _FakeVarnode(f"lane_value_{lane}", size=4)
        addend_vn = _FakeVarnode(f"lane_addend_{lane}", size=4)
        next_sum = _FakeVarnode(f"sum_after_lane_{lane}", size=4)
        addr_op = _FakePcodeOp("PTRADD", [vector_phi, index_vn, four_vn], addr_vn)
        load_op = _FakePcodeOp("LOAD", [ram_space, addr_vn], value_vn)
        if lane == 0:
            duplicate_op = _FakePcodeOp("INT_ADD", [value_vn, value_vn], addend_vn)
            ops.append(duplicate_op)
        else:
            addend_vn = value_vn
        add_op = _FakePcodeOp("INT_ADD", [running_sum, addend_vn], next_sum)
        ops.extend([addr_op, load_op, add_op])
        running_sum = next_sum
    return_op = _FakePcodeOp("RETURN", [_FakeVarnode("return_target", size=8), running_sum], None)
    ops.append(return_op)

    summarizer = StructuralRecurrenceSummarizer(_FakeTracer("unused", _const(0)), debug=False)

    assert not summarizer._vector_prefix_lanes_contribute_additively_to_return(
        ops,
        vector_phi,
        base_offset=0,
        vector_stride=16,
        element_size=4,
    )

def test_vector_prefix_lanes_reject_duplicate_loads_from_same_offset():
    vector_phi = _FakeVarnode("vector_phi", size=8, high=_FakeHighVar("vector_phi"))
    four_vn = _FakeVarnode("four", size=8, expr=Expression.constant(4, size=8))
    one_vn = _FakeVarnode("one", size=8, expr=Expression.constant(1, size=8))
    ram_space = _FakeVarnode("ram", size=8, expr=Expression.constant(0, size=8))
    lane0_a = _FakeVarnode("lane0_a", size=4)
    lane0_b = _FakeVarnode("lane0_b", size=4)
    lane1_addr = _FakeVarnode("lane1_addr", size=8)
    lane1 = _FakeVarnode("lane1", size=4)
    sum0 = _FakeVarnode("sum0", size=4)
    sum1 = _FakeVarnode("sum1", size=4)
    sum2 = _FakeVarnode("sum2", size=4)
    ops = [
        _FakePcodeOp("LOAD", [ram_space, vector_phi], lane0_a),
        _FakePcodeOp("LOAD", [ram_space, vector_phi], lane0_b),
        _FakePcodeOp("PTRADD", [vector_phi, one_vn, four_vn], lane1_addr),
        _FakePcodeOp("LOAD", [ram_space, lane1_addr], lane1),
        _FakePcodeOp("INT_ADD", [_FakeVarnode("zero", size=4, expr=Expression.constant(0, size=4)), lane0_a], sum0),
        _FakePcodeOp("INT_ADD", [sum0, lane0_b], sum1),
        _FakePcodeOp("INT_ADD", [sum1, lane1], sum2),
        _FakePcodeOp("RETURN", [_FakeVarnode("return_target", size=8), sum2], None),
    ]
    summarizer = StructuralRecurrenceSummarizer(_FakeTracer("unused", _const(0)), debug=False)

    assert not summarizer._vector_prefix_lanes_contribute_additively_to_return(
        ops,
        vector_phi,
        base_offset=0,
        vector_stride=8,
        element_size=4,
    )

def test_vector_prefix_return_term_proof_rejects_duplicated_lane():
    pointer_param = {"name": "param_1", "index": 0, "data_type": "int *", "size": 8}
    analysis = create_mock_analysis(
        "vector_prefix_sum",
        return_type="int",
        parameters=[
            pointer_param,
            {"name": "param_2", "index": 1, "data_type": "int", "size": 4},
        ],
        returns=[
            ReturnInfo(
                address="0x1000",
                value=Expression.binary_op(
                    "INT_ADD",
                    Expression.binary_op("INT_ADD", _mem("param_1", 0), _mem("param_1", 0)),
                    _mem("param_1", 4),
                ),
                conditions=[],
            )
        ],
    )
    summarizer = StructuralRecurrenceSummarizer(_FakeTracer("unused", _const(0)), debug=False)

    assert summarizer._vector_prefix_lanes_have_unit_terms_in_positive_return(
        analysis,
        pointer_param,
        [],
        vector_stride=8,
        element_size=4,
    ) is False

def test_vector_prefix_return_term_proof_requires_all_overlapping_returns():
    pointer_param = {"name": "param_1", "index": 0, "data_type": "int *", "size": 8}
    analysis = create_mock_analysis(
        "vector_prefix_sum",
        return_type="int",
        parameters=[
            pointer_param,
            {"name": "param_2", "index": 1, "data_type": "int", "size": 4},
        ],
        returns=[
            ReturnInfo(
                address="0x1000",
                value=Expression.binary_op("INT_ADD", _mem("param_1", 0), _mem("param_1", 4)),
                conditions=[],
            ),
            ReturnInfo(
                address="0x1004",
                value=Expression.unknown("unproved_vector_body"),
                conditions=[],
            ),
        ],
    )
    summarizer = StructuralRecurrenceSummarizer(_FakeTracer("unused", _const(0)), debug=False)

    assert summarizer._vector_prefix_lanes_have_unit_terms_in_positive_return(
        analysis,
        pointer_param,
        [],
        vector_stride=8,
        element_size=4,
    ) is False

def test_vector_prefix_return_term_proof_rejects_extra_in_base_terms():
    pointer_param = {"name": "param_1", "index": 0, "data_type": "int *", "size": 8}
    analysis = create_mock_analysis(
        "vector_prefix_sum",
        return_type="int",
        parameters=[
            pointer_param,
            {"name": "param_2", "index": 1, "data_type": "int", "size": 4},
        ],
        returns=[
            ReturnInfo(
                address="0x1000",
                value=Expression.binary_op(
                    "INT_ADD",
                    Expression.binary_op("INT_ADD", _mem("param_1", 0), _mem("param_1", 4)),
                    _mem("param_1", 8),
                ),
                conditions=[],
            )
        ],
    )
    summarizer = StructuralRecurrenceSummarizer(_FakeTracer("unused", _const(0)), debug=False)

    assert summarizer._vector_prefix_lanes_have_unit_terms_in_positive_return(
        analysis,
        pointer_param,
        [],
        vector_stride=8,
        element_size=4,
    ) is False

def test_vector_prefix_return_term_proof_rejects_nonzero_constant_bias():
    pointer_param = {"name": "param_1", "index": 0, "data_type": "int *", "size": 8}
    analysis = create_mock_analysis(
        "vector_prefix_sum",
        return_type="int",
        parameters=[
            pointer_param,
            {"name": "param_2", "index": 1, "data_type": "int", "size": 4},
        ],
        returns=[
            ReturnInfo(
                address="0x1000",
                value=Expression.binary_op(
                    "INT_ADD",
                    Expression.binary_op("INT_ADD", _mem("param_1", 0), _mem("param_1", 4)),
                    Expression.constant(5, size=4),
                ),
                conditions=[],
            )
        ],
    )
    summarizer = StructuralRecurrenceSummarizer(_FakeTracer("unused", _const(0)), debug=False)

    assert summarizer._vector_prefix_lanes_have_unit_terms_in_positive_return(
        analysis,
        pointer_param,
        [],
        vector_stride=8,
        element_size=4,
    ) is False

def test_vector_prefix_lanes_reject_multiequal_selection_as_sum():
    vector_phi = _FakeVarnode("vector_phi", size=8, high=_FakeHighVar("vector_phi"))
    four_vn = _FakeVarnode("four", size=8, expr=Expression.constant(4, size=8))
    one_vn = _FakeVarnode("one", size=8, expr=Expression.constant(1, size=8))
    ram_space = _FakeVarnode("ram", size=8, expr=Expression.constant(0, size=8))
    lane0 = _FakeVarnode("lane0", size=4)
    lane1_addr = _FakeVarnode("lane1_addr", size=8)
    lane1 = _FakeVarnode("lane1", size=4)
    selected = _FakeVarnode("selected", size=4)
    ops = [
        _FakePcodeOp("LOAD", [ram_space, vector_phi], lane0),
        _FakePcodeOp("PTRADD", [vector_phi, one_vn, four_vn], lane1_addr),
        _FakePcodeOp("LOAD", [ram_space, lane1_addr], lane1),
        _FakePcodeOp("MULTIEQUAL", [lane0, lane1], selected),
        _FakePcodeOp("RETURN", [_FakeVarnode("return_target", size=8), selected], None),
    ]
    summarizer = StructuralRecurrenceSummarizer(_FakeTracer("unused", _const(0)), debug=False)

    assert not summarizer._vector_prefix_lanes_contribute_additively_to_return(
        ops,
        vector_phi,
        base_offset=0,
        vector_stride=8,
        element_size=4,
    )

def test_vector_prefix_lanes_reject_conditional_accumulator_updates():
    vector_phi = _FakeVarnode("vector_phi", size=8, high=_FakeHighVar("vector_phi"))
    four_vn = _FakeVarnode("four", size=8, expr=Expression.constant(4, size=8))
    one_vn = _FakeVarnode("one", size=8, expr=Expression.constant(1, size=8))
    zero_vn = _FakeVarnode("zero", size=4, expr=Expression.constant(0, size=4))
    ram_space = _FakeVarnode("ram", size=8, expr=Expression.constant(0, size=8))
    lane0 = _FakeVarnode("lane0", size=4)
    lane1_addr = _FakeVarnode("lane1_addr", size=8)
    lane1 = _FakeVarnode("lane1", size=4)
    acc_phi = _FakeVarnode("acc_phi", size=4)
    acc_lane0 = _FakeVarnode("acc_lane0", size=4)
    acc_lane1 = _FakeVarnode("acc_lane1", size=4)
    ops = [
        _FakePcodeOp("LOAD", [ram_space, vector_phi], lane0),
        _FakePcodeOp("PTRADD", [vector_phi, one_vn, four_vn], lane1_addr),
        _FakePcodeOp("LOAD", [ram_space, lane1_addr], lane1),
        _FakePcodeOp("INT_ADD", [acc_phi, lane0], acc_lane0),
        _FakePcodeOp("INT_ADD", [acc_phi, lane1], acc_lane1),
        _FakePcodeOp("MULTIEQUAL", [zero_vn, acc_lane0, acc_lane1], acc_phi),
        _FakePcodeOp("RETURN", [_FakeVarnode("return_target", size=8), acc_phi], None),
    ]
    summarizer = StructuralRecurrenceSummarizer(_FakeTracer("unused", _const(0)), debug=False)

    assert not summarizer._vector_prefix_lanes_contribute_additively_to_return(
        ops,
        vector_phi,
        base_offset=0,
        vector_stride=8,
        element_size=4,
    )

def test_vector_prefix_lanes_reject_single_conditional_accumulator_update():
    vector_phi = _FakeVarnode("vector_phi", size=8, high=_FakeHighVar("vector_phi"))
    four_vn = _FakeVarnode("four", size=8, expr=Expression.constant(4, size=8))
    ram_space = _FakeVarnode("ram", size=8, expr=Expression.constant(0, size=8))
    lane0 = _FakeVarnode("lane0", size=4)
    acc_phi = _FakeVarnode("acc_phi", size=4)
    acc_lane0 = _FakeVarnode("acc_lane0", size=4)
    ops = [
        _FakePcodeOp("LOAD", [ram_space, vector_phi], lane0),
        _FakePcodeOp("INT_ADD", [acc_phi, lane0], acc_lane0),
        _FakePcodeOp("MULTIEQUAL", [acc_phi, acc_lane0], acc_phi),
        _FakePcodeOp("RETURN", [_FakeVarnode("return_target", size=8), acc_phi], None),
    ]
    summarizer = StructuralRecurrenceSummarizer(_FakeTracer("unused", _const(0)), debug=False)

    assert not summarizer._vector_prefix_lanes_contribute_additively_to_return(
        ops,
        vector_phi,
        base_offset=0,
        vector_stride=4,
        element_size=4,
    )

def test_vector_prefix_lanes_reject_copied_pass_through_accumulator_update():
    vector_phi = _FakeVarnode("vector_phi", size=8, high=_FakeHighVar("vector_phi"))
    ram_space = _FakeVarnode("ram", size=8, expr=Expression.constant(0, size=8))
    lane0 = _FakeVarnode("lane0", size=4)
    acc_phi = _FakeVarnode("acc_phi", size=4)
    acc_copy = _FakeVarnode("acc_copy", size=4)
    acc_lane0 = _FakeVarnode("acc_lane0", size=4)
    ops = [
        _FakePcodeOp("LOAD", [ram_space, vector_phi], lane0),
        _FakePcodeOp("COPY", [acc_phi], acc_copy),
        _FakePcodeOp("INT_ADD", [acc_phi, lane0], acc_lane0),
        _FakePcodeOp("MULTIEQUAL", [acc_copy, acc_lane0], acc_phi),
        _FakePcodeOp("RETURN", [_FakeVarnode("return_target", size=8), acc_phi], None),
    ]
    summarizer = StructuralRecurrenceSummarizer(_FakeTracer("unused", _const(0)), debug=False)

    assert not summarizer._vector_prefix_lanes_contribute_additively_to_return(
        ops,
        vector_phi,
        base_offset=0,
        vector_stride=4,
        element_size=4,
    )

def test_vector_prefix_lanes_reject_same_high_pass_through_accumulator_update():
    vector_phi = _FakeVarnode("vector_phi", size=8, high=_FakeHighVar("vector_phi"))
    ram_space = _FakeVarnode("ram", size=8, expr=Expression.constant(0, size=8))
    lane0 = _FakeVarnode("lane0", size=4)
    acc_high = _FakeHighVar("accumulator")
    acc_phi = _FakeVarnode("acc_phi", size=4, high=acc_high)
    acc_pass = _FakeVarnode("acc_pass", size=4, high=acc_high)
    acc_lane0 = _FakeVarnode("acc_lane0", size=4)
    ops = [
        _FakePcodeOp("LOAD", [ram_space, vector_phi], lane0),
        _FakePcodeOp("INT_ADD", [acc_phi, lane0], acc_lane0),
        _FakePcodeOp("MULTIEQUAL", [acc_pass, acc_lane0], acc_phi),
        _FakePcodeOp("RETURN", [_FakeVarnode("return_target", size=8), acc_phi], None),
    ]
    summarizer = StructuralRecurrenceSummarizer(_FakeTracer("unused", _const(0)), debug=False)

    assert not summarizer._vector_prefix_lanes_contribute_additively_to_return(
        ops,
        vector_phi,
        base_offset=0,
        vector_stride=4,
        element_size=4,
    )

def test_vector_prefix_lanes_allow_same_high_cfg_entry_seed():
    vector_phi = _FakeVarnode("vector_phi", size=8, high=_FakeHighVar("vector_phi"))
    ram_space = _FakeVarnode("ram", size=8, expr=Expression.constant(0, size=8))
    lane0 = _FakeVarnode("lane0", size=4)
    acc_high = _FakeHighVar("accumulator")
    acc_seed = _FakeVarnode("acc_seed", size=4, expr=Expression.constant(0, size=4), high=acc_high)
    acc_phi = _FakeVarnode("acc_phi", size=4, high=acc_high)
    acc_lane0 = _FakeVarnode("acc_lane0", size=4)
    load_op = _FakePcodeOp("LOAD", [ram_space, vector_phi], lane0)
    add_op = _FakePcodeOp("INT_ADD", [acc_phi, lane0], acc_lane0)
    phi_op = _FakePcodeOp("MULTIEQUAL", [acc_seed, acc_lane0], acc_phi)
    return_op = _FakePcodeOp("RETURN", [_FakeVarnode("return_target", size=8), acc_phi], None)
    preheader = _FakeCfgBlock(0)
    header = _FakeCfgBlock(1, [phi_op, return_op])
    latch = _FakeCfgBlock(2, [load_op, add_op])
    preheader.add_edge(header)
    header.add_edge(latch)
    latch.add_edge(header)
    summarizer = StructuralRecurrenceSummarizer(_FakeTracer("unused", _const(0)), debug=False)

    assert summarizer._vector_prefix_lanes_contribute_additively_to_return(
        [load_op, add_op, phi_op, return_op],
        vector_phi,
        base_offset=0,
        vector_stride=4,
        element_size=4,
    )

def test_vectorized_readonly_prefix_proof_records_seed_term_count(monkeypatch):
    pointer_param = {"name": "param_1", "index": 0, "data_type": "int *", "size": 8}
    count_param = {"name": "param_2", "index": 1, "data_type": "uint", "size": 4, "is_signed": False}
    analysis = create_mock_analysis(
        "sum_vectorized_seed_term_count",
        return_type="int",
        parameters=[pointer_param, count_param],
        returns=[
            ReturnInfo(
                address="0x1000",
                pcode_time=10,
                value=_const(0),
                conditions=[
                    _cond(
                        "INT_SLESS",
                        Expression.constant(0, size=4),
                        Expression.parameter("param_2", index=1, data_type="uint", size=4),
                    )
                ],
            )
        ],
    )

    large_start_index = 128_000
    rounded_vn = _FakeVarnode("rounded", size=8)
    summarizer = StructuralRecurrenceSummarizer(_FakeTracer("unused", _const(0)), debug=False)

    monkeypatch.setattr(
        summarizer,
        "_readonly_round_down_candidates",
        lambda *_args, **_kwargs: [ReadonlyRoundedCountCandidate(rounded_vn, 8, large_start_index)],
    )
    vector_phi = _FakeVarnode("vector_phi", size=8)
    monkeypatch.setattr(
        summarizer,
        "_match_vector_prefix_pointer",
        lambda *_args, **_kwargs: (vector_phi, 0, 0),
    )
    monkeypatch.setattr(
        summarizer,
        "_vector_prefix_lanes_cover_block",
        lambda *_args, **_kwargs: True,
    )
    monkeypatch.setattr(
        summarizer,
        "_vector_prefix_lanes_have_unit_terms_in_positive_return",
        lambda *_args, **_kwargs: True,
    )
    monkeypatch.setattr(
        summarizer,
        "_vector_prefix_lanes_contribute_additively_to_return",
        lambda *_args, **_kwargs: True,
    )
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
    monkeypatch.setattr(
        summarizer,
        "_has_vector_countdown_loop",
        lambda *_args, **_kwargs: False,
    )
    monkeypatch.setattr(
        summarizer,
        "_has_vector_loop_bound_to_rounded_count",
        lambda *_args, **_kwargs: True,
    )
    monkeypatch.setattr(
        summarizer,
        "_has_scalar_tail_from_rounded_count",
        lambda *_args, **_kwargs: True,
    )

    proof = summarizer._detect_vectorized_readonly_prefix_sum_accumulator_proof(
        [],
        pointer_param,
        count_param,
        LocationBaseRef.parameter("param_1", index=0),
        Expression.parameter("param_2", index=1, data_type="uint", size=4),
        analysis,
        counter_signed=False,
    )

    assert proof is not None
    assert proof.seed_terms == ()
    assert proof.seed_term_count == large_start_index
    assert proof.start_index == large_start_index
    assert proof.start_offset == large_start_index * 4
    assert proof.return_region_value_proven is True
    assert proof.return_value_op_refs
    assert proof.source == "vectorized_readonly_prefix_sum"
    assert proof.seed_terms_for_count_value(3) == (
        ReadonlyReductionTermRef(byte_offset=0, access_size=4),
        ReadonlyReductionTermRef(byte_offset=4, access_size=4),
        ReadonlyReductionTermRef(byte_offset=8, access_size=4),
    )
    assert proof.seed_terms_for_count_value(large_start_index + 1) == ()

def test_vectorized_readonly_prefix_proof_accepts_def_use_return_site_proof_without_exact_witness(monkeypatch):
    pointer_param = {"name": "param_1", "index": 0, "data_type": "int *", "size": 8}
    count_param = {"name": "param_2", "index": 1, "data_type": "int", "size": 4, "is_signed": True}
    analysis = create_mock_analysis(
        "sum_vectorized_def_use_region_proof",
        return_type="int",
        parameters=[pointer_param, count_param],
        returns=[
            ReturnInfo(
                address="0x2000",
                pcode_time=20,
                value=Expression.unknown("phi_circular"),
                conditions=[
                    _cond(
                        "INT_NOTEQUAL",
                        Expression.parameter("param_1", index=0, data_type="int *", size=8),
                        Expression.constant(0, size=8),
                    ),
                    _cond(
                        "INT_SLESS",
                        Expression.constant(0, size=4),
                        Expression.parameter("param_2", index=1, data_type="int", size=4),
                    ),
                ],
            )
        ],
    )

    rounded_vn = _FakeVarnode("rounded", size=8)
    summarizer = StructuralRecurrenceSummarizer(_FakeTracer("unused", _const(0)), debug=False)

    monkeypatch.setattr(
        summarizer,
        "_readonly_round_down_candidates",
        lambda *_args, **_kwargs: [ReadonlyRoundedCountCandidate(rounded_vn, 8, 3)],
    )
    vector_phi = _FakeVarnode("vector_phi", size=8)
    monkeypatch.setattr(
        summarizer,
        "_match_vector_prefix_pointer",
        lambda *_args, **_kwargs: (vector_phi, 0, 0),
    )
    monkeypatch.setattr(
        summarizer,
        "_vector_prefix_lanes_cover_block",
        lambda *_args, **_kwargs: True,
    )
    monkeypatch.setattr(
        summarizer,
        "_vector_prefix_lanes_have_unit_terms_in_positive_return",
        lambda *_args, **_kwargs: False,
    )
    monkeypatch.setattr(
        summarizer,
        "_vector_prefix_lanes_contribute_additively_to_return",
        lambda *_args, **_kwargs: True,
    )
    monkeypatch.setattr(
        summarizer,
        "_vector_prefix_unit_term_positive_return_refs",
        lambda *_args, **_kwargs: (),
    )
    monkeypatch.setattr(
        summarizer,
        "_vector_prefix_lane_return_refs",
        lambda *_args, **_kwargs: (
            (PcodeOpRef(address_offset=0x2000, seq_time=20, mnemonic="RETURN"),),
            (PcodeOpRef(address_offset=0x2000, seq_time=19, mnemonic="INT_ADD"),),
        ),
    )
    monkeypatch.setattr(
        summarizer,
        "_has_vector_countdown_loop",
        lambda *_args, **_kwargs: False,
    )
    monkeypatch.setattr(
        summarizer,
        "_has_vector_loop_bound_to_rounded_count",
        lambda *_args, **_kwargs: True,
    )
    monkeypatch.setattr(
        summarizer,
        "_has_scalar_tail_from_rounded_count",
        lambda *_args, **_kwargs: True,
    )

    proof = summarizer._detect_vectorized_readonly_prefix_sum_accumulator_proof(
        [],
        pointer_param,
        count_param,
        LocationBaseRef.parameter("param_1", index=0),
        Expression.parameter("param_2", index=1, data_type="int", size=4),
        analysis,
        counter_signed=True,
    )

    assert proof is not None
    assert proof.return_region_value_proven is True
    assert proof.return_op_refs == (PcodeOpRef(address_offset=0x2000, seq_time=20, mnemonic="RETURN"),)
    assert proof.return_value_op_refs == (PcodeOpRef(address_offset=0x2000, seq_time=19, mnemonic="INT_ADD"),)
    assert proof.start_index == 3
    assert proof.start_offset == 12
    assert proof.source == "vectorized_readonly_prefix_sum"

def test_vector_prefix_pointer_requires_peeled_seed_offset_object_link():
    pointer_expr = Expression.parameter("param_1", index=0, data_type="int *", size=8)
    pointer_vn = _FakeVarnode("param_1", size=8, expr=pointer_expr)
    three_vn = _FakeVarnode("three", size=8, expr=Expression.constant(3, size=8))
    four_vn = _FakeVarnode("four", size=8, expr=Expression.constant(4, size=8))
    seed_vn = _FakeVarnode("seed", size=8)
    seed_op = _FakePcodeOp("PTRADD", [pointer_vn, three_vn, four_vn], seed_vn)
    vector_phi = _FakeVarnode("vector_phi", size=8, high=_FakeHighVar("vector_phi"))
    vector_next = _FakeVarnode("vector_next", size=8)
    vector_step_op = _FakePcodeOp("PTRADD", [vector_phi, _FakeVarnode("eight", size=8, expr=Expression.constant(8, size=8)), four_vn], vector_next)
    vector_phi_op = _FakePcodeOp("MULTIEQUAL", [seed_vn, vector_next], vector_phi)
    ram_space = _FakeVarnode("ram", size=8, expr=Expression.constant(0, size=8))
    lane0 = _FakeVarnode("lane0", size=4)
    lane1_addr = _FakeVarnode("lane1_addr", size=8)
    lane1_addr_op = _FakePcodeOp("PTRADD", [vector_phi, _FakeVarnode("one", size=8, expr=Expression.constant(1, size=8)), four_vn], lane1_addr)
    lane1 = _FakeVarnode("lane1", size=4)
    load0_op = _FakePcodeOp("LOAD", [ram_space, vector_phi], lane0)
    load1_op = _FakePcodeOp("LOAD", [ram_space, lane1_addr], lane1)
    summarizer = StructuralRecurrenceSummarizer(_FakeTracer("unused", _const(0)), debug=False)

    assert summarizer._match_vector_prefix_pointer(
        [seed_op, vector_step_op, vector_phi_op, lane1_addr_op, load0_op, load1_op],
        {"name": "param_1", "index": 0, "data_type": "int *", "size": 8},
        vector_stride=32,
        element_size=4,
        expected_start_offset=16,
    ) is None
    assert summarizer._match_vector_prefix_pointer(
        [seed_op, vector_step_op, vector_phi_op, lane1_addr_op, load0_op, load1_op],
        {"name": "param_1", "index": 0, "data_type": "int *", "size": 8},
        vector_stride=32,
        element_size=4,
        expected_start_offset=12,
    ) == (vector_phi, 0, 12)

def test_vector_loop_bound_uses_postincrement_def_before_storage_alias():
    pointer_expr = Expression.parameter("param_1", index=0, data_type="int *", size=8)
    pointer_vn = _FakeVarnode("param_1", size=8, expr=pointer_expr)
    rounded_vn = _FakeVarnode("rounded", size=8)
    seven_vn = _FakeVarnode("seven", size=8, expr=Expression.constant(7, size=8))
    four_vn = _FakeVarnode("four", size=8, expr=Expression.constant(4, size=8))
    index_vn = _FakeVarnode("rounded_plus_seven", size=8)
    end_vn = _FakeVarnode("end", size=8)
    cursor_high = _FakeHighVar("cursor")
    cursor_phi = _FakeVarnode("cursor_phi", size=8, high=cursor_high, storage_offset=0x4010)
    cursor_next = _FakeVarnode("cursor_next", size=8, high=cursor_high, storage_offset=0x4010)
    cond_vn = _FakeVarnode("cond", size=1)
    index_op = _FakePcodeOp("INT_ADD", [rounded_vn, seven_vn], index_vn)
    end_op = _FakePcodeOp("PTRADD", [pointer_vn, index_vn, four_vn], end_vn)
    step_op = _FakePcodeOp(
        "PTRADD",
        [cursor_phi, _FakeVarnode("four_lanes", size=8, expr=Expression.constant(4, size=8)), four_vn],
        cursor_next,
    )
    compare_op = _FakePcodeOp("INT_NOTEQUAL", [end_vn, cursor_next], cond_vn)
    summarizer = StructuralRecurrenceSummarizer(_FakeTracer("unused", _const(0)), debug=False)

    assert index_op.getOutput() is index_vn
    assert end_op.getOutput() is end_vn
    assert step_op.getOutput() is cursor_next
    assert summarizer._has_vector_loop_bound_to_rounded_count(
        [index_op, end_op, step_op, compare_op],
        cursor_phi,
        {"name": "param_1", "index": 0, "data_type": "int *", "size": 8},
        rounded_vn,
        element_size=4,
        base_offset=12,
        vector_stride=16,
    )

def test_readonly_vector_lane_summary_enters_scalar_iteration_space_only_with_witnesses():
    summarizer = StructuralRecurrenceSummarizer(_FakeTracer("unused", _const(0)), debug=False)
    count_expr = Expression.parameter("param_2", index=1, data_type="int", size=4)
    base_ref = LocationBaseRef.parameter("param_1", index=0)
    witnesses = tuple(
        ReadonlyReductionWitness(
            exact_count=count,
            terms=tuple(
                ReadonlyReductionTermRef(byte_offset=index * 4, access_size=4)
                for index in range(count)
            ),
        )
        for count in (1, 2, 3)
    )
    scalar_proof = _readonly_accumulator_proof(
            base_ref=base_ref,
            count_expr=count_expr,
            stride=4,
            element_size=4,
            index_scale=4,
            witnesses=witnesses,
    )
    scalar_summary = scalar_proof.with_runtime_evidence(
        limit_expr=count_expr,
        result_size=4,
        loop_body_witnesses=witnesses,
        exact_return_witnesses=(),
        guard_constraints=(),
        signed_counter=True,
    ).lower_to_loop_summary_ref()
    vector_proof = _readonly_accumulator_proof(
            base_ref=base_ref,
            count_expr=count_expr,
            stride=16,
            element_size=8,
            index_scale=16,
            lane_terms=((0, 4), (4, 4), (8, 4), (12, 4)),
            witnesses=witnesses,
    )
    vector_summary = vector_proof.with_runtime_evidence(
        limit_expr=count_expr,
        result_size=4,
        loop_body_witnesses=witnesses,
        exact_return_witnesses=(),
        guard_constraints=(),
        signed_counter=True,
    ).lower_to_loop_summary_ref()
    unproven_vector_proof = _readonly_accumulator_proof(
            base_ref=base_ref,
            count_expr=count_expr,
            stride=16,
            element_size=8,
            index_scale=16,
            lane_terms=((0, 4), (4, 4), (8, 4), (12, 4)),
    )
    unproven_vector_summary = unproven_vector_proof.with_runtime_evidence(
        limit_expr=count_expr,
        result_size=4,
        loop_body_witnesses=(),
        exact_return_witnesses=(),
        guard_constraints=(),
        signed_counter=True,
    ).lower_to_loop_summary_ref()

    assert scalar_summary is not None
    assert vector_summary is not None
    assert unproven_vector_summary is not None
    assert vector_summary.loop_var_unit == "scalar_element_index"
    assert loop_summary_method_b_key(vector_summary) == loop_summary_method_b_key(scalar_summary)
    assert unproven_vector_summary.loop_var_unit == "element_index"
    assert loop_summary_method_b_key(unproven_vector_summary) != loop_summary_method_b_key(scalar_summary)

def test_readonly_reduction_result_size_uses_positive_region_return():
    ptr_expr = Expression.parameter("param_1", index=0, data_type="long *", size=8)
    count_expr = Expression.parameter("param_2", index=1, data_type="int", size=4)
    positive = [
        _cond("INT_NOTEQUAL", ptr_expr, Expression.constant(0, size=8)),
        _cond("INT_SLESS", Expression.constant(0, size=4), count_expr),
    ]
    positive_value = Expression.unknown("wide_positive")
    positive_value.size = 8
    analysis = create_mock_analysis(
        "wide_sum",
        return_type="long",
        parameters=[
            {"name": "param_1", "index": 0, "data_type": "long *", "size": 8},
            {"name": "param_2", "index": 1, "data_type": "int", "size": 4},
        ],
        returns=[
            ReturnInfo(
                address="0x1000",
                value=Expression.constant(-1, size=4),
                conditions=[_cond("INT_EQUAL", ptr_expr, Expression.constant(0, size=8))],
            ),
            ReturnInfo(
                address="0x1004",
                value=positive_value,
                conditions=positive,
            ),
        ],
    )
    summarizer = StructuralRecurrenceSummarizer(_FakeTracer("unused", _const(0)), debug=False)

    assert summarizer._readonly_reduction_result_size(analysis, positive_conditions=positive) == 8

def test_readonly_reduction_summary_passes_positive_region_to_accumulator_proof(monkeypatch):
    ptr_expr = Expression.parameter("param_1", index=0, data_type="long *", size=8)
    count_expr = Expression.parameter("param_2", index=1, data_type="int", size=4)
    pointer_param = {"name": "param_1", "index": 0, "data_type": "long *", "size": 8}
    count_param = {"name": "param_2", "index": 1, "data_type": "int", "size": 4}
    positive_value = Expression.unknown("wide_positive")
    positive_value.size = 8
    analysis = create_mock_analysis(
        "wide_sum",
        return_type="long",
        parameters=[pointer_param, count_param],
        returns=[
            ReturnInfo(
                address="0x1000",
                value=Expression.constant(-1, size=4),
                conditions=[_cond("INT_EQUAL", ptr_expr, Expression.constant(0, size=8))],
            ),
            ReturnInfo(
                address="0x1004",
                value=positive_value,
                conditions=[
                    _cond("INT_NOTEQUAL", ptr_expr, Expression.constant(0, size=8)),
                    _cond("INT_SLESS", Expression.constant(0, size=4), count_expr),
                ],
            ),
        ],
    )
    captured = {}
    summarizer = StructuralRecurrenceSummarizer(_FakeTracer("unused", _const(0)), debug=False)
    monkeypatch.setattr(
        summarizer,
        "_infer_readonly_pointer_reduction_parameters",
        lambda _analysis, _high_function: (pointer_param, count_param),
    )

    def capture_accumulator_proof(
        _high_function,
        _analysis,
        _pointer_param,
        _count_param,
        *,
        counter_signed,
        positive_conditions=(),
    ):
        captured["counter_signed"] = counter_signed
        captured["positive_conditions"] = tuple(positive_conditions)
        return None

    monkeypatch.setattr(summarizer, "_detect_readonly_sum_accumulator_proof", capture_accumulator_proof)

    assert summarizer._try_summarize_readonly_pointer_reduction(
        _FakeFunction("wide_sum"),
        _FakeHighFunction([]),
        analysis,
    ) is None
    assert captured["positive_conditions"]
    assert summarizer._readonly_reduction_result_size(
        analysis,
        positive_conditions=captured["positive_conditions"],
    ) == 8

def test_readonly_sum_detection_prefers_vectorized_before_scalar_phi_match(monkeypatch):
    pointer_param = {"name": "param_1", "index": 0, "data_type": "int *", "size": 8}
    count_param = {"name": "param_2", "index": 1, "data_type": "uint", "size": 4, "is_signed": False}
    analysis = create_mock_analysis(
        "sum_vectorized_primacy",
        return_type="int",
        parameters=[pointer_param, count_param],
        returns=[
            ReturnInfo(
                address="0x1000",
                value=_const(0),
                conditions=[
                    _cond(
                        "INT_SLESS",
                        Expression.constant(0, size=4),
                        Expression.parameter("param_2", index=1, data_type="uint", size=4),
                    ),
                ],
            ),
        ],
    )
    high_function = _FakeHighFunction([])
    summarizer = StructuralRecurrenceSummarizer(_FakeTracer("unused", _const(0)), debug=False)
    invocation = {"vectorized": 0, "scalar": 0}

    expected = _readonly_accumulator_proof(
        base_ref=LocationBaseRef.parameter("param_1", index=0),
        count_expr=Expression.parameter("param_2", index=1, data_type="uint", size=4),
        stride=4,
        element_size=4,
    )

    def capture_vectorized(*_args, **_kwargs):
        invocation["vectorized"] += 1
        return expected

    def capture_scalar(*_args, **_kwargs):
        invocation["scalar"] += 1
        return expected

    monkeypatch.setattr(
        summarizer,
        "_analysis_mentions_parameter_in_conditions",
        lambda _analysis, _param_name: True,
    )
    monkeypatch.setattr(
        summarizer,
        "_detect_vectorized_readonly_prefix_sum_accumulator_proof",
        capture_vectorized,
    )
    monkeypatch.setattr(
        summarizer,
        "_match_accumulator_phi",
        capture_scalar,
    )

    actual = summarizer._detect_readonly_sum_accumulator_proof(
        high_function,
        analysis,
        pointer_param,
        count_param,
        counter_signed=True,
    )

    assert actual == expected
    assert invocation["vectorized"] == 1
    assert invocation["scalar"] == 0

def test_structural_recurrence_summarizer_declines_readonly_reduction_from_prefix_returns_only():
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
                value=Expression.memory(
                    Expression.parameter("param_1", index=0, data_type="int *", size=8),
                    size=4,
                ),
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
                    Expression.memory(
                        Expression.parameter("param_1", index=0, data_type="int *", size=8),
                        size=4,
                    ),
                    Expression.memory(
                        Expression.binary_op(
                            "INT_ADD",
                            Expression.parameter("param_1", index=0, data_type="int *", size=8),
                            Expression.constant(4, size=8),
                        ),
                        size=4,
                    ),
                ),
                conditions=[
                    _cond(
                        "INT_NOTEQUAL",
                        Expression.parameter("param_1", index=0, data_type="int *", size=8),
                        Expression.constant(0, size=8),
                    ),
                    _cond("INT_EQUAL", _param("param_2"), _const(2)),
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

def test_readonly_semantic_witnesses_use_exact_returns_as_provisional_lane_evidence(monkeypatch):
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
        stride=8,
        element_size=8,
        start_offset=4,
        start_index=0,
        index_step=1,
        index_scale=8,
        lane_terms=((0, 4), (4, 4)),
    )
    exact_witnesses = (
        ReadonlyReductionWitness(
            exact_count=1,
            terms=(ReadonlyReductionTermRef(byte_offset=4, access_size=4),),
        ),
        ReadonlyReductionWitness(
            exact_count=2,
            terms=(
                ReadonlyReductionTermRef(byte_offset=4, access_size=4),
                ReadonlyReductionTermRef(byte_offset=8, access_size=4),
            ),
        ),
    )
    analysis = create_mock_analysis(
        "shifted_lane_sum",
        return_type="int",
        parameters=[pointer_param, count_param],
        returns=[],
    )
    summarizer = StructuralRecurrenceSummarizer(_FakeTracer("unused", _const(0)), debug=False)
    monkeypatch.setattr(
        summarizer,
        "_extract_readonly_reduction_exact_witnesses",
        lambda *_args, **_kwargs: exact_witnesses,
    )

    witnesses = summarizer._build_readonly_reduction_semantic_witnesses(
        analysis,
        pointer_param,
        count_param,
        [],
        proof,
        result_size=4,
    )

    assert witnesses == exact_witnesses

def test_readonly_accumulator_proof_materializes_missing_small_prefix_from_larger_exact_witness():
    count_expr = Expression.parameter("param_2", index=1, data_type="int", size=4)
    proof = ReductionAccumulatorProof(
        reduction_kind="memory_sum",
        pointer_base_ref=LocationBaseRef.parameter("param_1", index=0),
        count_parameter_name="param_2",
        count_parameter_index=1,
        limit_expr=count_expr,
        result_size=4,
        stride=16,
        element_size=8,
        start_offset=4,
        start_index=0,
        index_step=1,
        index_scale=16,
        exact_return_witnesses=(
            ReadonlyReductionWitness(
                exact_count=1,
                terms=(ReadonlyReductionTermRef(byte_offset=0, access_size=4),),
            ),
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

    assert proof.loop_body_terms_for_count_value(2) is None
    assert tuple(term.byte_offset for term in (proof.full_terms_for_count_value(2) or ())) == (
        0,
        4,
    )
    assert proof.full_terms_for_count_value(5) is None

def test_return_analyzer_normalization_does_not_widen_readonly_summary_domain():
    analyzer = ReturnAnalyzer(program=None, debug=False)
    params = [
        {"name": "param_1", "index": 0, "data_type": "int *", "size": 8},
        {"name": "param_2", "index": 1, "data_type": "int", "size": 4, "is_signed": True},
    ]
    reduction_expr = Expression.intrinsic(
        "READONLY_SUM",
        [
            Expression.parameter("param_1", index=0, data_type="int *", size=8),
            Expression.parameter("param_2", index=1, data_type="int", size=4),
        ],
        size=4,
        runtime_ref=ReadonlyReductionRef(
            reduction_kind="readonly_sum",
            pointer_base_ref=LocationBaseRef.parameter("param_1", index=0),
            count_parameter_name="param_2",
            count_parameter_index=1,
            stride=4,
            element_size=4,
            result_size=4,
        ),
        opcode=READONLY_SUM_OPCODE,
    )
    corrupted = ReturnInfo(
        address="0x1008",
        value=reduction_expr,
        conditions=[
            _cond(
                "INT_NOTEQUAL",
                Expression.parameter("param_1", index=0, data_type="int *", size=8),
                Expression.binary_op(
                    "INT_ADD",
                    Expression.parameter("param_1", index=0, data_type="int *", size=8),
                    Expression.constant(8, size=8),
                ),
            ),
            _cond("INT_SLESS", _const(0), _param("param_2")),
        ],
    )

    analysis = create_mock_analysis(
        "readonly_partition_preserved_basic",
        return_type="int",
        parameters=params,
        returns=[corrupted],
    )

    analyzer._normalize_return_partition(analysis)

    normalized_conditions = [cond.to_string() for cond in analysis.returns[0].conditions]

    assert normalized_conditions == ["(0 < param_2)"]
    assert "(3 < param_2)" not in normalized_conditions

def test_return_analyzer_normalization_keeps_existing_readonly_lower_bound():
    analyzer = ReturnAnalyzer(program=None, debug=False)
    params = [
        {"name": "param_1", "index": 0, "data_type": "int *", "size": 8},
        {"name": "param_2", "index": 1, "data_type": "int", "size": 4, "is_signed": True},
    ]
    base_ref = LocationBaseRef.parameter("param_1", index=0)
    count_expr = _param("param_2", size=4)
    accumulator_proof = _readonly_accumulator_proof(
        base_ref=base_ref,
        count_expr=count_expr,
        stride=4,
        element_size=4,
        start_index=3,
    )
    reduction_expr = Expression.intrinsic(
        "READONLY_SUM",
        [
            Expression.parameter("param_1", index=0, data_type="int *", size=8),
            Expression.parameter("param_2", index=1, data_type="int", size=4),
        ],
        size=4,
        runtime_ref=ReadonlyReductionRef(
            reduction_kind="readonly_sum",
            pointer_base_ref=base_ref,
            count_parameter_name="param_2",
            count_parameter_index=1,
            stride=4,
            element_size=4,
            result_size=4,
            signed_counter=True,
            accumulator_proof=accumulator_proof,
        ),
        opcode=READONLY_SUM_OPCODE,
    )
    corrupted = ReturnInfo(
        address="0x1010",
        value=reduction_expr,
        conditions=[
            _cond(
                "INT_NOTEQUAL",
                Expression.parameter("param_1", index=0, data_type="int *", size=8),
                Expression.binary_op(
                    "INT_ADD",
                    Expression.parameter("param_1", index=0, data_type="int *", size=8),
                    Expression.constant(8, size=8),
                ),
            ),
            _cond("INT_SLESS", _const(0), _param("param_2")),
        ],
    )

    analysis = create_mock_analysis(
        "readonly_partition_preserved_with_start_index",
        return_type="int",
        parameters=params,
        returns=[corrupted],
    )

    analyzer._normalize_return_partition(analysis)

    normalized_conditions = [cond.to_string() for cond in analysis.returns[0].conditions]

    assert normalized_conditions == ["(0 < param_2)"]
    assert "(3 < param_2)" not in normalized_conditions

def test_structural_recurrence_omitted_positive_return_requires_exact_readonly_witness(monkeypatch):
    summarizer = StructuralRecurrenceSummarizer(tracer=None, debug=False)
    pointer_param = {"name": "param_1", "index": 0, "data_type": "int *", "size": 8, "is_signed": False}
    count_param = {"name": "param_2", "index": 1, "data_type": "uint", "size": 4, "is_signed": False}
    analysis = FunctionReturnAnalysis(
        function_name="readonly_partial_positive_region_like",
        entry_point="0x1000",
        parameters=[pointer_param, count_param],
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
                    _cond("INT_EQUAL", _param("param_2"), _const(1)),
                ],
                value=_const(999),
            ),
        ],
    )
    proof = _readonly_accumulator_proof(
        base_ref=LocationBaseRef.parameter("param_1", index=0),
        count_expr=_param("param_2"),
        stride=4,
        element_size=4,
    )

    omitted = analysis.returns[1]

    assert (
        summarizer._readonly_positive_return_matches_accumulator_proof(
            analysis,
            pointer_param,
            count_param,
            omitted,
            proof,
        )
        is False
    )

def test_readonly_positive_prefix_coverage_accepts_anchor_backed_prefix_returns(monkeypatch):
    summarizer = StructuralRecurrenceSummarizer(tracer=None, debug=False)
    pointer_param = {"name": "param_1", "index": 0, "data_type": "int *", "size": 8, "is_signed": False}
    count_param = {"name": "param_2", "index": 1, "data_type": "int", "size": 4, "is_signed": True}
    count_expr = _param("param_2")
    broad_ret = ReturnInfo(
        address="0x1300",
        conditions=[
            _cond("INT_NOTEQUAL", _param("param_1", size=8), _const(0, size=8)),
            _cond("INT_SLESS", _const(0), count_expr),
        ],
        value=Expression.unknown("phi_circular"),
    )
    exact_one = ReturnInfo(
        address="0x1301",
        conditions=[
            _cond("INT_NOTEQUAL", _param("param_1", size=8), _const(0, size=8)),
            _cond("INT_EQUAL", count_expr, _const(1)),
        ],
        value=_mem("param_1", 0),
    )
    exact_two = ReturnInfo(
        address="0x1302",
        conditions=[
            _cond("INT_NOTEQUAL", _param("param_1", size=8), _const(0, size=8)),
            _cond("INT_EQUAL", count_expr, _const(2)),
        ],
        value=Expression.binary_op("INT_ADD", _mem("param_1", 0), _mem("param_1", 4)),
    )
    exact_three = ReturnInfo(
        address="0x1303",
        conditions=[
            _cond("INT_NOTEQUAL", _param("param_1", size=8), _const(0, size=8)),
            _cond("INT_EQUAL", count_expr, _const(3)),
        ],
        value=Expression.binary_op(
            "INT_ADD",
            _mem("param_1", 8),
            Expression.binary_op("INT_ADD", _mem("param_1", 0), _mem("param_1", 4)),
        ),
    )
    analysis = FunctionReturnAnalysis(
        function_name="readonly_anchor_backed_prefix_coverage_like",
        entry_point="0x1300",
        parameters=[pointer_param, count_param],
        returns=[broad_ret, exact_one, exact_two, exact_three],
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

    monkeypatch.setattr(
        summarizer,
        "_readonly_positive_return_matches_accumulator_proof",
        lambda *_args, **_kwargs: False,
    )
    monkeypatch.setattr(
        summarizer,
        "_readonly_positive_return_accumulator_anchor_count",
        lambda _analysis, _pointer_param, _count_param, ret, _proof: {
            "0x1301": 1,
            "0x1302": 2,
            "0x1303": 3,
        }.get(ret.address),
    )

    assert summarizer._readonly_positive_prefix_is_exactly_covered(
        analysis,
        pointer_param,
        count_param,
        broad_ret,
        proof,
    ) is True

def test_readonly_positive_prefix_coverage_accepts_materialized_count_specific_returns(monkeypatch):
    summarizer = StructuralRecurrenceSummarizer(tracer=None, debug=False)
    pointer_param = {"name": "param_1", "index": 0, "data_type": "int *", "size": 8, "is_signed": False}
    count_param = {"name": "param_2", "index": 1, "data_type": "int", "size": 4, "is_signed": True}
    count_expr = _param("param_2")
    broad_ret = ReturnInfo(
        address="0x1310",
        conditions=[
            _cond("INT_NOTEQUAL", _param("param_1", size=8), _const(0, size=8)),
            _cond("INT_SLESS", _const(0), count_expr),
        ],
        value=Expression.unknown("phi_circular"),
    )
    exact_one = ReturnInfo(
        address="0x1311",
        conditions=[
            _cond("INT_NOTEQUAL", _param("param_1", size=8), _const(0, size=8)),
            _cond("INT_EQUAL", count_expr, _const(1)),
        ],
        value=_mem("param_1", 0),
    )
    exact_two = ReturnInfo(
        address="0x1312",
        conditions=[
            _cond("INT_NOTEQUAL", _param("param_1", size=8), _const(0, size=8)),
            _cond("INT_EQUAL", count_expr, _const(2)),
        ],
        value=Expression.binary_op("INT_ADD", _mem("param_1", 0), _mem("param_1", 4)),
    )
    exact_three = ReturnInfo(
        address="0x1313",
        conditions=[
            _cond("INT_NOTEQUAL", _param("param_1", size=8), _const(0, size=8)),
            _cond("INT_EQUAL", count_expr, _const(3)),
        ],
        value=Expression.binary_op(
            "INT_ADD",
            _mem("param_1", 8),
            Expression.binary_op("INT_ADD", _mem("param_1", 0), _mem("param_1", 4)),
        ),
    )
    analysis = FunctionReturnAnalysis(
        function_name="readonly_materialized_prefix_coverage_like",
        entry_point="0x1310",
        parameters=[pointer_param, count_param],
        returns=[broad_ret, exact_one, exact_two, exact_three],
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

    monkeypatch.setattr(
        summarizer,
        "_readonly_positive_return_matches_accumulator_proof",
        lambda *_args, **_kwargs: False,
    )
    monkeypatch.setattr(
        summarizer,
        "_readonly_positive_return_accumulator_anchor_count",
        lambda *_args, **_kwargs: None,
    )

    assert summarizer._readonly_positive_prefix_is_exactly_covered(
        analysis,
        pointer_param,
        count_param,
        broad_ret,
        proof,
    ) is True
