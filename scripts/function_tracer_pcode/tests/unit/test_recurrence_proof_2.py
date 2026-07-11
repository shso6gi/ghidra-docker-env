from scripts.function_tracer_pcode.tests.unit._recurrence_fixtures import *

def test_structural_recurrence_declines_summary_when_counter_signedness_is_ambiguous(monkeypatch):
    summarizer = StructuralRecurrenceSummarizer(tracer=None, debug=False)
    analysis = FunctionReturnAnalysis(
        function_name="readonly_ambiguous_counter_like",
        entry_point="0x1000",
        parameters=[
            {"name": "param_1", "index": 0, "data_type": "int *", "size": 8, "is_signed": False},
            {"name": "param_2", "index": 1, "data_type": "uint", "size": 4, "is_signed": False},
        ],
        returns=[ReturnInfo(address="0x1000", conditions=[], value=_const(1))],
    )
    pointer_param = analysis.parameters[0]
    count_param = analysis.parameters[1]

    class _FakeFunction:
        def getName(self):
            return "readonly_ambiguous_counter_like"

    monkeypatch.setattr(
        summarizer,
        "_infer_readonly_pointer_reduction_parameters",
        lambda _analysis, _high_function: (pointer_param, count_param),
    )
    monkeypatch.setattr(
        summarizer,
        "_readonly_reduction_counter_is_signed",
        lambda _analysis, _count_param: None,
    )

    assert (
        summarizer._try_summarize_readonly_pointer_reduction(
            _FakeFunction(),
            object(),
            analysis,
        )
        is None
    )

def test_structural_recurrence_summary_uses_effective_declared_signedness_to_break_viable_tie(monkeypatch):
    summarizer = StructuralRecurrenceSummarizer(tracer=None, debug=False)
    pointer_param = {"name": "param_1", "index": 0, "data_type": "int *", "size": 8, "is_signed": False}
    count_param = {"name": "param_2", "index": 1, "data_type": "uint", "size": 4, "is_signed": False}
    count_expr = Expression.parameter("param_2", index=1, data_type="uint", size=4)
    positive_conditions = [
        _cond("INT_NOTEQUAL", _param("param_1", size=8), _const(0, size=8)),
        _cond("INT_LESS", _const(0), count_expr),
    ]
    positive_ret = ReturnInfo(address="0x1001", conditions=list(positive_conditions), value=_mem("param_1", 0))
    null_ret = ReturnInfo(
        address="0x1000",
        conditions=[_cond("INT_EQUAL", _param("param_1", size=8), _const(0, size=8))],
        value=_const(0),
    )
    analysis = create_mock_analysis(
        "readonly_signedness_tie_break",
        return_type="int",
        parameters=[pointer_param, count_param],
        returns=[null_ret, positive_ret],
    )
    proof = _readonly_accumulator_proof(
        base_ref=LocationBaseRef.parameter("param_1", index=0),
        count_expr=count_expr,
        stride=4,
        element_size=4,
    )

    monkeypatch.setattr(
        summarizer,
        "_infer_readonly_pointer_reduction_parameters",
        lambda _analysis, _high_function: (pointer_param, count_param),
    )
    monkeypatch.setattr(
        summarizer,
        "_readonly_reduction_positive_conditions",
        lambda *_args, **_kwargs: list(positive_conditions),
    )
    monkeypatch.setattr(
        summarizer,
        "_readonly_reduction_region_returns_with_signedness",
        lambda *_args, **_kwargs: [positive_ret],
    )
    monkeypatch.setattr(
        summarizer,
        "_detect_readonly_sum_accumulator_proof",
        lambda *_args, **_kwargs: proof,
    )
    monkeypatch.setattr(
        summarizer,
        "_readonly_reduction_replaceable_positive_returns",
        lambda *_args, **_kwargs: [positive_ret],
    )
    monkeypatch.setattr(
        summarizer,
        "_build_readonly_reduction_semantic_witnesses",
        lambda *_args, **_kwargs: (),
    )
    monkeypatch.setattr(
        summarizer,
        "_extract_readonly_reduction_exact_witnesses",
        lambda *_args, **_kwargs: (),
    )

    summary = summarizer._try_summarize_readonly_pointer_reduction(
        _FakeFunction("readonly_signedness_tie_break"),
        object(),
        analysis,
    )

    assert summary is not None
    summarized_returns, _note = summary
    readonly_ret = next(ret for ret in summarized_returns if getattr(ret.value, "opcode", None) == READONLY_SUM_OPCODE)
    assert readonly_ret.value.runtime_ref.signed_counter is False

def test_structural_recurrence_declines_when_viable_signedness_tie_has_no_local_declaration_winner(monkeypatch):
    summarizer = StructuralRecurrenceSummarizer(tracer=None, debug=False)
    pointer_param = {"name": "param_1", "index": 0, "data_type": "int *", "size": 8, "is_signed": False}
    count_param = {"name": "param_2", "index": 1, "data_type": "uint", "size": 4, "is_signed": None}
    count_expr = Expression.parameter("param_2", index=1, data_type="uint", size=4)
    positive_conditions = [
        _cond("INT_NOTEQUAL", _param("param_1", size=8), _const(0, size=8)),
        _cond("INT_LESS", _const(0), count_expr),
    ]
    positive_ret = ReturnInfo(address="0x1001", conditions=list(positive_conditions), value=_mem("param_1", 0))
    analysis = create_mock_analysis(
        "readonly_signedness_tie_decline",
        return_type="int",
        parameters=[pointer_param, count_param],
        returns=[positive_ret],
    )
    proof = _readonly_accumulator_proof(
        base_ref=LocationBaseRef.parameter("param_1", index=0),
        count_expr=count_expr,
        stride=4,
        element_size=4,
    )

    monkeypatch.setattr(
        summarizer,
        "_infer_readonly_pointer_reduction_parameters",
        lambda _analysis, _high_function: (pointer_param, count_param),
    )
    monkeypatch.setattr(
        summarizer,
        "_readonly_reduction_positive_conditions",
        lambda *_args, **_kwargs: list(positive_conditions),
    )
    monkeypatch.setattr(
        summarizer,
        "_readonly_reduction_region_returns_with_signedness",
        lambda *_args, **_kwargs: [positive_ret],
    )
    monkeypatch.setattr(
        summarizer,
        "_detect_readonly_sum_accumulator_proof",
        lambda *_args, **_kwargs: proof,
    )
    monkeypatch.setattr(
        summarizer,
        "_readonly_reduction_replaceable_positive_returns",
        lambda *_args, **_kwargs: [positive_ret],
    )

    assert (
        summarizer._try_summarize_readonly_pointer_reduction(
            _FakeFunction("readonly_signedness_tie_decline"),
            object(),
            analysis,
        )
        is None
    )

def test_structural_recurrence_preserves_exact_positive_return_as_partition_evidence(monkeypatch):
    summarizer = StructuralRecurrenceSummarizer(tracer=None, debug=False)
    pointer_param = {"name": "param_1", "index": 0, "data_type": "int *", "size": 8, "is_signed": False}
    count_param = {"name": "param_2", "index": 1, "data_type": "int", "size": 4, "is_signed": True}
    count_expr = Expression.parameter("param_2", index=1, data_type="int", size=4)
    positive_conditions = [
        _cond("INT_NOTEQUAL", _param("param_1", size=8), _const(0, size=8)),
        _cond("INT_SLESS", _const(0), count_expr),
    ]
    exact_ret = ReturnInfo(
        address="0x1000",
        value=_mem("param_1", 0),
        conditions=list(positive_conditions) + [_cond("INT_EQUAL", count_expr, _const(1))],
    )
    broad_ret = ReturnInfo(
        address="0x1004",
        value=Expression.binary_op(
            "INT_ADD",
            _mem("param_1", 0),
            _mem("param_1", 4),
        ),
        conditions=list(positive_conditions),
    )
    analysis = create_mock_analysis(
        "readonly_absorb_exact_positive_return",
        return_type="int",
        parameters=[pointer_param, count_param],
        returns=[exact_ret, broad_ret],
    )
    proof = _readonly_accumulator_proof(
        base_ref=LocationBaseRef.parameter("param_1", index=0),
        count_expr=count_expr,
        stride=4,
        element_size=4,
        result_size=4,
    )

    monkeypatch.setattr(
        summarizer,
        "_infer_readonly_pointer_reduction_parameters",
        lambda _analysis, _high_function: (pointer_param, count_param),
    )
    monkeypatch.setattr(
        summarizer,
        "_readonly_reduction_positive_conditions",
        lambda *_args, **_kwargs: list(positive_conditions),
    )
    monkeypatch.setattr(
        summarizer,
        "_readonly_reduction_region_returns",
        lambda _analysis, _conditions: [exact_ret, broad_ret],
    )
    monkeypatch.setattr(
        summarizer,
        "_detect_readonly_sum_accumulator_proof",
        lambda *_args, **_kwargs: proof,
    )
    monkeypatch.setattr(
        summarizer,
        "_readonly_reduction_replaceable_positive_returns",
        lambda *_args, **_kwargs: [exact_ret, broad_ret],
    )
    monkeypatch.setattr(
        summarizer,
        "_build_readonly_reduction_semantic_witnesses",
        lambda *_args, **_kwargs: (),
    )

    class _FakeFunction:
        def getName(self):
            return "readonly_absorb_exact_positive_return"

    summarized = summarizer._try_summarize_readonly_pointer_reduction(
        _FakeFunction(),
        object(),
        analysis,
    )

    assert summarized is not None
    summarized_returns, _note = summarized
    readonly_ret = next(
        ret for ret in summarized_returns
        if getattr(ret.value, "opcode", None) == READONLY_SUM_OPCODE
    )
    assert any(
        getattr(condition, "negated", False)
        and getattr(getattr(condition, "expression", None), "operator", None) == "INT_EQUAL"
        for condition in readonly_ret.conditions
    )
    assert exact_ret in summarized_returns

def test_structural_recurrence_preserves_nonpositive_return_misclassified_as_positive_overlap(monkeypatch):
    summarizer = StructuralRecurrenceSummarizer(tracer=None, debug=False)
    pointer_param = {"name": "param_1", "index": 0, "data_type": "int *", "size": 8, "is_signed": False}
    count_param = {"name": "param_2", "index": 1, "data_type": "int", "size": 4, "is_signed": True}
    pointer_expr = _param("param_1", size=8)
    count_expr = Expression.parameter("param_2", index=1, data_type="int", size=4)
    positive_conditions = [
        _cond("INT_NOTEQUAL", pointer_expr, _const(0, size=8)),
        _cond("INT_SLESS", _const(0), count_expr),
    ]
    positive_ret = ReturnInfo(
        address="0x1004",
        value=_mem("param_1", 0),
        conditions=list(positive_conditions),
    )
    nonpositive_ret = ReturnInfo(
        address="0x1008",
        value=_const(0xFFFFFED4, size=4),
        conditions=[
            _cond("INT_NOTEQUAL", pointer_expr, _const(0, size=8)),
            _cond("INT_SLESS", _const(0), count_expr, negated=True),
        ],
        return_kind="phi_expansion",
    )
    analysis = create_mock_analysis(
        "readonly_preserve_nonpositive_overlap",
        return_type="int",
        parameters=[pointer_param, count_param],
        returns=[positive_ret, nonpositive_ret],
    )
    proof = _readonly_accumulator_proof(
        base_ref=LocationBaseRef.parameter("param_1", index=0),
        count_expr=count_expr,
        stride=4,
        element_size=4,
        result_size=4,
    )

    monkeypatch.setattr(
        summarizer,
        "_infer_readonly_pointer_reduction_parameters",
        lambda _analysis, _high_function: (pointer_param, count_param),
    )
    monkeypatch.setattr(
        summarizer,
        "_readonly_reduction_positive_conditions",
        lambda *_args, **_kwargs: list(positive_conditions),
    )
    monkeypatch.setattr(
        summarizer,
        "_detect_readonly_sum_accumulator_proof",
        lambda *_args, **_kwargs: proof,
    )
    monkeypatch.setattr(
        summarizer,
        "_readonly_reduction_replaceable_positive_returns",
        lambda *_args, **_kwargs: [nonpositive_ret, positive_ret],
    )
    monkeypatch.setattr(
        summarizer,
        "_build_readonly_reduction_semantic_witnesses",
        lambda *_args, **_kwargs: (),
    )
    monkeypatch.setattr(
        summarizer,
        "_extract_readonly_reduction_exact_witnesses",
        lambda *_args, **_kwargs: (),
    )
    monkeypatch.setattr(
        summarizer,
        "_record_readonly_reduction_return_region_proof",
        lambda **_kwargs: ("unit", "proof"),
    )

    class _FakeFunction:
        def getName(self):
            return "readonly_preserve_nonpositive_overlap"

    summarized = summarizer._try_summarize_readonly_pointer_reduction(
        _FakeFunction(),
        object(),
        analysis,
    )

    assert summarized is not None
    summarized_returns, _note = summarized
    retained_nonpositive = next(
        ret for ret in summarized_returns
        if ret.address == nonpositive_ret.address
        and [cond.to_string() for cond in ret.conditions] == [cond.to_string() for cond in nonpositive_ret.conditions]
    )
    assert retained_nonpositive.return_kind == "exact"
    readonly_ret = next(
        ret for ret in summarized_returns
        if getattr(ret.value, "opcode", None) == READONLY_SUM_OPCODE
    )
    assert readonly_ret is not nonpositive_ret

def test_structural_recurrence_summary_ignores_unrelated_early_return_signedness(monkeypatch):
    summarizer = StructuralRecurrenceSummarizer(tracer=None, debug=False)
    pointer_param = {"name": "param_1", "index": 0, "data_type": "int *", "size": 8, "is_signed": False}
    count_param = {"name": "param_2", "index": 1, "data_type": "uint", "size": 4, "is_signed": False}
    analysis = FunctionReturnAnalysis(
        function_name="readonly_unsigned_positive_region_like",
        entry_point="0x1000",
        parameters=[pointer_param, count_param],
        returns=[
            ReturnInfo(
                address="0x1000",
                conditions=[
                    _cond("INT_EQUAL", _param("param_1", size=8), _const(0, size=8)),
                    _cond("INT_SLESS", _const(0), _param("param_2")),
                ],
                value=_const(0),
            ),
            ReturnInfo(
                address="0x1001",
                conditions=[
                    _cond("INT_NOTEQUAL", _param("param_1", size=8), _const(0, size=8)),
                    _cond("INT_LESS", _const(0), _param("param_2")),
                ],
                value=_const(1),
            ),
        ],
    )
    expected_proof = _readonly_accumulator_proof(
        base_ref=LocationBaseRef.parameter("param_1", index=0),
        count_expr=_param("param_2"),
        stride=4,
        element_size=4,
    )

    class _FakeFunction:
        def getName(self):
            return "readonly_unsigned_positive_region_like"

    monkeypatch.setattr(
        summarizer,
        "_infer_readonly_pointer_reduction_parameters",
        lambda _analysis, _high_function: (pointer_param, count_param),
    )
    monkeypatch.setattr(
        summarizer,
        "_detect_readonly_sum_accumulator_proof",
        lambda *_args, **_kwargs: expected_proof,
    )
    monkeypatch.setattr(
        summarizer,
        "_build_readonly_reduction_semantic_witnesses",
        lambda *_args, **_kwargs: (),
    )
    monkeypatch.setattr(
        summarizer,
        "_extract_readonly_reduction_exact_witnesses",
        lambda *_args, **_kwargs: (),
    )

    summarized = summarizer._try_summarize_readonly_pointer_reduction(
        _FakeFunction(),
        object(),
        analysis,
    )

    assert summarized is not None
    summarized_returns, _label = summarized
    summary_return = next(
        ret for ret in summarized_returns
        if getattr(getattr(ret.value, "runtime_ref", None), "count_parameter_name", None) == "param_2"
    )
    assert summary_return.value.runtime_ref.signed_counter is False

def test_structural_recurrence_declines_summary_when_positive_region_returns_cannot_all_be_replaced(monkeypatch):
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
                    _cond("INT_LESS", _const(0), _param("param_2")),
                    _cond("INT_NOTEQUAL", _param("param_3", size=4), _const(0)),
                ],
                value=_const(2),
            ),
        ],
    )
    expected_proof = _readonly_accumulator_proof(
        base_ref=LocationBaseRef.parameter("param_1", index=0),
        count_expr=_param("param_2"),
        stride=4,
        element_size=4,
    )

    class _FakeFunction:
        def getName(self):
            return "readonly_partial_positive_region_like"

    monkeypatch.setattr(
        summarizer,
        "_infer_readonly_pointer_reduction_parameters",
        lambda _analysis, _high_function: (pointer_param, count_param),
    )
    monkeypatch.setattr(
        summarizer,
        "_detect_readonly_sum_accumulator_proof",
        lambda *_args, **_kwargs: expected_proof,
    )
    monkeypatch.setattr(
        summarizer,
        "_readonly_reduction_region_returns_with_signedness",
        lambda analysis, count_param, conditions, expected_signed: [
            ret for ret in (analysis.returns or []) if getattr(ret, "address", None) == "0x1000"
        ],
    )

    assert (
        summarizer._try_summarize_readonly_pointer_reduction(
            _FakeFunction(),
            object(),
            analysis,
        )
        is None
    )

def test_structural_recurrence_does_not_replace_overlap_only_positive_return():
    summarizer = StructuralRecurrenceSummarizer(tracer=None, debug=False)
    pointer_param = {"name": "param_1", "index": 0, "data_type": "int *", "size": 8, "is_signed": False}
    count_param = {"name": "param_2", "index": 1, "data_type": "int", "size": 4, "is_signed": True}
    analysis = FunctionReturnAnalysis(
        function_name="readonly_overlap_only_positive_region_like",
        entry_point="0x1000",
        parameters=[pointer_param, count_param],
        returns=[
            ReturnInfo(
                address="0x1000",
                conditions=[
                    _cond("INT_NOTEQUAL", _param("param_1", size=8), _const(0, size=8)),
                    _cond("INT_SLESS", _const(-10), _param("param_2")),
                ],
                value=_const(1),
            ),
        ],
    )
    proof = _readonly_accumulator_proof(
        base_ref=LocationBaseRef.parameter("param_1", index=0),
        count_expr=_param("param_2"),
        stride=4,
        element_size=4,
    )
    positive_conditions = summarizer._readonly_reduction_positive_conditions(
        analysis,
        pointer_param,
        count_param,
        signed_counter=True,
    )

    replaceable = summarizer._readonly_reduction_replaceable_positive_returns(
        analysis,
        pointer_param,
        count_param,
        positive_conditions,
        positive_conditions,
        expected_signed=True,
        accumulator_proof=proof,
    )

    assert replaceable == []

def test_structural_recurrence_declines_broad_positive_return_with_only_single_count_anchor():
    summarizer = StructuralRecurrenceSummarizer(tracer=None, debug=False)
    pointer_param = {"name": "param_1", "index": 0, "data_type": "int *", "size": 8, "is_signed": False}
    count_param = {"name": "param_2", "index": 1, "data_type": "int", "size": 4, "is_signed": True}
    broad_return = ReturnInfo(
        address="0x1008",
        pcode_time=17,
        conditions=[
            _cond("INT_NOTEQUAL", Expression.parameter("param_1", index=0, data_type="int *", size=8), _const(0, size=8)),
            _cond("INT_SLESS", _const(3), Expression.parameter("param_2", index=1, data_type="int", size=4)),
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
        function_name="readonly_loop_anchor_positive_region_like",
        entry_point="0x1000",
        parameters=[pointer_param, count_param],
        returns=[broad_return],
    )
    proof = _readonly_accumulator_proof(
        base_ref=LocationBaseRef.parameter("param_1", index=0),
        count_expr=Expression.parameter("param_2", index=1, data_type="int", size=4),
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
        _cond("INT_SLESS", _const(0), Expression.parameter("param_2", index=1, data_type="int", size=4)),
    ]
    positive_conditions = broad_positive_conditions[:-1] + [
        _cond("INT_SLESS", _const(3), Expression.parameter("param_2", index=1, data_type="int", size=4)),
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

def test_structural_recurrence_replaces_broad_anchor_when_return_region_value_is_proven():
    summarizer = StructuralRecurrenceSummarizer(tracer=None, debug=False)
    pointer_param = {"name": "param_1", "index": 0, "data_type": "int *", "size": 8, "is_signed": False}
    count_param = {"name": "param_2", "index": 1, "data_type": "int", "size": 4, "is_signed": True}
    broad_return = ReturnInfo(
        address="0x1008",
        pcode_time=17,
        conditions=[
            _cond("INT_NOTEQUAL", Expression.parameter("param_1", index=0, data_type="int *", size=8), _const(0, size=8)),
            _cond("INT_SLESS", _const(3), Expression.parameter("param_2", index=1, data_type="int", size=4)),
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
        function_name="readonly_loop_anchor_region_proven_like",
        entry_point="0x1000",
        parameters=[pointer_param, count_param],
        returns=[broad_return],
    )
    proof = _readonly_accumulator_proof(
        base_ref=LocationBaseRef.parameter("param_1", index=0),
        count_expr=Expression.parameter("param_2", index=1, data_type="int", size=4),
        stride=4,
        element_size=4,
        start_offset=12,
        start_index=3,
        seed_terms=(
            ReadonlyReductionTermRef(byte_offset=0, access_size=4),
            ReadonlyReductionTermRef(byte_offset=4, access_size=4),
            ReadonlyReductionTermRef(byte_offset=8, access_size=4),
        ),
        return_op_refs=(PcodeOpRef(address_offset=0x1008, seq_time=17, mnemonic="RETURN"),),
        return_region_value_proven=True,
    )
    broad_positive_conditions = [
        _cond("INT_NOTEQUAL", Expression.parameter("param_1", index=0, data_type="int *", size=8), _const(0, size=8)),
        _cond("INT_SLESS", _const(0), Expression.parameter("param_2", index=1, data_type="int", size=4)),
    ]
    positive_conditions = broad_positive_conditions[:-1] + [
        _cond("INT_SLESS", _const(3), Expression.parameter("param_2", index=1, data_type="int", size=4)),
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

    assert broad_return in replaceable

def test_structural_recurrence_synthesizes_positive_anchor_from_object_proof():
    summarizer = StructuralRecurrenceSummarizer(tracer=None, debug=False)
    pointer_expr = Expression.parameter("param_1", index=0, data_type="int *", size=8)
    count_expr = Expression.parameter("param_2", index=1, data_type="int", size=4)
    positive_conditions = [
        _cond("INT_NOTEQUAL", pointer_expr, _const(0, size=8)),
        _cond("INT_SLESS", _const(0), count_expr),
    ]
    proof = _readonly_accumulator_proof(
        base_ref=LocationBaseRef.parameter("param_1", index=0),
        count_expr=count_expr,
        stride=4,
        element_size=4,
        return_value_op_refs=(
            PcodeOpRef(address_offset=0x1008, seq_time=47, seq_order=2, mnemonic="RETURN"),
        ),
        return_region_value_proven=True,
    )

    synthetic = summarizer._readonly_synthetic_positive_return_from_proof(
        proof,
        positive_conditions,
        result_size=4,
    )

    assert synthetic is not None
    assert synthetic.address == "00001008"
    assert synthetic.pcode_identity == "00001008:t47"
    assert synthetic.pcode_op_ref == proof.return_value_op_refs[0]
    assert synthetic.conditions == positive_conditions
    assert synthetic.value.expr_type == ExpressionType.CONSTANT

def test_structural_recurrence_refuses_synthetic_anchor_without_return_proof():
    summarizer = StructuralRecurrenceSummarizer(tracer=None, debug=False)
    count_expr = Expression.parameter("param_2", index=1, data_type="int", size=4)
    proof = _readonly_accumulator_proof(
        base_ref=LocationBaseRef.parameter("param_1", index=0),
        count_expr=count_expr,
        stride=4,
        element_size=4,
        return_region_value_proven=False,
    )

    synthetic = summarizer._readonly_synthetic_positive_return_from_proof(
        proof,
        [],
        result_size=4,
    )

    assert synthetic is None

def test_structural_recurrence_broadens_counter_only_region_when_return_value_proof_exists():
    summarizer = StructuralRecurrenceSummarizer(tracer=None, debug=False)
    pointer_param = {"name": "param_1", "index": 0, "data_type": "int *", "size": 8, "is_signed": False}
    count_param = {"name": "param_2", "index": 1, "data_type": "int", "size": 4, "is_signed": True}
    count_expr = Expression.parameter("param_2", index=1, data_type="int", size=4)
    broad_return = ReturnInfo(
        address="0x1018",
        pcode_time=41,
        conditions=[
            _cond("INT_NOTEQUAL", Expression.parameter("param_1", index=0, data_type="int *", size=8), _const(0, size=8)),
            _cond("INT_SLESS", _const(10), count_expr),
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
    exact_one = ReturnInfo(
        address="0x1011",
        conditions=[
            _cond("INT_NOTEQUAL", Expression.parameter("param_1", index=0, data_type="int *", size=8), _const(0, size=8)),
            _cond("INT_EQUAL", count_expr, _const(1)),
        ],
        value=_mem("param_1", 0),
    )
    exact_two = ReturnInfo(
        address="0x1012",
        conditions=[
            _cond("INT_NOTEQUAL", Expression.parameter("param_1", index=0, data_type="int *", size=8), _const(0, size=8)),
            _cond("INT_EQUAL", count_expr, _const(2)),
        ],
        value=Expression.binary_op("INT_ADD", _mem("param_1", 0), _mem("param_1", 4)),
    )
    exact_three = ReturnInfo(
        address="0x1013",
        conditions=[
            _cond("INT_NOTEQUAL", Expression.parameter("param_1", index=0, data_type="int *", size=8), _const(0, size=8)),
            _cond("INT_EQUAL", count_expr, _const(3)),
        ],
        value=Expression.binary_op(
            "INT_ADD",
            _mem("param_1", 8),
            Expression.binary_op("INT_ADD", _mem("param_1", 0), _mem("param_1", 4)),
        ),
    )
    exact_four = ReturnInfo(
        address="0x1014",
        conditions=[
            _cond("INT_NOTEQUAL", Expression.parameter("param_1", index=0, data_type="int *", size=8), _const(0, size=8)),
            _cond("INT_EQUAL", count_expr, _const(4)),
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
        function_name="readonly_counter_only_region_proven_like",
        entry_point="0x1000",
        parameters=[pointer_param, count_param],
        returns=[broad_return, exact_one, exact_two, exact_three, exact_four],
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
        return_op_refs=(PcodeOpRef(address_offset=0x1018, seq_time=41, mnemonic="RETURN"),),
        return_region_value_proven=True,
    )
    broad_positive_conditions = [
        _cond("INT_NOTEQUAL", Expression.parameter("param_1", index=0, data_type="int *", size=8), _const(0, size=8)),
        _cond("INT_SLESS", _const(0), count_expr),
    ]
    positive_conditions = [
        _cond("INT_NOTEQUAL", Expression.parameter("param_1", index=0, data_type="int *", size=8), _const(0, size=8)),
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

    assert broad_return in replaceable

def test_structural_recurrence_accepts_proven_return_value_site_before_final_return():
    summarizer = StructuralRecurrenceSummarizer(tracer=None, debug=False)
    pointer_param = {"name": "param_1", "index": 0, "data_type": "int *", "size": 8, "is_signed": False}
    count_param = {"name": "param_2", "index": 1, "data_type": "int", "size": 4, "is_signed": True}
    broad_return = ReturnInfo(
        address="0x1008",
        pcode_time=23,
        conditions=[
            _cond("INT_NOTEQUAL", Expression.parameter("param_1", index=0, data_type="int *", size=8), _const(0, size=8)),
            _cond("INT_SLESS", _const(3), Expression.parameter("param_2", index=1, data_type="int", size=4)),
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
        function_name="readonly_loop_anchor_region_value_site_like",
        entry_point="0x1000",
        parameters=[pointer_param, count_param],
        returns=[broad_return],
    )
    proof = _readonly_accumulator_proof(
        base_ref=LocationBaseRef.parameter("param_1", index=0),
        count_expr=Expression.parameter("param_2", index=1, data_type="int", size=4),
        stride=4,
        element_size=4,
        start_offset=12,
        start_index=3,
        seed_terms=(
            ReadonlyReductionTermRef(byte_offset=0, access_size=4),
            ReadonlyReductionTermRef(byte_offset=4, access_size=4),
            ReadonlyReductionTermRef(byte_offset=8, access_size=4),
        ),
        return_op_refs=(PcodeOpRef(address_offset=0x1010, seq_time=29, mnemonic="RETURN"),),
        return_value_op_refs=(PcodeOpRef(address_offset=0x1008, seq_time=23, mnemonic="MULTIEQUAL"),),
        return_region_value_proven=True,
    )
    broad_positive_conditions = [
        _cond("INT_NOTEQUAL", Expression.parameter("param_1", index=0, data_type="int *", size=8), _const(0, size=8)),
        _cond("INT_SLESS", _const(0), Expression.parameter("param_2", index=1, data_type="int", size=4)),
    ]
    positive_conditions = broad_positive_conditions[:-1] + [
        _cond("INT_SLESS", _const(3), Expression.parameter("param_2", index=1, data_type="int", size=4)),
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

    assert broad_return in replaceable

def test_structural_recurrence_accepts_adjacent_copy_value_site():
    summarizer = StructuralRecurrenceSummarizer(tracer=None, debug=False)
    ret = ReturnInfo(
        address="0x1008",
        pcode_time=24,
        pcode_order=1,
        conditions=[],
        value=_const(0),
    )
    ref = PcodeOpRef(address_offset=0x1008, seq_time=23, seq_order=0, mnemonic="COPY")

    assert summarizer._return_info_matches_pcode_op_ref(ret, ref) is True

def test_structural_recurrence_matches_adjacent_copy_with_qualified_identity():
    summarizer = StructuralRecurrenceSummarizer(tracer=None, debug=False)
    ret = ReturnInfo(
        address="ram:00001000",
        pcode_identity="ram:00001000:t24:o1",
        conditions=[],
        value=_const(0),
    )
    ref = PcodeOpRef(address_offset=0x1000, seq_time=23, seq_order=0, mnemonic="COPY")

    assert summarizer._return_info_matches_pcode_op_ref(ret, ref) is True

def test_structural_recurrence_matches_explicit_return_value_pcode_ref():
    summarizer = StructuralRecurrenceSummarizer(tracer=None, debug=False)
    value_ref = PcodeOpRef(address_offset=0x2000, seq_time=66, seq_order=6, mnemonic="COPY")
    ret = ReturnInfo(
        address="0x2008",
        pcode_identity="0x2008:t31:o0",
        conditions=[],
        value=_const(0),
        return_value_pcode_op_refs=(value_ref,),
    )

    assert summarizer._return_info_matches_pcode_op_ref(ret, value_ref) is True

def test_structural_recurrence_accepts_reachable_value_ref_for_return_region_proof():
    summarizer = StructuralRecurrenceSummarizer(tracer=None, debug=False)
    seed = _FakeVarnode("seed", size=4)
    add_out = _FakeVarnode("add_out", size=4)
    copy_out = _FakeVarnode("copy_out", size=4)
    add_op = _FakePcodeOp("INT_ADD", [seed, _FakeVarnode("one", size=4)], add_out)
    copy_op = _FakePcodeOp("COPY", [add_out], copy_out)
    return_op = _FakePcodeOp("RETURN", [copy_out], None)
    refs = {
        add_op: PcodeOpRef(address_offset=0x1008, seq_time=21, seq_order=0, block_index=6, mnemonic="INT_ADD"),
        copy_op: PcodeOpRef(address_offset=0x1008, seq_time=22, seq_order=0, block_index=6, mnemonic="COPY"),
        return_op: PcodeOpRef(address_offset=0x1008, seq_time=24, seq_order=1, block_index=6, mnemonic="RETURN"),
    }
    summarizer._make_pcode_op_ref = lambda op: refs.get(op)
    value_refs, return_refs = summarizer._reachable_return_value_and_return_refs_from_varnodes((seed,))

    ret = ReturnInfo(
        address="0x1008",
        pcode_time=24,
        pcode_order=1,
        pcode_op_ref=refs[return_op],
        conditions=[],
        value=_const(0),
    )
    proof = _readonly_accumulator_proof(
        base_ref=LocationBaseRef.parameter("param_1", index=0),
        count_expr=Expression.parameter("param_2", index=1, data_type="int", size=4),
        stride=4,
        element_size=4,
        return_op_refs=return_refs,
        return_value_op_refs=value_refs,
        return_region_value_proven=True,
    )

    assert refs[return_op] in return_refs
    assert refs[add_op] in value_refs
    assert summarizer._readonly_return_region_value_is_proven(ret, [], proof) is True

def test_structural_recurrence_direct_return_refs_reject_arithmetic_contribution():
    summarizer = StructuralRecurrenceSummarizer(tracer=None, debug=False)
    seed = _FakeVarnode("seed", size=4)
    other = _FakeVarnode("other", size=4)
    add_out = _FakeVarnode("add_out", size=4)
    copy_out = _FakeVarnode("copy_out", size=4)
    add_op = _FakePcodeOp("INT_ADD", [seed, other], add_out)
    copy_op = _FakePcodeOp("COPY", [add_out], copy_out)
    return_op = _FakePcodeOp("RETURN", [copy_out], None)
    refs = {
        add_op: PcodeOpRef(address_offset=0x1008, seq_time=21, seq_order=0, block_index=6, mnemonic="INT_ADD"),
        copy_op: PcodeOpRef(address_offset=0x1008, seq_time=22, seq_order=0, block_index=6, mnemonic="COPY"),
        return_op: PcodeOpRef(address_offset=0x1008, seq_time=24, seq_order=1, block_index=6, mnemonic="RETURN"),
    }
    summarizer._make_pcode_op_ref = lambda op: refs.get(op)

    reachable_value_refs, reachable_return_refs = summarizer._reachable_return_value_and_return_refs_from_varnodes((seed,))
    direct_value_refs, direct_return_refs = summarizer._direct_return_value_and_return_refs_from_varnodes((seed,))
    direct_full_value_refs, direct_full_return_refs = summarizer._direct_return_value_and_return_refs_from_varnodes((add_out,))

    assert refs[return_op] in reachable_return_refs
    assert refs[add_op] in reachable_value_refs
    assert direct_value_refs == ()
    assert direct_return_refs == ()
    assert direct_full_value_refs == (refs[copy_op],)
    assert direct_full_return_refs == (refs[return_op],)

def test_structural_recurrence_rejects_value_ref_without_reachable_return_ref():
    summarizer = StructuralRecurrenceSummarizer(tracer=None, debug=False)
    ret = ReturnInfo(
        address="0x1008",
        pcode_op_ref=PcodeOpRef(
            address_offset=0x1008,
            seq_time=24,
            seq_order=1,
            block_index=6,
            mnemonic="RETURN",
        ),
        conditions=[],
        value=_const(0),
    )
    proof = _readonly_accumulator_proof(
        base_ref=LocationBaseRef.parameter("param_1", index=0),
        count_expr=Expression.parameter("param_2", index=1, data_type="int", size=4),
        stride=4,
        element_size=4,
        return_value_op_refs=(
            PcodeOpRef(
                address_offset=0x1008,
                seq_time=21,
                seq_order=0,
                block_index=6,
                mnemonic="INT_ADD",
            ),
        ),
        return_region_value_proven=True,
    )

    assert summarizer._readonly_return_region_value_is_proven(ret, [], proof) is False

def test_structural_recurrence_rejects_region_value_boolean_without_site_refs():
    summarizer = StructuralRecurrenceSummarizer(tracer=None, debug=False)
    ret = ReturnInfo(
        address="0x1008",
        pcode_time=17,
        conditions=[],
        value=_const(0),
    )
    proof = _readonly_accumulator_proof(
        base_ref=LocationBaseRef.parameter("param_1", index=0),
        count_expr=Expression.parameter("param_2", index=1, data_type="int", size=4),
        stride=4,
        element_size=4,
        return_region_value_proven=True,
    )

    assert summarizer._readonly_return_region_value_is_proven(ret, [], proof) is False

def test_structural_recurrence_declines_region_value_proof_for_unmatched_return_site():
    summarizer = StructuralRecurrenceSummarizer(tracer=None, debug=False)
    pointer_param = {"name": "param_1", "index": 0, "data_type": "int *", "size": 8, "is_signed": False}
    count_param = {"name": "param_2", "index": 1, "data_type": "int", "size": 4, "is_signed": True}
    broad_return = ReturnInfo(
        address="0x1008",
        pcode_time=19,
        conditions=[
            _cond("INT_NOTEQUAL", Expression.parameter("param_1", index=0, data_type="int *", size=8), _const(0, size=8)),
            _cond("INT_SLESS", _const(3), Expression.parameter("param_2", index=1, data_type="int", size=4)),
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
        function_name="readonly_loop_anchor_region_wrong_return_site_like",
        entry_point="0x1000",
        parameters=[pointer_param, count_param],
        returns=[broad_return],
    )
    proof = _readonly_accumulator_proof(
        base_ref=LocationBaseRef.parameter("param_1", index=0),
        count_expr=Expression.parameter("param_2", index=1, data_type="int", size=4),
        stride=4,
        element_size=4,
        start_offset=12,
        start_index=3,
        seed_terms=(
            ReadonlyReductionTermRef(byte_offset=0, access_size=4),
            ReadonlyReductionTermRef(byte_offset=4, access_size=4),
            ReadonlyReductionTermRef(byte_offset=8, access_size=4),
        ),
        return_op_refs=(PcodeOpRef(address_offset=0x1010, seq_time=17, mnemonic="RETURN"),),
        return_region_value_proven=True,
    )
    broad_positive_conditions = [
        _cond("INT_NOTEQUAL", Expression.parameter("param_1", index=0, data_type="int *", size=8), _const(0, size=8)),
        _cond("INT_SLESS", _const(0), Expression.parameter("param_2", index=1, data_type="int", size=4)),
    ]
    positive_conditions = broad_positive_conditions[:-1] + [
        _cond("INT_SLESS", _const(3), Expression.parameter("param_2", index=1, data_type="int", size=4)),
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

def test_structural_recurrence_declines_counter_only_residual_without_exact_coverage():
    summarizer = StructuralRecurrenceSummarizer(tracer=None, debug=False)
    pointer_param = {"name": "param_1", "index": 0, "data_type": "int *", "size": 8, "is_signed": False}
    count_param = {"name": "param_2", "index": 1, "data_type": "int", "size": 4, "is_signed": True}
    count_expr = Expression.parameter("param_2", index=1, data_type="int", size=4)
    broad_return = ReturnInfo(
        address="0x1014",
        conditions=[
            _cond("INT_NOTEQUAL", Expression.parameter("param_1", index=0, data_type="int *", size=8), _const(0, size=8)),
            _cond("INT_SLESS", _const(3), count_expr),
            _cond("INT_NOTEQUAL", count_expr, _const(4)),
        ],
        value=Expression.binary_op(
            "INT_ADD",
            _mem("param_1", 12),
            Expression.binary_op(
                "INT_ADD",
                _mem("param_1", 0),
                Expression.binary_op("INT_ADD", _mem("param_1", 4), _mem("param_1", 8)),
            ),
        ),
    )
    analysis = FunctionReturnAnalysis(
        function_name="readonly_loop_anchor_uncovered_residual_like",
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
    positive_conditions = [
        _cond("INT_NOTEQUAL", Expression.parameter("param_1", index=0, data_type="int *", size=8), _const(0, size=8)),
        _cond("INT_SLESS", _const(3), count_expr),
    ]

    replaceable = summarizer._readonly_reduction_replaceable_positive_returns(
        analysis,
        pointer_param,
        count_param,
        positive_conditions,
        positive_conditions,
        expected_signed=True,
        accumulator_proof=proof,
    )

    assert replaceable == []

def test_structural_recurrence_declines_multi_return_shared_counter_residual_hole():
    summarizer = StructuralRecurrenceSummarizer(tracer=None, debug=False)
    pointer_param = {"name": "param_1", "index": 0, "data_type": "int *", "size": 8, "is_signed": False}
    count_param = {"name": "param_2", "index": 1, "data_type": "int", "size": 4, "is_signed": True}
    count_expr = Expression.parameter("param_2", index=1, data_type="int", size=4)
    value = Expression.binary_op(
        "INT_ADD",
        _mem("param_1", 12),
        Expression.binary_op(
            "INT_ADD",
            _mem("param_1", 0),
            Expression.binary_op("INT_ADD", _mem("param_1", 4), _mem("param_1", 8)),
        ),
    )
    shared_conditions = [
        _cond("INT_NOTEQUAL", Expression.parameter("param_1", index=0, data_type="int *", size=8), _const(0, size=8)),
        _cond("INT_SLESS", _const(3), count_expr),
        _cond("INT_NOTEQUAL", count_expr, _const(4)),
    ]
    returns = [
        ReturnInfo(address="0x1020", conditions=list(shared_conditions), value=value),
        ReturnInfo(address="0x1024", conditions=list(shared_conditions), value=value),
    ]
    analysis = FunctionReturnAnalysis(
        function_name="readonly_multi_return_shared_residual_hole_like",
        entry_point="0x1000",
        parameters=[pointer_param, count_param],
        returns=returns,
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
    positive_conditions = [
        _cond("INT_NOTEQUAL", Expression.parameter("param_1", index=0, data_type="int *", size=8), _const(0, size=8)),
        _cond("INT_SLESS", _const(3), count_expr),
    ]

    replaceable = summarizer._readonly_reduction_replaceable_positive_returns(
        analysis,
        pointer_param,
        count_param,
        positive_conditions,
        positive_conditions,
        expected_signed=True,
        accumulator_proof=proof,
    )

    assert replaceable == []

def test_structural_recurrence_residual_coverage_proves_all_excluded_regions():
    summarizer = StructuralRecurrenceSummarizer(tracer=None, debug=False)
    pointer_param = {"name": "param_1", "index": 0, "data_type": "int *", "size": 8, "is_signed": False}
    count_param = {"name": "param_2", "index": 1, "data_type": "int", "size": 4, "is_signed": True}
    count_expr = Expression.parameter("param_2", index=1, data_type="int", size=4)
    value = Expression.binary_op(
        "INT_ADD",
        _mem("param_1", 12),
        Expression.binary_op(
            "INT_ADD",
            _mem("param_1", 0),
            Expression.binary_op("INT_ADD", _mem("param_1", 4), _mem("param_1", 8)),
        ),
    )
    broad_return = ReturnInfo(
        address="0x1030",
        conditions=[
            _cond("INT_NOTEQUAL", Expression.parameter("param_1", index=0, data_type="int *", size=8), _const(0, size=8)),
            _cond("INT_SLESS", _const(3), count_expr),
            _cond("INT_NOTEQUAL", count_expr, _const(4)),
            _cond("INT_NOTEQUAL", count_expr, _const(1000)),
        ],
        value=value,
    )
    exact_count_four_return = ReturnInfo(
        address="0x1034",
        conditions=[
            _cond("INT_NOTEQUAL", Expression.parameter("param_1", index=0, data_type="int *", size=8), _const(0, size=8)),
            _cond("INT_EQUAL", count_expr, _const(4)),
        ],
        value=value,
    )
    analysis = FunctionReturnAnalysis(
        function_name="readonly_residual_sampling_miss_like",
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
    )
    positive_conditions = [
        _cond("INT_NOTEQUAL", Expression.parameter("param_1", index=0, data_type="int *", size=8), _const(0, size=8)),
        _cond("INT_SLESS", _const(3), count_expr),
    ]

    replaceable = summarizer._readonly_reduction_replaceable_positive_returns(
        analysis,
        pointer_param,
        count_param,
        positive_conditions,
        positive_conditions,
        expected_signed=True,
        accumulator_proof=proof,
    )

    assert replaceable == []

def test_structural_recurrence_accepts_materialized_exact_positive_return_without_exact_witness(monkeypatch):
    summarizer = StructuralRecurrenceSummarizer(tracer=None, debug=False)
    pointer_param = {"name": "param_1", "index": 0, "data_type": "int *", "size": 8, "is_signed": False}
    count_param = {"name": "param_2", "index": 1, "data_type": "int", "size": 4, "is_signed": True}
    count_expr = _param("param_2")
    broad_ret = ReturnInfo(
        address="0x1320",
        conditions=[
            _cond("INT_NOTEQUAL", _param("param_1", size=8), _const(0, size=8)),
            _cond("INT_SLESS", _const(0), count_expr),
        ],
        value=Expression.unknown("phi_circular"),
    )
    exact_one = ReturnInfo(
        address="0x1321",
        conditions=[
            _cond("INT_NOTEQUAL", _param("param_1", size=8), _const(0, size=8)),
            _cond("INT_EQUAL", count_expr, _const(1)),
        ],
        value=_mem("param_1", 0),
    )
    exact_two = ReturnInfo(
        address="0x1322",
        conditions=[
            _cond("INT_NOTEQUAL", _param("param_1", size=8), _const(0, size=8)),
            _cond("INT_EQUAL", count_expr, _const(2)),
        ],
        value=Expression.binary_op("INT_ADD", _mem("param_1", 0), _mem("param_1", 4)),
    )
    exact_three = ReturnInfo(
        address="0x1323",
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
    exact_four = ReturnInfo(
        address="0x1324",
        conditions=[
            _cond("INT_NOTEQUAL", _param("param_1", size=8), _const(0, size=8)),
            _cond("INT_EQUAL", count_expr, _const(4)),
        ],
        value=Expression.binary_op(
            "INT_ADD",
            _mem("param_1", 12),
            Expression.binary_op(
                "INT_ADD",
                _mem("param_1", 8),
                Expression.binary_op("INT_ADD", _mem("param_1", 0), _mem("param_1", 4)),
            ),
        ),
    )
    analysis = FunctionReturnAnalysis(
        function_name="readonly_materialized_exact_positive_like",
        entry_point="0x1320",
        parameters=[pointer_param, count_param],
        returns=[broad_ret, exact_one, exact_two, exact_three, exact_four],
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
    broad_positive_conditions = summarizer._readonly_reduction_positive_conditions(
        analysis,
        pointer_param,
        count_param,
        loop_start_index=0,
        signed_counter=True,
    )
    positive_conditions = summarizer._readonly_reduction_positive_conditions(
        analysis,
        pointer_param,
        count_param,
        loop_start_index=3,
        signed_counter=True,
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

    replaceable = summarizer._readonly_reduction_replaceable_positive_returns(
        analysis,
        pointer_param,
        count_param,
        broad_positive_conditions,
        positive_conditions,
        expected_signed=True,
        accumulator_proof=proof,
    )

    assert replaceable == [broad_ret, exact_four]

def test_structural_recurrence_declines_partial_exact_count_carve_out():
    summarizer = StructuralRecurrenceSummarizer(tracer=None, debug=False)
    pointer_param = {"name": "param_1", "index": 0, "data_type": "int *", "size": 8, "is_signed": False}
    count_param = {"name": "param_2", "index": 1, "data_type": "int", "size": 4, "is_signed": True}
    positive_conditions = summarizer._readonly_reduction_positive_conditions(
        FunctionReturnAnalysis(
            function_name="dummy",
            entry_point="0x0",
            parameters=[pointer_param, count_param],
            returns=[],
        ),
        pointer_param,
        count_param,
        signed_counter=True,
    )
    partial_exact_return = ReturnInfo(
        address="0x1100",
        conditions=[
            _cond("INT_NOTEQUAL", _param("param_1", size=8), _const(0, size=8)),
            _cond("INT_EQUAL", _param("param_2"), _const(1)),
            _cond("INT_NOTEQUAL", _param("flag"), _const(0)),
        ],
        value=_const(7),
    )

    assert summarizer._readonly_exact_count_region_is_fully_covered_by_return(
        partial_exact_return,
        positive_conditions,
        count_param,
        1,
    ) is False

def test_exact_counter_value_from_interval_conditions_recovers_singleton_count():
    summarizer = StructuralRecurrenceSummarizer(_FakeTracer("unused", _const(0)), debug=False)

    exact = summarizer._exact_counter_value_from_conditions(
        [
            _cond("INT_SLESSEQUAL", _const(1), _param("param_2")),
            _cond("INT_SLESSEQUAL", _param("param_2"), _const(1)),
        ],
        "param_2",
    )
    exact_two = summarizer._exact_counter_value_from_conditions(
        [
            _cond("INT_SLESS", _const(1), _param("param_2")),
            _cond("INT_SLESSEQUAL", _param("param_2"), _const(2)),
        ],
        "param_2",
    )

    assert exact == 1
    assert exact_two == 2

def test_bounded_prefix_region_drops_only_singleton_counter_selector():
    summarizer = StructuralRecurrenceSummarizer(_FakeTracer("unused", _const(0)), debug=False)
    count_param = {"name": "param_2", "index": 1, "data_type": "ulong", "size": 8, "is_signed": False}
    count_expr = Expression.parameter("param_2", index=1, data_type="ulong", size=8)
    singleton_selector = Condition(
        Expression.binary_op(
            "INT_NOTEQUAL",
            Expression.binary_op(
                "INT_SUB",
                Expression.binary_op("INT_AND", count_expr, Expression.constant(0xFFFFFFFF, size=8)),
                Expression.constant(1, size=8),
            ),
            Expression.constant(0, size=8),
        ),
        negated=True,
    )
    conditions = [
        _cond("INT_NOTEQUAL", Expression.parameter("param_1", index=0, data_type="int *", size=8), _const(0, size=8)),
        _cond("INT_SLESS", _const(0, size=8), count_expr),
        _cond("INT_SLESS", count_expr, _const(4, size=8)),
        singleton_selector,
    ]

    bounded = summarizer._bounded_prefix_region_conditions_from_exact_anchor(
        conditions,
        count_param,
        exact_count=1,
        upper_bound=3,
    )

    assert bounded is not None
    rendered = [condition.to_string() for condition in bounded]
    assert singleton_selector.to_string() not in rendered
    assert "(param_1 != 0)" in rendered
    assert "(0 < param_2)" in rendered
    assert "(param_2 < 4)" in rendered
    assert summarizer._conditions_allow_counter_value(bounded, count_param, 2)
    assert summarizer._conditions_allow_counter_value(bounded, count_param, 3)
    assert not summarizer._conditions_allow_counter_value(bounded, count_param, 4)

def test_bounded_counter_region_coverage_accepts_exact_count_partition():
    summarizer = StructuralRecurrenceSummarizer(_FakeTracer("unused", _const(0)), debug=False)
    count_param = {"name": "param_2", "index": 1, "data_type": "int", "size": 4, "is_signed": True}
    count_expr = Expression.parameter("param_2", index=1, data_type="int", size=4)
    region = [
        _cond("INT_NOTEQUAL", Expression.parameter("param_1", index=0, data_type="int *", size=8), _const(0, size=8)),
        _cond("INT_SLESS", _const(0), count_expr),
        _cond("INT_SLESS", _const(3), count_expr, negated=True),
    ]
    exact_returns = [
        ReturnInfo(
            address="0x1000",
            value=_mem("param_1", (count_value - 1) * 4),
            conditions=region + [summarizer._counter_equality_condition(count_param, count_value)],
        )
        for count_value in (1, 2, 3)
    ]

    assert summarizer._readonly_bounded_counter_region_is_covered_by_exact_returns(
        region,
        exact_returns,
        count_param,
    )
    assert not summarizer._readonly_bounded_counter_region_is_covered_by_exact_returns(
        region,
        exact_returns[:2],
        count_param,
    )
