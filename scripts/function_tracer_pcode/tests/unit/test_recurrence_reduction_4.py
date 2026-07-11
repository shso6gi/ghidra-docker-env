from scripts.function_tracer_pcode.tests.unit._recurrence_fixtures import *

def test_return_analyzer_normalization_does_not_promote_vectorized_readonly_start():
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
    loop_summary = LoopSummaryRef(
        start_expr=Expression.constant(0, size=4),
        limit_expr=count_expr,
        step_expr=Expression.constant(1, size=4),
        term_descriptor=LoopTermDescriptorRef(kind="readonly_memory"),
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
            loop_summary=loop_summary,
            accumulator_proof=accumulator_proof,
        ),
        opcode=READONLY_SUM_OPCODE,
    )
    corrupted = ReturnInfo(
        address="0x1020",
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
        "readonly_partition_preserved_vectorized_start_index",
        return_type="int",
        parameters=params,
        returns=[corrupted],
    )

    analyzer._normalize_return_partition(analysis)

    normalized_conditions = [cond.to_string() for cond in analysis.returns[0].conditions]

    assert normalized_conditions == ["(0 < param_2)"]
    assert "(3 < param_2)" not in normalized_conditions

def test_readonly_summary_supersedes_only_returns_proven_inside_summary_region():
    summarizer = StructuralRecurrenceSummarizer(_FakeTracer("unused", _const(0)), debug=False)
    pointer_expr = _param("param_1", size=8)
    count_expr = Expression.parameter("param_2", index=1, data_type="int", size=4)
    pointer_nonnull = _cond("INT_NOTEQUAL", pointer_expr, _const(0, size=8))
    positive = _cond("INT_SLESS", _const(0), count_expr)
    not_count_one = Condition(
        Expression.binary_op("INT_EQUAL", count_expr, _const(1)),
        negated=True,
    )
    summary_conditions = [pointer_nonnull, positive, not_count_one]
    broad_ret = ReturnInfo(
        address="0x1000",
        value=_const(0),
        conditions=list(summary_conditions),
    )
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
    exact_count_one = ReturnInfo(
        address="0x1004",
        value=_mem("param_1", 0),
        conditions=[pointer_nonnull, positive, Condition(selector_expr, negated=True)],
    )
    nonpositive = ReturnInfo(
        address="0x1008",
        value=_const(0),
        conditions=[
            pointer_nonnull,
            _cond("INT_SLESSEQUAL", count_expr, _const(0)),
        ],
    )

    assert summarizer._readonly_return_is_superseded_by_summary_region(
        broad_ret,
        summary_conditions,
        [broad_ret],
    )
    assert not summarizer._readonly_return_is_superseded_by_summary_region(
        exact_count_one,
        summary_conditions,
        [broad_ret],
    )
    assert not summarizer._readonly_return_is_superseded_by_summary_region(
        nonpositive,
        summary_conditions,
        [broad_ret],
    )
