from scripts.function_tracer_pcode.tests.unit._memory_model_fixtures import *
from scripts.function_tracer_pcode.proof.formula.input_correspondence import build_input_correspondence_set

def test_formula_builder_lowers_nested_symbolic_post_state_reads_before_smt_emission():
    trace = Expression.parameter("trace", 0, size=8)
    start = Expression.parameter("start", 1, size=4)
    limit = Expression.parameter("limit", 2, size=4)
    steps_addr = Expression.binary_op("INT_ADD", trace, Expression.constant(4, 8))
    odd_delta = Expression.unary_op("INT_2COMP", start)

    trace_nonnull = Condition(
        Expression.binary_op("INT_NOTEQUAL", trace, Expression.constant(0, 8)),
        False,
    )
    loop_active = Condition(
        Expression.binary_op("INT_SLESS", start, limit),
        False,
    )
    final_iter = Condition(
        Expression.binary_op(
            "INT_EQUAL",
            limit,
            Expression.binary_op("INT_ADD", start, Expression.constant(1, 4)),
        ),
        False,
    )
    odd_iteration = Condition(
        Expression.binary_op(
            "INT_NOTEQUAL",
            Expression.binary_op("INT_AND", start, Expression.constant(1, 4)),
            Expression.constant(0, 4),
        ),
        False,
    )
    even_iteration = odd_iteration.negate()

    params = [
        _param("trace", size=8, is_signed=False),
        _param("start", size=4, index=1),
        _param("limit", size=4, index=2),
    ]
    symbolic_expr = Expression.binary_op(
        "INT_ADD",
        post_state_read_expression_for_location(
            _loc("trace", 0, 4),
            params,
            symbolic=True,
        ),
        Expression.binary_op(
            "INT_SUB",
            Expression.binary_op(
                "INT_ADD",
                limit,
                post_state_read_expression_for_location(
                    _loc("trace", 4, 4),
                    params,
                    symbolic=True,
                ),
            ),
            start,
        ),
    )
    effects = [
        StoreEffect(
            location=_loc("trace", 0, 4),
            value=Expression.binary_op("INT_ADD", Expression.memory(trace, size=4), odd_delta),
            conditions=[trace_nonnull, loop_active, odd_iteration, final_iter],
            order_key=5,
        ),
        StoreEffect(
            location=_loc("trace", 0, 4),
            value=Expression.binary_op("INT_ADD", Expression.memory(trace, size=4), start),
            conditions=[trace_nonnull, loop_active, even_iteration, final_iter],
            order_key=5,
        ),
        StoreEffect(
            location=_loc("trace", 4, 4),
            value=Expression.binary_op(
                "INT_SUB",
                Expression.binary_op("INT_ADD", limit, Expression.memory(steps_addr, size=4)),
                start,
            ),
            conditions=[trace_nonnull, loop_active, final_iter],
            order_key=6,
        ),
    ]
    explicit_expr = Expression.binary_op(
        "INT_ADD",
        Expression.binary_op(
            "INT_ADD",
            Expression.memory(steps_addr, size=4),
            Expression.constant(1, 4),
        ),
        Expression.binary_op(
            "INT_ADD",
            Expression.memory(trace, size=4),
            odd_delta,
        ),
    )
    analysis1 = FunctionReturnAnalysis(
        function_name="f1",
        entry_point="0x0",
        parameters=params,
        returns=[
            ReturnInfo(
                address="0x1",
                value=explicit_expr,
                conditions=[trace_nonnull, loop_active, odd_iteration, final_iter],
            )
        ],
        return_type="int",
    )
    analysis2 = FunctionReturnAnalysis(
        function_name="f2",
        entry_point="0x0",
        parameters=params,
        returns=[
            ReturnInfo(
                address="0x2",
                value=symbolic_expr,
                conditions=[trace_nonnull, loop_active, odd_iteration, final_iter],
            )
        ],
        return_type="int",
        effect_summary=EffectSummary(
            parameter_names=["trace", "start", "limit"],
            effects=effects,
        ),
    )

    formula = FormulaBuilder(debug=False, exclude_ub=False).build_equivalence_formula_extended(
        analysis1,
        analysis2,input_correspondence=build_input_correspondence_set(analysis1, analysis2),
    ).formula

    assert "__locread__" not in formula
    assert "return_2" in formula

def test_normalize_post_state_expression_collapses_ordered_alias_updates_to_post_state_memory():
    dst = Expression.parameter("dst", 0, size=8)
    src = Expression.parameter("src", 1, size=8)
    delta = Expression.parameter("delta", 2, size=4)
    dst_nonnull = Condition(
        Expression.binary_op("INT_NOTEQUAL", dst, Expression.constant(0, 8)),
        False,
    )
    src_nonnull = Condition(
        Expression.binary_op("INT_NOTEQUAL", src, Expression.constant(0, 8)),
        False,
    )
    alias_cond = Condition(
        Expression.binary_op("INT_EQUAL", dst, src),
        False,
    )
    effects = [
        StoreEffect(
            location=_loc("dst", 0, 4),
            value=Expression.binary_op("INT_ADD", Expression.memory(dst, size=4), delta),
            conditions=[dst_nonnull, src_nonnull],
            order_key=10,
        ),
        StoreEffect(
            location=_loc("src", 0, 4),
            value=Expression.binary_op(
                "INT_ADD",
                Expression.memory(src, size=4),
                Expression.constant(4294967295, 4),
            ),
            conditions=[dst_nonnull, src_nonnull],
            order_key=20,
        ),
    ]
    expr = Expression.binary_op(
        "INT_ADD",
        Expression.binary_op("INT_ADD", Expression.memory(dst, size=4), delta),
        Expression.constant(4294967295, 4),
    )
    params = [
        _param("dst", size=8, is_signed=False),
        _param("src", size=8, is_signed=False, index=1),
        _param("delta", size=4, index=2),
    ]
    conditions = [dst_nonnull, src_nonnull, alias_cond]

    collapsed = collapse_post_state_expr_to_canonical_memory(
        expr,
        effects,
        params,
        return_conditions=conditions,
    )
    normalized = normalize_post_state_expression(
        expr,
        conditions,
        effects,
        params,
    )

    assert collapsed is not None
    assert collapsed.to_string() == "MEM[dst]"
    assert normalized.to_string() == "MEM[dst]"

def test_normalize_post_state_expression_keeps_ordered_alias_update_when_alias_not_implied():
    dst = Expression.parameter("dst", 0, size=8)
    src = Expression.parameter("src", 1, size=8)
    delta = Expression.parameter("delta", 2, size=4)
    dst_nonnull = Condition(
        Expression.binary_op("INT_NOTEQUAL", dst, Expression.constant(0, 8)),
        False,
    )
    src_nonnull = Condition(
        Expression.binary_op("INT_NOTEQUAL", src, Expression.constant(0, 8)),
        False,
    )
    effects = [
        StoreEffect(
            location=_loc("dst", 0, 4),
            value=Expression.binary_op("INT_ADD", Expression.memory(dst, size=4), delta),
            conditions=[dst_nonnull, src_nonnull],
            order_key=10,
        ),
        StoreEffect(
            location=_loc("src", 0, 4),
            value=Expression.binary_op(
                "INT_ADD",
                Expression.memory(src, size=4),
                Expression.constant(4294967295, 4),
            ),
            conditions=[dst_nonnull, src_nonnull],
            order_key=20,
        ),
    ]
    expr = Expression.binary_op(
        "INT_ADD",
        Expression.binary_op("INT_ADD", Expression.memory(dst, size=4), delta),
        Expression.constant(4294967295, 4),
    )
    params = [
        _param("dst", size=8, is_signed=False),
        _param("src", size=8, is_signed=False, index=1),
        _param("delta", size=4, index=2),
    ]
    conditions = [dst_nonnull, src_nonnull]

    collapsed = collapse_post_state_expr_to_canonical_memory(
        expr,
        effects,
        params,
        return_conditions=conditions,
    )
    normalized = normalize_post_state_expression(
        expr,
        conditions,
        effects,
        params,
    )

    assert collapsed is None
    assert normalized.to_string() == "(MEM[dst] + 4294967295)"

def test_normalize_post_state_expression_stays_conservative_when_guards_do_not_match():
    value = Expression.parameter("value", 0, size=8)
    delta = Expression.parameter("delta", 1, size=4)
    negate = Expression.parameter("negate", 2, size=8)
    negate_zero = Condition(
        Expression.binary_op("INT_EQUAL", negate, Expression.constant(0, 8)),
        False,
    )
    other_guard = Condition(
        Expression.binary_op("INT_EQUAL", negate, Expression.constant(1, 8)),
        False,
    )
    expr = Expression.binary_op("INT_ADD", Expression.memory(value, size=4), delta)

    normalized = normalize_post_state_expression(
        expr,
        [negate_zero],
        [
            StoreEffect(
                location=_loc("value", 0, 4),
                value=Expression.binary_op("INT_ADD", Expression.memory(value, size=4), delta),
                conditions=[other_guard],
                order_key=5,
            ),
        ],
        [
            _param("value", size=8, is_signed=False),
            _param("delta", size=4, index=1),
            _param("negate", size=8, index=2),
        ],
    )

    assert normalized.to_string() == "(MEM[value] + delta)"

def test_normalize_post_state_expression_promotes_raw_memory_leaf_to_symbolic_post_state_read():
    ptr = Expression.parameter("ptr", 0, size=8)
    value = Expression.parameter("value", 1, size=4)
    ptr_nonnull = Condition(
        Expression.binary_op("INT_NOTEQUAL", ptr, Expression.constant(0, 8)),
        False,
    )

    normalized = normalize_post_state_expression(
        Expression.memory(ptr, size=4),
        [ptr_nonnull],
        [
            StoreEffect(
                location=_loc("ptr", 0, 4),
                value=Expression.unary_op("INT_2COMP", value),
                conditions=[ptr_nonnull],
                order_key=1,
            ),
        ],
        [
            _param("ptr", size=8, is_signed=False),
            _param("value", size=4, is_signed=True, index=1),
        ],
        symbolic_post_state=True,
    )

    assert normalized is not None
    assert normalized.expr_type == ExpressionType.MEMORY
    assert _runtime_location(normalized) == _loc("ptr", 0, 4)

def test_normalize_post_state_expression_replays_definite_simple_store_then_read():
    ptr = Expression.parameter("ptr", 0, size=8)
    value = Expression.parameter("value", 1, size=4)
    ptr_nonnull = Condition(
        Expression.binary_op("INT_NOTEQUAL", ptr, Expression.constant(0, 8)),
        False,
    )
    expr = Expression.binary_op(
        "INT_ADD",
        Expression.memory(ptr, size=4),
        Expression.constant(4294967295, 4),
    )

    normalized = normalize_post_state_expression(
        expr,
        [ptr_nonnull],
        [
            StoreEffect(
                location=_loc("ptr", 0, 4),
                value=Expression.binary_op("INT_ADD", value, Expression.constant(3, 4)),
                conditions=[ptr_nonnull],
                order_key=5,
            ),
        ],
        [
            _param("ptr", size=8, is_signed=False),
            _param("value", size=4, is_signed=True, index=1),
        ],
    )

    assert normalized.to_string() == "((value + 3) + 4294967295)"

def test_normalize_post_state_expression_rewrites_wide_param_store_then_read_per_branch():
    param_1 = Expression.parameter("param_1", 0, size=8)
    param_2 = Expression.parameter("param_2", 1, size=8)
    param_3 = Expression.parameter("param_3", 2, size=4)
    param_4 = Expression.parameter("param_4", 3, size=8)
    param_4_zero = Condition(
        Expression.binary_op("INT_EQUAL", param_4, Expression.constant(0, 8)),
        False,
    )
    param_4_nonzero = param_4_zero.negate()
    param_2_lo = Expression.binary_op("SUBPIECE", param_2, Expression.constant(0, 4))
    param_2_lo.size = 4
    expr = Expression.binary_op(
        "INT_SUB",
        Expression.memory(param_1, size=4),
        param_2_lo,
    )

    normalized_zero = normalize_post_state_expression(
        expr,
        [param_4_zero],
        [
            StoreEffect(
                location=_loc("param_1", 0, 4),
                value=Expression.binary_op(
                    "INT_ADD",
                    Expression.binary_op(
                        "INT_ADD",
                        Expression.binary_op(
                            "INT_MULT",
                            param_2_lo,
                            Expression.constant(2, 4),
                        ),
                        Expression.constant(11, 4),
                    ),
                    param_3,
                ),
                conditions=[param_4_zero],
                order_key=5,
            ),
            StoreEffect(
                location=_loc("param_1", 0, 4),
                value=Expression.binary_op("INT_XOR", param_2_lo, param_3),
                conditions=[param_4_nonzero],
                order_key=5,
            ),
        ],
        [
            _param("param_1", size=8, is_signed=False),
            _param("param_2", size=8, is_signed=False, index=1),
            _param("param_3", size=4, index=2),
            _param("param_4", size=8, is_signed=False, index=3),
        ],
    )
    normalized_nonzero = normalize_post_state_expression(
        expr,
        [param_4_nonzero],
        [
            StoreEffect(
                location=_loc("param_1", 0, 4),
                value=Expression.binary_op(
                    "INT_ADD",
                    Expression.binary_op(
                        "INT_ADD",
                        Expression.binary_op(
                            "INT_MULT",
                            param_2_lo,
                            Expression.constant(2, 4),
                        ),
                        Expression.constant(11, 4),
                    ),
                    param_3,
                ),
                conditions=[param_4_zero],
                order_key=5,
            ),
            StoreEffect(
                location=_loc("param_1", 0, 4),
                value=Expression.binary_op("INT_XOR", param_2_lo, param_3),
                conditions=[param_4_nonzero],
                order_key=5,
            ),
        ],
        [
            _param("param_1", size=8, is_signed=False),
            _param("param_2", size=8, is_signed=False, index=1),
            _param("param_3", size=4, index=2),
            _param("param_4", size=8, is_signed=False, index=3),
        ],
    )

    assert normalized_zero.to_string() == (
        "(((((param_2 & 4294967295) * 2) + 11) + param_3) - (param_2 & 4294967295))"
    )
    assert normalized_nonzero.to_string() == (
        "(((param_2 & 4294967295) ^ param_3) - (param_2 & 4294967295))"
    )

def test_expression_expander_prefers_canonical_post_state_memory_after_observed_load_rewrite():
    value = Expression.parameter("value", 0, size=8)
    delta = Expression.parameter("delta", 1, size=4)
    negate = Expression.parameter("negate", 2, size=8)
    negate_zero = Condition(
        Expression.binary_op("INT_EQUAL", negate, Expression.constant(0, 8)),
        False,
    )
    negate_nonzero = negate_zero.negate()

    effect_summary = EffectSummary(
        parameter_names=["value", "delta", "negate"],
        effects=[
            StoreEffect(
                location=_loc("value", 0, 4),
                value=Expression.binary_op("INT_ADD", Expression.memory(value, size=4), delta),
                conditions=[negate_zero],
                order_key=5,
            ),
            StoreEffect(
                location=_loc("value", 0, 4),
                value=Expression.binary_op("INT_SUB", delta, Expression.memory(value, size=4)),
                conditions=[negate_nonzero],
                order_key=5,
            ),
        ],
    )

    expander = ExpressionExpander(
        tracer=None,
        condition_tracker=None,
        debug=False,
        effect_summary=effect_summary,
        parameters=[
            _param("value", size=8, is_signed=False),
            _param("delta", size=4, index=1),
            _param("negate", size=8, index=2),
        ],
    )

    canonicalized = expander._canonicalize_traced_expression(
        Expression.memory(value, size=4, read_order_key=9),
        [negate_zero],
    )

    assert canonicalized.to_string() == "MEM[value]"

def test_expression_expander_keeps_root_composite_observed_effect_value_until_return_normalization():
    value = Expression.parameter("value", 0, size=8)
    value_nonnull = Condition(
        Expression.binary_op("INT_NOTEQUAL", value, Expression.constant(0, 8)),
        False,
    )
    observed = Expression.memory(
        value,
        size=4,
        read_order_key=19,
        runtime_ref=_observed_read("value", index=0, size=4, order_key=19),
    )
    effect_summary = EffectSummary(
        parameter_names=["value"],
        effects=[
            StoreEffect(
                location=_loc("value", 0, 4),
                value=Expression.binary_op(
                    "INT_ADD",
                    Expression.memory(value, size=4),
                    Expression.constant(4294967295, 4),
                ),
                conditions=[value_nonnull],
                order_key=21,
            ),
        ],
    )

    expander = ExpressionExpander(
        tracer=None,
        condition_tracker=None,
        debug=False,
        effect_summary=effect_summary,
        parameters=[_param("value", size=8, is_signed=False)],
    )

    canonicalized = expander._canonicalize_traced_expression(
        Expression.binary_op(
            "INT_ADD",
            observed,
            Expression.constant(4294967295, 4),
        ),
        [value_nonnull],
    )

    assert canonicalized.to_string() == "(MEM[value] + 4294967295)"

def test_return_analyzer_keeps_canonical_post_state_return_unchanged():
    a = Expression.parameter("a", 0, size=8)
    b = Expression.parameter("b", 1, size=8)
    swap_taken = Condition(
        Expression.binary_op("INT_SLESS", Expression.memory(b, size=4), Expression.memory(a, size=4)),
        False,
    )
    effect_summary = EffectSummary(
        parameter_names=["a", "b"],
        effects=[
            StoreEffect(
                location=_loc("a", 0, 4),
                value=Expression.memory(b, size=4),
                conditions=[swap_taken],
                order_key=1,
            ),
            StoreEffect(
                location=_loc("b", 0, 4),
                value=Expression.memory(a, size=4),
                conditions=[swap_taken],
                order_key=2,
            ),
        ],
    )
    analyzer = ReturnAnalyzer(program=object(), debug=False)
    analyzer._current_effect_summary = effect_summary
    analyzer._current_parameters = [
        _param("a", size=8, is_signed=False),
        _param("b", size=8, is_signed=False, index=1),
    ]
    normalized = analyzer._normalize_expanded_return_value(
        Expression.binary_op("INT_SUB", Expression.memory(b, size=4), Expression.memory(a, size=4)),
        [swap_taken],
    )

    assert normalized.to_string() == "(MEM[b] - MEM[a])"

def test_return_analyzer_prefers_definite_branch_store_value_over_canonical_post_state_memory():
    param_1 = Expression.parameter("param_1", 0, size=8)
    param_2 = Expression.parameter("param_2", 1, size=8)
    param_3 = Expression.parameter("param_3", 2, size=4)
    param_4 = Expression.parameter("param_4", 3, size=8)
    param_4_zero = Condition(
        Expression.binary_op("INT_EQUAL", param_4, Expression.constant(0, 8)),
        False,
    )
    param_4_nonzero = param_4_zero.negate()
    param_2_lo = Expression.binary_op("SUBPIECE", param_2, Expression.constant(0, 4))
    param_2_lo.size = 4
    expr = Expression.binary_op(
        "INT_SUB",
        Expression.memory(param_1, size=4),
        param_2_lo,
    )

    analyzer = ReturnAnalyzer(program=object(), debug=False)
    analyzer._current_effect_summary = EffectSummary(
        parameter_names=["param_1", "param_2", "param_3", "param_4"],
        effects=[
            StoreEffect(
                location=_loc("param_1", 0, 4),
                value=Expression.binary_op(
                    "INT_ADD",
                    Expression.binary_op(
                        "INT_ADD",
                        Expression.binary_op(
                            "INT_MULT",
                            param_2_lo,
                            Expression.constant(2, 4),
                        ),
                        Expression.constant(11, 4),
                    ),
                    param_3,
                ),
                conditions=[param_4_zero],
                order_key=5,
            ),
            StoreEffect(
                location=_loc("param_1", 0, 4),
                value=Expression.binary_op("INT_XOR", param_2_lo, param_3),
                conditions=[param_4_nonzero],
                order_key=5,
            ),
        ],
    )
    analyzer._current_parameters = [
        _param("param_1", size=8, is_signed=False),
        _param("param_2", size=8, is_signed=False, index=1),
        _param("param_3", size=4, index=2),
        _param("param_4", size=8, is_signed=False, index=3),
    ]

    normalized_zero = analyzer._normalize_expanded_return_value(
        expr,
        [param_4_zero],
    )
    normalized_nonzero = analyzer._normalize_expanded_return_value(
        expr,
        [param_4_nonzero],
    )

    assert normalized_zero.to_string() == (
        "(((((param_2 & 4294967295) * 2) + 11) + param_3) - (param_2 & 4294967295))"
    )
    assert normalized_nonzero.to_string() == (
        "(((param_2 & 4294967295) ^ param_3) - (param_2 & 4294967295))"
    )

def test_return_analyzer_canonicalizes_partially_replayed_post_state_before_reapplying_effects():
    stats = Expression.parameter("param_1", 0, size=8)
    a = Expression.parameter("param_2", 1, size=4)
    b = Expression.parameter("param_3", 2, size=4)
    delta = Expression.parameter("param_4", 3, size=4)
    nonnull = Condition(
        Expression.binary_op("INT_NOTEQUAL", stats, Expression.constant(0, 8)),
        False,
    )
    count_addr = Expression.binary_op("INT_ADD", stats, Expression.constant(4, 8))
    partially_replayed = Expression.binary_op(
        "INT_ADD",
        Expression.binary_op(
            "INT_ADD",
            Expression.binary_op("INT_ADD", a, b),
            delta,
        ),
        Expression.binary_op(
            "INT_ADD",
            Expression.binary_op("INT_ADD", Expression.memory(count_addr, size=4), Expression.constant(1, 4)),
            Expression.constant(1, 4),
        ),
    )

    analyzer = ReturnAnalyzer(program=object(), debug=False)
    analyzer._current_effect_summary = EffectSummary(
        parameter_names=["param_1", "param_2", "param_3", "param_4"],
        effects=[
            StoreEffect(
                location=_loc("param_1", 0, 4),
                value=Expression.binary_op("INT_ADD", a, b),
                conditions=[nonnull],
                order_key=1,
            ),
            StoreEffect(
                location=_loc("param_1", 4, 4),
                value=Expression.binary_op("INT_ADD", Expression.memory(count_addr, size=4), Expression.constant(1, 4)),
                conditions=[nonnull],
                order_key=2,
            ),
            StoreEffect(
                location=_loc("param_1", 0, 4),
                value=Expression.binary_op("INT_ADD", Expression.memory(stats, size=4), delta),
                conditions=[nonnull],
                order_key=3,
            ),
            StoreEffect(
                location=_loc("param_1", 4, 4),
                value=Expression.binary_op("INT_ADD", Expression.memory(count_addr, size=4), Expression.constant(1, 4)),
                conditions=[nonnull],
                order_key=4,
            ),
        ],
    )
    analyzer._current_parameters = [
        _param("param_1", size=8, is_signed=False),
        _param("param_2", size=4, index=1),
        _param("param_3", size=4, index=2),
        _param("param_4", size=4, index=3),
    ]

    normalized = analyzer._normalize_expanded_return_value(partially_replayed, [nonnull])

    assert expression_contains_post_state_reads(normalized) is False
    assert normalized.to_string() == "(((param_2 + param_3) + param_4) + ((MEM[(param_1 + 4)] + 1) + 1))"

    lowered = lower_post_state_expression_for_smt(
        normalized,
        [nonnull],
        analyzer._current_effect_summary.effects,
        analyzer._current_parameters,
    )

    assert lowered.to_string() == "(((param_2 + param_3) + param_4) + ((MEM[(param_1 + 4)] + 1) + 1))"

def test_return_analyzer_falls_back_to_definite_replay_when_symbolic_roundtrip_is_rejected():
    trace = Expression.parameter("param_1", 0, size=8)
    start = Expression.parameter("param_2", 1, size=4)
    limit = Expression.parameter("param_3", 2, size=4)
    steps_addr = Expression.binary_op("INT_ADD", trace, Expression.constant(4, 8))

    trace_nonnull = Condition(
        Expression.binary_op("INT_NOTEQUAL", trace, Expression.constant(0, 8)),
        False,
    )
    loop_active = Condition(
        Expression.binary_op("INT_SLESS", start, limit),
        False,
    )
    odd_iteration = Condition(
        Expression.binary_op(
            "INT_NOTEQUAL",
            Expression.binary_op("INT_AND", start, Expression.constant(1, 4)),
            Expression.constant(0, 4),
        ),
        False,
    )
    final_iter = Condition(
        Expression.binary_op(
            "INT_EQUAL",
            limit,
            Expression.binary_op("INT_ADD", start, Expression.constant(1, 4)),
        ),
        False,
    )

    expr = Expression.binary_op(
        "INT_ADD",
        Expression.binary_op("INT_SUB", Expression.memory(trace, size=4), start),
        Expression.memory(steps_addr, size=4),
    )

    analyzer = ReturnAnalyzer(program=object(), debug=False)
    analyzer._current_effect_summary = EffectSummary(
        parameter_names=["param_1", "param_2", "param_3"],
        effects=[
            StoreEffect(
                location=_loc("param_1", 0, 4),
                value=Expression.binary_op(
                    "INT_ADD",
                    Expression.memory(trace, size=4),
                    Expression.unary_op("INT_2COMP", start),
                ),
                conditions=[trace_nonnull, loop_active, odd_iteration, final_iter],
                order_key=5,
            ),
            StoreEffect(
                location=_loc("param_1", 4, 4),
                value=Expression.binary_op(
                    "INT_ADD",
                    Expression.memory(steps_addr, size=4),
                    Expression.constant(1, 4),
                ),
                conditions=[trace_nonnull, loop_active, final_iter],
                order_key=6,
            ),
        ],
    )
    analyzer._current_parameters = [
        _param("param_1", size=8, is_signed=False),
        _param("param_2", size=4, index=1),
        _param("param_3", size=4, index=2),
    ]

    normalized = analyzer._normalize_expanded_return_value(
        expr,
        [trace_nonnull, loop_active, odd_iteration, final_iter],
    )

    assert normalized.to_string() == "((MEM[param_1] - param_2) + (MEM[(param_1 + 4)] + 1))"

def test_return_analyzer_keeps_symbolic_root_post_state_read_when_roundtrip_matches_materialized_leaf():
    ptr = Expression.parameter("param_1", 0, size=8)
    value = Expression.parameter("param_2", 1, size=4)
    flag = Expression.parameter("param_3", 2, size=4)
    ptr_nonnull = Condition(
        Expression.binary_op("INT_NOTEQUAL", ptr, Expression.constant(0, 8)),
        False,
    )
    flag_zero = Condition(
        Expression.binary_op("INT_EQUAL", flag, Expression.constant(0, 4)),
        False,
    )

    analyzer = ReturnAnalyzer(program=object(), debug=False)
    analyzer._current_effect_summary = EffectSummary(
        parameter_names=["param_1", "param_2", "param_3"],
        effects=[
            StoreEffect(
                location=_loc("param_1", 0, 4),
                value=Expression.unary_op("INT_2COMP", value),
                conditions=[ptr_nonnull, flag_zero],
                order_key=1,
            ),
        ],
    )
    analyzer._current_parameters = [
        _param("param_1", size=8, is_signed=False),
        _param("param_2", size=4, is_signed=True, index=1),
        _param("param_3", size=4, is_signed=False, index=2),
    ]

    normalized = analyzer._normalize_expanded_return_value(
        Expression.memory(ptr, size=4),
        [ptr_nonnull, flag_zero],
    )

    assert normalized is not None
    assert normalized.expr_type == ExpressionType.MEMORY
    assert _runtime_location(normalized) == _loc("param_1", 0, 4)

    lowered = lower_post_state_expression_for_smt(
        normalized,
        [ptr_nonnull, flag_zero],
        analyzer._current_effect_summary.effects,
        analyzer._current_parameters,
    )

    assert lowered.to_string() == "(-param_2)"

def test_expression_expander_rewrites_observed_loads_before_post_state_canonicalization_duplicate_path():
    a = Expression.parameter("a", 0, size=8)
    b = Expression.parameter("b", 1, size=8)
    nonnull_a = Condition(Expression.binary_op("INT_NOTEQUAL", a, Expression.constant(0, 8)), False)
    nonnull_b = Condition(Expression.binary_op("INT_NOTEQUAL", b, Expression.constant(0, 8)), False)
    swap_taken = Condition(
        Expression.binary_op("INT_SLESS", Expression.memory(b, size=4), Expression.memory(a, size=4)),
        False,
    )
    effect_summary = EffectSummary(
        parameter_names=["a", "b"],
        effects=[
            StoreEffect(
                location=_loc("a", 0, 4),
                value=Expression.memory(b, size=4),
                conditions=[swap_taken],
                order_key=10,
            ),
            StoreEffect(
                location=_loc("b", 0, 4),
                value=Expression.memory(a, size=4),
                conditions=[swap_taken],
                order_key=11,
            ),
        ],
    )
    traced = Expression.binary_op(
        "INT_SUB",
        Expression.memory(a, size=4, read_order_key=20),
        Expression.memory(b, size=4, read_order_key=21),
    )

    class FakeTracer:
        pass

    expander = ExpressionExpander(
        FakeTracer(),
        condition_tracker=None,
        debug=False,
        effect_summary=effect_summary,
        parameters=[
            _param("a", size=8, is_signed=False),
            _param("b", size=8, is_signed=False, index=1),
        ],
    )

    canonicalized = expander._canonicalize_traced_expression(
        traced,
        [nonnull_a, nonnull_b],
    )

    assert canonicalized.to_string() == "(MEM[a] - MEM[b])"

def test_expression_expander_infers_multiequal_location_by_identical_observed_load():
    a = Expression.parameter("a", 0, size=8)
    b = Expression.parameter("b", 1, size=8)
    swap_taken = Condition(
        Expression.binary_op("INT_SLESS", Expression.memory(b, size=4), Expression.memory(a, size=4)),
        False,
    )
    no_swap = swap_taken.negate()
    effect_summary = EffectSummary(
        parameter_names=["a", "b"],
        effects=[
            StoreEffect(
                location=_loc("a", 0, 4),
                value=Expression.memory(b, size=4),
                conditions=[swap_taken],
                order_key=1,
            ),
            StoreEffect(
                location=_loc("b", 0, 4),
                value=Expression.memory(a, size=4),
                conditions=[swap_taken],
                order_key=2,
            ),
        ],
    )

    class FakeTracer:
        debug = False

    expander = ExpressionExpander(
        FakeTracer(),
        condition_tracker=None,
        debug=False,
        effect_summary=effect_summary,
        parameters=[
            _param("a", size=8, is_signed=False),
            _param("b", size=8, is_signed=False, index=1),
        ],
    )

    inferred = expander._infer_multiequal_canonical_location(
        [
            ExpandedValue(Expression.memory(a, size=4), [swap_taken]),
            ExpandedValue(Expression.memory(a, size=4), [no_swap]),
        ],
        depth=0,
    )

    assert inferred == _loc("a", 0, 4)

def test_expression_expander_rewrites_observed_loads_before_post_state_canonicalization():
    a = Expression.parameter("a", 0, size=8)
    b = Expression.parameter("b", 1, size=8)
    nonnull_a = Condition(Expression.binary_op("INT_NOTEQUAL", a, Expression.constant(0, 8)), False)
    nonnull_b = Condition(Expression.binary_op("INT_NOTEQUAL", b, Expression.constant(0, 8)), False)
    swap_taken = Condition(
        Expression.binary_op("INT_SLESS", Expression.memory(b, size=4), Expression.memory(a, size=4)),
        False,
    )
    effect_summary = EffectSummary(
        parameter_names=["a", "b"],
        effects=[
            StoreEffect(
                location=_loc("a", 0, 4),
                value=Expression.memory(b, size=4),
                conditions=[swap_taken],
                order_key=10,
            ),
            StoreEffect(
                location=_loc("b", 0, 4),
                value=Expression.memory(a, size=4),
                conditions=[swap_taken],
                order_key=11,
            ),
        ],
    )
    traced = Expression.binary_op(
        "INT_SUB",
        Expression.memory(a, size=4, read_order_key=20),
        Expression.memory(b, size=4, read_order_key=21),
    )

    class FakeTracer:
        pass

    expander = ExpressionExpander(
        FakeTracer(),
        condition_tracker=None,
        debug=False,
        effect_summary=effect_summary,
        parameters=[
            _param("a", size=8, is_signed=False),
            _param("b", size=8, is_signed=False, index=1),
        ],
    )

    canonicalized = expander._canonicalize_traced_expression(
        traced,
        [nonnull_a, nonnull_b],
    )

    assert canonicalized.to_string() == "(MEM[a] - MEM[b])"

def test_expression_expander_keeps_symbolic_post_state_identity_after_observed_load_rewrite():
    a = Expression.parameter("a", 0, size=8)
    b = Expression.parameter("b", 1, size=8)
    nonnull_a = Condition(Expression.binary_op("INT_NOTEQUAL", a, Expression.constant(0, 8)), False)
    nonnull_b = Condition(Expression.binary_op("INT_NOTEQUAL", b, Expression.constant(0, 8)), False)
    swap_taken = Condition(
        Expression.binary_op("INT_SLESS", Expression.memory(b, size=4), Expression.memory(a, size=4)),
        False,
    )
    expr = Expression.binary_op(
        "INT_SUB",
        Expression.memory(a, size=4, read_order_key=20),
        Expression.memory(b, size=4, read_order_key=21),
    )
    effect_summary = EffectSummary(
        parameter_names=["a", "b"],
        effects=[
            StoreEffect(
                location=_loc("a", 0, 4),
                value=Expression.memory(b, size=4),
                conditions=[swap_taken],
                order_key=10,
            ),
            StoreEffect(
                location=_loc("b", 0, 4),
                value=Expression.memory(a, size=4),
                conditions=[swap_taken],
                order_key=11,
            ),
        ],
    )

    class FakeTracer:
        debug = False

    expander = ExpressionExpander(
        FakeTracer(),
        condition_tracker=None,
        debug=False,
        effect_summary=effect_summary,
        parameters=[
            _param("a", size=8, is_signed=False),
            _param("b", size=8, is_signed=False, index=1),
        ],
    )

    canonicalized = expander._canonicalize_traced_expression(expr, [nonnull_a, nonnull_b])

    assert canonicalized is not None
    assert expression_contains_post_state_reads(canonicalized)
    assert _runtime_location(canonicalized.operands[0]) == _loc("a", 0, 4)
    assert _runtime_location(canonicalized.operands[1]) == _loc("b", 0, 4)
    assert _runtime_snapshot(canonicalized.operands[0]) == _runtime_snapshot(canonicalized.operands[1])

def test_promote_observed_loads_to_post_state_reads_shares_snapshot_for_swap_pair():
    a = Expression.parameter("a", 0, size=8)
    b = Expression.parameter("b", 1, size=8)
    nonnull_a = Condition(Expression.binary_op("INT_NOTEQUAL", a, Expression.constant(0, 8)), False)
    nonnull_b = Condition(Expression.binary_op("INT_NOTEQUAL", b, Expression.constant(0, 8)), False)
    swap_taken = Condition(
        Expression.binary_op("INT_SLESS", Expression.memory(b, size=4), Expression.memory(a, size=4)),
        False,
    )
    expr = Expression.binary_op(
        "INT_SUB",
        Expression.memory(
            a,
            size=4,
            read_order_key=20,
            runtime_ref=ObservedMemoryReadRef(order_key=20, location=_loc("a", 0, 4)),
        ),
        Expression.memory(
            b,
            size=4,
            read_order_key=21,
            runtime_ref=ObservedMemoryReadRef(order_key=21, location=_loc("b", 0, 4)),
        ),
    )
    effects = [
        StoreEffect(
            location=_loc("a", 0, 4),
            value=Expression.memory(b, size=4),
            conditions=[swap_taken],
            order_key=10,
        ),
        StoreEffect(
            location=_loc("b", 0, 4),
            value=Expression.memory(a, size=4),
            conditions=[swap_taken],
            order_key=11,
        ),
    ]

    promoted = promote_observed_loads_to_post_state_reads(
        expr,
        [nonnull_a, nonnull_b],
        effects,
        [_param("a", size=8, is_signed=False), _param("b", size=8, is_signed=False, index=1)],
        symbolic_post_state=True,
    )

    assert promoted is not None
    assert expression_contains_post_state_reads(promoted)
    assert isinstance(getattr(promoted.operands[0], "runtime_ref", None), PostStateReadRef)
    assert isinstance(getattr(promoted.operands[1], "runtime_ref", None), PostStateReadRef)
    assert _runtime_location(promoted.operands[0]) == _loc("a", 0, 4)
    assert _runtime_location(promoted.operands[1]) == _loc("b", 0, 4)
    assert isinstance(_runtime_snapshot(promoted.operands[0]), PostStateSnapshotRef)
    assert _runtime_snapshot(promoted.operands[0]) == _runtime_snapshot(promoted.operands[1])

    lowered = lower_post_state_expression_for_smt(
        promoted,
        [nonnull_a, nonnull_b],
        effects,
        [_param("a", size=8, is_signed=False), _param("b", size=8, is_signed=False, index=1)],
    )

    assert lowered is not None
    assert expression_contains_post_state_reads(lowered) is False

def test_expression_expander_does_not_replay_plain_memory_leaf_inside_iteration_delta_wrapper():
    trace = Expression.parameter("param_1", 0, size=8)
    start = Expression.parameter("param_2", 1, size=4)
    limit = Expression.parameter("param_3", 2, size=4)
    steps_addr = Expression.binary_op("INT_ADD", trace, Expression.constant(4, 8))

    trace_nonnull = Condition(
        Expression.binary_op("INT_NOTEQUAL", trace, Expression.constant(0, 8)),
        False,
    )
    loop_active = Condition(
        Expression.binary_op("INT_SLESS", start, limit),
        False,
    )
    even_iteration = Condition(
        Expression.binary_op(
            "INT_EQUAL",
            Expression.binary_op("INT_AND", start, Expression.constant(1, 4)),
            Expression.constant(0, 4),
        ),
        False,
    )
    final_iter = Condition(
        Expression.binary_op(
            "INT_EQUAL",
            limit,
            Expression.binary_op("INT_ADD", start, Expression.constant(1, 4)),
        ),
        False,
    )
    traced = Expression.binary_op(
        "INT_SUB",
        Expression.binary_op("INT_ADD", limit, Expression.memory(steps_addr, size=4)),
        start,
    )
    effect_summary = EffectSummary(
        parameter_names=["param_1", "param_2", "param_3"],
        effects=[
            StoreEffect(
                location=_loc("param_1", 4, 4),
                value=Expression.binary_op(
                    "INT_ADD",
                    Expression.memory(steps_addr, size=4),
                    Expression.constant(1, 4),
                ),
                conditions=[trace_nonnull, loop_active, final_iter],
                order_key=6,
            ),
        ],
    )

    class FakeTracer:
        pass

    expander = ExpressionExpander(
        FakeTracer(),
        condition_tracker=None,
        debug=False,
        effect_summary=effect_summary,
        parameters=[
            _param("param_1", size=8, is_signed=False),
            _param("param_2", size=4, index=1),
            _param("param_3", size=4, index=2),
        ],
    )

    canonicalized = expander._canonicalize_traced_expression(
        traced,
        [trace_nonnull, loop_active, even_iteration, final_iter],
    )

    assert canonicalized.to_string() == "MEM[(param_1 + 4)]"

def test_expression_expander_ignores_identity_only_observed_load_rewrite_in_iteration_delta_wrapper():
    trace = Expression.parameter("param_1", 0, size=8)
    start = Expression.parameter("param_2", 1, size=4)
    limit = Expression.parameter("param_3", 2, size=4)
    steps_addr = Expression.binary_op("INT_ADD", trace, Expression.constant(4, 8))

    trace_nonnull = Condition(
        Expression.binary_op("INT_NOTEQUAL", trace, Expression.constant(0, 8)),
        False,
    )
    loop_active = Condition(
        Expression.binary_op("INT_SLESS", start, limit),
        False,
    )
    even_iteration = Condition(
        Expression.binary_op(
            "INT_EQUAL",
            Expression.binary_op("INT_AND", start, Expression.constant(1, 4)),
            Expression.constant(0, 4),
        ),
        False,
    )
    final_iter = Condition(
        Expression.binary_op(
            "INT_EQUAL",
            limit,
            Expression.binary_op("INT_ADD", start, Expression.constant(1, 4)),
        ),
        False,
    )
    traced = Expression.binary_op(
        "INT_SUB",
        Expression.binary_op(
            "INT_ADD",
            limit,
            Expression.memory(steps_addr, size=4, read_order_key=42),
        ),
        start,
    )
    effect_summary = EffectSummary(
        parameter_names=["param_1", "param_2", "param_3"],
        effects=[
            StoreEffect(
                location=_loc("param_1", 4, 4),
                value=Expression.binary_op(
                    "INT_ADD",
                    Expression.memory(steps_addr, size=4),
                    Expression.constant(1, 4),
                ),
                conditions=[trace_nonnull, loop_active, final_iter],
                order_key=6,
            ),
        ],
    )

    class FakeTracer:
        pass

    expander = ExpressionExpander(
        FakeTracer(),
        condition_tracker=None,
        debug=False,
        effect_summary=effect_summary,
        parameters=[
            _param("param_1", size=8, is_signed=False),
            _param("param_2", size=4, index=1),
            _param("param_3", size=4, index=2),
        ],
    )

    canonicalized = expander._canonicalize_traced_expression(
        traced,
        [trace_nonnull, loop_active, even_iteration, final_iter],
    )

    assert canonicalized.to_string() == "((param_3 + MEM[(param_1 + 4)]) - param_2)"

def test_return_analyzer_collapses_even_iteration_wrapper_with_observed_step_load_to_symbolic_post_state():
    trace = Expression.parameter("param_1", 0, size=8)
    start = Expression.parameter("param_2", 1, size=4)
    limit = Expression.parameter("param_3", 2, size=4)
    steps_addr = Expression.binary_op("INT_ADD", trace, Expression.constant(4, 8))

    trace_nonnull = Condition(
        Expression.binary_op("INT_NOTEQUAL", trace, Expression.constant(0, 8)),
        False,
    )
    loop_active = Condition(
        Expression.binary_op("INT_SLESS", start, limit),
        False,
    )
    even_iteration = Condition(
        Expression.binary_op(
            "INT_EQUAL",
            Expression.binary_op("INT_AND", start, Expression.constant(1, 4)),
            Expression.constant(0, 4),
        ),
        False,
    )
    final_iter = Condition(
        Expression.binary_op(
            "INT_EQUAL",
            limit,
            Expression.binary_op("INT_ADD", start, Expression.constant(1, 4)),
        ),
        False,
    )
    expr = Expression.binary_op(
        "INT_ADD",
        Expression.binary_op("INT_ADD", Expression.memory(trace, size=4), start),
        Expression.binary_op(
            "INT_SUB",
            Expression.binary_op(
                "INT_ADD",
                limit,
                Expression.memory(steps_addr, size=4, read_order_key=42),
            ),
            start,
        ),
    )

    analyzer = ReturnAnalyzer(program=object(), debug=False)
    analyzer._current_effect_summary = EffectSummary(
        parameter_names=["param_1", "param_2", "param_3"],
        effects=[
            StoreEffect(
                location=_loc("param_1", 0, 4),
                value=Expression.binary_op(
                    "INT_ADD",
                    Expression.memory(trace, size=4),
                    start,
                ),
                conditions=[trace_nonnull, loop_active, even_iteration, final_iter],
                order_key=5,
            ),
            StoreEffect(
                location=_loc("param_1", 4, 4),
                value=Expression.binary_op(
                    "INT_ADD",
                    Expression.memory(steps_addr, size=4),
                    Expression.constant(1, 4),
                ),
                conditions=[trace_nonnull, loop_active, final_iter],
                order_key=6,
            ),
        ],
    )
    analyzer._current_parameters = [
        _param("param_1", size=8, is_signed=False),
        _param("param_2", size=4, index=1),
        _param("param_3", size=4, index=2),
    ]

    normalized = analyzer._normalize_expanded_return_value(
        expr,
        [trace_nonnull, loop_active, even_iteration, final_iter],
    )

    assert expression_contains_post_state_reads(normalized)
    assert normalized.to_string() == "(MEM[param_1] + MEM[(param_1 + 4)])"

def test_return_analyzer_normalizes_observed_load_returns_to_symbolic_post_state():
    a = Expression.parameter("param_1", 0, size=8)
    b = Expression.parameter("param_2", 1, size=8)
    nonnull_a = Condition(
        Expression.binary_op("INT_NOTEQUAL", a, Expression.constant(0, 8)),
        False,
    )
    nonnull_b = Condition(
        Expression.binary_op("INT_NOTEQUAL", b, Expression.constant(0, 8)),
        False,
    )
    swap_taken = Condition(
        Expression.binary_op("INT_SLESS", Expression.memory(b, size=4), Expression.memory(a, size=4)),
        False,
    )
    expr = Expression.binary_op(
        "INT_SUB",
        Expression.memory(a, size=4, read_order_key=20),
        Expression.memory(b, size=4, read_order_key=21),
    )

    analyzer = ReturnAnalyzer(program=object(), debug=False)
    analyzer._current_parameters = [
        _param("param_1", size=8, is_signed=False),
        _param("param_2", size=8, is_signed=False, index=1),
    ]
    effect_summary = EffectSummary(
        parameter_names=["param_1", "param_2"],
        effects=[
            StoreEffect(
                location=_loc("param_1", 0, 4),
                value=Expression.memory(b, size=4),
                conditions=[swap_taken],
                order_key=10,
            ),
            StoreEffect(
                location=_loc("param_2", 0, 4),
                value=Expression.memory(a, size=4),
                conditions=[swap_taken],
                order_key=11,
            ),
        ],
    )

    normalized = analyzer._normalize_return_value_with_effect_summary(
        expr,
        [nonnull_a, nonnull_b],
        effect_summary,
    )

    assert normalized is not None
    # Issue #282 (I3): swap の後の param_1 の読み出しは、後の param_2 への store と重ならないと示せない。正規化は
    # 読み出しを時点つきのまま残し（入口の値の読み出しにしない）、`read_validation` の検査が EQ と NOT_EQ を止める
    assert [operand.read_order_key for operand in normalized.operands] == [20, 21]

    lowered = lower_post_state_expression_for_smt(
        normalized,
        [nonnull_a, nonnull_b],
        effect_summary.effects,
        analyzer._current_parameters,
    )

    assert lowered is not None
    assert expression_contains_post_state_reads(lowered) is False
    # param_1 は簡約しない（時点つきの読み出し）。param_2 は最後の store（param_2 への store）が値を決める
    assert lowered.operands[0].read_order_key is not None
    assert lowered.operands[1].expr_type == ExpressionType.PHI

def test_return_analyzer_normalizes_single_arithmetic_update_rhs_to_post_state():
    value = Expression.parameter("value", 0, size=8)
    delta = Expression.parameter("delta", 1, size=4)
    negate = Expression.parameter("negate", 2, size=4)
    value_nonnull = Condition(
        Expression.binary_op("INT_NOTEQUAL", value, Expression.constant(0, 8)),
        False,
    )
    negate_zero = Condition(
        Expression.binary_op("INT_EQUAL", negate, Expression.constant(0, 4)),
        False,
    )
    negate_nonzero = negate_zero.negate()

    analyzer = ReturnAnalyzer(program=object(), debug=False)
    analyzer._current_parameters = [
        _param("value", size=8, is_signed=False),
        _param("delta", size=4, index=1),
        _param("negate", size=4, index=2),
    ]
    analyzer._current_effect_summary = EffectSummary(
        parameter_names=["value", "delta", "negate"],
        effects=[
            StoreEffect(
                location=_loc("value", 0, 4),
                value=Expression.binary_op("INT_ADD", Expression.memory(value, size=4), delta),
                conditions=[value_nonnull, negate_zero],
                order_key=5,
            ),
            StoreEffect(
                location=_loc("value", 0, 4),
                value=Expression.binary_op("INT_SUB", delta, Expression.memory(value, size=4)),
                conditions=[value_nonnull, negate_nonzero],
                order_key=5,
            ),
        ],
    )

    normalized_zero = analyzer._normalize_expanded_return_value(
        Expression.binary_op("INT_ADD", Expression.memory(value, size=4), delta),
        [value_nonnull, negate_zero],
    )
    normalized_nonzero = analyzer._normalize_expanded_return_value(
        Expression.binary_op("INT_SUB", delta, Expression.memory(value, size=4)),
        [value_nonnull, negate_nonzero],
    )

    assert normalized_zero.to_string() == "MEM[value]"
    assert normalized_nonzero.to_string() == "MEM[value]"
    assert _runtime_location(normalized_zero) == _loc("value", 0, 4)
    assert _runtime_location(normalized_nonzero) == _loc("value", 0, 4)

    lowered_zero = lower_post_state_expression_for_smt(
        normalized_zero,
        [value_nonnull, negate_zero],
        analyzer._current_effect_summary.effects,
        analyzer._current_parameters,
    )
    lowered_nonzero = lower_post_state_expression_for_smt(
        normalized_nonzero,
        [value_nonnull, negate_nonzero],
        analyzer._current_effect_summary.effects,
        analyzer._current_parameters,
    )

    assert lowered_zero.to_string() == "(MEM[value] + delta)"
    assert lowered_nonzero.to_string() == "(delta - MEM[value])"

def test_expression_matches_stale_post_state_replay_for_same_location_self_update():
    value = Expression.parameter("value", 0, size=8)
    delta = Expression.parameter("delta", 1, size=4)
    negate = Expression.parameter("negate", 2, size=4)
    value_nonnull = Condition(
        Expression.binary_op("INT_NOTEQUAL", value, Expression.constant(0, 8)),
        False,
    )
    negate_zero = Condition(
        Expression.binary_op("INT_EQUAL", negate, Expression.constant(0, 4)),
        False,
    )
    effects = [
        StoreEffect(
            location=_loc("value", 0, 4),
            value=Expression.binary_op("INT_ADD", Expression.memory(value, size=4), delta),
            conditions=[value_nonnull, negate_zero],
            order_key=5,
        ),
    ]
    params = [
        _param("value", size=8, is_signed=False),
        _param("delta", size=4, index=1),
        _param("negate", size=4, index=2),
    ]
    symbolic_post_state = post_state_read_expression_for_location(
        _loc("value", 0, 4),
        params,
        symbolic=True,
    )
    stale_replay = Expression.binary_op(
        "INT_ADD",
        delta,
        Expression.binary_op("INT_ADD", Expression.memory(value, size=4), delta),
    )

    assert expression_matches_stale_post_state_replay(
        stale_replay,
        symbolic_post_state,
        [value_nonnull, negate_zero],
        effects,
        params,
    )

def test_return_analyzer_accepts_symbolic_post_state_for_stale_self_update_replay():
    value = Expression.parameter("value", 0, size=8)
    delta = Expression.parameter("delta", 1, size=4)
    negate = Expression.parameter("negate", 2, size=4)
    value_nonnull = Condition(
        Expression.binary_op("INT_NOTEQUAL", value, Expression.constant(0, 8)),
        False,
    )
    negate_zero = Condition(
        Expression.binary_op("INT_EQUAL", negate, Expression.constant(0, 4)),
        False,
    )

    analyzer = ReturnAnalyzer(program=object(), debug=False)
    analyzer._current_parameters = [
        _param("value", size=8, is_signed=False),
        _param("delta", size=4, index=1),
        _param("negate", size=4, index=2),
    ]
    analyzer._current_effect_summary = EffectSummary(
        parameter_names=["value", "delta", "negate"],
        effects=[
            StoreEffect(
                location=_loc("value", 0, 4),
                value=Expression.binary_op("INT_ADD", Expression.memory(value, size=4), delta),
                conditions=[value_nonnull, negate_zero],
                order_key=5,
            ),
        ],
    )

    stale_replay = Expression.binary_op(
        "INT_ADD",
        delta,
        Expression.binary_op("INT_ADD", Expression.memory(value, size=4), delta),
    )

    normalized = analyzer._normalize_expanded_return_value(
        stale_replay,
        [value_nonnull, negate_zero],
    )

    assert normalized.to_string() == "MEM[value]"
    assert _runtime_location(normalized) == _loc("value", 0, 4)

    lowered = lower_post_state_expression_for_smt(
        normalized,
        [value_nonnull, negate_zero],
        analyzer._current_effect_summary.effects,
        analyzer._current_parameters,
    )

    assert lowered.to_string() == "(MEM[value] + delta)"

def test_return_analyzer_accepts_symbolic_post_state_for_negate_effect_value_wrapper():
    value = Expression.parameter("value", 0, size=8)
    delta = Expression.parameter("delta", 1, size=4)
    negate = Expression.parameter("negate", 2, size=4)
    value_nonnull = Condition(
        Expression.binary_op("INT_NOTEQUAL", value, Expression.constant(0, 8)),
        False,
    )
    negate_nonzero = Condition(
        Expression.binary_op("INT_NOTEQUAL", negate, Expression.constant(0, 4)),
        False,
    )

    analyzer = ReturnAnalyzer(program=object(), debug=False)
    analyzer._current_parameters = [
        _param("value", size=8, is_signed=False),
        _param("delta", size=4, index=1),
        _param("negate", size=4, index=2),
    ]
    analyzer._current_effect_summary = EffectSummary(
        parameter_names=["value", "delta", "negate"],
        effects=[
            StoreEffect(
                location=_loc("value", 0, 4),
                value=Expression.binary_op("INT_SUB", delta, Expression.memory(value, size=4)),
                conditions=[value_nonnull, negate_nonzero],
                order_key=5,
            ),
        ],
    )

    negate_effect_wrapper = Expression.binary_op(
        "INT_ADD",
        Expression.unary_op("INT_2COMP", Expression.memory(value, size=4)),
        delta,
    )

    normalized = analyzer._normalize_expanded_return_value(
        negate_effect_wrapper,
        [value_nonnull, negate_nonzero],
    )

    assert normalized.to_string() == "MEM[value]"
    assert _runtime_location(normalized) == _loc("value", 0, 4)

    lowered = lower_post_state_expression_for_smt(
        normalized,
        [value_nonnull, negate_nonzero],
        analyzer._current_effect_summary.effects,
        analyzer._current_parameters,
    )

    assert lowered.to_string() == "(delta - MEM[value])"

def test_return_analyzer_does_not_merge_complementary_symbolic_post_state_cases_when_lowerings_differ():
    value = Expression.parameter("value", 0, size=8)
    delta = Expression.parameter("delta", 1, size=4)
    negate = Expression.parameter("negate", 2, size=4)
    value_nonnull = Condition(
        Expression.binary_op("INT_NOTEQUAL", value, Expression.constant(0, 8)),
        False,
    )
    negate_zero = Condition(
        Expression.binary_op("INT_EQUAL", negate, Expression.constant(0, 4)),
        False,
    )
    negate_nonzero = Condition(
        Expression.binary_op("INT_NOTEQUAL", negate, Expression.constant(0, 4)),
        False,
    )

    analyzer = ReturnAnalyzer(program=object(), debug=False)
    analyzer._current_parameters = [
        _param("value", size=8, is_signed=False),
        _param("delta", size=4, index=1),
        _param("negate", size=4, index=2),
    ]
    analyzer._current_effect_summary = EffectSummary(
        parameter_names=["value", "delta", "negate"],
        effects=[
            StoreEffect(
                location=_loc("value", 0, 4),
                value=Expression.binary_op("INT_ADD", Expression.memory(value, size=4), delta),
                conditions=[value_nonnull, negate_zero],
                order_key=5,
            ),
            StoreEffect(
                location=_loc("value", 0, 4),
                value=Expression.binary_op("INT_SUB", delta, Expression.memory(value, size=4)),
                conditions=[value_nonnull, negate_nonzero],
                order_key=6,
            ),
        ],
    )

    symbolic_post_state = post_state_read_expression_for_location(
        _loc("value", 0, 4),
        analyzer._current_parameters,
        symbolic=True,
    )

    left = ReturnInfo(
        address="ret",
        value=symbolic_post_state,
        conditions=[value_nonnull, negate_zero],
        branch_index=1,
        pcode_identity="ret:t1",
    )
    right = ReturnInfo(
        address="ret",
        value=symbolic_post_state,
        conditions=[value_nonnull, negate_nonzero],
        branch_index=2,
        pcode_identity="ret:t1",
    )

    assert analyzer._merge_return_info_pair(left, right, [left, right], 0, 1) is None
