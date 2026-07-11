from scripts.function_tracer_pcode.tests.unit._memory_model_fixtures import *

def test_effect_summary_rewrites_stack_local_post_state_reads_in_arithmetic_expression():
    a = Expression.parameter("a", 0, size=4)
    b = Expression.parameter("b", 1, size=4)
    sum_slot = Expression.variable(
        "sum_slot",
        size=4,
        storage_info=StorageInfo(**_stack_storage(24, size_bytes=4)),
    )
    diff_slot = Expression.variable(
        "diff_slot",
        size=4,
        storage_info=StorageInfo(**_stack_storage(28, size_bytes=4)),
    )
    sum_location = canonicalize_location(sum_slot, [_param("a", size=4), _param("b", size=4, index=1)], size=4)
    diff_location = canonicalize_location(diff_slot, [_param("a", size=4), _param("b", size=4, index=1)], size=4)
    assert sum_location is not None
    assert diff_location is not None

    expr = Expression.binary_op(
        "INT_ADD",
        Expression.binary_op("INT_MULT", memory_expression_for_location(sum_location, []), Expression.constant(4, 4)),
        memory_expression_for_location(diff_location, []),
    )

    rewritten = rewrite_loads_from_effects(
        expr,
        [],
        [
            StoreEffect(
                location=sum_location,
                value=Expression.binary_op("INT_ADD", a, b),
                conditions=[],
                order_key=1,
            ),
            StoreEffect(
                location=diff_location,
                value=Expression.binary_op("INT_SUB", a, b),
                conditions=[],
                order_key=2,
            ),
        ],
        [_param("a", size=4), _param("b", size=4, index=1)],
    )

    assert rewritten.to_string() == "(((a + b) * 4) + (a - b))"

def test_return_analyzer_preserves_symbolic_post_state_reads_until_smt_lowering():
    analyzer = ReturnAnalyzer(program=object(), debug=False)
    analyzer._current_parameters = [
        _param("param_1", size=4, is_signed=False, index=0),
        _param("param_2", size=4, is_signed=False, index=1),
    ]
    analyzer._current_effect_summary = EffectSummary(
        parameter_names=["param_1", "param_2"],
        effects=[
            StoreEffect(
                location=_loc("__locbase__stackframe", -32, 4),
                value=Expression.binary_op(
                    "INT_SUB",
                    Expression.parameter("param_1", 0, size=4),
                    Expression.parameter("param_2", 1, size=4),
                ),
                conditions=[],
                order_key=1,
            ),
            StoreEffect(
                location=_loc("__locbase__stackframe", -28, 4),
                value=Expression.binary_op(
                    "INT_ADD",
                    Expression.parameter("param_1", 0, size=4),
                    Expression.parameter("param_2", 1, size=4),
                ),
                conditions=[],
                order_key=2,
            ),
        ],
    )

    expr = Expression.binary_op(
        "INT_ADD",
        memory_expression_for_location(_loc("__locbase__stackframe", -32, 4), []),
        Expression.binary_op(
            "INT_MULT",
            memory_expression_for_location(_loc("__locbase__stackframe", -28, 4), []),
            Expression.constant(4, 4),
        ),
    )

    normalized = analyzer._normalize_expanded_return_value(expr, [])

    assert expression_contains_post_state_reads(normalized)
    assert "__locread__" not in normalized.to_string()

    lowered = lower_post_state_expression_for_smt(
        normalized,
        [],
        analyzer._current_effect_summary.effects,
        analyzer._current_parameters,
    )

    assert lowered.to_string() == "((param_1 - param_2) + ((param_1 + param_2) * 4))"

def test_return_analyzer_promotes_stale_effect_value_wrapper_to_object_centric_post_state():
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

    analyzer = ReturnAnalyzer(program=object(), debug=False)
    analyzer._current_parameters = [
        _param("dst", size=8, is_signed=False),
        _param("src", size=8, is_signed=False, index=1),
        _param("delta", size=4, index=2),
    ]
    analyzer._current_effect_summary = EffectSummary(
        parameter_names=["dst", "src", "delta"],
        effects=[
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
        ],
    )

    original = Expression.binary_op(
        "INT_ADD",
        Expression.memory(dst, size=4),
        Expression.constant(0, 4),
    )
    rewritten = Expression.binary_op(
        "INT_ADD",
        Expression.binary_op("INT_ADD", Expression.memory(dst, size=4), delta),
        Expression.constant(0, 4),
    )

    collapsed = analyzer._collapse_effect_sensitive_case_wrapper(
        original,
        rewritten,
        [dst_nonnull, src_nonnull, alias_cond],
        analyzer._current_effect_summary,
    )

    assert collapsed is not None
    assert expression_contains_post_state_reads(collapsed)
    assert collapsed.to_string() == "MEM[dst]"

def test_return_analyzer_keeps_object_centric_post_state_for_observed_stale_wrapper():
    ptr = Expression.parameter("ptr", 0, size=8)
    alias = Expression.parameter("alias", 1, size=8)
    delta = Expression.parameter("delta", 2, size=4)
    ptr_nonnull = Condition(
        Expression.binary_op("INT_NOTEQUAL", ptr, Expression.constant(0, 8)),
        False,
    )
    alias_nonnull = Condition(
        Expression.binary_op("INT_NOTEQUAL", alias, Expression.constant(0, 8)),
        False,
    )
    alias_cond = Condition(
        Expression.binary_op("INT_EQUAL", ptr, alias),
        False,
    )
    observed = Expression.memory(ptr, size=4, read_order_key=42)
    wrapped = Expression.binary_op(
        "INT_ADD",
        Expression.binary_op("INT_ADD", observed, delta),
        Expression.constant(0, 4),
    )

    analyzer = ReturnAnalyzer(program=object(), debug=False)
    analyzer._current_parameters = [
        _param("ptr", size=8, is_signed=False),
        _param("alias", size=8, is_signed=False, index=1),
        _param("delta", size=4, index=2),
    ]
    analyzer._current_effect_summary = EffectSummary(
        parameter_names=["ptr", "alias", "delta"],
        effects=[
            StoreEffect(
                location=_loc("ptr", 0, 4),
                value=Expression.binary_op("INT_ADD", observed, delta),
                conditions=[ptr_nonnull, alias_nonnull, alias_cond],
                order_key=10,
            ),
        ],
    )

    normalized = analyzer._normalize_expanded_return_value(
        wrapped,
        [ptr_nonnull, alias_nonnull, alias_cond],
    )

    assert normalized is not None
    assert expression_contains_post_state_reads(normalized)
    assert normalized.to_string() == "MEM[ptr]"

def test_canonicalize_post_state_subexpressions_does_not_promote_memory_address_parameter():
    param_1 = Expression.parameter("param_1", 0, size=8)
    param_2 = Expression.parameter("param_2", 1, size=8)
    param_3 = Expression.parameter("param_3", 2, size=4)
    nonnull_1 = Condition(
        Expression.binary_op("INT_NOTEQUAL", param_1, Expression.constant(0, 8)),
        False,
    )
    nonnull_2 = Condition(
        Expression.binary_op("INT_NOTEQUAL", param_2, Expression.constant(0, 8)),
        False,
    )
    alias_cond = Condition(
        Expression.binary_op("INT_EQUAL", param_1, param_2),
        False,
    )
    observed_1 = Expression.memory(
        param_1,
        size=4,
        read_order_key=100,
        runtime_ref=ObservedMemoryReadRef(
            order_key=100,
            location=_loc("param_1", 0, 4),
            source="ghidra_load",
        ),
    )
    observed_2 = Expression.memory(
        param_2,
        size=4,
        read_order_key=101,
        runtime_ref=ObservedMemoryReadRef(
            order_key=101,
            location=_loc("param_2", 0, 4),
            source="ghidra_load",
        ),
    )

    normalized = canonicalize_post_state_subexpressions(
        observed_1,
        [nonnull_1, nonnull_2, alias_cond],
        [
            StoreEffect(
                location=_loc("param_1", 0, 4),
                value=Expression.binary_op("INT_ADD", observed_1, param_3),
                conditions=[nonnull_1, nonnull_2],
                order_key=10,
            ),
            StoreEffect(
                location=_loc("param_2", 0, 4),
                value=Expression.binary_op(
                    "INT_ADD",
                    observed_2,
                    Expression.constant(4294967295, 4),
                ),
                conditions=[nonnull_1, nonnull_2],
                order_key=20,
            ),
        ],
        [
            _param("param_1", size=8, is_signed=False),
            _param("param_2", size=8, is_signed=False, index=1),
            _param("param_3", size=4, index=2),
        ],
        symbolic_post_state=True,
        allow_memory_leaf_collapse=False,
    )

    assert normalized is not None
    assert normalized.to_string() == "MEM[param_1]"

def test_normalize_post_state_expression_promotes_observed_alias_wrapper_with_interdependent_effects():
    param_1 = Expression.parameter("param_1", 0, size=8)
    param_2 = Expression.parameter("param_2", 1, size=8)
    param_3 = Expression.parameter("param_3", 2, size=4)
    nonnull_1 = Condition(
        Expression.binary_op("INT_NOTEQUAL", param_1, Expression.constant(0, 8)),
        False,
    )
    nonnull_2 = Condition(
        Expression.binary_op("INT_NOTEQUAL", param_2, Expression.constant(0, 8)),
        False,
    )
    alias_cond = Condition(
        Expression.binary_op("INT_EQUAL", param_1, param_2),
        False,
    )
    observed_1 = Expression.memory(
        param_1,
        size=4,
        read_order_key=100,
        runtime_ref=ObservedMemoryReadRef(
            order_key=100,
            location=_loc("param_1", 0, 4),
            source="ghidra_load",
        ),
    )
    observed_2 = Expression.memory(
        param_2,
        size=4,
        read_order_key=101,
        runtime_ref=ObservedMemoryReadRef(
            order_key=101,
            location=_loc("param_2", 0, 4),
            source="ghidra_load",
        ),
    )
    wrapped = Expression.binary_op(
        "INT_ADD",
        Expression.binary_op("INT_ADD", observed_1, param_3),
        Expression.constant(0, 4),
    )

    normalized = normalize_post_state_expression(
        wrapped,
        [nonnull_1, nonnull_2, alias_cond],
        [
            StoreEffect(
                location=_loc("param_1", 0, 4),
                value=Expression.binary_op("INT_ADD", observed_1, param_3),
                conditions=[nonnull_1, nonnull_2],
                order_key=10,
            ),
            StoreEffect(
                location=_loc("param_2", 0, 4),
                value=Expression.binary_op(
                    "INT_ADD",
                    observed_2,
                    Expression.constant(4294967295, 4),
                ),
                conditions=[nonnull_1, nonnull_2],
                order_key=20,
            ),
        ],
        [
            _param("param_1", size=8, is_signed=False),
            _param("param_2", size=8, is_signed=False, index=1),
            _param("param_3", size=4, index=2),
        ],
        prefer_canonical_post_state=True,
        symbolic_post_state=True,
    )

    assert normalized is not None
    assert expression_contains_post_state_reads(normalized)
    assert normalized.to_string() == "MEM[param_1]"

def test_normalize_post_state_expression_composes_same_location_increment_effects():
    ptr = Expression.parameter("ptr", 0, size=8)
    field = Expression.binary_op(
        "INT_ADD",
        ptr,
        Expression.binary_op(
            "INT_MULT",
            Expression.constant(1, 8),
            Expression.constant(4, 8),
        ),
    )
    field_load = Expression.memory(field, size=4)
    expr = Expression.binary_op("INT_ADD", field_load, Expression.constant(7, 4))
    effects = [
        StoreEffect(
            location=_loc("ptr", 4, 4),
            value=Expression.binary_op("INT_ADD", Expression.memory(field, size=4), Expression.constant(1, 4)),
            conditions=[],
            order_key=1,
        ),
        StoreEffect(
            location=_loc("ptr", 4, 4),
            value=Expression.binary_op("INT_ADD", Expression.memory(field, size=4), Expression.constant(1, 4)),
            conditions=[],
            order_key=2,
        ),
    ]

    normalized = normalize_post_state_expression(
        expr,
        [],
        effects,
        [_param("ptr", size=8, is_signed=False)],
        prefer_canonical_post_state=False,
    )

    assert normalized is not None
    assert normalized.to_string() == "(((MEM[(ptr + 4)] + 1) + 1) + 7)"

def test_normalize_post_state_expression_does_not_replay_existing_effect_value_twice():
    trace = Expression.parameter("trace", 0, size=8)
    trace_nonnull = Condition(
        Expression.binary_op("INT_NOTEQUAL", trace, Expression.constant(0, 8)),
        False,
    )
    steps_addr = Expression.binary_op("INT_ADD", trace, Expression.constant(4, 8))
    already_replayed = Expression.binary_op(
        "INT_ADD",
        Expression.memory(steps_addr, size=4),
        Expression.constant(1, 4),
    )

    normalized = normalize_post_state_expression(
        already_replayed,
        [trace_nonnull],
        [
            StoreEffect(
                location=_loc("trace", 4, 4),
                value=already_replayed,
                conditions=[trace_nonnull],
                order_key=1,
            ),
            StoreEffect(
                location=_loc("trace", 4, 4),
                value=already_replayed,
                conditions=[trace_nonnull],
                order_key=2,
            ),
        ],
        [_param("trace", size=8, is_signed=False)],
        prefer_canonical_post_state=False,
    )

    assert normalized is not None
    assert normalized.to_string() == "(MEM[(trace + 4)] + 1)"

def test_lower_post_state_expression_for_smt_keeps_materialized_object_state_value_atomic():
    dst = Expression.parameter("dst", 0, size=8)
    src = Expression.parameter("src", 1, size=8)
    copy_flag = Expression.parameter("copy_flag", 2, size=4)
    dst_nonnull = Condition(
        Expression.binary_op("INT_NOTEQUAL", dst, Expression.constant(0, 8)),
        False,
    )
    src_nonnull = Condition(
        Expression.binary_op("INT_NOTEQUAL", src, Expression.constant(0, 8)),
        False,
    )
    accumulate_taken = Condition(
        Expression.binary_op("INT_EQUAL", copy_flag, Expression.constant(0, 4)),
        False,
    )
    accumulated = Expression.binary_op(
        "INT_ADD",
        Expression.memory(dst, size=4),
        Expression.memory(src, size=4),
    )
    effects = [
        StoreEffect(
            location=_loc("dst", 0, 4),
            value=accumulated,
            conditions=[dst_nonnull, src_nonnull, accumulate_taken],
            order_key=7,
        ),
    ]
    params = [
        _param("dst", size=8, is_signed=False),
        _param("src", size=8, is_signed=False, index=1),
        _param("copy_flag", size=4, is_signed=False, index=2),
    ]

    symbolic_value = post_state_read_expression_for_location(
        _loc("dst", 0, 4),
        params,
        symbolic=True,
    )

    normalized = lower_post_state_expression_for_smt(
        symbolic_value,
        [dst_nonnull, src_nonnull, accumulate_taken],
        effects,
        params,
    )

    assert normalized is not None
    assert normalized.to_string() == "(MEM[dst] + MEM[src])"
    assert isinstance(getattr(normalized, "runtime_ref", None), PostStateValueRef)
    assert normalized.runtime_ref.location == _loc("dst", 0, 4)

    lowered = lower_post_state_expression_for_smt(
        normalized,
        [dst_nonnull, src_nonnull, accumulate_taken],
        effects,
        params,
    )

    assert lowered is not None
    assert lowered.to_string() == "(MEM[dst] + MEM[src])"

def test_lower_post_state_expression_for_smt_materializes_matching_composite_effect_value_before_replay():
    dst = Expression.parameter("dst", 0, size=8)
    src = Expression.parameter("src", 1, size=8)
    copy_flag = Expression.parameter("copy_flag", 2, size=4)
    dst_nonnull = Condition(
        Expression.binary_op("INT_NOTEQUAL", dst, Expression.constant(0, 8)),
        False,
    )
    src_nonnull = Condition(
        Expression.binary_op("INT_NOTEQUAL", src, Expression.constant(0, 8)),
        False,
    )
    accumulate_taken = Condition(
        Expression.binary_op("INT_EQUAL", copy_flag, Expression.constant(0, 4)),
        False,
    )
    expr = Expression.binary_op(
        "INT_ADD",
        Expression.memory(dst, size=4, runtime_ref=_loc("dst", 0, 4)),
        Expression.memory(src, size=4, runtime_ref=_loc("src", 0, 4)),
    )
    effects = [
        StoreEffect(
            location=_loc("dst", 0, 4),
            value=Expression.binary_op(
                "INT_ADD",
                Expression.memory(dst, size=4, read_order_key=10),
                Expression.memory(src, size=4, read_order_key=11),
            ),
            conditions=[dst_nonnull, src_nonnull, accumulate_taken],
            order_key=7,
        ),
    ]
    params = [
        _param("dst", size=8, is_signed=False),
        _param("src", size=8, is_signed=False, index=1),
        _param("copy_flag", size=4, is_signed=False, index=2),
    ]

    lowered = lower_post_state_expression_for_smt(
        expr,
        [dst_nonnull, src_nonnull, accumulate_taken],
        effects,
        params,
    )

    assert lowered is not None
    assert lowered.to_string() == "(MEM[dst] + MEM[src])"
    assert isinstance(getattr(lowered, "runtime_ref", None), PostStateValueRef)
    assert lowered.runtime_ref.location == _loc("dst", 0, 4)

def test_effect_summary_collapses_post_state_phi_to_canonical_memory_location():
    a = Expression.parameter("a", 0, size=8)
    b = Expression.parameter("b", 1, size=8)
    swap_taken = Condition(
        Expression.binary_op("INT_SLESS", Expression.memory(b, size=4), Expression.memory(a, size=4)),
        False,
    )
    post_swap_b = Expression.phi(
        [
            (swap_taken, Expression.memory(a, size=4)),
            (None, Expression.memory(b, size=4)),
        ]
    )
    post_swap_b.size = 4
    effects = [
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
    ]

    collapsed = collapse_post_state_expr_to_canonical_memory(
        post_swap_b,
        effects,
        [
            _param("a", size=8, is_signed=False),
            _param("b", size=8, is_signed=False, index=1),
        ],
    )

    assert collapsed is not None
    assert collapsed.to_string() == "MEM[b]"

def test_expression_expander_collapses_nested_multiequal_matching_effect_post_state():
    a = Expression.parameter("a", 0, size=8)
    b = Expression.parameter("b", 1, size=8)
    swap_taken = Condition(
        Expression.binary_op("INT_SLESS", Expression.memory(b, size=4), Expression.memory(a, size=4)),
        False,
    )
    post_swap_b = Expression.phi(
        [
            (swap_taken, Expression.memory(a, size=4)),
            (None, Expression.memory(b, size=4)),
        ]
    )
    post_swap_b.size = 4
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

    class FakeMultiequalOp:
        def getMnemonic(self):
            return "MULTIEQUAL"

    class FakeVarnode:
        def __init__(self, def_op):
            self._def_op = def_op

        def getSize(self):
            return 4

        def getDef(self):
            return self._def_op

    class FakeTracer:
        def _trace_pcode_op(self, _op, depth=0, use_cache=False):
            return post_swap_b

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

    expanded = expander._expand_input_varnode(
        FakeVarnode(FakeMultiequalOp()),
        [],
        depth=0,
    )

    assert len(expanded) == 1
    assert expanded[0].value.to_string() == "MEM[b]"

def test_effect_summary_collapses_post_state_phi_with_explicit_complementary_guards():
    a = Expression.parameter("a", 0, size=8)
    b = Expression.parameter("b", 1, size=8)
    swap_taken = Condition(
        Expression.binary_op("INT_SLESS", Expression.memory(b, size=4), Expression.memory(a, size=4)),
        False,
    )
    no_swap = Condition(swap_taken.expression, True)
    post_swap_b = Expression.phi(
        [
            (swap_taken, Expression.memory(a, size=4)),
            (no_swap, Expression.memory(b, size=4)),
        ]
    )
    post_swap_b.size = 4
    effects = [
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
    ]

    collapsed = collapse_post_state_expr_to_canonical_memory(
        post_swap_b,
        effects,
        [
            _param("a", size=8, is_signed=False),
            _param("b", size=8, is_signed=False, index=1),
        ],
        return_conditions=[swap_taken],
    )

    assert collapsed is not None
    assert collapsed.to_string() == "MEM[b]"

def test_effect_summary_collapses_pruned_post_state_memory_leaf_to_canonical_location():
    a = Expression.parameter("a", 0, size=8)
    b = Expression.parameter("b", 1, size=8)
    swap_taken = Condition(
        Expression.binary_op("INT_SLESS", Expression.memory(b, size=4), Expression.memory(a, size=4)),
        False,
    )
    effects = [
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
    ]

    collapsed = collapse_pruned_post_state_memory_leaf_to_canonical_memory(
        Expression.memory(a, size=4),
        effects,
        [
            _param("a", size=8, is_signed=False),
            _param("b", size=8, is_signed=False, index=1),
        ],
        return_conditions=[swap_taken],
    )

    assert collapsed is not None
    assert collapsed.to_string() == "MEM[b]"

def test_effect_summary_generalized_collapse_resolves_raw_post_state_memory_leaf():
    a = Expression.parameter("a", 0, size=8)
    b = Expression.parameter("b", 1, size=8)
    swap_taken = Condition(
        Expression.binary_op("INT_SLESS", Expression.memory(b, size=4), Expression.memory(a, size=4)),
        False,
    )
    effects = [
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
    ]

    collapsed = collapse_post_state_expr_to_canonical_memory(
        Expression.memory(a, size=4),
        effects,
        [
            _param("a", size=8, is_signed=False),
            _param("b", size=8, is_signed=False, index=1),
        ],
        return_conditions=[swap_taken],
    )

    assert collapsed is not None
    assert collapsed.to_string() == "MEM[b]"

def test_collapse_post_state_read_preserves_root_object_identity():
    a = Expression.parameter("a", 0, size=8)
    b = Expression.parameter("b", 1, size=8)
    swap_taken = Condition(
        Expression.binary_op("INT_SLESS", Expression.memory(b, size=4), Expression.memory(a, size=4)),
        False,
    )
    effects = [
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
    ]
    params = [
        _param("a", size=8, is_signed=False),
        _param("b", size=8, is_signed=False, index=1),
    ]
    post_state_b = post_state_read_expression_for_location(
        _loc("b", 0, 4),
        params,
        symbolic=True,
    )

    collapsed = collapse_post_state_expr_to_canonical_memory(
        post_state_b,
        effects,
        params,
        return_conditions=[swap_taken],
    )

    assert collapsed is not None
    assert collapsed.to_string() == "MEM[b]"

def test_canonicalize_post_state_subexpressions_handles_composite_guard_without_self_subtraction():
    a = Expression.parameter("a", 0, size=8)
    b = Expression.parameter("b", 1, size=8)
    nonnull_a = Condition(Expression.binary_op("INT_NOTEQUAL", a, Expression.constant(0, 8)), False)
    nonnull_b = Condition(Expression.binary_op("INT_NOTEQUAL", b, Expression.constant(0, 8)), False)
    swap_taken = Condition(
        Expression.binary_op("INT_SLESS", Expression.memory(b, size=4), Expression.memory(a, size=4)),
        False,
    )
    no_swap = Condition(swap_taken.expression, True)
    expr = Expression.binary_op(
        "INT_SUB",
        Expression.memory(a, size=4),
        Expression.phi(
            [
                (Condition.combine_and([nonnull_a, nonnull_b, swap_taken]), Expression.memory(a, size=4)),
                (Condition.combine_and([nonnull_a, nonnull_b, no_swap]), Expression.memory(b, size=4)),
            ]
        ),
    )
    expr.operands[1].size = 4
    effects = [
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
    ]

    normalized = canonicalize_post_state_subexpressions(
        expr,
        [nonnull_a, nonnull_b, swap_taken],
        effects,
        [
            _param("a", size=8, is_signed=False),
            _param("b", size=8, is_signed=False, index=1),
        ],
    )

    assert normalized.to_string() == "(MEM[a] - MEM[b])"

def test_normalize_post_state_expression_collapses_effect_rewritten_branch_value():
    value = Expression.parameter("value", 0, size=8)
    delta = Expression.parameter("delta", 1, size=4)
    negate = Expression.parameter("negate", 2, size=8)
    negate_zero = Condition(
        Expression.binary_op("INT_EQUAL", negate, Expression.constant(0, 8)),
        False,
    )
    negate_nonzero = negate_zero.negate()
    effects = [
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
    ]

    rewritten = rewrite_observed_loads_from_effects(
        Expression.memory(value, size=4, read_order_key=9),
        [negate_zero],
        effects,
        [
            _param("value", size=8, is_signed=False),
            _param("delta", size=4, index=1),
            _param("negate", size=8, index=2),
        ],
    )
    normalized = normalize_post_state_expression(
        rewritten,
        [negate_zero],
        effects,
        [
            _param("value", size=8, is_signed=False),
            _param("delta", size=4, index=1),
            _param("negate", size=8, index=2),
        ],
    )

    assert rewritten.to_string() == "(MEM[value] + delta)"
    assert normalized.to_string() == "MEM[value]"

def test_normalize_post_state_expression_rewrites_double_indirect_post_state_load():
    slot = Expression.parameter("slot", 0, size=8)
    value = Expression.parameter("value", 1, size=4)
    slot_nonnull = Condition(
        Expression.binary_op("INT_NOTEQUAL", slot, Expression.constant(0, 8)),
        False,
    )
    inner_nonnull = Condition(
        Expression.binary_op(
            "INT_NOTEQUAL",
            Expression.memory(slot, size=8),
            Expression.constant(0, 8),
        ),
        False,
    )
    expr = Expression.binary_op(
        "INT_ADD",
        Expression.memory(Expression.memory(slot, size=8), size=4),
        Expression.constant(1, 4),
    )

    normalized = normalize_post_state_expression(
        expr,
        [slot_nonnull, inner_nonnull],
        [
            StoreEffect(
                location=_loc(
                    "slot",
                    offset=0,
                    size=4,
                    steps=(LocationStep("deref", 8),),
                ),
                value=value,
                conditions=[slot_nonnull, inner_nonnull],
                order_key=5,
            ),
        ],
        [
            _param("slot", size=8, is_signed=False),
            _param("value", size=4, index=1),
        ],
    )

    assert normalized.to_string() == "(value + 1)"

def test_post_state_read_expression_for_location_can_build_symbolic_reads():
    expr = post_state_read_expression_for_location(
        _loc("trace", 4, 4),
        [_param("trace", size=8, is_signed=False)],
        symbolic=True,
    )

    assert expr is not None
    assert expr.expr_type == ExpressionType.MEMORY
    assert _runtime_location(expr) == _loc("trace", 4, 4)
    assert isinstance(getattr(expr, "runtime_ref", None), PostStateReadRef)

def test_post_state_read_expression_for_location_respects_nonsymbolic_mode():
    expr = post_state_read_expression_for_location(
        _loc("trace", 4, 4),
        [_param("trace", size=8, is_signed=False)],
        symbolic=False,
    )

    assert expr is not None
    assert expr.expr_type == ExpressionType.MEMORY
    assert getattr(expr, "runtime_ref", None) is None

def test_normalize_post_state_expression_preserves_symbolic_post_state_reads_until_smt_lowering():
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

    explicit_expr = Expression.binary_op(
        "INT_ADD",
        Expression.binary_op("INT_ADD", Expression.memory(steps_addr, size=4), Expression.constant(1, 4)),
        Expression.binary_op("INT_ADD", Expression.memory(trace, size=4), odd_delta),
    )
    effects = [
        StoreEffect(
            location=_loc("trace", 0, 4),
            value=Expression.binary_op("INT_ADD", Expression.memory(trace, size=4), odd_delta),
            conditions=[trace_nonnull, loop_active, odd_iteration, final_iter],
            order_key=5,
        ),
        StoreEffect(
            location=_loc("trace", 4, 4),
            value=Expression.binary_op("INT_ADD", Expression.memory(steps_addr, size=4), Expression.constant(1, 4)),
            conditions=[trace_nonnull, loop_active, final_iter],
            order_key=6,
        ),
    ]

    normalized = normalize_post_state_expression(
        explicit_expr,
        [trace_nonnull, loop_active, odd_iteration, final_iter],
        effects,
        [
            _param("trace", size=8, is_signed=False),
            _param("start", size=4, index=1),
            _param("limit", size=4, index=2),
        ],
        symbolic_post_state=True,
    )

    assert normalized is not None
    assert expression_contains_post_state_reads(normalized)

def test_normalize_post_state_expression_promotes_observed_loads_to_symbolic_post_state():
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
    params = [
        _param("param_1", size=8, is_signed=False),
        _param("param_2", size=8, is_signed=False, index=1),
    ]
    effects = [
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
    ]
    expr = Expression.binary_op(
        "INT_SUB",
        Expression.memory(a, size=4, read_order_key=20),
        Expression.memory(b, size=4, read_order_key=21),
    )

    normalized = normalize_post_state_expression(
        expr,
        [nonnull_a, nonnull_b],
        effects,
        params,
        symbolic_post_state=True,
    )

    assert normalized is not None
    assert expression_contains_post_state_reads(normalized)
    assert expression_contains_post_state_reads(normalized.operands[0])
    assert expression_contains_post_state_reads(normalized.operands[1])

    lowered = lower_post_state_expression_for_smt(
        normalized,
        [nonnull_a, nonnull_b],
        effects,
        params,
    )

    assert lowered is not None
    assert lowered.to_string() != expr.to_string()
    assert expression_contains_post_state_reads(lowered) is False
    assert lowered.operands[0].expr_type == ExpressionType.PHI
    assert lowered.operands[1].expr_type == ExpressionType.PHI

def test_lower_post_state_expression_for_smt_replays_symbolic_reads_under_merged_guards():
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
            _loc("trace", 4, 4),
            params,
            symbolic=True,
        ),
        post_state_read_expression_for_location(
            _loc("trace", 0, 4),
            params,
            symbolic=True,
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
            value=Expression.binary_op("INT_ADD", Expression.memory(steps_addr, size=4), Expression.constant(1, 4)),
            conditions=[trace_nonnull, loop_active, final_iter],
            order_key=6,
        ),
    ]

    lowered = lower_post_state_expression_for_smt(
        symbolic_expr,
        [trace_nonnull, loop_active, final_iter],
        effects,
        params,
    )

    assert lowered is not None
    lowered_smt = lowered.to_smt()
    assert "__locread__" not in lowered_smt
    assert "ite" in lowered_smt
    assert "bvneg start" in lowered_smt
    assert "select mem32 trace" in lowered_smt

def test_lower_post_state_expression_for_smt_rewrites_nested_symbolic_effect_values():
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

    lowered = lower_post_state_expression_for_smt(
        symbolic_expr,
        [trace_nonnull, loop_active, odd_iteration, final_iter],
        effects,
        params,
    )

    assert lowered is not None
    lowered_smt = lowered.to_smt()
    assert "__locread__" not in lowered_smt
    assert "select mem32 trace" in lowered_smt
    assert "select mem32 (bvadd trace (_ bv4 64))" in lowered_smt

def test_lower_post_state_expression_for_smt_materializes_iteration_delta_wrapped_symbolic_value():
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
    normalized = normalize_post_state_expression(
        symbolic_expr,
        [trace_nonnull, loop_active, odd_iteration, final_iter],
        [
            StoreEffect(
                location=_loc("trace", 0, 4),
                value=Expression.binary_op("INT_ADD", Expression.memory(trace, size=4), odd_delta),
                conditions=[trace_nonnull, loop_active, odd_iteration, final_iter],
                order_key=5,
            ),
            StoreEffect(
                location=_loc("trace", 4, 4),
                value=Expression.binary_op(
                    "INT_ADD",
                    Expression.memory(steps_addr, size=4),
                    Expression.constant(1, 4),
                ),
                conditions=[trace_nonnull, loop_active, final_iter],
                order_key=6,
            ),
        ],
        params,
        symbolic_post_state=True,
    )

    lowered = lower_post_state_expression_for_smt(
        normalized,
        [trace_nonnull, loop_active, odd_iteration, final_iter],
        [
            StoreEffect(
                location=_loc("trace", 0, 4),
                value=Expression.binary_op("INT_ADD", Expression.memory(trace, size=4), odd_delta),
                conditions=[trace_nonnull, loop_active, odd_iteration, final_iter],
                order_key=5,
            ),
            StoreEffect(
                location=_loc("trace", 4, 4),
                value=Expression.binary_op(
                    "INT_ADD",
                    Expression.memory(steps_addr, size=4),
                    Expression.constant(1, 4),
                ),
                conditions=[trace_nonnull, loop_active, final_iter],
                order_key=6,
            ),
        ],
        params,
    )

    assert lowered is not None
    lowered_smt = lowered.to_smt()
    assert "__locread__" not in lowered_smt
    assert "select mem32 trace" in lowered_smt
    assert "select mem32 (bvadd trace (_ bv4 64))" in lowered_smt

def test_normalize_and_lower_post_state_expression_avoids_extra_increment_for_wrapped_even_iteration_step():
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

    params = [
        _param("param_1", size=8, is_signed=False),
        _param("param_2", size=4, index=1),
        _param("param_3", size=4, index=2),
    ]
    expr = Expression.binary_op(
        "INT_ADD",
        Expression.binary_op(
            "INT_ADD",
            Expression.memory(trace, size=4),
            start,
        ),
        Expression.binary_op(
            "INT_SUB",
            Expression.binary_op(
                "INT_ADD",
                limit,
                Expression.memory(
                    steps_addr,
                    size=4,
                ),
            ),
            start,
        ),
    )
    effects = [
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
    ]

    normalized = normalize_post_state_expression(
        expr,
        [trace_nonnull, loop_active, even_iteration, final_iter],
        effects,
        params,
        symbolic_post_state=True,
    )

    lowered = lower_post_state_expression_for_smt(
        normalized,
        [trace_nonnull, loop_active, even_iteration, final_iter],
        effects,
        params,
    )

    assert lowered is not None
    assert lowered.to_string() == "((MEM[param_1] + param_2) + (MEM[(param_1 + 4)] + 1))"

def test_lower_post_state_expression_for_smt_does_not_double_replay_add_neg_form():
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
    effects = [
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
    ]
    params = [
        _param("param_1", size=8, is_signed=False),
        _param("param_2", size=4, index=1),
        _param("param_3", size=4, index=2),
    ]

    lowered = lower_post_state_expression_for_smt(
        expr,
        [trace_nonnull, loop_active, odd_iteration, final_iter],
        effects,
        params,
    )

    assert lowered is not None
    assert lowered.to_string() == "((MEM[param_1] - param_2) + (MEM[(param_1 + 4)] + 1))"

def test_formula_builder_lowers_symbolic_post_state_reads_before_smt_emission():
    trace = Expression.parameter("trace", 0, size=8)
    start = Expression.parameter("start", 1, size=4)
    limit = Expression.parameter("limit", 2, size=4)

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
    steps_addr = Expression.binary_op("INT_ADD", trace, Expression.constant(4, 8))
    value_expr = Expression.binary_op(
        "INT_ADD",
        post_state_read_expression_for_location(
            _loc("trace", 4, 4),
            params,
            symbolic=True,
        ),
        post_state_read_expression_for_location(
            _loc("trace", 0, 4),
            params,
            symbolic=True,
        ),
    )
    effects = [
        StoreEffect(
            location=_loc("trace", 0, 4),
            value=Expression.binary_op("INT_ADD", Expression.memory(trace, size=4), Expression.unary_op("INT_2COMP", start)),
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
            value=Expression.binary_op("INT_ADD", Expression.memory(steps_addr, size=4), Expression.constant(1, 4)),
            conditions=[trace_nonnull, loop_active, final_iter],
            order_key=6,
        ),
    ]
    analysis = FunctionReturnAnalysis(
        function_name="f",
        entry_point="0x1000",
        parameters=params,
        returns=[
            ReturnInfo(
                address="0x1004",
                value=value_expr,
                conditions=[trace_nonnull, loop_active, final_iter],
            )
        ],
        return_type="int",
        effect_summary=EffectSummary(
            parameter_names=["trace", "start", "limit"],
            effects=effects,
        ),
    )

    formula = FormulaBuilder(debug=False, exclude_ub=False).build_equivalence_formula_extended(
        analysis,
        analysis,
    ).formula

    assert "__locread__" not in formula
    assert "ite" in formula
