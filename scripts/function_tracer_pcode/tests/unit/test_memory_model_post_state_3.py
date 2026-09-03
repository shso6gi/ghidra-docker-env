from scripts.function_tracer_pcode.tests.unit._memory_model_fixtures import *
import scripts.function_tracer_pcode.semantics.transform.expander_canonical as _mx_expander_canonical

def test_return_analyzer_rewrite_prefers_precise_object_state_carrier_for_observed_effect_value():
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

    analyzer = ReturnAnalyzer(program=object(), debug=False)
    analyzer._current_parameters = [
        _param("dst", size=8, is_signed=False),
        _param("src", size=8, is_signed=False, index=1),
        _param("copy_flag", size=4, is_signed=False, index=2),
    ]
    effect_summary = EffectSummary(
        parameter_names=["dst", "src", "copy_flag"],
        effects=[
            StoreEffect(
                location=_loc("dst", 0, 4),
                value=Expression.binary_op(
                    "INT_ADD",
                    Expression.memory(
                        dst,
                        size=4,
                        read_order_key=10,
                        runtime_ref=_observed_read("dst", index=0, size=4, order_key=10),
                    ),
                    Expression.memory(
                        src,
                        size=4,
                        read_order_key=11,
                        runtime_ref=_observed_read("src", index=0, size=4, order_key=11),
                    ),
                ),
                conditions=[dst_nonnull, src_nonnull, accumulate_taken],
                order_key=7,
            ),
        ],
    )
    original = Expression.binary_op(
        "INT_ADD",
        Expression.memory(
            dst,
            size=4,
            read_order_key=10,
            runtime_ref=_observed_read("dst", index=0, size=4, order_key=10),
        ),
        Expression.memory(
            src,
            size=4,
            read_order_key=11,
            runtime_ref=_observed_read("src", index=0, size=4, order_key=11),
        ),
    )

    rewritten = analyzer._rewrite_effect_sensitive_return_value(
        original,
        [dst_nonnull, src_nonnull, accumulate_taken],
        effect_summary,
    )

    assert rewritten is not None
    assert rewritten.to_string() == "(MEM[dst] + MEM[src])"
    assert isinstance(getattr(rewritten, "runtime_ref", None), PostStateValueRef)
    assert rewritten.runtime_ref.location == _loc("dst", 0, 4)

def test_build_return_infos_materializes_observed_effect_value_before_generic_rewrite():
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

    analyzer = ReturnAnalyzer(program=object(), debug=False)
    analyzer._current_parameters = [
        _param("dst", size=8, is_signed=False),
        _param("src", size=8, is_signed=False, index=1),
        _param("copy_flag", size=4, is_signed=False, index=2),
    ]
    analyzer._current_effect_summary = EffectSummary(
        parameter_names=["dst", "src", "copy_flag"],
        effects=[
            StoreEffect(
                location=_loc("dst", 0, 4),
                value=Expression.binary_op(
                    "INT_ADD",
                    Expression.memory(
                        dst,
                        size=4,
                        read_order_key=10,
                        runtime_ref=_observed_read("dst", index=0, size=4, order_key=10),
                    ),
                    Expression.memory(
                        src,
                        size=4,
                        read_order_key=11,
                        runtime_ref=_observed_read("src", index=0, size=4, order_key=11),
                    ),
                ),
                conditions=[dst_nonnull, src_nonnull, accumulate_taken],
                order_key=7,
            ),
        ],
    )

    results = analyzer._build_return_infos_from_expansions(
        "00100000",
        [
            ExpandedValue(
                Expression.binary_op(
                    "INT_ADD",
                    Expression.memory(
                        dst,
                        size=4,
                        read_order_key=10,
                        runtime_ref=_observed_read("dst", index=0, size=4, order_key=10),
                    ),
                    Expression.memory(
                        src,
                        size=4,
                        read_order_key=11,
                        runtime_ref=_observed_read("src", index=0, size=4, order_key=11),
                    ),
                ),
                [dst_nonnull, src_nonnull, accumulate_taken],
            )
        ],
        return_index=0,
    )

    assert len(results) == 1
    assert results[0].value.to_string() == "(MEM[dst] + MEM[src])"
    assert isinstance(getattr(results[0].value, "runtime_ref", None), PostStateValueRef)
    assert results[0].value.runtime_ref.location == _loc("dst", 0, 4)

def test_return_analyzer_splits_effect_sensitive_observed_load_returns_into_cases():
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
    analyzer._current_effect_summary = EffectSummary(
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

    results = analyzer._build_return_infos_from_expansions(
        "00100000",
        [ExpandedValue(expr, [nonnull_a, nonnull_b])],
        return_index=0,
    )

    assert len(results) == 2
    rendered = {
        info.value.to_string(): " ".join(cond.to_string() for cond in info.conditions)
        for info in results
    }
    assert rendered.keys() == {"(MEM[param_1] - MEM[param_2])", "(MEM[param_2] - MEM[param_1])"}
    assert "(param_1 != 0)" in rendered["(MEM[param_1] - MEM[param_2])"]
    assert "(param_2 != 0)" in rendered["(MEM[param_1] - MEM[param_2])"]
    assert "(not (MEM[param_2] < MEM[param_1]))" in rendered["(MEM[param_1] - MEM[param_2])"]
    assert "(param_1 != 0)" in rendered["(MEM[param_2] - MEM[param_1])"]
    assert "(param_2 != 0)" in rendered["(MEM[param_2] - MEM[param_1])"]
    assert "(MEM[param_2] < MEM[param_1])" in rendered["(MEM[param_2] - MEM[param_1])"]

def test_return_analyzer_keeps_already_split_observed_swap_case():
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
        Expression.memory(
            b,
            size=4,
            runtime_ref=_observed_read("param_2", index=1, size=4, order_key=20),
        ),
        Expression.memory(
            a,
            size=4,
            runtime_ref=_observed_read("param_1", index=0, size=4, order_key=21),
        ),
    )

    analyzer = ReturnAnalyzer(program=object(), debug=False)
    analyzer._current_parameters = [
        _param("param_1", size=8, is_signed=False),
        _param("param_2", size=8, is_signed=False, index=1),
    ]
    analyzer._current_effect_summary = EffectSummary(
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

    results = analyzer._build_return_infos_from_expansions(
        "00100000",
        [ExpandedValue(expr, [nonnull_a, nonnull_b, swap_taken])],
        return_index=0,
    )

    assert len(results) == 1
    assert results[0].value.to_string() == "(MEM[param_2] - MEM[param_1])"
    assert {cond.to_string() for cond in results[0].conditions} == {
        "(param_1 != 0)",
        "(param_2 != 0)",
        "(MEM[param_2] < MEM[param_1])",
    }

def test_rewrite_observed_loads_uses_runtime_ref_provenance_when_read_order_key_is_missing():
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
        Expression.memory(
            a,
            size=4,
            runtime_ref=_observed_read("param_1", index=0, size=4, order_key=20),
        ),
        Expression.memory(
            b,
            size=4,
            runtime_ref=_observed_read("param_2", index=1, size=4, order_key=21),
        ),
    )
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

    rewritten = rewrite_observed_loads_from_effects(
        expr,
        [nonnull_a, nonnull_b, swap_taken],
        effects,
        [_param("param_1", size=8, is_signed=False), _param("param_2", size=8, is_signed=False, index=1)],
    )

    assert rewritten is not None
    assert rewritten.to_string() == "(MEM[param_2] - MEM[param_1])"

def test_expression_expander_prefers_observed_rewrite_over_flat_raw_normalization(monkeypatch):
    import scripts.function_tracer_pcode.semantics.transform.expander as expander_module

    a = Expression.parameter("a", 0, size=8)
    b = Expression.parameter("b", 1, size=8)
    nonnull_a = Condition(Expression.binary_op("INT_NOTEQUAL", a, Expression.constant(0, 8)), False)
    nonnull_b = Condition(Expression.binary_op("INT_NOTEQUAL", b, Expression.constant(0, 8)), False)
    swap_taken = Condition(
        Expression.binary_op("INT_SLESS", Expression.memory(b, size=4), Expression.memory(a, size=4)),
        False,
    )
    traced = Expression.binary_op(
        "INT_SUB",
        Expression.memory(
            a,
            size=4,
            runtime_ref=_observed_read("a", index=0, size=4, order_key=20),
        ),
        Expression.memory(
            b,
            size=4,
            runtime_ref=_observed_read("b", index=1, size=4, order_key=21),
        ),
    )
    swapped = Expression.binary_op(
        "INT_SUB",
        Expression.memory(b, size=4),
        Expression.memory(a, size=4),
    )
    flattened = Expression.binary_op(
        "INT_SUB",
        Expression.memory(a, size=4),
        Expression.memory(b, size=4),
    )

    class FakeTracer:
        pass

    expander = ExpressionExpander(
        FakeTracer(),
        condition_tracker=None,
        debug=False,
        effect_summary=EffectSummary(
            parameter_names=["a", "b"],
            effects=[
                StoreEffect(
                    location=_loc("a", 0, 4),
                    value=Expression.memory(b, size=4),
                    conditions=[swap_taken],
                    order_key=10,
                )
            ],
        ),
        parameters=[
            _param("a", size=8, is_signed=False),
            _param("b", size=8, is_signed=False, index=1),
        ],
    )

    monkeypatch.setattr(
        expander_module,
        "rewrite_observed_loads_from_effects",
        lambda expr, *_args, **_kwargs: swapped if expr is traced else expr,
    )
    monkeypatch.setattr(
        _mx_expander_canonical,
        "rewrite_observed_loads_from_effects",
        lambda expr, *_args, **_kwargs: swapped if expr is traced else expr,
    )
    monkeypatch.setattr(
        expander_module,
        "normalize_post_state_expression",
        lambda expr, *_args, **_kwargs: flattened if expr is traced else expr,
    )
    monkeypatch.setattr(
        _mx_expander_canonical,
        "normalize_post_state_expression",
        lambda expr, *_args, **_kwargs: flattened if expr is traced else expr,
    )

    canonicalized = expander._canonicalize_traced_expression(
        traced,
        [nonnull_a, nonnull_b],
    )

    assert canonicalized.to_string() == "(MEM[b] - MEM[a])"

def test_return_analyzer_splits_effect_sensitive_canonical_memory_returns_without_observed_metadata():
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
        Expression.memory(a, size=4),
        Expression.memory(b, size=4),
    )

    analyzer = ReturnAnalyzer(program=object(), debug=False)
    analyzer._current_parameters = [
        _param("param_1", size=8, is_signed=False),
        _param("param_2", size=8, is_signed=False, index=1),
    ]
    analyzer._current_effect_summary = EffectSummary(
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

    results = analyzer._build_return_infos_from_expansions(
        "00100004",
        [ExpandedValue(expr, [nonnull_a, nonnull_b])],
        return_index=0,
    )

    assert len(results) == 2
    rendered = {
        info.value.to_string(): " ".join(cond.to_string() for cond in info.conditions)
        for info in results
    }
    assert rendered.keys() == {"(MEM[param_1] - MEM[param_2])", "(MEM[param_2] - MEM[param_1])"}
    assert "(not (MEM[param_2] < MEM[param_1]))" in rendered["(MEM[param_1] - MEM[param_2])"]
    assert "(MEM[param_2] < MEM[param_1])" in rendered["(MEM[param_2] - MEM[param_1])"]

def test_return_analyzer_keeps_even_iteration_wrapper_when_definite_replay_would_change_meaning():
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
                Expression.memory(steps_addr, size=4),
            ),
            start,
        ),
    )
    wrapped_steps_effect = Expression.binary_op(
        "INT_SUB",
        Expression.binary_op(
            "INT_ADD",
            limit,
            Expression.binary_op(
                "INT_ADD",
                Expression.binary_op(
                    "INT_ADD",
                    Expression.memory(steps_addr, size=4),
                    Expression.constant(1, 4),
                ),
                Expression.binary_op("INT_SUB", start, start),
            ),
        ),
        start,
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
                value=wrapped_steps_effect,
                conditions=[trace_nonnull, loop_active, even_iteration, final_iter],
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

    assert normalized.to_string() == "((MEM[param_1] + param_2) + ((param_3 + MEM[(param_1 + 4)]) - param_2))"

def test_expression_expander_expands_observed_load_phi_difference_into_cases():
    a = Expression.parameter("a", 0, size=8)
    b = Expression.parameter("b", 1, size=8)
    nonnull_a = Condition(Expression.binary_op("INT_NOTEQUAL", a, Expression.constant(0, 8)), False)
    nonnull_b = Condition(Expression.binary_op("INT_NOTEQUAL", b, Expression.constant(0, 8)), False)
    swap_taken = Condition(
        Expression.binary_op("INT_SLESS", Expression.memory(b, size=4), Expression.memory(a, size=4)),
        False,
    )
    traced = Expression.binary_op(
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
        def _trace_pcode_op(self, _op, depth=0, use_cache=False):
            return traced

    class FakeOp:
        def getMnemonic(self):
            return "INT_SUB"

        def getNumInputs(self):
            return 2

        def getInput(self, index):
            class In:
                def getDef(self):
                    return None
            return In()

        def getOutput(self):
            class Out:
                def getSize(self):
                    return 4
            return Out()

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

    expanded = expander._expand_input_operation(
        FakeOp(),
        [nonnull_a, nonnull_b],
        depth=0,
    )

    assert len(expanded) == 2
    rendered = {ev.value.to_string(): " ".join(cond.to_string() for cond in ev.conditions) for ev in expanded}
    assert rendered.keys() == {"(MEM[a] - MEM[b])", "(MEM[b] - MEM[a])"}
    assert "(a != 0)" in rendered["(MEM[a] - MEM[b])"]
    assert "(b != 0)" in rendered["(MEM[a] - MEM[b])"]
    assert "(not (MEM[b] < MEM[a]))" in rendered["(MEM[a] - MEM[b])"]
    assert "(a != 0)" in rendered["(MEM[b] - MEM[a])"]
    assert "(b != 0)" in rendered["(MEM[b] - MEM[a])"]
    assert "(MEM[b] < MEM[a])" in rendered["(MEM[b] - MEM[a])"]

def test_expression_expander_multiequal_shortcut_defers_flattened_observed_load_rewrite(monkeypatch):
    import scripts.function_tracer_pcode.semantics.transform.expander as expander_module

    a = Expression.parameter("a", 0, size=8)
    b = Expression.parameter("b", 1, size=8)
    nonnull_a = Condition(Expression.binary_op("INT_NOTEQUAL", a, Expression.constant(0, 8)), False)
    nonnull_b = Condition(Expression.binary_op("INT_NOTEQUAL", b, Expression.constant(0, 8)), False)
    swap_taken = Condition(
        Expression.binary_op("INT_SLESS", Expression.memory(b, size=4), Expression.memory(a, size=4)),
        False,
    )
    traced = Expression.binary_op(
        "INT_SUB",
        Expression.memory(a, size=4, read_order_key=20),
        Expression.memory(b, size=4, read_order_key=21),
    )
    flattened = Expression.binary_op(
        "INT_SUB",
        Expression.memory(a, size=4),
        Expression.memory(b, size=4),
    )
    rewritten_phi = Expression.binary_op(
        "INT_SUB",
        Expression.phi(
            [
                (swap_taken, Expression.memory(b, size=4)),
                (None, Expression.memory(a, size=4)),
            ]
        ),
        Expression.phi(
            [
                (swap_taken, Expression.memory(a, size=4)),
                (None, Expression.memory(b, size=4)),
            ]
        ),
    )
    rewritten_phi.operands[0].size = 4
    rewritten_phi.operands[1].size = 4
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
        def trace_varnode(self, _varnode, depth=0, use_cache=False):
            return traced

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

    monkeypatch.setattr(
        expander,
        "_canonicalize_traced_expression",
        lambda _expr, _conditions: flattened,
    )
    monkeypatch.setattr(
        expander_module,
        "rewrite_observed_loads_from_effects",
        lambda _expr, _conditions, _effects, _parameters: rewritten_phi,
    )
    monkeypatch.setattr(
        _mx_expander_canonical,
        "rewrite_observed_loads_from_effects",
        lambda _expr, _conditions, _effects, _parameters: rewritten_phi,
    )

    result = expander._trace_and_canonicalize_input_value(
        object(),
        [nonnull_a, nonnull_b],
        depth=0,
    )

    assert result is None

def test_canonicalize_post_state_subexpressions_rewrites_phi_operand_to_memory_location():
    a = Expression.parameter("a", 0, size=8)
    b = Expression.parameter("b", 1, size=8)
    swap_taken = Condition(
        Expression.binary_op("INT_SLESS", Expression.memory(b, size=4), Expression.memory(a, size=4)),
        False,
    )
    expr = Expression.binary_op(
        "INT_SUB",
        Expression.memory(a, size=4),
        Expression.phi(
            [
                (swap_taken, Expression.memory(a, size=4)),
                (None, Expression.memory(b, size=4)),
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
        [swap_taken],
        effects,
        [
            _param("a", size=8, is_signed=False),
            _param("b", size=8, is_signed=False, index=1),
        ],
    )

    assert normalized.to_string() == "(MEM[a] - MEM[b])"
