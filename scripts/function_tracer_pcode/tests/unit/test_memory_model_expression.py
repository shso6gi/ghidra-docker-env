from scripts.function_tracer_pcode.tests.unit._memory_model_fixtures import *

def test_additive_signature_does_not_require_to_string(monkeypatch):
    shared = Expression.parameter("param_1", index=0, size=4)
    expr = Expression.binary_op("INT_ADD", shared, Expression.constant(4, 4))
    expr.size = 4

    def _boom_expr(_self, simplify=True):
        raise AssertionError("additive signature should not depend on Expression.to_string")

    monkeypatch.setattr(Expression, "to_string", _boom_expr)

    signature = _additive_signature(expr)

    assert signature is not None
    constant, terms, width = signature
    assert constant == 4
    assert len(terms) == 1
    assert width == 4

def test_mips64_handler_detects_spurious_same_pattern_extension_violation():
    handler = MIPS64Handler(debug=False)
    counterexample = {"param_1_1": 0x400000000002, "param_1_2": 0x400000000002}
    analysis1 = FunctionReturnAnalysis(
        function_name="f1",
        entry_point="0x0",
        parameters=[{"name": "param_1", "data_type": "long", "size": 8, "index": 0, "is_signed": True}],
        returns=[],
    )
    analysis2 = FunctionReturnAnalysis(
        function_name="f2",
        entry_point="0x0",
        parameters=[{"name": "param_1", "data_type": "long", "size": 8, "index": 0, "is_signed": True}],
        returns=[],
    )

    handler._analyze_parameter_usage = lambda analysis: {
        ("parameter_index", 0): ParameterSemanticHint(narrow_bits=32, signedness="signed")
    }

    constraints = handler.detect_spurious_counterexample(
        counterexample,
        analysis1,
        analysis2,
        is_mips64_1=True,
        is_mips64_2=True,
    )

    assert constraints == {"param_1_1": ("signed", 32), "param_1_2": ("signed", 32)}

def test_mips64_width_alignment_does_not_narrow_fp_parameter_by_ordinal_peer():
    handler = MIPS64Handler(debug=False)
    mips_analysis = FunctionReturnAnalysis(
        function_name="sphbes_like_mips",
        entry_point="0x0",
        parameters=[
            {"name": "param_1", "data_type": "int", "size": 4, "index": 0, "is_signed": True},
            {"name": "param_2", "data_type": "double", "size": 8, "index": 1, "is_signed": True},
        ],
        returns=[],
    )
    other_analysis = FunctionReturnAnalysis(
        function_name="sphbes_like_other",
        entry_point="0x0",
        parameters=[
            {"name": "param_1", "data_type": "double", "size": 8, "index": 0, "is_signed": True},
            {"name": "param_2", "data_type": "int", "size": 4, "index": 1, "is_signed": True},
        ],
        returns=[],
    )

    override_map = handler.detect_param_type_mismatch(mips_analysis, other_analysis)

    assert override_map == {}

def test_substitute_condition_simplifies_stack_local_nonnull_guard():
    params = [_param("param_1", size=8, is_signed=False)]
    sp = Expression.variable(
        "sp",
        size=8,
        storage_info=StorageInfo(
            is_register=True,
            space_name="register",
            register_name="sp",
            base_register_name="sp",
            size=8,
            size_bits=64,
            base_register_size=8,
            base_register_size_bits=64,
            bit_offset_in_base=0,
        ),
    )
    local_addr = Expression.binary_op("INT_ADD", sp, Expression.constant(-0x1C, 8))
    guard = Condition(
        Expression.binary_op(
            "INT_NOTEQUAL",
            Expression.parameter("out", 1, size=8),
            Expression.constant(0, 8),
        ),
        False,
    )

    substituted = substitute_condition(
        guard,
        _build_parameter_replacements([{"name": "out", "index": 1}], [local_addr]),
        params,
    )

    assert substituted.expression.expr_type.name == "CONSTANT"
    assert substituted.expression.value == 1

def test_find_block_info_for_pcode_op_uses_stable_ref_not_object_identity():
    class FakeOp:
        def __init__(self, ref):
            self.ref = ref

    class FakeBlock:
        def __init__(self, ops):
            self.pcode_ops = list(ops)

    class FakeTracer:
        def _make_pcode_op_ref(self, op):
            return op.ref

    class FakeConditionTracker:
        def __init__(self, block):
            self.tracer = FakeTracer()
            self.block_by_index = {0: block}

    ref = PcodeOpRef(
        address_offset=0x1000,
        seq_time=7,
        seq_order=0,
        block_index=3,
        mnemonic="CALL",
        input_sizes=(8,),
        output_size=4,
    )
    block_op = FakeOp(ref)
    query_op = FakeOp(ref)
    block = FakeBlock([block_op])

    assert _find_block_info_for_pcode_op(FakeConditionTracker(block), query_op) is block

def test_resolve_parameter_name_rejects_full_register_when_only_fragment_param_exists():
    params = [
        _param(
            "param_1",
            size=4,
            is_signed=False,
            index=0,
            storage={
                **_reg_storage("a0", size_bytes=4, register_name="a0_lo"),
                "offset": 36,
                "bit_offset_in_base": 32,
                "base_register_size": 8,
                "base_register_size_bits": 64,
            },
        )
    ]

    full_reg_expr = Expression.variable(
        "a0",
        size=8,
        storage_info=StorageInfo(**_reg_storage("a0", size_bytes=8, register_name="a0")),
    )
    fragment_expr = Expression.variable(
        "a0_lo",
        size=4,
        storage_info=StorageInfo(
            is_register=True,
            space_name="register",
            offset=36,
            size=4,
            size_bits=32,
            register_name="a0_lo",
            base_register_name="a0",
            base_register_offset=0,
            base_register_size=8,
            base_register_size_bits=64,
            bit_offset_in_base=32,
        ),
    )

    assert _resolve_parameter_name(full_reg_expr, params) is None
    assert _resolve_parameter_name(fragment_expr, params) == "param_1"

def test_expression_expander_collapses_nested_multiequal_using_active_conditions():
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
        [swap_taken],
        depth=0,
    )

    assert len(expanded) == 1
    assert expanded[0].value.to_string() == "MEM[b]"

def test_expression_expander_collapses_nested_multiequal_with_grouped_active_conditions():
    a = Expression.parameter("a", 0, size=8)
    b = Expression.parameter("b", 1, size=8)
    nonnull_a = Condition(Expression.binary_op("INT_NOTEQUAL", a, Expression.constant(0, 8)), False)
    nonnull_b = Condition(Expression.binary_op("INT_NOTEQUAL", b, Expression.constant(0, 8)), False)
    nonnull = Condition.combine_and([nonnull_a, nonnull_b])
    swap_taken = Condition(
        Expression.binary_op("INT_SLESS", Expression.memory(b, size=4), Expression.memory(a, size=4)),
        False,
    )
    no_swap = Condition(swap_taken.expression, True)
    post_swap_b = Expression.phi(
        [
            (Condition.combine_and([nonnull, swap_taken]), Expression.memory(a, size=4)),
            (Condition.combine_and([nonnull, no_swap]), Expression.memory(b, size=4)),
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
        [nonnull, swap_taken],
        depth=0,
    )

    assert len(expanded) == 1
    assert expanded[0].value.to_string() == "MEM[b]"

def test_return_analyzer_reduces_phi_bearing_expanded_return_without_recanonicalizing():
    a = Expression.parameter("param_1", 0, size=8)
    b = Expression.parameter("param_2", 1, size=8)
    nonnull_a = Condition(Expression.binary_op("INT_NOTEQUAL", a, Expression.constant(0, 8)), False)
    nonnull_b = Condition(Expression.binary_op("INT_NOTEQUAL", b, Expression.constant(0, 8)), False)
    swap_taken = Condition(
        Expression.binary_op("INT_SLESS", Expression.memory(b, size=4), Expression.memory(a, size=4)),
        False,
    )
    composite_less = Condition.combine_and([nonnull_a, nonnull_b, swap_taken])
    composite_not_less = Condition.combine_and([nonnull_a, nonnull_b, swap_taken.negate()])
    value = Expression.binary_op(
        "INT_SUB",
        Expression.phi(
            [
                (composite_less, Expression.memory(b, size=4)),
                (composite_not_less, Expression.memory(a, size=4)),
            ]
        ),
        Expression.phi(
            [
                (composite_less, Expression.memory(a, size=4)),
                (composite_not_less, Expression.memory(b, size=4)),
            ]
        ),
    )
    value.operands[0].size = 4
    value.operands[1].size = 4
    analyzer = ReturnAnalyzer(program=object(), debug=False)
    analyzer._current_effect_summary = EffectSummary(
        parameter_names=["param_1", "param_2"],
        effects=[
            StoreEffect(
                location=_loc("param_1", 0, 4),
                value=Expression.memory(b, size=4),
                conditions=[swap_taken],
                order_key=1,
            ),
            StoreEffect(
                location=_loc("param_2", 0, 4),
                value=Expression.memory(a, size=4),
                conditions=[swap_taken],
                order_key=2,
            ),
        ],
    )
    analyzer._current_parameters = [
        _param("param_1", size=8, is_signed=False),
        _param("param_2", size=8, is_signed=False, index=1),
    ]

    normalized_less = analyzer._normalize_expanded_return_value(
        value,
        [nonnull_a, nonnull_b, swap_taken],
    )
    normalized_not_less = analyzer._normalize_expanded_return_value(
        value,
        [nonnull_a, nonnull_b, swap_taken.negate()],
    )

    assert normalized_less.to_string() == "(MEM[param_2] - MEM[param_1])"
    assert normalized_not_less.to_string() == "(MEM[param_1] - MEM[param_2])"

def test_expression_expander_reduces_full_operation_trace_under_active_conditions_regression():
    a = Expression.parameter("a", 0, size=8)
    b = Expression.parameter("b", 1, size=8)
    swap_taken = Condition(
        Expression.binary_op("INT_SLESS", Expression.memory(b, size=4), Expression.memory(a, size=4)),
        False,
    )
    no_swap = Condition(swap_taken.expression, True)
    expr = Expression.binary_op(
        "INT_SUB",
        Expression.phi(
            [
                (no_swap, Expression.memory(a, size=4)),
                (swap_taken, Expression.memory(b, size=4)),
            ]
        ),
        Expression.phi(
            [
                (no_swap, Expression.memory(b, size=4)),
                (swap_taken, Expression.memory(a, size=4)),
            ]
        ),
    )
    expr.operands[0].size = 4
    expr.operands[1].size = 4
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
        def _trace_pcode_op(self, _op, depth=0, use_cache=False):
            return expr

    class FakeOp:
        def getMnemonic(self):
            return "INT_SUB"

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

    direct = expander._trace_operation_expression(FakeOp(), [no_swap], 0, output_size=4)

    assert direct is not None
    assert direct.to_string() == "(MEM[a] - MEM[b])"

def test_phi_handler_merge_preserves_same_value_with_distinct_conditions():
    a = Expression.parameter("a", 0, size=8)
    swap_taken = Condition(
        Expression.binary_op("INT_NOTEQUAL", a, Expression.constant(0, 8)),
        False,
    )
    no_swap = swap_taken.negate()

    class FakeTracer:
        debug = False

    handler = PhiHandler(FakeTracer(), condition_tracker=None)
    merged = handler._merge_branches(
        [
            PhiExpandedBranch([swap_taken], Expression.memory(a, size=4)),
            PhiExpandedBranch([no_swap], Expression.memory(a, size=4)),
        ]
    )

    assert len(merged) == 2

def test_expression_expander_reduces_full_operation_trace_under_active_conditions():
    a = Expression.parameter("a", 0, size=8)
    b = Expression.parameter("b", 1, size=8)
    swap_taken = Condition(
        Expression.binary_op("INT_SLESS", Expression.memory(b, size=4), Expression.memory(a, size=4)),
        False,
    )
    no_swap = Condition(swap_taken.expression, True)
    expr = Expression.binary_op(
        "INT_SUB",
        Expression.phi(
            [
                (no_swap, Expression.memory(a, size=4)),
                (swap_taken, Expression.memory(b, size=4)),
            ]
        ),
        Expression.phi(
            [
                (no_swap, Expression.memory(b, size=4)),
                (swap_taken, Expression.memory(a, size=4)),
            ]
        ),
    )
    expr.operands[0].size = 4
    expr.operands[1].size = 4
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
        def _trace_pcode_op(self, _op, depth=0, use_cache=False):
            return expr

    class FakeOp:
        def getMnemonic(self):
            return "INT_SUB"

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

    direct = expander._trace_operation_expression(FakeOp(), [no_swap], 0, output_size=4)

    assert direct is not None
    assert direct.to_string() == "(MEM[a] - MEM[b])"

def test_expression_expander_uses_whole_operation_shortcut_before_recursive_cartesian_combine(monkeypatch):
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

    class FakeDef:
        def getMnemonic(self):
            return "MULTIEQUAL"

    class FakeInput:
        def getDef(self):
            return FakeDef()

    class FakeTracer:
        debug = False

        def _trace_pcode_op(self, _op, depth=0, use_cache=False):
            return traced

    class FakeOp:
        def getMnemonic(self):
            return "INT_SUB"

        def getNumInputs(self):
            return 2

        def getInput(self, index):
            return FakeInput()

        def getOutput(self):
            class Out:
                def getSize(self):
                    return 4
            return Out()

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
                ),
                StoreEffect(
                    location=_loc("b", 0, 4),
                    value=Expression.memory(a, size=4),
                    conditions=[swap_taken],
                    order_key=11,
                ),
            ],
        ),
        parameters=[
            _param("a", size=8, is_signed=False),
            _param("b", size=8, is_signed=False, index=1),
        ],
    )

    monkeypatch.setattr(
        expander,
        "_expand_input_varnode",
        lambda *_args, **_kwargs: (_ for _ in ()).throw(AssertionError("recursive combine should not run")),
    )

    expanded = expander._expand_input_operation(
        FakeOp(),
        [nonnull_a, nonnull_b],
        depth=0,
    )

    assert len(expanded) == 2
    rendered = {ev.value.to_string(): " ".join(cond.to_string() for cond in ev.conditions) for ev in expanded}
    assert rendered.keys() == {"(MEM[a] - MEM[b])", "(MEM[b] - MEM[a])"}
