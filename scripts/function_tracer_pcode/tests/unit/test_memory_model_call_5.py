from scripts.function_tracer_pcode.tests.unit._memory_model_fixtures import *

def test_call_effect_summary_policy_accepts_interdependent_swap_writes():
    summary = EffectSummary(
        parameter_names=["a", "b"],
        effects=[
            StoreEffect(
                location=_loc("a", 0, 4),
                value=Expression.memory(Expression.parameter("b", 1, size=8), size=4),
                conditions=[],
                order_key=1,
            ),
            StoreEffect(
                location=_loc("b", 0, 4),
                value=Expression.memory(Expression.parameter("a", 0, size=8), size=4),
                conditions=[],
                order_key=2,
            ),
        ],
    )

    assert is_call_effect_summary_allowed(summary)

def test_effect_summary_rewrites_observed_post_call_loads_into_phi_difference():
    a = Expression.parameter("a", 0, size=8)
    b = Expression.parameter("b", 1, size=8)
    nonnull_a = Condition(Expression.binary_op("INT_NOTEQUAL", a, Expression.constant(0, 8)), False)
    nonnull_b = Condition(Expression.binary_op("INT_NOTEQUAL", b, Expression.constant(0, 8)), False)
    original = Expression.binary_op(
        "INT_SUB",
        Expression.memory(a, size=4, read_order_key=20),
        Expression.memory(b, size=4, read_order_key=21),
    )
    swap_taken = Condition(
        Expression.binary_op("INT_SLESS", Expression.memory(b, size=4), Expression.memory(a, size=4)),
        False,
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

    rewritten = rewrite_observed_loads_from_effects(
        original,
        [nonnull_a, nonnull_b],
        effects,
        [
            _param("a", size=8, is_signed=False),
            _param("b", size=8, is_signed=False, index=1),
        ],
    )

    assert rewritten.to_string() == "(PHI(MEM[b] if (MEM[b] < MEM[a]), MEM[a]) - PHI(MEM[a] if (MEM[b] < MEM[a]), MEM[b]))"

def test_normalize_post_state_expression_preserves_iteration_delta_wrapped_step_value_symbolically():
    trace = Expression.parameter("trace", 0, size=8)
    start = Expression.parameter("start", 1, size=4)
    limit = Expression.parameter("limit", 2, size=4)
    steps_addr = Expression.binary_op("INT_ADD", trace, Expression.constant(4, 8))

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

    wrapped_expr = Expression.binary_op(
        "INT_SUB",
        Expression.binary_op(
            "INT_ADD",
            limit,
            Expression.binary_op(
                "INT_ADD",
                Expression.memory(steps_addr, size=4),
                Expression.constant(1, 4),
            ),
        ),
        start,
    )
    normalized = normalize_post_state_expression(
        wrapped_expr,
        [trace_nonnull, loop_active, final_iter],
        [
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
        [
            _param("trace", size=8, is_signed=False),
            _param("start", size=4, index=1),
            _param("limit", size=4, index=2),
        ],
        symbolic_post_state=True,
    )

    assert normalized is not None
    assert expression_contains_post_state_reads(normalized)

def test_return_analyzer_accepts_semantically_lossless_swap_snapshot_rewrite():
    a = Expression.parameter("a", 0, size=8)
    b = Expression.parameter("b", 1, size=8)
    nonnull_a = Condition(Expression.binary_op("INT_NOTEQUAL", a, Expression.constant(0, 8)), False)
    nonnull_b = Condition(Expression.binary_op("INT_NOTEQUAL", b, Expression.constant(0, 8)), False)
    swap_taken = Condition(
        Expression.binary_op("INT_SLESS", Expression.memory(b, size=4), Expression.memory(a, size=4)),
        False,
    )
    original = Expression.binary_op(
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

    analyzer = ReturnAnalyzer(program=object(), debug=False)
    analyzer._current_parameters = [
        _param("a", size=8, is_signed=False),
        _param("b", size=8, is_signed=False, index=1),
    ]
    rewritten = promote_observed_loads_to_post_state_reads(
        original,
        [nonnull_a, nonnull_b],
        effect_summary.effects,
        analyzer._current_parameters,
        symbolic_post_state=True,
    )

    assert rewritten is not None
    assert analyzer._accept_effect_sensitive_rewrite(
        original,
        rewritten,
        [nonnull_a, nonnull_b],
        effect_summary,
        rewrite_kind="observed-load",
    ) is True

def test_effect_summary_resolves_callind_target_from_traced_constant():
    class FakeVarnode:
        def __init__(self, is_constant=False):
            self._is_constant = is_constant

        def isConstant(self):
            return self._is_constant

    class FakeAddressSpace:
        def getAddress(self, value):
            return value

    class FakeAddressFactory:
        def getDefaultAddressSpace(self):
            return FakeAddressSpace()

    class FakeFunction:
        def __init__(self, name):
            self._name = name

        def getName(self):
            return self._name

    class FakeFunctionManager:
        def getFunctionAt(self, addr):
            if addr == 0x401000:
                return FakeFunction("callee")
            return None

    class FakeProgram:
        def getAddressFactory(self):
            return FakeAddressFactory()

        def getFunctionManager(self):
            return FakeFunctionManager()

    class FakeTracer:
        def __init__(self):
            self.program = FakeProgram()

        def _get_function_name(self, _addr_varnode):
            return "UNKNOWN_FUNC"

        def trace_varnode(self, _varnode, use_cache=False):
            return Expression.constant(0x401000, 8)

    class FakeOp:
        def __init__(self):
            self._input = FakeVarnode(is_constant=False)

        def getNumInputs(self):
            return 1

        def getInput(self, index):
            assert index == 0
            return self._input

        def getMnemonic(self):
            return "CALLIND"

    assert _resolve_call_target_name(FakeTracer(), FakeOp()) == "callee"

def test_effect_summary_resolves_call_target_from_traced_constant():
    class FakeVarnode:
        def __init__(self, is_constant=False):
            self._is_constant = is_constant

        def isConstant(self):
            return self._is_constant

    class FakeAddressSpace:
        def getAddress(self, value):
            return value

    class FakeAddressFactory:
        def getDefaultAddressSpace(self):
            return FakeAddressSpace()

    class FakeFunction:
        def __init__(self, name):
            self._name = name

        def getName(self):
            return self._name

    class FakeFunctionManager:
        def getFunctionAt(self, addr):
            if addr == 0x401000:
                return FakeFunction("callee")
            return None

        def getFunctionContaining(self, addr):
            return self.getFunctionAt(addr)

    class FakeProgram:
        def getAddressFactory(self):
            return FakeAddressFactory()

        def getFunctionManager(self):
            return FakeFunctionManager()

    class FakeTracer:
        def __init__(self):
            self.program = FakeProgram()

        def _get_function_name(self, _addr_varnode):
            return "UNKNOWN_FUNC"

        def trace_varnode(self, _varnode, use_cache=False):
            return Expression.constant(0x401000, 8)

    class FakeOp:
        def __init__(self):
            self._input = FakeVarnode(is_constant=False)

        def getNumInputs(self):
            return 1

        def getInput(self, index):
            assert index == 0
            return self._input

        def getMnemonic(self):
            return "CALL"

    assert _resolve_call_target_name(FakeTracer(), FakeOp()) == "callee"

def test_tracer_deferred_call_target_ref_uses_traced_constant_target_expression():
    class FakeAddressSpace:
        def getAddress(self, value):
            return value

    class FakeAddressFactory:
        def getDefaultAddressSpace(self):
            return FakeAddressSpace()

    class FakeFunction:
        def __init__(self, name, entry, program):
            self._name = name
            self._entry = entry
            self._program = program

        def getName(self):
            return self._name

        def getEntryPoint(self):
            return self._entry

        def getProgram(self):
            return self._program

    class FakeFunctionManager:
        def __init__(self, program):
            self.program = program

        def getFunctionAt(self, addr):
            if addr == 0x401000:
                return FakeFunction("callee", 0x401000, self.program)
            return None

        def getReferencedFunction(self, _addr):
            return None

        def getFunctionContaining(self, _addr):
            return None

    class FakeProgram:
        def __init__(self):
            self._function_manager = FakeFunctionManager(self)

        def getAddressFactory(self):
            return FakeAddressFactory()

        def getFunctionManager(self):
            return self._function_manager

        def getUniqueProgramID(self):
            return 77

    class FakeOp:
        def getNumInputs(self):
            return 1

        def getInput(self, index):
            assert index == 0
            return object()

    tracer = object.__new__(PcodeTracer)
    tracer.program = FakeProgram()
    tracer.resolve_call_target_ref = lambda *_args, **_kwargs: None
    tracer.trace_varnode = lambda *_args, **_kwargs: Expression.constant(0x401000, 8)

    target_ref = PcodeTracer._resolve_call_target_ref_from_op(
        tracer,
        FakeOp(),
        depth=0,
        use_cache=False,
    )

    assert target_ref.is_function() is True
    assert target_ref.display_name() == "callee"
    assert target_ref.stable_key() == ("function", 77, 0x401000)

def test_call_effect_summary_policy_accepts_simple_param_store_summary():
    summary = EffectSummary(
        parameter_names=["ptr", "value"],
        effects=[
            StoreEffect(
                location=_loc("ptr", 0, 4),
                value=Expression.binary_op(
                    "INT_ADD",
                    Expression.memory(Expression.parameter("ptr", 0, size=8), size=4),
                    Expression.parameter("value", 1, size=4),
                ),
                conditions=[],
                order_key=1,
            )
        ],
    )

    assert is_call_effect_summary_allowed(summary)

def test_call_effect_summary_policy_rejects_nested_call_values():
    summary = EffectSummary(
        parameter_names=["ptr"],
        effects=[
            StoreEffect(
                location=_loc("ptr", 0, 4),
                value=Expression.call("callee", [Expression.parameter("ptr", 0, size=8)]),
                conditions=[],
                order_key=1,
            )
        ],
    )

    assert not is_call_effect_summary_allowed(summary)

def test_call_effect_summary_policy_rejects_unsupported_nested_calls():
    summary = EffectSummary(
        parameter_names=["ptr"],
        effects=[
            StoreEffect(
                location=_loc("ptr", 0, 4),
                value=Expression.constant(1, 4),
                conditions=[],
                order_key=1,
            )
        ],
        has_unsupported_call=True,
    )

    assert not is_call_effect_summary_allowed(summary)

def test_call_effect_summary_policy_rejects_incomplete_summary():
    summary = EffectSummary(
        parameter_names=["ptr"],
        effects=[
            StoreEffect(
                location=_loc("ptr", 0, 4),
                value=Expression.constant(1, 4),
                conditions=[],
                order_key=1,
            )
        ],
        incomplete_reasons=("effect_summary_path_coverage_incomplete",),
    )

    assert not is_call_effect_summary_allowed(summary)
