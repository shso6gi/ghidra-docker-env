from scripts.function_tracer_pcode.tests.unit._memory_model_fixtures import *

def test_effect_summary_does_not_reapply_when_expr_matches_phi_branch_value():
    dst = Expression.parameter("dst", 0, size=8)
    src = Expression.parameter("src", 1, size=8)
    choose_src = Expression.parameter("choose_src", 2, size=4)
    choose_true = Condition(
        Expression.binary_op("INT_NOTEQUAL", choose_src, Expression.constant(0, 4)),
        False,
    )
    choose_false = choose_true.negate()
    original = Expression.binary_op("INT_ADD", Expression.memory(dst, size=4), Expression.constant(1, 4))
    effect = StoreEffect(
        location=_loc("dst", 0, 4),
        value=Expression.phi(
            [
                (choose_true, Expression.memory(src, size=4)),
                (None, Expression.binary_op("INT_ADD", Expression.memory(dst, size=4), Expression.constant(1, 4))),
            ]
        ),
        conditions=[],
        order_key=3,
    )

    rewritten = rewrite_loads_from_effects(
        original,
        [choose_false],
        [effect],
        [
            _param("dst", size=8, is_signed=False),
            _param("src", size=8, is_signed=False, index=1),
            _param("choose_src", size=4, index=2),
        ],
    )

    assert rewritten.to_string() == "(MEM[dst] + 1)"

def test_effect_summary_does_not_reapply_when_expr_matches_true_phi_branch_value():
    dst = Expression.parameter("dst", 0, size=8)
    src = Expression.parameter("src", 1, size=8)
    choose_src = Expression.parameter("choose_src", 2, size=4)
    choose_true = Condition(
        Expression.binary_op("INT_NOTEQUAL", choose_src, Expression.constant(0, 4)),
        False,
    )
    original = Expression.memory(src, size=4)
    effect = StoreEffect(
        location=_loc("dst", 0, 4),
        value=Expression.phi(
            [
                (choose_true, Expression.memory(src, size=4)),
                (None, Expression.binary_op("INT_ADD", Expression.memory(dst, size=4), Expression.constant(1, 4))),
            ]
        ),
        conditions=[],
        order_key=3,
    )

    rewritten = rewrite_loads_from_effects(
        original,
        [choose_true],
        [effect],
        [
            _param("dst", size=8, is_signed=False),
            _param("src", size=8, is_signed=False, index=1),
            _param("choose_src", size=4, index=2),
        ],
    )

    assert rewritten.to_string() == "MEM[src]"

def test_effect_summary_prefers_traced_constant_over_synthetic_fun_name():
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
            return "FUN_401000"

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

def test_expander_combines_load_inputs_into_memory_expression():
    tracer = type("Tracer", (), {"debug": False})()
    expander = ExpressionExpander(tracer, condition_tracker=None, debug=False)

    result = expander._combine_input_expansions_with_conditions(
        "LOAD",
        [
            [ExpandedValue(Expression.constant(0x1B1, 4), [])],
            [ExpandedValue(Expression.parameter("ptr", 0, size=8), [])],
        ],
        [],
        0,
        output_size=4,
    )

    assert len(result) == 1
    assert result[0].value.expr_type.name == "MEMORY"
    assert result[0].value.to_string() == "MEM[ptr]"

def test_expander_resolves_indirect_stack_slot_read_via_effect_summary():
    class FakeOutputVarnode:
        def getHigh(self):
            return None

    class FakeTracer:
        debug = False

        def _get_storage_info_from_varnode(self, _varnode):
            return StorageInfo(**_stack_storage(-0x1C, size_bytes=4))

    expander = ExpressionExpander(
        FakeTracer(),
        condition_tracker=None,
        debug=False,
        effect_summary=EffectSummary(
            parameter_names=["a", "b"],
            effects=[
                StoreEffect(
                    location=_loc("__locbase__stackframe", -0x1C, 4),
                    value=Expression.binary_op(
                        "INT_ADD",
                        Expression.parameter("a", 0, size=4),
                        Expression.parameter("b", 1, size=4),
                    ),
                    conditions=[],
                    order_key=1,
                )
            ],
        ),
        parameters=[
            _param("a", size=4, is_signed=False, index=0),
            _param("b", size=4, is_signed=False, index=1),
        ],
    )

    result = expander._combine_input_expansions_with_conditions(
        "INDIRECT",
        [
            [ExpandedValue(Expression.constant(0, 4), [])],
            [ExpandedValue(Expression.constant(0x28, 4), [])],
        ],
        [],
        0,
        output_size=4,
        output_varnode=FakeOutputVarnode(),
    )

    assert len(result) == 1
    assert result[0].value.to_string() == "(a + b)"
