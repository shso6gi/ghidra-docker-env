from scripts.function_tracer_pcode.tests.unit._memory_model_fixtures import *

def test_summarize_store_effects_recovers_direct_call_store_values_from_call_expander():
    class FakeAddress:
        def __init__(self, offset):
            self._offset = offset

        def getOffset(self):
            return self._offset

    class FakeSeqnum:
        def __init__(self, offset, order):
            self._target = FakeAddress(offset)
            self._order = order

        def getTarget(self):
            return self._target

        def getOrder(self):
            return self._order

    class FakeVarnode:
        def __init__(self, key, size, def_op=None):
            self.key = key
            self._size = size
            self._def_op = def_op

        def getSize(self):
            return self._size

        def getDef(self):
            return self._def_op

        def getHigh(self):
            return None

    class FakeCallOp:
        def __init__(self):
            self._inputs = [
                FakeVarnode("target", 8),
                FakeVarnode("lhs", 4),
                FakeVarnode("rhs", 4),
            ]
            self._seqnum = FakeSeqnum(0x401180, 2)

        def getMnemonic(self):
            return "CALL"

        def getNumInputs(self):
            return len(self._inputs)

        def getInput(self, index):
            return self._inputs[index]

        def getOutput(self):
            return None

        def getSeqnum(self):
            return self._seqnum

    class FakeStoreOp:
        def __init__(self, call_op):
            self._inputs = [
                FakeVarnode("space", 4),
                FakeVarnode("addr", 8),
                FakeVarnode("value", 4, def_op=call_op),
            ]
            self._seqnum = FakeSeqnum(0x401190, 3)

        def getMnemonic(self):
            return "STORE"

        def getNumInputs(self):
            return len(self._inputs)

        def getInput(self, index):
            return self._inputs[index]

        def getOutput(self):
            return None

        def getSeqnum(self):
            return self._seqnum

    class FakeBlockInfo:
        def __init__(self, *ops):
            self.pcode_ops = list(ops)

    class FakeConditionTracker:
        def get_all_valid_paths_to_block(self, _block):
            return [[]]

    class FakeTracer:
        def _get_function_name(self, varnode):
            if getattr(varnode, "key", None) == "target":
                return "fc_add"
            return "UNKNOWN_FUNC"

        def trace_varnode(self, varnode, use_cache=False):
            if varnode.key == "addr":
                return Expression.parameter("slot", 0, size=8)
            if varnode.key == "lhs":
                return Expression.parameter("lhs", 1, size=4)
            if varnode.key == "rhs":
                return Expression.parameter("rhs", 2, size=4)
            if varnode.key == "value":
                return Expression.unknown("call_out_of_scope:fc_add")
            return Expression.constant(0, max(1, varnode.getSize()))

    call_op = FakeCallOp()
    summary = summarize_store_effects(
        [FakeBlockInfo(FakeStoreOp(call_op))],
        FakeTracer(),
        FakeConditionTracker(),
        [
            _param("slot", size=8, is_signed=False, index=0, storage=_reg_storage("x0", register_name="x0")),
            _param("lhs", size=4, index=1, storage=_reg_storage("x1", size_bytes=4, register_name="w1")),
            _param("rhs", size=4, index=2, storage=_reg_storage("x2", size_bytes=4, register_name="w2")),
        ],
        direct_call_expander=lambda _target_ref, args: [
            ExpandedValue(Expression.binary_op("INT_ADD", args[0], args[1]), [])
        ],
        resolve_callee_parameters=lambda _target_ref: [
            _param("a", size=4, index=0, storage=_reg_storage("x0", size_bytes=4, register_name="w0")),
            _param("b", size=4, index=1, storage=_reg_storage("x1", size_bytes=4, register_name="w1")),
        ],
        debug=False,
    )

    assert summary.has_unsupported_call is False
    assert len(summary.effects) == 1
    assert summary.effects[0].location == _loc("slot", 0, 4)
    assert summary.effects[0].value.to_string() == "(lhs + rhs)"

def test_summarize_store_effects_expands_nested_copy_and_arithmetic_store_values_object_centrically():
    class FakeAddress:
        def __init__(self, offset):
            self._offset = offset

        def getOffset(self):
            return self._offset

    class FakeSeqnum:
        def __init__(self, offset, order):
            self._target = FakeAddress(offset)
            self._order = order

        def getTarget(self):
            return self._target

        def getOrder(self):
            return self._order

    class FakeVarnode:
        def __init__(self, key, size, def_op=None):
            self.key = key
            self._size = size
            self._def_op = def_op

        def getSize(self):
            return self._size

        def getDef(self):
            return self._def_op

        def getHigh(self):
            return None

    class FakeCallOp:
        def __init__(self):
            self._inputs = [
                FakeVarnode("target", 8),
                FakeVarnode("lhs", 4),
                FakeVarnode("rhs", 4),
            ]
            self._output = FakeVarnode("ret", 4, def_op=self)
            self._seqnum = FakeSeqnum(0x401180, 2)

        def getMnemonic(self):
            return "CALL"

        def getNumInputs(self):
            return len(self._inputs)

        def getInput(self, index):
            return self._inputs[index]

        def getOutput(self):
            return self._output

        def getSeqnum(self):
            return self._seqnum

    class FakeCopyOp:
        def __init__(self, source):
            self._inputs = [source]
            self._output = FakeVarnode("copied", 4, def_op=self)
            self._seqnum = FakeSeqnum(0x401184, 3)

        def getMnemonic(self):
            return "COPY"

        def getNumInputs(self):
            return len(self._inputs)

        def getInput(self, index):
            return self._inputs[index]

        def getOutput(self):
            return self._output

        def getSeqnum(self):
            return self._seqnum

    class FakeAddOp:
        def __init__(self, lhs, rhs):
            self._inputs = [lhs, rhs]
            self._output = FakeVarnode("sum", 4, def_op=self)
            self._seqnum = FakeSeqnum(0x401188, 4)

        def getMnemonic(self):
            return "INT_ADD"

        def getNumInputs(self):
            return len(self._inputs)

        def getInput(self, index):
            return self._inputs[index]

        def getOutput(self):
            return self._output

        def getSeqnum(self):
            return self._seqnum

    class FakeStoreOp:
        def __init__(self, value_varnode):
            self._inputs = [
                FakeVarnode("space", 4),
                FakeVarnode("addr", 8),
                value_varnode,
            ]
            self._seqnum = FakeSeqnum(0x401190, 5)

        def getMnemonic(self):
            return "STORE"

        def getNumInputs(self):
            return len(self._inputs)

        def getInput(self, index):
            return self._inputs[index]

        def getOutput(self):
            return None

        def getSeqnum(self):
            return self._seqnum

    class FakeBlockInfo:
        def __init__(self, *ops):
            self.pcode_ops = list(ops)

    class FakeConditionTracker:
        def get_all_valid_paths_to_block(self, _block):
            return [[]]

    class FakeTracer:
        def _get_function_name(self, varnode):
            if getattr(varnode, "key", None) == "target":
                return "fc_add"
            return "UNKNOWN_FUNC"

        def _trace_pcode_op(self, pcode_op, depth=0, use_cache=False):
            mnemonic = pcode_op.getMnemonic()
            if mnemonic == "INT_ADD":
                return Expression.binary_op(
                    "INT_ADD",
                    self.trace_varnode(pcode_op.getInput(0), use_cache=False),
                    self.trace_varnode(pcode_op.getInput(1), use_cache=False),
                )
            raise AssertionError(f"unexpected traced op: {mnemonic}")

        def trace_varnode(self, varnode, depth=0, use_cache=False):
            if varnode.key == "addr":
                return Expression.parameter("slot", 0, size=8)
            if varnode.key == "lhs":
                return Expression.parameter("lhs", 1, size=4)
            if varnode.key == "rhs":
                return Expression.parameter("rhs", 2, size=4)
            if varnode.key == "copied":
                return Expression.unknown("copied_call_value")
            if varnode.key == "ret":
                return Expression.unknown("call_out_of_scope:fc_add")
            if varnode.key == "sum":
                return Expression.unknown("nested_sum")
            return Expression.constant(0, max(1, varnode.getSize()))

        def _get_op_order_key(self, pcode_op):
            return pcode_op.getSeqnum().getOrder()

    call_op = FakeCallOp()
    copy_op = FakeCopyOp(call_op.getOutput())
    add_op = FakeAddOp(copy_op.getOutput(), FakeVarnode("rhs", 4))

    summary = summarize_store_effects(
        [FakeBlockInfo(call_op, copy_op, add_op, FakeStoreOp(add_op.getOutput()))],
        FakeTracer(),
        FakeConditionTracker(),
        [
            _param("slot", size=8, is_signed=False, index=0, storage=_reg_storage("x0", register_name="x0")),
            _param("lhs", size=4, index=1, storage=_reg_storage("x1", size_bytes=4, register_name="w1")),
            _param("rhs", size=4, index=2, storage=_reg_storage("x2", size_bytes=4, register_name="w2")),
        ],
        direct_call_expander=lambda _target_ref, args: [
            ExpandedValue(Expression.binary_op("INT_ADD", args[0], args[1]), [])
        ],
        resolve_callee_parameters=lambda _target_ref: [
            _param("a", size=4, index=0, storage=_reg_storage("x0", size_bytes=4, register_name="w0")),
            _param("b", size=4, index=1, storage=_reg_storage("x1", size_bytes=4, register_name="w1")),
        ],
        debug=False,
    )

    assert summary.has_unsupported_call is False
    assert len(summary.effects) == 1
    assert summary.effects[0].location == _loc("slot", 0, 4)
    assert summary.effects[0].value.to_string() == "((lhs + rhs) + rhs)"

def test_summarize_store_effects_keeps_effect_free_value_calls_from_poisoning_summary():
    class FakeAddress:
        def __init__(self, offset):
            self._offset = offset

        def getOffset(self):
            return self._offset

    class FakeSeqnum:
        def __init__(self, offset, order):
            self._target = FakeAddress(offset)
            self._order = order

        def getTarget(self):
            return self._target

        def getOrder(self):
            return self._order

    class FakeVarnode:
        def __init__(self, key, size, def_op=None):
            self.key = key
            self._size = size
            self._def_op = def_op

        def getSize(self):
            return self._size

        def getDef(self):
            return self._def_op

        def getHigh(self):
            return None

    class FakeCallOp:
        def __init__(self):
            self._inputs = [
                FakeVarnode("target", 8),
                FakeVarnode("lhs", 4),
                FakeVarnode("rhs", 4),
            ]
            self._output = FakeVarnode("ret", 4, def_op=self)
            self._seqnum = FakeSeqnum(0x401180, 2)

        def getMnemonic(self):
            return "CALL"

        def getNumInputs(self):
            return len(self._inputs)

        def getInput(self, index):
            return self._inputs[index]

        def getOutput(self):
            return self._output

        def getSeqnum(self):
            return self._seqnum

    class FakeStoreOp:
        def __init__(self, call_op):
            self._inputs = [
                FakeVarnode("space", 4),
                FakeVarnode("addr", 8),
                call_op.getOutput(),
            ]
            self._seqnum = FakeSeqnum(0x401190, 3)

        def getMnemonic(self):
            return "STORE"

        def getNumInputs(self):
            return len(self._inputs)

        def getInput(self, index):
            return self._inputs[index]

        def getOutput(self):
            return None

        def getSeqnum(self):
            return self._seqnum

    class FakeBlockInfo:
        def __init__(self, *ops):
            self.pcode_ops = list(ops)

    class FakeConditionTracker:
        def get_all_valid_paths_to_block(self, _block):
            return [[]]

    class FakeTracer:
        def _get_function_name(self, varnode):
            if getattr(varnode, "key", None) == "target":
                return "fc_add"
            return "UNKNOWN_FUNC"

        def trace_varnode(self, varnode, use_cache=False):
            if varnode.key == "addr":
                return Expression.parameter("slot", 0, size=8)
            if varnode.key == "lhs":
                return Expression.parameter("lhs", 1, size=4)
            if varnode.key == "rhs":
                return Expression.parameter("rhs", 2, size=4)
            if varnode.key == "ret":
                return Expression.unknown("call_out_of_scope:fc_add")
            return Expression.constant(0, max(1, varnode.getSize()))

    call_op = FakeCallOp()
    summary = summarize_store_effects(
        [FakeBlockInfo(call_op, FakeStoreOp(call_op))],
        FakeTracer(),
        FakeConditionTracker(),
        [
            _param("slot", size=8, is_signed=False, index=0, storage=_reg_storage("x0", register_name="x0")),
            _param("lhs", size=4, index=1, storage=_reg_storage("x1", size_bytes=4, register_name="w1")),
            _param("rhs", size=4, index=2, storage=_reg_storage("x2", size_bytes=4, register_name="w2")),
        ],
        direct_call_summary=lambda _target_ref, _args: EffectSummary(
            parameter_names=["a", "b"],
            effects=[],
            has_unsupported_call=False,
        ),
        direct_call_expander=lambda _target_ref, args: [
            ExpandedValue(Expression.binary_op("INT_ADD", args[0], args[1]), [])
        ],
        resolve_callee_parameters=lambda _target_ref: [
            _param("a", size=4, index=0, storage=_reg_storage("x0", size_bytes=4, register_name="w0")),
            _param("b", size=4, index=1, storage=_reg_storage("x1", size_bytes=4, register_name="w1")),
        ],
        debug=False,
    )

    assert summary.has_unsupported_call is False
    assert len(summary.effects) == 1
    assert summary.effects[0].location == _loc("slot", 0, 4)
    assert summary.effects[0].value.to_string() == "(lhs + rhs)"
    assert len(summary.call_site_effect_summary_evidence) == 1
    call_effect_evidence = summary.call_site_effect_summary_evidence[0]
    assert call_effect_evidence.summary_status == "complete"
    assert call_effect_evidence.memory_effect_count == 0
    assert call_effect_evidence.has_unsupported_nested_call is False

def test_expression_expander_keeps_concrete_call_arg_when_canonical_candidate_is_unresolved_phi():
    class FakeAddress:
        def __init__(self, offset):
            self._offset = offset

        def getOffset(self):
            return self._offset

        def getAddressSpace(self):
            return self

        def getName(self):
            return "ram"

    class FakeSeqnum:
        def __init__(self, offset, order):
            self._target = FakeAddress(offset)
            self._order = order

        def getTarget(self):
            return self._target

        def getOrder(self):
            return self._order

    class FakeHigh:
        def __init__(self, name: str):
            self._name = name

        def getName(self):
            return self._name

        def getSymbol(self):
            return None

    class FakeVarnode:
        def __init__(self, name, size=4, def_op=None, high=None):
            self.name = name
            self._size = size
            self._def_op = def_op
            self._high = high

        def getDef(self):
            return self._def_op

        def getSize(self):
            return self._size

        def getHigh(self):
            return self._high

    class FakeOutput:
        def __init__(self, size):
            self._size = size

        def getSize(self):
            return self._size

    class FakeAddOp:
        def __init__(self):
            self._inputs = []

        def getMnemonic(self):
            return "INT_ADD"

        def getNumInputs(self):
            return len(self._inputs)

        def getInput(self, index):
            return self._inputs[index]

    class FakeCallOp:
        def __init__(self, inputs):
            self._inputs = inputs
            self._output = FakeOutput(4)
            self._seqnum = FakeSeqnum(0x401040, 12)

        def getMnemonic(self):
            return "CALL"

        def getNumInputs(self):
            return len(self._inputs)

        def getInput(self, index):
            return self._inputs[index]

        def getOutput(self):
            return self._output

        def getSeqnum(self):
            return self._seqnum

    target_varnode = FakeVarnode("callee_addr", size=8)
    unstable_source = FakeVarnode(
        "unstable_arg",
        size=4,
        def_op=FakeAddOp(),
        high=FakeHigh("tmp_w0"),
    )
    call_op = FakeCallOp([target_varnode, unstable_source])

    unresolved_phi = Expression.phi(
        [
            (
                Condition(Expression.binary_op("INT_EQUAL", Expression.parameter("param_1", 0, size=4), Expression.constant(0, 4))),
                Expression.unknown("call_out_of_scope:fc_wrap_add_then_bias"),
            ),
            (
                Condition(Expression.binary_op("INT_NOTEQUAL", Expression.parameter("param_1", 0, size=4), Expression.constant(0, 4))),
                Expression.unknown("call_out_of_scope:fc_bias"),
            ),
        ]
    )

    class FakeTracer:
        debug = False

        def resolve_call_target_ref(self, _varnode, **_kwargs):
            return CallTargetRef.from_name("fc_scale")

        def _get_function_name(self, _varnode):
            return "fc_scale"

        def trace_varnode(self, varnode, depth=0, use_cache=False):
            if varnode is target_varnode:
                return Expression.constant(0x401000, 8)
            if varnode is unstable_source:
                return unresolved_phi
            raise AssertionError(f"unexpected trace: {varnode}")

        def emit_unknown_event(self, **kwargs):
            raise AssertionError(f"call should have been resolved: {kwargs}")

        def _trace_pcode_op(self, *_args, **_kwargs):
            raise AssertionError("recursive tracing fallback should not run")

        def get_all_pcode_ops(self):
            return [call_op]

        def _get_storage_info_from_varnode(self, _varnode):
            return None

    captured = {}

    def resolve_call(target_ref, args):
        captured["target"] = target_ref
        captured["args"] = list(args)
        return [ExpandedValue(Expression.constant(1, 4), [])]

    expander = ExpressionExpander(
        FakeTracer(),
        condition_tracker=None,
        debug=False,
        call_resolver=resolve_call,
        parameters=[
            _param("param_1", size=4, index=0, storage=_reg_storage("a0", size_bytes=4, register_name="a0")),
        ],
        resolve_callee_parameters=lambda _target_ref: [
            _param("value", size=4, index=0, storage=_reg_storage("a0", size_bytes=4, register_name="a0")),
        ],
    )
    expander._expand_input_varnode = lambda varnode, conditions, depth: {
        unstable_source: [ExpandedValue(Expression.parameter("param_1", 0, size=4), [])],
    }[varnode]

    expanded = expander._expand_call_operation(call_op, [], depth=0, output_size=4)

    assert len(expanded) == 1
    assert captured["target"] == CallTargetRef.from_name("fc_scale")
    assert [arg.to_string() for arg in captured["args"]] == ["param_1"]

def test_summarize_store_effects_refuses_hidden_call_operands_without_object_evidence():
    class FakeAddress:
        def __init__(self, offset, space_name="ram"):
            self._offset = offset
            self._space_name = space_name

        def getOffset(self):
            return self._offset

        def getAddressSpace(self):
            return self

        def getName(self):
            return self._space_name

    class FakeSeqnum:
        def __init__(self, offset, order):
            self._target = FakeAddress(offset)
            self._order = order

        def getTarget(self):
            return self._target

        def getOrder(self):
            return self._order

    class FakeVarnode:
        def __init__(self, key, size=4, storage=None):
            self.key = key
            self._size = size
            self.storage = storage

        def getSize(self):
            return self._size

        def getDef(self):
            return None

        def getHigh(self):
            return None

    class FakeCallOp:
        def __init__(self):
            self._inputs = [
                FakeVarnode("target", size=8),
                FakeVarnode("hidden", size=4),
                FakeVarnode("lhs", size=4),
                FakeVarnode("rhs", size=4),
                FakeVarnode("bias", size=4),
            ]
            self._seqnum = FakeSeqnum(0x401100, 10)

        def getMnemonic(self):
            return "CALL"

        def getNumInputs(self):
            return len(self._inputs)

        def getInput(self, index):
            return self._inputs[index]

        def getOutput(self):
            return None

        def getSeqnum(self):
            return self._seqnum

    class FakeBlockInfo:
        def __init__(self, op):
            self.pcode_ops = [op]

    class FakeConditionTracker:
        def get_all_valid_paths_to_block(self, _block):
            return [[]]

    class FakeTracer:
        def __init__(self, op):
            self._op = op

        def _get_function_name(self, _varnode):
            return "callee"

        def get_all_pcode_ops(self):
            return [self._op]

        def _get_storage_info_from_varnode(self, _varnode):
            return None

        def trace_varnode(self, varnode, use_cache=False):
            if varnode.key == "hidden":
                return Expression.binary_op(
                    "INT_SUB",
                    Expression.parameter("param_1", 0, size=4),
                    Expression.parameter("param_2", 1, size=4),
                )
            if varnode.key == "lhs":
                return Expression.parameter("param_1", 0, size=4)
            if varnode.key == "rhs":
                return Expression.parameter("param_2", 1, size=4)
            if varnode.key == "bias":
                return Expression.constant(1, 4)
            return Expression.constant(0x401100, 8)

    captured_args = {}
    call_op = FakeCallOp()

    def _direct_call_summary(_name, args):
        captured_args["args"] = list(args)
        return EffectSummary(parameter_names=["lhs", "rhs", "bias"], effects=[])

    summary = summarize_store_effects(
        [FakeBlockInfo(call_op)],
        FakeTracer(call_op),
        FakeConditionTracker(),
        [
            _param("param_1", size=4, is_signed=False, index=0, storage=_reg_storage("a0", size_bytes=4)),
            _param("param_2", size=4, is_signed=False, index=1, storage=_reg_storage("a1", size_bytes=4)),
            _param("param_3", size=4, is_signed=False, index=2, storage=_reg_storage("a2", size_bytes=4)),
        ],
        direct_call_summary=_direct_call_summary,
        resolve_callee_parameters=lambda _target_ref: [
            _param("lhs", size=4, is_signed=False, index=0, storage=_reg_storage("a0", size_bytes=4)),
            _param("rhs", size=4, is_signed=False, index=1, storage=_reg_storage("a1", size_bytes=4)),
            _param("bias", size=4, is_signed=False, index=2, storage=_reg_storage("a2", size_bytes=4)),
        ],
        debug=False,
    )

    assert summary.effects == []
    assert summary.has_unsupported_call is True
    assert "args" not in captured_args

def test_summarize_store_effects_propagates_phi_argument_branch_conditions_into_effects():
    class FakeAddress:
        def __init__(self, offset):
            self._offset = offset

        def getOffset(self):
            return self._offset

    class FakeSeqnum:
        def __init__(self, offset, order):
            self._target = FakeAddress(offset)
            self._order = order

        def getTarget(self):
            return self._target

        def getOrder(self):
            return self._order

    class FakeVarnode:
        def __init__(self, key, size=4):
            self.key = key
            self._size = size

        def getSize(self):
            return self._size

        def getDef(self):
            return None

        def getHigh(self):
            return None

    class FakeCallOp:
        def __init__(self):
            self._inputs = [
                FakeVarnode("target", size=8),
                FakeVarnode("ptr", size=8),
                FakeVarnode("delta", size=4),
            ]
            self._seqnum = FakeSeqnum(0x401180, 12)

        def getMnemonic(self):
            return "CALL"

        def getNumInputs(self):
            return len(self._inputs)

        def getInput(self, index):
            return self._inputs[index]

        def getOutput(self):
            return None

        def getSeqnum(self):
            return self._seqnum

    class FakeBlockInfo:
        def __init__(self, op):
            self.pcode_ops = [op]

    class FakeConditionTracker:
        def get_all_valid_paths_to_block(self, _block):
            return [[
                Condition(
                    Expression.binary_op(
                        "INT_NOTEQUAL",
                        Expression.parameter("param_1", 0, size=8),
                        Expression.constant(0, size=8),
                    ),
                    False,
                )
            ]]

    class FakeTracer:
        def __init__(self, op):
            self._op = op

        def _get_function_name(self, _varnode):
            return "callee"

        def get_all_pcode_ops(self):
            return [self._op]

        def _get_storage_info_from_varnode(self, _varnode):
            return None

        def trace_varnode(self, varnode, use_cache=False):
            if varnode.key == "ptr":
                return Expression.parameter("param_1", 0, data_type="int *", size=8)
            if varnode.key == "delta":
                return Expression.phi(
                    [
                        (
                            Condition(
                                Expression.binary_op(
                                    "INT_EQUAL",
                                    Expression.binary_op(
                                        "INT_AND",
                                        Expression.parameter("param_2", 1, size=4),
                                        Expression.constant(1, size=4),
                                    ),
                                    Expression.constant(0, size=4),
                                ),
                                False,
                            ),
                            Expression.parameter("param_2", 1, size=4),
                        ),
                        (
                            Condition(
                                Expression.binary_op(
                                    "INT_EQUAL",
                                    Expression.binary_op(
                                        "INT_AND",
                                        Expression.parameter("param_2", 1, size=4),
                                        Expression.constant(1, size=4),
                                    ),
                                    Expression.constant(0, size=4),
                                ),
                                True,
                            ),
                            Expression.unary_op("INT_2COMP", Expression.parameter("param_2", 1, size=4)),
                        ),
                    ]
                )
            return Expression.constant(0x401180, 8)

    call_op = FakeCallOp()

    summary = summarize_store_effects(
        [FakeBlockInfo(call_op)],
        FakeTracer(call_op),
        FakeConditionTracker(),
        [
            _param("param_1", size=8, is_signed=False, index=0, storage=_reg_storage("a0", size_bytes=8)),
            _param("param_2", size=4, is_signed=True, index=1, storage=_reg_storage("a1", size_bytes=4)),
        ],
        direct_call_summary=lambda _target_ref, _args: EffectSummary(
            parameter_names=["ptr", "delta"],
            parameter_refs=[
                LocationBaseRef.parameter("ptr", index=0),
                LocationBaseRef.parameter("delta", index=1),
            ],
            effects=[
                StoreEffect(
                    location=_loc("ptr", 0, 4),
                    value=Expression.binary_op(
                        "INT_ADD",
                        Expression.memory(Expression.parameter("ptr", 0, data_type="int *", size=8), size=4),
                        Expression.parameter("delta", 1, size=4),
                    ),
                    conditions=[],
                    order_key=1,
                ),
            ],
        ),
        resolve_callee_parameters=lambda _target_ref: [
            _param("ptr", size=8, is_signed=False, index=0, storage=_reg_storage("a0", size_bytes=8)),
            _param("delta", size=4, is_signed=True, index=1, storage=_reg_storage("a1", size_bytes=4)),
        ],
        debug=False,
    )

    assert len(summary.effects) == 2
    effect_conditions = {tuple(cond.to_string() for cond in effect.conditions): effect.value.to_string() for effect in summary.effects}
    assert any("((param_2 & 1) == 0)" in " ".join(conds) for conds in effect_conditions)
    assert any("not ((param_2 & 1) == 0)" in " ".join(conds) for conds in effect_conditions)
    assert any(value == "(MEM[param_1] + param_2)" for value in effect_conditions.values())
    assert any(value == "(MEM[param_1] + (-param_2))" for value in effect_conditions.values())

def test_summarize_store_effects_reduces_phi_argument_and_path_conditions_under_active_path():
    class FakeAddress:
        def __init__(self, offset):
            self._offset = offset

        def getOffset(self):
            return self._offset

    class FakeSeqnum:
        def __init__(self, offset, order):
            self._target = FakeAddress(offset)
            self._order = order

        def getTarget(self):
            return self._target

        def getOrder(self):
            return self._order

    class FakeVarnode:
        def __init__(self, key, size=4):
            self.key = key
            self._size = size

        def getSize(self):
            return self._size

        def getDef(self):
            return None

        def getHigh(self):
            return None

    class FakeCallOp:
        def __init__(self):
            self._inputs = [
                FakeVarnode("target", size=8),
                FakeVarnode("ptr", size=8),
                FakeVarnode("delta", size=4),
            ]
            self._seqnum = FakeSeqnum(0x401188, 13)

        def getMnemonic(self):
            return "CALL"

        def getNumInputs(self):
            return len(self._inputs)

        def getInput(self, index):
            return self._inputs[index]

        def getOutput(self):
            return None

        def getSeqnum(self):
            return self._seqnum

    class FakeBlockInfo:
        def __init__(self, op):
            self.pcode_ops = [op]

    phi_counter = Expression.phi(
        [
            (
                None,
                Expression.binary_op(
                    "INT_ADD",
                    Expression.unknown("phi_circular"),
                    Expression.constant(1, size=4),
                ),
            ),
            (
                Condition(
                    Expression.binary_op(
                        "INT_EQUAL",
                        Expression.parameter("param_1", 0, size=8),
                        Expression.constant(0, size=8),
                    ),
                    True,
                ),
                Expression.parameter("param_2", 1, size=4),
            ),
        ]
    )

    class FakeConditionTracker:
        def get_all_valid_paths_to_block(self, _block):
            return [[
                Condition(
                    Expression.binary_op(
                        "INT_NOTEQUAL",
                        Expression.parameter("param_1", 0, size=8),
                        Expression.constant(0, size=8),
                    ),
                    False,
                ),
                Condition(
                    Expression.binary_op(
                        "INT_SLESS",
                        phi_counter,
                        Expression.parameter("param_3", 2, size=4),
                    ),
                    False,
                ),
                Condition(
                    Expression.binary_op(
                        "INT_EQUAL",
                        Expression.binary_op(
                            "INT_AND",
                            phi_counter,
                            Expression.constant(1, size=4),
                        ),
                        Expression.constant(0, size=4),
                    ),
                    False,
                ),
            ]]

    class FakeTracer:
        def __init__(self, op):
            self._op = op

        def _get_function_name(self, _varnode):
            return "callee"

        def get_all_pcode_ops(self):
            return [self._op]

        def _get_storage_info_from_varnode(self, _varnode):
            return None

        def trace_varnode(self, varnode, use_cache=False):
            if varnode.key == "ptr":
                return Expression.parameter("param_1", 0, data_type="int *", size=8)
            if varnode.key == "delta":
                return phi_counter
            return Expression.constant(0x401188, 8)

    call_op = FakeCallOp()
    summary = summarize_store_effects(
        [FakeBlockInfo(call_op)],
        FakeTracer(call_op),
        FakeConditionTracker(),
        [
            _param("param_1", size=8, is_signed=False, index=0, storage=_reg_storage("a0", size_bytes=8)),
            _param("param_2", size=4, is_signed=True, index=1, storage=_reg_storage("a1", size_bytes=4)),
            _param("param_3", size=4, is_signed=True, index=2, storage=_reg_storage("a2", size_bytes=4)),
        ],
        direct_call_summary=lambda _target_ref, _args: EffectSummary(
            parameter_names=["ptr", "delta"],
            parameter_refs=[
                LocationBaseRef.parameter("ptr", index=0),
                LocationBaseRef.parameter("delta", index=1),
            ],
            effects=[
                StoreEffect(
                    location=_loc("ptr", 0, 4),
                    value=Expression.binary_op(
                        "INT_ADD",
                        Expression.memory(Expression.parameter("ptr", 0, data_type="int *", size=8), size=4),
                        Expression.parameter("delta", 1, size=4),
                    ),
                    conditions=[],
                    order_key=1,
                )
            ],
        ),
        resolve_callee_parameters=lambda _target_ref: [
            _param("ptr", size=8, is_signed=False, index=0, storage=_reg_storage("a0", size_bytes=8)),
            _param("delta", size=4, is_signed=True, index=1, storage=_reg_storage("a1", size_bytes=4)),
        ],
        debug=False,
    )

    assert len(summary.effects) == 1
    effect = summary.effects[0]
    assert effect.value.to_string() == "(MEM[param_1] + param_2)"
    cond_strings = [cond.to_string() for cond in effect.conditions]
    assert "(param_1 != 0)" in cond_strings
    assert "(param_2 < param_3)" in cond_strings
    assert "((param_2 & 1) == 0)" in cond_strings

def test_summarize_store_effects_allows_pathless_effect_free_explicit_call():
    class FakeVarnode:
        def __init__(self, key, size):
            self.key = key
            self._size = size

        def getSize(self):
            return self._size

        def getDef(self):
            return None

    class FakeCallOp:
        def __init__(self):
            self._inputs = [
                FakeVarnode("target", 8),
                FakeVarnode("lhs", 4),
                FakeVarnode("rhs", 4),
            ]

        def getMnemonic(self):
            return "CALL"

        def getNumInputs(self):
            return len(self._inputs)

        def getInput(self, index):
            return self._inputs[index]

    class FakeBlockInfo:
        def __init__(self, op):
            self.pcode_ops = [op]

    class FakeConditionTracker:
        def get_all_valid_paths_to_block(self, _block):
            return []

    class FakeTracer:
        def resolve_call_target_ref(self, _varnode, **_kwargs):
            return CallTargetRef.from_name("effect_free")

        def trace_varnode(self, varnode, use_cache=False):
            if varnode.key == "lhs":
                return Expression.parameter("lhs", 0, size=4)
            if varnode.key == "rhs":
                return Expression.parameter("rhs", 1, size=4)
            return Expression.constant(0, max(1, varnode.getSize()))

    call_op = FakeCallOp()
    summary = summarize_store_effects(
        [FakeBlockInfo(call_op)],
        FakeTracer(),
        FakeConditionTracker(),
        [
            _param("lhs", size=4, index=0, storage=_reg_storage("x0", size_bytes=4, register_name="w0")),
            _param("rhs", size=4, index=1, storage=_reg_storage("x1", size_bytes=4, register_name="w1")),
        ],
        direct_call_summary=lambda _target_ref, _args: EffectSummary(
            parameter_names=["lhs", "rhs"],
            effects=[],
            has_unsupported_call=False,
        ),
        resolve_callee_parameters=lambda _target_ref: [
            _param("lhs", size=4, index=0, storage=_reg_storage("x0", size_bytes=4, register_name="w0")),
            _param("rhs", size=4, index=1, storage=_reg_storage("x1", size_bytes=4, register_name="w1")),
        ],
        debug=False,
    )

    assert summary.effects == []
    assert summary.has_unsupported_call is False
    assert summary.incomplete_reasons == ()

def test_summarize_store_effects_keeps_unresolved_scalar_callback_unsupported():
    class FakeVarnode:
        def __init__(self, key, size):
            self.key = key
            self._size = size

        def getSize(self):
            return self._size

    class FakeCallIndOp:
        def __init__(self):
            self._inputs = [
                FakeVarnode("target", 8),
                FakeVarnode("lhs", 4),
                FakeVarnode("rhs", 4),
            ]

        def getMnemonic(self):
            return "CALLIND"

        def getNumInputs(self):
            return len(self._inputs)

        def getInput(self, index):
            return self._inputs[index]

    class FakeBlockInfo:
        def __init__(self, op):
            self.pcode_ops = [op]

    class FakeCoverage:
        status = "complete"
        condition_paths = [[]]

    class FakeConditionTracker:
        def get_path_coverage_to_block(self, _block):
            return FakeCoverage()

    class FakeTracer:
        def resolve_call_target_ref(self, _varnode, **_kwargs):
            return None

        def trace_varnode(self, varnode, use_cache=False):
            if varnode.key == "lhs":
                return Expression.parameter("lhs", 0, size=4)
            if varnode.key == "rhs":
                return Expression.parameter("rhs", 1, size=4)
            return Expression.parameter("callback", 2, size=8)

    summary = summarize_store_effects(
        [FakeBlockInfo(FakeCallIndOp())],
        FakeTracer(),
        FakeConditionTracker(),
        [
            _param("lhs", size=4, index=0, storage=_reg_storage("w0", size_bytes=4, register_name="w0"), data_type="int"),
            _param("rhs", size=4, index=1, storage=_reg_storage("w1", size_bytes=4, register_name="w1"), data_type="int"),
        ],
        direct_call_summary=lambda _target_ref, _args: None,
        debug=False,
    )

    assert summary.effects == []
    assert summary.has_unsupported_call is True
    assert summary.incomplete_reasons == ()

def test_summarize_store_effects_keeps_unresolved_pointer_callback_effect_unsupported():
    class FakeVarnode:
        def __init__(self, key, size):
            self.key = key
            self._size = size

        def getSize(self):
            return self._size

    class FakeCallIndOp:
        def __init__(self):
            self._inputs = [
                FakeVarnode("target", 8),
                FakeVarnode("ptr", 8),
            ]

        def getMnemonic(self):
            return "CALLIND"

        def getNumInputs(self):
            return len(self._inputs)

        def getInput(self, index):
            return self._inputs[index]

    class FakeBlockInfo:
        def __init__(self, op):
            self.pcode_ops = [op]

    class FakeCoverage:
        status = "complete"
        condition_paths = [[]]

    class FakeConditionTracker:
        def get_path_coverage_to_block(self, _block):
            return FakeCoverage()

    class FakeTracer:
        def resolve_call_target_ref(self, _varnode, **_kwargs):
            return None

        def trace_varnode(self, varnode, use_cache=False):
            if varnode.key == "ptr":
                return Expression.parameter("ptr", 0, size=8)
            return Expression.parameter("callback", 1, size=8)

    ptr_param = _param(
        "ptr",
        size=8,
        index=0,
        storage=_reg_storage("x0", register_name="x0"),
    )
    ptr_param["data_type_obj"] = resolve_mock_data_type("int *")

    summary = summarize_store_effects(
        [FakeBlockInfo(FakeCallIndOp())],
        FakeTracer(),
        FakeConditionTracker(),
        [ptr_param],
        direct_call_summary=lambda _target_ref, _args: None,
        debug=False,
    )

    assert summary.effects == []
    assert summary.has_unsupported_call is True
    assert summary.incomplete_reasons == ()

def test_summarize_store_effects_keeps_data_type_string_pointer_callback_unsupported():
    summary = _summarize_unresolved_single_parameter_call(
        _param(
            "ptr",
            size=8,
            index=0,
            storage=_reg_storage("x0", register_name="x0"),
            data_type="int *",
        )
    )

    assert summary.effects == []
    assert summary.has_unsupported_call is True
    assert summary.incomplete_reasons == ()

def test_summarize_store_effects_keeps_undefined_address_sized_callback_unsupported():
    summary = _summarize_unresolved_single_parameter_call(
        _param(
            "maybe_ptr",
            size=8,
            index=0,
            storage=_reg_storage("x0", register_name="x0"),
            data_type="undefined8",
        )
    )

    assert summary.effects == []
    assert summary.has_unsupported_call is True
    assert summary.incomplete_reasons == ()

def test_summarize_store_effects_keeps_missing_scalar_only_callee_summary_unsupported():
    class FakeVarnode:
        def __init__(self, key, size):
            self.key = key
            self._size = size

        def getSize(self):
            return self._size

    class FakeCallOp:
        def __init__(self):
            self._inputs = [
                FakeVarnode("target", 8),
                FakeVarnode("lhs", 4),
                FakeVarnode("rhs", 4),
            ]

        def getMnemonic(self):
            return "CALL"

        def getNumInputs(self):
            return len(self._inputs)

        def getInput(self, index):
            return self._inputs[index]

    class FakeBlockInfo:
        def __init__(self, op):
            self.pcode_ops = [op]

    class FakeCoverage:
        status = "complete"
        condition_paths = [[]]

    class FakeConditionTracker:
        def get_path_coverage_to_block(self, _block):
            return FakeCoverage()

    class FakeTracer:
        def resolve_call_target_ref(self, _varnode, **_kwargs):
            return CallTargetRef.from_name("missing_scalar_helper")

        def trace_varnode(self, varnode, use_cache=False):
            if varnode.key == "lhs":
                return Expression.parameter("lhs", 0, size=4)
            if varnode.key == "rhs":
                return Expression.parameter("rhs", 1, size=4)
            return Expression.constant(0, max(1, varnode.getSize()))

    summary = summarize_store_effects(
        [FakeBlockInfo(FakeCallOp())],
        FakeTracer(),
        FakeConditionTracker(),
        [
            _param("lhs", size=8, index=0, storage=_reg_storage("x0", register_name="x0"), data_type="undefined8"),
            _param("rhs", size=8, index=1, storage=_reg_storage("x1", register_name="x1"), data_type="undefined8"),
        ],
        direct_call_summary=lambda _target_ref, _args: None,
        resolve_callee_parameters=lambda _target_ref: [
            _param("lhs", size=4, index=0, storage=_reg_storage("w0", size_bytes=4, register_name="w0"), data_type="int"),
            _param("rhs", size=4, index=1, storage=_reg_storage("w1", size_bytes=4, register_name="w1"), data_type="int"),
        ],
        debug=False,
    )

    assert summary.effects == []
    assert summary.has_unsupported_call is True
    assert summary.incomplete_reasons == ()

def test_summarize_store_effects_keeps_zero_arg_missing_callee_summary_unsupported():
    class FakeVarnode:
        def __init__(self, key, size):
            self.key = key
            self._size = size

        def getSize(self):
            return self._size

    class FakeCallOp:
        def __init__(self):
            self._inputs = [FakeVarnode("target", 8)]

        def getMnemonic(self):
            return "CALL"

        def getNumInputs(self):
            return len(self._inputs)

        def getInput(self, index):
            return self._inputs[index]

    class FakeBlockInfo:
        def __init__(self, op):
            self.pcode_ops = [op]

    class FakeCoverage:
        status = "complete"
        condition_paths = [[]]

    class FakeConditionTracker:
        def get_path_coverage_to_block(self, _block):
            return FakeCoverage()

    class FakeTracer:
        def resolve_call_target_ref(self, _varnode, **_kwargs):
            return CallTargetRef.from_name("missing_zero_arg_helper")

        def trace_varnode(self, varnode, use_cache=False):
            return Expression.constant(0, max(1, varnode.getSize()))

    summary = summarize_store_effects(
        [FakeBlockInfo(FakeCallOp())],
        FakeTracer(),
        FakeConditionTracker(),
        [],
        direct_call_summary=lambda _target_ref, _args: None,
        resolve_callee_parameters=lambda _target_ref: [],
        debug=False,
    )

    assert summary.effects == []
    assert summary.has_unsupported_call is True
    assert summary.incomplete_reasons == ()

def test_summarize_store_effects_does_not_propagate_scalar_only_unsupported_callee():
    class FakeVarnode:
        def __init__(self, key, size):
            self.key = key
            self._size = size

        def getSize(self):
            return self._size

    class FakeCallOp:
        def __init__(self):
            self._inputs = [
                FakeVarnode("target", 8),
                FakeVarnode("lhs", 4),
                FakeVarnode("rhs", 4),
            ]

        def getMnemonic(self):
            return "CALL"

        def getNumInputs(self):
            return len(self._inputs)

        def getInput(self, index):
            return self._inputs[index]

    class FakeBlockInfo:
        def __init__(self, op):
            self.pcode_ops = [op]

    class FakeCoverage:
        status = "complete"
        condition_paths = [[]]

    class FakeConditionTracker:
        def get_path_coverage_to_block(self, _block):
            return FakeCoverage()

    class FakeTracer:
        def resolve_call_target_ref(self, _varnode, **_kwargs):
            return CallTargetRef.from_name("scalar_callback_wrapper")

        def trace_varnode(self, varnode, use_cache=False):
            if varnode.key == "lhs":
                return Expression.parameter("lhs", 0, size=4)
            if varnode.key == "rhs":
                return Expression.parameter("rhs", 1, size=4)
            return Expression.constant(0, max(1, varnode.getSize()))

    summary = summarize_store_effects(
        [FakeBlockInfo(FakeCallOp())],
        FakeTracer(),
        FakeConditionTracker(),
        [
            _param("lhs", size=8, index=0, storage=_reg_storage("x0", register_name="x0"), data_type="undefined8"),
            _param("rhs", size=8, index=1, storage=_reg_storage("x1", register_name="x1"), data_type="undefined8"),
        ],
        direct_call_summary=lambda _target_ref, _args: EffectSummary(
            parameter_names=["lhs", "rhs"],
            effects=[],
            has_unsupported_call=True,
        ),
        resolve_callee_parameters=lambda _target_ref: [
            _param("lhs", size=4, index=0, storage=_reg_storage("w0", size_bytes=4, register_name="w0"), data_type="int"),
            _param("rhs", size=4, index=1, storage=_reg_storage("w1", size_bytes=4, register_name="w1"), data_type="int"),
        ],
        debug=False,
    )

    assert summary.effects == []
    assert summary.has_unsupported_call is False
    assert summary.incomplete_reasons == ()

def test_recoverable_partial_call_summary_does_not_become_unsupported_blocker():
    class FakeVarnode:
        def __init__(self, key, size):
            self.key = key
            self._size = size

        def getSize(self):
            return self._size

    class FakeCallOp:
        def __init__(self):
            self._inputs = [
                FakeVarnode("target", 8),
                FakeVarnode("lhs", 4),
            ]

        def getMnemonic(self):
            return "CALL"

        def getNumInputs(self):
            return len(self._inputs)

        def getInput(self, index):
            return self._inputs[index]

    class FakeBlockInfo:
        def __init__(self, op):
            self.pcode_ops = [op]

    class FakeCoverage:
        status = "complete"
        condition_paths = [[]]

    class FakeConditionTracker:
        def get_path_coverage_to_block(self, _block):
            return FakeCoverage()

    class FakeTracer:
        def resolve_call_target_ref(self, _varnode, **_kwargs):
            return CallTargetRef.from_name("effect_free_callee")

        def trace_varnode(self, varnode, use_cache=False):
            if varnode.key == "lhs":
                return Expression.parameter("lhs", 0, size=4)
            return Expression.constant(0, max(1, varnode.getSize()))

    captured_args = []

    def direct_call_summary(_target_ref, args):
        captured_args.append(tuple(args))
        return EffectSummary(parameter_names=["lhs", "rhs"], effects=[])

    summary = summarize_store_effects(
        [FakeBlockInfo(FakeCallOp())],
        FakeTracer(),
        FakeConditionTracker(),
        [
            _param("lhs", size=4, index=0, storage=_reg_storage("w0", size_bytes=4, register_name="w0")),
        ],
        direct_call_summary=direct_call_summary,
        resolve_callee_parameters=lambda _target_ref: [
            _param("lhs", size=4, index=0, storage=_reg_storage("w0", size_bytes=4, register_name="w0")),
            _param("rhs", size=4, index=1, storage=_reg_storage("w1", size_bytes=4, register_name="w1")),
        ],
        debug=False,
    )
    analysis = FunctionReturnAnalysis(
        function_name="caller",
        entry_point="0x1000",
        returns=[],
        parameters=[_param("lhs", size=4, index=0)],
        effect_summary=summary,
    )

    assert len(captured_args) == 1
    assert len(captured_args[0]) == 1
    assert summary.has_unsupported_call is False
    assert summary.incomplete_reasons == ()
    assert "unsupported_call_effect_summary" not in analysis.get_decisive_sat_unsafety_reasons()
    assert "unsupported_call_effect_summary" not in analysis.get_equivalence_blocking_unsafety_reasons()

def test_summarize_store_effects_rejects_nested_incomplete_effect_free_callee():
    class FakeVarnode:
        def __init__(self, key, size):
            self.key = key
            self._size = size

        def getSize(self):
            return self._size

    class FakeCallOp:
        def __init__(self):
            self._inputs = [
                FakeVarnode("target", 8),
                FakeVarnode("lhs", 4),
            ]

        def getMnemonic(self):
            return "CALL"

        def getNumInputs(self):
            return len(self._inputs)

        def getInput(self, index):
            return self._inputs[index]

    class FakeBlockInfo:
        def __init__(self, op):
            self.pcode_ops = [op]

    class FakeCoverage:
        status = "complete"
        condition_paths = [[]]

    class FakeConditionTracker:
        def get_path_coverage_to_block(self, _block):
            return FakeCoverage()

    class FakeTracer:
        def resolve_call_target_ref(self, _varnode, **_kwargs):
            return CallTargetRef.from_name("incomplete_helper")

        def trace_varnode(self, varnode, use_cache=False):
            if varnode.key == "lhs":
                return Expression.parameter("lhs", 0, size=4)
            return Expression.constant(0, max(1, varnode.getSize()))

    summary = summarize_store_effects(
        [FakeBlockInfo(FakeCallOp())],
        FakeTracer(),
        FakeConditionTracker(),
        [
            _param("lhs", size=4, index=0, storage=_reg_storage("w0", size_bytes=4, register_name="w0"), data_type="int"),
        ],
        direct_call_summary=lambda _target_ref, _args: EffectSummary(
            parameter_names=["lhs"],
            effects=[],
            has_unsupported_call=False,
            incomplete_reasons=("effect_summary_path_coverage_incomplete",),
        ),
        resolve_callee_parameters=lambda _target_ref: [
            _param("lhs", size=4, index=0, storage=_reg_storage("w0", size_bytes=4, register_name="w0"), data_type="int"),
        ],
        debug=False,
    )

    assert summary.effects == []
    assert summary.has_unsupported_call is True
    assert summary.incomplete_reasons == ()

def test_summarize_store_effects_keeps_pathless_side_effect_call_incomplete():
    class FakeVarnode:
        def __init__(self, key, size):
            self.key = key
            self._size = size

        def getSize(self):
            return self._size

    class FakeCallOp:
        def __init__(self):
            self._inputs = [
                FakeVarnode("target", 8),
                FakeVarnode("ptr", 8),
            ]

        def getMnemonic(self):
            return "CALL"

        def getNumInputs(self):
            return len(self._inputs)

        def getInput(self, index):
            return self._inputs[index]

    class FakeBlockInfo:
        def __init__(self, op):
            self.pcode_ops = [op]

    class FakeConditionTracker:
        def get_all_valid_paths_to_block(self, _block):
            return []

    class FakeTracer:
        def resolve_call_target_ref(self, _varnode, **_kwargs):
            return CallTargetRef.from_name("writer")

        def trace_varnode(self, varnode, use_cache=False):
            if varnode.key == "ptr":
                return Expression.parameter("ptr", 0, size=8)
            return Expression.constant(0, max(1, varnode.getSize()))

    call_op = FakeCallOp()
    summary = summarize_store_effects(
        [FakeBlockInfo(call_op)],
        FakeTracer(),
        FakeConditionTracker(),
        [_param("ptr", size=8, index=0, storage=_reg_storage("x0", register_name="x0"))],
        direct_call_summary=lambda _target_ref, _args: EffectSummary(
            parameter_names=["ptr"],
            effects=[
                StoreEffect(
                    location=_loc("ptr", 0, 4),
                    value=Expression.constant(7, 4),
                    conditions=[],
                    order_key=1,
                )
            ],
        ),
        resolve_callee_parameters=lambda _target_ref: [
            _param("ptr", size=8, index=0, storage=_reg_storage("x0", register_name="x0")),
        ],
        debug=False,
    )

    assert summary.effects == []
    assert summary.has_unsupported_call is True
    assert summary.incomplete_reasons == ("effect_summary_path_coverage_incomplete",)
