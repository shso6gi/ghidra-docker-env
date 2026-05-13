# -*- coding: utf-8 -*-
"""PhiHandler caching regressions."""

from scripts.function_tracer_pcode.analysis.phi_resolver import PhiHandler
from scripts.function_tracer_pcode.model import Condition, Expression


class _FakeAddressSpace:
    def __init__(self, name: str):
        self._name = name

    def getName(self):
        return self._name


class _FakeAddress:
    def __init__(self, space_name: str):
        self._space = _FakeAddressSpace(space_name)

    def getAddressSpace(self):
        return self._space


class _FakeHigh:
    def __init__(self, name: str):
        self._name = name

    def getName(self):
        return self._name


class _FakeVarnode:
    def __init__(self, space: str, offset: int, size: int, name: str, def_op=None):
        self._address = _FakeAddress(space)
        self._offset = offset
        self._size = size
        self._high = _FakeHigh(name)
        self._def = def_op

    def getAddress(self):
        return self._address

    def getOffset(self):
        return self._offset

    def getSize(self):
        return self._size

    def getHigh(self):
        return self._high

    def getDef(self):
        return self._def


class _FakeBlock:
    def __init__(self, index: int):
        self._index = index
        self._ins = []

    def getIndex(self):
        return self._index

    def getInSize(self):
        return len(self._ins)

    def getIn(self, index: int):
        return self._ins[index]

    def getOutSize(self):
        return 0


class _FakeBlockInfo:
    def __init__(self, block):
        self.block = block

    def has_conditional_branch(self):
        return False


class _FakeConditionTracker:
    def get_block_by_hash(self, block):
        return _FakeBlockInfo(block)

    def get_path_conditions_to_block(self, _block_info):
        return []

    def get_all_valid_paths_to_block(self, _block_info):
        return [[]]


class _FakeMultiequal:
    def __init__(self, inputs, output, parent, stable_key: str):
        self._inputs = inputs
        self._output = output
        self._parent = parent
        self._stable_key = stable_key

    def getNumInputs(self):
        return len(self._inputs)

    def getInput(self, index: int):
        return self._inputs[index]

    def getOutput(self):
        return self._output

    def getParent(self):
        return self._parent

    def getMnemonic(self):
        return "MULTIEQUAL"


class _FakeOp:
    def __init__(self, mnemonic: str, inputs, output=None, stable_key: str = "op"):
        self._mnemonic = mnemonic
        self._inputs = inputs
        self._output = output
        self._stable_key = stable_key

    def getMnemonic(self):
        return self._mnemonic

    def getNumInputs(self):
        return len(self._inputs)

    def getInput(self, index: int):
        return self._inputs[index]

    def getOutput(self):
        return self._output

    def getOpcode(self):
        return None


class _FakeTracer:
    def __init__(self):
        self.debug = False
        self.calls = 0

    def trace_varnode(self, varnode, depth=0, use_cache=False):
        self.calls += 1
        return Expression.variable(f"v_{varnode.getOffset()}", size=varnode.getSize())

    def emit_unknown_event(self, **_kwargs):
        return None


def _eq_param(value: int) -> Condition:
    param = Expression.parameter("param_1", size=4)
    return Condition(
        Expression.binary_op("INT_EQUAL", param, Expression.constant(value, 4)),
        False,
    )


def test_phi_handler_reuses_cached_multiequal_expansion():
    tracer = _FakeTracer()
    tracker = _FakeConditionTracker()
    handler = PhiHandler(tracer, tracker)

    in_block_0 = _FakeBlock(10)
    in_block_1 = _FakeBlock(11)
    phi_block = _FakeBlock(12)
    phi_block._ins = [in_block_0, in_block_1]

    output = _FakeVarnode("register", 0x5000, 8, "out")
    input_a = _FakeVarnode("register", 0x5008, 8, "a")
    input_b = _FakeVarnode("register", 0x5010, 8, "b")
    multiequal = _FakeMultiequal([input_a, input_b], output, phi_block, "phi:test")

    first = handler.expand_multiequal(multiequal, [], 0)
    second = handler.expand_multiequal(multiequal, [], 0)

    assert len(first) == 2
    assert len(second) == 2
    assert tracer.calls == 2


def test_phi_handler_uses_alternative_valid_path_when_first_path_contradicts():
    class _TrackerWithFallbackPath:
        def __init__(self, bad_condition, good_condition):
            self.bad_condition = bad_condition
            self.good_condition = good_condition

        def get_block_by_hash(self, block):
            return _FakeBlockInfo(block)

        def get_path_conditions_to_block(self, _block_info):
            return [self.bad_condition]

        def get_all_valid_paths_to_block(self, _block_info):
            return [[self.bad_condition], [self.good_condition]]

    tracer = _FakeTracer()
    param = Expression.parameter("param_1", size=4)
    zero = Expression.constant(0, 4)
    nonzero = Condition(Expression.binary_op("INT_NOTEQUAL", param, zero), False)
    zero_only = Condition(Expression.binary_op("INT_NOTEQUAL", param, zero), True)

    handler = PhiHandler(tracer, _TrackerWithFallbackPath(zero_only, nonzero))

    in_block = _FakeBlock(10)
    phi_block = _FakeBlock(12)
    phi_block._ins = [in_block]

    output = _FakeVarnode("register", 0x5000, 4, "out")
    input_a = _FakeVarnode("register", 0x5008, 4, "a")
    multiequal = _FakeMultiequal([input_a], output, phi_block, "phi:path-fallback")

    expanded = handler.expand_multiequal(multiequal, [nonzero], 0)

    assert len(expanded) == 1
    assert expanded[0].value.to_string() == "v_20488"


def test_phi_handler_passes_active_conditions_to_nested_multiequal_inputs():
    class _PathAwareTracker:
        def __init__(self, cond_a, cond_b):
            self.cond_a = cond_a
            self.cond_b = cond_b

        def get_block_by_hash(self, block):
            return _FakeBlockInfo(block)

        def get_path_conditions_to_block(self, _block_info):
            return []

        def get_all_valid_paths_to_block(self, block_info):
            if block_info.block.getIndex() == 10:
                return [[self.cond_a]]
            if block_info.block.getIndex() == 11:
                return [[self.cond_b]]
            return [[]]

    cond_a = _eq_param(1)
    cond_b = _eq_param(2)
    tracer = _FakeTracer()
    handler = PhiHandler(tracer, _PathAwareTracker(cond_a, cond_b))

    in_block_a = _FakeBlock(10)
    in_block_b = _FakeBlock(11)
    phi_block = _FakeBlock(12)
    phi_block._ins = [in_block_a, in_block_b]

    output = _FakeVarnode("register", 0x5000, 4, "out")
    input_a = _FakeVarnode("register", 0x5008, 4, "a")
    input_b = _FakeVarnode("register", 0x5010, 4, "b")
    multiequal = _FakeMultiequal([input_a, input_b], output, phi_block, "phi:nested")
    phi_output = _FakeVarnode("register", 0x5000, 4, "out", def_op=multiequal)
    add_output = _FakeVarnode("register", 0x5018, 4, "sum")
    one = _FakeVarnode("const", 1, 4, "one")
    add_op = _FakeOp("INT_ADD", [phi_output, one], add_output, "op:add")

    expanded = handler._trace_operation_with_phi(add_op, [cond_a], 0)

    assert len(expanded) == 1
    assert "v_20488" in expanded[0].value.to_string()
    assert "v_20496" not in expanded[0].value.to_string()
