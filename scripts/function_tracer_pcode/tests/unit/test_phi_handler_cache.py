# -*- coding: utf-8 -*-
"""PhiHandler caching regressions."""

from scripts.function_tracer_pcode.analysis.phi_resolver import PhiHandler
from scripts.function_tracer_pcode.model import Expression


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


class _FakeTracer:
    def __init__(self):
        self.debug = False
        self.calls = 0

    def _get_stable_op_key(self, op):
        return op._stable_key

    def trace_varnode(self, varnode, depth=0, use_cache=False):
        self.calls += 1
        return Expression.variable(f"v_{varnode.getOffset()}", size=varnode.getSize())

    def emit_unknown_event(self, **_kwargs):
        return None


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
