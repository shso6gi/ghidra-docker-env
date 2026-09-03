# -*- coding: utf-8 -*-
"""PhiHandler caching regressions."""

from scripts.function_tracer_pcode.analysis.phi_resolver import ExpandedBranch, PhiHandler
from scripts.function_tracer_pcode.core import Condition, Expression, PcodeOpRef


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
        self.unknown_events = []

    def trace_varnode(self, varnode, depth=0, use_cache=False):
        self.calls += 1
        return Expression.variable(f"v_{varnode.getOffset()}", size=varnode.getSize())

    def emit_unknown_event(self, **kwargs):
        self.unknown_events.append(kwargs)
        return None


class _FakeTracerWithoutUnknownEvents:
    debug = False


class _ContextualTracer(_FakeTracerWithoutUnknownEvents):
    def __init__(self, binary_id: str):
        self.debug = False
        self.binary_id = binary_id

    def _make_pcode_op_ref(self, pcode_op):
        return PcodeOpRef(
            binary_id=self.binary_id,
            function_entry_space="ram",
            function_entry_offset=0x1000,
            target_space="ram",
            target_offset=0x1010,
            seq_time=23,
            seq_order=7,
            opcode=27,
            local_op_ordinal=1,
            mnemonic=getattr(pcode_op, "getMnemonic", lambda: "INT_ADD")(),
        )


class _StableOrigin:
    def __init__(self, key):
        self._key = key

    def stable_key(self):
        return self._key


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


def test_phi_handler_returns_unknown_when_combined_branch_budget_is_exceeded():
    tracer = _FakeTracer()
    handler = PhiHandler(tracer, _FakeConditionTracker())
    handler._combined_branch_limit = 4
    left = [
        ExpandedBranch([], Expression.constant(value, size=4))
        for value in range(3)
    ]
    right = [
        ExpandedBranch([], Expression.constant(value + 10, size=4))
        for value in range(3)
    ]

    result = handler._combine_expansions(
        "INT_ADD",
        [left, right],
        [],
        output_size=4,
    )

    assert len(result) == 1
    assert result[0].value.name == "phi_expansion_budget_exceeded"
    assert result[0].value.size == 4
    assert tracer.unknown_events[-1]["reason"] == "phi_expansion_budget_exceeded"


def test_phi_handler_budget_unknown_uses_origin_specific_smt_symbol():
    handler = PhiHandler(_FakeTracerWithoutUnknownEvents(), _FakeConditionTracker())
    handler._combined_branch_limit = 1
    left = [ExpandedBranch([], Expression.constant(1, size=4))]
    right = [
        ExpandedBranch([], Expression.constant(2, size=4)),
        ExpandedBranch([], Expression.constant(3, size=4)),
    ]

    first = handler._combine_expansions(
        "INT_ADD",
        [left, right],
        [],
        output_size=4,
        origin_ref=_StableOrigin(("phi_budget_site", "left")),
    )[0].value
    second = handler._combine_expansions(
        "INT_ADD",
        [left, right],
        [],
        output_size=4,
        origin_ref=_StableOrigin(("phi_budget_site", "right")),
    )[0].value

    assert first.name == "phi_expansion_budget_exceeded"
    assert second.name == "phi_expansion_budget_exceeded"
    assert first.to_smt() != second.to_smt()


def test_phi_handler_budget_origin_uses_tracer_binary_context_for_smt_symbol():
    left_handler = PhiHandler(_ContextualTracer("BLEFT"), _FakeConditionTracker())
    right_handler = PhiHandler(_ContextualTracer("BRIGHT"), _FakeConditionTracker())
    left_handler._combined_branch_limit = 1
    right_handler._combined_branch_limit = 1
    left = [ExpandedBranch([], Expression.constant(1, size=4))]
    right = [
        ExpandedBranch([], Expression.constant(2, size=4)),
        ExpandedBranch([], Expression.constant(3, size=4)),
    ]
    same_surface_op = _FakeOp(
        "INT_ADD",
        [],
        output=_FakeVarnode("register", 0x5000, 4, "out"),
        stable_key="same-surface",
    )

    left_value = left_handler._combine_expansions(
        "INT_ADD",
        [left, right],
        [],
        output_size=4,
        origin_ref=left_handler._phi_expansion_budget_origin(
            "INT_ADD",
            opcode=None,
            pcode_op=same_surface_op,
            base_conditions=[],
            output_size=4,
        ),
    )[0].value
    right_value = right_handler._combine_expansions(
        "INT_ADD",
        [left, right],
        [],
        output_size=4,
        origin_ref=right_handler._phi_expansion_budget_origin(
            "INT_ADD",
            opcode=None,
            pcode_op=same_surface_op,
            base_conditions=[],
            output_size=4,
        ),
    )[0].value

    assert left_value.to_smt() != right_value.to_smt()


def test_phi_handler_budget_unknown_does_not_require_unknown_event_hook():
    handler = PhiHandler(_FakeTracerWithoutUnknownEvents(), _FakeConditionTracker())
    handler._combined_branch_limit = 1
    left = [ExpandedBranch([], Expression.constant(1, size=4))]
    right = [
        ExpandedBranch([], Expression.constant(2, size=4)),
        ExpandedBranch([], Expression.constant(3, size=4)),
    ]

    result = handler._combine_expansions(
        "INT_ADD",
        [left, right],
        [],
        output_size=4,
    )

    assert len(result) == 1
    assert result[0].value.name == "phi_expansion_budget_exceeded"
