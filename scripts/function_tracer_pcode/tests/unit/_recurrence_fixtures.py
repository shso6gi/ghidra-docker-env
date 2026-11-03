from dataclasses import replace

from typing import Optional

from unittest.mock import Mock

from scripts.function_tracer_pcode.analysis.recurrence.summarizer import (
    CountedLoopAccumulator,
    CountedLoopGuard,
    CountedLoopInduction,
    CountedLoopUpdateCase,
    ReadonlyRoundedCountCandidate,
    ResidueLoopCase,
    StateTransitionLoopModel,
    StructuralRecurrenceSummarizer,
)

from scripts.function_tracer_pcode.analysis import ReturnAnalyzer

from scripts.function_tracer_pcode.analysis.condition import ConditionSimplifier

from scripts.function_tracer_pcode.analysis.returns.summary_returns import (
    _summary_transition_evidence_key,
    _transition_evidence_has_required_parts,
)

from scripts.function_tracer_pcode.analysis.tracer import PcodeTracer

from scripts.function_tracer_pcode.analysis.effects.summary import (
    CanonicalLocation,
    EffectSummary,
    StoreEffect,
)

from scripts.function_tracer_pcode.core import (
    COUNTED_LOOP_SUM_OPCODE,
    COUNTED_STATE_TRANSITION_VALUE_OPCODE,
    READONLY_SUM_OPCODE,
    CallTargetRef,
    Condition,
    CountedStateTransitionLoopSummaryRef,
    CountedLoopSummaryRef,
    Expression,
    ExpressionType,
    FunctionReturnAnalysis,
    LoopTermDescriptorRef,
    LoopBodyEffectRef,
    LoopSideEffectProfileRef,
    LoopSummaryRef,
    LocationBaseRef,
    PcodeOpRef,
    ReductionAccumulatorProof,
    ReadonlyReductionTermRef,
    ReturnInfo,
    ReadonlyReductionRef,
    ReadonlyReductionWitness,
    STATE_TRANSITION_LOOP_COUNT_OPCODE,
    StorageInfo,
    StateTransitionLoopSummaryRef,
    UnknownValueRef,
    loop_summary_method_b_key,
)

from scripts.function_tracer_pcode.proof.formula.returns import expression_has_unresolved_value

from scripts.function_tracer_pcode.core.render_smt import expression_to_smt

from scripts.function_tracer_pcode.tests.conftest import create_mock_analysis

def _param(name: str = "param_1", size: int = 4) -> Expression:
    index = 0
    if name.startswith("param_"):
        try:
            index = max(0, int(name.split("_", 1)[1]) - 1)
        except ValueError:
            index = 0
    return Expression.parameter(name, index=index, data_type="int", size=size)

def _readonly_accumulator_proof(
    *,
    base_ref: LocationBaseRef,
    count_expr: Expression,
    stride: int,
    element_size: int,
    result_size: int = 4,
    start_offset: int = 0,
    start_index: int = 0,
    index_step: int = 1,
    index_scale: Optional[int] = None,
    seed_terms=(),
    lane_terms=(),
    witnesses=(),
    return_op_refs=(),
    return_value_op_refs=(),
    return_region_value_proven: bool = True,
    source: str = "recurrence_summary",
) -> ReductionAccumulatorProof:
    return ReductionAccumulatorProof(
        reduction_kind="memory_sum",
        pointer_base_ref=base_ref,
        count_parameter_name=getattr(count_expr, "name", None) or "count",
        count_parameter_index=getattr(count_expr, "value", None),
        limit_expr=count_expr,
        result_size=result_size,
        stride=stride,
        element_size=element_size,
        start_offset=start_offset,
        start_index=start_index,
        index_step=index_step,
        index_scale=stride if index_scale is None else index_scale,
        seed_terms=tuple(seed_terms or ()),
        lane_terms=tuple(lane_terms or ()),
        loop_body_witnesses=tuple(witnesses or ()),
        return_op_refs=tuple(return_op_refs or ()),
        return_value_op_refs=tuple(return_value_op_refs or ()),
        return_region_value_proven=bool(return_region_value_proven),
        source=source,
    )

def _const(value: int, size: int = 4) -> Expression:
    return Expression.constant(value, size)

def _cond(operator: str, left: Expression, right: Expression, negated: bool = False) -> Condition:
    return Condition(Expression.binary_op(operator, left, right), negated=negated)

class _Phase1FakeHighIterator:
    def __init__(self, ops):
        self._ops = list(ops)
        self._index = 0

    def hasNext(self):
        return self._index < len(self._ops)

    def next(self):
        op = self._ops[self._index]
        self._index += 1
        return op

class _Phase1FakePcodeOp:
    def __init__(self, mnemonic):
        self._mnemonic = mnemonic

    def getMnemonic(self):
        return self._mnemonic

class _Phase1FakeHighBlock:
    def __init__(self, mnemonics):
        self._ops = [_Phase1FakePcodeOp(mnemonic) for mnemonic in mnemonics]

    def getIterator(self):
        return _Phase1FakeHighIterator(self._ops)

class _Phase1FakeHighFunction:
    def __init__(self, blocks):
        self._blocks = [_Phase1FakeHighBlock(block) for block in blocks]

    def getBasicBlocks(self):
        return list(self._blocks)

class _Phase1BrokenIteratorAfterSafeOp:
    def __init__(self):
        self._index = 0

    def hasNext(self):
        if self._index == 0:
            return True
        raise RuntimeError("iterator failed after safe op")

    def next(self):
        self._index += 1
        return _Phase1FakePcodeOp("COPY")

class _Phase1BrokenInstruction:
    def getPcode(self):
        return _Phase1BrokenIteratorAfterSafeOp()

class _Phase1FakeInstruction:
    def __init__(self, mnemonics, flows=None, fallthrough=None):
        self._ops = [_Phase1FakePcodeOp(mnemonic) for mnemonic in mnemonics]
        self._flows = tuple(flows or ())
        self._fallthrough = fallthrough

    def getPcode(self):
        return list(self._ops)

    def getFlows(self):
        return self._flows

    def getFallThrough(self):
        return self._fallthrough

class _Phase1FakeAddress:
    def __init__(self, offset):
        self._offset = int(offset)

    def getOffset(self):
        return self._offset

class _Phase1FakeBody:
    def __init__(self, start=0x1000, end=0x10FF):
        self._start = _Phase1FakeAddress(start)
        self._end = _Phase1FakeAddress(end)

    def contains(self, target):
        return self._start.getOffset() <= target.getOffset() <= self._end.getOffset()

    def getMinAddress(self):
        return self._start

    def getMaxAddress(self):
        return self._end

class _Phase1FakeListing:
    def __init__(self, instructions):
        self._instructions = list(instructions)

    def getInstructions(self, _body, _forward=True):
        return list(self._instructions)

class _Phase1FakeProgram:
    def __init__(self, instructions):
        self._listing = _Phase1FakeListing(instructions)

    def getListing(self):
        return self._listing

class _Phase1FakeFunction:
    def __init__(self, body=None):
        if body is None:
            body = _Phase1FakeBody()
        self._body = body

    def getBody(self):
        return self._body

def _expression_operators(expr: Expression | None) -> set[str]:
    operators = set()
    if expr is None:
        return operators
    operator = getattr(expr, "operator", None)
    if operator:
        operators.add(operator)
    for operand in getattr(expr, "operands", None) or ():
        operators.update(_expression_operators(operand))
    if getattr(expr, "expr_type", None) == ExpressionType.PHI:
        for condition, value in getattr(expr, "value", None) or ():
            operators.update(_expression_operators(getattr(condition, "expression", None)))
            operators.update(_expression_operators(value))
    return operators

def _eval_bv_expression(expr: Expression, parameters: dict[str, int]) -> int:
    size = max(1, int(getattr(expr, "size", 0) or 4))
    mask = (1 << (size * 8)) - 1
    if expr.expr_type == ExpressionType.CONSTANT:
        return int(expr.value or 0) & mask
    if expr.expr_type == ExpressionType.PARAMETER:
        return int(parameters[expr.name]) & mask
    if expr.expr_type == ExpressionType.UNARY_OP and expr.operator == "INT_ZEXT":
        return _eval_bv_expression(expr.operands[0], parameters) & mask
    if expr.expr_type != ExpressionType.BINARY_OP or len(expr.operands) != 2:
        raise AssertionError(f"unsupported expression in test evaluator: {expr.to_string()}")

    left, right = expr.operands
    if expr.operator == "SUBPIECE":
        offset = _eval_bv_expression(right, parameters)
        return (_eval_bv_expression(left, parameters) >> (offset * 8)) & mask

    left_value = _eval_bv_expression(left, parameters)
    right_value = _eval_bv_expression(right, parameters)
    if expr.operator == "INT_ADD":
        return (left_value + right_value) & mask
    if expr.operator == "INT_SUB":
        return (left_value - right_value) & mask
    if expr.operator == "INT_MULT":
        return (left_value * right_value) & mask
    if expr.operator == "INT_RIGHT":
        return (left_value >> right_value) & mask
    raise AssertionError(f"unsupported operator in test evaluator: {expr.operator}")

class _FakeIterator:
    def __init__(self, items):
        self._items = list(items)
        self._index = 0

    def hasNext(self):
        return self._index < len(self._items)

    def next(self):
        item = self._items[self._index]
        self._index += 1
        return item

class _FakeBlock:
    def __init__(self, ops):
        self._ops = list(ops)

    def getIterator(self):
        return _FakeIterator(self._ops)

class _FakeHighFunction:
    def __init__(self, ops):
        self._ops = list(ops)

    def getBasicBlocks(self):
        return [_FakeBlock(self._ops)]

class _FakeSeqTarget:
    def __init__(self, text: str):
        self._text = text

    def __str__(self):
        return self._text

class _FakeSeqNum:
    def __init__(self, text: str, order: int):
        self._target = _FakeSeqTarget(text)
        self._order = order

    def getTarget(self):
        return self._target

    def getOrder(self):
        return self._order

class _FakeAddressSpace:
    def __init__(
        self,
        name: str,
        *,
        space_id: int | None = None,
        space_type: int | None = None,
        is_memory: bool | None = None,
        is_register: bool | None = None,
        is_stack: bool | None = None,
    ):
        self._name = name
        self._space_id = space_id
        self._space_type = space_type
        self._is_memory = is_memory
        self._is_register = is_register
        self._is_stack = is_stack

    def getName(self):
        return self._name

    def getSpaceID(self):
        if self._space_id is None:
            raise AttributeError("space id unavailable")
        return self._space_id

    def getType(self):
        if self._space_type is None:
            raise AttributeError("space type unavailable")
        return self._space_type

    def isMemorySpace(self):
        if self._is_memory is None:
            raise AttributeError("memory flag unavailable")
        return self._is_memory

    def isRegisterSpace(self):
        if self._is_register is None:
            raise AttributeError("register flag unavailable")
        return self._is_register

    def isStackSpace(self):
        if self._is_stack is None:
            raise AttributeError("stack flag unavailable")
        return self._is_stack

    def getAddress(self, offset):
        return _FakeAddress(self, offset=int(offset))

class _FakeAddress:
    def __init__(self, space_name: str | _FakeAddressSpace, *, offset: int | None = None):
        self._space = space_name if isinstance(space_name, _FakeAddressSpace) else _FakeAddressSpace(space_name)
        self._offset = offset

    def getAddressSpace(self):
        return self._space

    def getOffset(self):
        if self._offset is None:
            raise AttributeError("offset unavailable")
        return self._offset

    def add(self, offset):
        if self._offset is None:
            raise AttributeError("offset unavailable")
        return _FakeAddress(self._space, offset=self._offset + int(offset))

class _FakeOutput:
    def __init__(self, space_name: str = "register", offset: int = 0x4000, size: int = 4):
        self._address = _FakeAddress(space_name)
        self._offset = offset
        self._size = size

    def getAddress(self):
        return self._address

    def getOffset(self):
        return self._offset

    def getSize(self):
        return self._size

class _FakeTargetVarnode:
    pass

class _FakeArgVarnode:
    def __init__(self, expr: Expression):
        self.expr = expr

class _FakeCallOp:
    def __init__(self, target_name: str, arg_expr: Expression):
        self._target_name = target_name
        self._arg = _FakeArgVarnode(arg_expr)

    def getMnemonic(self):
        return "CALL"

    def getNumInputs(self):
        return 2

    def getInput(self, index):
        if index == 0:
            return _FakeTargetVarnode()
        if index == 1:
            return self._arg
        raise IndexError(index)

class _FakeFunction:
    def __init__(self, name: str):
        self._name = name

    def getName(self):
        return self._name

class _FakeHighSymbol:
    def __init__(self, category_index: int | None = None):
        self._category_index = category_index

    def getCategoryIndex(self):
        if self._category_index is None:
            raise AttributeError("category index unavailable")
        return self._category_index

class _FakeHighVar:
    def __init__(self, name: str, symbol=None):
        self._name = name
        self._symbol = symbol

    def getName(self):
        return self._name

    def getSymbol(self):
        return self._symbol

    def getRepresentative(self):
        return self

class _FakeVarnode:
    def __init__(
        self,
        name: str,
        size: int = 4,
        expr: Expression | None = None,
        high=None,
        storage_offset: int | None = None,
        storage_space: str = "register",
    ):
        self._name = name
        self._size = size
        self._expr = expr
        self._def = None
        self._high = high or _FakeHighVar(name)
        self._descendants = []
        self._storage_offset = storage_offset
        self._storage_space = storage_space

    def getDef(self):
        return self._def

    def setDef(self, op):
        self._def = op

    def addDescendant(self, op):
        self._descendants.append(op)

    def getDescendants(self):
        return iter(self._descendants)

    def getHigh(self):
        return self._high

    def getSize(self):
        return self._size

    def getAddress(self):
        if self._storage_offset is None:
            raise AttributeError("storage address unavailable")
        return _FakeAddress(self._storage_space)

    def getOffset(self):
        if self._storage_offset is None:
            raise AttributeError("storage offset unavailable")
        return self._storage_offset

class _FakeConstantVarnode(_FakeVarnode):
    def __init__(self, value: int, size: int = 4):
        super().__init__(f"const_{value}", size=size, storage_offset=int(value), storage_space="const")
        self._value = int(value)

    def isConstant(self):
        return True

    def getOffset(self):
        return self._value

class _FakeStoreSpaceVarnode:
    def __init__(
        self,
        *,
        target_space_id: int,
        size: int = 8,
        pcode_space: _FakeAddressSpace | None = None,
    ):
        self._target_space_id = target_space_id
        self._size = size
        self._address = _FakeAddress(pcode_space or _FakeAddressSpace("const", space_id=0))

    def getAddress(self):
        return self._address

    def getOffset(self):
        return self._target_space_id

    def getSize(self):
        return self._size

class _FakeAddressFactory:
    def __init__(self, spaces, default_space=None):
        self._spaces = dict(spaces)
        self._default_space = default_space

    def getAddressSpace(self, space_id):
        return self._spaces[int(space_id)]

    def getDefaultAddressSpace(self):
        if self._default_space is not None:
            return self._default_space
        return next(iter(self._spaces.values()))

class _FakeMemoryBlock:
    def __init__(self, start: int, end: int, *, execute: bool, read: bool = True, write: bool = False):
        self._start = int(start)
        self._end = int(end)
        self._execute = bool(execute)
        self._read = bool(read)
        self._write = bool(write)

    def contains(self, address):
        try:
            offset = int(address.getOffset())
        except Exception:
            return False
        return self._start <= offset <= self._end

    def isExecute(self):
        return self._execute

    def isRead(self):
        return self._read

    def isWrite(self):
        return self._write

    # Issue #282 (Q1): 具体化は block の init・volatile・overlay・範囲を確かめる
    def isInitialized(self):
        return True

    def isVolatile(self):
        return False

    def isOverlay(self):
        return False

    def getStart(self):
        return _FakeAddress("ram", offset=self._start)

    def getEnd(self):
        return _FakeAddress("ram", offset=self._end)

class _FakeRelocationTable:
    def getRelocations(self, _address):
        return iter(())

class _FakeMemory:
    def __init__(self, blocks, bytes_by_address=None):
        self._blocks = list(blocks or [])
        self._bytes_by_address = dict(bytes_by_address or {})

    def getBlock(self, address):
        return next((block for block in self._blocks if block.contains(address)), None)

    def getByte(self, address):
        offset = int(address.getOffset())
        if offset not in self._bytes_by_address:
            raise KeyError(offset)
        return self._bytes_by_address[offset]

class _FakeLanguage:
    def __init__(self, *, big_endian: bool = False):
        self._big_endian = bool(big_endian)

    def isBigEndian(self):
        return self._big_endian

class _FakeIntDataType:
    def __init__(self, *, signed: bool = True, length: int = 4):
        self._signed = bool(signed)
        self._length = int(length)

    def isSigned(self):
        return self._signed

    def getLength(self):
        return self._length

class _FakeProgram:
    def __init__(self, address_factory, memory=None, language=None):
        self._address_factory = address_factory
        self._memory = memory
        self._language = language or _FakeLanguage()

    def getAddressFactory(self):
        return self._address_factory

    def getMemory(self):
        return self._memory

    def getLanguage(self):
        return self._language

    def getRelocationTable(self):
        return _FakeRelocationTable()

class _IdentityTracer:
    def __init__(self, expressions=None, storages=None):
        self._expressions = dict(expressions or {})
        self._storages = dict(storages or {})

    def trace_varnode(self, varnode, *args, **kwargs):
        return self._expressions.get(varnode, getattr(varnode, "_expr", None))

    def _get_storage_info_from_varnode(self, varnode):
        return self._storages.get(varnode)

def _register_storage(
    register_name: str,
    *,
    offset: int,
    size: int,
) -> StorageInfo:
    return StorageInfo(
        is_register=True,
        space_name="register",
        space_id=0,
        offset=offset,
        size=size,
        size_bits=size * 8,
        register_name=register_name,
        base_register_name=register_name,
        base_register_offset=offset,
        base_register_size=size,
        base_register_size_bits=size * 8,
        bit_offset_in_base=0,
    )

class _FakePcodeOp:
    def __init__(self, mnemonic: str, inputs, output=None):
        self._mnemonic = mnemonic
        self._inputs = list(inputs)
        self._output = output
        self._parent = None
        if output is not None:
            output.setDef(self)
        for input_varnode in self._inputs:
            add_descendant = getattr(input_varnode, "addDescendant", None)
            if callable(add_descendant):
                add_descendant(self)

    def getMnemonic(self):
        return self._mnemonic

    def getNumInputs(self):
        return len(self._inputs)

    def getInput(self, index):
        return self._inputs[index]

    def getOutput(self):
        return self._output

    def setParent(self, parent):
        self._parent = parent

    def getParent(self):
        return self._parent

class _FakeBranchOp(_FakePcodeOp):
    def __init__(self, condition_expr: Expression):
        super().__init__("CBRANCH", [_FakeVarnode("branch_target"), _FakeArgVarnode(condition_expr)], None)

class _FakeCfgBlock:
    def __init__(self, index: int, ops=None):
        self._index = index
        self._ops = list(ops or [])
        self._ins = []
        self._outs = []
        self._true_out = None
        self._false_out = None
        for op in self._ops:
            if hasattr(op, "setParent"):
                op.setParent(self)

    def getIndex(self):
        return self._index

    def getIterator(self):
        return _FakeIterator(self._ops)

    def add_edge(self, target, *, truth: bool | None = None):
        self._outs.append(target)
        target._ins.append(self)
        if truth is True:
            self._true_out = target
        elif truth is False:
            self._false_out = target

    def getOutSize(self):
        return len(self._outs)

    def getOut(self, index):
        return self._outs[index]

    def getInSize(self):
        return len(self._ins)

    def getIn(self, index):
        return self._ins[index]

    def getInRevIndex(self, index):
        incoming = self.getIn(index)
        for out_index, target in enumerate(incoming._outs):
            if target is self:
                return out_index
        return -1

    def getTrueOut(self):
        return self._true_out

    def getFalseOut(self):
        return self._false_out

class _FakeCfgBlockWithoutIterator(_FakeCfgBlock):
    def getIterator(self):
        return None

class _FakeCfgHighFunction:
    def __init__(self, blocks):
        self._blocks = list(blocks)

    def getBasicBlocks(self):
        return list(self._blocks)

class _FakeTracer:
    def __init__(self, function_name: str, arg_expr: Expression, *, program=None):
        self._function_name = function_name
        self._arg_expr = arg_expr
        self.debug = False
        self.program = program

    def trace_varnode(self, varnode, use_cache=True):
        if hasattr(varnode, "expr"):
            return varnode.expr
        if hasattr(varnode, "_expr") and varnode._expr is not None:
            return varnode._expr
        return self._arg_expr

    def resolve_call_target_ref(self, _addr_varnode, **_kwargs):
        return CallTargetRef.from_name(self._function_name)

def _build_branch_while_state_cfg(
    *,
    swap_transition_inputs: bool = False,
    accumulator_init_expr: Optional[Expression] = None,
):
    param = _param("param_1")
    zero_expr = _const(0)
    one_expr = _const(1)
    three_expr = _const(3)

    preheader = _FakeCfgBlock(0)
    header = _FakeCfgBlock(1)
    body = _FakeCfgBlock(2)
    even_block = _FakeCfgBlock(3)
    odd_block = _FakeCfgBlock(4)
    latch = _FakeCfgBlock(5)
    exit_block = _FakeCfgBlock(6)

    preheader.add_edge(header)
    header.add_edge(body, truth=True)
    header.add_edge(exit_block, truth=False)
    body.add_edge(odd_block, truth=True)
    body.add_edge(even_block, truth=False)
    even_block.add_edge(latch)
    odd_block.add_edge(latch)
    latch.add_edge(header)

    param_vn = _FakeVarnode("param", expr=param)
    zero_vn = _FakeVarnode("zero", expr=zero_expr)
    acc_init_vn = _FakeVarnode("acc_init", expr=accumulator_init_expr or zero_expr)
    one_vn = _FakeVarnode("one", expr=one_expr)
    three_vn = _FakeVarnode("three", expr=three_expr)

    state_phi_vn = _FakeVarnode("state_phi")
    state_merge_vn = _FakeVarnode("state_merge")
    state_even_vn = _FakeVarnode("state_even")
    state_odd_vn = _FakeVarnode("state_odd")
    acc_phi_vn = _FakeVarnode("acc_phi")
    acc_next_vn = _FakeVarnode("acc_next")
    guard_vn = _FakeVarnode("guard", size=1)
    parity_vn = _FakeVarnode("parity")
    parity_cond_vn = _FakeVarnode("parity_cond", size=1)

    state_phi_op = _FakePcodeOp("MULTIEQUAL", [param_vn, state_merge_vn], state_phi_vn)
    acc_phi_op = _FakePcodeOp("MULTIEQUAL", [acc_init_vn, acc_next_vn], acc_phi_vn)
    guard_op = _FakePcodeOp("INT_SLESS", [zero_vn, state_phi_vn], guard_vn)
    header_branch = _FakePcodeOp("CBRANCH", [_FakeVarnode("header_target"), guard_vn], None)
    header._ops[:] = [state_phi_op, acc_phi_op, guard_op, header_branch]
    for op in header._ops:
        op.setParent(header)

    parity_op = _FakePcodeOp("INT_AND", [state_phi_vn, one_vn], parity_vn)
    parity_cmp = _FakePcodeOp("INT_NOTEQUAL", [parity_vn, zero_vn], parity_cond_vn)
    body_branch = _FakePcodeOp("CBRANCH", [_FakeVarnode("body_target"), parity_cond_vn], None)
    body._ops[:] = [parity_op, parity_cmp, body_branch]
    for op in body._ops:
        op.setParent(body)

    state_even_op = _FakePcodeOp("INT_SRIGHT", [state_phi_vn, one_vn], state_even_vn)
    even_block._ops[:] = [state_even_op]
    state_even_op.setParent(even_block)

    state_odd_op = _FakePcodeOp("INT_SUB", [state_phi_vn, three_vn], state_odd_vn)
    odd_block._ops[:] = [state_odd_op]
    state_odd_op.setParent(odd_block)

    merge_inputs = [state_even_vn, state_odd_vn]
    if swap_transition_inputs:
        merge_inputs = [state_odd_vn, state_even_vn]
        latch._ins[:] = [odd_block, even_block]
    state_merge_op = _FakePcodeOp("MULTIEQUAL", merge_inputs, state_merge_vn)
    acc_next_op = _FakePcodeOp("INT_ADD", [acc_phi_vn, one_vn], acc_next_vn)
    latch._ops[:] = [state_merge_op, acc_next_op]
    for op in latch._ops:
        op.setParent(latch)

    return_op = _FakePcodeOp("RETURN", [_FakeVarnode("return_target"), acc_phi_vn], None)
    exit_block._ops[:] = [return_op]
    return_op.setParent(exit_block)

    return _FakeCfgHighFunction([preheader, header, body, even_block, odd_block, latch, exit_block])

def _build_branch_while_state_latch_guarded_cfg(*, shift_mnemonic: str = "INT_SRIGHT"):
    param = _param("param_1")
    zero_expr = _const(0)
    one_expr = _const(1)
    three_expr = _const(3)

    precheck = _FakeCfgBlock(0)
    zero_exit = _FakeCfgBlock(1)
    entry = _FakeCfgBlock(2)
    header = _FakeCfgBlock(3)
    odd_block = _FakeCfgBlock(4)
    latch = _FakeCfgBlock(5)
    exit_block = _FakeCfgBlock(6)

    precheck.add_edge(entry, truth=True)
    precheck.add_edge(zero_exit, truth=False)
    entry.add_edge(header)
    header.add_edge(odd_block, truth=True)
    header.add_edge(latch, truth=False)
    odd_block.add_edge(latch)
    latch.add_edge(header, truth=True)
    latch.add_edge(exit_block, truth=False)

    param_vn = _FakeVarnode("param", expr=param)
    zero_vn = _FakeVarnode("zero", expr=zero_expr)
    one_vn = _FakeVarnode("one", expr=one_expr)
    three_vn = _FakeVarnode("three", expr=three_expr)

    entry_guard_vn = _FakeVarnode("entry_guard", size=1)
    state_phi_vn = _FakeVarnode("state_phi")
    state_even_vn = _FakeVarnode("state_even")
    state_odd_vn = _FakeVarnode("state_odd")
    state_merge_vn = _FakeVarnode("state_merge")
    acc_phi_vn = _FakeVarnode("acc_phi")
    acc_next_vn = _FakeVarnode("acc_next")
    parity_vn = _FakeVarnode("parity")
    parity_cond_vn = _FakeVarnode("parity_cond", size=1)
    latch_guard_vn = _FakeVarnode("latch_guard", size=1)

    entry_guard_op = _FakePcodeOp("INT_SLESS", [zero_vn, param_vn], entry_guard_vn)
    precheck_branch = _FakePcodeOp("CBRANCH", [_FakeVarnode("entry_target"), entry_guard_vn], None)
    precheck._ops[:] = [entry_guard_op, precheck_branch]
    for op in precheck._ops:
        op.setParent(precheck)

    state_phi_op = _FakePcodeOp("MULTIEQUAL", [param_vn, state_merge_vn], state_phi_vn)
    acc_phi_op = _FakePcodeOp("MULTIEQUAL", [zero_vn, acc_next_vn], acc_phi_vn)
    state_even_op = _FakePcodeOp(shift_mnemonic, [state_phi_vn, one_vn], state_even_vn)
    parity_op = _FakePcodeOp("INT_AND", [state_phi_vn, one_vn], parity_vn)
    parity_cmp = _FakePcodeOp("INT_NOTEQUAL", [parity_vn, zero_vn], parity_cond_vn)
    header_branch = _FakePcodeOp("CBRANCH", [_FakeVarnode("body_target"), parity_cond_vn], None)
    header._ops[:] = [state_phi_op, acc_phi_op, state_even_op, parity_op, parity_cmp, header_branch]
    for op in header._ops:
        op.setParent(header)

    state_odd_op = _FakePcodeOp("INT_SUB", [state_phi_vn, three_vn], state_odd_vn)
    odd_block._ops[:] = [state_odd_op]
    state_odd_op.setParent(odd_block)

    state_merge_op = _FakePcodeOp("MULTIEQUAL", [state_even_vn, state_odd_vn], state_merge_vn)
    acc_next_op = _FakePcodeOp("INT_ADD", [acc_phi_vn, one_vn], acc_next_vn)
    latch_guard_op = _FakePcodeOp("INT_SLESS", [zero_vn, state_merge_vn], latch_guard_vn)
    latch_branch = _FakePcodeOp("CBRANCH", [_FakeVarnode("latch_target"), latch_guard_vn], None)
    latch._ops[:] = [state_merge_op, acc_next_op, latch_guard_op, latch_branch]
    for op in latch._ops:
        op.setParent(latch)

    return_op = _FakePcodeOp("RETURN", [_FakeVarnode("return_target"), acc_next_vn], None)
    exit_block._ops[:] = [return_op]
    return_op.setParent(exit_block)

    return _FakeCfgHighFunction([precheck, zero_exit, entry, header, odd_block, latch, exit_block])

def _build_decrement_accumulator_sum_cfg():
    param = _param("param_1")
    zero_expr = _const(0)
    one_expr = _const(1)

    preheader = _FakeCfgBlock(0)
    header = _FakeCfgBlock(1)
    body = _FakeCfgBlock(2)
    exit_block = _FakeCfgBlock(3)

    preheader.add_edge(header)
    header.add_edge(body, truth=True)
    header.add_edge(exit_block, truth=False)
    body.add_edge(header)

    param_vn = _FakeVarnode("param", expr=param)
    zero_vn = _FakeVarnode("zero", expr=zero_expr)
    one_vn = _FakeVarnode("one", expr=one_expr)

    state_phi_vn = _FakeVarnode("state_phi")
    state_next_vn = _FakeVarnode("state_next")
    acc_phi_vn = _FakeVarnode("acc_phi")
    acc_next_vn = _FakeVarnode("acc_next")
    guard_vn = _FakeVarnode("guard", size=1)

    state_phi_op = _FakePcodeOp("MULTIEQUAL", [param_vn, state_next_vn], state_phi_vn)
    acc_phi_op = _FakePcodeOp("MULTIEQUAL", [zero_vn, acc_next_vn], acc_phi_vn)
    guard_op = _FakePcodeOp("INT_SLESS", [zero_vn, state_phi_vn], guard_vn)
    branch = _FakePcodeOp("CBRANCH", [_FakeVarnode("body_target"), guard_vn], None)
    header._ops[:] = [state_phi_op, acc_phi_op, guard_op, branch]
    for op in header._ops:
        op.setParent(header)

    acc_next_op = _FakePcodeOp("INT_ADD", [acc_phi_vn, state_phi_vn], acc_next_vn)
    state_next_op = _FakePcodeOp("INT_SUB", [state_phi_vn, one_vn], state_next_vn)
    body._ops[:] = [acc_next_op, state_next_op]
    for op in body._ops:
        op.setParent(body)

    return_op = _FakePcodeOp("RETURN", [_FakeVarnode("return_target"), acc_phi_vn], None)
    exit_block._ops[:] = [return_op]
    return_op.setParent(exit_block)

    return _FakeCfgHighFunction([preheader, header, body, exit_block])

def _build_progress_guarded_unit_state_transition_cfg():
    t_param = _param("param_1")
    c_param = _param("param_2")
    zero_expr = _const(0)

    preheader = _FakeCfgBlock(0)
    header = _FakeCfgBlock(1)
    body = _FakeCfgBlock(2)
    exit_block = _FakeCfgBlock(3)

    preheader.add_edge(header)
    header.add_edge(body, truth=True)
    header.add_edge(exit_block, truth=False)
    body.add_edge(header)

    t_param_vn = _FakeVarnode("t_param", expr=t_param)
    c_param_vn = _FakeVarnode("c_param", expr=c_param)
    zero_vn = _FakeVarnode("zero", expr=zero_expr)

    state_phi_vn = _FakeVarnode("state_phi")
    state_next_vn = _FakeVarnode("state_next")
    acc_phi_vn = _FakeVarnode("acc_phi")
    acc_next_vn = _FakeVarnode("acc_next")
    state_guard_vn = _FakeVarnode("state_guard", size=1)
    progress_guard_vn = _FakeVarnode("progress_guard", size=1)

    state_phi_op = _FakePcodeOp("MULTIEQUAL", [c_param_vn, state_next_vn], state_phi_vn)
    acc_phi_op = _FakePcodeOp("MULTIEQUAL", [zero_vn, acc_next_vn], acc_phi_vn)
    state_guard_op = _FakePcodeOp("INT_SLESS", [zero_vn, state_phi_vn], state_guard_vn)
    branch = _FakePcodeOp("CBRANCH", [_FakeVarnode("body_target"), state_guard_vn], None)
    header._ops[:] = [state_phi_op, acc_phi_op, state_guard_op, branch]
    for op in header._ops:
        op.setParent(header)

    progress_guard_op = _FakePcodeOp("INT_SLESS", [zero_vn, t_param_vn], progress_guard_vn)
    state_next_op = _FakePcodeOp("INT_SUB", [state_phi_vn, progress_guard_vn], state_next_vn)
    acc_next_op = _FakePcodeOp("INT_ADD", [acc_phi_vn, progress_guard_vn], acc_next_vn)
    body._ops[:] = [progress_guard_op, state_next_op, acc_next_op]
    for op in body._ops:
        op.setParent(body)

    return_op = _FakePcodeOp("RETURN", [_FakeVarnode("return_target"), acc_phi_vn], None)
    exit_block._ops[:] = [return_op]
    return_op.setParent(exit_block)

    return _FakeCfgHighFunction([preheader, header, body, exit_block])

def _build_latch_progress_guarded_unit_state_transition_cfg():
    t_param = _param("param_1")
    c_param = _param("param_2")
    zero_expr = _const(0)

    preheader = _FakeCfgBlock(0)
    header = _FakeCfgBlock(1)
    latch = _FakeCfgBlock(2)
    exit_block = _FakeCfgBlock(3)

    preheader.add_edge(header)
    header.add_edge(latch)
    latch.add_edge(header, truth=True)
    latch.add_edge(exit_block, truth=False)

    t_param_vn = _FakeVarnode("t_param", expr=t_param)
    c_param_vn = _FakeVarnode("c_param", expr=c_param)
    zero_vn = _FakeVarnode("zero", expr=zero_expr)

    state_phi_vn = _FakeVarnode("state_phi")
    state_next_vn = _FakeVarnode("state_next")
    acc_phi_vn = _FakeVarnode("acc_phi")
    acc_next_vn = _FakeVarnode("acc_next")
    progress_guard_vn = _FakeVarnode("progress_guard", size=1)
    latch_guard_vn = _FakeVarnode("latch_guard", size=1)

    state_phi_op = _FakePcodeOp("MULTIEQUAL", [c_param_vn, state_next_vn], state_phi_vn)
    acc_phi_op = _FakePcodeOp("MULTIEQUAL", [zero_vn, acc_next_vn], acc_phi_vn)
    header._ops[:] = [state_phi_op, acc_phi_op]
    for op in header._ops:
        op.setParent(header)

    progress_guard_op = _FakePcodeOp("INT_SLESS", [zero_vn, t_param_vn], progress_guard_vn)
    state_next_op = _FakePcodeOp("INT_SUB", [state_phi_vn, progress_guard_vn], state_next_vn)
    acc_next_op = _FakePcodeOp("INT_ADD", [acc_phi_vn, progress_guard_vn], acc_next_vn)
    latch_guard_op = _FakePcodeOp("INT_SLESS", [zero_vn, state_next_vn], latch_guard_vn)
    latch_branch = _FakePcodeOp("CBRANCH", [_FakeVarnode("latch_target"), latch_guard_vn], None)
    latch._ops[:] = [progress_guard_op, state_next_op, acc_next_op, latch_guard_op, latch_branch]
    for op in latch._ops:
        op.setParent(latch)

    return_op = _FakePcodeOp("RETURN", [_FakeVarnode("return_target"), acc_next_vn], None)
    exit_block._ops[:] = [return_op]
    return_op.setParent(exit_block)

    return _FakeCfgHighFunction([preheader, header, latch, exit_block])

def _build_latch_exit_decrement_accumulator_sum_cfg():
    param = _param("param_1")
    zero_expr = _const(0)
    one_expr = _const(1)

    precheck = _FakeCfgBlock(0)
    zero_exit = _FakeCfgBlock(1)
    header = _FakeCfgBlock(2)
    latch = _FakeCfgBlock(3)
    exit_block = _FakeCfgBlock(4)

    precheck.add_edge(header, truth=True)
    precheck.add_edge(zero_exit, truth=False)
    header.add_edge(latch)
    latch.add_edge(header, truth=True)
    latch.add_edge(exit_block, truth=False)

    param_vn = _FakeVarnode("param", expr=param)
    zero_vn = _FakeVarnode("zero", expr=zero_expr)
    one_vn = _FakeVarnode("one", expr=one_expr)

    entry_guard_vn = _FakeVarnode("entry_guard", size=1)
    state_phi_vn = _FakeVarnode("state_phi")
    state_next_vn = _FakeVarnode("state_next")
    guard_state_vn = _FakeVarnode("guard_state")
    acc_phi_vn = _FakeVarnode("acc_phi")
    acc_next_vn = _FakeVarnode("acc_next")
    latch_guard_vn = _FakeVarnode("latch_guard", size=1)

    entry_guard_op = _FakePcodeOp("INT_SLESS", [zero_vn, param_vn], entry_guard_vn)
    precheck_branch = _FakePcodeOp("CBRANCH", [_FakeVarnode("entry_target"), entry_guard_vn], None)
    precheck._ops[:] = [entry_guard_op, precheck_branch]
    for op in precheck._ops:
        op.setParent(precheck)

    state_phi_op = _FakePcodeOp("MULTIEQUAL", [param_vn, state_next_vn], state_phi_vn)
    acc_phi_op = _FakePcodeOp("MULTIEQUAL", [zero_vn, acc_next_vn], acc_phi_vn)
    header._ops[:] = [state_phi_op, acc_phi_op]
    for op in header._ops:
        op.setParent(header)

    acc_next_op = _FakePcodeOp("INT_ADD", [acc_phi_vn, state_phi_vn], acc_next_vn)
    state_next_op = _FakePcodeOp("INT_SUB", [state_phi_vn, one_vn], state_next_vn)
    guard_state_op = _FakePcodeOp("INT_SUB", [state_phi_vn, one_vn], guard_state_vn)
    latch_guard_op = _FakePcodeOp("INT_NOTEQUAL", [guard_state_vn, zero_vn], latch_guard_vn)
    latch_branch = _FakePcodeOp("CBRANCH", [_FakeVarnode("latch_target"), latch_guard_vn], None)
    latch._ops[:] = [acc_next_op, state_next_op, guard_state_op, latch_guard_op, latch_branch]
    for op in latch._ops:
        op.setParent(latch)

    zero_return = _FakePcodeOp("RETURN", [_FakeVarnode("return_target"), zero_vn], None)
    zero_exit._ops[:] = [zero_return]
    zero_return.setParent(zero_exit)

    loop_return = _FakePcodeOp("RETURN", [_FakeVarnode("return_target"), acc_next_vn], None)
    exit_block._ops[:] = [loop_return]
    loop_return.setParent(exit_block)

    return _FakeCfgHighFunction([precheck, zero_exit, header, latch, exit_block])

def _build_branch_while_state_multi_latch_cfg(*, shift_mnemonic: str = "INT_SRIGHT"):
    param = _param("param_1")
    zero_expr = _const(0)
    one_expr = _const(1)
    three_expr = _const(3)

    precheck = _FakeCfgBlock(0)
    zero_exit = _FakeCfgBlock(1)
    header = _FakeCfgBlock(2)
    even_latch = _FakeCfgBlock(3)
    odd_latch = _FakeCfgBlock(4)
    exit_block = _FakeCfgBlock(5)

    precheck.add_edge(header, truth=True)
    precheck.add_edge(zero_exit, truth=False)
    header.add_edge(even_latch, truth=True)
    header.add_edge(odd_latch, truth=False)
    even_latch.add_edge(exit_block, truth=True)
    even_latch.add_edge(header, truth=False)
    odd_latch.add_edge(header, truth=True)
    odd_latch.add_edge(exit_block, truth=False)

    param_vn = _FakeVarnode("param", expr=param)
    zero_vn = _FakeVarnode("zero", expr=zero_expr)
    one_vn = _FakeVarnode("one", expr=one_expr)
    three_vn = _FakeVarnode("three", expr=three_expr)

    entry_guard_vn = _FakeVarnode("entry_guard", size=1)
    state_phi_vn = _FakeVarnode("state_phi")
    state_even_vn = _FakeVarnode("state_even")
    state_odd_vn = _FakeVarnode("state_odd")
    acc_phi_vn = _FakeVarnode("acc_phi")
    acc_even_vn = _FakeVarnode("acc_even")
    acc_odd_vn = _FakeVarnode("acc_odd")
    parity_vn = _FakeVarnode("parity")
    parity_cond_vn = _FakeVarnode("parity_cond", size=1)
    even_exit_guard_vn = _FakeVarnode("even_exit_guard", size=1)
    odd_continue_guard_vn = _FakeVarnode("odd_continue_guard", size=1)

    entry_guard_op = _FakePcodeOp("INT_SLESS", [zero_vn, param_vn], entry_guard_vn)
    precheck_branch = _FakePcodeOp("CBRANCH", [_FakeVarnode("entry_target"), entry_guard_vn], None)
    precheck._ops[:] = [entry_guard_op, precheck_branch]
    for op in precheck._ops:
        op.setParent(precheck)

    state_phi_op = _FakePcodeOp("MULTIEQUAL", [param_vn, state_even_vn, state_odd_vn], state_phi_vn)
    acc_phi_op = _FakePcodeOp("MULTIEQUAL", [zero_vn, acc_even_vn, acc_odd_vn], acc_phi_vn)
    parity_op = _FakePcodeOp("INT_AND", [state_phi_vn, one_vn], parity_vn)
    parity_cmp = _FakePcodeOp("INT_EQUAL", [parity_vn, zero_vn], parity_cond_vn)
    header_branch = _FakePcodeOp("CBRANCH", [_FakeVarnode("body_target"), parity_cond_vn], None)
    header._ops[:] = [state_phi_op, acc_phi_op, parity_op, parity_cmp, header_branch]
    for op in header._ops:
        op.setParent(header)

    state_even_op = _FakePcodeOp(shift_mnemonic, [state_phi_vn, one_vn], state_even_vn)
    acc_even_op = _FakePcodeOp("INT_ADD", [acc_phi_vn, one_vn], acc_even_vn)
    even_exit_guard_op = _FakePcodeOp("INT_SLESS", [state_even_vn, one_vn], even_exit_guard_vn)
    even_branch = _FakePcodeOp("CBRANCH", [_FakeVarnode("even_latch_target"), even_exit_guard_vn], None)
    even_latch._ops[:] = [state_even_op, acc_even_op, even_exit_guard_op, even_branch]
    for op in even_latch._ops:
        op.setParent(even_latch)

    state_odd_op = _FakePcodeOp("INT_SUB", [state_phi_vn, three_vn], state_odd_vn)
    acc_odd_op = _FakePcodeOp("INT_ADD", [acc_phi_vn, one_vn], acc_odd_vn)
    odd_continue_guard_op = _FakePcodeOp("INT_SLESS", [zero_vn, state_odd_vn], odd_continue_guard_vn)
    odd_branch = _FakePcodeOp("CBRANCH", [_FakeVarnode("odd_latch_target"), odd_continue_guard_vn], None)
    odd_latch._ops[:] = [state_odd_op, acc_odd_op, odd_continue_guard_op, odd_branch]
    for op in odd_latch._ops:
        op.setParent(odd_latch)

    return_op = _FakePcodeOp("RETURN", [_FakeVarnode("return_target"), acc_phi_vn], None)
    exit_block._ops[:] = [return_op]
    return_op.setParent(exit_block)

    return _FakeCfgHighFunction([precheck, zero_exit, header, even_latch, odd_latch, exit_block])

def _mem(base_name: str, offset: int = 0) -> Expression:
    base = Expression.parameter(base_name, index=0, data_type="int *", size=8)
    if offset == 0:
        return Expression.memory(base, size=4)
    return Expression.memory(
        Expression.binary_op("INT_ADD", base, Expression.constant(offset, size=8)),
        size=4,
    )

def _loc(base_name: str, offset: int = 0, size: int = 4) -> CanonicalLocation:
    return CanonicalLocation(
        base_ref=LocationBaseRef.parameter(base_name, index=0),
        offset=offset,
        size=size,
    )

def _mem_mul_offset(base_name: str, offset: int) -> Expression:
    base = Expression.parameter(base_name, index=0, data_type="int *", size=8)
    return Expression.memory(
        Expression.binary_op(
            "INT_ADD",
            base,
            Expression.binary_op(
                "INT_MULT",
                Expression.constant(1, size=8),
                Expression.constant(offset, size=8),
            ),
        ),
        size=4,
    )

def _mem_ptradd_index(base_name: str, index: int) -> Expression:
    base = Expression.parameter(base_name, index=0, data_type="int *", size=8)
    if index == 0:
        return Expression.memory(base, size=4)
    return Expression.memory(
        Expression.intrinsic(
            "PTRADD",
            [base, Expression.constant(index, size=8), Expression.constant(4, size=8)],
            size=8,
        ),
        size=4,
    )

def _sum_terms(*terms: Expression) -> Expression:
    value = terms[0]
    for term in terms[1:]:
        value = Expression.binary_op("INT_ADD", value, term)
    return value

# Export private helpers as well; split tests retain the original module globals.
__all__ = [name for name in globals() if not name.startswith('__')]
