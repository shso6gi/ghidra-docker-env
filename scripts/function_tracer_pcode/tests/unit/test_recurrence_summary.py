# -*- coding: utf-8 -*-

from scripts.function_tracer_pcode.analysis.recurrence_summary import StructuralRecurrenceSummarizer
from scripts.function_tracer_pcode.analysis import ReturnAnalyzer
from scripts.function_tracer_pcode.analysis.tracer import PcodeTracer
from scripts.function_tracer_pcode.analysis.effect_summary import (
    CanonicalLocation,
    EffectSummary,
    StoreEffect,
)
from scripts.function_tracer_pcode.model import (
    READONLY_SUM_OPCODE,
    CallTargetRef,
    Condition,
    Expression,
    LocationBaseRef,
    ReadonlyReductionTermRef,
    ReturnInfo,
    ReadonlyReductionRef,
    ReadonlyReductionWitness,
    UnknownValueRef,
)
from scripts.function_tracer_pcode.equivalence.formula.returns import expression_has_unresolved_value
from scripts.function_tracer_pcode.model.render_smt import expression_to_smt
from scripts.function_tracer_pcode.tests.conftest import create_mock_analysis


def _param(name: str = "param_1", size: int = 4) -> Expression:
    return Expression.parameter(name, index=0, data_type="int", size=size)


def _const(value: int, size: int = 4) -> Expression:
    return Expression.constant(value, size)


def _cond(operator: str, left: Expression, right: Expression, negated: bool = False) -> Condition:
    return Condition(Expression.binary_op(operator, left, right), negated=negated)


def test_recurrence_terms_equivalent_does_not_require_to_string(monkeypatch):
    summarizer = StructuralRecurrenceSummarizer(PcodeTracer.__new__(PcodeTracer), debug=False)
    left = Expression.binary_op(
        "INT_ADD",
        Expression.parameter("param_1", index=0, size=4),
        Expression.constant(1, 4),
    )
    right = Expression.binary_op(
        "INT_ADD",
        Expression.constant(1, 4),
        Expression.parameter("param_1", index=0, size=4),
    )

    def _boom_expr(_self, simplify=True):
        raise AssertionError("recurrence equivalence should not depend on Expression.to_string")

    monkeypatch.setattr(Expression, "to_string", _boom_expr)

    assert summarizer._terms_equivalent(left, right, []) is True


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
    def __init__(self, name: str):
        self._name = name

    def getName(self):
        return self._name


class _FakeAddress:
    def __init__(self, space_name: str):
        self._space = _FakeAddressSpace(space_name)

    def getAddressSpace(self):
        return self._space


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


class _FakeHighVar:
    def __init__(self, name: str):
        self._name = name

    def getName(self):
        return self._name

    def getRepresentative(self):
        return self


class _FakeVarnode:
    def __init__(self, name: str, size: int = 4, expr: Expression | None = None, high=None):
        self._name = name
        self._size = size
        self._expr = expr
        self._def = None
        self._high = high or _FakeHighVar(name)

    def getDef(self):
        return self._def

    def setDef(self, op):
        self._def = op

    def getHigh(self):
        return self._high

    def getSize(self):
        return self._size


class _FakePcodeOp:
    def __init__(self, mnemonic: str, inputs, output=None):
        self._mnemonic = mnemonic
        self._inputs = list(inputs)
        self._output = output
        self._parent = None
        if output is not None:
            output.setDef(self)

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

    def getTrueOut(self):
        return self._true_out

    def getFalseOut(self):
        return self._false_out


class _FakeCfgHighFunction:
    def __init__(self, blocks):
        self._blocks = list(blocks)

    def getBasicBlocks(self):
        return list(self._blocks)


class _FakeTracer:
    def __init__(self, function_name: str, arg_expr: Expression):
        self._function_name = function_name
        self._arg_expr = arg_expr
        self.debug = False

    def trace_varnode(self, varnode, use_cache=True):
        if hasattr(varnode, "expr"):
            return varnode.expr
        if hasattr(varnode, "_expr") and varnode._expr is not None:
            return varnode._expr
        return self._arg_expr

    def resolve_call_target_ref(self, _addr_varnode, **_kwargs):
        return CallTargetRef.from_name(self._function_name)


def test_structural_recurrence_summarizer_recovers_linear_self_recursion():
    param = _param()
    unknown = Expression.unknown(
        "call_out_of_scope:fc_recursive_sum",
        runtime_ref=UnknownValueRef.out_of_scope_call(
            reason="call_out_of_scope",
            target_ref=CallTargetRef.from_name("fc_recursive_sum"),
            display_hint="fc_recursive_sum",
        ),
    )
    recursive_value = Expression.binary_op("INT_ADD", unknown, param)
    analysis = create_mock_analysis(
        "fc_recursive_sum",
        return_type="int",
        parameters=[{"name": "param_1", "index": 0, "data_type": "int", "size": 4}],
        returns=[
            ReturnInfo(address="0x1000", value=_const(0), conditions=[]),
            ReturnInfo(
                address="0x1004",
                value=recursive_value,
                conditions=[_cond("INT_SLESS", _const(0), param)],
            ),
        ],
    )
    summarizer = StructuralRecurrenceSummarizer(
        _FakeTracer(
            "fc_recursive_sum",
            Expression.binary_op("INT_SUB", param, _const(1)),
        ),
        debug=False,
    )

    summary = summarizer.try_summarize_function(
        _FakeFunction("fc_recursive_sum"),
        _FakeHighFunction([
            _FakeCallOp("fc_recursive_sum", Expression.binary_op("INT_SUB", param, _const(1))),
        ]),
        analysis,
    )

    assert summary is not None
    summarized_returns, note = summary
    assert note == "linear_self_recursion_summary"
    assert len(summarized_returns) == 2
    assert all("call_out_of_scope" not in ret.value.to_string() for ret in summarized_returns)
    assert any(">> 1" in ret.value.to_string() for ret in summarized_returns if ret.value.to_string() != "0")
    recursive_case = next(ret for ret in summarized_returns if ret.value.to_string() != "0")
    assert recursive_case.conditions[0].to_string() == "(0 < param_1)"


def test_structural_recurrence_summarizer_rejects_non_affine_recursion():
    param = _param()
    unknown = Expression.unknown(
        "call_out_of_scope:fc_recursive_sum",
        runtime_ref=UnknownValueRef.out_of_scope_call(
            reason="call_out_of_scope",
            target_ref=CallTargetRef.from_name("fc_recursive_sum"),
            display_hint="fc_recursive_sum",
        ),
    )
    recursive_value = Expression.binary_op(
        "INT_ADD",
        unknown,
        Expression.binary_op("INT_MULT", param, param),
    )
    analysis = create_mock_analysis(
        "fc_recursive_sum",
        return_type="int",
        parameters=[{"name": "param_1", "index": 0, "data_type": "int", "size": 4}],
        returns=[
            ReturnInfo(address="0x1000", value=_const(0), conditions=[]),
            ReturnInfo(
                address="0x1004",
                value=recursive_value,
                conditions=[_cond("INT_SLESS", _const(0), param)],
            ),
        ],
    )
    summarizer = StructuralRecurrenceSummarizer(
        _FakeTracer(
            "fc_recursive_sum",
            Expression.binary_op("INT_SUB", param, _const(1)),
        ),
        debug=False,
    )

    summary = summarizer.try_summarize_function(
        _FakeFunction("fc_recursive_sum"),
        _FakeHighFunction([
            _FakeCallOp("fc_recursive_sum", Expression.binary_op("INT_SUB", param, _const(1))),
        ]),
        analysis,
    )

    assert summary is None


def test_extract_index_step_accepts_subtractive_phi_updates():
    phi_output = _FakeVarnode("loop_aux")
    one_vn = _FakeVarnode("one", expr=_const(1))
    next_vn = _FakeVarnode("loop_aux_next")
    _FakePcodeOp("INT_SUB", [phi_output, one_vn], next_vn)

    summarizer = StructuralRecurrenceSummarizer(_FakeTracer("unused", _const(0)), debug=False)

    assert summarizer._extract_index_step(next_vn, phi_output) == -1


def test_affine_loop_state_phi_uses_entry_counter_placeholder():
    start_expr = Expression.binary_op("INT_AND", _param("param_1"), _const(0xFFFFFFF8))
    one_vn = _FakeVarnode("one", expr=_const(1))
    iv_entry_vn = _FakeVarnode("iv_entry", expr=start_expr)

    header = _FakeCfgBlock(0)
    latch = _FakeCfgBlock(1)
    header.add_edge(latch)
    latch.add_edge(header)

    iv_phi_vn = _FakeVarnode("iv_phi")
    iv_next_vn = _FakeVarnode("iv_next")
    aux_init_vn = _FakeVarnode("aux_init")
    aux_phi_vn = _FakeVarnode("aux_phi")
    aux_next_vn = _FakeVarnode("aux_next")

    iv_phi_op = _FakePcodeOp("MULTIEQUAL", [iv_entry_vn, iv_next_vn], iv_phi_vn)
    aux_init_op = _FakePcodeOp("INT_2COMP", [iv_entry_vn], aux_init_vn)
    aux_phi_op = _FakePcodeOp("MULTIEQUAL", [aux_init_vn, aux_next_vn], aux_phi_vn)
    header._ops[:] = [aux_phi_op, iv_phi_op]
    for op in header._ops:
        op.setParent(header)

    iv_next_op = _FakePcodeOp("INT_ADD", [iv_phi_vn, one_vn], iv_next_vn)
    aux_next_op = _FakePcodeOp("INT_SUB", [aux_phi_vn, one_vn], aux_next_vn)
    latch._ops[:] = [iv_next_op, aux_next_op]
    for op in latch._ops:
        op.setParent(latch)

    summarizer = StructuralRecurrenceSummarizer(_FakeTracer("unused", _const(0)), debug=False)
    induction = summarizer._match_counted_loop_induction(iv_phi_op)

    assert induction is not None
    aux_expr = summarizer._summarize_affine_loop_state_phi(aux_phi_op, induction)

    assert aux_expr is not None
    assert summarizer._extract_affine_term(aux_expr, "__loop_iv") == (-1, 0)


def test_structural_recurrence_summarizer_recovers_counted_scalar_loop_from_pcode_cfg():
    limit_expr = _param("param_1")
    zero_expr = _const(0)
    one_expr = _const(1)

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

    limit_vn = _FakeVarnode("limit", expr=limit_expr)
    zero_vn = _FakeVarnode("zero", expr=zero_expr)
    one_vn = _FakeVarnode("one", expr=one_expr)

    iv_phi_vn = _FakeVarnode("iv_phi")
    iv_next_vn = _FakeVarnode("iv_next")
    acc_phi_vn = _FakeVarnode("acc_phi")
    acc_merge_vn = _FakeVarnode("acc_merge")
    acc_even_vn = _FakeVarnode("acc_even")
    acc_odd_vn = _FakeVarnode("acc_odd")
    header_cond_vn = _FakeVarnode("header_cond", size=1)
    parity_and_vn = _FakeVarnode("parity_and")
    parity_cond_vn = _FakeVarnode("parity_cond", size=1)

    iv_phi_op = _FakePcodeOp("MULTIEQUAL", [zero_vn, iv_next_vn], iv_phi_vn)
    acc_phi_op = _FakePcodeOp("MULTIEQUAL", [zero_vn, acc_merge_vn], acc_phi_vn)
    header_cmp_op = _FakePcodeOp("INT_SLESS", [iv_phi_vn, limit_vn], header_cond_vn)
    header_branch = _FakePcodeOp("CBRANCH", [_FakeVarnode("header_target"), header_cond_vn], None)
    header._ops[:] = [iv_phi_op, acc_phi_op, header_cmp_op, header_branch]
    for op in header._ops:
        op.setParent(header)

    parity_and_op = _FakePcodeOp("INT_AND", [iv_phi_vn, one_vn], parity_and_vn)
    parity_cmp_op = _FakePcodeOp("INT_NOTEQUAL", [parity_and_vn, zero_vn], parity_cond_vn)
    body_branch = _FakePcodeOp("CBRANCH", [_FakeVarnode("body_target"), parity_cond_vn], None)
    body._ops[:] = [parity_and_op, parity_cmp_op, body_branch]
    for op in body._ops:
        op.setParent(body)

    acc_even_op = _FakePcodeOp("INT_ADD", [acc_phi_vn, iv_phi_vn], acc_even_vn)
    even_block._ops[:] = [acc_even_op]
    acc_even_op.setParent(even_block)

    acc_odd_op = _FakePcodeOp("INT_SUB", [acc_phi_vn, iv_phi_vn], acc_odd_vn)
    odd_block._ops[:] = [acc_odd_op]
    acc_odd_op.setParent(odd_block)

    acc_merge_op = _FakePcodeOp("MULTIEQUAL", [acc_even_vn, acc_odd_vn], acc_merge_vn)
    iv_next_op = _FakePcodeOp("INT_ADD", [iv_phi_vn, one_vn], iv_next_vn)
    latch._ops[:] = [acc_merge_op, iv_next_op]
    for op in latch._ops:
        op.setParent(latch)

    analysis = create_mock_analysis(
        "branch_for_accumulate",
        return_type="int",
        parameters=[{"name": "param_1", "index": 0, "data_type": "int", "size": 4, "is_signed": True}],
        returns=[
            ReturnInfo(
                address="0x1000",
                value=_const(0),
                conditions=[_cond("INT_SLESS", _const(0), _param("param_1"), negated=True)],
            ),
            ReturnInfo(
                address="0x1004",
                value=Expression.binary_op("INT_ADD", Expression.unknown("phi_circular"), _const(0)),
                conditions=[_cond("INT_SLESS", _const(0), _param("param_1"))],
            ),
        ],
    )

    summarizer = StructuralRecurrenceSummarizer(_FakeTracer("unused", _const(0)), debug=False)
    summary = summarizer.try_summarize_function(
        _FakeFunction("branch_for_accumulate"),
        _FakeCfgHighFunction([preheader, header, body, even_block, odd_block, latch, exit_block]),
        analysis,
    )

    assert summary is not None
    summarized_returns, note = summary
    assert note == "counted_scalar_loop_summary"
    assert len(summarized_returns) == 2
    assert all(expression_has_unresolved_value(ret.value) is False for ret in summarized_returns)
    loop_case = next(ret for ret in summarized_returns if ret.conditions and ret.conditions[0].to_string() == "(0 < param_1)")
    loop_smt = expression_to_smt(loop_case.value)
    assert "rtunk_" not in loop_smt
    assert "ite" in loop_smt


def test_structural_recurrence_summarizer_accepts_masked_counter_recursion():
    param = _param(size=8)
    masked_param = Expression.binary_op("INT_AND", param, _const(0xFFFFFFFF, size=8))
    unknown = Expression.unknown(
        "call_out_of_scope:fc_recursive_sum",
        runtime_ref=UnknownValueRef.out_of_scope_call(
            reason="call_out_of_scope",
            target_ref=CallTargetRef.from_name("fc_recursive_sum"),
            display_hint="fc_recursive_sum",
        ),
    )
    recursive_value = Expression.binary_op("INT_ADD", unknown, masked_param)
    analysis = create_mock_analysis(
        "fc_recursive_sum",
        return_type="int",
        parameters=[{"name": "param_1", "index": 0, "data_type": "int", "size": 8}],
        returns=[
            ReturnInfo(address="0x1000", value=_const(0), conditions=[]),
            ReturnInfo(
                address="0x1004",
                value=recursive_value,
                conditions=[_cond("INT_SLESS", _const(0), param)],
            ),
        ],
    )
    summarizer = StructuralRecurrenceSummarizer(
        _FakeTracer(
            "fc_recursive_sum",
            Expression.binary_op("INT_ADD", masked_param, _const(0xFFFFFFFF, size=8)),
        ),
        debug=False,
    )

    summary = summarizer.try_summarize_function(
        _FakeFunction("fc_recursive_sum"),
        _FakeHighFunction([
            _FakeCallOp(
                "fc_recursive_sum",
                Expression.binary_op("INT_ADD", masked_param, _const(0xFFFFFFFF, size=8)),
            ),
        ]),
        analysis,
    )

    assert summary is not None
    summarized_returns, note = summary
    assert note == "linear_self_recursion_summary"
    assert all("call_out_of_scope" not in ret.value.to_string() for ret in summarized_returns)
    recursive_case = next(ret for ret in summarized_returns if ret.value.to_string() != "0")
    assert "param_1" in recursive_case.value.to_string()


def test_structural_recurrence_summarizer_accepts_reconstructed_guard_counter():
    param = _param(size=4)
    high_fragment = Expression.variable("in_a0_hi", size=4)
    reconstructed_param = Expression.binary_op(
        "INT_OR",
        Expression.binary_op("INT_LEFT", high_fragment, _const(32)),
        param,
    )
    unknown = Expression.unknown(
        "call_out_of_scope:fc_recursive_sum",
        runtime_ref=UnknownValueRef.out_of_scope_call(
            reason="call_out_of_scope",
            target_ref=CallTargetRef.from_name("fc_recursive_sum"),
            display_hint="fc_recursive_sum",
        ),
    )
    recursive_value = Expression.binary_op("INT_ADD", unknown, param)
    analysis = create_mock_analysis(
        "fc_recursive_sum",
        return_type="int",
        parameters=[{"name": "param_1", "index": 0, "data_type": "int", "size": 4}],
        returns=[
            ReturnInfo(
                address="0x1004",
                value=recursive_value,
                conditions=[_cond("INT_SLESS", reconstructed_param, _const(1), negated=True)],
            ),
            ReturnInfo(
                address="0x1000",
                value=_const(0),
                conditions=[_cond("INT_SLESS", reconstructed_param, _const(1))],
            ),
        ],
    )
    summarizer = StructuralRecurrenceSummarizer(
        _FakeTracer(
            "fc_recursive_sum",
            Expression.binary_op("INT_ADD", param, _const(0xFFFFFFFF)),
        ),
        debug=False,
    )

    summary = summarizer.try_summarize_function(
        _FakeFunction("fc_recursive_sum"),
        _FakeHighFunction([
            _FakeCallOp("fc_recursive_sum", Expression.binary_op("INT_ADD", param, _const(0xFFFFFFFF))),
        ]),
        analysis,
    )

    assert summary is not None
    summarized_returns, note = summary
    assert note == "linear_self_recursion_summary"
    assert all("call_out_of_scope" not in ret.value.to_string() for ret in summarized_returns)
    recursive_case = next(ret for ret in summarized_returns if ret.value.to_string() != "0")
    assert recursive_case.conditions[0].to_string() == "(0 < param_1)"


def test_structural_recurrence_summary_uses_widened_closed_form():
    param = _param()
    unknown = Expression.unknown(
        "call_out_of_scope:fc_recursive_sum",
        runtime_ref=UnknownValueRef.out_of_scope_call(
            reason="call_out_of_scope",
            target_ref=CallTargetRef.from_name("fc_recursive_sum"),
            display_hint="fc_recursive_sum",
        ),
    )
    recursive_value = Expression.binary_op("INT_ADD", unknown, param)
    analysis = create_mock_analysis(
        "fc_recursive_sum",
        return_type="int",
        parameters=[{"name": "param_1", "index": 0, "data_type": "int", "size": 4}],
        returns=[
            ReturnInfo(address="0x1000", value=_const(0), conditions=[]),
            ReturnInfo(
                address="0x1004",
                value=recursive_value,
                conditions=[_cond("INT_SLESS", _const(0), param)],
            ),
        ],
    )
    summarizer = StructuralRecurrenceSummarizer(
        _FakeTracer(
            "fc_recursive_sum",
            Expression.binary_op("INT_SUB", param, _const(1)),
        ),
        debug=False,
    )

    summary = summarizer.try_summarize_function(
        _FakeFunction("fc_recursive_sum"),
        _FakeHighFunction([
            _FakeCallOp("fc_recursive_sum", Expression.binary_op("INT_SUB", param, _const(1))),
        ]),
        analysis,
    )

    assert summary is not None
    summarized_returns, _ = summary
    recursive_case = next(ret for ret in summarized_returns if ret.value.to_string() != "0")
    recursive_smt = recursive_case.value.to_smt()
    assert "zero_extend" in recursive_smt
    assert "extract 31 0" in recursive_smt
    assert "(bvmul ((_ zero_extend" in recursive_smt


def test_stable_op_key_collapses_distinct_wrappers_for_same_logical_pcode():
    tracer = object.__new__(PcodeTracer)

    class _FakeOp:
        def __init__(self):
            self._seq = _FakeSeqNum("ram:00001000", 0)
            self._output = _FakeOutput(offset=0x24, size=4)

        def getSeqnum(self):
            return self._seq

        def getMnemonic(self):
            return "MULTIEQUAL"

        def getOutput(self):
            return self._output

    op1 = _FakeOp()
    op2 = _FakeOp()

    assert tracer._get_stable_op_key(op1) == tracer._get_stable_op_key(op2)
    assert tracer._get_op_key(op1) != tracer._get_op_key(op2)


def _mem(base_name: str, offset: int = 0) -> Expression:
    base = Expression.parameter(base_name, index=0, data_type="int *", size=8)
    if offset == 0:
        return Expression.memory(base, size=4)
    return Expression.memory(
        Expression.binary_op("INT_ADD", base, Expression.constant(offset, size=8)),
        size=4,
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


def test_structural_recurrence_summarizer_recovers_branch_accumulator_loop_summary():
    params = [
        {"name": "trace", "index": 0, "data_type": "int *", "size": 8},
        {"name": "start", "index": 1, "data_type": "int", "size": 4, "is_signed": True},
        {"name": "limit", "index": 2, "data_type": "int", "size": 4, "is_signed": True},
    ]
    base_expr = Expression.binary_op("INT_ADD", _mem("trace", 0), _mem("trace", 4))
    null_case = ReturnInfo(
        address="0x1000",
        value=Expression.constant(-100, size=4),
        conditions=[_cond("INT_EQUAL", Expression.parameter("trace", 0, size=8), Expression.constant(0, size=8))],
    )
    base_case = ReturnInfo(
        address="0x1004",
        value=base_expr,
        conditions=[
            _cond("INT_NOTEQUAL", Expression.parameter("trace", 0, size=8), Expression.constant(0, size=8)),
            _cond("INT_SLESS", _param("start"), _param("limit"), negated=True),
        ],
    )
    even_step = ReturnInfo(
        address="0x1008",
        value=Expression.binary_op("INT_ADD", base_expr, Expression.binary_op("INT_ADD", _param("start"), _const(1))),
        conditions=[
            _cond("INT_NOTEQUAL", Expression.parameter("trace", 0, size=8), Expression.constant(0, size=8)),
            _cond("INT_SLESS", _param("start"), _param("limit")),
            _cond("INT_EQUAL", Expression.binary_op("INT_AND", _param("start"), _const(1)), _const(0)),
            _cond("INT_EQUAL", _param("limit"), Expression.binary_op("INT_ADD", _param("start"), _const(1))),
        ],
    )
    odd_step = ReturnInfo(
        address="0x100c",
        value=Expression.binary_op("INT_ADD", base_expr, Expression.binary_op("INT_ADD", Expression.unary_op("INT_2COMP", _param("start")), _const(1))),
        conditions=[
            _cond("INT_NOTEQUAL", Expression.parameter("trace", 0, size=8), Expression.constant(0, size=8)),
            _cond("INT_SLESS", _param("start"), _param("limit")),
            _cond("INT_EQUAL", Expression.binary_op("INT_AND", _param("start"), _const(1)), _const(0), negated=True),
            _cond("INT_EQUAL", _param("limit"), Expression.binary_op("INT_ADD", _param("start"), _const(1))),
        ],
    )
    analysis = create_mock_analysis(
        "lr_loop_with_side_effect",
        return_type="int",
        parameters=params,
        returns=[null_case, base_case, even_step, odd_step],
    )
    analysis.effect_summary = EffectSummary(parameter_names=["trace", "start", "limit"], effects=[])

    summarizer = StructuralRecurrenceSummarizer(_FakeTracer("unused", _const(0)), debug=False)
    summary = summarizer.try_summarize_function(
        _FakeFunction("lr_loop_with_side_effect"),
        _FakeHighFunction([]),
        analysis,
    )

    assert summary is not None
    summarized_returns, note = summary
    assert note == "counted_loop_branch_accumulator_summary"
    assert len(summarized_returns) == 4
    loop_cases = [
        ret
        for ret in summarized_returns
        if any(cond.to_string() == "(start < limit)" for cond in ret.conditions)
    ]
    assert len(loop_cases) == 2
    assert any("((start & 1) == 0)" in cond.to_string() for ret in loop_cases for cond in ret.conditions)
    assert any("not ((start & 1) == 0)" in cond.to_string() for ret in loop_cases for cond in ret.conditions)


def test_structural_recurrence_summarizer_synthesizes_missing_one_step_cases_from_effects():
    params = [
        {"name": "trace", "index": 0, "data_type": "int *", "size": 8},
        {"name": "start", "index": 1, "data_type": "int", "size": 4, "is_signed": True},
        {"name": "limit", "index": 2, "data_type": "int", "size": 4, "is_signed": True},
    ]
    trace_param = Expression.parameter("trace", index=0, data_type="int *", size=8)
    base_expr = Expression.binary_op("INT_ADD", _mem("trace", 0), _mem("trace", 4))
    analysis = create_mock_analysis(
        "lr_loop_with_side_effect",
        return_type="int",
        parameters=params,
        returns=[
            ReturnInfo(
                address="0x1000",
                value=Expression.constant(-100, size=4),
                conditions=[_cond("INT_EQUAL", trace_param, Expression.constant(0, size=8))],
            ),
            ReturnInfo(
                address="0x1004",
                value=base_expr,
                conditions=[
                    _cond("INT_NOTEQUAL", trace_param, Expression.constant(0, size=8)),
                    _cond("INT_SLESS", _param("start"), _param("limit"), negated=True),
                ],
            ),
        ],
    )
    even_conditions = [
        _cond("INT_NOTEQUAL", trace_param, Expression.constant(0, size=8)),
        _cond("INT_SLESS", _param("start"), _param("limit")),
        _cond("INT_EQUAL", Expression.binary_op("INT_AND", _param("start"), _const(1)), _const(0)),
    ]
    odd_conditions = [
        _cond("INT_NOTEQUAL", trace_param, Expression.constant(0, size=8)),
        _cond("INT_SLESS", _param("start"), _param("limit")),
        _cond("INT_EQUAL", Expression.binary_op("INT_AND", _param("start"), _const(1)), _const(0), negated=True),
    ]
    analysis.effect_summary = EffectSummary(
        parameter_names=["trace", "start", "limit"],
        effects=[
            StoreEffect(CanonicalLocation("trace", 0, 4), Expression.binary_op("INT_ADD", _mem("trace", 0), _param("start")), even_conditions, 1),
            StoreEffect(CanonicalLocation("trace", 4, 4), Expression.binary_op("INT_ADD", _mem("trace", 4), _const(1)), even_conditions, 2),
            StoreEffect(CanonicalLocation("trace", 0, 4), Expression.binary_op("INT_ADD", _mem("trace", 0), Expression.unary_op("INT_2COMP", _param("start"))), odd_conditions, 3),
            StoreEffect(CanonicalLocation("trace", 4, 4), Expression.binary_op("INT_ADD", _mem("trace", 4), _const(1)), odd_conditions, 4),
        ],
    )

    summarizer = StructuralRecurrenceSummarizer(_FakeTracer("unused", _const(0)), debug=False)
    summary = summarizer.try_summarize_function(
        _FakeFunction("lr_loop_with_side_effect"),
        _FakeHighFunction([]),
        analysis,
    )

    assert summary is not None
    summarized_returns, note = summary
    assert note == "counted_loop_branch_accumulator_summary"
    assert len(summarized_returns) == 4


def test_structural_recurrence_summarizer_accepts_swapped_lessequal_base_case():
    params = [
        {"name": "trace", "index": 0, "data_type": "int *", "size": 8},
        {"name": "start", "index": 1, "data_type": "int", "size": 4, "is_signed": True},
        {"name": "limit", "index": 2, "data_type": "int", "size": 4, "is_signed": True},
    ]
    trace_param = Expression.parameter("trace", index=0, data_type="int *", size=8)
    base_expr = Expression.binary_op("INT_ADD", _mem("trace", 0), _mem("trace", 4))
    analysis = create_mock_analysis(
        "lr_loop_with_side_effect",
        return_type="int",
        parameters=params,
        returns=[
            ReturnInfo(
                address="0x1000",
                value=Expression.constant(-100, size=4),
                conditions=[_cond("INT_EQUAL", trace_param, Expression.constant(0, size=8))],
            ),
            ReturnInfo(
                address="0x1004",
                value=base_expr,
                conditions=[
                    _cond("INT_NOTEQUAL", trace_param, Expression.constant(0, size=8)),
                    _cond("INT_SLESSEQUAL", _param("limit"), _param("start")),
                ],
            ),
        ],
    )
    even_conditions = [
        _cond("INT_NOTEQUAL", trace_param, Expression.constant(0, size=8)),
        _cond("INT_SLESS", _param("start"), _param("limit")),
        _cond("INT_EQUAL", Expression.binary_op("INT_AND", _param("start"), _const(1)), _const(0)),
    ]
    odd_conditions = [
        _cond("INT_NOTEQUAL", trace_param, Expression.constant(0, size=8)),
        _cond("INT_SLESS", _param("start"), _param("limit")),
        _cond("INT_EQUAL", Expression.binary_op("INT_AND", _param("start"), _const(1)), _const(0), negated=True),
    ]
    analysis.effect_summary = EffectSummary(
        parameter_names=["trace", "start", "limit"],
        effects=[
            StoreEffect(CanonicalLocation("trace", 0, 4), Expression.binary_op("INT_ADD", _mem("trace", 0), _param("start")), even_conditions, 1),
            StoreEffect(CanonicalLocation("trace", 4, 4), Expression.binary_op("INT_ADD", _mem("trace", 4), _const(1)), even_conditions, 2),
            StoreEffect(CanonicalLocation("trace", 0, 4), Expression.binary_op("INT_ADD", _mem("trace", 0), Expression.unary_op("INT_2COMP", _param("start"))), odd_conditions, 3),
            StoreEffect(CanonicalLocation("trace", 4, 4), Expression.binary_op("INT_ADD", _mem("trace", 4), _const(1)), odd_conditions, 4),
        ],
    )

    summarizer = StructuralRecurrenceSummarizer(_FakeTracer("unused", _const(0)), debug=False)
    summary = summarizer.try_summarize_function(
        _FakeFunction("lr_loop_with_side_effect"),
        _FakeHighFunction([]),
        analysis,
    )

    assert summary is not None
    summarized_returns, note = summary
    assert note == "counted_loop_branch_accumulator_summary"
    assert len(summarized_returns) == 4
    assert any(
        any(cond.to_string() == "(start < limit)" for cond in ret.conditions)
        for ret in summarized_returns
    )


def test_structural_recurrence_summarizer_infers_loop_pair_from_negated_lessequal_progress_guard():
    params = [
        {"name": "trace", "index": 0, "data_type": "int *", "size": 8},
        {"name": "start", "index": 1, "data_type": "int", "size": 4, "is_signed": True},
        {"name": "limit", "index": 2, "data_type": "int", "size": 4, "is_signed": True},
    ]
    base_expr = Expression.binary_op("INT_ADD", _mem("trace", 0), _mem("trace", 4))
    analysis = create_mock_analysis(
        "lr_loop_with_side_effect.part.0",
        return_type="int",
        parameters=params,
        returns=[
            ReturnInfo(
                address="0x1000",
                value=base_expr,
                conditions=[
                    _cond("INT_SLESSEQUAL", _param("limit"), _param("start")),
                ],
            ),
            ReturnInfo(
                address="0x1004",
                value=Expression.binary_op(
                    "INT_ADD",
                    Expression.binary_op("INT_ADD", _mem("trace", 4), _const(1)),
                    Expression.binary_op("INT_ADD", _mem("trace", 0), _param("start")),
                ),
                conditions=[
                    _cond("INT_SLESSEQUAL", _param("limit"), _param("start"), negated=True),
                    _cond("INT_EQUAL", Expression.binary_op("INT_AND", _param("start"), _const(1)), _const(0)),
                    _cond("INT_EQUAL", Expression.binary_op("INT_ADD", _param("start"), _const(1)), _param("limit")),
                ],
            ),
            ReturnInfo(
                address="0x1008",
                value=Expression.binary_op(
                    "INT_ADD",
                    Expression.binary_op("INT_ADD", _mem("trace", 4), _const(1)),
                    Expression.binary_op("INT_ADD", _mem("trace", 0), Expression.unary_op("INT_2COMP", _param("start"))),
                ),
                conditions=[
                    _cond("INT_SLESSEQUAL", _param("limit"), _param("start"), negated=True),
                    _cond("INT_EQUAL", Expression.binary_op("INT_AND", _param("start"), _const(1)), _const(0), negated=True),
                    _cond("INT_EQUAL", Expression.binary_op("INT_ADD", _param("start"), _const(1)), _param("limit")),
                ],
            ),
        ],
    )

    summarizer = StructuralRecurrenceSummarizer(_FakeTracer("unused", _const(0)), debug=False)
    assert summarizer._infer_loop_parameter_pair(analysis) == ("start", "limit")


def test_structural_recurrence_summarizer_synthesizes_effects_with_mul_wrapped_memory_offsets():
    params = [
        {"name": "param_1", "index": 0, "data_type": "int *", "size": 8},
        {"name": "param_2", "index": 1, "data_type": "int", "size": 4, "is_signed": True},
        {"name": "param_3", "index": 2, "data_type": "int", "size": 4, "is_signed": True},
    ]
    base_expr = Expression.binary_op("INT_ADD", _mem("param_1", 0), _mem("param_1", 4))
    trace_param = Expression.parameter("param_1", index=0, data_type="int *", size=8)
    analysis = create_mock_analysis(
        "lr_loop_with_side_effect",
        return_type="int",
        parameters=params,
        returns=[
            ReturnInfo(
                address="0x1000",
                value=Expression.constant(-100, size=4),
                conditions=[_cond("INT_EQUAL", trace_param, Expression.constant(0, size=8))],
            ),
            ReturnInfo(
                address="0x1004",
                value=base_expr,
                conditions=[
                    _cond("INT_NOTEQUAL", trace_param, Expression.constant(0, size=8)),
                    _cond("INT_SLESSEQUAL", _param("param_3"), _param("param_2")),
                ],
            ),
        ],
    )
    odd_conditions = [
        _cond("INT_NOTEQUAL", trace_param, Expression.constant(0, size=8)),
        _cond("INT_SLESS", _param("param_2"), _param("param_3")),
        _cond("INT_EQUAL", Expression.binary_op("INT_AND", _param("param_2"), _const(1)), _const(0), negated=True),
    ]
    even_conditions = [
        _cond("INT_NOTEQUAL", trace_param, Expression.constant(0, size=8)),
        _cond("INT_SLESS", _param("param_2"), _param("param_3")),
        _cond("INT_EQUAL", Expression.binary_op("INT_AND", _param("param_2"), _const(1)), _const(0)),
    ]
    analysis.effect_summary = EffectSummary(
        parameter_names=["param_1", "param_2", "param_3"],
        effects=[
            StoreEffect(
                CanonicalLocation("param_1", 0, 4),
                Expression.binary_op("INT_ADD", _mem("param_1", 0), Expression.unary_op("INT_2COMP", _param("param_2"))),
                odd_conditions,
                1,
            ),
            StoreEffect(
                CanonicalLocation("param_1", 4, 4),
                Expression.binary_op("INT_ADD", _mem_mul_offset("param_1", 4), _const(1)),
                odd_conditions,
                2,
            ),
            StoreEffect(
                CanonicalLocation("param_1", 0, 4),
                Expression.binary_op("INT_ADD", _mem("param_1", 0), _param("param_2")),
                even_conditions,
                3,
            ),
            StoreEffect(
                CanonicalLocation("param_1", 4, 4),
                Expression.binary_op("INT_ADD", _mem_mul_offset("param_1", 4), _const(1)),
                even_conditions,
                4,
            ),
        ],
    )

    summarizer = StructuralRecurrenceSummarizer(_FakeTracer("unused", _const(0)), debug=False)
    summary = summarizer.try_summarize_function(
        _FakeFunction("lr_loop_with_side_effect"),
        _FakeHighFunction([]),
        analysis,
    )

    assert summary is not None
    summarized_returns, note = summary
    assert note == "counted_loop_branch_accumulator_summary"
    assert len(summarized_returns) == 4


def test_structural_recurrence_summarizer_accepts_wrapper_guarded_helper_without_local_nonnull_check():
    params = [
        {"name": "param_1", "index": 0, "data_type": "int *", "size": 8},
        {"name": "param_2", "index": 1, "data_type": "int", "size": 4, "is_signed": True},
        {"name": "param_3", "index": 2, "data_type": "int", "size": 4, "is_signed": True},
    ]
    base_expr = Expression.binary_op("INT_ADD", _mem("param_1", 0), _mem("param_1", 4))
    analysis = create_mock_analysis(
        "lr_loop_with_side_effect.part.0",
        return_type="int",
        parameters=params,
        returns=[
            ReturnInfo(
                address="0x1004",
                value=base_expr,
                conditions=[
                    _cond("INT_SLESSEQUAL", _param("param_3"), _param("param_2")),
                ],
            ),
        ],
    )
    odd_conditions = [
        _cond("INT_SLESS", _param("param_2"), _param("param_3")),
        _cond("INT_EQUAL", Expression.binary_op("INT_AND", _param("param_2"), _const(1)), _const(0), negated=True),
    ]
    even_conditions = [
        _cond("INT_SLESS", _param("param_2"), _param("param_3")),
        _cond("INT_EQUAL", Expression.binary_op("INT_AND", _param("param_2"), _const(1)), _const(0)),
    ]
    analysis.effect_summary = EffectSummary(
        parameter_names=["param_1", "param_2", "param_3"],
        effects=[
            StoreEffect(
                CanonicalLocation("param_1", 0, 4),
                Expression.binary_op("INT_ADD", _mem("param_1", 0), Expression.unary_op("INT_2COMP", _param("param_2"))),
                odd_conditions,
                1,
            ),
            StoreEffect(
                CanonicalLocation("param_1", 4, 4),
                Expression.binary_op("INT_ADD", _mem("param_1", 4), _const(1)),
                odd_conditions,
                2,
            ),
            StoreEffect(
                CanonicalLocation("param_1", 0, 4),
                Expression.binary_op("INT_ADD", _mem("param_1", 0), _param("param_2")),
                even_conditions,
                3,
            ),
            StoreEffect(
                CanonicalLocation("param_1", 4, 4),
                Expression.binary_op("INT_ADD", _mem("param_1", 4), _const(1)),
                even_conditions,
                4,
            ),
        ],
    )

    summarizer = StructuralRecurrenceSummarizer(_FakeTracer("unused", _const(0)), debug=False)
    summary = summarizer.try_summarize_function(
        _FakeFunction("lr_loop_with_side_effect.part.0"),
        _FakeHighFunction([]),
        analysis,
    )

    assert summary is not None
    summarized_returns, note = summary
    assert note == "counted_loop_branch_accumulator_summary"
    assert len(summarized_returns) == 3
    assert any(
        any(cond.to_string() == "(param_2 < param_3)" for cond in ret.conditions)
        for ret in summarized_returns
    )


def test_structural_recurrence_summarizer_accepts_direct_notequal_odd_parity_conditions():
    params = [
        {"name": "param_1", "index": 0, "data_type": "int *", "size": 8},
        {"name": "param_2", "index": 1, "data_type": "int", "size": 4, "is_signed": True},
        {"name": "param_3", "index": 2, "data_type": "int", "size": 4, "is_signed": True},
    ]
    base_expr = Expression.binary_op("INT_ADD", _mem("param_1", 0), _mem("param_1", 4))
    analysis = create_mock_analysis(
        "lr_loop_with_side_effect.part.0",
        return_type="int",
        parameters=params,
        returns=[
            ReturnInfo(
                address="0x1004",
                value=base_expr,
                conditions=[
                    _cond("INT_SLESSEQUAL", _param("param_3"), _param("param_2")),
                ],
            ),
        ],
    )
    odd_conditions = [
        Condition(
            Expression.binary_op(
                "INT_EQUAL",
                Expression.parameter("param_1", index=0, data_type="int *", size=8),
                Expression.constant(0, size=8),
            ),
            True,
        ),
        _cond("INT_SLESS", _param("param_2"), _param("param_3")),
        Condition(
            Expression.binary_op(
                "INT_NOTEQUAL",
                Expression.binary_op("INT_AND", _param("param_2"), _const(1)),
                _const(0),
            ),
            False,
        ),
    ]
    even_conditions = [
        Condition(
            Expression.binary_op(
                "INT_EQUAL",
                Expression.parameter("param_1", index=0, data_type="int *", size=8),
                Expression.constant(0, size=8),
            ),
            True,
        ),
        _cond("INT_SLESS", _param("param_2"), _param("param_3")),
        _cond("INT_EQUAL", Expression.binary_op("INT_AND", _param("param_2"), _const(1)), _const(0)),
    ]
    analysis.effect_summary = EffectSummary(
        parameter_names=["param_1", "param_2", "param_3"],
        effects=[
            StoreEffect(
                CanonicalLocation("param_1", 0, 4),
                Expression.binary_op("INT_ADD", _mem("param_1", 0), Expression.unary_op("INT_2COMP", _param("param_2"))),
                odd_conditions,
                1,
            ),
            StoreEffect(
                CanonicalLocation("param_1", 4, 4),
                Expression.binary_op("INT_ADD", _mem_mul_offset("param_1", 4), _const(1)),
                odd_conditions,
                2,
            ),
            StoreEffect(
                CanonicalLocation("param_1", 0, 4),
                Expression.binary_op("INT_ADD", _mem("param_1", 0), _param("param_2")),
                even_conditions,
                3,
            ),
            StoreEffect(
                CanonicalLocation("param_1", 4, 4),
                Expression.binary_op("INT_ADD", _mem_mul_offset("param_1", 4), _const(1)),
                even_conditions,
                4,
            ),
        ],
    )

    summarizer = StructuralRecurrenceSummarizer(_FakeTracer("unused", _const(0)), debug=False)
    summary = summarizer.try_summarize_function(
        _FakeFunction("lr_loop_with_side_effect.part.0"),
        _FakeHighFunction([]),
        analysis,
    )

    assert summary is not None
    summarized_returns, note = summary
    assert note == "counted_loop_branch_accumulator_summary"
    assert len(summarized_returns) == 3
    assert any(
        any(cond.to_string() == "((param_2 & 1) != 0)" for cond in ret.conditions)
        or any(cond.to_string() == "(not ((param_2 & 1) == 0))" for cond in ret.conditions)
        for ret in summarized_returns
    )


def test_structural_recurrence_summarizer_reduces_phi_wrapped_store_effects_before_delta_extraction():
    params = [
        {"name": "param_1", "index": 0, "data_type": "int *", "size": 8},
        {"name": "param_2", "index": 1, "data_type": "int", "size": 4, "is_signed": True},
        {"name": "param_3", "index": 2, "data_type": "int", "size": 4, "is_signed": True},
    ]
    base_expr = Expression.binary_op("INT_ADD", _mem("param_1", 0), _mem("param_1", 4))
    analysis = create_mock_analysis(
        "lr_loop_with_side_effect.part.0",
        return_type="int",
        parameters=params,
        returns=[
            ReturnInfo(
                address="0x1004",
                value=base_expr,
                conditions=[
                    _cond("INT_SLESSEQUAL", _param("param_3"), _param("param_2")),
                ],
            ),
        ],
    )

    odd_conditions = [
        _cond("INT_SLESS", _param("param_2"), _param("param_3")),
        Condition(
            Expression.binary_op(
                "INT_NOTEQUAL",
                Expression.binary_op("INT_AND", _param("param_2"), _const(1)),
                _const(0),
            ),
            False,
        ),
    ]
    even_conditions = [
        _cond("INT_SLESS", _param("param_2"), _param("param_3")),
        _cond("INT_EQUAL", Expression.binary_op("INT_AND", _param("param_2"), _const(1)), _const(0)),
    ]
    step_notequal = Condition(
        Expression.binary_op(
            "INT_NOTEQUAL",
            Expression.binary_op("INT_ADD", _param("param_2"), _const(1)),
            _param("param_3"),
        ),
        False,
    )

    odd_phi_base = Expression.phi(
        [
            (_cond("INT_SLESS", _param("param_2"), _param("param_3")), _mem("param_1", 0)),
            (step_notequal, Expression.unknown("phi_circular_odd")),
        ]
    )
    odd_phi_base.size = 4
    even_phi_base = Expression.phi(
        [
            (_cond("INT_SLESS", _param("param_2"), _param("param_3")), _mem("param_1", 0)),
            (step_notequal, Expression.unknown("phi_circular_even")),
        ]
    )
    even_phi_base.size = 4

    analysis.effect_summary = EffectSummary(
        parameter_names=["param_1", "param_2", "param_3"],
        effects=[
            StoreEffect(
                CanonicalLocation("param_1", 0, 4),
                Expression.binary_op(
                    "INT_ADD",
                    odd_phi_base,
                    Expression.unary_op("INT_2COMP", _param("param_2")),
                ),
                odd_conditions,
                1,
            ),
            StoreEffect(
                CanonicalLocation("param_1", 4, 4),
                Expression.binary_op("INT_ADD", _mem_mul_offset("param_1", 4), _const(1)),
                odd_conditions,
                2,
            ),
            StoreEffect(
                CanonicalLocation("param_1", 0, 4),
                Expression.binary_op("INT_ADD", even_phi_base, _param("param_2")),
                even_conditions,
                3,
            ),
            StoreEffect(
                CanonicalLocation("param_1", 4, 4),
                Expression.binary_op("INT_ADD", _mem_mul_offset("param_1", 4), _const(1)),
                even_conditions,
                4,
            ),
        ],
    )

    summarizer = StructuralRecurrenceSummarizer(_FakeTracer("unused", _const(0)), debug=False)
    summary = summarizer.try_summarize_function(
        _FakeFunction("lr_loop_with_side_effect.part.0"),
        _FakeHighFunction([]),
        analysis,
    )

    assert summary is not None
    summarized_returns, note = summary
    assert note == "counted_loop_branch_accumulator_summary"
    assert len(summarized_returns) == 3


def test_structural_recurrence_summarizer_recovers_readonly_pointer_reduction_summary():
    params = [
        {"name": "param_1", "index": 0, "data_type": "int *", "size": 8},
        {"name": "param_2", "index": 1, "data_type": "int", "size": 4, "is_signed": True},
    ]
    analysis = create_mock_analysis(
        "ptr_sum_window",
        return_type="int",
        parameters=params,
        returns=[
            ReturnInfo(
                address="0x1000",
                value=_const(-300),
                conditions=[
                    _cond(
                        "INT_EQUAL",
                        Expression.parameter("param_1", index=0, data_type="int *", size=8),
                        Expression.constant(0, size=8),
                    )
                ],
            ),
            ReturnInfo(
                address="0x1004",
                value=_const(-300),
                conditions=[
                    _cond(
                        "INT_NOTEQUAL",
                        Expression.parameter("param_1", index=0, data_type="int *", size=8),
                        Expression.constant(0, size=8),
                    ),
                    _cond("INT_SLESSEQUAL", _param("param_2"), _const(0)),
                ],
            ),
            ReturnInfo(
                address="0x1008",
                value=Expression.unknown("phi_circular"),
                conditions=[
                    _cond(
                        "INT_NOTEQUAL",
                        Expression.parameter("param_1", index=0, data_type="int *", size=8),
                        Expression.constant(0, size=8),
                    ),
                    _cond("INT_SLESS", _const(0), _param("param_2")),
                ],
            ),
        ],
    )

    ptr_param = _FakeVarnode(
        "param_1",
        size=8,
        expr=Expression.parameter("param_1", index=0, data_type="int *", size=8),
    )
    count_param = _FakeVarnode(
        "param_2",
        size=4,
        expr=Expression.parameter("param_2", index=1, data_type="int", size=4),
    )
    zero32 = _FakeVarnode("zero32", size=4, expr=Expression.constant(0, 4))
    one32 = _FakeVarnode("one32", size=4, expr=Expression.constant(1, 4))
    four64 = _FakeVarnode("four64", size=8, expr=Expression.constant(4, 8))
    ram_space = _FakeVarnode("ram", size=8, expr=Expression.constant(0, 8))

    idx_high = _FakeHighVar("idx")
    idx_phi = _FakeVarnode("idx_phi", size=4, high=idx_high)
    idx_next = _FakeVarnode("idx_next", size=4)
    idx_add_op = _FakePcodeOp("INT_ADD", [idx_phi, one32], idx_next)
    idx_phi_op = _FakePcodeOp("MULTIEQUAL", [zero32, idx_next], idx_phi)

    addr = _FakeVarnode("addr", size=8)
    ptradd_op = _FakePcodeOp("PTRADD", [ptr_param, idx_phi, four64], addr)
    load_value = _FakeVarnode("load_value", size=4)
    load_op = _FakePcodeOp("LOAD", [ram_space, addr], load_value)

    acc_high = _FakeHighVar("acc")
    acc_phi = _FakeVarnode("acc_phi", size=4, high=acc_high)
    acc_next = _FakeVarnode("acc_next", size=4)
    acc_add_op = _FakePcodeOp("INT_ADD", [acc_phi, load_value], acc_next)
    acc_phi_op = _FakePcodeOp("MULTIEQUAL", [zero32, acc_next], acc_phi)

    high_function = _FakeHighFunction([idx_add_op, idx_phi_op, ptradd_op, load_op, acc_add_op, acc_phi_op])
    tracer = _FakeTracer("unused", _const(0))
    tracer.trace_varnode = lambda varnode, *args, **kwargs: getattr(varnode, "_expr", None)

    summarizer = StructuralRecurrenceSummarizer(tracer, debug=False)
    summary = summarizer.try_summarize_function(
        _FakeFunction("ptr_sum_window"),
        high_function,
        analysis,
    )

    assert summary is not None
    summarized_returns, note = summary
    assert note == "readonly_pointer_reduction_summary"
    assert len(summarized_returns) == 3
    positive_case = next(ret for ret in summarized_returns if ret.value.expr_type == ret.value.expr_type.__class__.INTRINSIC)
    assert positive_case.value.opcode == READONLY_SUM_OPCODE
    assert isinstance(positive_case.value.runtime_ref, ReadonlyReductionRef)
    assert positive_case.value.runtime_ref.stride == 4
    assert positive_case.value.runtime_ref.element_size == 4
    assert positive_case.conditions[0].to_string() == "(param_1 != 0)"
    assert positive_case.conditions[1].to_string() == "(0 < param_2)"


def test_structural_recurrence_summarizer_candidate_probe_rejects_plain_memory_return():
    analysis = create_mock_analysis(
        "plain_load",
        return_type="int",
        parameters=[
            {"name": "param_1", "index": 0, "data_type": "int *", "size": 8},
            {"name": "param_2", "index": 1, "data_type": "int", "size": 4, "is_signed": True},
        ],
        returns=[
            ReturnInfo(
                address="0x1000",
                value=Expression.memory(
                    Expression.parameter("param_1", index=0, data_type="int *", size=8),
                    size=4,
                ),
                conditions=[],
            ),
        ],
    )

    summarizer = StructuralRecurrenceSummarizer(_FakeTracer("unused", _const(0)), debug=False)

    assert (
        summarizer.has_summary_candidate(
            _FakeFunction("plain_load"),
            _FakeHighFunction([]),
            analysis,
        )
        is False
    )


def test_structural_recurrence_summarizer_candidate_probe_accepts_readonly_reduction_shape():
    params = [
        {"name": "param_1", "index": 0, "data_type": "int *", "size": 8},
        {"name": "param_2", "index": 1, "data_type": "int", "size": 4, "is_signed": True},
    ]
    analysis = create_mock_analysis(
        "ptr_sum_window",
        return_type="int",
        parameters=params,
        returns=[
            ReturnInfo(
                address="0x1000",
                value=_const(-300),
                conditions=[
                    _cond(
                        "INT_EQUAL",
                        Expression.parameter("param_1", index=0, data_type="int *", size=8),
                        Expression.constant(0, size=8),
                    )
                ],
            ),
            ReturnInfo(
                address="0x1004",
                value=_const(-300),
                conditions=[
                    _cond(
                        "INT_NOTEQUAL",
                        Expression.parameter("param_1", index=0, data_type="int *", size=8),
                        Expression.constant(0, size=8),
                    ),
                    _cond("INT_SLESSEQUAL", _param("param_2"), _const(0)),
                ],
            ),
            ReturnInfo(
                address="0x1008",
                value=Expression.unknown("phi_circular"),
                conditions=[
                    _cond(
                        "INT_NOTEQUAL",
                        Expression.parameter("param_1", index=0, data_type="int *", size=8),
                        Expression.constant(0, size=8),
                    ),
                    _cond("INT_SLESS", _const(0), _param("param_2")),
                ],
            ),
        ],
    )

    ptr_param = _FakeVarnode(
        "param_1",
        size=8,
        expr=Expression.parameter("param_1", index=0, data_type="int *", size=8),
    )
    zero32 = _FakeVarnode("zero32", size=4, expr=Expression.constant(0, 4))
    one32 = _FakeVarnode("one32", size=4, expr=Expression.constant(1, 4))
    four64 = _FakeVarnode("four64", size=8, expr=Expression.constant(4, 8))
    ram_space = _FakeVarnode("ram", size=8, expr=Expression.constant(0, 8))

    idx_high = _FakeHighVar("idx")
    idx_phi = _FakeVarnode("idx_phi", size=4, high=idx_high)
    idx_next = _FakeVarnode("idx_next", size=4)
    _FakePcodeOp("INT_ADD", [idx_phi, one32], idx_next)
    idx_phi_op = _FakePcodeOp("MULTIEQUAL", [zero32, idx_next], idx_phi)

    addr = _FakeVarnode("addr", size=8)
    ptradd_op = _FakePcodeOp("PTRADD", [ptr_param, idx_phi, four64], addr)
    load_value = _FakeVarnode("load_value", size=4)
    load_op = _FakePcodeOp("LOAD", [ram_space, addr], load_value)

    acc_high = _FakeHighVar("acc")
    acc_phi = _FakeVarnode("acc_phi", size=4, high=acc_high)
    acc_next = _FakeVarnode("acc_next", size=4)
    acc_add_op = _FakePcodeOp("INT_ADD", [acc_phi, load_value], acc_next)
    acc_phi_op = _FakePcodeOp("MULTIEQUAL", [zero32, acc_next], acc_phi)

    high_function = _FakeHighFunction([idx_phi_op, ptradd_op, load_op, acc_add_op, acc_phi_op])
    tracer = _FakeTracer("unused", _const(0))
    tracer.trace_varnode = lambda varnode, *args, **kwargs: getattr(varnode, "_expr", None)

    summarizer = StructuralRecurrenceSummarizer(tracer, debug=False)

    assert summarizer.has_summary_candidate(_FakeFunction("ptr_sum_window"), high_function, analysis) is True


def test_structural_recurrence_summarizer_recovers_readonly_reduction_from_affine_exact_count_case():
    params = [
        {"name": "param_1", "index": 0, "data_type": "long", "size": 8},
        {"name": "param_2", "index": 1, "data_type": "uint", "size": 4, "is_signed": False},
    ]
    count_param = Expression.parameter("param_2", index=1, data_type="uint", size=4)
    widened_count = Expression.unary_op("INT_ZEXT", count_param)
    widened_count.size = 8
    exact_one_expr = Expression.binary_op(
        "INT_EQUAL",
        Expression.binary_op("INT_SUB", widened_count, Expression.constant(1, size=8)),
        Expression.constant(0, size=8),
    )
    analysis = create_mock_analysis(
        "ptr_sum_window",
        return_type="int",
        parameters=params,
        returns=[
            ReturnInfo(
                address="0x1000",
                value=_const(-300),
                conditions=[
                    _cond(
                        "INT_EQUAL",
                        Expression.parameter("param_1", index=0, data_type="long", size=8),
                        Expression.constant(0, size=8),
                    )
                ],
            ),
            ReturnInfo(
                address="0x1004",
                value=_const(-300),
                conditions=[
                    _cond(
                        "INT_NOTEQUAL",
                        Expression.parameter("param_1", index=0, data_type="long", size=8),
                        Expression.constant(0, size=8),
                    ),
                    _cond("INT_SLESSEQUAL", count_param, _const(0)),
                ],
            ),
            ReturnInfo(
                address="0x1008",
                value=Expression.binary_op("INT_ADD", _mem("param_1", 0), _const(0)),
                conditions=[
                    _cond(
                        "INT_NOTEQUAL",
                        Expression.parameter("param_1", index=0, data_type="long", size=8),
                        Expression.constant(0, size=8),
                    ),
                    _cond("INT_SLESS", _const(0), count_param),
                    _cond("INT_SLESS", count_param, _const(8)),
                    Condition(exact_one_expr, False),
                ],
            ),
        ],
    )

    summarizer = StructuralRecurrenceSummarizer(_FakeTracer("unused", _const(0)), debug=False)
    summary = summarizer.try_summarize_function(
        _FakeFunction("ptr_sum_window"),
        _FakeHighFunction([]),
        analysis,
    )

    assert summary is not None
    summarized_returns, note = summary
    assert note == "readonly_pointer_reduction_summary"
    assert len(summarized_returns) == 3
    positive_case = next(ret for ret in summarized_returns if ret.value.expr_type == ret.value.expr_type.__class__.INTRINSIC)
    assert positive_case.value.opcode == READONLY_SUM_OPCODE
    assert isinstance(positive_case.value.runtime_ref, ReadonlyReductionRef)
    assert positive_case.value.runtime_ref.stride == 4
    assert positive_case.value.runtime_ref.element_size == 4
    assert [cond.to_string() for cond in positive_case.conditions] == ["(param_1 != 0)", "(0 < param_2)"]


def test_structural_recurrence_summarizer_infers_pointer_parameter_object_centrically():
    params = [
        {"name": "param_1", "index": 0, "data_type": "long", "size": 8},
        {"name": "param_2", "index": 1, "data_type": "uint", "size": 4, "is_signed": False},
    ]
    analysis = create_mock_analysis(
        "ptr_sum_window",
        return_type="int",
        parameters=params,
        returns=[
            ReturnInfo(
                address="0x1000",
                value=_const(-300),
                conditions=[
                    _cond(
                        "INT_EQUAL",
                        Expression.parameter("param_1", index=0, data_type="long", size=8),
                        Expression.constant(0, size=8),
                    )
                ],
            ),
            ReturnInfo(
                address="0x1004",
                value=_const(-300),
                conditions=[
                    _cond(
                        "INT_NOTEQUAL",
                        Expression.parameter("param_1", index=0, data_type="long", size=8),
                        Expression.constant(0, size=8),
                    ),
                    _cond("INT_SLESSEQUAL", Expression.parameter("param_2", index=1, data_type="uint", size=4), _const(0)),
                ],
            ),
            ReturnInfo(
                address="0x1008",
                value=Expression.binary_op(
                    "INT_ADD",
                    _mem("param_1", 0),
                    Expression.unknown("phi_circular"),
                ),
                conditions=[
                    _cond(
                        "INT_NOTEQUAL",
                        Expression.parameter("param_1", index=0, data_type="long", size=8),
                        Expression.constant(0, size=8),
                    ),
                    _cond("INT_SLESS", _const(0), Expression.parameter("param_2", index=1, data_type="uint", size=4)),
                ],
            ),
        ],
    )

    ptr_param = _FakeVarnode(
        "param_1",
        size=8,
        expr=Expression.parameter("param_1", index=0, data_type="long", size=8),
    )
    count_param = _FakeVarnode(
        "param_2",
        size=4,
        expr=Expression.parameter("param_2", index=1, data_type="uint", size=4),
    )
    zero32 = _FakeVarnode("zero32", size=4, expr=Expression.constant(0, 4))
    one32 = _FakeVarnode("one32", size=4, expr=Expression.constant(1, 4))
    four64 = _FakeVarnode("four64", size=8, expr=Expression.constant(4, 8))
    ram_space = _FakeVarnode("ram", size=8, expr=Expression.constant(0, 8))

    idx_high = _FakeHighVar("idx")
    idx_phi = _FakeVarnode("idx_phi", size=4, high=idx_high)
    idx_next = _FakeVarnode("idx_next", size=4)
    idx_add_op = _FakePcodeOp("INT_ADD", [idx_phi, one32], idx_next)
    idx_phi_op = _FakePcodeOp("MULTIEQUAL", [zero32, idx_next], idx_phi)

    addr = _FakeVarnode("addr", size=8)
    ptradd_op = _FakePcodeOp("PTRADD", [ptr_param, idx_phi, four64], addr)
    load_value = _FakeVarnode("load_value", size=4)
    load_op = _FakePcodeOp("LOAD", [ram_space, addr], load_value)

    acc_high = _FakeHighVar("acc")
    acc_phi = _FakeVarnode("acc_phi", size=4, high=acc_high)
    acc_next = _FakeVarnode("acc_next", size=4)
    acc_add_op = _FakePcodeOp("INT_ADD", [acc_phi, load_value], acc_next)
    acc_phi_op = _FakePcodeOp("MULTIEQUAL", [zero32, acc_next], acc_phi)

    high_function = _FakeHighFunction([idx_add_op, idx_phi_op, ptradd_op, load_op, acc_add_op, acc_phi_op])
    tracer = _FakeTracer("unused", _const(0))
    tracer.trace_varnode = lambda varnode, *args, **kwargs: getattr(varnode, "_expr", None)

    summarizer = StructuralRecurrenceSummarizer(tracer, debug=False)
    summary = summarizer.try_summarize_function(
        _FakeFunction("ptr_sum_window"),
        high_function,
        analysis,
    )

    assert summary is not None
    summarized_returns, note = summary
    assert note == "readonly_pointer_reduction_summary"
    positive_case = next(ret for ret in summarized_returns if ret.value.expr_type == ret.value.expr_type.__class__.INTRINSIC)
    assert positive_case.value.runtime_ref.pointer_base_ref.parameter_index == 0
    assert positive_case.value.runtime_ref.count_parameter_index == 1
    assert [cond.to_string() for cond in positive_case.conditions] == ["(param_1 != 0)", "(0 < param_2)"]


def test_structural_recurrence_summarizer_recovers_readonly_pointer_reduction_from_prefix_returns():
    params = [
        {"name": "param_1", "index": 0, "data_type": "int *", "size": 8},
        {"name": "param_2", "index": 1, "data_type": "int", "size": 4, "is_signed": True},
    ]
    analysis = create_mock_analysis(
        "ptr_sum_window",
        return_type="int",
        parameters=params,
        returns=[
            ReturnInfo(
                address="0x1000",
                value=_const(-300),
                conditions=[
                    _cond(
                        "INT_EQUAL",
                        Expression.parameter("param_1", index=0, data_type="int *", size=8),
                        Expression.constant(0, size=8),
                    )
                ],
            ),
            ReturnInfo(
                address="0x1004",
                value=_const(-300),
                conditions=[
                    _cond(
                        "INT_NOTEQUAL",
                        Expression.parameter("param_1", index=0, data_type="int *", size=8),
                        Expression.constant(0, size=8),
                    ),
                    _cond("INT_SLESSEQUAL", _param("param_2"), _const(0)),
                ],
            ),
            ReturnInfo(
                address="0x1008",
                value=Expression.memory(
                    Expression.parameter("param_1", index=0, data_type="int *", size=8),
                    size=4,
                ),
                conditions=[
                    _cond(
                        "INT_NOTEQUAL",
                        Expression.parameter("param_1", index=0, data_type="int *", size=8),
                        Expression.constant(0, size=8),
                    ),
                    _cond("INT_EQUAL", _param("param_2"), _const(1)),
                ],
            ),
            ReturnInfo(
                address="0x100C",
                value=Expression.binary_op(
                    "INT_ADD",
                    Expression.memory(
                        Expression.parameter("param_1", index=0, data_type="int *", size=8),
                        size=4,
                    ),
                    Expression.memory(
                        Expression.binary_op(
                            "INT_ADD",
                            Expression.parameter("param_1", index=0, data_type="int *", size=8),
                            Expression.constant(4, size=8),
                        ),
                        size=4,
                    ),
                ),
                conditions=[
                    _cond(
                        "INT_NOTEQUAL",
                        Expression.parameter("param_1", index=0, data_type="int *", size=8),
                        Expression.constant(0, size=8),
                    ),
                    _cond("INT_EQUAL", _param("param_2"), _const(2)),
                ],
            ),
        ],
    )

    summarizer = StructuralRecurrenceSummarizer(_FakeTracer("unused", _const(0)), debug=False)
    summary = summarizer.try_summarize_function(
        _FakeFunction("ptr_sum_window"),
        _FakeHighFunction([]),
        analysis,
    )

    assert summary is not None
    summarized_returns, note = summary
    assert note == "readonly_pointer_reduction_summary"
    positive_case = next(ret for ret in summarized_returns if ret.value.expr_type == ret.value.expr_type.__class__.INTRINSIC)
    assert positive_case.value.opcode == READONLY_SUM_OPCODE
    assert positive_case.value.runtime_ref.stride == 4
    assert positive_case.value.runtime_ref.semantic_witnesses[:2] == (
        ReadonlyReductionWitness(
            exact_count=1,
            terms=(ReadonlyReductionTermRef(byte_offset=0, access_size=4),),
        ),
        ReadonlyReductionWitness(
            exact_count=2,
            terms=(
                ReadonlyReductionTermRef(byte_offset=0, access_size=4),
                ReadonlyReductionTermRef(byte_offset=4, access_size=4),
            ),
        ),
    )
    assert [w.exact_count for w in positive_case.value.runtime_ref.semantic_witnesses] == [1, 2, 3, 4]


def test_structural_recurrence_summarizer_synthesizes_linear_semantic_witnesses_for_simple_loop():
    params = [
        {"name": "param_1", "index": 0, "data_type": "int *", "size": 8},
        {"name": "param_2", "index": 1, "data_type": "int", "size": 4, "is_signed": True},
    ]
    analysis = create_mock_analysis(
        "ptr_sum_window",
        return_type="int",
        parameters=params,
        returns=[
            ReturnInfo(
                address="0x1000",
                value=_const(-300),
                conditions=[
                    _cond(
                        "INT_EQUAL",
                        Expression.parameter("param_1", index=0, data_type="int *", size=8),
                        Expression.constant(0, size=8),
                    )
                ],
            ),
            ReturnInfo(
                address="0x1004",
                value=_const(-300),
                conditions=[
                    _cond(
                        "INT_NOTEQUAL",
                        Expression.parameter("param_1", index=0, data_type="int *", size=8),
                        Expression.constant(0, size=8),
                    ),
                    _cond("INT_SLESSEQUAL", _param("param_2"), _const(0)),
                ],
            ),
            ReturnInfo(
                address="0x1008",
                value=Expression.binary_op(
                    "INT_ADD",
                    _mem("param_1", 0),
                    Expression.unknown("phi_circular"),
                ),
                conditions=[
                    _cond(
                        "INT_NOTEQUAL",
                        Expression.parameter("param_1", index=0, data_type="int *", size=8),
                        Expression.constant(0, size=8),
                    ),
                    _cond("INT_SLESS", _const(0), _param("param_2")),
                ],
            ),
        ],
    )

    ptr_param = _FakeVarnode(
        "param_1",
        size=8,
        expr=Expression.parameter("param_1", index=0, data_type="int *", size=8),
    )
    zero32 = _FakeVarnode("zero32", size=4, expr=Expression.constant(0, 4))
    one32 = _FakeVarnode("one32", size=4, expr=Expression.constant(1, 4))
    four64 = _FakeVarnode("four64", size=8, expr=Expression.constant(4, 8))
    ram_space = _FakeVarnode("ram", size=8, expr=Expression.constant(0, 8))

    idx_high = _FakeHighVar("idx")
    idx_phi = _FakeVarnode("idx_phi", size=4, high=idx_high)
    idx_next = _FakeVarnode("idx_next", size=4)
    idx_add_op = _FakePcodeOp("INT_ADD", [idx_phi, one32], idx_next)
    idx_phi_op = _FakePcodeOp("MULTIEQUAL", [zero32, idx_next], idx_phi)

    addr = _FakeVarnode("addr", size=8)
    ptradd_op = _FakePcodeOp("PTRADD", [ptr_param, idx_phi, four64], addr)
    load_value = _FakeVarnode("load_value", size=4)
    load_op = _FakePcodeOp("LOAD", [ram_space, addr], load_value)

    acc_high = _FakeHighVar("acc")
    acc_phi = _FakeVarnode("acc_phi", size=4, high=acc_high)
    acc_next = _FakeVarnode("acc_next", size=4)
    acc_add_op = _FakePcodeOp("INT_ADD", [acc_phi, load_value], acc_next)
    acc_phi_op = _FakePcodeOp("MULTIEQUAL", [zero32, acc_next], acc_phi)

    high_function = _FakeHighFunction([idx_add_op, idx_phi_op, ptradd_op, load_op, acc_add_op, acc_phi_op])
    tracer = _FakeTracer("unused", _const(0))
    tracer.trace_varnode = lambda varnode, *args, **kwargs: getattr(varnode, "_expr", None)

    summarizer = StructuralRecurrenceSummarizer(tracer, debug=False)
    summary = summarizer.try_summarize_function(
        _FakeFunction("ptr_sum_window"),
        high_function,
        analysis,
    )

    assert summary is not None
    summarized_returns, note = summary
    assert note == "readonly_pointer_reduction_summary"
    positive_case = next(ret for ret in summarized_returns if ret.value.expr_type == ret.value.expr_type.__class__.INTRINSIC)
    assert positive_case.value.runtime_ref.semantic_witnesses[:2] == (
        ReadonlyReductionWitness(
            exact_count=1,
            terms=(ReadonlyReductionTermRef(byte_offset=0, access_size=4),),
        ),
        ReadonlyReductionWitness(
            exact_count=2,
            terms=(
                ReadonlyReductionTermRef(byte_offset=0, access_size=4),
                ReadonlyReductionTermRef(byte_offset=4, access_size=4),
            ),
        ),
    )


def test_structural_recurrence_summarizer_merges_exact_and_synthesized_semantic_witnesses():
    params = [
        {"name": "param_1", "index": 0, "data_type": "int *", "size": 8},
        {"name": "param_2", "index": 1, "data_type": "int", "size": 4, "is_signed": True},
    ]
    analysis = create_mock_analysis(
        "ptr_sum_window",
        return_type="int",
        parameters=params,
        returns=[
            ReturnInfo(
                address="0x1000",
                value=_const(-300),
                conditions=[
                    _cond(
                        "INT_EQUAL",
                        Expression.parameter("param_1", index=0, data_type="int *", size=8),
                        Expression.constant(0, size=8),
                    )
                ],
            ),
            ReturnInfo(
                address="0x1004",
                value=_const(-300),
                conditions=[
                    _cond(
                        "INT_NOTEQUAL",
                        Expression.parameter("param_1", index=0, data_type="int *", size=8),
                        Expression.constant(0, size=8),
                    ),
                    _cond("INT_SLESSEQUAL", _param("param_2"), _const(0)),
                ],
            ),
            ReturnInfo(
                address="0x1008",
                value=_mem("param_1", 0),
                conditions=[
                    _cond(
                        "INT_NOTEQUAL",
                        Expression.parameter("param_1", index=0, data_type="int *", size=8),
                        Expression.constant(0, size=8),
                    ),
                    _cond("INT_EQUAL", _param("param_2"), _const(1)),
                ],
            ),
            ReturnInfo(
                address="0x100C",
                value=Expression.binary_op(
                    "INT_ADD",
                    _mem("param_1", 0),
                    Expression.unknown("phi_circular"),
                ),
                conditions=[
                    _cond(
                        "INT_NOTEQUAL",
                        Expression.parameter("param_1", index=0, data_type="int *", size=8),
                        Expression.constant(0, size=8),
                    ),
                    _cond("INT_SLESS", _const(0), _param("param_2")),
                ],
            ),
        ],
    )

    ptr_param = _FakeVarnode(
        "param_1",
        size=8,
        expr=Expression.parameter("param_1", index=0, data_type="int *", size=8),
    )
    zero32 = _FakeVarnode("zero32", size=4, expr=Expression.constant(0, 4))
    one32 = _FakeVarnode("one32", size=4, expr=Expression.constant(1, 4))
    four64 = _FakeVarnode("four64", size=8, expr=Expression.constant(4, 8))
    ram_space = _FakeVarnode("ram", size=8, expr=Expression.constant(0, 8))

    idx_high = _FakeHighVar("idx")
    idx_phi = _FakeVarnode("idx_phi", size=4, high=idx_high)
    idx_next = _FakeVarnode("idx_next", size=4)
    idx_add_op = _FakePcodeOp("INT_ADD", [idx_phi, one32], idx_next)
    idx_phi_op = _FakePcodeOp("MULTIEQUAL", [zero32, idx_next], idx_phi)

    addr = _FakeVarnode("addr", size=8)
    ptradd_op = _FakePcodeOp("PTRADD", [ptr_param, idx_phi, four64], addr)
    load_value = _FakeVarnode("load_value", size=4)
    load_op = _FakePcodeOp("LOAD", [ram_space, addr], load_value)

    acc_high = _FakeHighVar("acc")
    acc_phi = _FakeVarnode("acc_phi", size=4, high=acc_high)
    acc_next = _FakeVarnode("acc_next", size=4)
    acc_add_op = _FakePcodeOp("INT_ADD", [acc_phi, load_value], acc_next)
    acc_phi_op = _FakePcodeOp("MULTIEQUAL", [zero32, acc_next], acc_phi)

    high_function = _FakeHighFunction([idx_add_op, idx_phi_op, ptradd_op, load_op, acc_add_op, acc_phi_op])
    tracer = _FakeTracer("unused", _const(0))
    tracer.trace_varnode = lambda varnode, *args, **kwargs: getattr(varnode, "_expr", None)

    summarizer = StructuralRecurrenceSummarizer(tracer, debug=False)
    summary = summarizer.try_summarize_function(
        _FakeFunction("ptr_sum_window"),
        high_function,
        analysis,
    )

    assert summary is not None
    summarized_returns, note = summary
    assert note == "readonly_pointer_reduction_summary"
    positive_case = next(ret for ret in summarized_returns if ret.value.expr_type == ret.value.expr_type.__class__.INTRINSIC)
    assert [w.exact_count for w in positive_case.value.runtime_ref.semantic_witnesses] == [1, 2, 3, 4]


def test_return_analyzer_restores_canonical_readonly_summary_guards():
    analyzer = ReturnAnalyzer(program=None, debug=False)
    params = [
        {"name": "param_1", "index": 0, "data_type": "int *", "size": 8},
        {"name": "param_2", "index": 1, "data_type": "int", "size": 4, "is_signed": True},
    ]
    reduction_expr = Expression.intrinsic(
        "READONLY_SUM",
        [
            Expression.parameter("param_1", index=0, data_type="int *", size=8),
            Expression.parameter("param_2", index=1, data_type="int", size=4),
        ],
        size=4,
        runtime_ref=ReadonlyReductionRef(
            reduction_kind="readonly_sum",
            pointer_base_ref=LocationBaseRef.parameter("param_1", index=0),
            count_parameter_name="param_2",
            count_parameter_index=1,
            stride=4,
            element_size=4,
            result_size=4,
        ),
        opcode=READONLY_SUM_OPCODE,
    )
    corrupted = ReturnInfo(
        address="0x1008",
        value=reduction_expr,
        conditions=[
            _cond(
                "INT_NOTEQUAL",
                Expression.parameter("param_1", index=0, data_type="int *", size=8),
                Expression.binary_op(
                    "INT_ADD",
                    Expression.parameter("param_1", index=0, data_type="int *", size=8),
                    Expression.constant(8, size=8),
                ),
            ),
            _cond("INT_SLESS", _const(0), _param("param_2")),
        ],
    )

    repaired = analyzer._restore_readonly_reduction_summary_conditions([corrupted], params)

    assert [cond.to_string() for cond in repaired[0].conditions] == ["(param_1 != 0)", "(0 < param_2)"]


def test_exact_counter_value_from_interval_conditions_recovers_singleton_count():
    summarizer = StructuralRecurrenceSummarizer(_FakeTracer("unused", _const(0)), debug=False)

    exact = summarizer._exact_counter_value_from_conditions(
        [
            _cond("INT_SLESSEQUAL", _const(1), _param("param_2")),
            _cond("INT_SLESSEQUAL", _param("param_2"), _const(1)),
        ],
        "param_2",
    )
    exact_two = summarizer._exact_counter_value_from_conditions(
        [
            _cond("INT_SLESS", _const(1), _param("param_2")),
            _cond("INT_SLESSEQUAL", _param("param_2"), _const(2)),
        ],
        "param_2",
    )

    assert exact == 1
    assert exact_two == 2
