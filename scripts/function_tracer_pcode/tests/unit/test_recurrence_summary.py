# -*- coding: utf-8 -*-

from typing import Optional

from scripts.function_tracer_pcode.analysis.recurrence_summary import (
    CountedLoopAccumulator,
    CountedLoopGuard,
    CountedLoopInduction,
    CountedLoopUpdateCase,
    ResidueLoopCase,
    StructuralRecurrenceSummarizer,
)
from scripts.function_tracer_pcode.analysis import ReturnAnalyzer
from scripts.function_tracer_pcode.analysis.condition import ConditionSimplifier
from scripts.function_tracer_pcode.analysis.tracer import PcodeTracer
from scripts.function_tracer_pcode.analysis.effect_summary import (
    CanonicalLocation,
    EffectSummary,
    StoreEffect,
)
from scripts.function_tracer_pcode.model import (
    COUNTED_LOOP_SUM_OPCODE,
    READONLY_SUM_OPCODE,
    CallTargetRef,
    Condition,
    CountedLoopSummaryRef,
    Expression,
    ExpressionType,
    LoopBodyEffectRef,
    LoopSideEffectProfileRef,
    LoopSummaryRef,
    LocationBaseRef,
    ReductionAccumulatorProof,
    ReadonlyReductionTermRef,
    ReturnInfo,
    ReadonlyReductionRef,
    ReadonlyReductionWitness,
    UnknownValueRef,
    loop_summary_method_b_key,
)
from scripts.function_tracer_pcode.equivalence.formula.returns import expression_has_unresolved_value
from scripts.function_tracer_pcode.model.render_smt import expression_to_smt
from scripts.function_tracer_pcode.tests.conftest import create_mock_analysis


def _param(name: str = "param_1", size: int = 4) -> Expression:
    return Expression.parameter(name, index=0, data_type="int", size=size)


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
    )


def _const(value: int, size: int = 4) -> Expression:
    return Expression.constant(value, size)


def _cond(operator: str, left: Expression, right: Expression, negated: bool = False) -> Condition:
    return Condition(Expression.binary_op(operator, left, right), negated=negated)


def test_counted_loop_summary_canonicalizes_zero_contribution_prefix():
    summarizer = StructuralRecurrenceSummarizer(PcodeTracer.__new__(PcodeTracer), debug=False)
    residue_cases = (
        ResidueLoopCase(modulus=2, residue=0, affine=(1, 0)),
        ResidueLoopCase(modulus=2, residue=1, affine=(-1, 0)),
    )
    value = summarizer._build_counted_loop_summary_intrinsic(
        base_expr=_const(0),
        start_expr=_const(1),
        limit_expr=_param(),
        induction_step=1,
        residue_cases=residue_cases,
        result_size=4,
        signed_loop=True,
    )

    assert value is not None
    assert isinstance(value.runtime_ref.loop_summary, LoopSummaryRef)
    assert loop_summary_method_b_key(value.runtime_ref.loop_summary) is not None
    assert value.runtime_ref.semantic_key() is not None

    canonical = summarizer._canonicalize_zero_prefix_counted_loop_value(
        value,
        base_expr=_const(0),
        limit_expr=_param(),
        induction_step=1,
        residue_cases=residue_cases,
        result_size=4,
        signed_loop=True,
    )

    assert canonical is not None
    assert canonical.expr_type == ExpressionType.INTRINSIC
    assert canonical.operands[1].equals(_const(0))


def test_counted_loop_summary_keeps_nonzero_prefix_start():
    summarizer = StructuralRecurrenceSummarizer(PcodeTracer.__new__(PcodeTracer), debug=False)
    residue_cases = (ResidueLoopCase(modulus=1, residue=0, affine=(1, 1)),)
    value = summarizer._build_counted_loop_summary_intrinsic(
        base_expr=_const(0),
        start_expr=_const(1),
        limit_expr=_param(),
        induction_step=1,
        residue_cases=residue_cases,
        result_size=4,
        signed_loop=True,
    )

    canonical = summarizer._canonicalize_zero_prefix_counted_loop_value(
        value,
        base_expr=_const(0),
        limit_expr=_param(),
        induction_step=1,
        residue_cases=residue_cases,
        result_size=4,
        signed_loop=True,
    )

    assert canonical is value


def test_counted_loop_summary_intrinsic_preserves_effect_aware_profile():
    summarizer = StructuralRecurrenceSummarizer(PcodeTracer.__new__(PcodeTracer), debug=False)
    effect_profile = LoopSideEffectProfileRef(
        profile="effect_aware",
        memory_writes=True,
        effect_count=1,
        effect_descriptors=(
            LoopBodyEffectRef(
                kind="memory_write",
                location=CanonicalLocation(
                    base_ref=LocationBaseRef.parameter("out", index=0),
                    offset=0,
                    size=4,
                ),
                value_expr=_param("param_1"),
                guard_constraints=(_cond("INT_SLESS", _const(0), _param("param_1")),),
                order_key=7,
            ),
        ),
    )
    value = summarizer._build_counted_loop_summary_intrinsic(
        base_expr=_const(0),
        start_expr=_const(0),
        limit_expr=_param("param_1"),
        induction_step=1,
        residue_cases=(ResidueLoopCase(modulus=1, residue=0, affine=(1, 0)),),
        result_size=4,
        signed_loop=True,
        side_effect_profile=effect_profile,
        guard_constraints=[_cond("INT_SLESS", _const(0), _param("param_1"))],
    )

    assert value is not None
    loop_summary = value.runtime_ref.loop_summary
    assert loop_summary.side_effect_profile.profile == "effect_aware"
    assert loop_summary.side_effect_profile.memory_writes is True
    assert loop_summary.guard_constraints
    assert loop_summary.stable_key() is not None


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


def test_counted_loop_update_validation_rejects_non_affine_update_semantics():
    summarizer = StructuralRecurrenceSummarizer(PcodeTracer.__new__(PcodeTracer), debug=False)
    loop_iv = Expression.parameter("__loop_iv", index=-10000, size=4)
    loop_acc = Expression.variable("__loop_acc", size=4)
    induction = CountedLoopInduction(
        phi_op=object(),
        phi_output=object(),
        init_expr=_const(0),
        backedge_index=1,
        step=1,
        placeholder=loop_iv,
        signed_guard=False,
    )
    accumulator = CountedLoopAccumulator(
        phi_op=None,
        phi_output=None,
        init_expr=_const(0),
        backedge_index=1,
        placeholder=loop_acc,
    )
    actual_update = Expression.binary_op("INT_ADD", loop_acc, loop_iv)
    actual_update.size = 4
    wrong_delta = Expression.constant(-1, 4)
    case = CountedLoopUpdateCase(
        conditions=(),
        update_expr=actual_update,
        delta_expr=wrong_delta,
    )

    assert not summarizer._validate_counted_loop_update_cases(
        cases=(case,),
        residue_cases=(ResidueLoopCase(modulus=1, residue=0, affine=(0, -1)),),
        induction=induction,
        accumulator=accumulator,
    )


def test_counted_loop_update_validation_accepts_solver_proven_affine_update():
    summarizer = StructuralRecurrenceSummarizer(PcodeTracer.__new__(PcodeTracer), debug=False)
    loop_iv = Expression.parameter("__loop_iv", index=-10000, size=4)
    loop_acc = Expression.variable("__loop_acc", size=4)
    even_condition = _cond(
        "INT_EQUAL",
        Expression.binary_op("INT_AND", loop_iv, _const(1)),
        _const(0),
    )
    update_expr = Expression.binary_op("INT_ADD", loop_acc, loop_iv)
    update_expr.size = 4
    case = CountedLoopUpdateCase(
        conditions=(even_condition,),
        update_expr=update_expr,
        delta_expr=loop_iv,
    )
    induction = CountedLoopInduction(
        phi_op=object(),
        phi_output=object(),
        init_expr=_const(0),
        backedge_index=1,
        step=1,
        placeholder=loop_iv,
        signed_guard=False,
    )
    accumulator = CountedLoopAccumulator(
        phi_op=None,
        phi_output=None,
        init_expr=_const(0),
        backedge_index=1,
        placeholder=loop_acc,
    )

    assert summarizer._validate_counted_loop_update_cases(
        cases=(case,),
        residue_cases=(ResidueLoopCase(modulus=2, residue=0, affine=(1, 0)),),
        induction=induction,
        accumulator=accumulator,
    )


def test_counted_loop_update_validation_query_uses_symbol_replacer_names():
    summarizer = StructuralRecurrenceSummarizer(PcodeTracer.__new__(PcodeTracer), debug=False)
    loop_iv = Expression.parameter("__loop_iv", index=-10000, size=4)
    loop_acc = Expression.variable("__loop_acc", size=4)
    condition = _cond("INT_EQUAL", Expression.binary_op("INT_AND", loop_iv, _const(1)), _const(0))
    query = summarizer._build_expression_equivalence_query(
        Expression.binary_op("INT_ADD", loop_acc, loop_iv),
        Expression.binary_op("INT_ADD", loop_acc, loop_iv),
        [condition],
        [{"name": "param_1", "index": 0, "size": 4, "data_type": "int"}],
    )

    assert query is not None
    assert "(declare-const __loop_iv_aux (_ BitVec 32))" in query
    assert "(declare-const __loop_acc_aux (_ BitVec 32))" in query
    assert "__loop_iv_aux" in query
    assert "__loop_acc_aux" in query
    assert " __loop_iv)" not in query
    assert " __loop_acc)" not in query


def test_expression_equivalence_query_coerces_mixed_width_values():
    summarizer = StructuralRecurrenceSummarizer(PcodeTracer.__new__(PcodeTracer), debug=False)
    wide_zero = Expression.unary_op("INT_ZEXT", _const(0))
    wide_zero.size = 16
    query = summarizer._build_expression_equivalence_query(
        wide_zero,
        _const(0),
        [],
        [],
    )

    assert query is not None
    assert "(assert (not (= ((_ zero_extend 96) (_ bv0 32)) ((_ zero_extend 96) (_ bv0 32)))))" in query


def test_zero_base_canonicalization_handles_wide_zero_expression():
    summarizer = StructuralRecurrenceSummarizer(PcodeTracer.__new__(PcodeTracer), debug=False)
    wide_zero = Expression.unary_op("INT_ZEXT", _const(0))
    wide_zero.size = 16
    canonical = summarizer._canonicalize_zero_value_under_conditions(wide_zero, [])

    assert canonical.expr_type == ExpressionType.CONSTANT
    assert canonical.value == 0
    assert canonical.size == 16


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


class _FakeAddress:
    def __init__(self, space_name: str | _FakeAddressSpace):
        self._space = space_name if isinstance(space_name, _FakeAddressSpace) else _FakeAddressSpace(space_name)

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
        self._descendants = []

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
    def __init__(self, spaces):
        self._spaces = dict(spaces)

    def getAddressSpace(self, space_id):
        return self._spaces[int(space_id)]


class _FakeProgram:
    def __init__(self, address_factory):
        self._address_factory = address_factory

    def getAddressFactory(self):
        return self._address_factory


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

    tracer = _FakeTracer("unused", Expression.unknown("untraced"))
    tracer.trace_varnode = lambda varnode, *args, **kwargs: getattr(varnode, "_expr", None)
    summarizer = StructuralRecurrenceSummarizer(tracer, debug=False)

    assert summarizer._extract_index_step(next_vn, phi_output) == -1


def test_match_index_progression_phi_accepts_positive_non_unit_step():
    phi_output = _FakeVarnode("loop_index")
    init_vn = _FakeVarnode("zero", expr=_const(0))
    two_vn = _FakeVarnode("two", expr=_const(2))
    next_vn = _FakeVarnode("loop_index_next")
    _FakePcodeOp("INT_ADD", [phi_output, two_vn], next_vn)
    phi_op = _FakePcodeOp("MULTIEQUAL", [init_vn, next_vn], phi_output)
    summarizer = StructuralRecurrenceSummarizer(_FakeTracer("unused", _const(0)), debug=False)

    match = summarizer._match_index_progression_phi(phi_op)

    assert match is not None
    assert match["start"] == 0
    assert match["step"] == 2


def test_readonly_index_progression_declines_negative_step():
    phi_output = _FakeVarnode("loop_index")
    init_vn = _FakeVarnode("limit_minus_one", expr=_const(7))
    one_vn = _FakeVarnode("one", expr=_const(1))
    next_vn = _FakeVarnode("loop_index_next")
    _FakePcodeOp("INT_SUB", [phi_output, one_vn], next_vn)
    phi_op = _FakePcodeOp("MULTIEQUAL", [init_vn, next_vn], phi_output)
    summarizer = StructuralRecurrenceSummarizer(_FakeTracer("unused", _const(0)), debug=False)

    assert summarizer._extract_index_step(next_vn, phi_output) == -1
    assert summarizer._match_index_progression_phi(phi_op) is None


def test_dynamic_index_step_is_parsed_but_not_accepted_as_constant_progression():
    phi_output = _FakeVarnode("loop_index")
    init_vn = _FakeVarnode("zero", expr=_const(0))
    step_expr = Expression.parameter("step", index=1, data_type="int", size=4)
    step_vn = _FakeVarnode("step", expr=step_expr)
    next_vn = _FakeVarnode("loop_index_next")
    _FakePcodeOp("INT_ADD", [phi_output, step_vn], next_vn)
    phi_op = _FakePcodeOp("MULTIEQUAL", [init_vn, next_vn], phi_output)
    summarizer = StructuralRecurrenceSummarizer(_FakeTracer("unused", _const(0)), debug=False)

    extracted_step = summarizer._extract_index_step_expression(next_vn, phi_output)

    assert extracted_step is not None
    assert extracted_step.equals(step_expr)
    assert summarizer._extract_index_step(next_vn, phi_output) is None
    assert summarizer._match_index_progression_phi(phi_op) is None


def test_counted_loop_induction_preserves_positive_non_unit_step_in_loop_summary():
    phi_output = _FakeVarnode("loop_iv")
    init_vn = _FakeVarnode("zero", expr=_const(0))
    two_vn = _FakeVarnode("two", expr=_const(2))
    next_vn = _FakeVarnode("loop_iv_next")
    _FakePcodeOp("INT_ADD", [phi_output, two_vn], next_vn)
    phi_op = _FakePcodeOp("MULTIEQUAL", [init_vn, next_vn], phi_output)
    summarizer = StructuralRecurrenceSummarizer(_FakeTracer("unused", _const(0)), debug=False)

    induction = summarizer._match_counted_loop_induction(phi_op)
    value = summarizer._build_counted_loop_summary_intrinsic(
        base_expr=_const(0),
        start_expr=_const(0),
        limit_expr=_param("param_1"),
        induction_step=2,
        residue_cases=(ResidueLoopCase(modulus=1, residue=0, affine=(1, 0)),),
        result_size=4,
        signed_loop=True,
    )

    assert induction is not None
    assert induction.step == 2
    assert value is not None
    assert value.runtime_ref.induction_step == 2
    assert value.runtime_ref.loop_summary.step_expr.value == 2


def test_counted_loop_induction_preserves_decrement_step_in_loop_summary():
    phi_output = _FakeVarnode("loop_iv")
    init_vn = _FakeVarnode("start", expr=_const(7))
    one_vn = _FakeVarnode("one", expr=_const(1))
    next_vn = _FakeVarnode("loop_iv_next")
    _FakePcodeOp("INT_SUB", [phi_output, one_vn], next_vn)
    phi_op = _FakePcodeOp("MULTIEQUAL", [init_vn, next_vn], phi_output)
    summarizer = StructuralRecurrenceSummarizer(_FakeTracer("unused", _const(0)), debug=False)

    induction = summarizer._match_counted_loop_induction(phi_op)
    value = summarizer._build_counted_loop_summary_intrinsic(
        base_expr=_const(0),
        start_expr=_const(7),
        limit_expr=_const(0),
        induction_step=-1,
        residue_cases=(ResidueLoopCase(modulus=1, residue=0, affine=(1, 0)),),
        result_size=4,
        signed_loop=True,
    )

    assert induction is not None
    assert induction.step == -1
    assert value is not None
    assert value.runtime_ref.induction_step == -1
    assert value.runtime_ref.loop_summary.step_expr.value == -1


def test_counted_loop_continue_guard_accepts_decrementing_counter():
    summarizer = StructuralRecurrenceSummarizer(_FakeTracer("unused", _const(0)), debug=False)
    counter = Expression.parameter("__loop_iv", index=-10000, size=4)
    raw_guard = Expression.binary_op("INT_SLESS", _const(0), counter)
    raw_guard.size = 1

    normalized = summarizer._normalize_loop_continue_guard(
        raw_guard,
        counter,
        body_on_true=True,
        step=-1,
    )

    assert normalized is not None
    condition_expr, bound_expr, signed = normalized
    assert signed is True
    assert bound_expr.equals(_const(0))
    assert condition_expr.operator == "INT_SLESS"
    assert condition_expr.operands[0].equals(_const(0))
    assert condition_expr.operands[1].equals(counter)


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
    assert "rt_counted_loop_sum_" not in loop_smt
    assert "(ite " in loop_smt
    loop_summary = loop_case.value.runtime_ref.loop_summary
    assert len(loop_summary.cases) == 2
    assert all(case.case_kind == "accumulator_delta" for case in loop_summary.cases)
    assert all(case.path_conditions for case in loop_summary.cases)
    assert all(case.body_effect.kind == "accumulator_update" for case in loop_summary.cases)
    assert all(case.term_expr is not None for case in loop_summary.cases)
    assert all(case.stable_key() is not None for case in loop_summary.cases)


def test_path_enumeration_no_path_is_not_unconditional_success():
    start = _FakeCfgBlock(0)
    target = _FakeCfgBlock(1)
    header = _FakeCfgBlock(2)
    summarizer = StructuralRecurrenceSummarizer(_FakeTracer("unused", _const(0)), debug=False)

    assert summarizer._enumerate_paths_with_conditions(
        start_block=start,
        target_block=target,
        header_block=header,
        placeholders={},
    ) == []


def test_pre_return_counted_loop_summary_requires_single_covered_return(monkeypatch):
    header = _FakeCfgBlock(0)
    ret_block = _FakeCfgBlock(1)
    header.add_edge(ret_block)
    iv_phi = _FakePcodeOp("MULTIEQUAL", [], _FakeVarnode("iv_phi"))
    acc_phi_vn = _FakeVarnode("acc_phi")
    acc_phi = _FakePcodeOp("MULTIEQUAL", [], acc_phi_vn)
    branch = _FakeBranchOp(_cond("INT_SLESS", _const(0), _param()).expression)
    header._ops[:] = [iv_phi, acc_phi, branch]
    for op in header._ops:
        op.setParent(header)
    return_op = _FakePcodeOp("RETURN", [_FakeVarnode("target"), acc_phi_vn], None)
    ret_block._ops[:] = [return_op]
    return_op.setParent(ret_block)

    summarizer = StructuralRecurrenceSummarizer(_FakeTracer("unused", _const(0)), debug=False)
    induction = CountedLoopInduction(
        phi_op=iv_phi,
        phi_output=iv_phi.getOutput(),
        init_expr=_const(0),
        backedge_index=0,
        step=1,
        placeholder=Expression.parameter("__loop_iv", index=-1, size=4),
        signed_guard=True,
    )
    accumulator = CountedLoopAccumulator(
        phi_op=acc_phi,
        phi_output=acc_phi_vn,
        init_expr=_const(0),
        backedge_index=0,
        placeholder=Expression.variable("__loop_acc", size=4),
        member_outputs=(acc_phi_vn,),
    )
    guard = CountedLoopGuard(
        condition_expr=Expression.binary_op("INT_SLESS", induction.placeholder, _param()),
        bound_expr=_param(),
        continue_on_true=True,
        body_block=header,
        exit_block=ret_block,
        signed_comparison=True,
    )
    monkeypatch.setattr(
        summarizer,
        "_extract_counted_scalar_loop_model",
        lambda *_args, **_kwargs: (
            induction,
            accumulator,
            guard,
            (ResidueLoopCase(modulus=1, residue=0, affine=(1, 0)),),
        ),
    )
    monkeypatch.setattr(summarizer, "_derive_direct_counted_loop_conditions", lambda *_args, **_kwargs: None)
    analysis = create_mock_analysis(
        "branch_for_accumulate",
        return_type="int",
        parameters=[{"name": "param_1", "index": 0, "data_type": "int", "size": 4}],
        returns=[ReturnInfo(address="0x1000", value=Expression.unknown("pre_return"), conditions=[])],
    )

    summary = summarizer.try_summarize_pre_return_counted_scalar_loop(
        _FakeFunction("branch_for_accumulate"),
        _FakeCfgHighFunction([header, ret_block]),
        analysis,
        [return_op],
    )

    assert summary is not None
    extra_ret_block = _FakeCfgBlock(2)
    assert summarizer.try_summarize_pre_return_counted_scalar_loop(
        _FakeFunction("branch_for_accumulate"),
        _FakeCfgHighFunction([header, ret_block, extra_ret_block]),
        analysis,
        [return_op],
    ) is None


def test_structural_recurrence_summarizer_recovers_multi_backedge_counted_loop_cfg():
    limit_expr = _param("param_1")
    zero_expr = _const(0)
    one_expr = _const(1)

    entry = _FakeCfgBlock(0)
    ret_zero = _FakeCfgBlock(1)
    preheader = _FakeCfgBlock(2)
    header = _FakeCfgBlock(3)
    even_block = _FakeCfgBlock(4)
    even_exit = _FakeCfgBlock(5)
    odd_block = _FakeCfgBlock(6)
    odd_exit = _FakeCfgBlock(7)

    entry.add_edge(ret_zero, truth=True)
    entry.add_edge(preheader, truth=False)
    odd_block.add_edge(header, truth=True)
    odd_block.add_edge(odd_exit, truth=False)
    preheader.add_edge(header)
    even_block.add_edge(even_exit, truth=True)
    even_block.add_edge(header, truth=False)
    header.add_edge(even_block, truth=True)
    header.add_edge(odd_block, truth=False)

    limit_vn = _FakeVarnode("limit", expr=limit_expr)
    zero_vn = _FakeVarnode("zero", expr=zero_expr)
    one_vn = _FakeVarnode("one", expr=one_expr)

    signed_limit_vn = _FakeVarnode("signed_limit")
    entry_cond_vn = _FakeVarnode("entry_cond", size=1)
    iv_phi_vn = _FakeVarnode("iv_phi")
    acc_phi_vn = _FakeVarnode("acc_phi")
    parity_vn = _FakeVarnode("parity")
    parity_cond_vn = _FakeVarnode("parity_cond", size=1)
    even_acc_vn = _FakeVarnode("even_acc")
    even_next_vn = _FakeVarnode("even_next")
    even_exit_cond_vn = _FakeVarnode("even_exit_cond", size=1)
    odd_acc_vn = _FakeVarnode("odd_acc")
    odd_next_vn = _FakeVarnode("odd_next")
    odd_continue_cond_vn = _FakeVarnode("odd_continue_cond", size=1)

    entry_cast_op = _FakePcodeOp("CAST", [limit_vn], signed_limit_vn)
    entry_cmp_op = _FakePcodeOp("INT_SLESS", [signed_limit_vn, one_vn], entry_cond_vn)
    entry_branch = _FakePcodeOp("CBRANCH", [_FakeVarnode("entry_target"), entry_cond_vn], None)
    entry._ops[:] = [entry_cast_op, entry_cmp_op, entry_branch]
    for op in entry._ops:
        op.setParent(entry)

    iv_phi_op = _FakePcodeOp("MULTIEQUAL", [odd_next_vn, zero_vn, even_next_vn], iv_phi_vn)
    acc_phi_op = _FakePcodeOp("MULTIEQUAL", [odd_acc_vn, zero_vn, even_acc_vn], acc_phi_vn)
    parity_and_op = _FakePcodeOp("INT_AND", [iv_phi_vn, one_vn], parity_vn)
    parity_cmp_op = _FakePcodeOp("INT_EQUAL", [parity_vn, zero_vn], parity_cond_vn)
    parity_branch = _FakePcodeOp("CBRANCH", [_FakeVarnode("parity_target"), parity_cond_vn], None)
    header._ops[:] = [iv_phi_op, acc_phi_op, parity_and_op, parity_cmp_op, parity_branch]
    for op in header._ops:
        op.setParent(header)

    even_acc_op = _FakePcodeOp("INT_ADD", [acc_phi_vn, iv_phi_vn], even_acc_vn)
    even_next_op = _FakePcodeOp("INT_ADD", [iv_phi_vn, one_vn], even_next_vn)
    even_cmp_op = _FakePcodeOp("INT_EQUAL", [limit_vn, even_next_vn], even_exit_cond_vn)
    even_branch = _FakePcodeOp("CBRANCH", [_FakeVarnode("even_target"), even_exit_cond_vn], None)
    even_block._ops[:] = [even_acc_op, even_next_op, even_cmp_op, even_branch]
    for op in even_block._ops:
        op.setParent(even_block)

    odd_acc_op = _FakePcodeOp("INT_SUB", [acc_phi_vn, iv_phi_vn], odd_acc_vn)
    odd_next_op = _FakePcodeOp("INT_ADD", [iv_phi_vn, one_vn], odd_next_vn)
    odd_cmp_op = _FakePcodeOp("INT_NOTEQUAL", [limit_vn, odd_next_vn], odd_continue_cond_vn)
    odd_branch = _FakePcodeOp("CBRANCH", [_FakeVarnode("odd_target"), odd_continue_cond_vn], None)
    odd_block._ops[:] = [odd_acc_op, odd_next_op, odd_cmp_op, odd_branch]
    for op in odd_block._ops:
        op.setParent(odd_block)

    summarizer = StructuralRecurrenceSummarizer(_FakeTracer("unused", _const(0)), debug=False)
    analysis = create_mock_analysis(
        "branch_for_accumulate",
        return_type="int",
        parameters=[{"name": "param_1", "index": 0, "data_type": "int", "size": 4}],
        returns=[
            ReturnInfo(
                address="0x401000",
                value=Expression.unknown("phi_circular"),
                conditions=[],
            )
        ],
    )
    summary = summarizer.try_summarize_function(
        _FakeFunction("branch_for_accumulate"),
        _FakeCfgHighFunction([entry, ret_zero, preheader, header, even_block, even_exit, odd_block, odd_exit]),
        analysis,
    )

    assert summary is not None
    summarized_returns, note = summary
    assert note == "counted_scalar_loop_summary"
    assert len(summarized_returns) == 2
    assert all(expression_has_unresolved_value(ret.value) is False for ret in summarized_returns)
    loop_case = next(ret for ret in summarized_returns if ret.value.to_string() != "0")
    assert any("param_1" in condition.to_string() for condition in loop_case.conditions)
    loop_smt = expression_to_smt(loop_case.value)
    assert "rtunk_" not in loop_smt
    assert "rt_counted_loop_sum_" not in loop_smt
    assert "(ite " in loop_smt


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


def test_counted_loop_summary_value_uses_intrinsic_for_negative_step_single_residue():
    summarizer = StructuralRecurrenceSummarizer(_FakeTracer("unused", _const(0)), debug=False)
    expr = summarizer._build_counted_loop_summary_value(
        base_expr=_const(0),
        start_expr=_const(16),
        limit_expr=_const(0),
        induction_step=-8,
        residue_cases=(ResidueLoopCase(modulus=1, residue=0, affine=(0, -4)),),
        result_size=4,
        signed_loop=True,
    )

    assert expr is not None
    assert expr.expr_type == ExpressionType.INTRINSIC
    assert expr.opcode == COUNTED_LOOP_SUM_OPCODE
    assert expression_has_unresolved_value(expr) is False
    assert "rt_counted_loop_sum_" not in expression_to_smt(expr)


def test_counted_loop_latch_guard_rejects_boolean_bound_expression():
    summarizer = StructuralRecurrenceSummarizer(_FakeTracer("unused", _const(0)), debug=False)
    counter = Expression.parameter("__loop_iv", index=-10000, size=4)
    bool_bound = Expression.binary_op(
        "INT_EQUAL",
        Expression.binary_op("INT_AND", _const(0), _const(1)),
        _const(0),
    )
    bool_bound.size = 1
    counter_next = Expression.binary_op("INT_ADD", counter, _const(1))
    counter_next.size = 4
    raw_guard = Expression.binary_op("INT_NOTEQUAL", bool_bound, counter_next)
    raw_guard.size = 1

    assert summarizer._normalize_latch_continue_guard(
        raw_guard,
        counter,
        continue_on_true=True,
        step=1,
    ) is None


def test_affine_loop_state_phi_supports_nonunit_induction_step():
    tracer = _FakeTracer("unused", _const(0))
    summarizer = StructuralRecurrenceSummarizer(tracer, debug=False)

    iv_phi_vn = _FakeVarnode("__loop_iv", size=4, high=_FakeHighVar("__loop_iv"))
    iv_next_vn = _FakeVarnode("iv_next", size=4)
    eight_vn = _FakeVarnode("eight", size=4, expr=_const(8))
    iv_init_vn = _FakeVarnode("iv_init", size=4, expr=_const(16))
    iv_step_op = _FakePcodeOp("INT_SUB", [iv_phi_vn, eight_vn], iv_next_vn)
    iv_phi_op = _FakePcodeOp("MULTIEQUAL", [iv_init_vn, iv_next_vn], iv_phi_vn)

    state_phi_vn = _FakeVarnode("lane", size=4, high=_FakeHighVar("lane"))
    state_next_vn = _FakeVarnode("lane_next", size=4)
    state_init_vn = _FakeVarnode("lane_init", size=4, expr=_const(0))
    state_delta_op = _FakePcodeOp("INT_ADD", [state_phi_vn, eight_vn], state_next_vn)
    state_phi_op = _FakePcodeOp("MULTIEQUAL", [state_init_vn, state_next_vn], state_phi_vn)

    induction = CountedLoopInduction(
        phi_op=iv_phi_op,
        phi_output=iv_phi_vn,
        init_expr=_const(16),
        backedge_index=1,
        step=-8,
        placeholder=Expression.parameter("__loop_iv", index=-10000, size=4),
        signed_guard=False,
    )

    expr = summarizer._summarize_affine_loop_state_phi(state_phi_op, induction)

    assert expr is not None
    assert summarizer._extract_affine_term(expr, "__loop_iv") == (-1, 16)


def test_extract_counted_scalar_loop_model_evaluates_multiple_accumulator_candidates(monkeypatch):
    header = _FakeCfgBlock(1)
    phi_bad = _FakePcodeOp("MULTIEQUAL", [], _FakeVarnode("bad_acc", size=4))
    phi_good = _FakePcodeOp("MULTIEQUAL", [], _FakeVarnode("good_acc", size=4))
    phi_iv = _FakePcodeOp("MULTIEQUAL", [], _FakeVarnode("iv", size=4))
    branch = _FakeBranchOp(_cond("INT_SLESS", _const(0), _param()).expression)
    header._ops[:] = [phi_iv, phi_bad, phi_good, branch]
    for op in header._ops:
        op.setParent(header)

    summarizer = StructuralRecurrenceSummarizer(_FakeTracer("unused", _const(0)), debug=False)
    induction = CountedLoopInduction(
        phi_op=phi_iv,
        phi_output=phi_iv.getOutput(),
        init_expr=_const(0),
        backedge_index=1,
        step=1,
        placeholder=Expression.parameter("__loop_iv", index=-10000, size=4),
        signed_guard=False,
    )
    guard = CountedLoopGuard(
        condition_expr=Expression.binary_op("INT_SLESS", induction.placeholder, _param()),
        bound_expr=_param(),
        continue_on_true=True,
        body_block=header,
        exit_block=header,
        signed_comparison=True,
        entry_condition_expr=Expression.binary_op("INT_SLESS", induction.placeholder, _param()),
    )
    bad_acc = CountedLoopAccumulator(
        phi_op=phi_bad,
        phi_output=phi_bad.getOutput(),
        init_expr=_const(0),
        backedge_index=1,
        placeholder=Expression.variable("__loop_acc_bad", size=4),
        member_outputs=(phi_bad.getOutput(),),
        member_placeholders=(Expression.variable("__loop_acc_bad", size=4),),
    )
    good_acc = CountedLoopAccumulator(
        phi_op=phi_good,
        phi_output=phi_good.getOutput(),
        init_expr=_const(0),
        backedge_index=1,
        placeholder=Expression.variable("__loop_acc_good", size=4),
        member_outputs=(phi_good.getOutput(),),
        member_placeholders=(Expression.variable("__loop_acc_good", size=4),),
    )

    monkeypatch.setattr(summarizer, "_match_counted_loop_induction", lambda op: induction if op is phi_iv else None)
    monkeypatch.setattr(summarizer, "_candidate_counted_loop_guards", lambda *_args, **_kwargs: [guard])
    monkeypatch.setattr(summarizer, "_match_counted_loop_accumulators", lambda *_args, **_kwargs: [bad_acc, good_acc])

    def _fake_cases(accumulator, *_args, **_kwargs):
        if accumulator is bad_acc:
            return []
        return [
            CountedLoopUpdateCase(
                conditions=(),
                update_expr=Expression.binary_op("INT_ADD", accumulator.placeholder, induction.placeholder),
                delta_expr=induction.placeholder,
            )
        ]

    monkeypatch.setattr(summarizer, "_extract_counted_loop_update_cases", _fake_cases)
    monkeypatch.setattr(
        summarizer,
        "_extract_residue_loop_cases",
        lambda cases, _counter_name: (ResidueLoopCase(modulus=1, residue=0, affine=(1, 0)),) if cases else None,
    )
    model = summarizer._extract_counted_scalar_loop_model(
        _FakeCfgHighFunction([header]),
        analysis=None,
    )

    assert model is not None
    _, accumulator, _, residue_cases = model
    assert accumulator is good_acc
    assert residue_cases == (ResidueLoopCase(modulus=1, residue=0, affine=(1, 0)),)


def test_counted_loop_model_prefers_return_reaching_accumulator_over_larger_coeff(monkeypatch):
    header = _FakeCfgBlock(1)
    phi_bad = _FakePcodeOp("MULTIEQUAL", [], _FakeVarnode("bad_acc", size=4))
    phi_good = _FakePcodeOp("MULTIEQUAL", [], _FakeVarnode("good_acc", size=4))
    phi_iv = _FakePcodeOp("MULTIEQUAL", [], _FakeVarnode("iv", size=4))
    branch = _FakeBranchOp(_cond("INT_SLESS", _const(0), _param()).expression)
    header._ops[:] = [phi_iv, phi_bad, phi_good, branch]
    for op in header._ops:
        op.setParent(header)

    summarizer = StructuralRecurrenceSummarizer(_FakeTracer("unused", _const(0)), debug=False)
    induction = CountedLoopInduction(
        phi_op=phi_iv,
        phi_output=phi_iv.getOutput(),
        init_expr=_const(0),
        backedge_index=1,
        step=1,
        placeholder=Expression.parameter("__loop_iv", index=-10000, size=4),
        signed_guard=False,
    )
    guard = CountedLoopGuard(
        condition_expr=Expression.binary_op("INT_SLESS", induction.placeholder, _param()),
        bound_expr=_param(),
        continue_on_true=True,
        body_block=header,
        exit_block=header,
        signed_comparison=True,
        entry_condition_expr=Expression.binary_op("INT_SLESS", induction.placeholder, _param()),
    )
    bad_acc = CountedLoopAccumulator(
        phi_op=phi_bad,
        phi_output=phi_bad.getOutput(),
        init_expr=_const(0),
        backedge_index=1,
        placeholder=Expression.variable("__loop_acc_bad", size=4),
        member_outputs=(phi_bad.getOutput(),),
        member_placeholders=(Expression.variable("__loop_acc_bad", size=4),),
    )
    good_acc = CountedLoopAccumulator(
        phi_op=phi_good,
        phi_output=phi_good.getOutput(),
        init_expr=_const(0),
        backedge_index=1,
        placeholder=Expression.variable("__loop_acc_good", size=4),
        member_outputs=(phi_good.getOutput(),),
        member_placeholders=(Expression.variable("__loop_acc_good", size=4),),
    )

    monkeypatch.setattr(summarizer, "_match_counted_loop_induction", lambda op: induction if op is phi_iv else None)
    monkeypatch.setattr(summarizer, "_candidate_counted_loop_guards", lambda *_args, **_kwargs: [guard])
    monkeypatch.setattr(summarizer, "_match_counted_loop_accumulators", lambda *_args, **_kwargs: [bad_acc, good_acc])
    monkeypatch.setattr(
        summarizer,
        "_varnode_reaches_return",
        lambda varnode, **_kwargs: varnode is good_acc.phi_output,
    )

    def _fake_cases(accumulator, *_args, **_kwargs):
        coeff = 8 if accumulator is bad_acc else 1
        return [
            CountedLoopUpdateCase(
                conditions=(),
                update_expr=Expression.binary_op("INT_ADD", accumulator.placeholder, induction.placeholder),
                delta_expr=Expression.binary_op("INT_MULT", induction.placeholder, _const(coeff)),
            )
        ]

    monkeypatch.setattr(summarizer, "_extract_counted_loop_update_cases", _fake_cases)
    monkeypatch.setattr(
        summarizer,
        "_extract_residue_loop_cases",
        lambda cases, _counter_name: (
            ResidueLoopCase(
                modulus=1,
                residue=0,
                affine=(int(cases[0].delta_expr.operands[1].value), 0),
            ),
        ) if cases else None,
    )

    model = summarizer._extract_counted_scalar_loop_model(
        _FakeCfgHighFunction([header]),
        analysis=None,
    )

    assert model is not None
    _, accumulator, _, residue_cases = model
    assert accumulator is good_acc
    assert residue_cases == (ResidueLoopCase(modulus=1, residue=0, affine=(1, 0)),)


def test_counted_scalar_loop_summary_keeps_function_memory_writes_as_context():
    analysis = create_mock_analysis(
        "counted_loop_effectful",
        return_type="int",
        parameters=[{"name": "param_1", "index": 0, "data_type": "int", "size": 4}],
        returns=[
            ReturnInfo(
                address="0x1000",
                value=_const(0),
                conditions=[_cond("INT_SLESS", _const(0), _param("param_1"), negated=True)],
            ),
            ReturnInfo(
                address="0x1004",
                value=Expression.unknown("phi_circular"),
                conditions=[_cond("INT_SLESS", _const(0), _param("param_1"))],
            ),
        ],
    )
    analysis.effect_summary = EffectSummary(
        parameter_names=["param_1"],
        effects=[
            StoreEffect(
                location=CanonicalLocation(
                    base_ref=LocationBaseRef.parameter("param_1", index=0),
                    offset=0,
                    size=4,
                ),
                value=_const(1),
                conditions=[],
                order_key=0,
            )
        ],
    )

    summarizer = StructuralRecurrenceSummarizer(_FakeTracer("unused", _const(0)), debug=False)
    profile = summarizer._build_loop_side_effect_profile(analysis=analysis)

    assert summarizer._analysis_is_safe_for_counted_scalar_summary(analysis) is True
    assert profile.profile == "pure"
    assert profile.memory_writes is False
    assert profile.context_memory_writes is True
    assert profile.calls is False
    assert profile.escapes is False
    assert profile.effect_descriptors == ()
    assert len(profile.context_descriptors) == 1
    assert profile.context_descriptors[0].kind == "memory_write"
    assert profile.context_descriptors[0].source == "function_effect_summary"
    assert profile.context_descriptors[0].scope == "function"


def test_readonly_loop_summary_preserves_non_unit_index_step_object_centrically():
    summarizer = StructuralRecurrenceSummarizer(_FakeTracer("unused", _const(0)), debug=False)
    count_expr = Expression.parameter("count", index=1, data_type="int", size=4)
    pointer_base_ref = LocationBaseRef.parameter("ptr", index=0)
    proof = _readonly_accumulator_proof(
        base_ref=pointer_base_ref,
        count_expr=count_expr,
        stride=8,
        element_size=4,
        start_index=0,
        index_step=2,
        index_scale=4,
    )

    summary = proof.with_runtime_evidence(
        limit_expr=count_expr,
        result_size=4,
        loop_body_witnesses=(),
        exact_return_witnesses=(),
        guard_constraints=(),
        signed_counter=True,
    ).lower_to_loop_summary_ref()
    witnesses = summarizer._synthesize_linear_readonly_reduction_witnesses(
        {"name": "ptr", "index": 0},
        proof,
        result_size=4,
    )

    assert summary is not None
    assert summary.start_expr.value == 0
    assert summary.step_expr.value == 2
    assert summary.term_descriptor.stride == 4
    assert summarizer._readonly_loop_trip_count_for_count_value(proof, 5) == 3
    count_five = next(witness for witness in witnesses if witness.exact_count == 5)
    assert [term.byte_offset for term in count_five.terms] == [0, 8, 16]


def test_loop_side_effect_profile_records_pcode_store_address_and_value():
    address = Expression.parameter("out", index=0, data_type="int *", size=8)
    value = Expression.binary_op("INT_ADD", _param("param_1"), _const(1))
    body = _FakeCfgBlock(
        1,
        ops=[
            _FakePcodeOp(
                "STORE",
                [_FakeVarnode("ram"), _FakeArgVarnode(address), _FakeArgVarnode(value)],
                None,
            ),
        ],
    )
    summarizer = StructuralRecurrenceSummarizer(_FakeTracer("unused", _const(0)), debug=False)

    profile = summarizer._build_loop_side_effect_profile(loop_blocks=[body])

    assert profile.profile == "effect_aware"
    assert profile.memory_writes is True
    assert len(profile.effect_descriptors) == 1
    effect = profile.effect_descriptors[0]
    assert effect.kind == "memory_write"
    assert effect.keyable is True
    assert effect.address_space["space_name"] == "ram"
    assert effect.location.equals(address)
    assert effect.value_expr.equals(value)
    assert effect.stable_key() is not None


def test_loop_store_address_space_uses_program_address_factory_target_space():
    address = Expression.parameter("out", index=0, data_type="int *", size=8)
    value = _const(7)
    store_space = _FakeStoreSpaceVarnode(target_space_id=1)
    body = _FakeCfgBlock(
        1,
        ops=[
            _FakePcodeOp(
                "STORE",
                [store_space, _FakeArgVarnode(address), _FakeArgVarnode(value)],
                None,
            ),
        ],
    )
    tracer = _FakeTracer("unused", _const(0))
    tracer.program = _FakeProgram(
        _FakeAddressFactory({
            1: _FakeAddressSpace(
                "ram",
                space_id=1,
                space_type=17,
                is_memory=True,
                is_register=False,
                is_stack=False,
            ),
        })
    )
    summarizer = StructuralRecurrenceSummarizer(tracer, debug=False)

    profile = summarizer._build_loop_side_effect_profile(loop_blocks=[body])

    effect = profile.effect_descriptors[0]
    assert effect.address_space["encoding"] == "ghidra_store_space_id"
    assert effect.address_space["space_name"] == "ram"
    assert effect.address_space["space_id"] == 1
    assert effect.address_space["is_memory_space"] is True
    assert effect.address_space["pcode_space_id_constant"] == 1
    assert effect.address_space["pcode_input_space"]["space_name"] == "const"
    assert effect.stable_key() is not None


def test_counted_scalar_loop_summary_declines_unsupported_call_effect():
    analysis = create_mock_analysis(
        "counted_loop_call",
        return_type="int",
        parameters=[{"name": "param_1", "index": 0, "data_type": "int", "size": 4}],
        returns=[],
    )
    analysis.effect_summary = EffectSummary(
        parameter_names=["param_1"],
        effects=[],
        has_unsupported_call=True,
    )

    summarizer = StructuralRecurrenceSummarizer(_FakeTracer("unused", _const(0)), debug=False)

    assert summarizer._analysis_is_safe_for_counted_scalar_summary(analysis) is False


def test_loop_side_effect_profile_classifies_body_guards_calls_and_escapes():
    guard_expr = Expression.binary_op("INT_EQUAL", _param("param_1"), _const(0))
    body = _FakeCfgBlock(
        1,
        ops=[
            _FakePcodeOp("CBRANCH", [_FakeVarnode("target"), _FakeArgVarnode(guard_expr)], None),
            _FakePcodeOp("STORE", [], None),
            _FakePcodeOp("CALL", [_FakeVarnode("direct_target")], None),
            _FakePcodeOp("CALLIND", [_FakeVarnode("indirect_target")], None),
            _FakePcodeOp("BRANCHIND", [_FakeVarnode("escape_target")], None),
        ],
    )
    summarizer = StructuralRecurrenceSummarizer(_FakeTracer("callee", _const(0)), debug=False)

    profile = summarizer._build_loop_side_effect_profile(loop_blocks=[body])

    assert profile.profile == "effect_unknown"
    assert profile.memory_writes is True
    assert profile.calls is True
    assert profile.escapes is True
    assert profile.conditional_guards is True
    assert any(effect.kind == "conditional_guard" for effect in profile.effect_descriptors)
    assert any(effect.kind == "memory_write" for effect in profile.effect_descriptors)
    assert any(effect.kind == "call" for effect in profile.effect_descriptors)
    assert any(effect.kind == "escape" for effect in profile.effect_descriptors)
    assert any(
        effect.kind == "memory_write" and effect.keyable is False
        for effect in profile.effect_descriptors
    )
    assert all(
        effect.source == "pcode_scan" and effect.scope == "loop"
        for effect in profile.effect_descriptors
    )


def test_loop_effect_profile_keeps_function_and_loop_effect_origins_separate():
    analysis = create_mock_analysis(
        "loop_effect_origins",
        return_type="int",
        parameters=[{"name": "param_1", "index": 0, "data_type": "int *", "size": 8}],
        returns=[],
    )
    analysis.effect_summary = EffectSummary(
        parameter_names=["param_1"],
        effects=[
            StoreEffect(
                location=CanonicalLocation(
                    base_ref=LocationBaseRef.parameter("param_1", index=0),
                    offset=4,
                    size=4,
                ),
                value=_const(11),
                conditions=[],
                order_key=3,
            ),
        ],
    )
    body = _FakeCfgBlock(1, ops=[_FakePcodeOp("STORE", [], None)])
    summarizer = StructuralRecurrenceSummarizer(_FakeTracer("unused", _const(0)), debug=False)

    profile = summarizer._build_loop_side_effect_profile(analysis=analysis, loop_blocks=[body])

    loop_sources = [(effect.source, effect.scope) for effect in profile.effect_descriptors]
    context_sources = [(effect.source, effect.scope) for effect in profile.context_descriptors]
    assert ("function_effect_summary", "function") in context_sources
    assert ("pcode_scan", "loop") in loop_sources


def test_loop_body_block_collection_includes_header_and_latch_effects():
    summarizer = StructuralRecurrenceSummarizer(_FakeTracer("unused", _const(0)), debug=False)
    guard_expr = Expression.binary_op("INT_SLESS", _param("param_1"), _const(8))
    header_branch = _FakePcodeOp("CBRANCH", [_FakeVarnode("header_target"), _FakeArgVarnode(guard_expr)], None)
    header = _FakeCfgBlock(0, ops=[header_branch, _FakePcodeOp("STORE", [], None)])
    body = _FakeCfgBlock(1)
    latch = _FakeCfgBlock(2, ops=[_FakePcodeOp("STORE", [], None)])
    exit_block = _FakeCfgBlock(3)
    header.add_edge(body, truth=True)
    header.add_edge(exit_block, truth=False)
    body.add_edge(latch)
    latch.add_edge(header)
    guard = CountedLoopGuard(
        condition_expr=guard_expr,
        bound_expr=_const(8),
        continue_on_true=True,
        body_block=body,
        exit_block=exit_block,
        signed_comparison=True,
        latch_block=latch,
    )

    loop_blocks = summarizer._collect_loop_body_blocks(header_block=header, guard=guard)
    profile = summarizer._build_loop_side_effect_profile(
        loop_blocks=loop_blocks,
        ignored_branch_ops=[header_branch],
    )

    assert {block.getIndex() for block in loop_blocks} == {0, 1, 2}
    assert profile.memory_writes is True
    assert profile.conditional_guards is False
    assert sum(1 for effect in profile.effect_descriptors if effect.kind == "memory_write") == 2


def test_loop_body_block_collection_uses_natural_loop_boundary():
    summarizer = StructuralRecurrenceSummarizer(_FakeTracer("unused", _const(0)), debug=False)
    guard_expr = Expression.binary_op("INT_SLESS", _param("param_1"), _const(8))
    header = _FakeCfgBlock(0)
    body = _FakeCfgBlock(1)
    latch = _FakeCfgBlock(2)
    cleanup = _FakeCfgBlock(3, ops=[_FakePcodeOp("STORE", [], None)])
    exit_block = _FakeCfgBlock(4)
    header.add_edge(body, truth=True)
    header.add_edge(exit_block, truth=False)
    body.add_edge(latch)
    body.add_edge(cleanup)
    latch.add_edge(header)
    cleanup.add_edge(exit_block)
    guard = CountedLoopGuard(
        condition_expr=guard_expr,
        bound_expr=_const(8),
        continue_on_true=True,
        body_block=body,
        exit_block=exit_block,
        signed_comparison=True,
        latch_block=latch,
    )

    loop_blocks = summarizer._collect_loop_body_blocks(header_block=header, guard=guard)

    assert {block.getIndex() for block in loop_blocks} == {0, 1, 2}


def test_loop_store_effect_carries_block_control_guard():
    summarizer = StructuralRecurrenceSummarizer(_FakeTracer("unused", _const(0)), debug=False)
    guard_expr = Expression.binary_op("INT_EQUAL", Expression.binary_op("INT_AND", _param("param_1"), _const(1)), _const(0))
    header = _FakeCfgBlock(0)
    body_branch = _FakePcodeOp("CBRANCH", [_FakeVarnode("body_target"), _FakeArgVarnode(guard_expr)], None)
    body = _FakeCfgBlock(1, ops=[body_branch])
    store_block = _FakeCfgBlock(
        2,
        ops=[
            _FakePcodeOp(
                "STORE",
                [
                    _FakeVarnode("ram"),
                    _FakeArgVarnode(Expression.parameter("out", index=0, data_type="int *", size=8)),
                    _FakeArgVarnode(_param("param_1")),
                ],
                None,
            )
        ],
    )
    latch = _FakeCfgBlock(3)
    exit_block = _FakeCfgBlock(4)
    header.add_edge(body, truth=True)
    header.add_edge(exit_block, truth=False)
    body.add_edge(store_block, truth=True)
    body.add_edge(latch, truth=False)
    store_block.add_edge(latch)
    latch.add_edge(header)
    guard = CountedLoopGuard(
        condition_expr=Expression.binary_op("INT_SLESS", _param("param_1"), _const(8)),
        bound_expr=_const(8),
        continue_on_true=True,
        body_block=body,
        exit_block=exit_block,
        signed_comparison=True,
        latch_block=latch,
    )
    loop_blocks = summarizer._collect_loop_body_blocks(header_block=header, guard=guard)
    block_guard_info = summarizer._loop_block_guard_effect_info(
        header_block=header,
        guard=guard,
        loop_blocks=loop_blocks,
    )

    profile = summarizer._build_loop_side_effect_profile(
        loop_blocks=loop_blocks,
        ignored_branch_ops=[],
        block_guard_info=block_guard_info,
    )

    store_effect = next(effect for effect in profile.effect_descriptors if effect.kind == "memory_write")
    assert len(store_effect.guard_constraints) == 1
    assert store_effect.guard_constraints[0].expression.equals(guard_expr)
    assert len(store_effect.path_condition_sets) == 1
    assert len(store_effect.path_condition_sets[0]) == 1
    assert store_effect.path_condition_sets[0][0].expression.equals(guard_expr)
    assert store_effect.guard_paths_incomplete is False


def test_store_effect_with_incomplete_guard_paths_is_unkeyable():
    summarizer = StructuralRecurrenceSummarizer(_FakeTracer("unused", _const(0)), debug=False)
    store_op = _FakePcodeOp(
        "STORE",
        [
            _FakeVarnode("ram"),
            _FakeArgVarnode(Expression.parameter("out", index=0, data_type="int *", size=8)),
            _FakeArgVarnode(_param("param_1")),
        ],
        None,
    )

    effect = summarizer._store_effect_ref_for_op(
        store_op,
        scope="loop",
        guard_paths_incomplete=True,
    )

    assert effect.keyable is False
    assert effect.guard_paths_incomplete is True
    assert "store_guard_paths_incomplete" in effect.unkeyable_reason
    assert effect.stable_key() is None


def test_path_enumeration_reports_incomplete_when_limit_is_reached():
    summarizer = StructuralRecurrenceSummarizer(_FakeTracer("unused", _const(0)), debug=False)
    header = _FakeCfgBlock(0)
    body = _FakeCfgBlock(1)
    left = _FakeCfgBlock(2)
    right = _FakeCfgBlock(3)
    target = _FakeCfgBlock(4)
    exit_block = _FakeCfgBlock(5)
    body.add_edge(left)
    body.add_edge(right)
    left.add_edge(target)
    right.add_edge(target)
    target.add_edge(header)

    paths, incomplete = summarizer._enumerate_paths_with_conditions_result(
        start_block=body,
        target_block=target,
        header_block=header,
        placeholders={},
        stop_block=exit_block,
        limit=1,
    )

    assert len(paths) == 1
    assert incomplete is True


def test_counted_scalar_loop_summary_rejects_unresolved_operands():
    summarizer = StructuralRecurrenceSummarizer(_FakeTracer("unused", _const(0)), debug=False)
    summary_value = summarizer._build_counted_loop_summary_value(
        base_expr=_const(0),
        start_expr=Expression.unknown("phi_circular"),
        limit_expr=_param("param_1"),
        induction_step=1,
        residue_cases=(
            ResidueLoopCase(modulus=2, residue=0, affine=(1, 0)),
            ResidueLoopCase(modulus=2, residue=1, affine=(-1, 0)),
        ),
        result_size=4,
        signed_loop=True,
    )

    assert summary_value is None


def test_canonicalize_peeled_counted_loop_value_rewrites_proven_phi_start(monkeypatch):
    summarizer = StructuralRecurrenceSummarizer(_FakeTracer("unused", _const(0)), debug=False)
    start_expr = Expression.phi(
        [
            (None, _const(0)),
            (
                _cond("INT_NOTEQUAL", Expression.binary_op("INT_AND", _param(), _const(0xFFFFFFF8)), _param()),
                Expression.binary_op("INT_AND", _param(), _const(0xFFFFFFF8)),
            ),
        ]
    )
    original = Expression.intrinsic(
        "COUNTED_LOOP_SUM",
        [_const(0), start_expr, _param()],
        size=4,
        runtime_ref=CountedLoopSummaryRef(
            induction_step=1,
            result_size=4,
            signed_loop=True,
            residue_cases=((2, 0, 1, 0), (2, 1, -1, 0)),
        ),
        opcode=COUNTED_LOOP_SUM_OPCODE,
    )
    monkeypatch.setattr(
        summarizer,
        "_prove_expression_equivalence_under_conditions",
        lambda *_args, **_kwargs: True,
    )

    rewritten = summarizer._canonicalize_peeled_counted_loop_value(
        original,
        continue_conditions=[_cond("INT_SLESS", _const(0), _param())],
        parameters=[{"name": "param_1", "index": 0, "size": 4, "data_type": "int"}],
        base_expr=_const(0),
        limit_expr=_param(),
        induction_step=1,
        residue_cases=(
            ResidueLoopCase(modulus=2, residue=0, affine=(1, 0)),
            ResidueLoopCase(modulus=2, residue=1, affine=(-1, 0)),
        ),
        result_size=4,
        signed_loop=True,
    )

    assert rewritten is not None
    assert rewritten.expr_type == ExpressionType.INTRINSIC
    assert rewritten.operands[1].expr_type == ExpressionType.CONSTANT
    assert rewritten.operands[1].value == 0


def test_canonicalize_peeled_counted_loop_value_keeps_original_when_unproved(monkeypatch):
    summarizer = StructuralRecurrenceSummarizer(_FakeTracer("unused", _const(0)), debug=False)
    start_expr = Expression.phi(
        [
            (None, _const(0)),
            (_cond("INT_SLESS", _const(0), _param()), Expression.binary_op("INT_AND", _param(), _const(0xFFFFFFF8))),
        ]
    )
    original = Expression.intrinsic(
        "COUNTED_LOOP_SUM",
        [_const(0), start_expr, _param()],
        size=4,
        runtime_ref=CountedLoopSummaryRef(
            induction_step=1,
            result_size=4,
            signed_loop=True,
            residue_cases=((2, 0, 1, 0), (2, 1, -1, 0)),
        ),
        opcode=COUNTED_LOOP_SUM_OPCODE,
    )
    monkeypatch.setattr(
        summarizer,
        "_prove_expression_equivalence_under_conditions",
        lambda *_args, **_kwargs: False,
    )

    rewritten = summarizer._canonicalize_peeled_counted_loop_value(
        original,
        continue_conditions=[_cond("INT_SLESS", _const(0), _param())],
        parameters=[{"name": "param_1", "index": 0, "size": 4, "data_type": "int"}],
        base_expr=_const(0),
        limit_expr=_param(),
        induction_step=1,
        residue_cases=(
            ResidueLoopCase(modulus=2, residue=0, affine=(1, 0)),
            ResidueLoopCase(modulus=2, residue=1, affine=(-1, 0)),
        ),
        result_size=4,
        signed_loop=True,
    )

    assert rewritten is original


def test_counted_scalar_loop_summary_recovers_when_analysis_erases_loop_effect(monkeypatch):
    analysis = create_mock_analysis(
        "branch_for_accumulate",
        return_type="int",
        parameters=[{"name": "param_1", "index": 0, "data_type": "int", "size": 4}],
        returns=[
            ReturnInfo(
                address="0x1000",
                value=_const(0),
                conditions=[],
            ),
            ReturnInfo(
                address="0x1004",
                value=_const(0),
                conditions=[_cond("INT_SLESS", _const(0), _param("param_1"))],
            ),
        ],
    )
    analysis.effect_summary = EffectSummary(parameter_names=["param_1"], effects=[])

    summarizer = StructuralRecurrenceSummarizer(_FakeTracer("unused", _const(0)), debug=False)
    induction = CountedLoopInduction(
        phi_op=_FakePcodeOp("MULTIEQUAL", [], _FakeVarnode("iv_phi")),
        phi_output=_FakeVarnode("iv_phi"),
        init_expr=_const(0),
        backedge_index=0,
        step=1,
        placeholder=Expression.parameter("__loop_iv", index=-1, size=4),
        signed_guard=True,
        init_index=1,
        backedge_indices=(0,),
    )
    accumulator = CountedLoopAccumulator(
        phi_op=_FakePcodeOp("MULTIEQUAL", [], _FakeVarnode("acc_phi")),
        phi_output=_FakeVarnode("acc_phi"),
        init_expr=_const(0),
        backedge_index=0,
        placeholder=Expression.variable("__loop_acc", size=4),
        init_index=1,
        backedge_indices=(0,),
    )
    guard = CountedLoopGuard(
        condition_expr=Expression.binary_op("INT_SLESS", induction.placeholder, _param("param_1")),
        bound_expr=_param("param_1"),
        continue_on_true=True,
        body_block=object(),
        exit_block=object(),
        signed_comparison=True,
    )

    monkeypatch.setattr(
        summarizer,
        "_extract_counted_scalar_loop_model",
        lambda *_args, **_kwargs: (
            induction,
            accumulator,
            guard,
            (
                ResidueLoopCase(modulus=2, residue=0, affine=(1, 0)),
                ResidueLoopCase(modulus=2, residue=1, affine=(-1, 0)),
            ),
        ),
    )
    monkeypatch.setattr(
        summarizer,
        "_derive_direct_counted_loop_conditions",
        lambda *_args, **_kwargs: (
            [_cond("INT_SLESS", _const(0), _param("param_1"), negated=True)],
            [_cond("INT_SLESS", _const(0), _param("param_1"))],
        ),
    )

    summary = summarizer._build_counted_scalar_loop_summary(
        _FakeFunction("branch_for_accumulate"),
        _FakeCfgHighFunction([]),
        analysis,
    )

    assert summary is not None
    summarized_returns, note = summary
    assert note == "counted_scalar_loop_summary"
    assert any(ret.value.expr_type == ExpressionType.INTRINSIC for ret in summarized_returns)
    base_case = next(ret for ret in summarized_returns if ret.value.expr_type != ExpressionType.INTRINSIC)
    loop_case = next(ret for ret in summarized_returns if ret.value.expr_type == ExpressionType.INTRINSIC)
    assert ConditionSimplifier.get_simplified_condition_string(base_case.conditions[0]) == "(param_1 <= 0)"
    assert ConditionSimplifier.get_simplified_condition_string(loop_case.conditions[0]) == "(0 < param_1)"


def test_repair_two_way_partition_conditions_preserves_existing_continue_conditions():
    summarizer = StructuralRecurrenceSummarizer(_FakeTracer("unused", _const(0)), debug=False)

    base_conditions = [_cond("INT_SLESS", _const(0), _param("param_1"), negated=True)]
    continue_conditions = [
        _cond("INT_SLESS", _const(0), _param("param_1")),
        _cond("INT_NOTEQUAL", Expression.binary_op("INT_AND", _param("param_1"), _const(1)), _const(0)),
    ]

    repaired_base, repaired_continue = summarizer._repair_two_way_partition_conditions(
        base_conditions,
        continue_conditions,
    )

    assert [cond.to_string() for cond in repaired_base] == ["(not (0 < param_1))"]
    assert [cond.to_string() for cond in repaired_continue] == [
        "(0 < param_1)",
        "((param_1 & 1) != 0)",
    ]


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


def test_structural_recurrence_summarizer_declines_readonly_reduction_from_exact_count_only():
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

    assert summary is None


def test_readonly_reduction_summary_preserves_nonzero_start_offset_object_centrically():
    params = [
        {"name": "param_1", "index": 0, "data_type": "int *", "size": 8},
        {"name": "param_2", "index": 1, "data_type": "int", "size": 4, "is_signed": True},
    ]
    ptr_param = Expression.parameter("param_1", index=0, data_type="int *", size=8)
    count_param = Expression.parameter("param_2", index=1, data_type="int", size=4)
    analysis = create_mock_analysis(
        "ptr_sum_window",
        return_type="int",
        parameters=params,
        returns=[
            ReturnInfo(
                address="0x1000",
                value=_const(0),
                conditions=[_cond("INT_EQUAL", ptr_param, Expression.constant(0, size=8))],
            ),
            ReturnInfo(
                address="0x1004",
                value=_const(0),
                conditions=[
                    _cond("INT_NOTEQUAL", ptr_param, Expression.constant(0, size=8)),
                    _cond("INT_SLESSEQUAL", count_param, _const(1)),
                ],
            ),
            ReturnInfo(
                address="0x1008",
                value=Expression.unknown("phi_circular"),
                conditions=[
                    _cond("INT_NOTEQUAL", ptr_param, Expression.constant(0, size=8)),
                    _cond("INT_SLESS", _const(1), count_param),
                ],
            ),
        ],
    )

    ptr_varnode = _FakeVarnode(
        "param_1",
        size=8,
        expr=Expression.parameter("param_1", index=0, data_type="int *", size=8),
    )
    one32 = _FakeVarnode("one32", size=4, expr=Expression.constant(1, 4))
    four64 = _FakeVarnode("four64", size=8, expr=Expression.constant(4, 8))
    ram_space = _FakeVarnode("ram", size=8, expr=Expression.constant(0, 8))

    idx_high = _FakeHighVar("idx")
    idx_phi = _FakeVarnode("idx_phi", size=4, high=idx_high)
    idx_next = _FakeVarnode("idx_next", size=4)
    idx_add_op = _FakePcodeOp("INT_ADD", [idx_phi, one32], idx_next)
    idx_phi_op = _FakePcodeOp("MULTIEQUAL", [one32, idx_next], idx_phi)

    addr = _FakeVarnode("addr", size=8)
    ptradd_op = _FakePcodeOp("PTRADD", [ptr_varnode, idx_phi, four64], addr)
    load_value = _FakeVarnode("load_value", size=4)
    load_op = _FakePcodeOp("LOAD", [ram_space, addr], load_value)

    acc_high = _FakeHighVar("acc")
    acc_phi = _FakeVarnode("acc_phi", size=4, high=acc_high)
    acc_next = _FakeVarnode("acc_next", size=4)
    zero32 = _FakeVarnode("zero32", size=4, expr=Expression.constant(0, 4))
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
    positive_case = next(ret for ret in summarized_returns if ret.value.expr_type == ExpressionType.INTRINSIC)
    runtime_ref = positive_case.value.runtime_ref
    assert isinstance(runtime_ref, ReadonlyReductionRef)
    assert runtime_ref.reduction_kind == "memory_sum"
    assert runtime_ref.start_offset == 4
    assert runtime_ref.stride == 4
    assert isinstance(runtime_ref.loop_summary, LoopSummaryRef)
    assert runtime_ref.loop_summary.loop_var_unit == "element_index"
    assert runtime_ref.loop_summary.start_expr.equals(Expression.constant(1, size=4))
    assert runtime_ref.loop_summary.step_expr.equals(Expression.constant(1, size=4))
    assert runtime_ref.loop_summary.term_descriptor.start_offset == 0
    assert runtime_ref.loop_summary.term_descriptor.stride == 4
    assert runtime_ref.loop_summary.seed_terms == ()
    assert runtime_ref.loop_summary.witnesses == runtime_ref.semantic_witnesses
    assert loop_summary_method_b_key(runtime_ref.loop_summary) is not None
    assert runtime_ref.semantic_key() is not None
    assert runtime_ref.semantic_witnesses[:2] == (
        ReadonlyReductionWitness(
            exact_count=1,
            terms=(),
        ),
        ReadonlyReductionWitness(
            exact_count=2,
            terms=(ReadonlyReductionTermRef(byte_offset=4, access_size=4),),
        ),
    )
    assert [cond.to_string() for cond in positive_case.conditions] == ["(param_1 != 0)", "(1 < param_2)"]


def test_readonly_reduction_summary_records_prefix_seed_terms_from_accumulator_init():
    params = [
        {"name": "param_1", "index": 0, "data_type": "int *", "size": 8},
        {"name": "param_2", "index": 1, "data_type": "int", "size": 4, "is_signed": True},
    ]
    ptr_param = Expression.parameter("param_1", index=0, data_type="int *", size=8)
    count_param = Expression.parameter("param_2", index=1, data_type="int", size=4)
    analysis = create_mock_analysis(
        "ptr_sum_window",
        return_type="int",
        parameters=params,
        returns=[
            ReturnInfo(
                address="0x1000",
                value=_const(0),
                conditions=[_cond("INT_EQUAL", ptr_param, Expression.constant(0, size=8))],
            ),
            ReturnInfo(
                address="0x1004",
                value=_mem("param_1", 0),
                conditions=[
                    _cond("INT_NOTEQUAL", ptr_param, Expression.constant(0, size=8)),
                    _cond("INT_SLESSEQUAL", count_param, _const(1)),
                ],
            ),
            ReturnInfo(
                address="0x1008",
                value=Expression.unknown("phi_circular"),
                conditions=[
                    _cond("INT_NOTEQUAL", ptr_param, Expression.constant(0, size=8)),
                    _cond("INT_SLESS", _const(1), count_param),
                ],
            ),
        ],
    )

    ptr_varnode = _FakeVarnode(
        "param_1",
        size=8,
        expr=Expression.parameter("param_1", index=0, data_type="int *", size=8),
    )
    one32 = _FakeVarnode("one32", size=4, expr=Expression.constant(1, 4))
    four64 = _FakeVarnode("four64", size=8, expr=Expression.constant(4, 8))
    ram_space = _FakeVarnode("ram", size=8, expr=Expression.constant(0, 8))

    idx_high = _FakeHighVar("idx")
    idx_phi = _FakeVarnode("idx_phi", size=4, high=idx_high)
    idx_next = _FakeVarnode("idx_next", size=4)
    idx_add_op = _FakePcodeOp("INT_ADD", [idx_phi, one32], idx_next)
    idx_phi_op = _FakePcodeOp("MULTIEQUAL", [one32, idx_next], idx_phi)

    addr = _FakeVarnode("addr", size=8)
    ptradd_op = _FakePcodeOp("PTRADD", [ptr_varnode, idx_phi, four64], addr)
    load_value = _FakeVarnode("load_value", size=4)
    load_op = _FakePcodeOp("LOAD", [ram_space, addr], load_value)

    acc_high = _FakeHighVar("acc")
    acc_phi = _FakeVarnode("acc_phi", size=4, high=acc_high)
    acc_next = _FakeVarnode("acc_next", size=4)
    acc_seed = _FakeVarnode("acc_seed", size=4, expr=_mem("param_1", 0))
    acc_add_op = _FakePcodeOp("INT_ADD", [acc_phi, load_value], acc_next)
    acc_phi_op = _FakePcodeOp("MULTIEQUAL", [acc_seed, acc_next], acc_phi)

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
    positive_case = next(ret for ret in summarized_returns if ret.value.expr_type == ExpressionType.INTRINSIC)
    runtime_ref = positive_case.value.runtime_ref
    loop_summary = runtime_ref.loop_summary
    assert loop_summary.seed_terms == (ReadonlyReductionTermRef(byte_offset=0, access_size=4),)

    full_summary = LoopSummaryRef(
        start_expr=Expression.constant(0, size=4),
        limit_expr=loop_summary.limit_expr,
        step_expr=loop_summary.step_expr,
        term_descriptor=loop_summary.term_descriptor,
        side_effect_profile=loop_summary.side_effect_profile,
        loop_var_unit=loop_summary.loop_var_unit,
    )
    assert loop_summary_method_b_key(loop_summary) == loop_summary_method_b_key(full_summary)


def test_readonly_reduction_summary_records_non_unit_step_prefix_seed_terms():
    params = [
        {"name": "param_1", "index": 0, "data_type": "int *", "size": 8},
        {"name": "param_2", "index": 1, "data_type": "int", "size": 4, "is_signed": True},
    ]
    ptr_param = Expression.parameter("param_1", index=0, data_type="int *", size=8)
    count_param = Expression.parameter("param_2", index=1, data_type="int", size=4)
    analysis = create_mock_analysis(
        "ptr_sum_window",
        return_type="int",
        parameters=params,
        returns=[
            ReturnInfo(
                address="0x1000",
                value=_const(0),
                conditions=[_cond("INT_EQUAL", ptr_param, Expression.constant(0, size=8))],
            ),
            ReturnInfo(
                address="0x1004",
                value=_mem("param_1", 4),
                conditions=[
                    _cond("INT_NOTEQUAL", ptr_param, Expression.constant(0, size=8)),
                    _cond("INT_SLESSEQUAL", count_param, _const(3)),
                ],
            ),
            ReturnInfo(
                address="0x1008",
                value=Expression.unknown("phi_circular"),
                conditions=[
                    _cond("INT_NOTEQUAL", ptr_param, Expression.constant(0, size=8)),
                    _cond("INT_SLESS", _const(3), count_param),
                ],
            ),
        ],
    )

    ptr_varnode = _FakeVarnode(
        "param_1",
        size=8,
        expr=Expression.parameter("param_1", index=0, data_type="int *", size=8),
    )
    two32 = _FakeVarnode("two32", size=4, expr=Expression.constant(2, 4))
    three32 = _FakeVarnode("three32", size=4, expr=Expression.constant(3, 4))
    four64 = _FakeVarnode("four64", size=8, expr=Expression.constant(4, 8))
    ram_space = _FakeVarnode("ram", size=8, expr=Expression.constant(0, 8))

    idx_high = _FakeHighVar("idx")
    idx_phi = _FakeVarnode("idx_phi", size=4, high=idx_high)
    idx_next = _FakeVarnode("idx_next", size=4)
    idx_add_op = _FakePcodeOp("INT_ADD", [idx_phi, two32], idx_next)
    idx_phi_op = _FakePcodeOp("MULTIEQUAL", [three32, idx_next], idx_phi)

    addr = _FakeVarnode("addr", size=8)
    ptradd_op = _FakePcodeOp("PTRADD", [ptr_varnode, idx_phi, four64], addr)
    load_value = _FakeVarnode("load_value", size=4)
    load_op = _FakePcodeOp("LOAD", [ram_space, addr], load_value)

    acc_high = _FakeHighVar("acc")
    acc_phi = _FakeVarnode("acc_phi", size=4, high=acc_high)
    acc_next = _FakeVarnode("acc_next", size=4)
    acc_seed = _FakeVarnode("acc_seed", size=4, expr=_mem("param_1", 4))
    acc_add_op = _FakePcodeOp("INT_ADD", [acc_phi, load_value], acc_next)
    acc_phi_op = _FakePcodeOp("MULTIEQUAL", [acc_seed, acc_next], acc_phi)

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
    positive_case = next(ret for ret in summarized_returns if ret.value.expr_type == ExpressionType.INTRINSIC)
    runtime_ref = positive_case.value.runtime_ref
    loop_summary = runtime_ref.loop_summary
    assert runtime_ref.start_offset == 12
    assert runtime_ref.stride == 8
    assert loop_summary.start_expr.equals(Expression.constant(3, size=4))
    assert loop_summary.step_expr.equals(Expression.constant(2, size=4))
    assert loop_summary.seed_terms == (ReadonlyReductionTermRef(byte_offset=4, access_size=4),)

    full_summary = LoopSummaryRef(
        start_expr=Expression.constant(1, size=4),
        limit_expr=loop_summary.limit_expr,
        step_expr=loop_summary.step_expr,
        term_descriptor=loop_summary.term_descriptor,
        side_effect_profile=loop_summary.side_effect_profile,
        loop_var_unit=loop_summary.loop_var_unit,
    )
    assert loop_summary_method_b_key(loop_summary) == loop_summary_method_b_key(full_summary)


def test_readonly_reduction_detects_vector_pointer_loop_with_ptradd_tail():
    params = [
        {"name": "param_1", "index": 0, "data_type": "int *", "size": 8},
        {"name": "param_2", "index": 1, "data_type": "int", "size": 4, "is_signed": True},
    ]
    ptr_expr = Expression.parameter("param_1", index=0, data_type="int *", size=8)
    count_expr = Expression.parameter("param_2", index=1, data_type="int", size=4)
    vector_body_value = _mem("param_1", 0)
    for byte_offset in range(4, 32, 4):
        vector_body_value = Expression.binary_op(
            "INT_ADD",
            vector_body_value,
            _mem("param_1", byte_offset),
        )
    analysis = create_mock_analysis(
        "vector_prefix_sum",
        return_type="int",
        parameters=params,
        returns=[
            ReturnInfo(
                address="0x1000",
                value=vector_body_value,
                conditions=[
                    _cond("INT_NOTEQUAL", ptr_expr, Expression.constant(0, size=8)),
                    _cond("INT_SLESS", Expression.constant(0, size=4), count_expr),
                    _cond("INT_SLESSEQUAL", Expression.constant(8, size=4), count_expr),
                ],
            )
        ],
    )

    ptr_vn = _FakeVarnode("param_1", size=8, expr=ptr_expr)
    count_vn = _FakeVarnode("param_2", size=4, expr=count_expr)
    mask_vn = _FakeVarnode("mask", size=4, expr=Expression.constant(0xFFFFFFF8, size=4))
    rounded_vn = _FakeVarnode("rounded", size=4)
    round_op = _FakePcodeOp("INT_AND", [count_vn, mask_vn], rounded_vn)

    four_vn = _FakeVarnode("four", size=4, expr=Expression.constant(4, size=4))
    eight_vn = _FakeVarnode("eight", size=4, expr=Expression.constant(8, size=4))
    base_bias_vn = _FakeVarnode("base_bias", size=4, expr=Expression.constant(4, size=4))
    vector_init = _FakeVarnode("vector_init", size=8)
    vector_phi = _FakeVarnode("vector_phi", size=8, high=_FakeHighVar("vector_phi"))
    vector_next = _FakeVarnode("vector_next", size=8)
    vector_end_base = _FakeVarnode("vector_end_base", size=8)
    vector_end = _FakeVarnode("vector_end", size=8)
    vector_cond = _FakeVarnode("vector_cond", size=1)

    init_op = _FakePcodeOp("PTRADD", [ptr_vn, base_bias_vn, four_vn], vector_init)
    next_op = _FakePcodeOp("PTRADD", [vector_phi, eight_vn, four_vn], vector_next)
    vector_phi_op = _FakePcodeOp("MULTIEQUAL", [vector_init, vector_next], vector_phi)
    end_base_op = _FakePcodeOp("PTRADD", [ptr_vn, rounded_vn, four_vn], vector_end_base)
    end_op = _FakePcodeOp("INT_ADD", [vector_end_base, _FakeVarnode("sixteen", size=8, expr=Expression.constant(16, size=8))], vector_end)
    vector_cmp_op = _FakePcodeOp("INT_NOTEQUAL", [vector_phi, vector_end], vector_cond)

    ram_space = _FakeVarnode("ram", size=8, expr=Expression.constant(0, size=8))
    load_ops = []
    sum_ops = []
    running_sum = _FakeVarnode("sum_zero", size=4, expr=Expression.constant(0, size=4))
    for lane, index_value in enumerate(range(-4, 4)):
        index_vn = _FakeVarnode(f"lane_index_{lane}", size=4, expr=Expression.constant(index_value, size=4))
        addr_vn = _FakeVarnode(f"lane_addr_{lane}", size=8)
        value_vn = _FakeVarnode(f"lane_value_{lane}", size=4)
        next_sum = _FakeVarnode(f"sum_after_lane_{lane}", size=4)
        addr_op = _FakePcodeOp("PTRADD", [vector_phi, index_vn, four_vn], addr_vn)
        load_op = _FakePcodeOp("LOAD", [ram_space, addr_vn], value_vn)
        add_op = _FakePcodeOp("INT_ADD", [running_sum, value_vn], next_sum)
        load_ops.extend([addr_op, load_op])
        sum_ops.append(add_op)
        running_sum = next_sum

    tail_start = _FakeVarnode("tail_start", size=8)
    tail_next = _FakeVarnode("tail_next", size=8)
    tail_phi = _FakeVarnode("tail_phi", size=8, high=_FakeHighVar("tail_phi"))
    tail_load = _FakeVarnode("tail_load", size=4)
    tail_sum = _FakeVarnode("tail_sum", size=4)
    remaining_init = _FakeVarnode("remaining_init", size=8)
    remaining_phi = _FakeVarnode("remaining_phi", size=8, high=_FakeHighVar("remaining"))
    remaining_next = _FakeVarnode("remaining_next", size=8)
    remaining_cond = _FakeVarnode("remaining_cond", size=1)
    tail_start_op = _FakePcodeOp("PTRADD", [ptr_vn, rounded_vn, four_vn], tail_start)
    tail_next_op = _FakePcodeOp("PTRADD", [tail_phi, _FakeVarnode("one", size=4, expr=Expression.constant(1, size=4)), four_vn], tail_next)
    tail_phi_op = _FakePcodeOp("MULTIEQUAL", [tail_start, tail_next], tail_phi)
    tail_load_op = _FakePcodeOp("LOAD", [ram_space, tail_phi], tail_load)
    tail_add_op = _FakePcodeOp("INT_ADD", [running_sum, tail_load], tail_sum)
    return_op = _FakePcodeOp("RETURN", [_FakeVarnode("return_target", size=8), tail_sum], None)
    remaining_init_op = _FakePcodeOp("INT_SUB", [count_vn, rounded_vn], remaining_init)
    remaining_phi_op = _FakePcodeOp("MULTIEQUAL", [remaining_init, remaining_next], remaining_phi)
    remaining_next_op = _FakePcodeOp(
        "INT_ADD",
        [remaining_phi, _FakeVarnode("minus_one", size=8, expr=Expression.constant(-1, size=8))],
        remaining_next,
    )
    remaining_cmp_op = _FakePcodeOp(
        "INT_NOTEQUAL",
        [remaining_next, _FakeVarnode("zero64", size=8, expr=Expression.constant(0, size=8))],
        remaining_cond,
    )

    high_function = _FakeHighFunction(
        [
            round_op,
            init_op,
            next_op,
            vector_phi_op,
            end_base_op,
            end_op,
            vector_cmp_op,
            *load_ops,
            *sum_ops,
            tail_start_op,
            tail_next_op,
            tail_phi_op,
            tail_load_op,
            tail_add_op,
            return_op,
            remaining_init_op,
            remaining_phi_op,
            remaining_next_op,
            remaining_cmp_op,
        ]
    )
    tracer = _FakeTracer("unused", _const(0))
    tracer.trace_varnode = lambda varnode, *args, **kwargs: getattr(varnode, "_expr", None)
    summarizer = StructuralRecurrenceSummarizer(tracer, debug=False)

    proof = summarizer._detect_readonly_sum_accumulator_proof(high_function, analysis, params[0], params[1])

    assert proof is not None
    assert proof.stride == 4
    assert proof.element_size == 4
    assert proof.start_index == 0
    assert proof.index_step == 1
    assert proof.stable_key() is not None


def test_readonly_addend_proof_rejects_nonzero_constant_sibling():
    pointer_param = {"name": "param_1", "index": 0, "data_type": "int *", "size": 8}
    phi_vn = _FakeVarnode("ptr_phi", size=8)
    ram_space = _FakeVarnode("ram", size=8, expr=Expression.constant(0, size=8))
    load_vn = _FakeVarnode("load", size=4)
    const_five = _FakeVarnode("five", size=4, expr=Expression.constant(5, size=4))
    add_vn = _FakeVarnode("load_plus_five", size=4)
    _FakePcodeOp("LOAD", [ram_space, phi_vn], load_vn)
    _FakePcodeOp("INT_ADD", [load_vn, const_five], add_vn)
    tracer = _FakeTracer("unused", Expression.unknown("unknown"))
    tracer.trace_varnode = lambda varnode, *args, **kwargs: getattr(varnode, "_expr", None)
    summarizer = StructuralRecurrenceSummarizer(tracer, debug=False)

    progressions = summarizer._collect_load_progressions_from_varnode(
        add_vn,
        pointer_param,
        [
            {
                "phi_op": _FakePcodeOp("MULTIEQUAL", [], phi_vn),
                "phi_output": phi_vn,
                "stride": 4,
                "start_offset": 0,
                "start_index": 0,
                "index_step": 1,
                "index_scale": 4,
            }
        ],
        [],
    )

    assert progressions is None


def test_readonly_addend_proof_rejects_duplicate_load_terms():
    pointer_param = {"name": "param_1", "index": 0, "data_type": "int *", "size": 8}
    phi_vn = _FakeVarnode("ptr_phi", size=8)
    ram_space = _FakeVarnode("ram", size=8, expr=Expression.constant(0, size=8))
    load_vn = _FakeVarnode("load", size=4)
    doubled_vn = _FakeVarnode("load_plus_load", size=4)
    _FakePcodeOp("LOAD", [ram_space, phi_vn], load_vn)
    _FakePcodeOp("INT_ADD", [load_vn, load_vn], doubled_vn)
    tracer = _FakeTracer("unused", Expression.unknown("unknown"))
    tracer.trace_varnode = lambda varnode, *args, **kwargs: getattr(varnode, "_expr", None)
    summarizer = StructuralRecurrenceSummarizer(tracer, debug=False)
    load_progressions = summarizer._collect_load_progressions_from_varnode(
        doubled_vn,
        pointer_param,
        [
            {
                "phi_op": _FakePcodeOp("MULTIEQUAL", [], phi_vn),
                "phi_output": phi_vn,
                "stride": 4,
                "start_offset": 0,
                "start_index": 0,
                "index_step": 1,
                "index_scale": 4,
            }
        ],
        [],
    )

    assert load_progressions is not None
    assert summarizer._readonly_load_progression_term_counter(load_progressions, result_size=4) == {
        (0, 4): 2,
    }


def test_readonly_addend_proof_rejects_signed_extension_until_mode_is_represented():
    pointer_param = {"name": "param_1", "index": 0, "data_type": "char *", "size": 8}
    phi_vn = _FakeVarnode("ptr_phi", size=8)
    ram_space = _FakeVarnode("ram", size=8, expr=Expression.constant(0, size=8))
    load_vn = _FakeVarnode("load", size=1)
    sext_vn = _FakeVarnode("sext_load", size=4)
    _FakePcodeOp("LOAD", [ram_space, phi_vn], load_vn)
    _FakePcodeOp("INT_SEXT", [load_vn], sext_vn)
    tracer = _FakeTracer("unused", Expression.unknown("unknown"))
    tracer.trace_varnode = lambda varnode, *args, **kwargs: getattr(varnode, "_expr", None)
    summarizer = StructuralRecurrenceSummarizer(tracer, debug=False)

    progressions = summarizer._collect_load_progressions_from_varnode(
        sext_vn,
        pointer_param,
        [
            {
                "phi_op": _FakePcodeOp("MULTIEQUAL", [], phi_vn),
                "phi_output": phi_vn,
                "stride": 1,
                "start_offset": 0,
                "start_index": 0,
                "index_step": 1,
                "index_scale": 1,
            }
        ],
        [],
    )

    assert progressions is None


def test_readonly_exact_expression_extracts_terms_and_constant_bias_object_centrically():
    pointer_param = {"name": "param_1", "index": 0, "data_type": "int *", "size": 8}
    expr = Expression.binary_op("INT_ADD", _mem("param_1", 0), Expression.constant(5, size=4))
    summarizer = StructuralRecurrenceSummarizer(_FakeTracer("unused", Expression.unknown("unknown")), debug=False)

    extracted = summarizer._extract_readonly_reduction_terms_and_bias(
        expr,
        [pointer_param],
        pointer_param,
    )

    assert extracted == (
        (ReadonlyReductionTermRef(byte_offset=0, access_size=4),),
        5,
    )
    assert summarizer._extract_readonly_reduction_terms(expr, [pointer_param], pointer_param) is None


def test_readonly_exact_return_witness_rejects_bias_width_mismatch():
    pointer_param = {"name": "param_1", "index": 0, "data_type": "int *", "size": 8}
    count_param = {"name": "param_2", "index": 1, "data_type": "int", "size": 4, "is_signed": True}
    count_expr = Expression.parameter("param_2", index=1, data_type="int", size=4)
    proof = ReductionAccumulatorProof(
        reduction_kind="memory_sum",
        pointer_base_ref=LocationBaseRef.parameter("param_1", index=0),
        count_parameter_name="param_2",
        count_parameter_index=1,
        limit_expr=count_expr,
        result_size=4,
        stride=4,
        element_size=4,
    )
    wide_bias = Expression.constant(1 << 32, size=8)
    wide_return = Expression.binary_op("INT_ADD", _mem("param_1", 0), wide_bias)
    wide_return.size = 8
    ret = ReturnInfo(
        address="0x2000",
        value=wide_return,
        conditions=[_cond("INT_EQUAL", count_expr, _const(1))],
    )
    analysis = create_mock_analysis(
        "readonly_wide_bias",
        return_type="long",
        parameters=[pointer_param, count_param],
        returns=[ret],
    )
    summarizer = StructuralRecurrenceSummarizer(_FakeTracer("unused", Expression.unknown("unknown")), debug=False)

    witnesses = summarizer._extract_readonly_reduction_exact_witnesses(
        analysis,
        pointer_param,
        count_param,
        [ret],
        proof,
    )

    assert witnesses == ()


def test_readonly_addend_proof_rejects_signed_extension_behind_copy():
    pointer_param = {"name": "param_1", "index": 0, "data_type": "char *", "size": 8}
    phi_vn = _FakeVarnode("ptr_phi", size=8)
    ram_space = _FakeVarnode("ram", size=8, expr=Expression.constant(0, size=8))
    load_vn = _FakeVarnode("load", size=1)
    sext_vn = _FakeVarnode("sext_load", size=4)
    copy_vn = _FakeVarnode("copy_sext_load", size=4)
    _FakePcodeOp("LOAD", [ram_space, phi_vn], load_vn)
    _FakePcodeOp("INT_SEXT", [load_vn], sext_vn)
    _FakePcodeOp("COPY", [sext_vn], copy_vn)
    tracer = _FakeTracer("unused", Expression.unknown("unknown"))
    tracer.trace_varnode = lambda varnode, *args, **kwargs: getattr(varnode, "_expr", None)
    summarizer = StructuralRecurrenceSummarizer(tracer, debug=False)

    progressions = summarizer._collect_load_progressions_from_varnode(
        copy_vn,
        pointer_param,
        [
            {
                "phi_op": _FakePcodeOp("MULTIEQUAL", [], phi_vn),
                "phi_output": phi_vn,
                "stride": 1,
                "start_offset": 0,
                "start_index": 0,
                "index_step": 1,
                "index_scale": 1,
            }
        ],
        [],
    )

    assert progressions is None


def test_readonly_addend_proof_preserves_subpiece_behind_copy():
    pointer_param = {"name": "param_1", "index": 0, "data_type": "int *", "size": 8}
    phi_vn = _FakeVarnode("ptr_phi", size=8)
    ram_space = _FakeVarnode("ram", size=8, expr=Expression.constant(0, size=8))
    load_vn = _FakeVarnode("load", size=4)
    offset_vn = _FakeVarnode("offset", size=4, expr=Expression.constant(1, size=4))
    subpiece_vn = _FakeVarnode("subpiece", size=2)
    copy_vn = _FakeVarnode("copy_subpiece", size=2)
    mask_vn = _FakeVarnode("mask", size=4, expr=Expression.constant(0xFF, size=4))
    masked_copy_vn = _FakeVarnode("masked_copy_subpiece", size=2)
    _FakePcodeOp("LOAD", [ram_space, phi_vn], load_vn)
    _FakePcodeOp("SUBPIECE", [load_vn, offset_vn], subpiece_vn)
    _FakePcodeOp("COPY", [subpiece_vn], copy_vn)
    _FakePcodeOp("INT_AND", [copy_vn, mask_vn], masked_copy_vn)
    tracer = _FakeTracer("unused", Expression.unknown("unknown"))
    tracer.trace_varnode = lambda varnode, *args, **kwargs: getattr(varnode, "_expr", None)
    summarizer = StructuralRecurrenceSummarizer(tracer, debug=False)
    pointer_phis = [
        {
            "phi_op": _FakePcodeOp("MULTIEQUAL", [], phi_vn),
            "phi_output": phi_vn,
            "stride": 4,
            "start_offset": 0,
            "start_index": 0,
            "index_step": 1,
            "index_scale": 4,
        }
    ]

    progressions = summarizer._collect_load_progressions_from_varnode(
        copy_vn,
        pointer_param,
        pointer_phis,
        [],
    )
    masked_progressions = summarizer._collect_load_progressions_from_varnode(
        masked_copy_vn,
        pointer_param,
        pointer_phis,
        [],
    )

    assert progressions is not None
    assert progressions[0]["start_offset"] == 1
    assert progressions[0]["element_size"] == 2
    assert masked_progressions is not None
    assert masked_progressions[0]["start_offset"] == 1
    assert masked_progressions[0]["element_size"] == 1


def test_readonly_addend_proof_reflects_mask_and_subpiece_access_size():
    pointer_param = {"name": "param_1", "index": 0, "data_type": "int *", "size": 8}
    phi_vn = _FakeVarnode("ptr_phi", size=8)
    ram_space = _FakeVarnode("ram", size=8, expr=Expression.constant(0, size=8))
    load_vn = _FakeVarnode("load", size=4)
    mask_vn = _FakeVarnode("mask", size=4, expr=Expression.constant(0xFF, size=4))
    masked_vn = _FakeVarnode("masked", size=4)
    offset_vn = _FakeVarnode("offset", size=4, expr=Expression.constant(1, size=4))
    subpiece_vn = _FakeVarnode("subpiece", size=2)
    _FakePcodeOp("LOAD", [ram_space, phi_vn], load_vn)
    _FakePcodeOp("INT_AND", [load_vn, mask_vn], masked_vn)
    _FakePcodeOp("SUBPIECE", [load_vn, offset_vn], subpiece_vn)
    pointer_phis = [
        {
            "phi_op": _FakePcodeOp("MULTIEQUAL", [], phi_vn),
            "phi_output": phi_vn,
            "stride": 4,
            "start_offset": 0,
            "start_index": 0,
            "index_step": 1,
            "index_scale": 4,
        }
    ]
    tracer = _FakeTracer("unused", Expression.unknown("unknown"))
    tracer.trace_varnode = lambda varnode, *args, **kwargs: getattr(varnode, "_expr", None)
    summarizer = StructuralRecurrenceSummarizer(tracer, debug=False)

    masked_progressions = summarizer._collect_load_progressions_from_varnode(
        masked_vn,
        pointer_param,
        pointer_phis,
        [],
    )
    subpiece_progressions = summarizer._collect_load_progressions_from_varnode(
        subpiece_vn,
        pointer_param,
        pointer_phis,
        [],
    )

    assert masked_progressions is not None
    assert masked_progressions[0]["start_offset"] == 0
    assert masked_progressions[0]["element_size"] == 1
    assert subpiece_progressions is not None
    assert subpiece_progressions[0]["start_offset"] == 1
    assert subpiece_progressions[0]["element_size"] == 2


def test_vector_prefix_lanes_must_flow_additively_to_return():
    ptr_expr = Expression.parameter("param_1", index=0, data_type="int *", size=8)
    ptr_vn = _FakeVarnode("param_1", size=8, expr=ptr_expr)
    four_vn = _FakeVarnode("four", size=8, expr=Expression.constant(4, size=8))
    vector_phi = _FakeVarnode("vector_phi", size=8, high=_FakeHighVar("vector_phi"))
    ram_space = _FakeVarnode("ram", size=8, expr=Expression.constant(0, size=8))
    ops = []
    for lane, index_value in enumerate(range(4)):
        index_vn = _FakeVarnode(f"lane_index_{lane}", size=8, expr=Expression.constant(index_value, size=8))
        addr_vn = _FakeVarnode(f"lane_addr_{lane}", size=8)
        value_vn = _FakeVarnode(f"lane_value_{lane}", size=4)
        product_vn = _FakeVarnode(f"product_{lane}", size=4)
        addr_op = _FakePcodeOp("PTRADD", [vector_phi, index_vn, four_vn], addr_vn)
        load_op = _FakePcodeOp("LOAD", [ram_space, addr_vn], value_vn)
        mul_op = _FakePcodeOp("INT_MULT", [value_vn, _FakeVarnode("two", size=4, expr=Expression.constant(2, size=4))], product_vn)
        ops.extend([addr_op, load_op, mul_op])
    return_op = _FakePcodeOp("RETURN", [_FakeVarnode("return_target", size=8), product_vn], None)
    ops.append(return_op)

    tracer = _FakeTracer("unused", Expression.unknown("untraced"))
    tracer.trace_varnode = lambda varnode, *args, **kwargs: getattr(varnode, "_expr", None)
    summarizer = StructuralRecurrenceSummarizer(tracer, debug=False)

    assert not summarizer._vector_prefix_lanes_contribute_additively_to_return(
        ops,
        vector_phi,
        base_offset=0,
        vector_stride=16,
        element_size=4,
    )


def test_vector_prefix_lanes_must_contribute_with_coefficient_one():
    vector_phi = _FakeVarnode("vector_phi", size=8, high=_FakeHighVar("vector_phi"))
    four_vn = _FakeVarnode("four", size=8, expr=Expression.constant(4, size=8))
    ram_space = _FakeVarnode("ram", size=8, expr=Expression.constant(0, size=8))
    running_sum = _FakeVarnode("sum_zero", size=4, expr=Expression.constant(0, size=4))
    ops = []
    for lane, index_value in enumerate(range(4)):
        index_vn = _FakeVarnode(f"lane_index_{lane}", size=8, expr=Expression.constant(index_value, size=8))
        addr_vn = _FakeVarnode(f"lane_addr_{lane}", size=8)
        value_vn = _FakeVarnode(f"lane_value_{lane}", size=4)
        addend_vn = _FakeVarnode(f"lane_addend_{lane}", size=4)
        next_sum = _FakeVarnode(f"sum_after_lane_{lane}", size=4)
        addr_op = _FakePcodeOp("PTRADD", [vector_phi, index_vn, four_vn], addr_vn)
        load_op = _FakePcodeOp("LOAD", [ram_space, addr_vn], value_vn)
        if lane == 0:
            duplicate_op = _FakePcodeOp("INT_ADD", [value_vn, value_vn], addend_vn)
            ops.append(duplicate_op)
        else:
            addend_vn = value_vn
        add_op = _FakePcodeOp("INT_ADD", [running_sum, addend_vn], next_sum)
        ops.extend([addr_op, load_op, add_op])
        running_sum = next_sum
    return_op = _FakePcodeOp("RETURN", [_FakeVarnode("return_target", size=8), running_sum], None)
    ops.append(return_op)

    summarizer = StructuralRecurrenceSummarizer(_FakeTracer("unused", _const(0)), debug=False)

    assert not summarizer._vector_prefix_lanes_contribute_additively_to_return(
        ops,
        vector_phi,
        base_offset=0,
        vector_stride=16,
        element_size=4,
    )


def test_vector_prefix_lanes_reject_duplicate_loads_from_same_offset():
    vector_phi = _FakeVarnode("vector_phi", size=8, high=_FakeHighVar("vector_phi"))
    four_vn = _FakeVarnode("four", size=8, expr=Expression.constant(4, size=8))
    one_vn = _FakeVarnode("one", size=8, expr=Expression.constant(1, size=8))
    ram_space = _FakeVarnode("ram", size=8, expr=Expression.constant(0, size=8))
    lane0_a = _FakeVarnode("lane0_a", size=4)
    lane0_b = _FakeVarnode("lane0_b", size=4)
    lane1_addr = _FakeVarnode("lane1_addr", size=8)
    lane1 = _FakeVarnode("lane1", size=4)
    sum0 = _FakeVarnode("sum0", size=4)
    sum1 = _FakeVarnode("sum1", size=4)
    sum2 = _FakeVarnode("sum2", size=4)
    ops = [
        _FakePcodeOp("LOAD", [ram_space, vector_phi], lane0_a),
        _FakePcodeOp("LOAD", [ram_space, vector_phi], lane0_b),
        _FakePcodeOp("PTRADD", [vector_phi, one_vn, four_vn], lane1_addr),
        _FakePcodeOp("LOAD", [ram_space, lane1_addr], lane1),
        _FakePcodeOp("INT_ADD", [_FakeVarnode("zero", size=4, expr=Expression.constant(0, size=4)), lane0_a], sum0),
        _FakePcodeOp("INT_ADD", [sum0, lane0_b], sum1),
        _FakePcodeOp("INT_ADD", [sum1, lane1], sum2),
        _FakePcodeOp("RETURN", [_FakeVarnode("return_target", size=8), sum2], None),
    ]
    summarizer = StructuralRecurrenceSummarizer(_FakeTracer("unused", _const(0)), debug=False)

    assert not summarizer._vector_prefix_lanes_contribute_additively_to_return(
        ops,
        vector_phi,
        base_offset=0,
        vector_stride=8,
        element_size=4,
    )


def test_vector_prefix_return_term_proof_rejects_duplicated_lane():
    pointer_param = {"name": "param_1", "index": 0, "data_type": "int *", "size": 8}
    analysis = create_mock_analysis(
        "vector_prefix_sum",
        return_type="int",
        parameters=[
            pointer_param,
            {"name": "param_2", "index": 1, "data_type": "int", "size": 4},
        ],
        returns=[
            ReturnInfo(
                address="0x1000",
                value=Expression.binary_op(
                    "INT_ADD",
                    Expression.binary_op("INT_ADD", _mem("param_1", 0), _mem("param_1", 0)),
                    _mem("param_1", 4),
                ),
                conditions=[],
            )
        ],
    )
    summarizer = StructuralRecurrenceSummarizer(_FakeTracer("unused", _const(0)), debug=False)

    assert summarizer._vector_prefix_lanes_have_unit_terms_in_positive_return(
        analysis,
        pointer_param,
        [],
        vector_stride=8,
        element_size=4,
    ) is False


def test_vector_prefix_return_term_proof_requires_all_overlapping_returns():
    pointer_param = {"name": "param_1", "index": 0, "data_type": "int *", "size": 8}
    analysis = create_mock_analysis(
        "vector_prefix_sum",
        return_type="int",
        parameters=[
            pointer_param,
            {"name": "param_2", "index": 1, "data_type": "int", "size": 4},
        ],
        returns=[
            ReturnInfo(
                address="0x1000",
                value=Expression.binary_op("INT_ADD", _mem("param_1", 0), _mem("param_1", 4)),
                conditions=[],
            ),
            ReturnInfo(
                address="0x1004",
                value=Expression.unknown("unproved_vector_body"),
                conditions=[],
            ),
        ],
    )
    summarizer = StructuralRecurrenceSummarizer(_FakeTracer("unused", _const(0)), debug=False)

    assert summarizer._vector_prefix_lanes_have_unit_terms_in_positive_return(
        analysis,
        pointer_param,
        [],
        vector_stride=8,
        element_size=4,
    ) is False


def test_vector_prefix_return_term_proof_rejects_extra_in_base_terms():
    pointer_param = {"name": "param_1", "index": 0, "data_type": "int *", "size": 8}
    analysis = create_mock_analysis(
        "vector_prefix_sum",
        return_type="int",
        parameters=[
            pointer_param,
            {"name": "param_2", "index": 1, "data_type": "int", "size": 4},
        ],
        returns=[
            ReturnInfo(
                address="0x1000",
                value=Expression.binary_op(
                    "INT_ADD",
                    Expression.binary_op("INT_ADD", _mem("param_1", 0), _mem("param_1", 4)),
                    _mem("param_1", 8),
                ),
                conditions=[],
            )
        ],
    )
    summarizer = StructuralRecurrenceSummarizer(_FakeTracer("unused", _const(0)), debug=False)

    assert summarizer._vector_prefix_lanes_have_unit_terms_in_positive_return(
        analysis,
        pointer_param,
        [],
        vector_stride=8,
        element_size=4,
    ) is False


def test_vector_prefix_return_term_proof_rejects_nonzero_constant_bias():
    pointer_param = {"name": "param_1", "index": 0, "data_type": "int *", "size": 8}
    analysis = create_mock_analysis(
        "vector_prefix_sum",
        return_type="int",
        parameters=[
            pointer_param,
            {"name": "param_2", "index": 1, "data_type": "int", "size": 4},
        ],
        returns=[
            ReturnInfo(
                address="0x1000",
                value=Expression.binary_op(
                    "INT_ADD",
                    Expression.binary_op("INT_ADD", _mem("param_1", 0), _mem("param_1", 4)),
                    Expression.constant(5, size=4),
                ),
                conditions=[],
            )
        ],
    )
    summarizer = StructuralRecurrenceSummarizer(_FakeTracer("unused", _const(0)), debug=False)

    assert summarizer._vector_prefix_lanes_have_unit_terms_in_positive_return(
        analysis,
        pointer_param,
        [],
        vector_stride=8,
        element_size=4,
    ) is False


def test_vector_prefix_lanes_reject_multiequal_selection_as_sum():
    vector_phi = _FakeVarnode("vector_phi", size=8, high=_FakeHighVar("vector_phi"))
    four_vn = _FakeVarnode("four", size=8, expr=Expression.constant(4, size=8))
    one_vn = _FakeVarnode("one", size=8, expr=Expression.constant(1, size=8))
    ram_space = _FakeVarnode("ram", size=8, expr=Expression.constant(0, size=8))
    lane0 = _FakeVarnode("lane0", size=4)
    lane1_addr = _FakeVarnode("lane1_addr", size=8)
    lane1 = _FakeVarnode("lane1", size=4)
    selected = _FakeVarnode("selected", size=4)
    ops = [
        _FakePcodeOp("LOAD", [ram_space, vector_phi], lane0),
        _FakePcodeOp("PTRADD", [vector_phi, one_vn, four_vn], lane1_addr),
        _FakePcodeOp("LOAD", [ram_space, lane1_addr], lane1),
        _FakePcodeOp("MULTIEQUAL", [lane0, lane1], selected),
        _FakePcodeOp("RETURN", [_FakeVarnode("return_target", size=8), selected], None),
    ]
    summarizer = StructuralRecurrenceSummarizer(_FakeTracer("unused", _const(0)), debug=False)

    assert not summarizer._vector_prefix_lanes_contribute_additively_to_return(
        ops,
        vector_phi,
        base_offset=0,
        vector_stride=8,
        element_size=4,
    )


def test_vector_prefix_lanes_reject_conditional_accumulator_updates():
    vector_phi = _FakeVarnode("vector_phi", size=8, high=_FakeHighVar("vector_phi"))
    four_vn = _FakeVarnode("four", size=8, expr=Expression.constant(4, size=8))
    one_vn = _FakeVarnode("one", size=8, expr=Expression.constant(1, size=8))
    zero_vn = _FakeVarnode("zero", size=4, expr=Expression.constant(0, size=4))
    ram_space = _FakeVarnode("ram", size=8, expr=Expression.constant(0, size=8))
    lane0 = _FakeVarnode("lane0", size=4)
    lane1_addr = _FakeVarnode("lane1_addr", size=8)
    lane1 = _FakeVarnode("lane1", size=4)
    acc_phi = _FakeVarnode("acc_phi", size=4)
    acc_lane0 = _FakeVarnode("acc_lane0", size=4)
    acc_lane1 = _FakeVarnode("acc_lane1", size=4)
    ops = [
        _FakePcodeOp("LOAD", [ram_space, vector_phi], lane0),
        _FakePcodeOp("PTRADD", [vector_phi, one_vn, four_vn], lane1_addr),
        _FakePcodeOp("LOAD", [ram_space, lane1_addr], lane1),
        _FakePcodeOp("INT_ADD", [acc_phi, lane0], acc_lane0),
        _FakePcodeOp("INT_ADD", [acc_phi, lane1], acc_lane1),
        _FakePcodeOp("MULTIEQUAL", [zero_vn, acc_lane0, acc_lane1], acc_phi),
        _FakePcodeOp("RETURN", [_FakeVarnode("return_target", size=8), acc_phi], None),
    ]
    summarizer = StructuralRecurrenceSummarizer(_FakeTracer("unused", _const(0)), debug=False)

    assert not summarizer._vector_prefix_lanes_contribute_additively_to_return(
        ops,
        vector_phi,
        base_offset=0,
        vector_stride=8,
        element_size=4,
    )


def test_vector_prefix_lanes_reject_single_conditional_accumulator_update():
    vector_phi = _FakeVarnode("vector_phi", size=8, high=_FakeHighVar("vector_phi"))
    four_vn = _FakeVarnode("four", size=8, expr=Expression.constant(4, size=8))
    ram_space = _FakeVarnode("ram", size=8, expr=Expression.constant(0, size=8))
    lane0 = _FakeVarnode("lane0", size=4)
    acc_phi = _FakeVarnode("acc_phi", size=4)
    acc_lane0 = _FakeVarnode("acc_lane0", size=4)
    ops = [
        _FakePcodeOp("LOAD", [ram_space, vector_phi], lane0),
        _FakePcodeOp("INT_ADD", [acc_phi, lane0], acc_lane0),
        _FakePcodeOp("MULTIEQUAL", [acc_phi, acc_lane0], acc_phi),
        _FakePcodeOp("RETURN", [_FakeVarnode("return_target", size=8), acc_phi], None),
    ]
    summarizer = StructuralRecurrenceSummarizer(_FakeTracer("unused", _const(0)), debug=False)

    assert not summarizer._vector_prefix_lanes_contribute_additively_to_return(
        ops,
        vector_phi,
        base_offset=0,
        vector_stride=4,
        element_size=4,
    )


def test_vector_prefix_lanes_reject_copied_pass_through_accumulator_update():
    vector_phi = _FakeVarnode("vector_phi", size=8, high=_FakeHighVar("vector_phi"))
    ram_space = _FakeVarnode("ram", size=8, expr=Expression.constant(0, size=8))
    lane0 = _FakeVarnode("lane0", size=4)
    acc_phi = _FakeVarnode("acc_phi", size=4)
    acc_copy = _FakeVarnode("acc_copy", size=4)
    acc_lane0 = _FakeVarnode("acc_lane0", size=4)
    ops = [
        _FakePcodeOp("LOAD", [ram_space, vector_phi], lane0),
        _FakePcodeOp("COPY", [acc_phi], acc_copy),
        _FakePcodeOp("INT_ADD", [acc_phi, lane0], acc_lane0),
        _FakePcodeOp("MULTIEQUAL", [acc_copy, acc_lane0], acc_phi),
        _FakePcodeOp("RETURN", [_FakeVarnode("return_target", size=8), acc_phi], None),
    ]
    summarizer = StructuralRecurrenceSummarizer(_FakeTracer("unused", _const(0)), debug=False)

    assert not summarizer._vector_prefix_lanes_contribute_additively_to_return(
        ops,
        vector_phi,
        base_offset=0,
        vector_stride=4,
        element_size=4,
    )


def test_vector_prefix_lanes_reject_same_high_pass_through_accumulator_update():
    vector_phi = _FakeVarnode("vector_phi", size=8, high=_FakeHighVar("vector_phi"))
    ram_space = _FakeVarnode("ram", size=8, expr=Expression.constant(0, size=8))
    lane0 = _FakeVarnode("lane0", size=4)
    acc_high = _FakeHighVar("accumulator")
    acc_phi = _FakeVarnode("acc_phi", size=4, high=acc_high)
    acc_pass = _FakeVarnode("acc_pass", size=4, high=acc_high)
    acc_lane0 = _FakeVarnode("acc_lane0", size=4)
    ops = [
        _FakePcodeOp("LOAD", [ram_space, vector_phi], lane0),
        _FakePcodeOp("INT_ADD", [acc_phi, lane0], acc_lane0),
        _FakePcodeOp("MULTIEQUAL", [acc_pass, acc_lane0], acc_phi),
        _FakePcodeOp("RETURN", [_FakeVarnode("return_target", size=8), acc_phi], None),
    ]
    summarizer = StructuralRecurrenceSummarizer(_FakeTracer("unused", _const(0)), debug=False)

    assert not summarizer._vector_prefix_lanes_contribute_additively_to_return(
        ops,
        vector_phi,
        base_offset=0,
        vector_stride=4,
        element_size=4,
    )


def test_vector_prefix_lanes_allow_same_high_cfg_entry_seed():
    vector_phi = _FakeVarnode("vector_phi", size=8, high=_FakeHighVar("vector_phi"))
    ram_space = _FakeVarnode("ram", size=8, expr=Expression.constant(0, size=8))
    lane0 = _FakeVarnode("lane0", size=4)
    acc_high = _FakeHighVar("accumulator")
    acc_seed = _FakeVarnode("acc_seed", size=4, expr=Expression.constant(0, size=4), high=acc_high)
    acc_phi = _FakeVarnode("acc_phi", size=4, high=acc_high)
    acc_lane0 = _FakeVarnode("acc_lane0", size=4)
    load_op = _FakePcodeOp("LOAD", [ram_space, vector_phi], lane0)
    add_op = _FakePcodeOp("INT_ADD", [acc_phi, lane0], acc_lane0)
    phi_op = _FakePcodeOp("MULTIEQUAL", [acc_seed, acc_lane0], acc_phi)
    return_op = _FakePcodeOp("RETURN", [_FakeVarnode("return_target", size=8), acc_phi], None)
    preheader = _FakeCfgBlock(0)
    header = _FakeCfgBlock(1, [phi_op, return_op])
    latch = _FakeCfgBlock(2, [load_op, add_op])
    preheader.add_edge(header)
    header.add_edge(latch)
    latch.add_edge(header)
    summarizer = StructuralRecurrenceSummarizer(_FakeTracer("unused", _const(0)), debug=False)

    assert summarizer._vector_prefix_lanes_contribute_additively_to_return(
        [load_op, add_op, phi_op, return_op],
        vector_phi,
        base_offset=0,
        vector_stride=4,
        element_size=4,
    )


def test_round_down_mask_requires_high_bits_preserved_for_counter_width():
    summarizer = StructuralRecurrenceSummarizer(_FakeTracer("unused", _const(0)), debug=False)

    assert summarizer._power_of_two_rounding_from_mask(0xFFFFFFF8, count_width_bits=32) == 8
    assert summarizer._power_of_two_rounding_from_mask(0xF8, count_width_bits=32) is None
    assert summarizer._power_of_two_rounding_from_mask(0xFFFFFFFFFFFFFFF8, count_width_bits=64) == 8


def test_round_down_candidate_uses_counter_semantic_width_through_zext():
    count_expr = Expression.parameter("param_2", index=1, data_type="int", size=4)
    count_vn = _FakeVarnode("param_2", size=4, expr=count_expr)
    zext_vn = _FakeVarnode("count_zext", size=8, expr=Expression.unary_op("INT_ZEXT", count_expr))
    zext_op = _FakePcodeOp("INT_ZEXT", [count_vn], zext_vn)
    mask_vn = _FakeVarnode("mask", size=8, expr=Expression.constant(0xFFFFFFF8, size=8))
    rounded_vn = _FakeVarnode("rounded", size=8)
    round_op = _FakePcodeOp("INT_AND", [zext_vn, mask_vn], rounded_vn)
    summarizer = StructuralRecurrenceSummarizer(_FakeTracer("unused", _const(0)), debug=False)

    assert summarizer._readonly_round_down_candidates(
        [zext_op, round_op],
        {"name": "param_2", "index": 1, "data_type": "int", "size": 4},
    ) == [(rounded_vn, 8)]


def test_readonly_vector_lane_summary_enters_scalar_iteration_space_only_with_witnesses():
    summarizer = StructuralRecurrenceSummarizer(_FakeTracer("unused", _const(0)), debug=False)
    count_expr = Expression.parameter("param_2", index=1, data_type="int", size=4)
    base_ref = LocationBaseRef.parameter("param_1", index=0)
    witnesses = tuple(
        ReadonlyReductionWitness(
            exact_count=count,
            terms=tuple(
                ReadonlyReductionTermRef(byte_offset=index * 4, access_size=4)
                for index in range(count)
            ),
        )
        for count in (1, 2, 3)
    )
    scalar_proof = _readonly_accumulator_proof(
            base_ref=base_ref,
            count_expr=count_expr,
            stride=4,
            element_size=4,
            index_scale=4,
            witnesses=witnesses,
    )
    scalar_summary = scalar_proof.with_runtime_evidence(
        limit_expr=count_expr,
        result_size=4,
        loop_body_witnesses=witnesses,
        exact_return_witnesses=(),
        guard_constraints=(),
        signed_counter=True,
    ).lower_to_loop_summary_ref()
    vector_proof = _readonly_accumulator_proof(
            base_ref=base_ref,
            count_expr=count_expr,
            stride=16,
            element_size=8,
            index_scale=16,
            lane_terms=((0, 4), (4, 4), (8, 4), (12, 4)),
            witnesses=witnesses,
    )
    vector_summary = vector_proof.with_runtime_evidence(
        limit_expr=count_expr,
        result_size=4,
        loop_body_witnesses=witnesses,
        exact_return_witnesses=(),
        guard_constraints=(),
        signed_counter=True,
    ).lower_to_loop_summary_ref()
    unproven_vector_proof = _readonly_accumulator_proof(
            base_ref=base_ref,
            count_expr=count_expr,
            stride=16,
            element_size=8,
            index_scale=16,
            lane_terms=((0, 4), (4, 4), (8, 4), (12, 4)),
    )
    unproven_vector_summary = unproven_vector_proof.with_runtime_evidence(
        limit_expr=count_expr,
        result_size=4,
        loop_body_witnesses=(),
        exact_return_witnesses=(),
        guard_constraints=(),
        signed_counter=True,
    ).lower_to_loop_summary_ref()

    assert scalar_summary is not None
    assert vector_summary is not None
    assert unproven_vector_summary is not None
    assert vector_summary.loop_var_unit == "scalar_element_index"
    assert loop_summary_method_b_key(vector_summary) == loop_summary_method_b_key(scalar_summary)
    assert unproven_vector_summary.loop_var_unit == "element_index"
    assert loop_summary_method_b_key(unproven_vector_summary) != loop_summary_method_b_key(scalar_summary)


def test_readonly_reduction_result_size_uses_positive_region_return():
    ptr_expr = Expression.parameter("param_1", index=0, data_type="long *", size=8)
    count_expr = Expression.parameter("param_2", index=1, data_type="int", size=4)
    positive = [
        _cond("INT_NOTEQUAL", ptr_expr, Expression.constant(0, size=8)),
        _cond("INT_SLESS", Expression.constant(0, size=4), count_expr),
    ]
    positive_value = Expression.unknown("wide_positive")
    positive_value.size = 8
    analysis = create_mock_analysis(
        "wide_sum",
        return_type="long",
        parameters=[
            {"name": "param_1", "index": 0, "data_type": "long *", "size": 8},
            {"name": "param_2", "index": 1, "data_type": "int", "size": 4},
        ],
        returns=[
            ReturnInfo(
                address="0x1000",
                value=Expression.constant(-1, size=4),
                conditions=[_cond("INT_EQUAL", ptr_expr, Expression.constant(0, size=8))],
            ),
            ReturnInfo(
                address="0x1004",
                value=positive_value,
                conditions=positive,
            ),
        ],
    )
    summarizer = StructuralRecurrenceSummarizer(_FakeTracer("unused", _const(0)), debug=False)

    assert summarizer._readonly_reduction_result_size(analysis, positive_conditions=positive) == 8


def test_readonly_reduction_summary_passes_positive_region_to_accumulator_proof(monkeypatch):
    ptr_expr = Expression.parameter("param_1", index=0, data_type="long *", size=8)
    count_expr = Expression.parameter("param_2", index=1, data_type="int", size=4)
    pointer_param = {"name": "param_1", "index": 0, "data_type": "long *", "size": 8}
    count_param = {"name": "param_2", "index": 1, "data_type": "int", "size": 4}
    positive_value = Expression.unknown("wide_positive")
    positive_value.size = 8
    analysis = create_mock_analysis(
        "wide_sum",
        return_type="long",
        parameters=[pointer_param, count_param],
        returns=[
            ReturnInfo(
                address="0x1000",
                value=Expression.constant(-1, size=4),
                conditions=[_cond("INT_EQUAL", ptr_expr, Expression.constant(0, size=8))],
            ),
            ReturnInfo(
                address="0x1004",
                value=positive_value,
                conditions=[
                    _cond("INT_NOTEQUAL", ptr_expr, Expression.constant(0, size=8)),
                    _cond("INT_SLESS", Expression.constant(0, size=4), count_expr),
                ],
            ),
        ],
    )
    captured = {}
    summarizer = StructuralRecurrenceSummarizer(_FakeTracer("unused", _const(0)), debug=False)
    monkeypatch.setattr(
        summarizer,
        "_infer_readonly_pointer_reduction_parameters",
        lambda _analysis, _high_function: (pointer_param, count_param),
    )

    def capture_accumulator_proof(_high_function, _analysis, _pointer_param, _count_param, *, positive_conditions=()):
        captured["positive_conditions"] = tuple(positive_conditions)
        return None

    monkeypatch.setattr(summarizer, "_detect_readonly_sum_accumulator_proof", capture_accumulator_proof)

    assert summarizer._try_summarize_readonly_pointer_reduction(
        _FakeFunction("wide_sum"),
        _FakeHighFunction([]),
        analysis,
    ) is None
    assert captured["positive_conditions"]
    assert summarizer._readonly_reduction_result_size(
        analysis,
        positive_conditions=captured["positive_conditions"],
    ) == 8


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


def test_structural_recurrence_summarizer_declines_readonly_reduction_from_prefix_returns_only():
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

    assert summary is None


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


def test_readonly_semantic_witnesses_use_exact_returns_as_provisional_lane_evidence(monkeypatch):
    pointer_param = {"name": "param_1", "index": 0, "data_type": "int *", "size": 8}
    count_param = {"name": "param_2", "index": 1, "data_type": "int", "size": 4, "is_signed": True}
    count_expr = Expression.parameter("param_2", index=1, data_type="int", size=4)
    proof = ReductionAccumulatorProof(
        reduction_kind="memory_sum",
        pointer_base_ref=LocationBaseRef.parameter("param_1", index=0),
        count_parameter_name="param_2",
        count_parameter_index=1,
        limit_expr=count_expr,
        result_size=4,
        stride=8,
        element_size=8,
        start_offset=4,
        start_index=0,
        index_step=1,
        index_scale=8,
        lane_terms=((0, 4), (4, 4)),
    )
    exact_witnesses = (
        ReadonlyReductionWitness(
            exact_count=1,
            terms=(ReadonlyReductionTermRef(byte_offset=4, access_size=4),),
        ),
        ReadonlyReductionWitness(
            exact_count=2,
            terms=(
                ReadonlyReductionTermRef(byte_offset=4, access_size=4),
                ReadonlyReductionTermRef(byte_offset=8, access_size=4),
            ),
        ),
    )
    analysis = create_mock_analysis(
        "shifted_lane_sum",
        return_type="int",
        parameters=[pointer_param, count_param],
        returns=[],
    )
    summarizer = StructuralRecurrenceSummarizer(_FakeTracer("unused", _const(0)), debug=False)
    monkeypatch.setattr(
        summarizer,
        "_extract_readonly_reduction_exact_witnesses",
        lambda *_args, **_kwargs: exact_witnesses,
    )

    witnesses = summarizer._build_readonly_reduction_semantic_witnesses(
        analysis,
        pointer_param,
        count_param,
        [],
        proof,
        result_size=4,
    )

    assert witnesses == exact_witnesses


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
