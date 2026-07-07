# -*- coding: utf-8 -*-

from unittest.mock import Mock

from scripts.function_tracer_pcode.analysis import ReturnAnalyzer
from scripts.function_tracer_pcode.equivalence.strategies.pairwise import PairwiseStrategy
from scripts.function_tracer_pcode.model import (
    CallTargetRef,
    Condition,
    DeferredCallInfo,
    DivergenceOutcome,
    Expression,
    ExpressionType,
    FunctionReturnAnalysis,
    ReturnInfo,
    ReturnOutcome,
    UnknownOutcome,
)
from scripts.function_tracer_pcode.smt.parallel import ParallelResult
from scripts.function_tracer_pcode.smt.solvers.z3 import Z3Solver


def _param() -> Expression:
    return Expression.parameter("param_1", index=0, data_type="int", size=4)


def _param2() -> Expression:
    return Expression.parameter("param_2", index=1, data_type="int", size=4)


def _const(value: int) -> Expression:
    return Expression.constant(value, 4)


def _positive() -> Condition:
    return Condition(Expression.binary_op("INT_SLESS", _const(0), _param()), False)


def _nonpositive() -> Condition:
    return _positive().negate()


def _positive2() -> Condition:
    return Condition(Expression.binary_op("INT_SLESS", _const(0), _param2()), False)


def _nonpositive2() -> Condition:
    return _positive2().negate()


def _gt_one() -> Condition:
    return Condition(Expression.binary_op("INT_SLESS", _const(1), _param()), False)


def _le_one() -> Condition:
    return _gt_one().negate()


def _analysis(
    *,
    return_guards,
    divergence_guards,
    return_values=None,
    unknown_guards=(),
) -> FunctionReturnAnalysis:
    returns = [
        ReturnInfo(
            address=f"0x{index:x}",
            value=(return_values[index] if return_values is not None else _const(0)),
            conditions=list(guard),
            branch_index=index,
        )
        for index, guard in enumerate(return_guards)
    ]
    analysis = FunctionReturnAnalysis(
        function_name="f",
        entry_point="0x1000",
        parameters=[{"name": "param_1", "index": 0, "size": 4, "data_type": "int", "is_signed": True}],
        returns=returns,
        return_type="int",
    )
    analysis.return_outcomes = tuple(
        ReturnOutcome(guard=tuple(ret.conditions), value=ret.value, return_info=ret)
        for ret in returns
    )
    analysis.divergence_outcomes = tuple(
        DivergenceOutcome(guard=tuple(guard), proof={"proof_kind": "must_diverge"})
        for guard in divergence_guards
    )
    analysis.unknown_outcomes = tuple(
        UnknownOutcome(guard=tuple(guard), reason="test_unknown")
        for guard in unknown_guards
    )
    return analysis


class _FakeOp:
    def __init__(self, mnemonic: str, *, condition_expr=None, writes_guard_state=False, inputs=(), output=None):
        self._mnemonic = mnemonic
        self.condition_expr = condition_expr
        self.writes_guard_state = writes_guard_state
        self._inputs = tuple(inputs or ())
        self._output = output

    def getMnemonic(self):
        return self._mnemonic

    def getNumInputs(self):
        return len(self._inputs)

    def getInput(self, index):
        return self._inputs[index]

    def getOutput(self):
        return self._output


class _FakeAddressSpace:
    def __init__(self, name):
        self._name = name

    def getName(self):
        return self._name


class _FakeAddress:
    def __init__(self, space, offset):
        self._space = _FakeAddressSpace(space)
        self._offset = offset

    def getAddressSpace(self):
        return self._space

    def getOffset(self):
        return self._offset


class _FakeVarnode:
    def __init__(self, space, offset, size, *, is_constant=False, def_op=None):
        self._address = _FakeAddress(space, offset)
        self._size = size
        self._is_constant = is_constant
        self._def_op = def_op

    def isConstant(self):
        return self._is_constant

    def getAddress(self):
        return self._address

    def getSize(self):
        return self._size

    def getDef(self):
        return self._def_op


class _FakeIterator:
    def __init__(self, values):
        self._values = list(values)
        self._index = 0

    def hasNext(self):
        return self._index < len(self._values)

    def next(self):
        value = self._values[self._index]
        self._index += 1
        return value


class _FakeBlock:
    def __init__(self, ops, *, index=None, start=None):
        self._ops = list(ops)
        self._outs = []
        self._ins = []
        self._edge_conditions = {}
        self._true_out = None
        self._false_out = None
        self._index = index
        self._start = _FakeAddress("ram", int(start if start is not None else 0x3000 + int(index or 0) * 0x10))

    def add_out(self, block, *, condition=None, is_true=None):
        self._outs.append(block)
        block._ins.append(self)
        if condition is not None:
            self._edge_conditions[block] = condition
        if is_true is True:
            self._true_out = block
        elif is_true is False:
            self._false_out = block

    def getIterator(self):
        return _FakeIterator(self._ops)

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

    def getIndex(self):
        return self._index

    def getStart(self):
        return self._start


class _FakeHighFunction:
    def __init__(self, blocks):
        self._blocks = list(blocks)

    def getBasicBlocks(self):
        return list(self._blocks)


def _cyclic_high_function(*mnemonics):
    first = _FakeBlock([_FakeOp(mnemonic) for mnemonic in mnemonics], index=0)
    second = _FakeBlock([], index=1)
    first.add_out(second)
    second.add_out(first)
    return _FakeHighFunction([first, second])


def _guard_cbranch_ops(condition: Condition | None = None, *, writes_guard_state=False):
    zero = _FakeVarnode("const", 0, 4, is_constant=True)
    state = _FakeVarnode("unique", 0x100, 4)
    compare_out = _FakeVarnode("unique", 0x200, 1)
    compare = _FakeOp("INT_SLESS", inputs=(zero, state), output=compare_out)
    compare_out._def_op = compare
    cbranch = _FakeOp(
        "CBRANCH",
        condition_expr=(condition.expression if condition is not None else None),
        writes_guard_state=writes_guard_state,
        inputs=(_FakeVarnode("const", 0x3000, 8, is_constant=True), compare_out),
    )
    return [compare, cbranch]


def _condition_cbranch_op(
    condition: Condition,
    state: _FakeVarnode,
    *,
    target_offset: int = 0x3000,
    target_space: str = "const",
    target_is_constant: bool = True,
    condition_def_mnemonic: str = "INT_SLESS",
    root_condition_without_def: bool = False,
):
    if root_condition_without_def:
        cbranch = _FakeOp(
            "CBRANCH",
            condition_expr=condition.expression,
            inputs=(_FakeVarnode(target_space, target_offset, 8, is_constant=target_is_constant), state),
        )
        return None, cbranch
    zero = _FakeVarnode("const", 0, 4, is_constant=True)
    compare_out = _FakeVarnode("unique", target_offset + 0x1000, 1)
    compare = _FakeOp(condition_def_mnemonic, inputs=(zero, state), output=compare_out)
    compare_out._def_op = compare
    cbranch = _FakeOp(
        "CBRANCH",
        condition_expr=condition.expression,
        inputs=(_FakeVarnode(target_space, target_offset, 8, is_constant=target_is_constant), compare_out),
    )
    return compare, cbranch


def _proved_nonprogress_high_function(*, exit_condition=None, writes_guard_state=False):
    entry = _FakeBlock([], index=0)
    loop = _FakeBlock(
        _guard_cbranch_ops(_positive(), writes_guard_state=writes_guard_state),
        index=1,
    )
    ret = _FakeBlock([_FakeOp("RETURN")], index=2)
    entry.add_out(loop)
    loop.add_out(loop, condition=_positive(), is_true=True)
    if exit_condition is None:
        exit_condition = _nonpositive()
    loop.add_out(ret, condition=exit_condition, is_true=False)
    return _FakeHighFunction([entry, loop, ret])


def _guarded_closed_self_loop_high_function():
    entry = _FakeBlock([_FakeOp("CBRANCH", condition_expr=_positive().expression)], index=0)
    ret = _FakeBlock([_FakeOp("RETURN")], index=1)
    loop = _FakeBlock([], index=2)
    entry.add_out(loop, condition=_positive(), is_true=True)
    entry.add_out(ret, condition=_nonpositive(), is_true=False)
    loop.add_out(loop)
    return _FakeHighFunction([entry, ret, loop])


def _branch_guarded_while_proved_high_function(
    *,
    redefine_cycle_guard_dependency=False,
    redefine_precycle_guard_dependency=False,
    condition_def_mnemonic: str = "INT_SLESS",
    root_condition_without_def: bool = False,
):
    t_state = _FakeVarnode("register", 0x4000, 4)
    c_state = _FakeVarnode("register", 0x4004, 4)
    c_compare, c_cbranch = _condition_cbranch_op(
        _positive2(),
        c_state,
        target_offset=0x3020,
        condition_def_mnemonic=condition_def_mnemonic,
        root_condition_without_def=root_condition_without_def,
    )
    t_compare, t_cbranch = _condition_cbranch_op(
        _positive(),
        t_state,
        target_offset=0x3030,
        condition_def_mnemonic=condition_def_mnemonic,
        root_condition_without_def=root_condition_without_def,
    )
    entry_ops = []
    if redefine_precycle_guard_dependency:
        entry_ops.append(_FakeOp("COPY", inputs=(_const(0),), output=t_state))
    entry = _FakeBlock(entry_ops, index=0)
    header = _FakeBlock([op for op in (c_compare, c_cbranch) if op is not None], index=1)
    branch_ops = [op for op in (t_compare, t_cbranch) if op is not None]
    if redefine_cycle_guard_dependency:
        branch_ops.append(_FakeOp("COPY", inputs=(_const(0),), output=t_state))
    branch = _FakeBlock(branch_ops, index=2)
    body = _FakeBlock([_FakeOp("COPY", writes_guard_state=True)], index=3)
    ret = _FakeBlock([_FakeOp("RETURN")], index=4)
    entry.add_out(header)
    header.add_out(branch, condition=_positive2(), is_true=True)
    header.add_out(ret, condition=_nonpositive2(), is_true=False)
    branch.add_out(body, condition=_positive(), is_true=True)
    branch.add_out(header, condition=_nonpositive(), is_true=False)
    body.add_out(header)
    return _FakeHighFunction([entry, header, branch, body, ret])


def _branch_guarded_while_direct_target_high_function(*, target_space: str = "const", target_is_constant: bool = True):
    t_state = _FakeVarnode("register", 0x4000, 4)
    c_state = _FakeVarnode("register", 0x4004, 4)
    c_compare, c_cbranch = _condition_cbranch_op(
        _positive2(),
        c_state,
        target_offset=0x3020,
        target_space=target_space,
        target_is_constant=target_is_constant,
    )
    t_compare, t_cbranch = _condition_cbranch_op(
        _positive(),
        t_state,
        target_offset=0x3030,
        target_space=target_space,
        target_is_constant=target_is_constant,
    )
    entry = _FakeBlock([], index=0, start=0x3000)
    header = _FakeBlock(
        [c_compare, c_cbranch],
        index=1,
        start=0x3010,
    )
    branch = _FakeBlock(
        [t_compare, t_cbranch],
        index=2,
        start=0x3020,
    )
    body = _FakeBlock([_FakeOp("COPY", writes_guard_state=True)], index=3, start=0x3030)
    ret = _FakeBlock([_FakeOp("RETURN")], index=4, start=0x3040)
    entry.add_out(header)
    header.add_out(branch)
    header.add_out(ret)
    branch.add_out(body)
    branch.add_out(header)
    body.add_out(header)
    return _FakeHighFunction([entry, header, branch, body, ret])


def _unreachable_guarded_self_loop_high_function():
    entry = _FakeBlock([], index=0)
    ret = _FakeBlock([_FakeOp("RETURN")], index=1)
    loop = _FakeBlock([_FakeOp("CBRANCH", condition_expr=_positive().expression)], index=2)
    entry.add_out(ret)
    loop.add_out(loop, condition=_positive(), is_true=True)
    return _FakeHighFunction([entry, ret, loop])


def _ambiguous_edge_polarity_high_function():
    entry = _FakeBlock([], index=0)
    loop = _FakeBlock([_FakeOp("CBRANCH", condition_expr=_positive().expression)], index=1)
    ret = _FakeBlock([_FakeOp("RETURN")], index=2)
    entry.add_out(loop)
    loop.add_out(loop)
    loop.add_out(ret)
    return _FakeHighFunction([entry, loop, ret])


def _guard_dependency_block(*, redefine_guard_varnode=False, redefine_parameter_varnode=False):
    zero = _FakeVarnode("const", 0, 4, is_constant=True)
    state = _FakeVarnode("unique", 0x100, 4)
    param = _FakeVarnode("register", 0x4000, 4)
    compare_out = _FakeVarnode("unique", 0x200, 1)
    compare = _FakeOp("INT_SLESS", inputs=(zero, state), output=compare_out)
    compare_out._def_op = compare
    cbranch = _FakeOp("CBRANCH", inputs=(_FakeVarnode("const", 0x3000, 8, is_constant=True), compare_out))
    ops = [compare, cbranch]
    if redefine_guard_varnode:
        ops.append(_FakeOp("COPY", inputs=(state,), output=state))
    if redefine_parameter_varnode:
        param_compare_out = _FakeVarnode("unique", 0x220, 1)
        param_compare = _FakeOp("INT_SLESS", inputs=(zero, param), output=param_compare_out)
        param_compare_out._def_op = param_compare
        cbranch = _FakeOp("CBRANCH", inputs=(_FakeVarnode("const", 0x3000, 8, is_constant=True), param_compare_out))
        ops = [param_compare, cbranch, _FakeOp("COPY", inputs=(param,), output=param)]
    return _FakeBlock(ops, index=10)


def _base_analysis(function_name: str, params, returns):
    return FunctionReturnAnalysis(
        function_name=function_name,
        entry_point="0x1000",
        parameters=params,
        returns=returns,
        return_type="int",
    )


def _branch_guarded_while_analysis():
    phi = Expression(ExpressionType.UNKNOWN, value="phi_circular", size=4)
    t_param = _param()
    c_param = _param2()
    t_positive = Condition(Expression.binary_op("INT_SLESS", _const(0), t_param), False)
    t_nonpositive = t_positive.negate()
    c_positive = Condition(Expression.binary_op("INT_SLESS", _const(0), c_param), False)
    c_nonpositive = c_positive.negate()
    recursive_value = Expression.binary_op("INT_ADD", phi, _const(1))
    recursive_value.size = 4
    return _base_analysis(
        "f",
        [
            {"name": "param_1", "index": 0, "size": 4, "data_type": "int", "is_signed": True},
            {"name": "param_2", "index": 1, "size": 4, "data_type": "int", "is_signed": True},
        ],
        [
            ReturnInfo(address="0x1000", value=phi, conditions=[c_positive, t_nonpositive]),
            ReturnInfo(address="0x1004", value=_const(0), conditions=[c_nonpositive]),
            ReturnInfo(address="0x1008", value=c_param, conditions=[c_positive, t_positive]),
            ReturnInfo(address="0x1008", value=recursive_value, conditions=[c_positive, t_positive]),
        ],
    )


class _Z3Runner:
    def __init__(self):
        self._solver = Z3Solver(timeout=2)

    def run_sequential(self, query: str):
        return ParallelResult([self._solver.check_equivalence_direct(query)])


def _strategy() -> PairwiseStrategy:
    return PairwiseStrategy(Mock(), _Z3Runner(), debug=False)


def _base_ctx():
    return {
        "header_lines": [
            "(declare-fun p1 () (_ BitVec 32))",
            "(declare-fun p2 () (_ BitVec 32))",
            "(assert (= p1 p2))",
        ],
    }


def _replace_param(symbol: str):
    def _replace(obj):
        if isinstance(obj, Condition):
            smt = obj.to_smt(float_mode="fp")
        elif isinstance(obj, Expression):
            smt = obj.to_smt(float_mode="fp")
        else:
            smt = str(obj)
        return smt.replace("param_1", symbol)

    return _replace


def _replace_params(mapping):
    def _replace(obj):
        if isinstance(obj, Condition):
            smt = obj.to_smt(float_mode="fp")
        elif isinstance(obj, Expression):
            smt = obj.to_smt(float_mode="fp")
        else:
            smt = str(obj)
        for source, target in mapping.items():
            smt = smt.replace(source, target)
        return smt

    return _replace


def test_outcome_smt_zero_width_normalization_rewrites_left_zero_operand():
    assert _strategy()._normalize_zero_constant_widths_for_declared_symbols(
        ["(bvslt (_ bv0 64) p1)"],
        ["(declare-fun p1 () (_ BitVec 32))"],
    ) == ["(bvslt (_ bv0 32) p1)"]


def test_outcome_smt_zero_width_normalization_rewrites_right_zero_operand():
    assert _strategy()._normalize_zero_constant_widths_for_declared_symbols(
        ["(bvslt p1 (_ bv0 64))"],
        ["(declare-fun p1 () (_ BitVec 32))"],
    ) == ["(bvslt p1 (_ bv0 32))"]


def test_outcome_smt_zero_width_normalization_does_not_rewrite_nonzero_constant():
    assert _strategy()._normalize_zero_constant_widths_for_declared_symbols(
        ["(bvslt (_ bv1 64) p1)", "(= p1 (_ bv2 64))"],
        ["(declare-fun p1 () (_ BitVec 32))"],
    ) == ["(bvslt (_ bv1 64) p1)", "(= p1 (_ bv2 64))"]


def test_outcome_smt_zero_width_normalization_does_not_rewrite_undeclared_symbol():
    assert _strategy()._normalize_zero_constant_widths_for_declared_symbols(
        ["(bvslt (_ bv0 64) p2)", "(= p2 (_ bv0 64))"],
        ["(declare-fun p1 () (_ BitVec 32))"],
    ) == ["(bvslt (_ bv0 64) p2)", "(= p2 (_ bv0 64))"]


def test_outcome_partition_equivalence_accepts_matching_divergence_guard():
    strategy = _strategy()
    left = _analysis(return_guards=[[_nonpositive()]], divergence_guards=[[_positive()]])
    right = _analysis(return_guards=[[_nonpositive()]], divergence_guards=[[_positive()]])

    assert strategy._outcome_partition_covered_labels(
        _base_ctx(),
        left,
        right,
        _replace_param("p1"),
        _replace_param("p2"),
    ) == {"function1", "function2"}


def test_outcome_partition_equivalence_requires_side_specific_base_context():
    strategy = _strategy()
    left = _analysis(return_guards=[[_nonpositive()]], divergence_guards=[[_positive()]])
    right = _analysis(return_guards=[[_nonpositive()]], divergence_guards=[[_positive()]])

    assert strategy._outcome_partition_covered_labels({}, left, right, None, None) == set()


def test_outcome_partition_equivalence_rejects_divergence_guard_mismatch():
    strategy = _strategy()
    left = _analysis(return_guards=[[_nonpositive()]], divergence_guards=[[_positive()]])
    right = _analysis(return_guards=[[_le_one()]], divergence_guards=[[_gt_one()]])

    assert strategy._outcome_partition_covered_labels(
        _base_ctx(),
        left,
        right,
        _replace_param("p1"),
        _replace_param("p2"),
    ) == set()


def test_outcome_partition_equivalence_rejects_unrelated_parameter_divergence_guard():
    strategy = _strategy()
    left = _analysis(return_guards=[[_nonpositive()]], divergence_guards=[[_positive()]])
    right = _analysis(return_guards=[[_nonpositive2()]], divergence_guards=[[_positive2()]])
    base_ctx = {
        "header_lines": [
            "(declare-fun p1 () (_ BitVec 32))",
            "(declare-fun p2 () (_ BitVec 32))",
        ],
    }

    assert strategy._outcome_partition_covered_labels(
        base_ctx,
        left,
        right,
        _replace_params({"param_1": "p1"}),
        _replace_params({"param_2": "p2"}),
    ) == set()


def test_outcome_partition_equivalence_rejects_return_diverge_overlap():
    strategy = _strategy()
    left = _analysis(return_guards=[[_nonpositive()]], divergence_guards=[[_positive()]])
    right = _analysis(return_guards=[[]], divergence_guards=[[_positive()]])

    assert strategy._outcome_partition_covered_labels(
        _base_ctx(),
        left,
        right,
        _replace_param("p1"),
        _replace_param("p2"),
    ) == set()


def test_outcome_partition_equivalence_rejects_return_value_mismatch():
    strategy = _strategy()
    left = _analysis(
        return_guards=[[_nonpositive()]],
        divergence_guards=[[_positive()]],
        return_values=[_const(0)],
    )
    right = _analysis(
        return_guards=[[_nonpositive()]],
        divergence_guards=[[_positive()]],
        return_values=[_const(1)],
    )

    assert strategy._outcome_partition_covered_labels(
        _base_ctx(),
        left,
        right,
        _replace_param("p1"),
        _replace_param("p2"),
    ) == set()


def test_unknown_outcome_partition_is_unknown_not_covered():
    strategy = _strategy()
    left = _analysis(
        return_guards=[[_nonpositive()]],
        divergence_guards=[],
        unknown_guards=[[_positive()]],
    )
    right = _analysis(
        return_guards=[[_nonpositive()]],
        divergence_guards=[],
        unknown_guards=[[_positive()]],
    )

    assert strategy._outcome_partition_covered_labels(
        _base_ctx(),
        left,
        right,
        _replace_param("p1"),
        _replace_param("p2"),
    ) == set()
    assert strategy._outcome_partition_inconclusive_labels(
        _base_ctx(),
        left,
        right,
        _replace_param("p1"),
        _replace_param("p2"),
    ) == {"function1", "function2"}


def test_outcome_partition_unknown_reason_maps_to_specific_reason_and_evidence():
    strategy = _strategy()
    left = _analysis(
        return_guards=[[_nonpositive()]],
        divergence_guards=[],
        unknown_guards=[[_positive()]],
    )
    right = _analysis(
        return_guards=[[_nonpositive()]],
        divergence_guards=[],
        unknown_guards=[[_positive()]],
    )

    record = strategy._make_blocking_unsafety_unknown_reason(
        "function1:outcome_partition_unknown",
        left,
        right,
        stage="unit",
    )

    assert record.reason_id == "outcome_partition_unknown"
    assert record.object_evidence["unknown_outcomes"][0] == "unknown_outcomes"
    assert record.object_evidence["unknown_outcomes"][1][0][0] == "unknown_outcome"


def test_unknown_outcomes_skip_monolithic_fallback():
    analysis = _analysis(
        return_guards=[[_nonpositive()]],
        divergence_guards=[],
        unknown_guards=[[_positive()]],
    )

    assert analysis.should_skip_monolithic_fallback() is True


def test_unknown_outcomes_without_partition_do_not_skip_monolithic_fallback():
    analysis = FunctionReturnAnalysis(
        function_name="f",
        entry_point="0x1000",
        parameters=[{"name": "param_1", "index": 0, "size": 4, "data_type": "int", "is_signed": True}],
        returns=[],
        return_type="int",
    )
    analysis.unknown_outcomes = (
        UnknownOutcome(guard=(_positive(),), reason="test_unknown"),
    )

    assert analysis.should_skip_monolithic_fallback() is False


def test_analyzer_keeps_single_guard_nonprogress_loop_unknown_without_must_diverge_proof():
    ret = ReturnInfo(address="0x1000", value=_const(0), conditions=[_nonpositive()])
    analysis = _base_analysis(
        "tr",
        [{"name": "param_1", "index": 0, "size": 4, "data_type": "int", "is_signed": True}],
        [ret],
    )

    ReturnAnalyzer(None)._apply_outcome_partition_summaries(
        None,
        _cyclic_high_function("CBRANCH"),
        analysis,
    )

    assert analysis.divergence_outcomes == ()
    assert len(analysis.unknown_outcomes) == 1
    assert analysis.unknown_outcomes[0].reason == "must_diverge_proof_missing"
    assert analysis.return_outcomes[0].value.value == 0


def test_analyzer_promotes_single_guard_nonprogress_loop_to_divergence_when_scc_exit_is_infeasible():
    ret = ReturnInfo(address="0x1000", value=_const(0), conditions=[_nonpositive()])
    analysis = _base_analysis(
        "tr",
        [{"name": "param_1", "index": 0, "size": 4, "data_type": "int", "is_signed": True}],
        [ret],
    )

    ReturnAnalyzer(None)._apply_outcome_partition_summaries(
        None,
        _proved_nonprogress_high_function(),
        analysis,
    )

    assert analysis.unknown_outcomes == ()
    assert len(analysis.divergence_outcomes) == 1
    assert analysis.divergence_outcomes[0].guard == (_positive(),)
    assert analysis.divergence_outcomes[0].proof["proof_kind"] == "single_guard_nonprogress_must_diverge"
    assert analysis.return_outcomes[0].value.value == 0


def test_analyzer_promotes_guarded_closed_self_loop_to_divergence():
    ret = ReturnInfo(address="0x1000", value=_const(0), conditions=[_nonpositive()])
    analysis = _base_analysis(
        "tr",
        [{"name": "param_1", "index": 0, "size": 4, "data_type": "int", "is_signed": True}],
        [ret],
    )

    ReturnAnalyzer(None)._apply_outcome_partition_summaries(
        None,
        _guarded_closed_self_loop_high_function(),
        analysis,
    )

    assert analysis.unknown_outcomes == ()
    assert len(analysis.divergence_outcomes) == 1
    assert analysis.divergence_outcomes[0].guard == (_positive(),)


def test_analyzer_keeps_single_guard_loop_unknown_when_exit_is_feasible():
    ret = ReturnInfo(address="0x1000", value=_const(0), conditions=[_nonpositive()])
    analysis = _base_analysis(
        "tr",
        [{"name": "param_1", "index": 0, "size": 4, "data_type": "int", "is_signed": True}],
        [ret],
    )

    ReturnAnalyzer(None)._apply_outcome_partition_summaries(
        None,
        _proved_nonprogress_high_function(exit_condition=_positive()),
        analysis,
    )

    assert analysis.divergence_outcomes == ()
    assert len(analysis.unknown_outcomes) == 1
    assert analysis.unknown_outcomes[0].reason == "must_diverge_proof_missing"


def test_analyzer_keeps_single_guard_loop_unknown_when_guard_state_is_written():
    ret = ReturnInfo(address="0x1000", value=_const(0), conditions=[_nonpositive()])
    analysis = _base_analysis(
        "tr",
        [{"name": "param_1", "index": 0, "size": 4, "data_type": "int", "is_signed": True}],
        [ret],
    )

    ReturnAnalyzer(None)._apply_outcome_partition_summaries(
        None,
        _proved_nonprogress_high_function(writes_guard_state=True),
        analysis,
    )

    assert analysis.divergence_outcomes == ()
    assert len(analysis.unknown_outcomes) == 1
    assert analysis.unknown_outcomes[0].reason == "must_diverge_proof_missing"


def test_analyzer_keeps_single_guard_loop_unknown_for_unreachable_scc():
    ret = ReturnInfo(address="0x1000", value=_const(0), conditions=[_nonpositive()])
    analysis = _base_analysis(
        "tr",
        [{"name": "param_1", "index": 0, "size": 4, "data_type": "int", "is_signed": True}],
        [ret],
    )

    ReturnAnalyzer(None)._apply_outcome_partition_summaries(
        None,
        _unreachable_guarded_self_loop_high_function(),
        analysis,
    )

    assert analysis.divergence_outcomes == ()
    assert len(analysis.unknown_outcomes) == 1
    assert analysis.unknown_outcomes[0].reason == "must_diverge_proof_missing"


def test_analyzer_keeps_single_guard_loop_unknown_when_edge_polarity_is_ambiguous():
    ret = ReturnInfo(address="0x1000", value=_const(0), conditions=[_nonpositive()])
    analysis = _base_analysis(
        "tr",
        [{"name": "param_1", "index": 0, "size": 4, "data_type": "int", "is_signed": True}],
        [ret],
    )

    ReturnAnalyzer(None)._apply_outcome_partition_summaries(
        None,
        _ambiguous_edge_polarity_high_function(),
        analysis,
    )

    assert analysis.divergence_outcomes == ()
    assert len(analysis.unknown_outcomes) == 1
    assert analysis.unknown_outcomes[0].reason == "must_diverge_proof_missing"


def test_analyzer_guard_dependency_preservation_rejects_guard_state_redefinition():
    analyzer = ReturnAnalyzer(None)
    block = _guard_dependency_block(redefine_guard_varnode=True)

    assert analyzer._scc_preserves_guard_dependencies({block}) is False


def test_analyzer_guard_dependency_preservation_rejects_parameter_redefinition():
    analyzer = ReturnAnalyzer(None)
    block = _guard_dependency_block(redefine_parameter_varnode=True)

    assert analyzer._scc_preserves_guard_dependencies({block}) is False


def test_analyzer_guard_dependency_preservation_accepts_read_only_guard_inputs():
    analyzer = ReturnAnalyzer(None)
    block = _guard_dependency_block()

    assert analyzer._scc_preserves_guard_dependencies({block}) is True


def test_analyzer_does_not_create_triangular_caller_outcome_without_callee_contract():
    param = _param()
    call_arg = Expression.binary_op("INT_ADD", param, Expression.constant(0xFFFFFFFF, 4))
    deferred = DeferredCallInfo(
        target_ref=CallTargetRef.from_name("tr"),
        arguments=[call_arg],
        call_argument_recovery_status="complete",
    )
    analysis = _base_analysis(
        "f",
        [{"name": "param_1", "index": 0, "size": 4, "data_type": "int", "is_signed": True}],
        [ReturnInfo(address="0x1000", value=Expression.unknown("tr@0x1000"), conditions=[])],
    )
    analysis.deferred_calls = {deferred.deferred_call_ref.stable_key(): deferred}

    ReturnAnalyzer(None)._apply_outcome_partition_summaries(
        None,
        _cyclic_high_function("CALL", "CBRANCH"),
        analysis,
    )

    assert analysis.return_outcomes == ()
    assert analysis.divergence_outcomes == ()
    assert analysis.unknown_outcomes == ()


def test_analyzer_does_not_use_callee_contract_without_caller_return_proof():
    analyzer = ReturnAnalyzer(None)
    target_ref = CallTargetRef.from_name("callee_with_contract")
    callee_ret = ReturnInfo(address="0x2000", value=_const(0), conditions=[_nonpositive()])
    callee = _base_analysis(
        "callee_with_contract",
        [{"name": "param_1", "index": 0, "size": 4, "data_type": "int", "is_signed": True}],
        [callee_ret],
    )
    analyzer._apply_outcome_partition_summaries(
        None,
        _cyclic_high_function("CBRANCH"),
        callee,
    )
    analyzer._call_analysis_cache[analyzer._analysis_scope_key(target_ref)] = callee

    param = _param()
    call_arg = Expression.binary_op("INT_ADD", param, Expression.constant(0xFFFFFFFF, 4))
    deferred = DeferredCallInfo(
        target_ref=target_ref,
        arguments=[call_arg],
        call_argument_recovery_status="complete",
    )
    analysis = _base_analysis(
        "f",
        [{"name": "param_1", "index": 0, "size": 4, "data_type": "int", "is_signed": True}],
        [ReturnInfo(address="0x1000", value=Expression.unknown("call@0x1000"), conditions=[])],
    )
    analysis.deferred_calls = {deferred.deferred_call_ref.stable_key(): deferred}

    analyzer._apply_outcome_partition_summaries(
        None,
        _cyclic_high_function("CALL", "CBRANCH"),
        analysis,
    )

    assert analysis.return_outcomes == ()
    assert analysis.divergence_outcomes == ()
    assert analysis.unknown_outcomes == ()


def test_analyzer_uses_callee_outcome_obligation_when_caller_returns_are_proved():
    analyzer = ReturnAnalyzer(None)
    target_ref = CallTargetRef.from_name("callee_with_contract")
    callee_ret = ReturnInfo(address="0x2000", value=_const(0), conditions=[_nonpositive()])
    callee = _base_analysis(
        "callee_with_contract",
        [{"name": "param_1", "index": 0, "size": 4, "data_type": "int", "is_signed": True}],
        [callee_ret],
    )
    analyzer._apply_outcome_partition_summaries(
        None,
        _cyclic_high_function("CBRANCH"),
        callee,
    )
    analyzer._call_analysis_cache[analyzer._analysis_scope_key(target_ref)] = callee

    param = _param()
    call_arg = Expression.binary_op("INT_ADD", param, Expression.constant(0xFFFFFFFF, 4))
    deferred = DeferredCallInfo(
        target_ref=target_ref,
        arguments=[call_arg],
        call_argument_recovery_status="complete",
    )
    analysis = _base_analysis(
        "f",
        [{"name": "param_1", "index": 0, "size": 4, "data_type": "int", "is_signed": True}],
        [
            ReturnInfo(address="0x1000", value=_const(0), conditions=[_nonpositive()]),
            ReturnInfo(address="0x1004", value=param, conditions=[Condition(Expression.binary_op("INT_EQUAL", param, _const(1)), False)]),
        ],
    )
    analysis.deferred_calls = {deferred.deferred_call_ref.stable_key(): deferred}

    analyzer._apply_outcome_partition_summaries(
        None,
        _cyclic_high_function("CALL", "CBRANCH"),
        analysis,
    )

    assert len(analysis.returns) == 2
    assert analysis.divergence_outcomes == ()
    assert len(analysis.unknown_outcomes) == 1
    assert analysis.unknown_outcomes[0].reason == "callee_positive_region_outcome_proof_missing"


def test_analyzer_rejects_callee_contract_when_caller_return_value_is_not_param():
    analyzer = ReturnAnalyzer(None)
    target_ref = CallTargetRef.from_name("callee_with_contract")
    callee_ret = ReturnInfo(address="0x2000", value=_const(0), conditions=[_nonpositive()])
    callee = _base_analysis(
        "callee_with_contract",
        [{"name": "param_1", "index": 0, "size": 4, "data_type": "int", "is_signed": True}],
        [callee_ret],
    )
    analyzer._apply_outcome_partition_summaries(
        None,
        _cyclic_high_function("CBRANCH"),
        callee,
    )
    analyzer._call_analysis_cache[analyzer._analysis_scope_key(target_ref)] = callee

    param = _param()
    call_arg = Expression.binary_op("INT_ADD", param, Expression.constant(0xFFFFFFFF, 4))
    deferred = DeferredCallInfo(
        target_ref=target_ref,
        arguments=[call_arg],
        call_argument_recovery_status="complete",
    )
    analysis = _base_analysis(
        "f",
        [{"name": "param_1", "index": 0, "size": 4, "data_type": "int", "is_signed": True}],
        [
            ReturnInfo(address="0x1000", value=_const(0), conditions=[_nonpositive()]),
            ReturnInfo(address="0x1004", value=Expression.constant(42, 4), conditions=[Condition(Expression.binary_op("INT_EQUAL", param, _const(1)), False)]),
        ],
    )
    analysis.deferred_calls = {deferred.deferred_call_ref.stable_key(): deferred}

    analyzer._apply_outcome_partition_summaries(
        None,
        _cyclic_high_function("CALL", "CBRANCH"),
        analysis,
    )

    assert analysis.return_outcomes == ()
    assert analysis.divergence_outcomes == ()
    assert analysis.unknown_outcomes == ()


def test_analyzer_keeps_whileif_divergence_unknown_without_recurrence_proof():
    phi = Expression(ExpressionType.UNKNOWN, value="phi_circular", size=4)
    t_param = _param()
    c_param = _param2()
    t_positive = Condition(Expression.binary_op("INT_SLESS", _const(0), t_param), False)
    t_nonpositive = t_positive.negate()
    c_positive = Condition(Expression.binary_op("INT_SLESS", _const(0), c_param), False)
    c_nonpositive = c_positive.negate()
    analysis = _base_analysis(
        "f",
        [
            {"name": "param_1", "index": 0, "size": 4, "data_type": "int", "is_signed": True},
            {"name": "param_2", "index": 1, "size": 4, "data_type": "int", "is_signed": True},
        ],
        [
            ReturnInfo(address="0x1000", value=phi, conditions=[]),
            ReturnInfo(address="0x1004", value=_const(0), conditions=[c_nonpositive]),
            ReturnInfo(address="0x1008", value=c_param, conditions=[c_positive, t_positive]),
        ],
    )

    ReturnAnalyzer(None)._apply_outcome_partition_summaries(
        None,
        _cyclic_high_function("CBRANCH", "CBRANCH", "MULTIEQUAL"),
        analysis,
    )

    assert len(analysis.returns) == 2
    assert analysis.returns[1].value.expr_type == ExpressionType.PARAMETER
    assert analysis.returns[1].value.value == 1
    assert analysis.divergence_outcomes == ()
    assert len(analysis.unknown_outcomes) == 1
    assert analysis.unknown_outcomes[0].reason == "branch_guarded_recurrence_proof_missing"


def test_analyzer_proves_whileif_affine_return_and_nonprogress_divergence():
    phi = Expression(ExpressionType.UNKNOWN, value="phi_circular", size=4)
    t_param = _param()
    c_param = _param2()
    t_positive = Condition(Expression.binary_op("INT_SLESS", _const(0), t_param), False)
    t_nonpositive = t_positive.negate()
    c_positive = Condition(Expression.binary_op("INT_SLESS", _const(0), c_param), False)
    c_nonpositive = c_positive.negate()
    recursive_value = Expression.binary_op("INT_ADD", phi, _const(1))
    recursive_value.size = 4
    analysis = _base_analysis(
        "f",
        [
            {"name": "param_1", "index": 0, "size": 4, "data_type": "int", "is_signed": True},
            {"name": "param_2", "index": 1, "size": 4, "data_type": "int", "is_signed": True},
        ],
        [
            ReturnInfo(address="0x1000", value=phi, conditions=[c_positive, t_nonpositive]),
            ReturnInfo(address="0x1004", value=_const(0), conditions=[c_nonpositive]),
            ReturnInfo(address="0x1008", value=c_param, conditions=[c_positive, t_positive]),
            ReturnInfo(address="0x1008", value=recursive_value, conditions=[c_positive, t_positive]),
        ],
    )

    ReturnAnalyzer(None)._apply_outcome_partition_summaries(
        None,
        _branch_guarded_while_proved_high_function(),
        analysis,
    )

    assert len(analysis.returns) == 2
    assert analysis.returns[1].value.expr_type == ExpressionType.PARAMETER
    assert analysis.returns[1].value.value == 1
    assert len(analysis.return_outcomes) == 2
    assert len(analysis.divergence_outcomes) == 1
    assert analysis.divergence_outcomes[0].proof["proof_kind"] == "branch_guarded_while_nonprogress_must_diverge"
    assert analysis.unknown_outcomes == ()


def test_analyzer_proves_whileif_divergence_from_direct_cbranch_targets():
    phi = Expression(ExpressionType.UNKNOWN, value="phi_circular", size=4)
    t_param = _param()
    c_param = _param2()
    t_positive = Condition(Expression.binary_op("INT_SLESS", _const(0), t_param), False)
    t_nonpositive = t_positive.negate()
    c_positive = Condition(Expression.binary_op("INT_SLESS", _const(0), c_param), False)
    c_nonpositive = c_positive.negate()
    recursive_value = Expression.binary_op("INT_ADD", phi, _const(1))
    recursive_value.size = 4
    analysis = _base_analysis(
        "f",
        [
            {"name": "param_1", "index": 0, "size": 4, "data_type": "int", "is_signed": True},
            {"name": "param_2", "index": 1, "size": 4, "data_type": "int", "is_signed": True},
        ],
        [
            ReturnInfo(address="0x1000", value=phi, conditions=[c_positive, t_nonpositive]),
            ReturnInfo(address="0x1004", value=_const(0), conditions=[c_nonpositive]),
            ReturnInfo(address="0x1008", value=c_param, conditions=[c_positive, t_positive]),
            ReturnInfo(address="0x1008", value=recursive_value, conditions=[c_positive, t_positive]),
        ],
    )

    ReturnAnalyzer(None)._apply_outcome_partition_summaries(
        None,
        _branch_guarded_while_direct_target_high_function(),
        analysis,
    )

    assert len(analysis.divergence_outcomes) == 1
    assert analysis.divergence_outcomes[0].proof["excluded_edges"]
    assert analysis.unknown_outcomes == ()


def test_analyzer_rejects_whileif_divergence_from_direct_cbranch_target_space_mismatch():
    phi = Expression(ExpressionType.UNKNOWN, value="phi_circular", size=4)
    t_param = _param()
    c_param = _param2()
    t_positive = Condition(Expression.binary_op("INT_SLESS", _const(0), t_param), False)
    t_nonpositive = t_positive.negate()
    c_positive = Condition(Expression.binary_op("INT_SLESS", _const(0), c_param), False)
    c_nonpositive = c_positive.negate()
    recursive_value = Expression.binary_op("INT_ADD", phi, _const(1))
    recursive_value.size = 4
    analysis = _base_analysis(
        "f",
        [
            {"name": "param_1", "index": 0, "size": 4, "data_type": "int", "is_signed": True},
            {"name": "param_2", "index": 1, "size": 4, "data_type": "int", "is_signed": True},
        ],
        [
            ReturnInfo(address="0x1000", value=phi, conditions=[c_positive, t_nonpositive]),
            ReturnInfo(address="0x1004", value=_const(0), conditions=[c_nonpositive]),
            ReturnInfo(address="0x1008", value=c_param, conditions=[c_positive, t_positive]),
            ReturnInfo(address="0x1008", value=recursive_value, conditions=[c_positive, t_positive]),
        ],
    )

    ReturnAnalyzer(None)._apply_outcome_partition_summaries(
        None,
        _branch_guarded_while_direct_target_high_function(target_space="rom", target_is_constant=False),
        analysis,
    )

    assert analysis.divergence_outcomes == ()
    assert len(analysis.unknown_outcomes) == 1
    assert analysis.unknown_outcomes[0].reason == "branch_guarded_recurrence_proof_missing"


def test_analyzer_rejects_whileif_divergence_when_cycle_redefines_guard_dependency():
    phi = Expression(ExpressionType.UNKNOWN, value="phi_circular", size=4)
    t_param = _param()
    c_param = _param2()
    t_positive = Condition(Expression.binary_op("INT_SLESS", _const(0), t_param), False)
    t_nonpositive = t_positive.negate()
    c_positive = Condition(Expression.binary_op("INT_SLESS", _const(0), c_param), False)
    c_nonpositive = c_positive.negate()
    recursive_value = Expression.binary_op("INT_ADD", phi, _const(1))
    recursive_value.size = 4
    analysis = _base_analysis(
        "f",
        [
            {"name": "param_1", "index": 0, "size": 4, "data_type": "int", "is_signed": True},
            {"name": "param_2", "index": 1, "size": 4, "data_type": "int", "is_signed": True},
        ],
        [
            ReturnInfo(address="0x1000", value=phi, conditions=[c_positive, t_nonpositive]),
            ReturnInfo(address="0x1004", value=_const(0), conditions=[c_nonpositive]),
            ReturnInfo(address="0x1008", value=c_param, conditions=[c_positive, t_positive]),
            ReturnInfo(address="0x1008", value=recursive_value, conditions=[c_positive, t_positive]),
        ],
    )

    ReturnAnalyzer(None)._apply_outcome_partition_summaries(
        None,
        _branch_guarded_while_proved_high_function(redefine_cycle_guard_dependency=True),
        analysis,
    )

    assert len(analysis.returns) == 2
    assert analysis.divergence_outcomes == ()
    assert len(analysis.unknown_outcomes) == 1
    assert analysis.unknown_outcomes[0].reason == "branch_guarded_recurrence_proof_missing"


def test_analyzer_rejects_whileif_divergence_when_precycle_redefines_guard_dependency():
    phi = Expression(ExpressionType.UNKNOWN, value="phi_circular", size=4)
    t_param = _param()
    c_param = _param2()
    t_positive = Condition(Expression.binary_op("INT_SLESS", _const(0), t_param), False)
    t_nonpositive = t_positive.negate()
    c_positive = Condition(Expression.binary_op("INT_SLESS", _const(0), c_param), False)
    c_nonpositive = c_positive.negate()
    recursive_value = Expression.binary_op("INT_ADD", phi, _const(1))
    recursive_value.size = 4
    analysis = _base_analysis(
        "f",
        [
            {"name": "param_1", "index": 0, "size": 4, "data_type": "int", "is_signed": True},
            {"name": "param_2", "index": 1, "size": 4, "data_type": "int", "is_signed": True},
        ],
        [
            ReturnInfo(address="0x1000", value=phi, conditions=[c_positive, t_nonpositive]),
            ReturnInfo(address="0x1004", value=_const(0), conditions=[c_nonpositive]),
            ReturnInfo(address="0x1008", value=c_param, conditions=[c_positive, t_positive]),
            ReturnInfo(address="0x1008", value=recursive_value, conditions=[c_positive, t_positive]),
        ],
    )

    ReturnAnalyzer(None)._apply_outcome_partition_summaries(
        None,
        _branch_guarded_while_proved_high_function(redefine_precycle_guard_dependency=True),
        analysis,
    )

    assert len(analysis.returns) == 2
    assert analysis.divergence_outcomes == ()
    assert len(analysis.unknown_outcomes) == 1
    assert analysis.unknown_outcomes[0].reason == "branch_guarded_recurrence_proof_missing"


def test_analyzer_rejects_whileif_divergence_when_root_guard_varnode_is_redefined():
    analysis = _branch_guarded_while_analysis()

    ReturnAnalyzer(None)._apply_outcome_partition_summaries(
        None,
        _branch_guarded_while_proved_high_function(
            root_condition_without_def=True,
            redefine_precycle_guard_dependency=True,
        ),
        analysis,
    )

    assert len(analysis.returns) == 2
    assert analysis.divergence_outcomes == ()
    assert len(analysis.unknown_outcomes) == 1
    assert analysis.unknown_outcomes[0].reason == "branch_guarded_recurrence_proof_missing"


def test_analyzer_rejects_whileif_divergence_when_guard_condition_def_is_unsupported():
    for mnemonic in ("LOAD", "FLOAT_ADD", "PIECE"):
        analysis = _branch_guarded_while_analysis()

        ReturnAnalyzer(None)._apply_outcome_partition_summaries(
            None,
            _branch_guarded_while_proved_high_function(condition_def_mnemonic=mnemonic),
            analysis,
        )

        assert analysis.divergence_outcomes == ()


def test_analyzer_rejects_structural_conditional_nonprogress_without_current_cfg_proof():
    analyzer = ReturnAnalyzer(None)
    target_conditions = (_positive2(), _positive())
    structural_proof = (
        "branch_guarded_affine_unit_count_structural_proof",
        ("schema_version", 1),
        ("function", "f"),
        ("acc_phi", ("pcode_op", "stale-acc")),
        ("state_phi", ("pcode_op", "stale-state")),
        ("progress_backedges", (1,)),
        ("nonprogress_backedges", ()),
        ("conditional_progress_backedges", (1,)),
        ("target", ("(0 < param_2)", "(0 < param_1)")),
        ("target_guard_keys", tuple(sorted((analyzer._condition_identity_key(condition) for condition in target_conditions), key=repr))),
    )
    ret = ReturnInfo(
        address="0x1000",
        value=_param2(),
        conditions=list(target_conditions),
        summary_candidate_source_key=(
            "branch_guarded_affine_initial_count",
            ("structural_proof", structural_proof),
        ),
    )

    proof = analyzer._prove_branch_guarded_structural_nonprogress_must_diverge(
        _branch_guarded_while_proved_high_function(),
        initial_c_ret=ret,
        invariant_conditions=(_positive2(), _nonpositive()),
    )

    assert proof is None


def test_analyzer_rejects_structural_conditional_nonprogress_without_negated_guard():
    analyzer = ReturnAnalyzer(None)
    target_conditions = (_positive2(), _positive())
    structural_proof = (
        "branch_guarded_affine_unit_count_structural_proof",
        ("schema_version", 1),
        ("function", "f"),
        ("acc_phi", ("pcode_op", "stale-acc")),
        ("state_phi", ("pcode_op", "stale-state")),
        ("progress_backedges", (1,)),
        ("nonprogress_backedges", ()),
        ("conditional_progress_backedges", (1,)),
        ("target", ("(0 < param_2)", "(0 < param_1)")),
        ("target_guard_keys", tuple(sorted((analyzer._condition_identity_key(condition) for condition in target_conditions), key=repr))),
    )
    ret = ReturnInfo(
        address="0x1000",
        value=_param2(),
        conditions=list(target_conditions),
        summary_candidate_source_key=(
            "branch_guarded_affine_initial_count",
            ("structural_proof", structural_proof),
        ),
    )

    proof = analyzer._prove_branch_guarded_structural_nonprogress_must_diverge(
        _branch_guarded_while_proved_high_function(),
        initial_c_ret=ret,
        invariant_conditions=(_positive2(), _positive()),
    )

    assert proof is None


def test_analyzer_requires_conditional_progress_guard_itself_to_contradict_invariant():
    analyzer = ReturnAnalyzer(None)
    c_positive = _positive2()
    t_positive = _positive()
    t_nonpositive = _nonpositive()

    assert analyzer._conditional_progress_guards_contradict_invariant(
        {1: analyzer._condition_identity_key(c_positive)},
        target_conditions=(c_positive, t_positive),
        invariant_conditions=(c_positive, t_nonpositive),
    ) is False


def test_analyzer_accepts_conditional_progress_only_when_progress_guard_contradicts_invariant():
    analyzer = ReturnAnalyzer(None)
    c_positive = _positive2()
    t_positive = _positive()
    t_nonpositive = _nonpositive()

    assert analyzer._conditional_progress_guards_contradict_invariant(
        {1: analyzer._condition_identity_key(t_positive)},
        target_conditions=(c_positive, t_positive),
        invariant_conditions=(c_positive, t_nonpositive),
    ) is True


def test_analyzer_rejects_whileif_affine_step_two_without_structural_recurrence_proof():
    phi = Expression(ExpressionType.UNKNOWN, value="phi_circular", size=4)
    t_param = _param()
    c_param = _param2()
    t_positive = Condition(Expression.binary_op("INT_SLESS", _const(0), t_param), False)
    t_nonpositive = t_positive.negate()
    c_positive = Condition(Expression.binary_op("INT_SLESS", _const(0), c_param), False)
    c_nonpositive = c_positive.negate()
    c_minus_one = Expression.binary_op("INT_SUB", c_param, _const(1))
    base_guard = Condition(Expression.binary_op("INT_SLESSEQUAL", c_minus_one, _const(0)), False)
    step_guard = Condition(Expression.binary_op("INT_SLESS", _const(0), c_minus_one), False)
    recursive_value = Expression.binary_op(
        "INT_ADD",
        Expression.binary_op("INT_ADD", phi, _const(1)),
        _const(1),
    )
    recursive_value.size = 4
    analysis = _base_analysis(
        "f",
        [
            {"name": "param_1", "index": 0, "size": 4, "data_type": "int", "is_signed": True},
            {"name": "param_2", "index": 1, "size": 4, "data_type": "int", "is_signed": True},
        ],
        [
            ReturnInfo(address="0x1000", value=phi, conditions=[c_positive, t_nonpositive]),
            ReturnInfo(address="0x1004", value=_const(0), conditions=[c_nonpositive]),
            ReturnInfo(address="0x1008", value=_const(1), conditions=[c_positive, t_positive, base_guard]),
            ReturnInfo(address="0x1008", value=recursive_value, conditions=[c_positive, t_positive, step_guard]),
        ],
    )

    ReturnAnalyzer(None)._apply_outcome_partition_summaries(
        None,
        _branch_guarded_while_proved_high_function(),
        analysis,
    )

    assert analysis.return_outcomes == ()
    assert analysis.divergence_outcomes == ()
    assert analysis.unknown_outcomes == ()


def test_analyzer_rejects_whileif_affine_step_two_wrong_base_anchor_value():
    phi = Expression(ExpressionType.UNKNOWN, value="phi_circular", size=4)
    t_param = _param()
    c_param = _param2()
    t_positive = Condition(Expression.binary_op("INT_SLESS", _const(0), t_param), False)
    t_nonpositive = t_positive.negate()
    c_positive = Condition(Expression.binary_op("INT_SLESS", _const(0), c_param), False)
    c_nonpositive = c_positive.negate()
    c_minus_one = Expression.binary_op("INT_SUB", c_param, _const(1))
    base_guard = Condition(Expression.binary_op("INT_SLESSEQUAL", c_minus_one, _const(0)), False)
    step_guard = Condition(Expression.binary_op("INT_SLESS", _const(0), c_minus_one), False)
    recursive_value = Expression.binary_op(
        "INT_ADD",
        Expression.binary_op("INT_ADD", phi, _const(1)),
        _const(1),
    )
    recursive_value.size = 4
    analysis = _base_analysis(
        "f",
        [
            {"name": "param_1", "index": 0, "size": 4, "data_type": "int", "is_signed": True},
            {"name": "param_2", "index": 1, "size": 4, "data_type": "int", "is_signed": True},
        ],
        [
            ReturnInfo(address="0x1000", value=phi, conditions=[c_positive, t_nonpositive]),
            ReturnInfo(address="0x1004", value=_const(0), conditions=[c_nonpositive]),
            ReturnInfo(address="0x1008", value=_const(2), conditions=[c_positive, t_positive, base_guard]),
            ReturnInfo(address="0x1008", value=recursive_value, conditions=[c_positive, t_positive, step_guard]),
        ],
    )

    ReturnAnalyzer(None)._apply_outcome_partition_summaries(
        None,
        _branch_guarded_while_proved_high_function(),
        analysis,
    )

    assert analysis.return_outcomes == ()
    assert analysis.divergence_outcomes == ()
    assert analysis.unknown_outcomes == ()


def test_analyzer_rejects_whileif_affine_summary_without_exact_base_return():
    phi = Expression(ExpressionType.UNKNOWN, value="phi_circular", size=4)
    t_param = _param()
    c_param = _param2()
    t_positive = Condition(Expression.binary_op("INT_SLESS", _const(0), t_param), False)
    t_nonpositive = t_positive.negate()
    c_positive = Condition(Expression.binary_op("INT_SLESS", _const(0), c_param), False)
    c_nonpositive = c_positive.negate()
    recursive_value = Expression.binary_op("INT_ADD", phi, _const(1))
    recursive_value.size = 4
    analysis = _base_analysis(
        "f",
        [
            {"name": "param_1", "index": 0, "size": 4, "data_type": "int", "is_signed": True},
            {"name": "param_2", "index": 1, "size": 4, "data_type": "int", "is_signed": True},
        ],
        [
            ReturnInfo(address="0x1000", value=phi, conditions=[c_positive, t_nonpositive]),
            ReturnInfo(address="0x1004", value=_const(0), conditions=[c_nonpositive]),
            ReturnInfo(address="0x1008", value=recursive_value, conditions=[c_positive, t_positive]),
        ],
    )

    ReturnAnalyzer(None)._apply_outcome_partition_summaries(
        None,
        _branch_guarded_while_proved_high_function(),
        analysis,
    )

    assert analysis.return_outcomes == ()
    assert analysis.divergence_outcomes == ()
    assert analysis.unknown_outcomes == ()


def test_analyzer_rejects_whileif_affine_summary_with_conflicting_same_site_artifact():
    phi = Expression(ExpressionType.UNKNOWN, value="phi_circular", size=4)
    t_param = _param()
    c_param = _param2()
    t_positive = Condition(Expression.binary_op("INT_SLESS", _const(0), t_param), False)
    t_nonpositive = t_positive.negate()
    c_positive = Condition(Expression.binary_op("INT_SLESS", _const(0), c_param), False)
    c_nonpositive = c_positive.negate()
    c_minus_one = Expression.binary_op("INT_SUB", c_param, _const(1))
    base_guard = Condition(Expression.binary_op("INT_SLESSEQUAL", c_minus_one, _const(0)), False)
    step_guard = Condition(Expression.binary_op("INT_SLESS", _const(0), c_minus_one), False)
    recursive_value = Expression.binary_op(
        "INT_ADD",
        Expression.binary_op("INT_ADD", phi, _const(1)),
        _const(1),
    )
    recursive_value.size = 4
    analysis = _base_analysis(
        "f",
        [
            {"name": "param_1", "index": 0, "size": 4, "data_type": "int", "is_signed": True},
            {"name": "param_2", "index": 1, "size": 4, "data_type": "int", "is_signed": True},
        ],
        [
            ReturnInfo(address="0x1000", value=phi, conditions=[c_positive, t_nonpositive]),
            ReturnInfo(address="0x1004", value=_const(0), conditions=[c_nonpositive]),
            ReturnInfo(address="0x1008", value=_const(1), conditions=[c_positive, t_positive, base_guard]),
            ReturnInfo(address="0x100c", value=_const(0), conditions=[c_positive, t_positive, step_guard]),
            ReturnInfo(address="0x100c", value=recursive_value, conditions=[c_positive, t_positive, step_guard]),
        ],
    )

    ReturnAnalyzer(None)._apply_outcome_partition_summaries(
        None,
        _branch_guarded_while_proved_high_function(),
        analysis,
    )

    assert analysis.return_outcomes == ()
    assert analysis.divergence_outcomes == ()
    assert analysis.unknown_outcomes == ()


def test_analyzer_does_not_prune_return_edge_from_final_return_partition_only():
    phi = Expression(ExpressionType.UNKNOWN, value="phi_circular", size=4)
    t_param = _param()
    c_param = _param2()
    t_positive = Condition(Expression.binary_op("INT_SLESS", _const(0), t_param), False)
    t_nonpositive = t_positive.negate()
    c_positive = Condition(Expression.binary_op("INT_SLESS", _const(0), c_param), False)
    c_nonpositive = c_positive.negate()
    recursive_value = Expression.binary_op("INT_ADD", phi, _const(1))
    recursive_value.size = 4
    analysis = _base_analysis(
        "f",
        [
            {"name": "param_1", "index": 0, "size": 4, "data_type": "int", "is_signed": True},
            {"name": "param_2", "index": 1, "size": 4, "data_type": "int", "is_signed": True},
        ],
        [
            ReturnInfo(address="0x1000", value=phi, conditions=[c_positive, t_nonpositive]),
            ReturnInfo(address="0x1004", value=_const(0), conditions=[c_nonpositive]),
            ReturnInfo(address="0x1008", value=c_param, conditions=[c_positive, t_positive]),
            ReturnInfo(address="0x1008", value=recursive_value, conditions=[c_positive, t_positive]),
        ],
    )

    ReturnAnalyzer(None)._apply_outcome_partition_summaries(
        None,
        _cyclic_high_function("CBRANCH", "CBRANCH", "MULTIEQUAL"),
        analysis,
    )

    assert len(analysis.returns) == 2
    assert analysis.divergence_outcomes == ()
    assert len(analysis.unknown_outcomes) == 1
    assert analysis.unknown_outcomes[0].reason == "branch_guarded_recurrence_proof_missing"


def test_analyzer_does_not_synthesize_whileif_partition_from_phi_only():
    phi = Expression(ExpressionType.UNKNOWN, value="phi_circular", size=4)
    analysis = _base_analysis(
        "f",
        [
            {"name": "param_1", "index": 0, "size": 4, "data_type": "int", "is_signed": True},
            {"name": "param_2", "index": 1, "size": 4, "data_type": "int", "is_signed": True},
        ],
        [ReturnInfo(address="0x1000", value=phi, conditions=[])],
    )

    ReturnAnalyzer(None)._apply_outcome_partition_summaries(
        None,
        _cyclic_high_function("CBRANCH", "CBRANCH", "MULTIEQUAL"),
        analysis,
    )

    assert analysis.return_outcomes == ()
    assert analysis.divergence_outcomes == ()
    assert analysis.unknown_outcomes == ()


def test_analyzer_does_not_synthesize_whileif_partition_when_initial_count_value_missing():
    phi = Expression(ExpressionType.UNKNOWN, value="phi_circular", size=4)
    t_param = _param()
    c_param = _param2()
    t_positive = Condition(Expression.binary_op("INT_SLESS", _const(0), t_param), False)
    c_positive = Condition(Expression.binary_op("INT_SLESS", _const(0), c_param), False)
    c_nonpositive = c_positive.negate()
    analysis = _base_analysis(
        "f",
        [
            {"name": "param_1", "index": 0, "size": 4, "data_type": "int", "is_signed": True},
            {"name": "param_2", "index": 1, "size": 4, "data_type": "int", "is_signed": True},
        ],
        [
            ReturnInfo(address="0x1000", value=phi, conditions=[]),
            ReturnInfo(address="0x1004", value=_const(0), conditions=[c_nonpositive]),
            ReturnInfo(address="0x1008", value=Expression.constant(42, 4), conditions=[c_positive, t_positive]),
        ],
    )

    ReturnAnalyzer(None)._apply_outcome_partition_summaries(
        None,
        _cyclic_high_function("CBRANCH", "CBRANCH", "MULTIEQUAL"),
        analysis,
    )

    assert analysis.return_outcomes == ()
    assert analysis.divergence_outcomes == ()
    assert analysis.unknown_outcomes == ()


def test_analyzer_clears_stale_unknown_outcomes_after_return_partition_changes():
    phi = Expression(ExpressionType.UNKNOWN, value="phi_circular", size=4)
    t_param = _param()
    c_param = _param2()
    t_positive = Condition(Expression.binary_op("INT_SLESS", _const(0), t_param), False)
    c_positive = Condition(Expression.binary_op("INT_SLESS", _const(0), c_param), False)
    c_nonpositive = c_positive.negate()
    analysis = _base_analysis(
        "f",
        [
            {"name": "param_1", "index": 0, "size": 4, "data_type": "int", "is_signed": True},
            {"name": "param_2", "index": 1, "size": 4, "data_type": "int", "is_signed": True},
        ],
        [
            ReturnInfo(address="0x1000", value=phi, conditions=[]),
            ReturnInfo(address="0x1004", value=_const(0), conditions=[c_nonpositive]),
            ReturnInfo(address="0x1008", value=c_param, conditions=[c_positive, t_positive]),
        ],
    )
    analyzer = ReturnAnalyzer(None)
    high_function = _cyclic_high_function("CBRANCH", "CBRANCH", "MULTIEQUAL")

    analyzer._apply_outcome_partition_summaries(None, high_function, analysis)
    assert len(analysis.unknown_outcomes) == 1

    analysis.returns = [
        ReturnInfo(address="0x1004", value=_const(0), conditions=[]),
    ]
    analyzer._apply_outcome_partition_summaries(None, high_function, analysis)

    assert analysis.return_outcomes == ()
    assert analysis.divergence_outcomes == ()
    assert analysis.unknown_outcomes == ()


def test_analyzer_does_not_propagate_caller_divergence_with_incomplete_argument_binding():
    param = _param()
    call_arg = Expression.binary_op("INT_ADD", param, Expression.constant(0xFFFFFFFF, 4))
    deferred = DeferredCallInfo(
        target_ref=CallTargetRef.from_name("tr"),
        arguments=[call_arg],
        call_argument_recovery_status="recoverable_partial",
    )
    analysis = _base_analysis(
        "f",
        [{"name": "param_1", "index": 0, "size": 4, "data_type": "int", "is_signed": True}],
        [ReturnInfo(address="0x1000", value=Expression.unknown("tr@0x1000"), conditions=[])],
    )
    analysis.deferred_calls = {deferred.deferred_call_ref.stable_key(): deferred}

    ReturnAnalyzer(None)._apply_outcome_partition_summaries(
        None,
        _cyclic_high_function("CALL", "CBRANCH"),
        analysis,
    )

    assert analysis.return_outcomes == ()
    assert analysis.divergence_outcomes == ()
    assert analysis.unknown_outcomes == ()


def test_analyzer_does_not_classify_nonpositive_return_with_forbidden_store_as_divergence():
    ret = ReturnInfo(address="0x1000", value=_const(0), conditions=[_nonpositive()])
    analysis = _base_analysis(
        "tr",
        [{"name": "param_1", "index": 0, "size": 4, "data_type": "int", "is_signed": True}],
        [ret],
    )

    ReturnAnalyzer(None)._apply_outcome_partition_summaries(
        None,
        _cyclic_high_function("CBRANCH", "STORE"),
        analysis,
    )

    assert analysis.return_outcomes == ()
    assert analysis.divergence_outcomes == ()
    assert analysis.unknown_outcomes == ()


def test_analyzer_does_not_classify_guard_mismatch_loop_as_divergence():
    ret = ReturnInfo(address="0x1000", value=_const(0), conditions=[_le_one()])
    analysis = _base_analysis(
        "tr",
        [{"name": "param_1", "index": 0, "size": 4, "data_type": "int", "is_signed": True}],
        [ret],
    )

    ReturnAnalyzer(None)._apply_outcome_partition_summaries(
        None,
        _cyclic_high_function("CBRANCH"),
        analysis,
    )

    assert analysis.return_outcomes == ()
    assert analysis.divergence_outcomes == ()
    assert analysis.unknown_outcomes == ()
