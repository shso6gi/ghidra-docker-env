# -*- coding: utf-8 -*-

from unittest.mock import Mock
from dataclasses import replace

import pytest

from scripts.function_tracer_pcode.analysis import ReturnAnalyzer
from scripts.function_tracer_pcode.analysis.analyzer_services.return_extraction_1 import (
    _build_function_outcome_seed,
    _produce_standard_termination_path_effect_evidence,
)
from scripts.function_tracer_pcode.analysis.recurrence_summary import StructuralRecurrenceSummarizer
from scripts.function_tracer_pcode.equivalence.strategies.pairwise import PairwiseStrategy
from scripts.function_tracer_pcode.equivalence.strategies.proof_gates.return_coverage import (
    _prove_unary_outcome_for_analysis,
)
from scripts.function_tracer_pcode.equivalence.obligations import AnalysisSnapshot, ObligationRuntimeSession
from scripts.function_tracer_pcode.model import (
    CallTargetRef,
    Condition,
    DeferredCallInfo,
    DivergenceOutcome,
    Expression,
    ExpressionType,
    FunctionReturnAnalysis,
    FunctionOutcomeSeed,
    PcodeOpRef,
    ReturnInfo,
    ReturnPathEvidence,
    ReturnOutcome,
    SymbolicRegionCandidate,
    TerminalCandidate,
    TerminationContractRef,
    TerminationPathEffectEvidence,
    UnknownOutcome,
    UnknownValueRef,
)
from scripts.function_tracer_pcode.smt.parallel import ParallelResult
from scripts.function_tracer_pcode.smt.solvers.z3 import Z3Solver


class _CompleteProfile:
    pcode_enumeration_complete = True
    cfg_edges_complete = True
    region_identity_complete = True
    region_single_entry = True
    region_all_exits_enumerated = True
    region_cross_edges_enumerated = True
    terminal_return_coverage_complete = True
    unsupported_mnemonics = ()
    branchind_count = 0
    callind_count = 0
    callother_count = 0
    abnormal_terminal_block_count = 0
    cfg_acyclic = True
    return_block_count = 1
    region_pcode_op_keys = (PcodeOpRef(address_offset=1, mnemonic="RETURN").stable_key(),)
    region_entry_block_key = ("block", 0)
    region_block_keys = (("block", 0),)
    region_exit_block_keys = (("block", 0),)
    region_cfg_edge_keys = ()

    def stable_key(self):
        return ("function_control_effect_profile", "complete")


class _EffectSummaryStub:
    def __init__(self, profile=None):
        self.function_control_effect_profile = profile or _CompleteProfile()

    def stable_key(self):
        return ("effect_summary_stub", self.function_control_effect_profile.stable_key())


class _DisconnectedProfile(_CompleteProfile):
    region_block_keys = (("block", 0), ("block", 1))
    region_exit_block_keys = (("block", 0),)
    region_cfg_edge_keys = ()

    def stable_key(self):
        return ("function_control_effect_profile", "disconnected")


class _TerminationProfile(_CompleteProfile):
    call_ref = PcodeOpRef(address_offset=2, mnemonic="CALL")
    region_pcode_op_keys = (call_ref.stable_key(),)
    terminal_return_coverage_complete = False
    abnormal_terminal_block_count = 1
    return_block_count = 0
    region_exit_block_keys = ()

    def stable_key(self):
        return ("function_control_effect_profile", "termination")


class _DivergenceProfile(_CompleteProfile):
    region_entry_block_key = ("pcode_block", "bin", ("function",), 0, "ram", 0)
    region_block_keys = (
        region_entry_block_key,
        ("pcode_block", "bin", ("function",), 1, "ram", 16),
    )
    region_exit_block_keys = (region_entry_block_key,)
    region_cfg_edge_keys = (
        (
            ("pcode_block", "bin", ("function_entry",), 0, 0),
            ("pcode_block", "bin", ("function_entry",), 1, 16),
        ),
        (
            ("pcode_block", "bin", ("function_entry",), 1, 16),
            ("pcode_block", "bin", ("function_entry",), 1, 16),
        ),
    )
    cfg_acyclic = False

    def stable_key(self):
        return ("function_control_effect_profile", "divergence")


class _MultiReturnProfile(_CompleteProfile):
    return_block_count = 2
    region_entry_block_key = ("block", 0)
    region_block_keys = (("block", 0), ("block", 1), ("block", 2))
    region_exit_block_keys = (("block", 1), ("block", 2))
    region_cfg_edge_keys = ((("block", 0), ("block", 1)), (("block", 0), ("block", 2)))
    region_pcode_op_keys = (
        PcodeOpRef(address_offset=1, mnemonic="RETURN").stable_key(),
        PcodeOpRef(address_offset=2, mnemonic="RETURN").stable_key(),
    )

    def stable_key(self):
        return ("function_control_effect_profile", "multi_return")


class _ThreeReturnProfile(_CompleteProfile):
    return_block_count = 3
    region_entry_block_key = ("block", 0)
    region_block_keys = (("block", 0), ("block", 1), ("block", 2), ("block", 3))
    region_exit_block_keys = (("block", 1), ("block", 2), ("block", 3))
    region_cfg_edge_keys = tuple((("block", 0), ("block", index)) for index in (1, 2, 3))
    region_pcode_op_keys = tuple(
        PcodeOpRef(address_offset=index, mnemonic="RETURN").stable_key() for index in (1, 2, 3)
    )

    def stable_key(self):
        return ("function_control_effect_profile", "three_return")


def _valid_must_diverge_proof():
    return {
        "proof_kind": "single_guard_nonprogress_must_diverge",
        "candidate_rule": "side_effect_free_nonprogress_loop_guard_complement",
        "guard": "param_positive",
        "return_partition": "param_nonpositive_return_zero",
        "scc_blocks": [1],
        "entry_edges": [{"source": 0, "target": 1, "guard_relation": "entry_guard_equivalent_to_divergence_guard"}],
        "exit_edges": [],
        "side_effect_control_safety": {
            "forbidden_ops_absent": True,
            "return_ops_absent_in_scc": True,
            "guard_state_writes_absent": True,
        },
        "invariant_preservation": {
            "internal_guarded_continue": True,
            "internal_unconditional_continue": False,
        },
        "cfg_applicability_surface": ((0, 1), ((0, 1), (1, 1))),
    }


def _valid_branch_structural_proof():
    return {
        "proof_kind": "branch_guarded_structural_nonprogress_must_diverge",
        "candidate_rule": "branch_guarded_loop_invariant_nonprogress",
        "invariant": ["param_1 > 0"],
        "structural_recurrence_proof": ("branch_guarded_affine_unit_count_structural_proof", "v1"),
        "nonprogress_backedges": ((1, 1),),
        "conditional_progress_backedges": (),
        "conditional_progress_guard_keys": (),
        "conditional_progress_guard_negated_by_invariant": False,
        "state_preservation": "state_phi_nonprogress_backedge_identity",
        "accumulator_preservation": "accumulator_phi_nonprogress_backedge_identity",
        "loop_has_cfg_cycle": True,
        "forbidden_control_effect_ops_absent": True,
        "cfg_applicability_surface": ((0, 1), ((0, 1), (1, 1))),
    }


def _valid_branch_while_proof():
    return {
        "proof_kind": "branch_guarded_while_nonprogress_must_diverge",
        "candidate_rule": "branch_guarded_loop_invariant_nonprogress",
        "invariant": ["param_1 > 0"],
        "reachable_blocks": ["0", "1"],
        "cycle_blocks": ["1"],
        "excluded_edges": [{
            "source": "0", "target": "1", "edge_condition": "param_1 <= 0",
            "relation": "invariant_contradicts_edge",
        }],
        "side_effect_control_safety": {
            "forbidden_ops_absent": True,
            "return_ops_absent_under_invariant": True,
            "guard_state_writes_absent_under_invariant": True,
            "guard_dependency_writes_absent_under_invariant": True,
        },
        "cfg_applicability_surface": ((0, 1), ((0, 1), (1, 1))),
    }


def _process_termination_contract(terminal_id, guard=(), payload=("symbolic",)):
    profile = _TerminationProfile()
    source = (
        "terminal_path_effect_evidence_v1",
        profile.call_ref.stable_key(),
        profile.stable_key(),
        tuple(sorted((condition.structural_key() for condition in guard), key=repr)),
    )
    return TerminationContractRef(
        termination_class="process",
        object_identity_key=profile.call_ref.stable_key(),
        payload_key=(
            "process_exit_payload_v1", "immediate_process_exit",
            ("termination_callee_contract_v1", ("external_function", "libc.so.6", "_Exit", 1)),
            payload,
        ),
        effect_key=(
            "termination_effect_v2", "process", "immediate_process_exit",
            ("atexit_handlers", False),
            ("quick_exit_handlers", False),
            ("stdio_flush", False),
            ("automatic_object_cleanup", False),
        ),
        observation_contract_key=(
            "termination_observation_v2", "process",
            ("process_exit_status", True),
            ("pretermination_memory_effects", "compared_separately"),
        ),
        source_contract_key=source,
    )


def _param() -> Expression:
    return Expression.parameter("param_1", index=0, data_type="int", size=4)


def _param2() -> Expression:
    return Expression.parameter("param_2", index=1, data_type="int", size=4)


def _const(value: int) -> Expression:
    return Expression.constant(value, 4)


def _attach_complete_return_path_evidence(analysis, index=0, condition_sets=None):
    ref = PcodeOpRef(address_offset=index + 1, mnemonic="RETURN")
    info = analysis.returns[index]
    info.pcode_op_ref = ref
    conditions = condition_sets if condition_sets is not None else [tuple(info.conditions)]
    info.return_path_evidence = ReturnPathEvidence(
        terminal_op_ref=ref,
        coverage_status="complete",
        path_block_keys=((('path_block', 0, '0x0'),),),
        path_guard_keys=tuple(sorted({
            tuple(sorted((condition.structural_key() for condition in group), key=repr))
            for group in conditions
        }, key=repr)),
    )
    return info.return_path_evidence


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


def _equals(value: int) -> Condition:
    return Condition(Expression.binary_op("INT_EQUAL", _param(), _const(value)), False)


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


class _FakeSeq:
    def __init__(self, target, time, order):
        self._target = _FakeAddress("ram", target)
        self._time = time
        self._order = order

    def getTarget(self):
        return self._target

    def getTime(self):
        return self._time

    def getOrder(self):
        return self._order


class _FakeOp:
    def __init__(
        self,
        mnemonic: str,
        *,
        condition_expr=None,
        writes_guard_state=False,
        inputs=(),
        output=None,
        opcode=None,
        target=0x3000,
        time=0,
        order=0,
    ):
        self._mnemonic = mnemonic
        self.condition_expr = condition_expr
        self.writes_guard_state = writes_guard_state
        self._inputs = tuple(inputs or ())
        self._output = output
        self._opcode = opcode
        self._seq = _FakeSeq(target, time, order)
        self._parent = None
        if output is not None:
            output._def_op = self

    def getMnemonic(self):
        return self._mnemonic

    def getOpcode(self):
        return self._opcode

    def getSeqnum(self):
        return self._seq

    def getParent(self):
        return self._parent

    def setParent(self, parent):
        self._parent = parent

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

    def getOffset(self):
        return self._address.getOffset()

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
        for op in self._ops:
            setter = getattr(op, "setParent", None)
            if callable(setter):
                setter(self)
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


class _BranchGuardedStructuralFixture:
    def __init__(self, high_function, acc_phi, trace_map, state_phi=None):
        self.high_function = high_function
        self.acc_phi = acc_phi
        self.state_phi = state_phi
        self.trace_map = trace_map


class _FakeStructuralTracer:
    def __init__(self, trace_map):
        self._trace_map = dict(trace_map)
        self._function_binary_id = None
        self._function_program_id = None
        self._function_entry_space = None
        self._function_entry_offset = None

    def trace_varnode(self, varnode, *args, **kwargs):
        if varnode in self._trace_map:
            return self._trace_map[varnode]
        if getattr(varnode, "isConstant", lambda: False)():
            return Expression.constant(int(varnode.getOffset()), size=max(1, int(varnode.getSize())))
        return None


def _branch_guarded_structural_phi_fixture(
    *,
    acc_increments=True,
    state_decrements=True,
    include_nonprogress_edge=True,
    forbidden_op=None,
):
    zero = _FakeVarnode("const", 0, 4, is_constant=True)
    one = _FakeVarnode("const", 1, 4, is_constant=True)
    t_input = _FakeVarnode("register", 0x4010, 4)
    c_input = _FakeVarnode("register", 0x4014, 4)
    acc_out = _FakeVarnode("unique", 0x5010, 4)
    state_out = _FakeVarnode("unique", 0x5014, 4)
    acc_progress = _FakeVarnode("unique", 0x5020, 4)
    state_progress = _FakeVarnode("unique", 0x5024, 4)
    acc_add = _FakeOp(
        "INT_ADD" if acc_increments else "COPY",
        inputs=(acc_out, one) if acc_increments else (acc_out,),
        output=acc_progress,
        opcode=1,
        target=0x3040,
        time=40,
        order=0,
    )
    state_op = _FakeOp(
        "INT_SUB" if state_decrements else "COPY",
        inputs=(state_out, one) if state_decrements else (state_out,),
        output=state_progress,
        opcode=2,
        target=0x3040,
        time=41,
        order=0,
    )
    acc_inputs = [zero]
    state_inputs = [c_input]
    if include_nonprogress_edge:
        acc_inputs.append(acc_out)
        state_inputs.append(state_out)
    acc_inputs.append(acc_progress)
    state_inputs.append(state_progress)
    acc_phi = _FakeOp(
        "MULTIEQUAL",
        inputs=tuple(acc_inputs),
        output=acc_out,
        opcode=27,
        target=0x3010,
        time=10,
        order=0,
    )
    state_phi = _FakeOp(
        "MULTIEQUAL",
        inputs=tuple(state_inputs),
        output=state_out,
        opcode=27,
        target=0x3010,
        time=11,
        order=0,
    )
    c_compare_out = _FakeVarnode("unique", 0x5030, 1)
    c_compare = _FakeOp(
        "INT_SLESS",
        inputs=(zero, state_out),
        output=c_compare_out,
        opcode=3,
        target=0x3010,
        time=12,
        order=0,
    )
    c_cbranch = _FakeOp(
        "CBRANCH",
        condition_expr=_positive2().expression,
        inputs=(_FakeVarnode("const", 0x3020, 8, is_constant=True), c_compare_out),
        opcode=4,
        target=0x3010,
        time=13,
        order=0,
    )
    t_compare_out = _FakeVarnode("unique", 0x5040, 1)
    t_compare = _FakeOp(
        "INT_SLESS",
        inputs=(zero, t_input),
        output=t_compare_out,
        opcode=3,
        target=0x3020,
        time=20,
        order=0,
    )
    t_cbranch = _FakeOp(
        "CBRANCH",
        condition_expr=_positive().expression,
        inputs=(_FakeVarnode("const", 0x3030, 8, is_constant=True), t_compare_out),
        opcode=4,
        target=0x3020,
        time=21,
        order=0,
    )
    entry = _FakeBlock([], index=0, start=0x3000)
    header = _FakeBlock([acc_phi, state_phi, c_compare, c_cbranch], index=1, start=0x3010)
    branch = _FakeBlock([t_compare, t_cbranch], index=2, start=0x3020)
    body_ops = [acc_add, state_op]
    if forbidden_op is not None:
        body_ops.append(_FakeOp(forbidden_op, opcode=99, target=0x3030, time=30, order=0))
    body = _FakeBlock(body_ops, index=3, start=0x3030)
    ret = _FakeBlock([_FakeOp("RETURN", opcode=5, target=0x3050, time=50, order=0)], index=4, start=0x3050)
    entry.add_out(header)
    header.add_out(branch, condition=_positive2(), is_true=True)
    header.add_out(ret, condition=_nonpositive2(), is_true=False)
    if include_nonprogress_edge:
        branch.add_out(header, condition=_nonpositive(), is_true=False)
    branch.add_out(body, condition=_positive(), is_true=True)
    body.add_out(header)
    return _BranchGuardedStructuralFixture(
        _FakeHighFunction([entry, header, branch, body, ret]),
        acc_phi,
        {zero: _const(0), one: _const(1), t_input: _param(), c_input: _param2()},
        state_phi=state_phi,
    )


def _candidate_phi_source_key(analyzer, acc_phi):
    pcode_ref = PcodeOpRef.from_pcode_op(acc_phi)
    key = pcode_ref.stable_key()
    return (
        "phi_reachability_fallback",
        ("candidate_phi_origin_keys", (key,)),
        ("return_phi_origin_keys", (key,)),
    )


def _branch_guarded_phi_free_fallback_analysis(
    analyzer,
    acc_phi,
    *,
    base_value=1,
    base_guard_matches=True,
    implicit_progress_anchor=False,
):
    t_param = _param()
    c_param = _param2()
    t_positive = Condition(Expression.binary_op("INT_SLESS", _const(0), t_param), False)
    c_positive = Condition(Expression.binary_op("INT_SLESS", _const(0), c_param), False)
    c_nonpositive = c_positive.negate()
    c_minus_one = Expression.binary_op("INT_SUB", c_param, _const(1))
    if implicit_progress_anchor:
        t_less_one = Expression.binary_op("INT_SLESS", t_param, _const(1))
        t_less_one_zext = Expression.unary_op("INT_ZEXT", t_less_one)
        t_less_one_zext.size = 4
        delta = Expression.binary_op("INT_SUB", t_less_one_zext, _const(1))
        delta.size = 4
        adjusted = Expression.binary_op("INT_ADD", delta, c_param)
        adjusted.size = 4
        base_guard = Condition(Expression.binary_op("INT_SLESS", _const(0), adjusted), True)
        base_conditions = [c_positive, base_guard]
    else:
        base_guard = (
            Condition(Expression.binary_op("INT_SLESSEQUAL", c_minus_one, _const(0)), False)
            if base_guard_matches
            else Condition(Expression.binary_op("INT_SLESSEQUAL", c_param, _const(0)), False)
        )
        base_conditions = [c_positive, t_positive, base_guard]
    return _base_analysis(
        "f",
        [
            {"name": "param_1", "index": 0, "size": 4, "data_type": "int", "is_signed": True},
            {"name": "param_2", "index": 1, "size": 4, "data_type": "int", "is_signed": True},
        ],
        [
            ReturnInfo(address="0x1004", value=_const(0), conditions=[c_nonpositive]),
            ReturnInfo(
                address="0x1008",
                value=_const(base_value),
                conditions=base_conditions,
                return_kind="phi_reachability_fallback",
                summary_candidate_source_key=_candidate_phi_source_key(analyzer, acc_phi),
            ),
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


def test_unary_seed_accepts_total_return_only_partition_without_divergence():
    strategy = _strategy()
    left = _analysis(return_guards=[[]], divergence_guards=[])
    right = _analysis(return_guards=[[]], divergence_guards=[])
    for analysis in (left, right):
        terminal_id = ("return", analysis.entry_point)
        evidence = _attach_complete_return_path_evidence(analysis)
        analysis.return_outcomes = ()
        analysis.outcome_seed = FunctionOutcomeSeed(
            function_identity=analysis.outcome_function_identity(),
            input_domain_contract=("all_inputs",),
            terminal_candidates=(TerminalCandidate(
                terminal_id, "return", op_ref=PcodeOpRef(address_offset=1, mnemonic="RETURN")
            ),),
            symbolic_regions=(SymbolicRegionCandidate(
                ("region", terminal_id), terminal_id, (), True,
                producer_evidence_key=("return_path_evidence", evidence.stable_key()),
                observed_value=_const(0)
            ),),
            control_flow_evidence_key=_CompleteProfile().stable_key(),
        )
        analysis.effect_summary = _EffectSummaryStub()
    strategy._obligation_runtime_session = ObligationRuntimeSession.create(left, right)
    assert strategy._outcome_partition_covered_labels(
        _base_ctx(), left, right, _replace_param("p1"), _replace_param("p2")
    ) == {"function1", "function2"}


def test_unary_seed_accepts_complementary_multi_return_partition():
    strategy = _strategy()
    left = _analysis(
        return_guards=[[_positive()], [_nonpositive()]], divergence_guards=[],
        return_values=[_const(1), _const(0)],
    )
    right = _analysis(
        return_guards=[[_positive()], [_nonpositive()]], divergence_guards=[],
        return_values=[_const(1), _const(0)],
    )
    for analysis in (left, right):
        _attach_complete_return_path_evidence(analysis, 0)
        _attach_complete_return_path_evidence(analysis, 1)
        _build_function_outcome_seed(analysis)
        analysis.outcome_seed = replace(
            analysis.outcome_seed,
            control_flow_evidence_key=_MultiReturnProfile().stable_key(),
        )
        analysis.effect_summary = _EffectSummaryStub(_MultiReturnProfile())
    strategy._obligation_runtime_session = ObligationRuntimeSession.create(left, right)
    assert strategy._outcome_partition_covered_labels(
        _base_ctx(), left, right, _replace_param("p1"), _replace_param("p2")
    ) == {"function1", "function2"}


def test_unary_seed_aggregates_multiple_paths_to_one_return_terminal():
    strategy = _strategy()
    analyses = []
    for _ in range(2):
        analysis = _analysis(return_guards=[[_positive()]], divergence_guards=[])
        info = analysis.returns[0]
        evidence = _attach_complete_return_path_evidence(
            analysis, 0, condition_sets=[(_positive(),), (_nonpositive(),)]
        )
        analysis.return_outcomes = (
            ReturnOutcome((_positive(),), _const(0), return_info=info),
            ReturnOutcome((_nonpositive(),), _const(0), return_info=info),
        )
        _build_function_outcome_seed(analysis)
        analysis.outcome_seed = replace(
            analysis.outcome_seed,
            control_flow_evidence_key=_CompleteProfile().stable_key(),
        )
        analysis.effect_summary = _EffectSummaryStub()
        assert len(analysis.outcome_seed.terminal_candidates) == 1
        assert len(analysis.outcome_seed.symbolic_regions) == 2
        assert all(
            region.producer_evidence_key == ("return_path_evidence", evidence.stable_key())
            for region in analysis.outcome_seed.symbolic_regions
        )
        analyses.append(analysis)
    left, right = analyses
    strategy._obligation_runtime_session = ObligationRuntimeSession.create(left, right)
    assert strategy._outcome_partition_covered_labels(
        _base_ctx(), left, right, _replace_param("p1"), _replace_param("p2")
    ) == {"function1", "function2"}


def test_unary_seed_rejects_multi_return_guard_not_matching_path_evidence():
    strategy = _strategy()
    analysis = _analysis(
        return_guards=[[_positive()], [_nonpositive()]], divergence_guards=[],
        return_values=[_const(1), _const(0)],
    )
    _attach_complete_return_path_evidence(analysis, 0)
    _attach_complete_return_path_evidence(analysis, 1)
    _build_function_outcome_seed(analysis)
    first = analysis.outcome_seed.symbolic_regions[0]
    analysis.outcome_seed = replace(
        analysis.outcome_seed,
        symbolic_regions=(replace(first, guard=()), *analysis.outcome_seed.symbolic_regions[1:]),
        control_flow_evidence_key=_MultiReturnProfile().stable_key(),
    )
    analysis.effect_summary = _EffectSummaryStub(_MultiReturnProfile())
    assert not strategy._analysis_has_proved_outcome_partition(
        _base_ctx(), analysis, _replace_param("p1"), "function1"
    )


@pytest.mark.parametrize("guards", [
    [[_equals(0)], [_equals(1)], [_equals(0).negate(), _equals(1).negate()]],
    [[_positive()], [_nonpositive(), _equals(0).negate()], [_equals(0)]],
])
def test_unary_seed_accepts_three_way_and_switch_shaped_return_partitions(guards):
    strategy = _strategy()
    analyses = [
        _analysis(return_guards=guards, divergence_guards=[], return_values=[_const(0), _const(1), _const(2)])
        for _ in range(2)
    ]
    for analysis in analyses:
        for index in range(3):
            _attach_complete_return_path_evidence(analysis, index)
        _build_function_outcome_seed(analysis)
        analysis.outcome_seed = replace(
            analysis.outcome_seed,
            control_flow_evidence_key=_ThreeReturnProfile().stable_key(),
        )
        analysis.effect_summary = _EffectSummaryStub(_ThreeReturnProfile())
    left, right = analyses
    strategy._obligation_runtime_session = ObligationRuntimeSession.create(left, right)
    assert strategy._outcome_partition_covered_labels(
        _base_ctx(), left, right, _replace_param("p1"), _replace_param("p2")
    ) == {"function1", "function2"}


def test_unary_seed_rejects_return_only_partition_with_control_gap():
    strategy = _strategy()
    analysis = _analysis(return_guards=[[]], divergence_guards=[])
    terminal_id = ("return", analysis.entry_point)
    analysis.outcome_seed = FunctionOutcomeSeed(
        function_identity=analysis.outcome_function_identity(),
        input_domain_contract=("all_inputs",),
        terminal_candidates=(TerminalCandidate(terminal_id, "return", cfg_reachable=True),),
        symbolic_regions=(SymbolicRegionCandidate(
            ("region", terminal_id), terminal_id, (), True, observed_value=_const(0)
        ),),
        unresolved_control_evidence=(("indirect_branch",),),
    )
    assert not strategy._analysis_has_proved_outcome_partition(
        _base_ctx(), analysis, _replace_param("p1"), "function1"
    )


def test_unary_gate_does_not_add_redundant_blocker_for_incomplete_control_flow():
    strategy = _strategy()
    analyses = []
    for _ in range(2):
        analysis = _analysis(return_guards=[[]], divergence_guards=[])
        evidence = _attach_complete_return_path_evidence(analysis)
        terminal_id = ("return", analysis.entry_point)
        analysis.outcome_seed = FunctionOutcomeSeed(
            function_identity=analysis.outcome_function_identity(),
            input_domain_contract=("all_inputs",),
            terminal_candidates=(TerminalCandidate(
                terminal_id, "return", op_ref=evidence.terminal_op_ref,
            ),),
            symbolic_regions=(SymbolicRegionCandidate(
                ("region", terminal_id), terminal_id, (), True,
                producer_evidence_key=("return_path_evidence", evidence.stable_key()),
                observed_value=_const(0),
            ),),
            control_flow_evidence_key=_CompleteProfile().stable_key(),
        )
        analysis.effect_summary = _EffectSummaryStub()
        analysis.incomplete_control_flow = True
        analyses.append(analysis)
    left, right = analyses
    strategy._obligation_runtime_session = ObligationRuntimeSession.create(left, right)
    assert strategy._outcome_partition_covered_labels(
        _base_ctx(), left, right, _replace_param("p1"), _replace_param("p2")
    ) == set()
    assert strategy._last_unary_outcome_blockers == {}


def test_unary_production_gate_rejects_unclassified_termination_candidate():
    strategy = _strategy()
    left = _analysis(return_guards=[[]], divergence_guards=[])
    right = _analysis(return_guards=[[]], divergence_guards=[])
    for analysis in (left, right):
        terminal_id = ("termination", analysis.entry_point)
        analysis.outcome_seed = FunctionOutcomeSeed(
            function_identity=analysis.outcome_function_identity(),
            input_domain_contract=("all_inputs",),
            terminal_candidates=(TerminalCandidate(
                terminal_id, "exceptional_termination", op_ref=PcodeOpRef(address_offset=1, mnemonic="CALL")
            ),),
            symbolic_regions=(SymbolicRegionCandidate(
                ("region", terminal_id), terminal_id, (), True
            ),),
            control_flow_evidence_key=_CompleteProfile().stable_key(),
        )
        analysis.effect_summary = _EffectSummaryStub()
    strategy._obligation_runtime_session = ObligationRuntimeSession.create(left, right)
    assert strategy._outcome_partition_covered_labels(
        _base_ctx(), left, right, _replace_param("p1"), _replace_param("p2")
    ) == set()
    assert set(strategy._last_unary_outcome_blockers.values()) == {
        "outcome_termination_classification_unclassified"
    }


def test_outcome_seed_identity_excludes_divergence_proof_payload():
    left = _analysis(return_guards=[[_nonpositive()]], divergence_guards=[[_positive()]])
    right = _analysis(return_guards=[[_nonpositive()]], divergence_guards=[[_positive()]])
    left.divergence_outcomes = (
        DivergenceOutcome((_positive(),), {"proof_kind": "must_diverge", "solver": "first"}),
    )
    right.divergence_outcomes = (
        DivergenceOutcome((_positive(),), {"proof_kind": "must_diverge", "solver": "second"}),
    )
    _build_function_outcome_seed(left)
    _build_function_outcome_seed(right)
    assert left.outcome_seed.stable_key() == right.outcome_seed.stable_key()


def test_unary_cfg_producer_rejects_unreachable_block_surface():
    strategy = _strategy()
    left = _analysis(return_guards=[[]], divergence_guards=[])
    right = _analysis(return_guards=[[]], divergence_guards=[])
    for analysis in (left, right):
        terminal_id = ("return", analysis.entry_point)
        analysis.return_outcomes = ()
        analysis.outcome_seed = FunctionOutcomeSeed(
            function_identity=analysis.outcome_function_identity(),
            input_domain_contract=("all_inputs",),
            terminal_candidates=(TerminalCandidate(
                terminal_id, "return", op_ref=PcodeOpRef(address_offset=1, mnemonic="RETURN")
            ),),
            symbolic_regions=(SymbolicRegionCandidate(
                ("region", terminal_id), terminal_id, (), False, observed_value=_const(0)
            ),),
            control_flow_evidence_key=_DisconnectedProfile().stable_key(),
        )
        analysis.effect_summary = _EffectSummaryStub(_DisconnectedProfile())
    strategy._obligation_runtime_session = ObligationRuntimeSession.create(left, right)
    assert strategy._outcome_partition_covered_labels(
        _base_ctx(), left, right, _replace_param("p1"), _replace_param("p2")
    ) == set()
    assert set(strategy._last_unary_outcome_blockers.values()) == {
        "outcome_cfg_reachability_incomplete"
    }


def test_unary_blocker_target_excludes_pair_side_label():
    strategy = _strategy()
    analysis = _analysis(return_guards=[[]], divergence_guards=[])
    terminal_id = ("return", analysis.entry_point)
    analysis.outcome_seed = FunctionOutcomeSeed(
        function_identity=analysis.outcome_function_identity(),
        input_domain_contract=("all_inputs",),
        terminal_candidates=(TerminalCandidate(terminal_id, "return"),),
        symbolic_regions=(SymbolicRegionCandidate(
            ("region", terminal_id), terminal_id, (), False, observed_value=_const(0)
        ),),
    )
    left = strategy._outcome_partition_unknown_object_target_key(
        "function1:outcome_path_region_incomplete", analysis, analysis
    )
    right = strategy._outcome_partition_unknown_object_target_key(
        "function2:outcome_path_region_incomplete", analysis, analysis
    )
    assert left == right


def test_unary_partition_rejects_explicit_unknown_outcome_even_when_return_is_total():
    strategy = _strategy()
    left = _analysis(return_guards=[[]], divergence_guards=[], unknown_guards=[[]])
    right = _analysis(return_guards=[[]], divergence_guards=[], unknown_guards=[[]])
    for analysis in (left, right):
        _attach_complete_return_path_evidence(analysis)
        _build_function_outcome_seed(analysis)
        analysis.outcome_seed = replace(
            analysis.outcome_seed,
            control_flow_evidence_key=_CompleteProfile().stable_key(),
        )
        analysis.effect_summary = _EffectSummaryStub()
    strategy._obligation_runtime_session = ObligationRuntimeSession.create(left, right)
    assert strategy._outcome_partition_covered_labels(
        _base_ctx(), left, right, _replace_param("p1"), _replace_param("p2")
    ) == set()
    assert set(strategy._last_unary_outcome_blockers.values()) == {
        "outcome_path_region_completeness_incomplete"
    }


def test_validated_process_termination_contract_is_compared_relationally():
    strategy = _strategy()
    left = _analysis(return_guards=[], divergence_guards=[])
    right = _analysis(return_guards=[], divergence_guards=[])
    for analysis in (left, right):
        terminal_id = ("termination", analysis.entry_point)
        contract = _process_termination_contract(terminal_id)
        analysis.termination_path_effect_evidence = (TerminationPathEffectEvidence(
            terminal_candidate_id=terminal_id,
            terminal_op_ref=_TerminationProfile.call_ref,
            control_effect_profile_key=_TerminationProfile().stable_key(),
            path_guard_key=(),
            contract=contract,
        ),)
        analysis.outcome_seed = FunctionOutcomeSeed(
            function_identity=analysis.outcome_function_identity(),
            input_domain_contract=("all_inputs",),
            terminal_candidates=(TerminalCandidate(
                terminal_id,
                "process_termination",
                op_ref=_TerminationProfile.call_ref,
                termination_contract=contract,
            ),),
            symbolic_regions=(SymbolicRegionCandidate(
                ("region", terminal_id), terminal_id, (), False,
                producer_evidence_key=contract.source_contract_key,
            ),),
            control_flow_evidence_key=_TerminationProfile().stable_key(),
        )
        analysis.effect_summary = _EffectSummaryStub(_TerminationProfile())
    strategy._obligation_runtime_session = ObligationRuntimeSession.create(left, right)
    assert strategy._outcome_partition_covered_labels(
        _base_ctx(), left, right, _replace_param("p1"), _replace_param("p2")
    ) == {"function1", "function2"}


def test_termination_path_effect_evidence_changes_unary_snapshot_premise():
    analysis = _analysis(return_guards=[], divergence_guards=[])
    terminal_id = ("termination", analysis.entry_point)
    contract = _process_termination_contract(terminal_id)
    evidence = TerminationPathEffectEvidence(
        terminal_candidate_id=terminal_id,
        terminal_op_ref=_TerminationProfile.call_ref,
        control_effect_profile_key=_TerminationProfile().stable_key(),
        path_guard_key=(),
        contract=contract,
    )
    without_evidence = AnalysisSnapshot.from_function_analysis(analysis)
    analysis.termination_path_effect_evidence = (evidence,)
    with_evidence = AnalysisSnapshot.from_function_analysis(analysis)
    assert with_evidence.semantic_fingerprint != without_evidence.semantic_fingerprint
    analysis.termination_path_effect_evidence = (replace(
        evidence,
        contract=replace(contract, effect_key=("termination_effect_v2", "process", "changed")),
    ),)
    changed_effect = AnalysisSnapshot.from_function_analysis(analysis)
    assert changed_effect.semantic_fingerprint != with_evidence.semantic_fingerprint
    analysis.termination_path_effect_evidence = (replace(evidence, path_guard_key=(("changed",),)),)
    changed_guard = AnalysisSnapshot.from_function_analysis(analysis)
    assert changed_guard.semantic_fingerprint != with_evidence.semantic_fingerprint


def test_production_termination_producer_builds_seed_from_object_derived_exit_call():
    analyzer = ReturnAnalyzer(program=None)
    analysis = _analysis(return_guards=[], divergence_guards=[])
    analysis.effect_summary = _EffectSummaryStub(_TerminationProfile())
    external_function = Mock()
    external_function.getParameterCount.return_value = 1
    parameter = Mock()
    parameter.getDataType.return_value.getName.return_value = "int"
    external_function.getParameters.return_value = [parameter]
    external_function.getReturnType.return_value.getName.return_value = "void"
    target = CallTargetRef.from_name(
        "_Exit", program_id=1, is_external=True, library_name="libc.so.6",
        function_obj=external_function,
    )
    analyzer._current_noreturn_terminal_observations = [{
        "pcode_op_ref": _TerminationProfile.call_ref,
        "target_refs": (target,),
        "noreturn_contract_keys": ((
            "resolved_noreturn_function_v1", target.stable_key(), target.stable_key(),
        ),),
        "argument_keys": (("constant", 0),),
        "conditions": (_positive(),),
    }]
    _produce_standard_termination_path_effect_evidence(analyzer, analysis)
    _build_function_outcome_seed(analysis)
    assert len(analysis.termination_path_effect_evidence) == 1
    assert analysis.termination_path_effect_evidence[0].contract.termination_class == "process"
    assert analysis.outcome_seed.terminal_candidates[0].terminal_kind_candidate == "process_termination"
    assert analysis.outcome_seed.symbolic_regions[0].guard == (_positive(),)


def test_production_termination_producer_does_not_classify_unknown_noreturn_symbol():
    analyzer = ReturnAnalyzer(program=None)
    analysis = _analysis(return_guards=[], divergence_guards=[])
    analysis.effect_summary = _EffectSummaryStub(_TerminationProfile())
    analyzer._current_noreturn_terminal_observations = [{
        "pcode_op_ref": _TerminationProfile.call_ref,
        "target_refs": (CallTargetRef.from_name("project_specific_noreturn"),),
        "noreturn_contract_keys": (("resolved_noreturn_function_v1", ("local",), ("local",)),),
        "argument_keys": (),
        "conditions": (),
    }]
    _produce_standard_termination_path_effect_evidence(analyzer, analysis)
    assert analysis.termination_path_effect_evidence == ()
    assert analysis.unknown_outcomes[0].reason == "unknown_nonreturning_contract"


@pytest.mark.parametrize("target", [
    CallTargetRef.from_name("_Exit", program_id=1, entry_offset=0x1000, is_external=False),
    CallTargetRef.from_name("exit", program_id=1, is_external=True, library_name="libc.so.6"),
    CallTargetRef.from_name("quick_exit", program_id=1, is_external=True, library_name="libc.so.6"),
])
def test_termination_producer_keeps_local_or_unmodeled_standard_names_unknown(target):
    analyzer = ReturnAnalyzer(program=None)
    analysis = _analysis(return_guards=[], divergence_guards=[])
    analysis.effect_summary = _EffectSummaryStub(_TerminationProfile())
    analyzer._current_noreturn_terminal_observations = [{
        "pcode_op_ref": _TerminationProfile.call_ref,
        "target_refs": (target,),
        "noreturn_contract_keys": ((
            "resolved_noreturn_function_v1", target.stable_key(), target.stable_key(),
        ),),
        "argument_keys": (("constant", 0),),
        "conditions": (_positive(),),
    }]
    _produce_standard_termination_path_effect_evidence(analyzer, analysis)
    assert analysis.termination_path_effect_evidence == ()
    assert analysis.unknown_outcomes[0].reason == "unknown_nonreturning_contract"


def test_cached_termination_partition_rejects_removed_prerequisite_evidence():
    strategy = _strategy()
    analyses = []
    for _ in range(2):
        analysis = _analysis(return_guards=[], divergence_guards=[])
        terminal_id = ("termination", analysis.entry_point)
        contract = _process_termination_contract(terminal_id)
        evidence = TerminationPathEffectEvidence(
            terminal_candidate_id=terminal_id,
            terminal_op_ref=_TerminationProfile.call_ref,
            control_effect_profile_key=_TerminationProfile().stable_key(),
            path_guard_key=(),
            contract=contract,
        )
        analysis.termination_path_effect_evidence = (evidence,)
        analysis.outcome_seed = FunctionOutcomeSeed(
            function_identity=analysis.outcome_function_identity(),
            input_domain_contract=("all_inputs",),
            terminal_candidates=(TerminalCandidate(
                terminal_id, "process_termination", op_ref=_TerminationProfile.call_ref,
                termination_contract=contract,
            ),),
            symbolic_regions=(SymbolicRegionCandidate(
                ("region", terminal_id), terminal_id, (), True,
                producer_evidence_key=contract.source_contract_key,
            ),),
            control_flow_evidence_key=_TerminationProfile().stable_key(),
        )
        analysis.effect_summary = _EffectSummaryStub(_TerminationProfile())
        analyses.append(analysis)
    left, right = analyses
    strategy._obligation_runtime_session = ObligationRuntimeSession.create(left, right)
    proof = _prove_unary_outcome_for_analysis(
        strategy, _base_ctx(), left, _replace_param("p1")
    )
    assert proof.complete and proof.cache_entry is not None
    left.termination_path_effect_evidence = ()
    pair = ObligationRuntimeSession.create(left, right)
    with pytest.raises(ValueError, match="premise|snapshot"):
        pair.import_unary_artifact_for_analysis(
            proof.cache_entry,
            analysis=left,
            pair_side="left",
            domain_contract=("all_inputs",),
            normalization_policy_digest=(
                strategy._return_coverage_normalization_policy_digest(
                    strategy._return_coverage_normalization_policy()
                ) or "return-coverage-normalization-unavailable"
            ),
        )


def test_process_termination_payload_difference_is_not_equivalent():
    strategy = _strategy()
    analyses = []
    for payload in (("exit_status", 0), ("exit_status", 1)):
        analysis = _analysis(return_guards=[], divergence_guards=[])
        terminal_id = ("termination", analysis.entry_point)
        contract = _process_termination_contract(terminal_id, payload=payload)
        analysis.termination_path_effect_evidence = (TerminationPathEffectEvidence(
            terminal_candidate_id=terminal_id,
            terminal_op_ref=_TerminationProfile.call_ref,
            control_effect_profile_key=_TerminationProfile().stable_key(),
            path_guard_key=(),
            contract=contract,
        ),)
        analysis.outcome_seed = FunctionOutcomeSeed(
            function_identity=analysis.outcome_function_identity(),
            input_domain_contract=("all_inputs",),
            terminal_candidates=(TerminalCandidate(
                terminal_id, "process_termination", op_ref=_TerminationProfile.call_ref,
                termination_contract=contract,
            ),),
            symbolic_regions=(SymbolicRegionCandidate(
                ("region", terminal_id), terminal_id, (), False,
                producer_evidence_key=contract.source_contract_key,
            ),),
            control_flow_evidence_key=_TerminationProfile().stable_key(),
        )
        analysis.effect_summary = _EffectSummaryStub(_TerminationProfile())
        analyses.append(analysis)
    left, right = analyses
    strategy._obligation_runtime_session = ObligationRuntimeSession.create(left, right)
    assert strategy._outcome_partition_covered_labels(
        _base_ctx(), left, right, _replace_param("p1"), _replace_param("p2")
    ) == set()


def test_must_diverge_requires_exact_validated_proof_schema():
    strategy = _strategy()
    left = _analysis(return_guards=[[_nonpositive()]], divergence_guards=[[_positive()]])
    right = _analysis(return_guards=[[_nonpositive()]], divergence_guards=[[_positive()]])
    for analysis in (left, right):
        _attach_complete_return_path_evidence(analysis)
        analysis.divergence_outcomes = (
            DivergenceOutcome((_positive(),), {"proof_kind": "must_diverge"}),
        )
        _build_function_outcome_seed(analysis)
        analysis.outcome_seed = replace(
            analysis.outcome_seed,
            control_flow_evidence_key=_DivergenceProfile().stable_key(),
        )
        analysis.effect_summary = _EffectSummaryStub(_DivergenceProfile())
    strategy._obligation_runtime_session = ObligationRuntimeSession.create(left, right)
    assert strategy._outcome_partition_covered_labels(
        _base_ctx(), left, right, _replace_param("p1"), _replace_param("p2")
    ) == set()
    assert set(strategy._last_unary_outcome_blockers.values()) == {
        "outcome_path_region_completeness_incomplete"
    }


def test_must_diverge_exact_schema_participates_in_validated_partition():
    strategy = _strategy()
    left = _analysis(return_guards=[[_nonpositive()]], divergence_guards=[[_positive()]])
    right = _analysis(return_guards=[[_nonpositive()]], divergence_guards=[[_positive()]])
    for analysis in (left, right):
        _attach_complete_return_path_evidence(analysis)
        analysis.divergence_outcomes = (
            DivergenceOutcome((_positive(),), _valid_must_diverge_proof()),
        )
        _build_function_outcome_seed(analysis)
        analysis.outcome_seed = replace(
            analysis.outcome_seed,
            control_flow_evidence_key=_DivergenceProfile().stable_key(),
        )
        analysis.effect_summary = _EffectSummaryStub(_DivergenceProfile())
    strategy._obligation_runtime_session = ObligationRuntimeSession.create(left, right)
    assert strategy._outcome_partition_covered_labels(
        _base_ctx(), left, right, _replace_param("p1"), _replace_param("p2")
    ) == {"function1", "function2"}


@pytest.mark.parametrize("proof_factory", [_valid_branch_structural_proof, _valid_branch_while_proof])
def test_branch_guarded_must_diverge_schemas_participate_in_validated_partition(proof_factory):
    strategy = _strategy()
    left = _analysis(return_guards=[[_nonpositive()]], divergence_guards=[[_positive()]])
    right = _analysis(return_guards=[[_nonpositive()]], divergence_guards=[[_positive()]])
    for analysis in (left, right):
        _attach_complete_return_path_evidence(analysis)
        analysis.divergence_outcomes = (DivergenceOutcome((_positive(),), proof_factory()),)
        _build_function_outcome_seed(analysis)
        analysis.outcome_seed = replace(
            analysis.outcome_seed,
            control_flow_evidence_key=_DivergenceProfile().stable_key(),
        )
        analysis.effect_summary = _EffectSummaryStub(_DivergenceProfile())
    strategy._obligation_runtime_session = ObligationRuntimeSession.create(left, right)
    assert strategy._outcome_partition_covered_labels(
        _base_ctx(), left, right, _replace_param("p1"), _replace_param("p2")
    ) == {"function1", "function2"}


def test_branch_guarded_must_diverge_rejects_stale_cfg_applicability_surface():
    strategy = _strategy()
    analyses = [
        _analysis(return_guards=[[_nonpositive()]], divergence_guards=[[_positive()]])
        for _ in range(2)
    ]
    for analysis in analyses:
        _attach_complete_return_path_evidence(analysis)
        proof = _valid_branch_while_proof()
        proof["cfg_applicability_surface"] = ((0, 9), ((0, 9), (9, 9)))
        analysis.divergence_outcomes = (DivergenceOutcome((_positive(),), proof),)
        _build_function_outcome_seed(analysis)
        analysis.outcome_seed = replace(
            analysis.outcome_seed,
            control_flow_evidence_key=_DivergenceProfile().stable_key(),
        )
        analysis.effect_summary = _EffectSummaryStub(_DivergenceProfile())
    left, right = analyses
    strategy._obligation_runtime_session = ObligationRuntimeSession.create(left, right)
    assert strategy._outcome_partition_covered_labels(
        _base_ctx(), left, right, _replace_param("p1"), _replace_param("p2")
    ) == set()


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


def test_outcome_partition_completion_reason_maps_to_specific_evidence():
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
        "function1:outcome_partition_completion_unproven",
        left,
        right,
        stage="unit",
    )

    assert record.reason_id == "outcome_partition_completion_unproven"
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


def test_analyzer_synthesizes_whileif_partition_from_phi_free_fallback_provenance():
    analyzer = ReturnAnalyzer(object())
    fixture = _branch_guarded_structural_phi_fixture()
    analyzer._make_tracer = lambda _high_function: _FakeStructuralTracer(fixture.trace_map)
    analysis = _branch_guarded_phi_free_fallback_analysis(analyzer, fixture.acc_phi)

    analyzer._apply_outcome_partition_summaries(
        None,
        fixture.high_function,
        analysis,
    )

    assert len(analysis.returns) == 2
    assert analysis.returns[0].value.equals(_const(0))
    assert analysis.returns[1].value.equals(_param2())
    assert len(analysis.return_outcomes) == 2
    assert len(analysis.divergence_outcomes) == 1
    assert analysis.unknown_outcomes == ()
    assert (
        analysis.divergence_outcomes[0].proof["proof_kind"]
        == "branch_guarded_structural_nonprogress_must_diverge"
    )
    assert analysis.returns[1].summary_candidate_source_key is not None


def test_analyzer_rejects_phi_free_fallback_with_state_countdown_only_provenance():
    analyzer = ReturnAnalyzer(object())
    fixture = _branch_guarded_structural_phi_fixture()
    analyzer._make_tracer = lambda _high_function: _FakeStructuralTracer(fixture.trace_map)
    analysis = _branch_guarded_phi_free_fallback_analysis(
        analyzer,
        fixture.state_phi,
        implicit_progress_anchor=True,
    )

    analyzer._apply_outcome_partition_summaries(
        None,
        fixture.high_function,
        analysis,
    )

    assert all(not ret.value.equals(_param2()) for ret in analysis.returns)
    assert analysis.return_outcomes == ()
    assert analysis.divergence_outcomes == ()


def test_analyzer_ignores_union_fallback_provenance_as_structural_origin():
    analyzer = ReturnAnalyzer(object())
    fixture = _branch_guarded_structural_phi_fixture()
    pcode_ref = PcodeOpRef.from_pcode_op(fixture.state_phi)
    ret = ReturnInfo(
        address="0x1008",
        value=_const(1),
        conditions=[_positive2(), _positive()],
        return_kind="phi_union_reachability_fallback",
        summary_candidate_source_key=(
            "phi_union_reachability_fallback",
            ("candidate_discovery_only_phi_origin_keys", (pcode_ref.stable_key(),)),
        ),
    )

    assert analyzer._return_info_candidate_phi_origin_keys(ret) == set()


def test_analyzer_accepts_acc_phi_flow_to_return_origin_exit_phi():
    analyzer = ReturnAnalyzer(object())
    fixture = _branch_guarded_structural_phi_fixture()
    acc_parent = fixture.acc_phi.getParent()
    cold_pred = _FakeBlock([], index=8, start=0x3080)
    return_out = _FakeVarnode("register", 0x7000, 4)
    return_phi = _FakeOp(
        "MULTIEQUAL",
        inputs=(_FakeVarnode("const", 0, 4, is_constant=True), fixture.acc_phi.getOutput()),
        output=return_out,
        opcode=27,
        target=0x3090,
        time=90,
        order=0,
    )
    exit_block = _FakeBlock([return_phi], index=9, start=0x3090)
    cold_pred.add_out(exit_block)
    acc_parent.add_out(exit_block)
    high_function = _FakeHighFunction(fixture.high_function.getBasicBlocks() + [cold_pred, exit_block])
    summarizer = StructuralRecurrenceSummarizer(_FakeStructuralTracer(fixture.trace_map), debug=False)

    assert analyzer._acc_phi_flows_to_return_origin_phi(
        fixture.acc_phi,
        {PcodeOpRef.from_pcode_op(return_phi).stable_key()},
        summarizer=summarizer,
        high_function=high_function,
    )


def test_analyzer_rejects_unrelated_acc_phi_not_flowing_to_return_origin():
    analyzer = ReturnAnalyzer(object())
    fixture = _branch_guarded_structural_phi_fixture()
    acc_parent = fixture.acc_phi.getParent()
    cold_pred = _FakeBlock([], index=8, start=0x3080)
    unrelated_out = _FakeVarnode("unique", 0x7100, 4)
    unrelated_acc = _FakeOp(
        "MULTIEQUAL",
        inputs=(_FakeVarnode("const", 0, 4, is_constant=True), unrelated_out),
        output=unrelated_out,
        opcode=27,
        target=0x3010,
        time=99,
        order=0,
    )
    unrelated_acc.setParent(acc_parent)
    return_out = _FakeVarnode("register", 0x7000, 4)
    return_phi = _FakeOp(
        "MULTIEQUAL",
        inputs=(_FakeVarnode("const", 0, 4, is_constant=True), fixture.acc_phi.getOutput()),
        output=return_out,
        opcode=27,
        target=0x3090,
        time=90,
        order=0,
    )
    exit_block = _FakeBlock([return_phi], index=9, start=0x3090)
    cold_pred.add_out(exit_block)
    acc_parent.add_out(exit_block)
    high_function = _FakeHighFunction(fixture.high_function.getBasicBlocks() + [cold_pred, exit_block])
    summarizer = StructuralRecurrenceSummarizer(_FakeStructuralTracer(fixture.trace_map), debug=False)

    assert not analyzer._acc_phi_flows_to_return_origin_phi(
        unrelated_acc,
        {PcodeOpRef.from_pcode_op(return_phi).stable_key()},
        summarizer=summarizer,
        high_function=high_function,
    )


def test_outcome_partition_equivalence_covers_phi_free_fallback_partitions():
    strategy = _strategy()
    analyzer = ReturnAnalyzer(object())
    fixture = _branch_guarded_structural_phi_fixture()
    analyzer._make_tracer = lambda _high_function: _FakeStructuralTracer(fixture.trace_map)
    left = _branch_guarded_phi_free_fallback_analysis(analyzer, fixture.acc_phi)
    right = _branch_guarded_phi_free_fallback_analysis(analyzer, fixture.acc_phi)
    analyzer._apply_outcome_partition_summaries(None, fixture.high_function, left)
    analyzer._apply_outcome_partition_summaries(None, fixture.high_function, right)
    base_ctx = {
        "header_lines": [
            "(declare-fun t1 () (_ BitVec 32))",
            "(declare-fun c1 () (_ BitVec 32))",
            "(declare-fun t2 () (_ BitVec 32))",
            "(declare-fun c2 () (_ BitVec 32))",
            "(assert (= t1 t2))",
            "(assert (= c1 c2))",
        ],
    }

    assert strategy._outcome_partition_covered_labels(
        base_ctx,
        left,
        right,
        _replace_params({"param_1": "t1", "param_2": "c1"}),
        _replace_params({"param_1": "t2", "param_2": "c2"}),
    ) == {"function1", "function2"}


def test_analyzer_rejects_phi_free_fallback_with_stale_origin_key():
    analyzer = ReturnAnalyzer(object())
    fixture = _branch_guarded_structural_phi_fixture()
    stale_phi = _FakeOp(
        "MULTIEQUAL",
        inputs=(),
        output=_FakeVarnode("unique", 0x7770, 4),
        opcode=27,
        target=0x7770,
        time=77,
        order=0,
    )
    analyzer._make_tracer = lambda _high_function: _FakeStructuralTracer(fixture.trace_map)
    analysis = _branch_guarded_phi_free_fallback_analysis(analyzer, stale_phi)

    analyzer._apply_outcome_partition_summaries(None, fixture.high_function, analysis)

    assert analysis.divergence_outcomes == ()
    assert analysis.unknown_outcomes == ()


def test_analyzer_rejects_phi_free_fallback_when_base_anchor_value_wrong():
    analyzer = ReturnAnalyzer(object())
    fixture = _branch_guarded_structural_phi_fixture()
    analyzer._make_tracer = lambda _high_function: _FakeStructuralTracer(fixture.trace_map)
    analysis = _branch_guarded_phi_free_fallback_analysis(analyzer, fixture.acc_phi, base_value=2)

    analyzer._apply_outcome_partition_summaries(None, fixture.high_function, analysis)

    assert analysis.divergence_outcomes == ()
    assert analysis.unknown_outcomes == ()


def test_analyzer_rejects_phi_free_fallback_when_base_anchor_guard_wrong():
    analyzer = ReturnAnalyzer(object())
    fixture = _branch_guarded_structural_phi_fixture()
    analyzer._make_tracer = lambda _high_function: _FakeStructuralTracer(fixture.trace_map)
    analysis = _branch_guarded_phi_free_fallback_analysis(
        analyzer,
        fixture.acc_phi,
        base_guard_matches=False,
    )

    analyzer._apply_outcome_partition_summaries(None, fixture.high_function, analysis)

    assert analysis.return_outcomes == ()
    assert analysis.divergence_outcomes == ()
    assert analysis.unknown_outcomes == ()


def test_analyzer_rejects_phi_free_fallback_when_state_decrement_missing():
    analyzer = ReturnAnalyzer(object())
    fixture = _branch_guarded_structural_phi_fixture(state_decrements=False)
    analyzer._make_tracer = lambda _high_function: _FakeStructuralTracer(fixture.trace_map)
    analysis = _branch_guarded_phi_free_fallback_analysis(analyzer, fixture.acc_phi)

    analyzer._apply_outcome_partition_summaries(None, fixture.high_function, analysis)

    assert analysis.return_outcomes == ()
    assert analysis.divergence_outcomes == ()


def test_analyzer_rejects_phi_free_fallback_when_nonprogress_edge_missing():
    analyzer = ReturnAnalyzer(object())
    fixture = _branch_guarded_structural_phi_fixture(include_nonprogress_edge=False)
    analyzer._make_tracer = lambda _high_function: _FakeStructuralTracer(fixture.trace_map)
    analysis = _branch_guarded_phi_free_fallback_analysis(analyzer, fixture.acc_phi)

    analyzer._apply_outcome_partition_summaries(None, fixture.high_function, analysis)

    assert analysis.divergence_outcomes == ()


def test_analyzer_rejects_phi_free_fallback_with_forbidden_effect_op():
    analyzer = ReturnAnalyzer(object())
    fixture = _branch_guarded_structural_phi_fixture(forbidden_op="STORE")
    analyzer._make_tracer = lambda _high_function: _FakeStructuralTracer(fixture.trace_map)
    analysis = _branch_guarded_phi_free_fallback_analysis(analyzer, fixture.acc_phi)

    analyzer._apply_outcome_partition_summaries(None, fixture.high_function, analysis)

    assert analysis.return_outcomes == ()
    assert analysis.divergence_outcomes == ()


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
