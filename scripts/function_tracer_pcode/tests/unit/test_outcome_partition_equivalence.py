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
    def __init__(self, mnemonic: str):
        self._mnemonic = mnemonic

    def getMnemonic(self):
        return self._mnemonic


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
    def __init__(self, ops):
        self._ops = list(ops)
        self._outs = []

    def add_out(self, block):
        self._outs.append(block)

    def getIterator(self):
        return _FakeIterator(self._ops)

    def getOutSize(self):
        return len(self._outs)

    def getOut(self, index):
        return self._outs[index]


class _FakeHighFunction:
    def __init__(self, blocks):
        self._blocks = list(blocks)

    def getBasicBlocks(self):
        return list(self._blocks)


def _cyclic_high_function(*mnemonics):
    first = _FakeBlock([_FakeOp(mnemonic) for mnemonic in mnemonics])
    second = _FakeBlock([])
    first.add_out(second)
    second.add_out(first)
    return _FakeHighFunction([first, second])


def _base_analysis(function_name: str, params, returns):
    return FunctionReturnAnalysis(
        function_name=function_name,
        entry_point="0x1000",
        parameters=params,
        returns=returns,
        return_type="int",
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
