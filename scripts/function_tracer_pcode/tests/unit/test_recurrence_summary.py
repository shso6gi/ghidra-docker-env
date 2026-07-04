# -*- coding: utf-8 -*-

from dataclasses import replace
from typing import Optional
from unittest.mock import Mock

from scripts.function_tracer_pcode.analysis.recurrence_summary import (
    CountedLoopAccumulator,
    CountedLoopGuard,
    CountedLoopInduction,
    CountedLoopUpdateCase,
    ReadonlyRoundedCountCandidate,
    ResidueLoopCase,
    StructuralRecurrenceSummarizer,
)
from scripts.function_tracer_pcode.analysis import ReturnAnalyzer
from scripts.function_tracer_pcode.analysis.condition import ConditionSimplifier
from scripts.function_tracer_pcode.analysis.summary_returns import (
    _summary_transition_evidence_key,
    _transition_evidence_has_required_parts,
)
from scripts.function_tracer_pcode.analysis.tracer import PcodeTracer
from scripts.function_tracer_pcode.analysis.effect_summary import (
    CanonicalLocation,
    EffectSummary,
    StoreEffect,
)
from scripts.function_tracer_pcode.model import (
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
from scripts.function_tracer_pcode.equivalence.formula.returns import expression_has_unresolved_value
from scripts.function_tracer_pcode.model.render_smt import expression_to_smt
from scripts.function_tracer_pcode.tests.conftest import create_mock_analysis


def _param(name: str = "param_1", size: int = 4) -> Expression:
    index = 0
    if name.startswith("param_"):
        try:
            index = max(0, int(name.split("_", 1)[1]) - 1)
        except ValueError:
            index = 0
    return Expression.parameter(name, index=index, data_type="int", size=size)


def test_condition_implication_keeps_named_parameters_with_placeholder_indices_distinct():
    param_2_placeholder = Expression.parameter("param_2", index=0, data_type="int", size=4)
    param_3_placeholder = Expression.parameter("param_3", index=0, data_type="int", size=4)
    less_condition = _cond("INT_SLESS", param_2_placeholder, param_3_placeholder)
    parity_condition = _cond(
        "INT_EQUAL",
        Expression.binary_op("INT_AND", param_2_placeholder, _const(1)),
        _const(0),
    )

    assert ConditionSimplifier._condition_is_implied(
        parity_condition,
        [less_condition],
        prefer_solver=True,
    ) is False
    assert [condition.to_string() for condition in ConditionSimplifier.simplify_conditions_object_centric(
        [less_condition, parity_condition]
    )] == ["(param_2 < param_3)", "((param_2 & 1) == 0)"]


def test_return_region_summary_coverage_proves_positive_and_nonpositive_partition():
    summarizer = StructuralRecurrenceSummarizer(tracer=None, debug=False)
    n = _param()
    exact_nonpositive = ReturnInfo(
        address="0x1000",
        value=_const(1),
        conditions=[_cond("INT_SLESS", n, _const(1))],
    )

    coverage_key = summarizer._prove_summary_conditions_plus_exact_returns_cover_active_precondition(
        summary_conditions=[_cond("INT_SLESSEQUAL", _const(1), n)],
        exact_returns=[exact_nonpositive],
    )

    assert coverage_key is not None


def test_return_region_summary_coverage_rejects_positive_guard_with_one_gap():
    summarizer = StructuralRecurrenceSummarizer(tracer=None, debug=False)
    n = _param()
    exact_nonpositive = ReturnInfo(
        address="0x1000",
        value=_const(1),
        conditions=[_cond("INT_SLESS", n, _const(1))],
    )

    coverage_key = summarizer._prove_summary_conditions_plus_exact_returns_cover_active_precondition(
        summary_conditions=[_cond("INT_SLESS", _const(1), n)],
        exact_returns=[exact_nonpositive],
    )

    assert coverage_key is None


def test_return_region_summary_coverage_uses_active_preconditions():
    summarizer = StructuralRecurrenceSummarizer(tracer=None, debug=False)
    n = _param()
    exact_nonpositive = ReturnInfo(
        address="0x1000",
        value=_const(1),
        conditions=[_cond("INT_SLESS", n, _const(1))],
    )

    coverage_key = summarizer._prove_summary_conditions_plus_exact_returns_cover_active_precondition(
        active_preconditions=[_cond("INT_NOTEQUAL", n, _const(1))],
        summary_conditions=[_cond("INT_SLESS", _const(1), n)],
        exact_returns=[exact_nonpositive],
    )

    assert coverage_key is not None


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


def test_accepted_return_partition_view_does_not_mutate_seed_analysis():
    seed_return = ReturnInfo(address="0x1000", value=_const(0), conditions=[])
    accepted_return = ReturnInfo(
        address="0x1010",
        value=_const(1),
        conditions=[_cond("INT_SLESS", _const(0), _param())],
        return_kind="summary_derived",
    )
    seed = FunctionReturnAnalysis(
        function_name="pure_loop",
        entry_point="0x1000",
        parameters=[{"name": "param_1", "index": 0, "type": "int", "size": 4}],
        returns=[seed_return],
        analysis_scope_key=("function", "pure_loop"),
        return_type="int",
    )
    seed.analysis_notes.append("seed_note")

    view = seed.with_accepted_return_partition(
        [seed_return, accepted_return],
        reason="pure_return_coverage_completion",
    )
    other_view = seed.with_accepted_return_partition(
        [
            seed_return,
            ReturnInfo(
                address="0x1010",
                value=_const(2),
                conditions=[_cond("INT_SLESS", _const(0), _param())],
                return_kind="summary_derived",
            ),
        ],
        reason="pure_return_coverage_completion",
    )
    view.analysis_notes.append("view_note")

    assert seed.returns == [seed_return]
    assert "view_note" not in seed.analysis_notes
    assert view.returns == [seed_return, accepted_return]
    assert view.partition_revision == seed.partition_revision + 1
    assert view.analysis_view_identity is not None
    assert view.analysis_view_identity[0] == "accepted_return_partition_view"
    assert other_view.analysis_view_identity != view.analysis_view_identity
    assert view.to_dict()["analysis_view_identity"][0] == "accepted_return_partition_view"
    assert view.to_dict()["partition_revision"] == view.partition_revision


def test_phase1_high_function_visible_scan_allows_integer_no_effect_body():
    analyzer = ReturnAnalyzer.__new__(ReturnAnalyzer)
    high_function = _Phase1FakeHighFunction([
        ["COPY", "INT_ADD", "INT_SLESS", "CBRANCH"],
        ["MULTIEQUAL", "INT_MULT", "RETURN"],
    ])

    assert analyzer._high_function_has_phase1_pure_return_forbidden_ops(high_function) is False


def test_phase1_high_function_visible_scan_rejects_memory_call_control_and_fp_ops():
    analyzer = ReturnAnalyzer.__new__(ReturnAnalyzer)

    for mnemonic in (
        "LOAD",
        "STORE",
        "CALL",
        "CALLIND",
        "BRANCHIND",
        "CALLOTHER",
        "FLOAT_ADD",
        "FLOAT_LESSEQUAL",
        "INT2FLOAT",
        "FLOAT2INT",
    ):
        high_function = _Phase1FakeHighFunction([["COPY", mnemonic, "RETURN"]])
        assert analyzer._high_function_has_phase1_pure_return_forbidden_ops(high_function) is True


def test_phase1_function_body_scan_rejects_forbidden_ops_not_seen_in_high_function():
    analyzer = ReturnAnalyzer.__new__(ReturnAnalyzer)
    analyzer.debug = False
    analyzer.program = _Phase1FakeProgram([
        _Phase1FakeInstruction(["COPY", "INT_ADD"]),
        _Phase1FakeInstruction(["LOAD", "RETURN"]),
    ])
    function = _Phase1FakeFunction()
    high_function = _Phase1FakeHighFunction([["COPY", "INT_ADD", "RETURN"]])
    effect_summary = EffectSummary(parameter_names=[], effects=[])

    assert analyzer._function_body_has_phase1_pure_return_forbidden_ops(function) is True
    assert analyzer._effect_summary_allows_pre_return_structural_summary(
        effect_summary,
        function=function,
        high_function=high_function,
    ) is False


def test_phase1_function_body_scan_still_rejects_forbidden_high_function_ops():
    analyzer = ReturnAnalyzer.__new__(ReturnAnalyzer)
    analyzer.debug = False
    analyzer.program = _Phase1FakeProgram([
        _Phase1FakeInstruction(["COPY", "INT_ADD", "CBRANCH"]),
        _Phase1FakeInstruction(["MULTIEQUAL", "INT_MULT", "RETURN"]),
    ])
    function = _Phase1FakeFunction()
    high_function = _Phase1FakeHighFunction([["LOAD"]])
    effect_summary = EffectSummary(parameter_names=[], effects=[])

    assert analyzer._function_body_has_phase1_pure_return_forbidden_ops(function) is False
    assert analyzer._effect_summary_allows_pre_return_structural_summary(
        effect_summary,
        function=function,
        high_function=high_function,
    ) is False


def test_phase1_function_body_and_high_function_scan_allow_integer_no_effect_body():
    analyzer = ReturnAnalyzer.__new__(ReturnAnalyzer)
    analyzer.debug = False
    analyzer.program = _Phase1FakeProgram([
        _Phase1FakeInstruction(["COPY", "INT_ADD", "CBRANCH"]),
        _Phase1FakeInstruction(["MULTIEQUAL", "INT_MULT", "RETURN"]),
    ])
    function = _Phase1FakeFunction()
    high_function = _Phase1FakeHighFunction([["COPY", "INT_ADD", "RETURN"]])
    effect_summary = EffectSummary(parameter_names=[], effects=[])

    assert analyzer._function_body_has_phase1_pure_return_forbidden_ops(function) is False
    assert analyzer._high_function_has_phase1_pure_return_forbidden_ops(high_function) is False
    assert analyzer._effect_summary_allows_pre_return_structural_summary(
        effect_summary,
        function=function,
        high_function=high_function,
    ) is True


def test_phase1_function_body_scan_failure_is_conservative():
    analyzer = ReturnAnalyzer.__new__(ReturnAnalyzer)
    analyzer.debug = False
    analyzer.program = Mock()
    analyzer.program.getListing.side_effect = RuntimeError("listing unavailable")

    assert analyzer._function_body_has_phase1_pure_return_forbidden_ops(_Phase1FakeFunction()) is True


def test_phase1_function_body_pcode_iterator_failure_after_safe_op_is_conservative():
    analyzer = ReturnAnalyzer.__new__(ReturnAnalyzer)
    analyzer.debug = False
    analyzer.program = _Phase1FakeProgram([_Phase1BrokenInstruction()])

    assert analyzer._function_body_has_phase1_pure_return_forbidden_ops(_Phase1FakeFunction()) is True


def test_phase1_function_body_scan_rejects_direct_branch_outside_body():
    analyzer = ReturnAnalyzer.__new__(ReturnAnalyzer)
    analyzer.debug = False
    analyzer.program = _Phase1FakeProgram([
        _Phase1FakeInstruction(["COPY", "BRANCH"], flows=[_Phase1FakeAddress(0x2000)]),
    ])

    assert analyzer._function_body_has_phase1_pure_return_forbidden_ops(_Phase1FakeFunction()) is True


def test_phase1_function_body_scan_allows_direct_branch_inside_body():
    analyzer = ReturnAnalyzer.__new__(ReturnAnalyzer)
    analyzer.debug = False
    analyzer.program = _Phase1FakeProgram([
        _Phase1FakeInstruction(["COPY", "BRANCH"], flows=[_Phase1FakeAddress(0x1010)]),
        _Phase1FakeInstruction(["RETURN"]),
    ])

    assert analyzer._function_body_has_phase1_pure_return_forbidden_ops(_Phase1FakeFunction()) is False


def test_phase1_pre_return_effect_gate_rejects_impure_high_function():
    analyzer = ReturnAnalyzer.__new__(ReturnAnalyzer)
    analyzer.debug = False
    high_function = _Phase1FakeHighFunction([["COPY", "LOAD", "RETURN"]])
    effect_summary = EffectSummary(parameter_names=[], effects=[])

    assert analyzer._effect_summary_allows_pre_return_structural_summary(
        effect_summary,
        high_function=high_function,
    ) is False


def test_phase1_pre_return_effect_gate_rejects_float_return_type():
    analyzer = ReturnAnalyzer.__new__(ReturnAnalyzer)
    analyzer.debug = False
    high_function = _Phase1FakeHighFunction([["COPY", "INT_ADD", "RETURN"]])
    effect_summary = EffectSummary(parameter_names=[], effects=[])

    assert analyzer._effect_summary_allows_pre_return_structural_summary(
        effect_summary,
        high_function=high_function,
        return_type="double",
    ) is False


def test_state_transition_runtime_ref_supplies_summary_transition_evidence():
    state = Expression.variable("__loop_state", size=4)
    transition = Expression.binary_op("INT_SUB", state, _const(1))
    transition.size = 4
    accumulator_init = _const(0)
    accumulator_delta = _const(1)
    runtime_ref = StateTransitionLoopSummaryRef(
        state_guard=Expression.binary_op("INT_SLESS", _const(0), state),
        transition_expr=transition,
        accumulator_init=accumulator_init,
        accumulator_delta=accumulator_delta,
        transition_cases=(((), transition),),
        side_effect_profile=LoopSideEffectProfileRef(),
        state_size=4,
        result_size=4,
    )
    value = Expression.intrinsic(
        "STATE_TRANSITION_LOOP_COUNT",
        [state],
        size=4,
        runtime_ref=runtime_ref,
        opcode=STATE_TRANSITION_LOOP_COUNT_OPCODE,
    )
    ret = ReturnInfo(
        address="0x2000",
        value=value,
        conditions=[_cond("INT_SLESS", _const(0), _param())],
        return_kind="summary_derived",
    )
    analysis = FunctionReturnAnalysis(
        function_name="state_loop",
        entry_point="0x1000",
        parameters=[{"name": "param_1", "index": 0, "type": "int", "size": 4}],
        returns=[ReturnInfo(address="0x1000", value=_const(0), conditions=[])],
        return_type="int",
    )

    evidence = _summary_transition_evidence_key(ret)

    assert evidence is not None
    assert evidence[0] == "state_transition_loop_evidence"
    assert _transition_evidence_has_required_parts(
        evidence,
        analysis,
        enable_completed_recovery_proofs=True,
    )


def test_state_transition_evidence_allows_uniform_transition_cases():
    state = Expression.variable("__loop_state", size=4)
    transition = Expression.binary_op("INT_SUB", state, _const(1))
    transition.size = 4
    runtime_ref = StateTransitionLoopSummaryRef(
        state_guard=Expression.binary_op("INT_SLESS", _const(0), state),
        transition_expr=transition,
        accumulator_init=_const(0),
        accumulator_delta=_const(1),
        transition_cases=(),
        side_effect_profile=LoopSideEffectProfileRef(),
        state_size=4,
        result_size=4,
    )
    summarizer = StructuralRecurrenceSummarizer(PcodeTracer.__new__(PcodeTracer), debug=False)

    evidence = summarizer._state_transition_loop_transition_evidence_key(runtime_ref)

    assert evidence is not None
    assert (
        "transition_cases_key",
        ("transition_cases", "uniform_transition_expr", ("expression", transition.structural_key())),
    ) in evidence


def test_counted_loop_affine_case_preserves_parameter_bias_expression():
    summarizer = StructuralRecurrenceSummarizer(PcodeTracer.__new__(PcodeTracer), debug=False)
    counter = _param("__loop_iv")
    bias = _param("param_2")
    scaled = Expression.binary_op("INT_MULT", Expression.constant(5, size=4), counter)
    scaled.size = 4
    delta = Expression.binary_op("INT_ADD", scaled, bias)
    delta.size = 4

    affine_case = summarizer._extract_affine_loop_case(delta, "__loop_iv")

    assert affine_case is not None
    affine, bias_expr = affine_case
    assert affine == (5, 0)
    assert bias_expr is not None
    assert bias_expr.structural_key() == bias.structural_key()


def test_counted_loop_affine_case_rejects_loop_carried_variable_bias_expression():
    summarizer = StructuralRecurrenceSummarizer(PcodeTracer.__new__(PcodeTracer), debug=False)
    counter = _param("__loop_iv")
    loop_carried = Expression.variable("__other_loop_state", size=4)
    scaled = Expression.binary_op("INT_MULT", Expression.constant(5, size=4), counter)
    scaled.size = 4
    delta = Expression.binary_op("INT_ADD", scaled, loop_carried)
    delta.size = 4

    affine_case = summarizer._extract_affine_loop_case(delta, "__loop_iv")

    assert affine_case is None


def test_readonly_parameter_helpers_preserve_storage_backed_identity_without_fabricated_index():
    storage = StorageInfo(
        is_register=True,
        space_name="register",
        register_name="a1",
        base_register_name="a1",
        size=4,
        size_bits=32,
    )
    summarizer = StructuralRecurrenceSummarizer(PcodeTracer.__new__(PcodeTracer), debug=False)
    param = {
        "name": "renamed_count",
        "size": 4,
        "data_type": "int",
        "storage_info": storage,
    }

    expr = summarizer._parameter_expression(param)
    base_ref = summarizer._location_base_ref_from_parameter(param, default_name="count")

    assert expr.value == -1
    assert expr.storage_info is storage
    assert summarizer._parameter_storage_identity_key(param) == storage.storage_identity_key()
    assert base_ref.is_storage()
    assert base_ref.semantic_key() == ("storage_identity", storage.storage_identity_key())


def test_vector_zero_base_coverage_normalizes_counter_parameter_identity():
    summarizer = StructuralRecurrenceSummarizer(PcodeTracer.__new__(PcodeTracer), debug=False)
    counter_param = {
        "name": "renamed_count",
        "index": 0,
        "size": 4,
        "data_type": "int",
    }
    primary_counter = summarizer._parameter_expression(counter_param)
    return_counter = Expression.parameter("param_1", index=0, data_type="int", size=4)
    positive_guard = _cond("INT_SLESS", _const(0), primary_counter)
    zero_case = ReturnInfo(
        address="00100000",
        value=_const(0),
        conditions=[_cond("INT_SLESS", return_counter, _const(1))],
    )
    positive_case = ReturnInfo(
        address="00100004",
        value=_const(1),
        conditions=[_cond("INT_SLESS", _const(0), return_counter)],
    )
    analysis = type("Analysis", (), {"returns": [zero_case, positive_case]})()

    base_guard = summarizer._zero_base_guard_cover_for_positive_counter_guard(
        analysis,
        counter_param,
        primary_counter,
        positive_guard,
    )

    assert base_guard is not None
    assert summarizer._nonzero_returns_are_disjoint_from_base_guard(
        analysis,
        base_guard,
        counter_param,
        primary_counter,
    )


def test_counter_parameter_normalization_rejects_same_name_different_index():
    summarizer = StructuralRecurrenceSummarizer(PcodeTracer.__new__(PcodeTracer), debug=False)
    primary_counter = Expression.parameter("param_1", index=0, data_type="int", size=4)
    same_name_other_index = Expression.parameter("param_1", index=1, data_type="int", size=4)
    expr = Expression.binary_op("INT_SLESS", same_name_other_index, _const(1))

    normalized = summarizer._normalize_counter_parameter_expression(
        expr,
        {"name": "param_1", "index": 0, "size": 4, "data_type": "int"},
        primary_counter,
    )

    assert normalized is expr
    assert normalized.operands[0] is same_name_other_index


def test_counter_parameter_candidate_selection_rejects_name_only_parameter():
    summarizer = StructuralRecurrenceSummarizer(PcodeTracer.__new__(PcodeTracer), debug=False)
    name_only_param = {"name": "count", "size": 4, "data_type": "int"}
    return_counter = Expression.parameter("count", index=-1, data_type="int", size=4)
    analysis = type(
        "Analysis",
        (),
        {
            "returns": [
                ReturnInfo(
                    address="00100000",
                    value=_const(1),
                    conditions=[_cond("INT_SLESS", _const(0), return_counter)],
                )
            ]
        },
    )()

    assert summarizer._vectorized_affine_counter_expression(name_only_param, analysis) is None


def test_same_counter_expression_rejects_name_only_parameter_alias():
    summarizer = StructuralRecurrenceSummarizer(PcodeTracer.__new__(PcodeTracer), debug=False)
    left = Expression.parameter("count", index=-1, data_type="int", size=4)
    right = Expression.parameter("count", index=-1, data_type="int", size=4)

    assert not summarizer._same_counter_expression(left, right)


def test_counter_guard_signedness_ignores_name_only_parameter_alias():
    summarizer = StructuralRecurrenceSummarizer(PcodeTracer.__new__(PcodeTracer), debug=False)
    name_only_param = {"name": "count", "size": 4, "data_type": "int"}
    return_counter = Expression.parameter("count", index=-1, data_type="int", size=4)
    analysis = type(
        "Analysis",
        (),
        {
            "returns": [
                ReturnInfo(
                    address="00100000",
                    value=_const(1),
                    conditions=[_cond("INT_SLESS", _const(0), return_counter)],
                )
            ]
        },
    )()

    assert summarizer._vectorized_affine_counter_guard_signedness(analysis, name_only_param) is None


def test_counter_parameter_normalization_requires_storage_match_when_present():
    storage_a = StorageInfo(
        is_register=True,
        space_name="register",
        register_name="w0",
        base_register_name="x0",
        size=4,
        size_bits=32,
    )
    storage_b = StorageInfo(
        is_register=True,
        space_name="register",
        register_name="w1",
        base_register_name="x1",
        size=4,
        size_bits=32,
    )
    summarizer = StructuralRecurrenceSummarizer(PcodeTracer.__new__(PcodeTracer), debug=False)
    primary_counter = Expression.parameter("param_1", index=-1, data_type="int", size=4, storage_info=storage_a)
    same_name_other_storage = Expression.parameter("param_1", index=-1, data_type="int", size=4, storage_info=storage_b)
    expr = Expression.binary_op("INT_SLESS", same_name_other_storage, _const(1))

    normalized = summarizer._normalize_counter_parameter_expression(
        expr,
        {"name": "param_1", "size": 4, "data_type": "int", "storage_info": storage_a},
        primary_counter,
    )

    assert normalized is expr
    assert normalized.operands[0] is same_name_other_storage


def test_counter_parameter_normalization_allows_same_register_slot_storage_variant():
    storage_descriptor = StorageInfo(
        is_register=True,
        space_name="register",
        space_id=0,
        offset=0x4000,
        register_offset=0x4000,
        register_name="w0",
        base_register_name="x0",
        base_register_offset=0x3D98,
        base_register_size=8,
        base_register_size_bits=64,
        size=4,
        size_bits=32,
        bit_offset_in_base=0,
    )
    storage_runtime = StorageInfo(
        is_register=True,
        space_name="register",
        space_id=548,
        offset=0x4000,
        register_offset=0x4000,
        register_name="w0",
        base_register_name="x0",
        base_register_offset=0x4000,
        base_register_size=8,
        base_register_size_bits=64,
        size=4,
        size_bits=32,
        bit_offset_in_base=0,
    )
    summarizer = StructuralRecurrenceSummarizer(PcodeTracer.__new__(PcodeTracer), debug=False)
    primary_counter = Expression.parameter("param_1", index=0, data_type="int", size=4, storage_info=storage_descriptor)
    runtime_counter = Expression.parameter("param_1", index=0, data_type="int", size=4, storage_info=storage_runtime)
    expr = Expression.binary_op("INT_SLESS", runtime_counter, _const(1))

    normalized = summarizer._normalize_counter_parameter_expression(
        expr,
        {"name": "param_1", "index": 0, "size": 4, "data_type": "int", "storage_info": storage_descriptor},
        primary_counter,
    )

    assert normalized is not expr
    assert normalized.operands[0] is primary_counter


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


def test_counted_loop_update_validation_query_uses_object_identity_aux_symbols():
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
    assert "(declare-const aux_sym_0 (_ BitVec 32))" in query
    assert "(declare-const aux_sym_1 (_ BitVec 32))" in query
    assert "aux_sym_0" in query
    assert "aux_sym_1" in query
    assert " __loop_iv)" not in query
    assert " __loop_acc)" not in query


def test_summary_auxiliary_symbols_are_reassigned_after_descriptor_merge():
    summarizer = StructuralRecurrenceSummarizer(PcodeTracer.__new__(PcodeTracer), debug=False)

    assigned = summarizer._assign_summary_auxiliary_symbols(
        [
            {
                "identity": ("synthetic_parameter_index", -10000),
                "size": 4,
                "aux_name": "aux_sym_0",
            },
            {
                "identity": ("parameter_index", 0),
                "size": 4,
            },
        ]
    )

    names = [spec["aux_name"] for spec in assigned]
    assert names == ["aux_sym_0", "aux_sym_1"]
    assert len(names) == len(set(names))


def test_try_summarize_prefers_vector_affine_before_counted_scalar(monkeypatch):
    summarizer = StructuralRecurrenceSummarizer(PcodeTracer.__new__(PcodeTracer), debug=False)
    calls = []

    monkeypatch.setattr(
        summarizer,
        "_try_summarize_linear_self_recursion",
        lambda *_args: None,
    )
    monkeypatch.setattr(
        summarizer,
        "_try_summarize_readonly_pointer_reduction",
        lambda *_args: None,
    )

    def vector_summary(*_args):
        calls.append("vector")
        return ([], "vectorized_affine_progression_sum_summary")

    def scalar_summary(*_args):
        calls.append("scalar")
        return ([], "counted_scalar_loop_summary")

    monkeypatch.setattr(summarizer, "_try_summarize_vectorized_affine_progression_sum", vector_summary)
    monkeypatch.setattr(summarizer, "_try_summarize_counted_scalar_loop", scalar_summary)

    analysis = type("Analysis", (), {"parameters": [{"name": "param_1"}]})()
    summary = summarizer.try_summarize_function(object(), object(), analysis)

    assert summary == ([], "vectorized_affine_progression_sum_summary")
    assert calls == ["vector"]


def test_counted_scalar_declines_residue_readonly_vector_literal_address(monkeypatch):
    summarizer = StructuralRecurrenceSummarizer(PcodeTracer.__new__(PcodeTracer), debug=False)

    monkeypatch.setattr(summarizer, "_address_points_to_readonly_data", lambda value: value == 0x100278)

    def fake_lanes(value, lane_count):
        if value == 0x100278 and lane_count == 4:
            return (1, 2, 3, 4)
        return None

    monkeypatch.setattr(summarizer, "_read_readonly_int32_lanes", fake_lanes)

    assert summarizer._residue_cases_contain_readonly_affine_literal_address(
        (
            ResidueLoopCase(
                modulus=1,
                residue=0,
                affine=(0, 0x100278),
                affine_from_readonly_literal=True,
            ),
        )
    )
    assert not summarizer._residue_cases_contain_readonly_affine_literal_address(
        (ResidueLoopCase(modulus=1, residue=0, affine=(1, 0)),)
    )


def test_counted_scalar_keeps_plain_affine_coefficient_equal_to_readonly_address(monkeypatch):
    summarizer = StructuralRecurrenceSummarizer(PcodeTracer.__new__(PcodeTracer), debug=False)

    monkeypatch.setattr(summarizer, "_address_points_to_readonly_data", lambda value: value == 0x100278)

    def fake_lanes(value, lane_count):
        if value == 0x100278 and lane_count == 4:
            return (1, 2, 3, 4)
        return None

    monkeypatch.setattr(summarizer, "_read_readonly_int32_lanes", fake_lanes)

    assert not summarizer._residue_cases_contain_readonly_affine_literal_address(
        (
            ResidueLoopCase(
                modulus=1,
                residue=0,
                affine=(0x100278, 0),
                affine_from_readonly_literal=False,
            ),
        )
    )


def test_counted_scalar_declines_plain_affine_bias_equal_to_readonly_progression(monkeypatch):
    summarizer = StructuralRecurrenceSummarizer(PcodeTracer.__new__(PcodeTracer), debug=False)

    def fake_lanes(value, lane_count):
        if value == 0x100278 and lane_count == 4:
            return (1, 2, 3, 4)
        return None

    monkeypatch.setattr(summarizer, "_read_readonly_int32_lanes", fake_lanes)

    assert summarizer._residue_cases_contain_readonly_affine_literal_address(
        (
            ResidueLoopCase(
                modulus=1,
                residue=0,
                affine=(0, 0x100278),
                affine_from_readonly_literal=False,
            ),
        )
    )


def test_counted_scalar_keeps_plain_affine_bias_equal_to_executable_address_without_provenance(monkeypatch):
    summarizer = StructuralRecurrenceSummarizer(PcodeTracer.__new__(PcodeTracer), debug=False)

    monkeypatch.setattr(summarizer, "_constant_resolves_to_executable_address", lambda value: value == 0x100278)

    assert not summarizer._residue_cases_contain_readonly_affine_literal_address(
        (
            ResidueLoopCase(
                modulus=1,
                residue=0,
                affine=(1, 0x100278),
                affine_from_readonly_literal=False,
                affine_from_address_literal=False,
            ),
        )
    )


def test_counted_scalar_declines_address_like_constant_iteration_bias_without_context(monkeypatch):
    summarizer = StructuralRecurrenceSummarizer(PcodeTracer.__new__(PcodeTracer), debug=False)

    monkeypatch.setattr(summarizer, "_constant_resolves_to_executable_address", lambda value: value == 0x100278)

    assert summarizer._residue_cases_contain_readonly_affine_literal_address(
        (
            ResidueLoopCase(
                modulus=1,
                residue=0,
                affine=(0, 0x100278),
                affine_from_readonly_literal=False,
                affine_from_address_literal=False,
            ),
        )
    )


def test_counted_scalar_declines_affine_bias_with_address_literal_provenance(monkeypatch):
    summarizer = StructuralRecurrenceSummarizer(PcodeTracer.__new__(PcodeTracer), debug=False)

    monkeypatch.setattr(summarizer, "_constant_resolves_to_executable_address", lambda value: value == 0x100278)

    assert summarizer._residue_cases_contain_readonly_affine_literal_address(
        (
            ResidueLoopCase(
                modulus=1,
                residue=0,
                affine=(0, 0x100278),
                affine_from_readonly_literal=False,
                affine_from_address_literal=True,
            ),
        )
    )


def test_extract_residue_case_marks_address_literal_access_provenance(monkeypatch):
    summarizer = StructuralRecurrenceSummarizer(PcodeTracer.__new__(PcodeTracer), debug=False)
    counter = _param("__loop_iv")
    address_lane = Expression.binary_op("SUBPIECE", Expression.constant(0x100278, size=8), _const(0))
    delta = Expression.binary_op("INT_ADD", counter, address_lane)

    monkeypatch.setattr(summarizer, "_constant_resolves_to_executable_address", lambda value: value == 0x100278)
    residue_cases = summarizer._extract_residue_loop_cases(
        (CountedLoopUpdateCase(conditions=(), update_expr=delta, delta_expr=delta),),
        "__loop_iv",
    )

    assert residue_cases is not None
    assert residue_cases[0].affine_from_address_literal is True
    assert summarizer._residue_cases_contain_readonly_affine_literal_address(residue_cases)


def test_extract_residue_case_does_not_mark_plain_function_body_immediate_as_address_literal_provenance():
    summarizer = StructuralRecurrenceSummarizer(PcodeTracer.__new__(PcodeTracer), debug=False)
    counter = _param("__loop_iv")
    delta = Expression.binary_op("INT_ADD", counter, Expression.constant(0x100278, size=4))

    residue_cases = summarizer._extract_residue_loop_cases(
        (CountedLoopUpdateCase(conditions=(), update_expr=delta, delta_expr=delta),),
        "__loop_iv",
        function_body_ranges=((0x100000, 0x100300),),
    )

    assert residue_cases is not None
    assert residue_cases[0].affine == (1, 0x100278)
    assert residue_cases[0].affine_from_address_literal is False
    assert not summarizer._residue_cases_contain_readonly_affine_literal_address(residue_cases)


def test_extract_residue_case_marks_function_body_address_literal_provenance_in_subpiece_context():
    summarizer = StructuralRecurrenceSummarizer(PcodeTracer.__new__(PcodeTracer), debug=False)
    counter = _param("__loop_iv")
    address_lane = Expression.binary_op("SUBPIECE", Expression.constant(0x100278, size=8), _const(0))
    delta = Expression.binary_op("INT_ADD", counter, address_lane)

    residue_cases = summarizer._extract_residue_loop_cases(
        (CountedLoopUpdateCase(conditions=(), update_expr=delta, delta_expr=delta),),
        "__loop_iv",
        function_body_ranges=((0x100000, 0x100300),),
    )

    assert residue_cases is not None
    assert residue_cases[0].affine_from_address_literal is True
    assert summarizer._residue_cases_contain_readonly_affine_literal_address(residue_cases)


def test_extract_residue_case_marks_readonly_literal_access_provenance(monkeypatch):
    summarizer = StructuralRecurrenceSummarizer(PcodeTracer.__new__(PcodeTracer), debug=False)
    counter = _param("__loop_iv")
    readonly_addr = Expression.constant(0x100278, size=8)
    low_lane = Expression.binary_op("SUBPIECE", readonly_addr, _const(0))
    delta = Expression.binary_op("INT_ADD", counter, low_lane)

    monkeypatch.setattr(summarizer, "_address_points_to_readonly_data", lambda value: value == 0x100278)
    residue_cases = summarizer._extract_residue_loop_cases(
        (CountedLoopUpdateCase(conditions=(), update_expr=delta, delta_expr=delta),),
        "__loop_iv",
    )

    assert residue_cases is not None
    assert residue_cases[0].affine_from_readonly_literal is True


def test_counted_scalar_declines_extracted_bias_readonly_literal_access(monkeypatch):
    summarizer = StructuralRecurrenceSummarizer(PcodeTracer.__new__(PcodeTracer), debug=False)
    counter = _param("__loop_iv")
    readonly_addr = Expression.constant(0x100278, size=8)
    low_lane = Expression.binary_op("SUBPIECE", readonly_addr, _const(0))
    delta = Expression.binary_op("INT_ADD", counter, low_lane)

    monkeypatch.setattr(summarizer, "_address_points_to_readonly_data", lambda value: value == 0x100278)
    residue_cases = summarizer._extract_residue_loop_cases(
        (CountedLoopUpdateCase(conditions=(), update_expr=delta, delta_expr=delta),),
        "__loop_iv",
    )

    assert residue_cases is not None
    assert residue_cases[0].affine == (1, 0)
    assert residue_cases[0].bias_expr is not None
    assert summarizer._residue_cases_contain_readonly_affine_literal_address(residue_cases)


def test_summary_expression_equivalence_query_refuses_name_only_parameter_symbol():
    summarizer = StructuralRecurrenceSummarizer(PcodeTracer.__new__(PcodeTracer), debug=False)
    name_only = Expression.parameter("count", data_type="int", size=4)

    query = summarizer._build_expression_equivalence_query(
        name_only,
        name_only,
        [],
        [{"name": "count", "size": 4, "data_type": "int"}],
    )

    assert query is None


def test_summary_expression_equivalence_query_does_not_alias_duplicate_variable_names():
    summarizer = StructuralRecurrenceSummarizer(PcodeTracer.__new__(PcodeTracer), debug=False)
    left = Expression.variable("tmp", size=4)
    right = Expression.variable("tmp", size=4)

    query = summarizer._build_expression_equivalence_query(left, right, [], [])

    assert query is not None
    assert "(declare-const aux_sym_0 (_ BitVec 32))" in query
    assert "(declare-const aux_sym_1 (_ BitVec 32))" in query
    assert "(assert (not (= aux_sym_0 aux_sym_1)))" in query or "(assert (not (= aux_sym_1 aux_sym_0)))" in query
    assert "tmp_aux" not in query


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


def test_expression_equivalence_query_declares_memory_arrays_for_readonly_witness_proof():
    summarizer = StructuralRecurrenceSummarizer(PcodeTracer.__new__(PcodeTracer), debug=False)
    left = Expression.binary_op("INT_ADD", _mem("param_1", 0), _mem("param_1", 4))
    right = Expression.binary_op("INT_ADD", _mem("param_1", 4), _mem("param_1", 0))

    query = summarizer._build_expression_equivalence_query(
        left,
        right,
        [],
        [{"name": "param_1", "index": 0, "size": 8, "data_type": "int *"}],
    )

    assert query is not None
    assert "(set-logic QF_AUFBV)" in query
    assert "(declare-const mem32 (Array (_ BitVec 64) (_ BitVec 32)))" in query


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


def test_same_high_variable_rejects_name_only_alias():
    summarizer = StructuralRecurrenceSummarizer(_IdentityTracer(), debug=False)
    left = _FakeVarnode("left", high=_FakeHighVar("loop_state"))
    right = _FakeVarnode("right", high=_FakeHighVar("loop_state"))

    assert summarizer._same_high_variable(left, right) is False


def test_same_high_variable_accepts_shared_symbol_object():
    summarizer = StructuralRecurrenceSummarizer(_IdentityTracer(), debug=False)
    symbol = _FakeHighSymbol(category_index=1)
    left = _FakeVarnode("left", high=_FakeHighVar("left_state", symbol=symbol))
    right = _FakeVarnode("right", high=_FakeHighVar("right_state", symbol=symbol))

    assert summarizer._same_high_variable(left, right) is True


def test_varnode_matches_parameter_rejects_name_only_high_variable():
    summarizer = StructuralRecurrenceSummarizer(_IdentityTracer(), debug=False)
    varnode = _FakeVarnode("param_1", high=_FakeHighVar("param_1"))
    parameter = {"name": "param_1", "index": 0, "size": 4}

    assert summarizer._varnode_matches_parameter(varnode, parameter) is False


def test_varnode_matches_parameter_accepts_parameter_index_or_storage_identity():
    index_symbol = _FakeHighSymbol(category_index=1)
    indexed_varnode = _FakeVarnode("renamed", high=_FakeHighVar("renamed", symbol=index_symbol))
    storage = _register_storage("x0", offset=0x4000, size=8)
    storage_varnode = _FakeVarnode("local_alias")
    parameter_by_index = {"name": "count", "index": 1, "size": 4}
    parameter_by_storage = {
        "name": "base",
        "index": -1,
        "size": 8,
        "storage": storage.to_dict(),
    }
    summarizer = StructuralRecurrenceSummarizer(
        _IdentityTracer(storages={storage_varnode: storage}),
        debug=False,
    )

    assert summarizer._varnode_matches_parameter(indexed_varnode, parameter_by_index) is True
    assert summarizer._varnode_matches_parameter(storage_varnode, parameter_by_storage) is True


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


def test_counted_loop_accumulator_extraction_assigns_distinct_binder_ordinals():
    header = _FakeCfgBlock(1)
    body = _FakeCfgBlock(2)
    header.add_edge(body)
    body.add_edge(header)

    zero_vn = _FakeVarnode("zero", expr=_const(0))
    one_vn = _FakeVarnode("one", expr=_const(1))
    iv_phi_vn = _FakeVarnode("iv_phi")
    iv_next_vn = _FakeVarnode("iv_next")
    iv_next_op = _FakePcodeOp("INT_ADD", [iv_phi_vn, one_vn], iv_next_vn)
    iv_phi_op = _FakePcodeOp("MULTIEQUAL", [zero_vn, iv_next_vn], iv_phi_vn)

    acc_a_phi_vn = _FakeVarnode("acc_a_phi")
    acc_a_next_vn = _FakeVarnode("acc_a_next")
    acc_a_next_op = _FakePcodeOp("INT_ADD", [acc_a_phi_vn, one_vn], acc_a_next_vn)
    acc_a_phi_op = _FakePcodeOp("MULTIEQUAL", [zero_vn, acc_a_next_vn], acc_a_phi_vn)

    acc_b_phi_vn = _FakeVarnode("acc_b_phi")
    acc_b_next_vn = _FakeVarnode("acc_b_next")
    acc_b_next_op = _FakePcodeOp("INT_ADD", [acc_b_phi_vn, one_vn], acc_b_next_vn)
    acc_b_phi_op = _FakePcodeOp("MULTIEQUAL", [zero_vn, acc_b_next_vn], acc_b_phi_vn)

    header._ops[:] = [iv_phi_op, acc_a_phi_op, acc_b_phi_op]
    body._ops[:] = [iv_next_op, acc_a_next_op, acc_b_next_op]
    for op in header._ops:
        op.setParent(header)
    for op in body._ops:
        op.setParent(body)

    induction = CountedLoopInduction(
        phi_op=iv_phi_op,
        phi_output=iv_phi_vn,
        init_expr=_const(0),
        backedge_index=1,
        step=1,
        placeholder=Expression.parameter("__loop_iv", index=-10_000, size=4),
        signed_guard=False,
        init_index=0,
        backedge_indices=(1,),
    )
    summarizer = StructuralRecurrenceSummarizer(_FakeTracer("unused", _const(0)), debug=False)

    accumulators = summarizer._match_counted_loop_accumulators(
        [iv_phi_op, acc_a_phi_op, acc_b_phi_op],
        induction,
        body,
    )

    ordinals = sorted(
        int(accumulator.placeholder.runtime_ref.binder_ordinal)
        for accumulator in accumulators
    )
    assert ordinals == [0, 1]
    ordinal_by_output = {
        accumulator.phi_output._name: int(accumulator.placeholder.runtime_ref.binder_ordinal)
        for accumulator in accumulators
    }
    reversed_accumulators = summarizer._match_counted_loop_accumulators(
        [iv_phi_op, acc_b_phi_op, acc_a_phi_op],
        induction,
        body,
    )
    reversed_ordinal_by_output = {
        accumulator.phi_output._name: int(accumulator.placeholder.runtime_ref.binder_ordinal)
        for accumulator in reversed_accumulators
    }
    assert reversed_ordinal_by_output == ordinal_by_output

    loop_summary = LoopSummaryRef(
        start_expr=_const(0),
        limit_expr=_param("param_1"),
        step_expr=_const(1),
        term_descriptor=LoopTermDescriptorRef(kind="affine_residue"),
        seed_terms=tuple(accumulator.placeholder for accumulator in accumulators),
        side_effect_profile=LoopSideEffectProfileRef(profile="pure"),
    )
    assert loop_summary_method_b_key(loop_summary) is not None


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
    condition_expr, entry_condition_expr, bound_expr, signed = normalized
    assert signed is True
    assert bound_expr.equals(_const(0))
    assert condition_expr.operator == "INT_SLESS"
    assert condition_expr.operands[0].equals(_const(0))
    assert condition_expr.operands[1].equals(counter)
    assert entry_condition_expr.operator == "INT_SLESS"
    assert entry_condition_expr.operands[0].equals(_const(0))
    assert entry_condition_expr.operands[1].equals(counter)


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
    assert loop_case.summary_candidate_source_key is not None
    assert loop_case.summary_transition_evidence_key is not None
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


def test_state_transition_loop_summary_recovers_branch_driven_trip_count():
    analysis = create_mock_analysis(
        "branch_while_state",
        return_type="int",
        parameters=[{"name": "param_1", "index": 0, "data_type": "int", "size": 4, "is_signed": True}],
        returns=[
            ReturnInfo(address="0x1000", value=_const(0), conditions=[]),
            ReturnInfo(
                address="0x1004",
                value=Expression.binary_op("INT_ADD", Expression.unknown("phi_circular"), _const(1)),
                conditions=[_cond("INT_SLESS", _const(0), _param("param_1"))],
            ),
        ],
    )

    summarizer = StructuralRecurrenceSummarizer(_FakeTracer("unused", _const(0)), debug=False)
    summary = summarizer.try_summarize_function(
        _FakeFunction("branch_while_state"),
        _build_branch_while_state_cfg(),
        analysis,
    )

    assert summary is not None
    summarized_returns, note = summary
    assert note == "state_transition_loop_summary"
    assert len(summarized_returns) == 2
    assert all(expression_has_unresolved_value(ret.value) is False for ret in summarized_returns)

    loop_case = next(ret for ret in summarized_returns if ret.value.expr_type == ExpressionType.INTRINSIC)
    assert loop_case.value.opcode == STATE_TRANSITION_LOOP_COUNT_OPCODE
    assert isinstance(loop_case.value.runtime_ref, StateTransitionLoopSummaryRef)
    loop_smt = expression_to_smt(loop_case.value)
    assert "rt_state_transition_loop_count_" in loop_smt
    assert "rtunk_" not in loop_smt


def test_state_transition_loop_summary_preserves_nonzero_accumulator_seed():
    analysis = create_mock_analysis(
        "branch_while_state_seeded",
        return_type="int",
        parameters=[{"name": "param_1", "index": 0, "data_type": "int", "size": 4, "is_signed": True}],
        returns=[
            ReturnInfo(address="0x1000", value=_const(5), conditions=[]),
            ReturnInfo(
                address="0x1004",
                value=Expression.binary_op("INT_ADD", _const(5), Expression.unknown("phi_circular")),
                conditions=[_cond("INT_SLESS", _const(0), _param("param_1"))],
            ),
        ],
    )

    summarizer = StructuralRecurrenceSummarizer(_FakeTracer("unused", _const(0)), debug=False)
    summary = summarizer.try_summarize_function(
        _FakeFunction("branch_while_state_seeded"),
        _build_branch_while_state_cfg(accumulator_init_expr=_const(5)),
        analysis,
    )

    assert summary is not None
    summarized_returns, note = summary
    assert note == "state_transition_loop_summary"
    base_case = next(ret for ret in summarized_returns if ret.conditions[0].negated is True)
    positive_case = next(ret for ret in summarized_returns if ret.conditions[0].negated is False)
    assert base_case.value.structural_key() == _const(5).structural_key()
    assert expression_has_unresolved_value(positive_case.value) is False
    positive_smt = expression_to_smt(positive_case.value)
    assert "rt_state_transition_loop_count_" in positive_smt
    assert "(bvadd (_ bv5 32)" in positive_smt


def test_state_transition_loop_summary_recovers_latch_guarded_state_loop():
    analysis = create_mock_analysis(
        "branch_while_state",
        return_type="int",
        parameters=[{"name": "param_1", "index": 0, "data_type": "int", "size": 4, "is_signed": True}],
        returns=[
            ReturnInfo(address="0x1000", value=_const(0), conditions=[]),
            ReturnInfo(address="0x1004", value=_const(1), conditions=[_cond("INT_SLESS", _const(0), _param("param_1"))]),
        ],
    )

    summarizer = StructuralRecurrenceSummarizer(_FakeTracer("unused", _const(0)), debug=False)
    summary = summarizer.try_summarize_function(
        _FakeFunction("branch_while_state"),
        _build_branch_while_state_latch_guarded_cfg(),
        analysis,
    )

    assert summary is not None
    summarized_returns, note = summary
    assert note == "state_transition_loop_summary"
    loop_case = next(ret for ret in summarized_returns if ret.value.expr_type == ExpressionType.INTRINSIC)
    assert loop_case.conditions[0].to_string() == "(0 < param_1)"
    assert loop_case.value.runtime_ref.semantic_key() is not None


def test_state_transition_loop_summary_recovers_state_affine_accumulator_sum():
    analysis = create_mock_analysis(
        "decrement_sum_state",
        return_type="int",
        parameters=[{"name": "param_1", "index": 0, "data_type": "int", "size": 4, "is_signed": True}],
        returns=[
            ReturnInfo(address="0x1000", value=_const(0), conditions=[]),
            ReturnInfo(address="0x1004", value=Expression.unknown("phi_circular"), conditions=[]),
        ],
    )

    summarizer = StructuralRecurrenceSummarizer(_FakeTracer("unused", _const(0)), debug=False)
    summary = summarizer._try_summarize_state_transition_loop(
        _FakeFunction("decrement_sum_state"),
        _build_decrement_accumulator_sum_cfg(),
        analysis,
    )

    assert summary is not None
    summarized_returns, note = summary
    assert note == "state_transition_loop_summary"
    positive_case = next(ret for ret in summarized_returns if ret.conditions[0].negated is False)
    assert positive_case.conditions[0].to_string() == "(0 < param_1)"
    assert expression_has_unresolved_value(positive_case.value) is False
    assert positive_case.value.expr_type != ExpressionType.INTRINSIC
    positive_smt = expression_to_smt(positive_case.value)
    assert "rt_state_transition_loop_count_" not in positive_smt
    assert "zero_extend" in positive_smt
    assert "(bvmul ((_ zero_extend" in positive_smt
    assert "extract 31 0" in positive_smt


def test_state_transition_loop_summary_recovers_latch_exit_decrement_sum_without_triangular_proof():
    state_equals_one = Expression.binary_op(
        "INT_NOTEQUAL",
        Expression.binary_op("INT_SUB", _param("param_1"), _const(1)),
        _const(0),
    )
    state_equals_one.size = 1
    analysis = create_mock_analysis(
        "latch_exit_decrement_sum",
        return_type="int",
        parameters=[{"name": "param_1", "index": 0, "data_type": "int", "size": 4, "is_signed": True}],
        returns=[
            ReturnInfo(address="0x1000", value=_const(0), conditions=[_cond("INT_SLESSEQUAL", _param("param_1"), _const(0))]),
            ReturnInfo(
                address="0x1004",
                value=Expression.binary_op("INT_ADD", _param("param_1"), _const(0)),
                conditions=[
                    _cond("INT_SLESS", _const(0), _param("param_1")),
                    Condition(state_equals_one, negated=True),
                ],
            ),
        ],
    )

    summarizer = StructuralRecurrenceSummarizer(_FakeTracer("unused", _const(0)), debug=False)
    summary = summarizer._try_summarize_state_transition_loop(
        _FakeFunction("latch_exit_decrement_sum"),
        _build_latch_exit_decrement_accumulator_sum_cfg(),
        analysis,
    )

    assert summary is not None
    summarized_returns, note = summary
    assert note == "state_transition_loop_summary"
    assert len(summarized_returns) == 2
    positive_case = next(ret for ret in summarized_returns if ret.branch_index == 10_300)
    assert positive_case.conditions[0].to_string() == "(0 < param_1)"
    assert expression_has_unresolved_value(positive_case.value) is False
    assert positive_case.value.expr_type != ExpressionType.INTRINSIC
    positive_smt = expression_to_smt(positive_case.value)
    assert "rt_state_transition_loop_count_" not in positive_smt
    assert "(bvmul (bvsub param_1 (_ bv1 32)) (bvsub param_1 (_ bv1 32)))" in positive_smt
    assert "bvlshr" in positive_smt


def test_multiplicative_phi_return_region_recovers_direct_state_value():
    phi_value = Expression.unknown("phi_circular")
    recursive_value = Expression.binary_op("INT_MULT", phi_value, _const(2))
    recursive_value.size = 4
    analysis = create_mock_analysis(
        "multiplicative_phi_region",
        return_type="int",
        parameters=[{"name": "param_1", "index": 0, "data_type": "int", "size": 4, "is_signed": True}],
        returns=[
            ReturnInfo(
                address="0x1000",
                value=_const(0),
                conditions=[_cond("INT_SLESSEQUAL", _param("param_1"), _const(0))],
            ),
            ReturnInfo(
                address="0x1004",
                value=_const(1),
                conditions=[_cond("INT_SLESS", _const(0), _param("param_1"))],
                return_kind="phi_expansion",
            ),
            ReturnInfo(
                address="0x1008",
                value=recursive_value,
                conditions=[_cond("INT_SLESS", _const(0), _param("param_1"))],
                return_kind="phi_expansion",
            ),
        ],
    )

    summarizer = StructuralRecurrenceSummarizer(_FakeTracer("unused", _const(0)), debug=False)
    summary = summarizer._try_summarize_multiplicative_phi_return_region(
        _FakeFunction("multiplicative_phi_region"),
        _build_decrement_accumulator_sum_cfg(),
        analysis,
    )

    assert summary is not None
    summarized_returns, note = summary
    assert note == "multiplicative_phi_return_region_summary"
    assert len(summarized_returns) == 2
    positive_case = next(
        ret
        for ret in summarized_returns
        if ret.value.opcode == COUNTED_STATE_TRANSITION_VALUE_OPCODE
    )
    assert positive_case.conditions[0].to_string() == "(0 < param_1)"
    assert positive_case.value.opcode == COUNTED_STATE_TRANSITION_VALUE_OPCODE
    assert isinstance(positive_case.value.runtime_ref, CountedStateTransitionLoopSummaryRef)
    assert expression_has_unresolved_value(positive_case.value) is False
    positive_smt = expression_to_smt(positive_case.value)
    assert "rt_counted_state_transition_value_" not in positive_smt
    assert "pow_acc" in positive_smt
    assert positive_case.summary_transition_evidence_key is not None


def test_multiplicative_phi_return_region_requires_zero_base_return_proof():
    phi_value = Expression.unknown("phi_circular")
    recursive_value = Expression.binary_op("INT_MULT", phi_value, _const(2))
    recursive_value.size = 4
    analysis = create_mock_analysis(
        "multiplicative_phi_region",
        return_type="int",
        parameters=[{"name": "param_1", "index": 0, "data_type": "int", "size": 4, "is_signed": True}],
        returns=[
            ReturnInfo(
                address="0x1000",
                value=_const(1),
                conditions=[_cond("INT_SLESSEQUAL", _param("param_1"), _const(0))],
            ),
            ReturnInfo(
                address="0x1004",
                value=_const(1),
                conditions=[_cond("INT_SLESS", _const(0), _param("param_1"))],
                return_kind="phi_expansion",
            ),
            ReturnInfo(
                address="0x1008",
                value=recursive_value,
                conditions=[_cond("INT_SLESS", _const(0), _param("param_1"))],
                return_kind="phi_expansion",
            ),
        ],
    )

    summarizer = StructuralRecurrenceSummarizer(_FakeTracer("unused", _const(0)), debug=False)

    assert summarizer._try_summarize_multiplicative_phi_return_region(
        _FakeFunction("multiplicative_phi_region"),
        _build_decrement_accumulator_sum_cfg(),
        analysis,
    ) is None


def test_multiplicative_phi_return_region_accepts_unconditional_zero_base_witness():
    phi_value = Expression.unknown("phi_circular")
    recursive_value = Expression.binary_op("INT_MULT", phi_value, _const(2))
    recursive_value.size = 4
    analysis = create_mock_analysis(
        "multiplicative_phi_region",
        return_type="int",
        parameters=[{"name": "param_1", "index": 0, "data_type": "int", "size": 4, "is_signed": True}],
        returns=[
            ReturnInfo(address="0x1000", value=_const(0), conditions=[]),
            ReturnInfo(
                address="0x1004",
                value=_const(1),
                conditions=[_cond("INT_SLESS", _const(0), _param("param_1"))],
                return_kind="phi_expansion",
            ),
            ReturnInfo(
                address="0x1008",
                value=recursive_value,
                conditions=[_cond("INT_SLESS", _const(0), _param("param_1"))],
                return_kind="phi_expansion",
            ),
        ],
    )

    summarizer = StructuralRecurrenceSummarizer(_FakeTracer("unused", _const(0)), debug=False)
    summary = summarizer._try_summarize_multiplicative_phi_return_region(
        _FakeFunction("multiplicative_phi_region"),
        _build_decrement_accumulator_sum_cfg(),
        analysis,
    )

    assert summary is not None
    summarized_returns, _note = summary
    assert any(ret.conditions and ret.conditions[0].to_string() == "(param_1 <= 0)" for ret in summarized_returns)


def test_multiplicative_phi_return_region_ignores_unrelated_high_function_multiplier():
    analysis = create_mock_analysis(
        "multiplicative_phi_region",
        return_type="int",
        parameters=[{"name": "param_1", "index": 0, "data_type": "int", "size": 4, "is_signed": True}],
        returns=[
            ReturnInfo(
                address="0x1000",
                value=_const(0),
                conditions=[_cond("INT_SLESSEQUAL", _param("param_1"), _const(0))],
            ),
            ReturnInfo(
                address="0x1004",
                value=_const(1),
                conditions=[_cond("INT_SLESS", _const(0), _param("param_1"))],
                return_kind="phi_expansion",
            ),
        ],
    )
    high_function = _build_decrement_accumulator_sum_cfg()
    unrelated_phi = _FakeVarnode("unrelated_phi")
    unrelated_next = _FakeVarnode("unrelated_next")
    _FakePcodeOp("MULTIEQUAL", [_FakeVarnode("seed", expr=_const(1)), unrelated_next], unrelated_phi)
    unrelated_mult = _FakePcodeOp(
        "INT_MULT",
        [unrelated_phi, _FakeConstantVarnode(2)],
        unrelated_next,
    )
    block = high_function.getBasicBlocks()[1]
    block._ops.append(unrelated_mult)
    unrelated_mult.setParent(block)

    summarizer = StructuralRecurrenceSummarizer(_FakeTracer("unused", _const(0)), debug=False)

    assert summarizer._try_summarize_multiplicative_phi_return_region(
        _FakeFunction("multiplicative_phi_region"),
        high_function,
        analysis,
    ) is None


def test_peeled_decrement_accumulator_sum_keeps_state_width_until_return_truncation():
    summarizer = StructuralRecurrenceSummarizer(_FakeTracer("unused", _const(0)), debug=False)
    value = summarizer._build_peeled_decrement_accumulator_sum_value(
        _param("param_1", size=8),
        result_size=4,
    )

    assert value is not None
    assert value.size == 4
    n_value = 0x100000001
    expected_low_sum = ((n_value * (n_value + 1)) // 2) & 0xFFFFFFFF
    assert expected_low_sum == 0x80000001
    assert _eval_bv_expression(value, {"param_1": n_value}) == expected_low_sum


def test_state_transition_loop_summary_rejects_latch_exit_decrement_sum_without_one_case_witness():
    analysis = create_mock_analysis(
        "latch_exit_decrement_sum",
        return_type="int",
        parameters=[{"name": "param_1", "index": 0, "data_type": "int", "size": 4, "is_signed": True}],
        returns=[
            ReturnInfo(address="0x1000", value=_const(0), conditions=[_cond("INT_SLESSEQUAL", _param("param_1"), _const(0))]),
            ReturnInfo(
                address="0x1004",
                value=Expression.binary_op("INT_ADD", _param("param_1"), _const(0)),
                conditions=[_cond("INT_SLESS", _const(0), _param("param_1"))],
            ),
        ],
    )

    summarizer = StructuralRecurrenceSummarizer(_FakeTracer("unused", _const(0)), debug=False)

    assert summarizer._try_summarize_state_transition_loop(
        _FakeFunction("latch_exit_decrement_sum"),
        _build_latch_exit_decrement_accumulator_sum_cfg(),
        analysis,
    ) is None


def test_state_transition_loop_summary_key_is_object_centric_across_branch_order():
    analysis = create_mock_analysis(
        "branch_while_state",
        return_type="int",
        parameters=[{"name": "param_1", "index": 0, "data_type": "int", "size": 4, "is_signed": True}],
        returns=[ReturnInfo(address="0x1000", value=Expression.unknown("phi_circular"), conditions=[])],
    )
    summarizer = StructuralRecurrenceSummarizer(_FakeTracer("unused", _const(0)), debug=False)

    left_returns, _ = summarizer.try_summarize_function(
        _FakeFunction("branch_while_state"),
        _build_branch_while_state_cfg(swap_transition_inputs=False),
        analysis,
    )
    right_returns, _ = summarizer.try_summarize_function(
        _FakeFunction("branch_while_state"),
        _build_branch_while_state_cfg(swap_transition_inputs=True),
        analysis,
    )

    left_intrinsic = next(ret.value for ret in left_returns if ret.value.expr_type == ExpressionType.INTRINSIC)
    right_intrinsic = next(ret.value for ret in right_returns if ret.value.expr_type == ExpressionType.INTRINSIC)
    assert left_intrinsic.runtime_ref.semantic_key() == right_intrinsic.runtime_ref.semantic_key()


def test_state_transition_loop_summary_key_matches_header_and_latch_guards():
    analysis = create_mock_analysis(
        "branch_while_state",
        return_type="int",
        parameters=[{"name": "param_1", "index": 0, "data_type": "int", "size": 4, "is_signed": True}],
        returns=[ReturnInfo(address="0x1000", value=Expression.unknown("phi_circular"), conditions=[])],
    )
    summarizer = StructuralRecurrenceSummarizer(_FakeTracer("unused", _const(0)), debug=False)

    header_returns, _ = summarizer.try_summarize_function(
        _FakeFunction("branch_while_state"),
        _build_branch_while_state_cfg(),
        analysis,
    )
    latch_returns, _ = summarizer.try_summarize_function(
        _FakeFunction("branch_while_state"),
        _build_branch_while_state_latch_guarded_cfg(),
        analysis,
    )

    header_intrinsic = next(ret.value for ret in header_returns if ret.value.expr_type == ExpressionType.INTRINSIC)
    latch_intrinsic = next(ret.value for ret in latch_returns if ret.value.expr_type == ExpressionType.INTRINSIC)
    assert header_intrinsic.runtime_ref.semantic_key() == latch_intrinsic.runtime_ref.semantic_key()


def test_state_transition_loop_summary_key_unifies_unsigned_shift_under_positive_guard():
    analysis = create_mock_analysis(
        "branch_while_state",
        return_type="int",
        parameters=[{"name": "param_1", "index": 0, "data_type": "int", "size": 4, "is_signed": True}],
        returns=[ReturnInfo(address="0x1000", value=Expression.unknown("phi_circular"), conditions=[])],
    )
    summarizer = StructuralRecurrenceSummarizer(_FakeTracer("unused", _const(0)), debug=False)

    signed_returns, _ = summarizer.try_summarize_function(
        _FakeFunction("branch_while_state"),
        _build_branch_while_state_latch_guarded_cfg(shift_mnemonic="INT_SRIGHT"),
        analysis,
    )
    unsigned_returns, _ = summarizer.try_summarize_function(
        _FakeFunction("branch_while_state"),
        _build_branch_while_state_latch_guarded_cfg(shift_mnemonic="INT_RIGHT"),
        analysis,
    )

    signed_intrinsic = next(ret.value for ret in signed_returns if ret.value.expr_type == ExpressionType.INTRINSIC)
    unsigned_intrinsic = next(ret.value for ret in unsigned_returns if ret.value.expr_type == ExpressionType.INTRINSIC)
    assert signed_intrinsic.runtime_ref.semantic_key() == unsigned_intrinsic.runtime_ref.semantic_key()


def test_state_transition_loop_summary_cases_drop_post_state_guard():
    analysis = create_mock_analysis(
        "branch_while_state",
        return_type="int",
        parameters=[{"name": "param_1", "index": 0, "data_type": "int", "size": 4, "is_signed": True}],
        returns=[ReturnInfo(address="0x1000", value=Expression.unknown("phi_circular"), conditions=[])],
    )
    summarizer = StructuralRecurrenceSummarizer(_FakeTracer("unused", _const(0)), debug=False)
    returns, _ = summarizer.try_summarize_function(
        _FakeFunction("branch_while_state"),
        _build_branch_while_state_latch_guarded_cfg(),
        analysis,
    )

    intrinsic = next(ret.value for ret in returns if ret.value.expr_type == ExpressionType.INTRINSIC)
    cases = intrinsic.runtime_ref.transition_cases
    assert len(cases) == 2
    for condition_expr, _negated, _value in cases:
        assert condition_expr is not None
        condition_operators = _expression_operators(condition_expr)
        assert "INT_AND" in condition_operators
        assert "INT_SLESS" not in condition_operators


def test_state_transition_loop_summary_completes_default_case_as_complement():
    state = Expression.variable("__loop_state", size=4)
    parity = Expression.binary_op("INT_EQUAL", Expression.binary_op("INT_AND", state, _const(1)), _const(0))
    shift = Expression.binary_op("INT_SRIGHT", state, _const(1))
    subtract = Expression.binary_op("INT_SUB", state, _const(3))
    guard = Expression.binary_op("INT_SLESS", _const(0), state)
    summarizer = StructuralRecurrenceSummarizer(_FakeTracer("unused", _const(0)), debug=False)
    parity, _ = summarizer._normalize_state_transition_condition_term(parity, False)

    default_cases = summarizer._complete_default_state_transition_cases(
        ((parity, False, shift, False), (None, False, subtract, True))
    )
    default_cases = tuple(
        (condition, negated, value)
        for condition, negated, value, _is_source_default in default_cases
    )
    explicit_ref = StateTransitionLoopSummaryRef(
        state_guard=guard,
        transition_expr=None,
        transition_cases=((parity, False, shift), (parity, True, subtract)),
        accumulator_init=_const(0),
        accumulator_delta=_const(1),
        state_size=4,
        result_size=4,
    )
    default_ref = StateTransitionLoopSummaryRef(
        state_guard=guard,
        transition_expr=None,
        transition_cases=default_cases,
        accumulator_init=_const(0),
        accumulator_delta=_const(1),
        state_size=4,
        result_size=4,
    )

    assert default_ref.semantic_key() == explicit_ref.semantic_key()


def test_state_transition_loop_summary_does_not_rewrite_shifted_negative_candidate():
    state = Expression.variable("__loop_state", size=4)
    signed_guard = Expression.binary_op("INT_SLESS", _const(0), state)
    unsigned_guard = Expression.binary_op("INT_LESS", _const(0), state)
    unsigned_prechecked_guard = Expression.binary_op("INT_LESSEQUAL", _const(1), state)
    unsigned_negated_exit_guard = Expression.unary_op(
        "BOOL_NEGATE",
        Expression.binary_op("INT_LESS", state, _const(1)),
    )
    unsigned_negated_exit_guard.size = 1
    one = _const(1)
    three = _const(3)
    summarizer = StructuralRecurrenceSummarizer(_FakeTracer("unused", _const(0)), debug=False)

    direct_shift = Expression.binary_op("INT_RIGHT", state, one)
    canonical_direct = summarizer._canonicalize_state_transition_value(
        direct_shift,
        state_placeholder=state,
        state_guard=signed_guard,
    )
    assert canonical_direct.operator == "INT_SRIGHT"

    unsigned_guard_shift = summarizer._canonicalize_state_transition_value(
        direct_shift,
        state_placeholder=state,
        state_guard=unsigned_guard,
    )
    assert unsigned_guard_shift.operator == "INT_RIGHT"

    normalized_unsigned_precheck = summarizer._normalize_state_transition_state_guard(
        unsigned_prechecked_guard,
        state,
    )
    assert not summarizer._state_guard_proves_signed_positive_placeholder(normalized_unsigned_precheck, state)
    unsigned_precheck_shift = summarizer._canonicalize_state_transition_value(
        direct_shift,
        state_placeholder=state,
        state_guard=normalized_unsigned_precheck,
    )
    assert unsigned_precheck_shift.operator == "INT_RIGHT"

    normalized_unsigned_exit = summarizer._normalize_state_transition_state_guard(
        unsigned_negated_exit_guard,
        state,
    )
    assert not summarizer._state_guard_proves_signed_positive_placeholder(normalized_unsigned_exit, state)
    unsigned_exit_shift = summarizer._canonicalize_state_transition_value(
        direct_shift,
        state_placeholder=state,
        state_guard=normalized_unsigned_exit,
    )
    assert unsigned_exit_shift.operator == "INT_RIGHT"

    shifted_subtract = Expression.binary_op("INT_RIGHT", Expression.binary_op("INT_SUB", state, three), one)
    canonical_shifted_subtract = summarizer._canonicalize_state_transition_value(
        shifted_subtract,
        state_placeholder=state,
        state_guard=signed_guard,
    )
    assert canonical_shifted_subtract.operator == "INT_RIGHT"


def test_multiplicative_state_transition_base_recovery_proves_chunked_constant_case():
    summarizer = StructuralRecurrenceSummarizer(_FakeTracer("unused", _const(0)), debug=False)
    n = _param("param_1")
    start = _const(1)
    limit = Expression.binary_op("INT_ADD", n, _const(1))
    condition = _cond("INT_EQUAL", n, _const(4))

    recovered = summarizer._recover_proved_multiplicative_state_transition_base(
        loop_base_expr=_const(625),
        continue_conditions=[condition],
        start_expr=start,
        limit_expr=limit,
        result_size=4,
        signed_loop=True,
    )

    assert recovered is not None
    assert recovered.opcode == COUNTED_STATE_TRANSITION_VALUE_OPCODE
    assert isinstance(recovered.runtime_ref, CountedStateTransitionLoopSummaryRef)
    assert recovered.runtime_ref.initial_state.equals(_const(1))
    assert recovered.runtime_ref.start_expr.equals(start)
    assert recovered.runtime_ref.limit_expr.equals(limit)


def test_multiplicative_state_transition_base_recovery_rejects_near_misses():
    summarizer = StructuralRecurrenceSummarizer(_FakeTracer("unused", _const(0)), debug=False)
    n = _param("param_1")
    start = _const(1)
    limit = Expression.binary_op("INT_ADD", n, _const(1))

    assert summarizer._recover_proved_multiplicative_state_transition_base(
        loop_base_expr=_const(1295),
        continue_conditions=[_cond("INT_EQUAL", n, _const(4))],
        start_expr=start,
        limit_expr=limit,
        result_size=4,
        signed_loop=True,
    ) is None
    assert summarizer._recover_proved_multiplicative_state_transition_base(
        loop_base_expr=_const(125),
        continue_conditions=[_cond("INT_EQUAL", n, _const(4))],
        start_expr=start,
        limit_expr=limit,
        result_size=4,
        signed_loop=True,
    ) is None
    assert summarizer._recover_proved_multiplicative_state_transition_base(
        loop_base_expr=_const(625),
        continue_conditions=[_cond("INT_EQUAL", n, _const(3))],
        start_expr=start,
        limit_expr=limit,
        result_size=4,
        signed_loop=True,
    ) is None
    assert summarizer._recover_proved_multiplicative_state_transition_base(
        loop_base_expr=Expression.unknown("chunked_state"),
        continue_conditions=[_cond("INT_EQUAL", n, _const(4))],
        start_expr=start,
        limit_expr=limit,
        result_size=4,
        signed_loop=True,
    ) is None


def test_state_transition_loop_summary_rejects_non_state_transition_condition():
    state = Expression.variable("__loop_state", size=4)
    selector = Expression.parameter("param_2", index=1, data_type="int", size=4)
    guard = Expression.binary_op("INT_SLESS", _const(0), state)
    selector_condition = Condition(Expression.binary_op("INT_SLESS", _const(0), selector), False)
    transition_expr = Expression.phi((
        (selector_condition, Expression.binary_op("INT_SUB", state, _const(1))),
        (None, Expression.binary_op("INT_SUB", state, _const(2))),
    ))
    transition_expr.size = 4
    summarizer = StructuralRecurrenceSummarizer(_FakeTracer("unused", _const(0)), debug=False)

    assert summarizer._state_transition_summary_cases(
        transition_expr=transition_expr,
        state_guard=guard,
        state_placeholder=state,
    ) is None


def test_state_transition_loop_summary_drops_non_state_condition_when_values_match():
    state = Expression.variable("__loop_state", size=4)
    selector = Expression.parameter("param_2", index=1, data_type="int", size=4)
    guard = Expression.binary_op("INT_SLESS", _const(0), state)
    selector_condition = Condition(Expression.binary_op("INT_SLESS", _const(0), selector), False)
    same_value = Expression.binary_op("INT_SUB", state, _const(1))
    transition_expr = Expression.phi((
        (selector_condition, same_value),
        (None, same_value),
    ))
    transition_expr.size = 4
    summarizer = StructuralRecurrenceSummarizer(_FakeTracer("unused", _const(0)), debug=False)

    cases = summarizer._state_transition_summary_cases(
        transition_expr=transition_expr,
        state_guard=guard,
        state_placeholder=state,
    )

    assert cases is not None
    assert len(cases) == 1
    condition_expr, negated, value = cases[0]
    assert condition_expr is None
    assert negated is False
    assert value.structural_key() == same_value.structural_key()


def test_state_transition_loop_summary_recovers_multi_latch_rotated_loop():
    analysis = create_mock_analysis(
        "branch_while_state",
        return_type="int",
        parameters=[{"name": "param_1", "index": 0, "data_type": "int", "size": 4, "is_signed": True}],
        returns=[ReturnInfo(address="0x1000", value=Expression.unknown("phi_circular"), conditions=[])],
    )
    summarizer = StructuralRecurrenceSummarizer(_FakeTracer("unused", _const(0)), debug=False)

    header_returns, _ = summarizer.try_summarize_function(
        _FakeFunction("branch_while_state"),
        _build_branch_while_state_cfg(),
        analysis,
    )
    multi_latch_returns, _ = summarizer.try_summarize_function(
        _FakeFunction("branch_while_state"),
        _build_branch_while_state_multi_latch_cfg(),
        analysis,
    )

    header_intrinsic = next(ret.value for ret in header_returns if ret.value.expr_type == ExpressionType.INTRINSIC)
    multi_latch_intrinsic = next(ret.value for ret in multi_latch_returns if ret.value.expr_type == ExpressionType.INTRINSIC)
    assert multi_latch_intrinsic.runtime_ref.semantic_key() == header_intrinsic.runtime_ref.semantic_key()


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
    monkeypatch.setattr(summarizer, "_count_counted_scalar_loop_models", lambda *_args, **_kwargs: 1)
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
    monkeypatch.setattr(summarizer, "_count_counted_scalar_loop_models", lambda *_args, **_kwargs: 2)
    assert summarizer.try_summarize_pre_return_counted_scalar_loop(
        _FakeFunction("branch_for_accumulate"),
        _FakeCfgHighFunction([header, ret_block]),
        analysis,
        [return_op],
    ) is None

    monkeypatch.setattr(summarizer, "_count_counted_scalar_loop_models", lambda *_args, **_kwargs: 1)
    extra_ret_block = _FakeCfgBlock(2)
    assert summarizer.try_summarize_pre_return_counted_scalar_loop(
        _FakeFunction("branch_for_accumulate"),
        _FakeCfgHighFunction([header, ret_block, extra_ret_block]),
        analysis,
        [return_op],
    ) is None


def test_counted_loop_model_count_includes_latch_guard_without_header_cbranch(monkeypatch):
    summarizer = StructuralRecurrenceSummarizer(_FakeTracer("unused", _const(0)), debug=False)
    iv_phi_vn = _FakeVarnode("iv_phi")
    acc_phi_vn = _FakeVarnode("acc_phi")
    iv_phi = _FakePcodeOp("MULTIEQUAL", [_FakeVarnode("iv_init"), _FakeVarnode("iv_next")], iv_phi_vn)
    acc_phi = _FakePcodeOp("MULTIEQUAL", [_FakeVarnode("acc_init"), _FakeVarnode("acc_next")], acc_phi_vn)
    header = _FakeCfgBlock(1, ops=[iv_phi, acc_phi])
    induction = CountedLoopInduction(
        phi_op=iv_phi,
        phi_output=iv_phi_vn,
        init_expr=_const(0),
        backedge_index=1,
        step=1,
        placeholder=Expression.parameter("__loop_iv", index=-1, size=4),
        signed_guard=True,
    )
    accumulator = CountedLoopAccumulator(
        phi_op=acc_phi,
        phi_output=acc_phi_vn,
        init_expr=_const(0),
        backedge_index=1,
        placeholder=Expression.variable("__loop_acc", size=4),
    )
    guard = CountedLoopGuard(
        condition_expr=Expression.binary_op("INT_SLESS", induction.placeholder, _param()),
        bound_expr=_param(),
        continue_on_true=True,
        body_block=header,
        exit_block=_FakeCfgBlock(2),
        signed_comparison=True,
        latch_block=_FakeCfgBlock(3),
    )

    monkeypatch.setattr(summarizer, "_find_cbranch_op", lambda block: None)
    monkeypatch.setattr(summarizer, "_match_counted_loop_induction", lambda phi_op: induction if phi_op is iv_phi else None)

    def fake_guards(candidate_header, cbranch, candidate_induction):
        assert candidate_header is header
        assert cbranch is None
        assert candidate_induction is induction
        return [guard]

    monkeypatch.setattr(summarizer, "_candidate_counted_loop_guards", fake_guards)
    monkeypatch.setattr(summarizer, "_match_counted_loop_accumulators", lambda *_args, **_kwargs: [accumulator])

    analysis = create_mock_analysis(
        "branch_for_accumulate",
        return_type="int",
        parameters=[{"name": "param_1", "index": 0, "data_type": "int", "size": 4}],
        returns=[],
    )

    assert summarizer._count_counted_scalar_loop_models(_FakeCfgHighFunction([header]), analysis) == 1


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
        lambda cases, _counter_name, **_kwargs: (
            ResidueLoopCase(modulus=1, residue=0, affine=(1, 0)),
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
        lambda cases, _counter_name, **_kwargs: (
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


def test_counted_loop_accumulator_extraction_rejects_executable_address_seed():
    header = _FakeCfgBlock(1)
    body = _FakeCfgBlock(2)
    header.add_edge(body)
    body.add_edge(header)

    text_space = _FakeAddressSpace("ram", space_id=1, is_memory=True)
    program = _FakeProgram(
        _FakeAddressFactory({1: text_space}, default_space=text_space),
        memory=_FakeMemory([_FakeMemoryBlock(0x100000, 0x101000, execute=False)]),
    )
    summarizer = StructuralRecurrenceSummarizer(
        _FakeTracer("unused", _const(0), program=program),
        debug=False,
    )

    zero_vn = _FakeVarnode("zero", expr=_const(0))
    one_vn = _FakeVarnode("one", expr=_const(1))
    twenty_vn = _FakeVarnode("twenty", expr=_const(20))
    param_2_vn = _FakeVarnode("param_2", expr=_param("param_2"))
    address_seed_vn = _FakeVarnode(
        "address_seed",
        expr=Expression.binary_op("INT_ADD", _param("param_2"), _const(0x100100)),
    )

    iv_phi_vn = _FakeVarnode("iv_phi")
    iv_next_vn = _FakeVarnode("iv_next")
    _FakePcodeOp("INT_ADD", [iv_phi_vn, one_vn], iv_next_vn).setParent(body)
    iv_phi_op = _FakePcodeOp("MULTIEQUAL", [zero_vn, iv_next_vn], iv_phi_vn)

    bad_phi_vn = _FakeVarnode("bad_acc")
    bad_next_vn = _FakeVarnode("bad_next")
    _FakePcodeOp("INT_ADD", [bad_phi_vn, twenty_vn], bad_next_vn).setParent(body)
    bad_phi_op = _FakePcodeOp("MULTIEQUAL", [address_seed_vn, bad_next_vn], bad_phi_vn)

    good_phi_vn = _FakeVarnode("good_acc")
    good_next_vn = _FakeVarnode("good_next")
    _FakePcodeOp("INT_ADD", [good_phi_vn, twenty_vn], good_next_vn).setParent(body)
    good_phi_op = _FakePcodeOp("MULTIEQUAL", [param_2_vn, good_next_vn], good_phi_vn)

    induction = CountedLoopInduction(
        phi_op=iv_phi_op,
        phi_output=iv_phi_vn,
        init_expr=_const(0),
        backedge_index=1,
        step=1,
        placeholder=Expression.parameter("__loop_iv", index=-10000, size=4),
        signed_guard=False,
        init_index=0,
        backedge_indices=(1,),
    )

    accumulators = summarizer._match_counted_loop_accumulators(
        [iv_phi_op, bad_phi_op, good_phi_op],
        induction,
        body,
        function_body_ranges=((0x100000, 0x101000),),
    )

    assert [accumulator.phi_output for accumulator in accumulators] == [good_phi_vn]


def test_vectorized_affine_progression_literal_summary_builds_counted_loop_sum():
    ram_space = _FakeAddressSpace("ram", space_id=1, is_memory=True)
    literal_base = 0x100120
    literal_bytes = bytes(
        byte
        for value in (0, 5, 10, 15)
        for byte in int(value).to_bytes(4, "little", signed=True)
    )
    program = _FakeProgram(
        _FakeAddressFactory({1: ram_space}, default_space=ram_space),
        memory=_FakeMemory(
            [_FakeMemoryBlock(literal_base, literal_base + len(literal_bytes) - 1, execute=False)],
            bytes_by_address={
                literal_base + offset: byte
                for offset, byte in enumerate(literal_bytes)
            },
        ),
    )
    tracer = _FakeTracer("f", _const(0), program=program)
    summarizer = StructuralRecurrenceSummarizer(tracer, debug=False)
    n_expr = Expression.parameter("param_1", index=0, data_type="int", size=4)
    bias_expr = Expression.parameter("param_2", index=1, data_type="int", size=4)
    positive_value = summarizer._build_affine_progression_sum_closed_expression(
        count_expr=n_expr,
        step=5,
        bias_expr=bias_expr,
        result_size=4,
    )
    assert positive_value is not None
    zero_case = ReturnInfo(
        address="00100104",
        value=_const(0),
        conditions=[
            Condition(
                Expression.binary_op("INT_SLESS", n_expr, _const(1)),
                False,
            )
        ],
        branch_index=0,
    )
    literal_case = ReturnInfo(
        address="00100104",
        value=positive_value,
        conditions=[Condition(Expression.binary_op("INT_SLESS", _const(0), n_expr), False)],
        branch_index=1,
    )
    literal_probe_case = ReturnInfo(
        address="00100104",
        value=Expression.binary_op("SUBPIECE", Expression.constant(literal_base, size=8), _const(0)),
        conditions=[
            Condition(Expression.binary_op("INT_EQUAL", n_expr, _const(0)), False),
            Condition(Expression.binary_op("INT_SLESS", _const(0), n_expr), False),
        ],
        branch_index=2,
    )
    analysis = type("FakeAnalysis", (), {})()
    int_type = _FakeIntDataType()
    analysis.parameters = [
        {"name": "param_1", "index": 0, "data_type": "uint", "data_type_obj": int_type, "size": 4},
        {"name": "param_2", "index": 1, "data_type": "int", "data_type_obj": int_type, "size": 4},
    ]
    analysis.returns = [zero_case, literal_case, literal_probe_case]
    analysis.incomplete_control_flow = False
    analysis.effect_summary = None

    summary = summarizer._try_summarize_vectorized_affine_progression_sum(
        _FakeFunction("f"),
        _FakeCfgHighFunction([]),
        analysis,
    )

    assert summary is not None
    returns, note = summary
    assert note == "vectorized_affine_progression_sum_summary"
    assert len(returns) == 2
    assert returns[0].value.equals(_const(0))
    loop_value = returns[1].value
    assert getattr(loop_value, "opcode", None) == COUNTED_LOOP_SUM_OPCODE
    runtime_ref = getattr(loop_value, "runtime_ref", None)
    assert runtime_ref is not None
    assert runtime_ref.residue_cases == ((1, 0, 5, 0),)
    assert runtime_ref.residue_bias_terms


def test_vectorized_affine_summary_preserves_side_effect_profile():
    ram_space = _FakeAddressSpace("ram", space_id=1, is_memory=True)
    literal_base = 0x100120
    literal_bytes = bytes(
        byte
        for value in (0, 5, 10, 15)
        for byte in int(value).to_bytes(4, "little", signed=True)
    )
    program = _FakeProgram(
        _FakeAddressFactory({1: ram_space}, default_space=ram_space),
        memory=_FakeMemory(
            [_FakeMemoryBlock(literal_base, literal_base + len(literal_bytes) - 1, execute=False)],
            bytes_by_address={
                literal_base + offset: byte
                for offset, byte in enumerate(literal_bytes)
            },
        ),
    )
    tracer = _FakeTracer("f", _const(0), program=program)
    summarizer = StructuralRecurrenceSummarizer(tracer, debug=False)
    n_expr = Expression.parameter("param_1", index=0, data_type="int", size=4)
    bias_expr = Expression.parameter("param_2", index=1, data_type="int", size=4)
    positive_value = summarizer._build_affine_progression_sum_closed_expression(
        count_expr=n_expr,
        step=5,
        bias_expr=bias_expr,
        result_size=4,
    )
    assert positive_value is not None
    analysis = type("FakeAnalysis", (), {})()
    int_type = _FakeIntDataType()
    analysis.parameters = [
        {"name": "param_1", "index": 0, "data_type": "int", "data_type_obj": int_type, "size": 4},
        {"name": "param_2", "index": 1, "data_type": "int", "data_type_obj": int_type, "size": 4},
    ]
    analysis.returns = [
        ReturnInfo(
            address="00100104",
            value=_const(0),
            conditions=[Condition(Expression.binary_op("INT_SLESS", n_expr, _const(1)), False)],
            branch_index=0,
        ),
        ReturnInfo(
            address="00100104",
            value=positive_value,
            conditions=[Condition(Expression.binary_op("INT_SLESS", _const(0), n_expr), False)],
            branch_index=1,
        ),
        ReturnInfo(
            address="00100104",
            value=Expression.binary_op("SUBPIECE", Expression.constant(literal_base, size=8), _const(0)),
            conditions=[
                Condition(Expression.binary_op("INT_EQUAL", n_expr, _const(0)), False),
                Condition(Expression.binary_op("INT_SLESS", _const(0), n_expr), False),
            ],
            branch_index=2,
        ),
    ]
    analysis.incomplete_control_flow = False
    analysis.effect_summary = None
    guard_block = _FakeCfgBlock(
        1,
        ops=[_FakeBranchOp(Expression.binary_op("INT_NOTEQUAL", n_expr, _const(0)))],
    )

    summary = summarizer._try_summarize_vectorized_affine_progression_sum(
        _FakeFunction("f"),
        _FakeCfgHighFunction([guard_block]),
        analysis,
    )

    assert summary is not None
    returns, _note = summary
    runtime_ref = getattr(returns[1].value, "runtime_ref", None)
    assert runtime_ref is not None
    profile = runtime_ref.loop_summary.side_effect_profile
    assert profile.profile == "pure"
    assert profile.conditional_guards is False
    assert profile.context_conditional_guards is True
    assert profile.guard_count == 0
    assert profile.effect_descriptors == ()
    assert len(profile.context_descriptors) == 1
    assert profile.context_descriptors[0].kind == "conditional_guard"


def test_vectorized_affine_progression_literal_summary_infers_constant_bias_for_single_parameter():
    ram_space = _FakeAddressSpace("ram", space_id=1, is_memory=True)
    literal_base = 0x100120
    literal_bytes = bytes(
        byte
        for value in (1, 2, 3, 4)
        for byte in int(value).to_bytes(4, "little", signed=True)
    )
    program = _FakeProgram(
        _FakeAddressFactory({1: ram_space}, default_space=ram_space),
        memory=_FakeMemory(
            [_FakeMemoryBlock(literal_base, literal_base + len(literal_bytes) - 1, execute=False)],
            bytes_by_address={
                literal_base + offset: byte
                for offset, byte in enumerate(literal_bytes)
            },
        ),
    )
    tracer = _FakeTracer("f", _const(0), program=program)
    summarizer = StructuralRecurrenceSummarizer(tracer, debug=False)
    n_expr = Expression.parameter("param_1", index=0, data_type="int", size=4)
    positive_value = summarizer._build_affine_progression_sum_closed_expression(
        count_expr=n_expr,
        step=1,
        bias_expr=_const(1),
        result_size=4,
    )
    assert positive_value is not None
    zero_case = ReturnInfo(
        address="00100104",
        value=_const(0),
        conditions=[
            Condition(
                Expression.binary_op("INT_SLESS", n_expr, _const(1)),
                False,
            )
        ],
        branch_index=0,
    )
    positive_case = ReturnInfo(
        address="00100104",
        value=positive_value,
        conditions=[Condition(Expression.binary_op("INT_SLESS", _const(0), n_expr), False)],
        branch_index=1,
    )
    literal_probe_case = ReturnInfo(
        address="00100104",
        value=Expression.binary_op("SUBPIECE", Expression.constant(literal_base, size=8), _const(0)),
        conditions=[
            Condition(Expression.binary_op("INT_EQUAL", n_expr, _const(0)), False),
            Condition(Expression.binary_op("INT_SLESS", _const(0), n_expr), False),
        ],
        branch_index=2,
    )
    analysis = type("FakeAnalysis", (), {})()
    int_type = _FakeIntDataType()
    analysis.parameters = [
        {"name": "param_1", "index": 0, "data_type": "int", "data_type_obj": int_type, "size": 4},
    ]
    analysis.returns = [zero_case, positive_case, literal_probe_case]
    analysis.incomplete_control_flow = False
    analysis.effect_summary = None

    summary = summarizer._try_summarize_vectorized_affine_progression_sum(
        _FakeFunction("f"),
        _FakeCfgHighFunction([]),
        analysis,
    )

    assert summary is not None
    returns, note = summary
    assert note == "vectorized_affine_progression_sum_summary"
    runtime_ref = getattr(returns[1].value, "runtime_ref", None)
    assert runtime_ref is not None
    assert runtime_ref.residue_cases == ((1, 0, 1, 0),)
    assert runtime_ref.residue_bias_terms
    assert runtime_ref.residue_bias_terms[0][2].equals(_const(1))


def test_vectorized_affine_progression_literal_summary_uses_nonzero_lane_base_for_single_parameter():
    ram_space = _FakeAddressSpace("ram", space_id=1, is_memory=True)
    literal_base = 0x100120
    literal_bytes = bytes(
        byte
        for value in (2, 7, 12, 17)
        for byte in int(value).to_bytes(4, "little", signed=True)
    )
    program = _FakeProgram(
        _FakeAddressFactory({1: ram_space}, default_space=ram_space),
        memory=_FakeMemory(
            [_FakeMemoryBlock(literal_base, literal_base + len(literal_bytes) - 1, execute=False)],
            bytes_by_address={
                literal_base + offset: byte
                for offset, byte in enumerate(literal_bytes)
            },
        ),
    )
    tracer = _FakeTracer("f", _const(0), program=program)
    summarizer = StructuralRecurrenceSummarizer(tracer, debug=False)
    n_expr = Expression.parameter("param_1", index=0, data_type="int", size=4)
    positive_value = summarizer._build_affine_progression_sum_closed_expression(
        count_expr=n_expr,
        step=5,
        bias_expr=_const(2),
        result_size=4,
    )
    assert positive_value is not None
    analysis = type("FakeAnalysis", (), {})()
    int_type = _FakeIntDataType()
    analysis.parameters = [
        {"name": "param_1", "index": 0, "data_type": "int", "data_type_obj": int_type, "size": 4},
    ]
    analysis.returns = [
        ReturnInfo(
            address="00100104",
            value=_const(0),
            conditions=[Condition(Expression.binary_op("INT_SLESS", n_expr, _const(1)), False)],
            branch_index=0,
        ),
        ReturnInfo(
            address="00100104",
            value=positive_value,
            conditions=[Condition(Expression.binary_op("INT_SLESS", _const(0), n_expr), False)],
            branch_index=1,
        ),
        ReturnInfo(
            address="00100104",
            value=Expression.binary_op("SUBPIECE", Expression.constant(literal_base, size=8), _const(0)),
            conditions=[
                Condition(Expression.binary_op("INT_EQUAL", n_expr, _const(0)), False),
                Condition(Expression.binary_op("INT_SLESS", _const(0), n_expr), False),
            ],
            branch_index=2,
        ),
    ]
    analysis.incomplete_control_flow = False
    analysis.effect_summary = None

    summary = summarizer._try_summarize_vectorized_affine_progression_sum(
        _FakeFunction("f"),
        _FakeCfgHighFunction([]),
        analysis,
    )

    assert summary is not None
    returns, note = summary
    assert note == "vectorized_affine_progression_sum_summary"
    runtime_ref = getattr(returns[1].value, "runtime_ref", None)
    assert runtime_ref is not None
    assert runtime_ref.residue_cases == ((1, 0, 5, 0),)
    assert runtime_ref.residue_bias_terms
    assert runtime_ref.residue_bias_terms[0][2].equals(_const(2))


def test_vectorized_affine_progression_literal_summary_adds_lane_base_to_parameter_bias():
    ram_space = _FakeAddressSpace("ram", space_id=1, is_memory=True)
    literal_base = 0x100120
    literal_bytes = bytes(
        byte
        for value in (2, 7, 12, 17)
        for byte in int(value).to_bytes(4, "little", signed=True)
    )
    program = _FakeProgram(
        _FakeAddressFactory({1: ram_space}, default_space=ram_space),
        memory=_FakeMemory(
            [_FakeMemoryBlock(literal_base, literal_base + len(literal_bytes) - 1, execute=False)],
            bytes_by_address={
                literal_base + offset: byte
                for offset, byte in enumerate(literal_bytes)
            },
        ),
    )
    tracer = _FakeTracer("f", _const(0), program=program)
    summarizer = StructuralRecurrenceSummarizer(tracer, debug=False)
    n_expr = Expression.parameter("param_1", index=0, data_type="int", size=4)
    bias_expr = Expression.parameter("param_2", index=1, data_type="int", size=4)
    bias_plus_lane_base = Expression.binary_op("INT_ADD", bias_expr, _const(2))
    bias_plus_lane_base.size = 4
    positive_value = summarizer._build_affine_progression_sum_closed_expression(
        count_expr=n_expr,
        step=5,
        bias_expr=bias_plus_lane_base,
        result_size=4,
    )
    assert positive_value is not None
    analysis = type("FakeAnalysis", (), {})()
    int_type = _FakeIntDataType()
    analysis.parameters = [
        {"name": "param_1", "index": 0, "data_type": "int", "data_type_obj": int_type, "size": 4},
        {"name": "param_2", "index": 1, "data_type": "int", "data_type_obj": int_type, "size": 4},
    ]
    analysis.returns = [
        ReturnInfo(
            address="00100104",
            value=_const(0),
            conditions=[Condition(Expression.binary_op("INT_SLESS", n_expr, _const(1)), False)],
            branch_index=0,
        ),
        ReturnInfo(
            address="00100104",
            value=positive_value,
            conditions=[Condition(Expression.binary_op("INT_SLESS", _const(0), n_expr), False)],
            branch_index=1,
        ),
        ReturnInfo(
            address="00100104",
            value=Expression.binary_op("SUBPIECE", Expression.constant(literal_base, size=8), _const(0)),
            conditions=[
                Condition(Expression.binary_op("INT_EQUAL", n_expr, _const(0)), False),
                Condition(Expression.binary_op("INT_SLESS", _const(0), n_expr), False),
            ],
            branch_index=2,
        ),
    ]
    analysis.incomplete_control_flow = False
    analysis.effect_summary = None

    summary = summarizer._try_summarize_vectorized_affine_progression_sum(
        _FakeFunction("f"),
        _FakeCfgHighFunction([]),
        analysis,
    )

    assert summary is not None
    returns, note = summary
    assert note == "vectorized_affine_progression_sum_summary"
    runtime_ref = getattr(returns[1].value, "runtime_ref", None)
    assert runtime_ref is not None
    assert runtime_ref.residue_cases == ((1, 0, 5, 0),)
    assert runtime_ref.residue_bias_terms
    assert runtime_ref.residue_bias_terms[0][2].equals(bias_plus_lane_base)


def test_vectorized_affine_progression_literal_summary_rejects_parameter_bias_without_lane_base():
    ram_space = _FakeAddressSpace("ram", space_id=1, is_memory=True)
    literal_base = 0x100120
    literal_bytes = bytes(
        byte
        for value in (2, 7, 12, 17)
        for byte in int(value).to_bytes(4, "little", signed=True)
    )
    program = _FakeProgram(
        _FakeAddressFactory({1: ram_space}, default_space=ram_space),
        memory=_FakeMemory(
            [_FakeMemoryBlock(literal_base, literal_base + len(literal_bytes) - 1, execute=False)],
            bytes_by_address={
                literal_base + offset: byte
                for offset, byte in enumerate(literal_bytes)
            },
        ),
    )
    tracer = _FakeTracer("f", _const(0), program=program)
    summarizer = StructuralRecurrenceSummarizer(tracer, debug=False)
    n_expr = Expression.parameter("param_1", index=0, data_type="int", size=4)
    bias_expr = Expression.parameter("param_2", index=1, data_type="int", size=4)
    positive_value = summarizer._build_affine_progression_sum_closed_expression(
        count_expr=n_expr,
        step=5,
        bias_expr=bias_expr,
        result_size=4,
    )
    assert positive_value is not None
    analysis = type("FakeAnalysis", (), {})()
    int_type = _FakeIntDataType()
    analysis.parameters = [
        {"name": "param_1", "index": 0, "data_type": "int", "data_type_obj": int_type, "size": 4},
        {"name": "param_2", "index": 1, "data_type": "int", "data_type_obj": int_type, "size": 4},
    ]
    analysis.returns = [
        ReturnInfo(
            address="00100104",
            value=_const(0),
            conditions=[Condition(Expression.binary_op("INT_SLESS", n_expr, _const(1)), False)],
            branch_index=0,
        ),
        ReturnInfo(
            address="00100104",
            value=positive_value,
            conditions=[Condition(Expression.binary_op("INT_SLESS", _const(0), n_expr), False)],
            branch_index=1,
        ),
        ReturnInfo(
            address="00100104",
            value=Expression.binary_op("SUBPIECE", Expression.constant(literal_base, size=8), _const(0)),
            conditions=[
                Condition(Expression.binary_op("INT_EQUAL", n_expr, _const(0)), False),
                Condition(Expression.binary_op("INT_SLESS", _const(0), n_expr), False),
            ],
            branch_index=2,
        ),
    ]
    analysis.incomplete_control_flow = False
    analysis.effect_summary = None

    assert summarizer._try_summarize_vectorized_affine_progression_sum(
        _FakeFunction("f"),
        _FakeCfgHighFunction([]),
        analysis,
    ) is None


def test_vectorized_affine_progression_literal_summary_uses_negative_lane_base_for_single_parameter():
    ram_space = _FakeAddressSpace("ram", space_id=1, is_memory=True)
    literal_base = 0x100120
    literal_bytes = bytes(
        byte
        for value in (-2, 3, 8, 13)
        for byte in int(value).to_bytes(4, "little", signed=True)
    )
    program = _FakeProgram(
        _FakeAddressFactory({1: ram_space}, default_space=ram_space),
        memory=_FakeMemory(
            [_FakeMemoryBlock(literal_base, literal_base + len(literal_bytes) - 1, execute=False)],
            bytes_by_address={
                literal_base + offset: byte
                for offset, byte in enumerate(literal_bytes)
            },
        ),
    )
    tracer = _FakeTracer("f", _const(0), program=program)
    summarizer = StructuralRecurrenceSummarizer(tracer, debug=False)
    n_expr = Expression.parameter("param_1", index=0, data_type="int", size=4)
    lane_base_expr = Expression.constant(-2, size=4)
    positive_value = summarizer._build_affine_progression_sum_closed_expression(
        count_expr=n_expr,
        step=5,
        bias_expr=lane_base_expr,
        result_size=4,
    )
    assert positive_value is not None
    analysis = type("FakeAnalysis", (), {})()
    int_type = _FakeIntDataType()
    analysis.parameters = [
        {"name": "param_1", "index": 0, "data_type": "int", "data_type_obj": int_type, "size": 4},
    ]
    analysis.returns = [
        ReturnInfo(
            address="00100104",
            value=_const(0),
            conditions=[Condition(Expression.binary_op("INT_SLESS", n_expr, _const(1)), False)],
            branch_index=0,
        ),
        ReturnInfo(
            address="00100104",
            value=positive_value,
            conditions=[Condition(Expression.binary_op("INT_SLESS", _const(0), n_expr), False)],
            branch_index=1,
        ),
        ReturnInfo(
            address="00100104",
            value=Expression.binary_op("SUBPIECE", Expression.constant(literal_base, size=8), _const(0)),
            conditions=[
                Condition(Expression.binary_op("INT_EQUAL", n_expr, _const(0)), False),
                Condition(Expression.binary_op("INT_SLESS", _const(0), n_expr), False),
            ],
            branch_index=2,
        ),
    ]
    analysis.incomplete_control_flow = False
    analysis.effect_summary = None

    summary = summarizer._try_summarize_vectorized_affine_progression_sum(
        _FakeFunction("f"),
        _FakeCfgHighFunction([]),
        analysis,
    )

    assert summary is not None
    returns, note = summary
    assert note == "vectorized_affine_progression_sum_summary"
    runtime_ref = getattr(returns[1].value, "runtime_ref", None)
    assert runtime_ref is not None
    assert runtime_ref.residue_cases == ((1, 0, 5, 0),)
    assert runtime_ref.residue_bias_terms
    assert runtime_ref.residue_bias_terms[0][2].equals(lane_base_expr)


def test_vectorized_affine_progression_literal_summary_rejects_parameter_bias_without_negative_lane_base():
    ram_space = _FakeAddressSpace("ram", space_id=1, is_memory=True)
    literal_base = 0x100120
    literal_bytes = bytes(
        byte
        for value in (-2, 3, 8, 13)
        for byte in int(value).to_bytes(4, "little", signed=True)
    )
    program = _FakeProgram(
        _FakeAddressFactory({1: ram_space}, default_space=ram_space),
        memory=_FakeMemory(
            [_FakeMemoryBlock(literal_base, literal_base + len(literal_bytes) - 1, execute=False)],
            bytes_by_address={
                literal_base + offset: byte
                for offset, byte in enumerate(literal_bytes)
            },
        ),
    )
    tracer = _FakeTracer("f", _const(0), program=program)
    summarizer = StructuralRecurrenceSummarizer(tracer, debug=False)
    n_expr = Expression.parameter("param_1", index=0, data_type="int", size=4)
    bias_expr = Expression.parameter("param_2", index=1, data_type="int", size=4)
    positive_value = summarizer._build_affine_progression_sum_closed_expression(
        count_expr=n_expr,
        step=5,
        bias_expr=bias_expr,
        result_size=4,
    )
    assert positive_value is not None
    analysis = type("FakeAnalysis", (), {})()
    int_type = _FakeIntDataType()
    analysis.parameters = [
        {"name": "param_1", "index": 0, "data_type": "int", "data_type_obj": int_type, "size": 4},
        {"name": "param_2", "index": 1, "data_type": "int", "data_type_obj": int_type, "size": 4},
    ]
    analysis.returns = [
        ReturnInfo(
            address="00100104",
            value=_const(0),
            conditions=[Condition(Expression.binary_op("INT_SLESS", n_expr, _const(1)), False)],
            branch_index=0,
        ),
        ReturnInfo(
            address="00100104",
            value=positive_value,
            conditions=[Condition(Expression.binary_op("INT_SLESS", _const(0), n_expr), False)],
            branch_index=1,
        ),
        ReturnInfo(
            address="00100104",
            value=Expression.binary_op("SUBPIECE", Expression.constant(literal_base, size=8), _const(0)),
            conditions=[
                Condition(Expression.binary_op("INT_EQUAL", n_expr, _const(0)), False),
                Condition(Expression.binary_op("INT_SLESS", _const(0), n_expr), False),
            ],
            branch_index=2,
        ),
    ]
    analysis.incomplete_control_flow = False
    analysis.effect_summary = None

    assert summarizer._try_summarize_vectorized_affine_progression_sum(
        _FakeFunction("f"),
        _FakeCfgHighFunction([]),
        analysis,
    ) is None


def test_vectorized_affine_progression_literal_summary_builds_unsigned_counted_loop_sum():
    ram_space = _FakeAddressSpace("ram", space_id=1, is_memory=True)
    literal_base = 0x100120
    literal_bytes = bytes(
        byte
        for value in (0, 5, 10, 15)
        for byte in int(value).to_bytes(4, "little", signed=True)
    )
    program = _FakeProgram(
        _FakeAddressFactory({1: ram_space}, default_space=ram_space),
        memory=_FakeMemory(
            [_FakeMemoryBlock(literal_base, literal_base + len(literal_bytes) - 1, execute=False)],
            bytes_by_address={
                literal_base + offset: byte
                for offset, byte in enumerate(literal_bytes)
            },
        ),
    )
    tracer = _FakeTracer("f", _const(0), program=program)
    summarizer = StructuralRecurrenceSummarizer(tracer, debug=False)
    n_expr = Expression.parameter("param_1", index=0, data_type="uint", size=4)
    bias_expr = Expression.parameter("param_2", index=1, data_type="int", size=4)
    positive_value = summarizer._build_affine_progression_sum_closed_expression(
        count_expr=n_expr,
        step=5,
        bias_expr=bias_expr,
        result_size=4,
        signed_count=False,
    )
    assert positive_value is not None
    zero_case = ReturnInfo(
        address="00100104",
        value=_const(0),
        conditions=[Condition(Expression.binary_op("INT_LESS", n_expr, _const(1)), False)],
        branch_index=0,
    )
    positive_case = ReturnInfo(
        address="00100104",
        value=positive_value,
        conditions=[Condition(Expression.binary_op("INT_LESS", _const(0), n_expr), False)],
        branch_index=1,
    )
    literal_probe_case = ReturnInfo(
        address="00100104",
        value=Expression.binary_op("SUBPIECE", Expression.constant(literal_base, size=8), _const(0)),
        conditions=[
            Condition(Expression.binary_op("INT_EQUAL", n_expr, _const(0)), False),
            Condition(Expression.binary_op("INT_LESS", _const(0), n_expr), False),
        ],
        branch_index=2,
    )
    analysis = type("FakeAnalysis", (), {})()
    int_type = _FakeIntDataType()
    analysis.parameters = [
        {"name": "param_1", "index": 0, "data_type": "uint", "data_type_obj": int_type, "size": 4},
        {"name": "param_2", "index": 1, "data_type": "int", "data_type_obj": int_type, "size": 4},
    ]
    analysis.returns = [zero_case, positive_case, literal_probe_case]
    analysis.incomplete_control_flow = False
    analysis.effect_summary = None

    summary = summarizer._try_summarize_vectorized_affine_progression_sum(
        _FakeFunction("f"),
        _FakeCfgHighFunction([]),
        analysis,
    )

    assert summary is not None
    returns, _note = summary
    positive_guard = returns[1].conditions[0]
    assert positive_guard.expression.operator == "INT_LESS"
    runtime_ref = getattr(returns[1].value, "runtime_ref", None)
    assert runtime_ref is not None
    assert runtime_ref.signed_loop is False


def test_vectorized_affine_progression_literal_summary_rejects_signed_local_bias_candidate_mismatch():
    ram_space = _FakeAddressSpace("ram", space_id=1, is_memory=True)
    literal_base = 0x100120
    literal_bytes = bytes(
        byte
        for value in (0, 5, 10, 15)
        for byte in int(value).to_bytes(4, "little", signed=True)
    )
    program = _FakeProgram(
        _FakeAddressFactory({1: ram_space}, default_space=ram_space),
        memory=_FakeMemory(
            [_FakeMemoryBlock(literal_base, literal_base + len(literal_bytes) - 1, execute=False)],
            bytes_by_address={
                literal_base + offset: byte
                for offset, byte in enumerate(literal_bytes)
            },
        ),
    )
    tracer = _FakeTracer("f", _const(0), program=program)
    summarizer = StructuralRecurrenceSummarizer(tracer, debug=False)
    n_expr = Expression.parameter("param_1", index=0, data_type="int", size=4)
    primary_unsigned_bias = Expression.parameter("param_2", index=1, data_type="uint16_t", size=2)
    signed_local_bias = Expression.parameter("param_2", index=1, data_type="short", size=2)
    positive_value = summarizer._build_affine_progression_sum_closed_expression(
        count_expr=n_expr,
        step=5,
        bias_expr=signed_local_bias,
        result_size=4,
    )
    assert positive_value is not None
    analysis = type("FakeAnalysis", (), {})()
    int_type = _FakeIntDataType()
    analysis.parameters = [
        {"name": "param_1", "index": 0, "data_type": "int", "data_type_obj": int_type, "size": 4},
        {"name": "param_2", "index": 1, "data_type": "uint16_t", "data_type_obj": int_type, "size": 2},
    ]
    analysis.returns = [
        ReturnInfo(
            address="00100104",
            value=_const(0),
            conditions=[Condition(Expression.binary_op("INT_SLESS", n_expr, _const(1)), False)],
            branch_index=0,
        ),
        ReturnInfo(
            address="00100104",
            value=positive_value,
            conditions=[Condition(Expression.binary_op("INT_SLESS", _const(0), n_expr), False)],
            branch_index=1,
        ),
        ReturnInfo(
            address="00100104",
            value=Expression.binary_op("SUBPIECE", Expression.constant(literal_base, size=8), _const(0)),
            conditions=[
                Condition(Expression.binary_op("INT_EQUAL", n_expr, _const(0)), False),
                Condition(Expression.binary_op("INT_SLESS", _const(0), n_expr), False),
            ],
            branch_index=2,
        ),
    ]
    analysis.incomplete_control_flow = False
    analysis.effect_summary = None

    assert summarizer._try_summarize_vectorized_affine_progression_sum(
        _FakeFunction("f"),
        _FakeCfgHighFunction([]),
        analysis,
    ) is None
    assert not primary_unsigned_bias.equals(signed_local_bias) or (
        primary_unsigned_bias.data_type != signed_local_bias.data_type
    )


def test_vectorized_affine_progression_literal_summary_rejects_unproved_positive_return():
    ram_space = _FakeAddressSpace("ram", space_id=1, is_memory=True)
    literal_base = 0x100120
    literal_bytes = bytes(
        byte
        for value in (0, 5, 10, 15)
        for byte in int(value).to_bytes(4, "little", signed=True)
    )
    program = _FakeProgram(
        _FakeAddressFactory({1: ram_space}, default_space=ram_space),
        memory=_FakeMemory(
            [_FakeMemoryBlock(literal_base, literal_base + len(literal_bytes) - 1, execute=False)],
            bytes_by_address={
                literal_base + offset: byte
                for offset, byte in enumerate(literal_bytes)
            },
        ),
    )
    tracer = _FakeTracer("f", _const(0), program=program)
    summarizer = StructuralRecurrenceSummarizer(tracer, debug=False)
    n_expr = Expression.parameter("param_1", index=0, data_type="int", size=4)
    analysis = type("FakeAnalysis", (), {})()
    int_type = _FakeIntDataType()
    analysis.parameters = [
        {"name": "param_1", "index": 0, "data_type": "uint", "data_type_obj": int_type, "size": 4},
        {"name": "param_2", "index": 1, "data_type": "int", "data_type_obj": int_type, "size": 4},
    ]
    analysis.returns = [
        ReturnInfo(
            address="00100104",
            value=_const(0),
            conditions=[Condition(Expression.binary_op("INT_LESS", n_expr, _const(1)), False)],
            branch_index=0,
        ),
        ReturnInfo(
            address="00100104",
            value=Expression.binary_op(
                "INT_ADD",
                Expression.parameter("param_2", index=1, data_type="int", size=4),
                Expression.binary_op("SUBPIECE", Expression.constant(literal_base, size=8), _const(0)),
            ),
            conditions=[Condition(Expression.binary_op("INT_SLESS", _const(0), n_expr), False)],
            branch_index=1,
        ),
    ]
    analysis.incomplete_control_flow = False
    analysis.effect_summary = None

    assert summarizer._try_summarize_vectorized_affine_progression_sum(
        _FakeFunction("f"),
        _FakeCfgHighFunction([]),
        analysis,
    ) is None


def test_vectorized_affine_progression_literal_summary_rejects_unknown_positive_overlap():
    ram_space = _FakeAddressSpace("ram", space_id=1, is_memory=True)
    literal_base = 0x100120
    literal_bytes = bytes(
        byte
        for value in (0, 5, 10, 15)
        for byte in int(value).to_bytes(4, "little", signed=True)
    )
    program = _FakeProgram(
        _FakeAddressFactory({1: ram_space}, default_space=ram_space),
        memory=_FakeMemory(
            [_FakeMemoryBlock(literal_base, literal_base + len(literal_bytes) - 1, execute=False)],
            bytes_by_address={
                literal_base + offset: byte
                for offset, byte in enumerate(literal_bytes)
            },
        ),
    )
    tracer = _FakeTracer("f", _const(0), program=program)
    summarizer = StructuralRecurrenceSummarizer(tracer, debug=False)
    n_expr = Expression.parameter("param_1", index=0, data_type="int", size=4)
    bias_expr = Expression.parameter("param_2", index=1, data_type="int", size=4)
    positive_value = summarizer._build_affine_progression_sum_closed_expression(
        count_expr=n_expr,
        step=5,
        bias_expr=bias_expr,
        result_size=4,
    )
    assert positive_value is not None
    opaque_guard = Expression.binary_op(
        "INT_SLESS",
        Expression.constant(0, size=4),
        Expression.variable("opaque_positive_guard", size=4),
    )
    analysis = type("FakeAnalysis", (), {})()
    int_type = _FakeIntDataType()
    analysis.parameters = [
        {"name": "param_1", "index": 0, "data_type": "int", "data_type_obj": int_type, "size": 4},
        {"name": "param_2", "index": 1, "data_type": "int", "data_type_obj": int_type, "size": 4},
    ]
    analysis.returns = [
        ReturnInfo(
            address="00100104",
            value=_const(0),
            conditions=[Condition(Expression.binary_op("INT_LESS", n_expr, _const(1)), False)],
            branch_index=0,
        ),
        ReturnInfo(
            address="00100104",
            value=positive_value,
            conditions=[Condition(Expression.binary_op("INT_SLESS", _const(0), n_expr), False)],
            branch_index=1,
        ),
        ReturnInfo(
            address="00100104",
            value=_const(123),
            conditions=[Condition(opaque_guard, False)],
            branch_index=2,
        ),
        ReturnInfo(
            address="00100104",
            value=Expression.binary_op("SUBPIECE", Expression.constant(literal_base, size=8), _const(0)),
            conditions=[
                Condition(Expression.binary_op("INT_EQUAL", n_expr, _const(0)), False),
                Condition(Expression.binary_op("INT_SLESS", _const(0), n_expr), False),
            ],
            branch_index=3,
        ),
    ]
    analysis.incomplete_control_flow = False
    analysis.effect_summary = None

    assert summarizer._try_summarize_vectorized_affine_progression_sum(
        _FakeFunction("f"),
        _FakeCfgHighFunction([]),
        analysis,
    ) is None


def test_vectorized_affine_progression_literal_summary_rejects_incomplete_zero_base_cover():
    ram_space = _FakeAddressSpace("ram", space_id=1, is_memory=True)
    literal_base = 0x100120
    literal_bytes = bytes(
        byte
        for value in (0, 5, 10, 15)
        for byte in int(value).to_bytes(4, "little", signed=True)
    )
    program = _FakeProgram(
        _FakeAddressFactory({1: ram_space}, default_space=ram_space),
        memory=_FakeMemory(
            [_FakeMemoryBlock(literal_base, literal_base + len(literal_bytes) - 1, execute=False)],
            bytes_by_address={
                literal_base + offset: byte
                for offset, byte in enumerate(literal_bytes)
            },
        ),
    )
    tracer = _FakeTracer("f", _const(0), program=program)
    summarizer = StructuralRecurrenceSummarizer(tracer, debug=False)
    n_expr = Expression.parameter("param_1", index=0, data_type="int", size=4)
    bias_expr = Expression.parameter("param_2", index=1, data_type="int", size=4)
    positive_value = summarizer._build_affine_progression_sum_closed_expression(
        count_expr=n_expr,
        step=5,
        bias_expr=bias_expr,
        result_size=4,
    )
    assert positive_value is not None
    analysis = type("FakeAnalysis", (), {})()
    int_type = _FakeIntDataType()
    analysis.parameters = [
        {"name": "param_1", "index": 0, "data_type": "int", "data_type_obj": int_type, "size": 4},
        {"name": "param_2", "index": 1, "data_type": "int", "data_type_obj": int_type, "size": 4},
    ]
    analysis.returns = [
        ReturnInfo(
            address="00100104",
            value=_const(0),
            conditions=[Condition(Expression.binary_op("INT_EQUAL", n_expr, _const(0)), False)],
            branch_index=0,
        ),
        ReturnInfo(
            address="00100104",
            value=_const(7),
            conditions=[Condition(Expression.binary_op("INT_SLESS", n_expr, _const(0)), False)],
            branch_index=1,
        ),
        ReturnInfo(
            address="00100104",
            value=positive_value,
            conditions=[Condition(Expression.binary_op("INT_SLESS", _const(0), n_expr), False)],
            branch_index=2,
        ),
    ]
    analysis.incomplete_control_flow = False
    analysis.effect_summary = None

    assert summarizer._try_summarize_vectorized_affine_progression_sum(
        _FakeFunction("f"),
        _FakeCfgHighFunction([]),
        analysis,
    ) is None


def test_vectorized_affine_progression_literal_summary_rejects_nonzero_base_overlap():
    ram_space = _FakeAddressSpace("ram", space_id=1, is_memory=True)
    literal_base = 0x100120
    literal_bytes = bytes(
        byte
        for value in (0, 5, 10, 15)
        for byte in int(value).to_bytes(4, "little", signed=True)
    )
    program = _FakeProgram(
        _FakeAddressFactory({1: ram_space}, default_space=ram_space),
        memory=_FakeMemory(
            [_FakeMemoryBlock(literal_base, literal_base + len(literal_bytes) - 1, execute=False)],
            bytes_by_address={
                literal_base + offset: byte
                for offset, byte in enumerate(literal_bytes)
            },
        ),
    )
    tracer = _FakeTracer("f", _const(0), program=program)
    summarizer = StructuralRecurrenceSummarizer(tracer, debug=False)
    n_expr = Expression.parameter("param_1", index=0, data_type="int", size=4)
    bias_expr = Expression.parameter("param_2", index=1, data_type="int", size=4)
    positive_value = summarizer._build_affine_progression_sum_closed_expression(
        count_expr=n_expr,
        step=5,
        bias_expr=bias_expr,
        result_size=4,
    )
    assert positive_value is not None
    analysis = type("FakeAnalysis", (), {})()
    int_type = _FakeIntDataType()
    analysis.parameters = [
        {"name": "param_1", "index": 0, "data_type": "int", "data_type_obj": int_type, "size": 4},
        {"name": "param_2", "index": 1, "data_type": "int", "data_type_obj": int_type, "size": 4},
    ]
    analysis.returns = [
        ReturnInfo(
            address="00100104",
            value=_const(0),
            conditions=[Condition(Expression.binary_op("INT_SLESS", n_expr, _const(1)), False)],
            branch_index=0,
        ),
        ReturnInfo(
            address="00100104",
            value=_const(7),
            conditions=[Condition(Expression.binary_op("INT_SLESS", n_expr, _const(0)), False)],
            branch_index=1,
        ),
        ReturnInfo(
            address="00100104",
            value=positive_value,
            conditions=[Condition(Expression.binary_op("INT_SLESS", _const(0), n_expr), False)],
            branch_index=2,
        ),
    ]
    analysis.incomplete_control_flow = False
    analysis.effect_summary = None

    assert summarizer._try_summarize_vectorized_affine_progression_sum(
        _FakeFunction("f"),
        _FakeCfgHighFunction([]),
        analysis,
    ) is None


def test_vectorized_affine_progression_literal_summary_rejects_memory_effects():
    ram_space = _FakeAddressSpace("ram", space_id=1, is_memory=True)
    literal_base = 0x100120
    literal_bytes = bytes(
        byte
        for value in (0, 5, 10, 15)
        for byte in int(value).to_bytes(4, "little", signed=True)
    )
    program = _FakeProgram(
        _FakeAddressFactory({1: ram_space}, default_space=ram_space),
        memory=_FakeMemory(
            [_FakeMemoryBlock(literal_base, literal_base + len(literal_bytes) - 1, execute=False)],
            bytes_by_address={
                literal_base + offset: byte
                for offset, byte in enumerate(literal_bytes)
            },
        ),
    )
    summarizer = StructuralRecurrenceSummarizer(
        _FakeTracer("f", _const(0), program=program),
        debug=False,
    )
    n_expr = Expression.parameter("param_1", index=0, data_type="int", size=4)
    bias_expr = Expression.parameter("param_2", index=1, data_type="int", size=4)
    positive_value = summarizer._build_affine_progression_sum_closed_expression(
        count_expr=n_expr,
        step=5,
        bias_expr=bias_expr,
        result_size=4,
    )
    assert positive_value is not None
    analysis = type("FakeAnalysis", (), {})()
    int_type = _FakeIntDataType()
    analysis.parameters = [
        {"name": "param_1", "index": 0, "data_type": "int", "data_type_obj": int_type, "size": 4},
        {"name": "param_2", "index": 1, "data_type": "int", "data_type_obj": int_type, "size": 4},
    ]
    analysis.returns = [
        ReturnInfo(
            address="00100104",
            value=_const(0),
            conditions=[Condition(Expression.binary_op("INT_LESS", n_expr, _const(1)), False)],
            branch_index=0,
        ),
        ReturnInfo(
            address="00100104",
            value=positive_value,
            conditions=[Condition(Expression.binary_op("INT_SLESS", _const(0), n_expr), False)],
            branch_index=1,
        ),
    ]
    analysis.incomplete_control_flow = False
    analysis.effect_summary = EffectSummary(
        parameter_names=["param_1", "param_2"],
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

    assert summarizer._try_summarize_vectorized_affine_progression_sum(
        _FakeFunction("f"),
        _FakeCfgHighFunction([]),
        analysis,
    ) is None


def test_vectorized_affine_progression_literal_summary_rejects_high_function_effects():
    ram_space = _FakeAddressSpace("ram", space_id=1, is_memory=True)
    literal_base = 0x100120
    literal_bytes = bytes(
        byte
        for value in (0, 5, 10, 15)
        for byte in int(value).to_bytes(4, "little", signed=True)
    )
    program = _FakeProgram(
        _FakeAddressFactory({1: ram_space}, default_space=ram_space),
        memory=_FakeMemory(
            [_FakeMemoryBlock(literal_base, literal_base + len(literal_bytes) - 1, execute=False)],
            bytes_by_address={
                literal_base + offset: byte
                for offset, byte in enumerate(literal_bytes)
            },
        ),
    )
    summarizer = StructuralRecurrenceSummarizer(
        _FakeTracer("f", _const(0), program=program),
        debug=False,
    )
    n_expr = Expression.parameter("param_1", index=0, data_type="int", size=4)
    bias_expr = Expression.parameter("param_2", index=1, data_type="int", size=4)
    positive_value = summarizer._build_affine_progression_sum_closed_expression(
        count_expr=n_expr,
        step=5,
        bias_expr=bias_expr,
        result_size=4,
    )
    assert positive_value is not None
    analysis = type("FakeAnalysis", (), {})()
    int_type = _FakeIntDataType()
    analysis.parameters = [
        {"name": "param_1", "index": 0, "data_type": "int", "data_type_obj": int_type, "size": 4},
        {"name": "param_2", "index": 1, "data_type": "int", "data_type_obj": int_type, "size": 4},
    ]
    analysis.returns = [
        ReturnInfo(
            address="00100104",
            value=_const(0),
            conditions=[Condition(Expression.binary_op("INT_LESS", n_expr, _const(1)), False)],
            branch_index=0,
        ),
        ReturnInfo(
            address="00100104",
            value=positive_value,
            conditions=[Condition(Expression.binary_op("INT_SLESS", _const(0), n_expr), False)],
            branch_index=1,
        ),
        ReturnInfo(
            address="00100104",
            value=Expression.binary_op("SUBPIECE", Expression.constant(literal_base, size=8), _const(0)),
            conditions=[
                Condition(Expression.binary_op("INT_EQUAL", n_expr, _const(0)), False),
                Condition(Expression.binary_op("INT_SLESS", _const(0), n_expr), False),
            ],
            branch_index=2,
        ),
    ]
    analysis.incomplete_control_flow = False
    analysis.effect_summary = None
    store_op = _FakePcodeOp(
        "STORE",
        [
            _FakeStoreSpaceVarnode(target_space_id=1),
            _FakeVarnode("store_addr", expr=n_expr),
            _FakeVarnode("store_value", expr=_const(1)),
        ],
    )
    call_op = _FakePcodeOp("CALL", [_FakeVarnode("call_target")])
    branchind_op = _FakePcodeOp("BRANCHIND", [_FakeVarnode("branch_target")])

    for op in (store_op, call_op, branchind_op):
        assert summarizer._try_summarize_vectorized_affine_progression_sum(
            _FakeFunction("f"),
            _FakeCfgHighFunction([_FakeCfgBlock(1, [op])]),
            analysis,
        ) is None


def test_vectorized_affine_progression_literal_summary_rejects_missing_zero_base_case():
    ram_space = _FakeAddressSpace("ram", space_id=1, is_memory=True)
    literal_base = 0x100120
    literal_bytes = bytes(
        byte
        for value in (0, 5, 10, 15)
        for byte in int(value).to_bytes(4, "little", signed=True)
    )
    program = _FakeProgram(
        _FakeAddressFactory({1: ram_space}, default_space=ram_space),
        memory=_FakeMemory(
            [_FakeMemoryBlock(literal_base, literal_base + len(literal_bytes) - 1, execute=False)],
            bytes_by_address={
                literal_base + offset: byte
                for offset, byte in enumerate(literal_bytes)
            },
        ),
    )
    tracer = _FakeTracer("f", _const(0), program=program)
    summarizer = StructuralRecurrenceSummarizer(tracer, debug=False)
    analysis = type("FakeAnalysis", (), {})()
    int_type = _FakeIntDataType()
    analysis.parameters = [
        {"name": "param_1", "index": 0, "data_type": "int", "data_type_obj": int_type, "size": 4},
        {"name": "param_2", "index": 1, "data_type": "int", "data_type_obj": int_type, "size": 4},
    ]
    analysis.returns = [
        ReturnInfo(
            address="00100104",
            value=Expression.binary_op(
                "INT_ADD",
                Expression.parameter("param_2", index=1, data_type="int", size=4),
                Expression.binary_op("SUBPIECE", Expression.constant(literal_base, size=8), _const(0)),
            ),
            conditions=[],
            branch_index=0,
        )
    ]
    analysis.incomplete_control_flow = False
    analysis.effect_summary = None

    assert summarizer._try_summarize_vectorized_affine_progression_sum(
        _FakeFunction("f"),
        _FakeCfgHighFunction([]),
        analysis,
    ) is None


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


def test_pcode_op_ref_stable_key_collapses_distinct_wrappers_for_same_logical_pcode():
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
    ref1 = PcodeOpRef.from_pcode_op(op1)
    ref2 = PcodeOpRef.from_pcode_op(op2)

    assert ref1 is not None
    assert ref2 is not None
    assert ref1.stable_key() == ref2.stable_key()
    assert not hasattr(tracer, "_get_" + "stable_op_key")
    assert tracer._get_op_key(op1) != tracer._get_op_key(op2)


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


def test_readonly_exact_positive_return_order_prefers_self_consistent_prefix_terms():
    summarizer = StructuralRecurrenceSummarizer(PcodeTracer.__new__(PcodeTracer), debug=False)
    pointer_param = {"name": "param_1", "index": 0, "data_type": "int *", "size": 8}
    count_param = {"name": "param_2", "index": 1, "data_type": "int", "size": 4}
    analysis = create_mock_analysis(
        function_name="lmb_sum_prefix_wrong_tail",
        parameters=[pointer_param, count_param],
        returns=[],
    )
    count_expr = Expression.parameter("param_2", index=1, data_type="int", size=4)
    proof = _readonly_accumulator_proof(
        base_ref=LocationBaseRef.parameter("param_1", index=0),
        count_expr=count_expr,
        stride=4,
        element_size=4,
        result_size=4,
        witnesses=(
            ReadonlyReductionWitness(
                exact_count=3,
                terms=(
                    ReadonlyReductionTermRef(byte_offset=0, access_size=4),
                    ReadonlyReductionTermRef(byte_offset=4, access_size=4),
                    ReadonlyReductionTermRef(byte_offset=8, access_size=4),
                ),
            ),
        ),
    )
    conditions = [_cond("INT_EQUAL", count_expr, _const(3))]
    wrong_tail_artifact = ReturnInfo(
        address="0x3000",
        value=_sum_terms(
            _mem_ptradd_index("param_1", 0),
            _mem_ptradd_index("param_1", 2),
            _mem_ptradd_index("param_1", 3),
        ),
        conditions=conditions,
        branch_index=10,
    )
    exact_prefix = ReturnInfo(
        address="0x3000",
        value=_sum_terms(
            _mem_ptradd_index("param_1", 1),
            _mem_ptradd_index("param_1", 0),
            _mem_ptradd_index("param_1", 2),
        ),
        conditions=conditions,
        branch_index=11,
    )

    ordered = summarizer._order_readonly_exact_positive_returns(
        [wrong_tail_artifact, exact_prefix],
        analysis,
        pointer_param,
        count_param,
        proof,
    )

    assert ordered[0] is exact_prefix
    assert summarizer._readonly_exact_positive_return_prefix_score(
        analysis,
        pointer_param,
        exact_prefix,
        proof,
        exact_count=3,
    ) > summarizer._readonly_exact_positive_return_prefix_score(
        analysis,
        pointer_param,
        wrong_tail_artifact,
        proof,
        exact_count=3,
    )


def test_readonly_witness_synthesis_materializes_excluded_exact_prefix_count():
    summarizer = StructuralRecurrenceSummarizer(PcodeTracer.__new__(PcodeTracer), debug=False)
    pointer_param = {"name": "param_1", "index": 0, "data_type": "int *", "size": 8}
    count_param = {"name": "param_2", "index": 1, "data_type": "int", "size": 4}
    analysis = create_mock_analysis(
        function_name="lmb_sum_prefix_wrong_tail",
        parameters=[pointer_param, count_param],
        returns=[],
    )
    count_expr = Expression.parameter("param_2", index=1, data_type="int", size=4)
    witnesses = (
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
        ReadonlyReductionWitness(
            exact_count=3,
            terms=(
                ReadonlyReductionTermRef(byte_offset=0, access_size=4),
                ReadonlyReductionTermRef(byte_offset=4, access_size=4),
                ReadonlyReductionTermRef(byte_offset=8, access_size=4),
            ),
        ),
        ReadonlyReductionWitness(
            exact_count=4,
            terms=(
                ReadonlyReductionTermRef(byte_offset=0, access_size=4),
                ReadonlyReductionTermRef(byte_offset=4, access_size=4),
                ReadonlyReductionTermRef(byte_offset=8, access_size=4),
                ReadonlyReductionTermRef(byte_offset=12, access_size=4),
            ),
        ),
    )
    reduction_ref = ReadonlyReductionRef(
        reduction_kind="memory_sum",
        pointer_base_ref=LocationBaseRef.parameter("param_1", index=0),
        count_parameter_name="param_2",
        count_parameter_index=1,
        stride=4,
        element_size=4,
        result_size=4,
        semantic_witnesses=witnesses,
    )
    existing = [
        ReturnInfo(
            address="0x3000",
            value=_sum_terms(_mem_ptradd_index("param_1", 0), _mem_ptradd_index("param_1", 1)),
            conditions=[
                _cond("INT_EQUAL", count_expr, _const(2)),
            ],
            branch_index=20,
        )
    ]

    synthesized = summarizer._synthesize_exact_returns_from_readonly_witnesses(
        analysis,
        pointer_param,
        count_param,
        broad_positive_conditions=[_cond("INT_SLESSEQUAL", _const(1), count_expr)],
        summary_positive_conditions=[
            _cond("INT_SLESS", _const(3), count_expr),
        ],
        existing_returns=existing,
        reduction_ref=reduction_ref,
        result_size=4,
    )

    exact_count_values = [
        summarizer._exact_counter_value_from_conditions(ret.conditions or [], "param_2")
        for ret in synthesized
    ]
    assert 3 in exact_count_values
    assert 4 not in exact_count_values


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
            StoreEffect(_loc("trace", 0, 4), Expression.binary_op("INT_ADD", _mem("trace", 0), _param("start")), even_conditions, 1),
            StoreEffect(_loc("trace", 4, 4), Expression.binary_op("INT_ADD", _mem("trace", 4), _const(1)), even_conditions, 2),
            StoreEffect(_loc("trace", 0, 4), Expression.binary_op("INT_ADD", _mem("trace", 0), Expression.unary_op("INT_2COMP", _param("start"))), odd_conditions, 3),
            StoreEffect(_loc("trace", 4, 4), Expression.binary_op("INT_ADD", _mem("trace", 4), _const(1)), odd_conditions, 4),
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
            StoreEffect(_loc("trace", 0, 4), Expression.binary_op("INT_ADD", _mem("trace", 0), _param("start")), even_conditions, 1),
            StoreEffect(_loc("trace", 4, 4), Expression.binary_op("INT_ADD", _mem("trace", 4), _const(1)), even_conditions, 2),
            StoreEffect(_loc("trace", 0, 4), Expression.binary_op("INT_ADD", _mem("trace", 0), Expression.unary_op("INT_2COMP", _param("start"))), odd_conditions, 3),
            StoreEffect(_loc("trace", 4, 4), Expression.binary_op("INT_ADD", _mem("trace", 4), _const(1)), odd_conditions, 4),
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
                _loc("param_1", 0, 4),
                Expression.binary_op("INT_ADD", _mem("param_1", 0), Expression.unary_op("INT_2COMP", _param("param_2"))),
                odd_conditions,
                1,
            ),
            StoreEffect(
                _loc("param_1", 4, 4),
                Expression.binary_op("INT_ADD", _mem_mul_offset("param_1", 4), _const(1)),
                odd_conditions,
                2,
            ),
            StoreEffect(
                _loc("param_1", 0, 4),
                Expression.binary_op("INT_ADD", _mem("param_1", 0), _param("param_2")),
                even_conditions,
                3,
            ),
            StoreEffect(
                _loc("param_1", 4, 4),
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
                _loc("param_1", 0, 4),
                Expression.binary_op("INT_ADD", _mem("param_1", 0), Expression.unary_op("INT_2COMP", _param("param_2"))),
                odd_conditions,
                1,
            ),
            StoreEffect(
                _loc("param_1", 4, 4),
                Expression.binary_op("INT_ADD", _mem("param_1", 4), _const(1)),
                odd_conditions,
                2,
            ),
            StoreEffect(
                _loc("param_1", 0, 4),
                Expression.binary_op("INT_ADD", _mem("param_1", 0), _param("param_2")),
                even_conditions,
                3,
            ),
            StoreEffect(
                _loc("param_1", 4, 4),
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
                _loc("param_1", 0, 4),
                Expression.binary_op("INT_ADD", _mem("param_1", 0), Expression.unary_op("INT_2COMP", _param("param_2"))),
                odd_conditions,
                1,
            ),
            StoreEffect(
                _loc("param_1", 4, 4),
                Expression.binary_op("INT_ADD", _mem_mul_offset("param_1", 4), _const(1)),
                odd_conditions,
                2,
            ),
            StoreEffect(
                _loc("param_1", 0, 4),
                Expression.binary_op("INT_ADD", _mem("param_1", 0), _param("param_2")),
                even_conditions,
                3,
            ),
            StoreEffect(
                _loc("param_1", 4, 4),
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
                _loc("param_1", 0, 4),
                Expression.binary_op(
                    "INT_ADD",
                    odd_phi_base,
                    Expression.unary_op("INT_2COMP", _param("param_2")),
                ),
                odd_conditions,
                1,
            ),
            StoreEffect(
                _loc("param_1", 4, 4),
                Expression.binary_op("INT_ADD", _mem_mul_offset("param_1", 4), _const(1)),
                odd_conditions,
                2,
            ),
            StoreEffect(
                _loc("param_1", 0, 4),
                Expression.binary_op("INT_ADD", even_phi_base, _param("param_2")),
                even_conditions,
                3,
            ),
            StoreEffect(
                _loc("param_1", 4, 4),
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


def test_readonly_reduction_summary_accepts_sign_extended_load_when_return_width_is_low_lane():
    params = [
        {"name": "param_1", "index": 0, "data_type": "int *", "size": 8},
        {"name": "param_2", "index": 1, "data_type": "int", "size": 4, "is_signed": True},
    ]
    pointer_expr = Expression.parameter("param_1", index=0, data_type="int *", size=8)
    count_expr = Expression.parameter("param_2", index=1, data_type="int", size=4)
    analysis = create_mock_analysis(
        "signed_load_prefix",
        return_type="int",
        parameters=params,
        returns=[
            ReturnInfo(
                address="0x1000",
                value=_const(-300),
                conditions=[_cond("INT_EQUAL", pointer_expr, Expression.constant(0, size=8))],
            ),
            ReturnInfo(
                address="0x1004",
                value=_const(-300),
                conditions=[
                    _cond("INT_NOTEQUAL", pointer_expr, Expression.constant(0, size=8)),
                    _cond("INT_SLESSEQUAL", count_expr, _const(0)),
                ],
            ),
            ReturnInfo(
                address="0x1008",
                value=Expression.unknown("phi_circular"),
                conditions=[
                    _cond("INT_NOTEQUAL", pointer_expr, Expression.constant(0, size=8)),
                    _cond("INT_SLESS", _const(0), count_expr),
                ],
            ),
        ],
    )
    analysis.returns[2].value.size = 4

    ptr_param = _FakeVarnode("param_1", size=8, expr=pointer_expr)
    count_param = _FakeVarnode("param_2", size=4, expr=count_expr)
    zero32 = _FakeVarnode("zero32", size=4, expr=Expression.constant(0, 4))
    one32 = _FakeVarnode("one32", size=4, expr=Expression.constant(1, 4))
    four64 = _FakeVarnode("four64", size=8, expr=Expression.constant(4, 8))
    ram_space = _FakeVarnode("ram", size=8, expr=Expression.constant(0, 8))

    idx_phi = _FakeVarnode("idx_phi", size=4, high=_FakeHighVar("idx"))
    idx_next = _FakeVarnode("idx_next", size=4)
    idx_add_op = _FakePcodeOp("INT_ADD", [idx_phi, one32], idx_next)
    idx_phi_op = _FakePcodeOp("MULTIEQUAL", [zero32, idx_next], idx_phi)

    idx_sext = _FakeVarnode("idx_sext", size=8)
    idx_sext_op = _FakePcodeOp("INT_SEXT", [idx_phi], idx_sext)
    scaled_idx = _FakeVarnode("scaled_idx", size=8)
    scale_op = _FakePcodeOp("INT_MULT", [idx_sext, four64], scaled_idx)
    addr = _FakeVarnode("addr", size=8)
    addr_op = _FakePcodeOp("INT_ADD", [ptr_param, scaled_idx], addr)
    load_value = _FakeVarnode("load_value", size=4)
    load_op = _FakePcodeOp("LOAD", [ram_space, addr], load_value)
    signed_load = _FakeVarnode("signed_load", size=8)
    signed_load_op = _FakePcodeOp("INT_SEXT", [load_value], signed_load)

    acc_phi = _FakeVarnode("acc_phi", size=8, high=_FakeHighVar("acc"))
    acc_next = _FakeVarnode("acc_next", size=8)
    acc_add_op = _FakePcodeOp("INT_ADD", [acc_phi, signed_load], acc_next)
    acc_phi_op = _FakePcodeOp("MULTIEQUAL", [zero32, acc_next], acc_phi)

    high_function = _FakeHighFunction(
        [
            idx_add_op,
            idx_phi_op,
            idx_sext_op,
            scale_op,
            addr_op,
            load_op,
            signed_load_op,
            acc_add_op,
            acc_phi_op,
        ]
    )
    tracer = _FakeTracer("unused", _const(0))
    tracer.trace_varnode = lambda varnode, *args, **kwargs: getattr(varnode, "_expr", None)

    summarizer = StructuralRecurrenceSummarizer(tracer, debug=False)
    summary = summarizer.try_summarize_function(
        _FakeFunction("signed_load_prefix"),
        high_function,
        analysis,
    )

    assert summary is not None
    summarized_returns, note = summary
    assert note == "readonly_pointer_reduction_summary"
    readonly_return = next(ret for ret in summarized_returns if ret.value.expr_type == ExpressionType.INTRINSIC)
    proof = readonly_return.value.runtime_ref.accumulator_proof
    assert proof is not None
    assert proof.result_size == 4
    assert proof.element_size == 4
    assert proof.start_index == 0
    assert tuple(term.byte_offset for term in (proof.full_terms_for_count_value(2) or ())) == (0, 4)


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


def test_readonly_reduction_summary_preserves_non_prefix_pre_loop_seed_terms():
    params = [
        {"name": "param_1", "index": 0, "data_type": "int *", "size": 8},
        {"name": "param_2", "index": 1, "data_type": "int", "size": 4, "is_signed": True},
    ]
    ptr_param = Expression.parameter("param_1", index=0, data_type="int *", size=8)
    count_param = Expression.parameter("param_2", index=1, data_type="int", size=4)
    analysis = create_mock_analysis(
        "ptr_sum_wrong_tail",
        return_type="int",
        parameters=params,
        returns=[
            ReturnInfo(
                address="0x1000",
                value=_const(-300),
                conditions=[_cond("INT_EQUAL", ptr_param, Expression.constant(0, size=8))],
            ),
            ReturnInfo(
                address="0x1004",
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
    one32 = _FakeVarnode("one32", size=4, expr=Expression.constant(1, 4))
    three32 = _FakeVarnode("three32", size=4, expr=Expression.constant(3, 4))
    four64 = _FakeVarnode("four64", size=8, expr=Expression.constant(4, 8))
    ram_space = _FakeVarnode("ram", size=8, expr=Expression.constant(0, 8))

    idx_high = _FakeHighVar("idx")
    idx_phi = _FakeVarnode("idx_phi", size=4, high=idx_high)
    idx_next = _FakeVarnode("idx_next", size=4)
    idx_add_op = _FakePcodeOp("INT_ADD", [idx_phi, one32], idx_next)
    idx_phi_op = _FakePcodeOp("MULTIEQUAL", [three32, idx_next], idx_phi)

    addr = _FakeVarnode("addr", size=8)
    ptradd_op = _FakePcodeOp("PTRADD", [ptr_varnode, idx_phi, four64], addr)
    load_value = _FakeVarnode("load_value", size=4)
    load_op = _FakePcodeOp("LOAD", [ram_space, addr], load_value)

    acc_high = _FakeHighVar("acc")
    acc_phi = _FakeVarnode("acc_phi", size=4, high=acc_high)
    acc_next = _FakeVarnode("acc_next", size=4)
    acc_seed_expr = Expression.binary_op("INT_ADD", _mem("param_1", 0), _mem("param_1", 8))
    acc_seed = _FakeVarnode("acc_seed", size=4, expr=acc_seed_expr)
    acc_add_op = _FakePcodeOp("INT_ADD", [acc_phi, load_value], acc_next)
    acc_phi_op = _FakePcodeOp("MULTIEQUAL", [acc_seed, acc_next], acc_phi)

    high_function = _FakeHighFunction([idx_add_op, idx_phi_op, ptradd_op, load_op, acc_add_op, acc_phi_op])
    tracer = _FakeTracer("unused", _const(0))
    tracer.trace_varnode = lambda varnode, *args, **kwargs: getattr(varnode, "_expr", None)
    summarizer = StructuralRecurrenceSummarizer(tracer, debug=False)
    summary = summarizer.try_summarize_function(
        _FakeFunction("ptr_sum_wrong_tail"),
        high_function,
        analysis,
    )

    assert summary is not None
    summarized_returns, note = summary
    assert note == "readonly_pointer_reduction_summary"
    positive_case = next(ret for ret in summarized_returns if ret.value.expr_type == ExpressionType.INTRINSIC)
    runtime_ref = positive_case.value.runtime_ref
    proof = runtime_ref.accumulator_proof
    assert tuple(term.byte_offset for term in proof.seed_terms) == (0, 8)
    assert tuple(term.byte_offset for term in (proof.full_terms_for_count_value(4) or ())) == (0, 8, 12)
    assert tuple(term.byte_offset for term in runtime_ref.loop_summary.seed_terms) == (0, 8)

    prefix_summary = LoopSummaryRef(
        start_expr=Expression.constant(0, size=4),
        limit_expr=runtime_ref.loop_summary.limit_expr,
        step_expr=runtime_ref.loop_summary.step_expr,
        term_descriptor=runtime_ref.loop_summary.term_descriptor,
        side_effect_profile=runtime_ref.loop_summary.side_effect_profile,
        loop_var_unit=runtime_ref.loop_summary.loop_var_unit,
    )
    assert loop_summary_method_b_key(runtime_ref.loop_summary) != loop_summary_method_b_key(prefix_summary)


def test_vectorized_readonly_seed_recovery_uses_exact_wrong_tail_terms():
    pointer_param = {"name": "param_1", "index": 0, "data_type": "int *", "size": 8}
    count_param = {"name": "param_2", "index": 1, "data_type": "int", "size": 4, "is_signed": True}
    ptr_expr = Expression.parameter("param_1", index=0, data_type="int *", size=8)
    count_expr = Expression.parameter("param_2", index=1, data_type="int", size=4)
    vector_region = [
        _cond("INT_NOTEQUAL", ptr_expr, _const(0, size=8)),
        _cond("INT_SLESS", _const(0), count_expr),
    ]
    exact_four = ReturnInfo(
        address="0x2000",
        value=Expression.binary_op(
            "INT_ADD",
            _mem("param_1", 12),
            Expression.binary_op("INT_ADD", _mem("param_1", 8), _mem("param_1", 0)),
        ),
        conditions=vector_region + [_cond("INT_EQUAL", count_expr, _const(4))],
    )
    analysis = create_mock_analysis(
        "vectorized_wrong_tail_seed",
        return_type="int",
        parameters=[pointer_param, count_param],
        returns=[exact_four],
    )
    summarizer = StructuralRecurrenceSummarizer(_FakeTracer("unused", _const(0)), debug=False)

    seed_terms = summarizer._vector_prefix_seed_terms_from_exact_returns(
        analysis,
        pointer_param,
        count_param,
        vector_region,
        start_index=3,
        element_size=4,
    )

    assert seed_terms is not None
    assert tuple(term.byte_offset for term in seed_terms) == (0, 8)


def test_materialized_wrong_tail_return_rejects_prefix_region_proof_only():
    pointer_param = {
        "name": "param_1",
        "index": 0,
        "data_type": "int *",
        "size": 8,
    }
    count_param = {
        "name": "param_2",
        "index": 1,
        "data_type": "int",
        "size": 4,
        "is_signed": True,
    }
    ptr_expr = Expression.parameter("param_1", index=0, data_type="int *", size=8)
    count_expr = Expression.parameter("param_2", index=1, data_type="int", size=4)
    ret = ReturnInfo(
        address="0x1004",
        value=Expression.binary_op(
            "INT_ADD",
            Expression.binary_op("INT_ADD", _mem("param_1", 0), _mem("param_1", 8)),
            _mem("param_1", 12),
        ),
        conditions=[
            _cond("INT_NOTEQUAL", ptr_expr, Expression.constant(0, size=8)),
            _cond("INT_SLESS", _const(3), count_expr),
        ],
    )
    analysis = create_mock_analysis(
        "ptr_sum_wrong_tail",
        return_type="int",
        parameters=[pointer_param, count_param],
        returns=[ret],
    )
    proof = _readonly_accumulator_proof(
        base_ref=LocationBaseRef.parameter("param_1", index=0),
        count_expr=count_expr,
        stride=4,
        element_size=4,
        start_offset=0,
        start_index=0,
        return_op_refs=(PcodeOpRef(address_offset=0x1004, seq_time=1, mnemonic="RETURN"),),
        return_region_value_proven=True,
    )
    summarizer = StructuralRecurrenceSummarizer(_FakeTracer("unused", _const(0)), debug=False)

    assert not summarizer._readonly_materialized_positive_return_matches_accumulator_contract(
        analysis,
        pointer_param,
        count_param,
        ret,
        proof,
    )


def test_materialized_wrong_tail_return_accepts_seeded_tail_contract():
    pointer_param = {
        "name": "param_1",
        "index": 0,
        "data_type": "int *",
        "size": 8,
    }
    count_param = {
        "name": "param_2",
        "index": 1,
        "data_type": "int",
        "size": 4,
        "is_signed": True,
    }
    ptr_expr = Expression.parameter("param_1", index=0, data_type="int *", size=8)
    count_expr = Expression.parameter("param_2", index=1, data_type="int", size=4)
    ret = ReturnInfo(
        address="0x1004",
        value=Expression.binary_op(
            "INT_ADD",
            Expression.binary_op("INT_ADD", _mem("param_1", 0), _mem("param_1", 8)),
            _mem("param_1", 12),
        ),
        conditions=[
            _cond("INT_NOTEQUAL", ptr_expr, Expression.constant(0, size=8)),
            _cond("INT_SLESS", _const(3), count_expr),
        ],
    )
    analysis = create_mock_analysis(
        "ptr_sum_wrong_tail",
        return_type="int",
        parameters=[pointer_param, count_param],
        returns=[ret],
    )
    proof = _readonly_accumulator_proof(
        base_ref=LocationBaseRef.parameter("param_1", index=0),
        count_expr=count_expr,
        stride=4,
        element_size=4,
        start_offset=12,
        start_index=3,
        seed_terms=(
            ReadonlyReductionTermRef(byte_offset=0, access_size=4),
            ReadonlyReductionTermRef(byte_offset=8, access_size=4),
        ),
        return_op_refs=(PcodeOpRef(address_offset=0x1004, seq_time=1, mnemonic="RETURN"),),
        return_region_value_proven=True,
    )
    summarizer = StructuralRecurrenceSummarizer(_FakeTracer("unused", _const(0)), debug=False)

    assert summarizer._readonly_materialized_positive_return_matches_accumulator_contract(
        analysis,
        pointer_param,
        count_param,
        ret,
        proof,
    )


def test_proof_backed_readonly_summary_subsumes_same_site_unresolved_artifact():
    count_expr = Expression.parameter("param_2", index=1, data_type="int", size=4)
    ptr_expr = Expression.parameter("param_1", index=0, data_type="int *", size=8)
    return_ref = PcodeOpRef(address_offset=0x1004, seq_time=47, seq_order=0, mnemonic="RETURN")
    conditions = [
        _cond("INT_NOTEQUAL", ptr_expr, Expression.constant(0, size=8)),
        _cond("INT_SLESS", _const(3), count_expr),
    ]
    proof = _readonly_accumulator_proof(
        base_ref=LocationBaseRef.parameter("param_1", index=0),
        count_expr=count_expr,
        stride=4,
        element_size=4,
        start_offset=12,
        start_index=3,
        seed_terms=(
            ReadonlyReductionTermRef(byte_offset=0, access_size=4),
            ReadonlyReductionTermRef(byte_offset=8, access_size=4),
        ),
        return_op_refs=(return_ref,),
        return_region_value_proven=True,
    )
    replacement_ref = proof.to_readonly_reduction_ref()
    assert replacement_ref is not None
    unresolved_ret = ReturnInfo(
        address="0x1004",
        value=Expression.binary_op(
            "INT_ADD",
            _mem("param_1", 12),
            Expression.unknown("phi_circular"),
        ),
        conditions=list(conditions),
        pcode_op_ref=return_ref,
    )
    different_region_ret = ReturnInfo(
        address="0x1004",
        value=unresolved_ret.value,
        conditions=list(conditions) + [_cond("INT_EQUAL", count_expr, _const(4))],
        pcode_op_ref=return_ref,
    )
    summary_excluding_count4 = list(conditions) + [_cond("INT_EQUAL", count_expr, _const(4), negated=True)]
    unproven_proof = replace(proof, return_region_value_proven=False)
    unproven_ref = unproven_proof.to_readonly_reduction_ref()
    summarizer = StructuralRecurrenceSummarizer(_FakeTracer("unused", _const(0)), debug=False)

    assert summarizer._readonly_unresolved_preserved_return_is_subsumed_by_replacement(
        unresolved_ret,
        conditions,
        proof,
        replacement_ref,
    )
    assert not summarizer._readonly_unresolved_preserved_return_is_subsumed_by_replacement(
        different_region_ret,
        summary_excluding_count4,
        proof,
        replacement_ref,
    )
    assert not summarizer._readonly_unresolved_preserved_return_is_subsumed_by_replacement(
        unresolved_ret,
        conditions,
        unproven_proof,
        unproven_ref,
    )


def test_materialized_wrong_tail_anchor_count_accounts_for_explicit_seed_terms():
    pointer_param = {
        "name": "param_1",
        "index": 0,
        "data_type": "int *",
        "size": 8,
    }
    count_param = {
        "name": "param_2",
        "index": 1,
        "data_type": "int",
        "size": 4,
        "is_signed": True,
    }
    ptr_expr = Expression.parameter("param_1", index=0, data_type="int *", size=8)
    count_expr = Expression.parameter("param_2", index=1, data_type="int", size=4)
    value = _mem("param_1", 0)
    for offset in (8, 12, 16, 20, 24, 28, 32, 36, 40):
        value = Expression.binary_op("INT_ADD", value, _mem("param_1", offset))
    ret = ReturnInfo(
        address="0x1004",
        value=value,
        conditions=[
            _cond("INT_NOTEQUAL", ptr_expr, Expression.constant(0, size=8)),
            _cond("INT_SLESS", _const(10), count_expr),
        ],
    )
    analysis = create_mock_analysis(
        "ptr_sum_wrong_tail_vector_anchor",
        return_type="int",
        parameters=[pointer_param, count_param],
        returns=[ret],
    )
    proof = _readonly_accumulator_proof(
        base_ref=LocationBaseRef.parameter("param_1", index=0),
        count_expr=count_expr,
        stride=4,
        element_size=4,
        start_offset=12,
        start_index=3,
        seed_terms=(
            ReadonlyReductionTermRef(byte_offset=0, access_size=4),
            ReadonlyReductionTermRef(byte_offset=8, access_size=4),
        ),
        return_op_refs=(PcodeOpRef(address_offset=0x1004, seq_time=1, mnemonic="RETURN"),),
        return_region_value_proven=True,
    )
    summarizer = StructuralRecurrenceSummarizer(_FakeTracer("unused", _const(0)), debug=False)

    assert summarizer._readonly_positive_return_accumulator_anchor_count(
        analysis,
        pointer_param,
        count_param,
        ret,
        proof,
    ) == 11
    assert summarizer._readonly_materialized_positive_return_matches_accumulator_contract(
        analysis,
        pointer_param,
        count_param,
        ret,
        proof,
    )


def test_vectorized_region_proof_subsumes_broad_materialized_return_shape():
    pointer_param = {
        "name": "param_1",
        "index": 0,
        "data_type": "int *",
        "size": 8,
    }
    count_param = {
        "name": "param_2",
        "index": 1,
        "data_type": "int",
        "size": 4,
        "is_signed": True,
    }
    ptr_expr = Expression.parameter("param_1", index=0, data_type="int *", size=8)
    count_expr = Expression.parameter("param_2", index=1, data_type="int", size=4)
    ret = ReturnInfo(
        address="0x1004",
        pcode_time=10,
        pcode_order=1,
        pcode_op_ref=PcodeOpRef(address_offset=0x1004, seq_time=10, seq_order=1, mnemonic="RETURN"),
        value=Expression.binary_op(
            "INT_ADD",
            _mem("param_1", 0),
            _mem("param_1", 4),
        ),
        conditions=[
            _cond("INT_NOTEQUAL", ptr_expr, Expression.constant(0, size=8)),
            _cond("INT_SLESS", _const(3), count_expr),
        ],
    )
    analysis = create_mock_analysis(
        "vectorized_region_contract_like",
        return_type="int",
        parameters=[pointer_param, count_param],
        returns=[ret],
    )
    proof = _readonly_accumulator_proof(
        base_ref=LocationBaseRef.parameter("param_1", index=0),
        count_expr=count_expr,
        stride=4,
        element_size=4,
        start_offset=12,
        start_index=3,
        seed_terms=(
            ReadonlyReductionTermRef(byte_offset=0, access_size=4),
            ReadonlyReductionTermRef(byte_offset=8, access_size=4),
        ),
        return_op_refs=(PcodeOpRef(address_offset=0x1004, seq_time=10, seq_order=1, mnemonic="RETURN"),),
        return_region_value_proven=True,
        source="vectorized_readonly_prefix_sum",
    )
    broad_positive_conditions = [
        _cond("INT_NOTEQUAL", ptr_expr, Expression.constant(0, size=8)),
        _cond("INT_SLESS", _const(0), count_expr),
    ]
    positive_conditions = [
        _cond("INT_NOTEQUAL", ptr_expr, Expression.constant(0, size=8)),
        _cond("INT_SLESS", _const(3), count_expr),
    ]
    summarizer = StructuralRecurrenceSummarizer(_FakeTracer("unused", _const(0)), debug=False)

    assert summarizer._readonly_reduction_replaceable_positive_returns(
        analysis,
        pointer_param,
        count_param,
        broad_positive_conditions,
        positive_conditions,
        expected_signed=True,
        accumulator_proof=proof,
    ) == [ret]


def test_readonly_witness_synthesis_does_not_override_existing_exact_return():
    pointer_param = {
        "name": "param_1",
        "index": 0,
        "data_type": "int *",
        "size": 8,
    }
    count_param = {
        "name": "param_2",
        "index": 1,
        "data_type": "int",
        "size": 4,
        "is_signed": True,
    }
    ptr_expr = Expression.parameter("param_1", index=0, data_type="int *", size=8)
    count_expr = Expression.parameter("param_2", index=1, data_type="int", size=4)
    wrong_tail_four = ReturnInfo(
        address="0x1004",
        value=Expression.binary_op(
            "INT_ADD",
            _mem("param_1", 12),
            Expression.binary_op("INT_ADD", _mem("param_1", 8), _mem("param_1", 0)),
        ),
        conditions=[
            _cond("INT_NOTEQUAL", ptr_expr, Expression.constant(0, size=8)),
            _cond("INT_EQUAL", count_expr, _const(4)),
        ],
    )
    analysis = create_mock_analysis(
        "witness_synthesis_conflict",
        return_type="int",
        parameters=[pointer_param, count_param],
        returns=[wrong_tail_four],
    )
    reduction_ref = ReadonlyReductionRef(
        reduction_kind="memory_sum",
        pointer_base_ref=LocationBaseRef.parameter("param_1", index=0),
        count_parameter_name="param_2",
        count_parameter_index=1,
        stride=4,
        element_size=4,
        result_size=4,
        semantic_witnesses=(
            ReadonlyReductionWitness(
                exact_count=4,
                terms=(
                    ReadonlyReductionTermRef(byte_offset=0, access_size=4),
                    ReadonlyReductionTermRef(byte_offset=4, access_size=4),
                    ReadonlyReductionTermRef(byte_offset=8, access_size=4),
                    ReadonlyReductionTermRef(byte_offset=12, access_size=4),
                ),
            ),
        ),
    )
    summarizer = StructuralRecurrenceSummarizer(_FakeTracer("unused", _const(0)), debug=False)

    synthesized = summarizer._synthesize_exact_returns_from_readonly_witnesses(
        analysis,
        pointer_param,
        count_param,
        broad_positive_conditions=[
            _cond("INT_NOTEQUAL", ptr_expr, Expression.constant(0, size=8)),
            _cond("INT_SLESS", _const(0), count_expr),
        ],
        summary_positive_conditions=[
            _cond("INT_NOTEQUAL", ptr_expr, Expression.constant(0, size=8)),
            _cond("INT_SLESS", _const(3), count_expr),
        ],
        existing_returns=[wrong_tail_four],
        reduction_ref=reduction_ref,
        result_size=4,
    )

    assert synthesized == [wrong_tail_four]


def test_readonly_candidate_selection_prefers_seeded_contract_over_declared_signedness():
    pointer_param = {
        "name": "param_1",
        "index": 0,
        "data_type": "int *",
        "size": 8,
        "is_signed": False,
    }
    count_param = {
        "name": "param_2",
        "index": 1,
        "data_type": "ulong",
        "size": 8,
        "is_signed": False,
    }
    ptr_expr = Expression.parameter("param_1", index=0, data_type="int *", size=8)
    count_expr = Expression.parameter("param_2", index=1, data_type="ulong", size=8)
    masked_count = Expression.binary_op(
        "INT_AND",
        Expression.constant(0xFFFFFFFF, size=8),
        count_expr,
    )
    masked_count.size = 8
    exact_four_expr = Expression.binary_op(
        "INT_ADD",
        Expression.binary_op(
            "INT_SUB",
            masked_count,
            Expression.constant(3, size=8),
        ),
        Expression.constant(-1, size=8),
    )
    exact_four_expr.size = 8
    exact_four = ReturnInfo(
        address="0x100cb4",
        pcode_time=35,
        pcode_order=2,
        pcode_op_ref=PcodeOpRef(address_offset=0x100CB4, seq_time=35, seq_order=2, mnemonic="RETURN"),
        value=Expression.binary_op(
            "INT_ADD",
            _mem("param_1", 12),
            Expression.binary_op("INT_ADD", _mem("param_1", 8), _mem("param_1", 0)),
        ),
        conditions=[
            _cond("INT_NOTEQUAL", ptr_expr, Expression.constant(0, size=8)),
            _cond("INT_SLESS", Expression.constant(0, size=8), count_expr),
            _cond("INT_SLESSEQUAL", Expression.constant(4, size=8), count_expr),
            _cond("INT_EQUAL", exact_four_expr, Expression.constant(0, size=8)),
        ],
    )
    analysis = FunctionReturnAnalysis(
        function_name="readonly_wrong_tail_seeded_candidate_like",
        entry_point="0x100c80",
        parameters=[pointer_param, count_param],
        returns=[exact_four],
    )
    prefix_proof = _readonly_accumulator_proof(
        base_ref=LocationBaseRef.parameter("param_1", index=0),
        count_expr=count_expr,
        stride=4,
        element_size=4,
        start_offset=0,
        start_index=0,
        return_op_refs=(PcodeOpRef(address_offset=0x100CB4, seq_time=35, seq_order=2, mnemonic="RETURN"),),
        return_region_value_proven=True,
    )
    seeded_proof = _readonly_accumulator_proof(
        base_ref=LocationBaseRef.parameter("param_1", index=0),
        count_expr=count_expr,
        stride=4,
        element_size=4,
        start_offset=12,
        start_index=3,
        seed_terms=(
            ReadonlyReductionTermRef(byte_offset=0, access_size=4),
            ReadonlyReductionTermRef(byte_offset=8, access_size=4),
        ),
        return_op_refs=(PcodeOpRef(address_offset=0x100CB4, seq_time=35, seq_order=2, mnemonic="RETURN"),),
        return_region_value_proven=True,
    )
    broad_positive_conditions = [
        _cond("INT_NOTEQUAL", ptr_expr, Expression.constant(0, size=8)),
        _cond("INT_SLESS", Expression.constant(0, size=8), count_expr),
    ]
    positive_conditions = [
        _cond("INT_NOTEQUAL", ptr_expr, Expression.constant(0, size=8)),
        _cond("INT_SLESS", Expression.constant(3, size=8), count_expr),
    ]
    summarizer = StructuralRecurrenceSummarizer(_FakeTracer("unused", _const(0)), debug=False)

    assert summarizer._readonly_reduction_replaceable_positive_returns(
        analysis,
        pointer_param,
        count_param,
        broad_positive_conditions,
        positive_conditions,
        expected_signed=True,
        declared_signedness=False,
        accumulator_proof=seeded_proof,
    ) == [exact_four]
    assert summarizer._readonly_reduction_replaceable_positive_returns(
        analysis,
        pointer_param,
        count_param,
        broad_positive_conditions,
        positive_conditions,
        expected_signed=False,
        declared_signedness=False,
        accumulator_proof=prefix_proof,
    ) == []

    selected = summarizer._select_readonly_reduction_candidate(
        analysis,
        pointer_param,
        count_param,
        [
            (False, broad_positive_conditions, prefix_proof, positive_conditions, [exact_four]),
            (True, broad_positive_conditions, seeded_proof, positive_conditions, [exact_four]),
        ],
    )

    assert selected is not None
    assert selected[2] is seeded_proof


def test_exact_materialized_return_rejects_conflicting_broad_prefix_proof():
    pointer_param = {
        "name": "param_1",
        "index": 0,
        "data_type": "int *",
        "size": 8,
        "is_signed": False,
    }
    count_param = {
        "name": "param_2",
        "index": 1,
        "data_type": "int",
        "size": 4,
        "is_signed": True,
    }
    ptr_expr = Expression.parameter("param_1", index=0, data_type="int *", size=8)
    count_expr = Expression.parameter("param_2", index=1, data_type="int", size=4)
    exact_four = ReturnInfo(
        address="0x1004",
        value=Expression.binary_op(
            "INT_ADD",
            _mem("param_1", 12),
            Expression.binary_op("INT_ADD", _mem("param_1", 8), _mem("param_1", 0)),
        ),
        conditions=[
            _cond("INT_NOTEQUAL", ptr_expr, Expression.constant(0, size=8)),
            _cond("INT_EQUAL", count_expr, _const(4)),
        ],
    )
    analysis = FunctionReturnAnalysis(
        function_name="readonly_exact_conflicts_with_prefix_contract_like",
        entry_point="0x1000",
        parameters=[pointer_param, count_param],
        returns=[exact_four],
    )
    prefix_proof = _readonly_accumulator_proof(
        base_ref=LocationBaseRef.parameter("param_1", index=0),
        count_expr=count_expr,
        stride=4,
        element_size=4,
        start_offset=0,
        start_index=0,
    )
    seeded_tail_proof = _readonly_accumulator_proof(
        base_ref=LocationBaseRef.parameter("param_1", index=0),
        count_expr=count_expr,
        stride=4,
        element_size=4,
        start_offset=12,
        start_index=3,
        seed_terms=(
            ReadonlyReductionTermRef(byte_offset=0, access_size=4),
            ReadonlyReductionTermRef(byte_offset=8, access_size=4),
        ),
    )
    broad_positive_conditions = [
        _cond("INT_NOTEQUAL", ptr_expr, Expression.constant(0, size=8)),
        _cond("INT_SLESS", _const(0), count_expr),
    ]
    tail_positive_conditions = [
        _cond("INT_NOTEQUAL", ptr_expr, Expression.constant(0, size=8)),
        _cond("INT_SLESS", _const(3), count_expr),
    ]
    summarizer = StructuralRecurrenceSummarizer(_FakeTracer("unused", _const(0)), debug=False)

    assert summarizer._readonly_exact_materialized_returns_conflict_with_accumulator_proof(
        analysis,
        pointer_param,
        count_param,
        broad_positive_conditions,
        prefix_proof,
    )
    assert not summarizer._readonly_exact_materialized_returns_conflict_with_accumulator_proof(
        analysis,
        pointer_param,
        count_param,
        tail_positive_conditions,
        seeded_tail_proof,
    )


def test_preserved_readonly_summary_is_dropped_when_return_site_proof_replaces_contract():
    pointer_param = {
        "name": "param_1",
        "index": 0,
        "data_type": "int *",
        "size": 8,
        "is_signed": False,
    }
    count_expr = Expression.parameter("param_2", index=1, data_type="int", size=4)
    ptr_expr = Expression.parameter("param_1", index=0, data_type="int *", size=8)
    site_ref = PcodeOpRef(address_offset=0x1004, seq_time=35, seq_order=2, mnemonic="RETURN")
    prefix_proof = _readonly_accumulator_proof(
        base_ref=LocationBaseRef.parameter("param_1", index=0),
        count_expr=count_expr,
        stride=4,
        element_size=4,
        start_offset=0,
        start_index=0,
        return_op_refs=(site_ref,),
        return_region_value_proven=True,
    )
    seeded_tail_proof = _readonly_accumulator_proof(
        base_ref=LocationBaseRef.parameter("param_1", index=0),
        count_expr=count_expr,
        stride=4,
        element_size=4,
        start_offset=12,
        start_index=3,
        seed_terms=(
            ReadonlyReductionTermRef(byte_offset=0, access_size=4),
            ReadonlyReductionTermRef(byte_offset=8, access_size=4),
        ),
        return_op_refs=(site_ref,),
        return_region_value_proven=True,
    )
    prefix_ref = prefix_proof.lower_to_readonly_reduction_ref()
    seeded_ref = seeded_tail_proof.lower_to_readonly_reduction_ref()
    assert prefix_ref is not None
    assert seeded_ref is not None
    conditions = [
        _cond("INT_NOTEQUAL", ptr_expr, Expression.constant(0, size=8)),
        _cond("INT_SLESS", _const(3), count_expr),
        _cond("INT_EQUAL", count_expr, _const(4), negated=True),
    ]
    preserved_summary = ReturnInfo(
        address="0x1004",
        pcode_time=35,
        pcode_order=2,
        pcode_op_ref=site_ref,
        value=Expression.intrinsic(
            "READONLY_SUM",
            [ptr_expr, count_expr],
            size=4,
            runtime_ref=prefix_ref,
            opcode=READONLY_SUM_OPCODE,
        ),
        conditions=conditions,
    )
    seeded_summary = replace(
        preserved_summary,
        value=Expression.intrinsic(
            "READONLY_SUM",
            [ptr_expr, count_expr],
            size=4,
            runtime_ref=seeded_ref,
            opcode=READONLY_SUM_OPCODE,
        ),
    )
    unrelated_site = replace(
        preserved_summary,
        pcode_op_ref=PcodeOpRef(address_offset=0x2000, seq_time=35, seq_order=2, mnemonic="RETURN"),
    )
    summarizer = StructuralRecurrenceSummarizer(_FakeTracer("unused", _const(0)), debug=False)
    analysis = FunctionReturnAnalysis(
        function_name="readonly_preserved_summary_replacement_like",
        entry_point="0x1000",
        parameters=[pointer_param, {"name": "param_2", "index": 1, "data_type": "int", "size": 4}],
        returns=[preserved_summary],
    )

    assert summarizer._readonly_preserved_summary_is_subsumed_by_replacement(
        analysis,
        pointer_param,
        {"name": "param_2", "index": 1, "data_type": "int", "size": 4},
        preserved_summary,
        conditions,
        conditions,
        seeded_tail_proof,
        seeded_ref,
    )
    assert not summarizer._readonly_preserved_summary_is_subsumed_by_replacement(
        analysis,
        pointer_param,
        {"name": "param_2", "index": 1, "data_type": "int", "size": 4},
        seeded_summary,
        conditions,
        conditions,
        prefix_proof,
        prefix_ref,
    )
    assert not summarizer._readonly_preserved_summary_is_subsumed_by_replacement(
        analysis,
        pointer_param,
        {"name": "param_2", "index": 1, "data_type": "int", "size": 4},
        unrelated_site,
        conditions,
        conditions,
        seeded_tail_proof,
        seeded_ref,
    )


def test_proof_backed_specific_readonly_summary_precedes_broader_preserved_summary():
    pointer_param = {"name": "param_1", "index": 0, "data_type": "int *", "size": 8}
    ptr_expr = Expression.parameter("param_1", index=0, data_type="int *", size=8)
    count_expr = Expression.parameter("param_2", index=1, data_type="int", size=4)
    prefix_proof = _readonly_accumulator_proof(
        base_ref=LocationBaseRef.parameter("param_1", index=0),
        count_expr=count_expr,
        stride=4,
        element_size=4,
        start_offset=0,
        start_index=0,
    )
    seeded_tail_proof = _readonly_accumulator_proof(
        base_ref=LocationBaseRef.parameter("param_1", index=0),
        count_expr=count_expr,
        stride=4,
        element_size=4,
        start_offset=12,
        start_index=3,
        seed_terms=(
            ReadonlyReductionTermRef(byte_offset=0, access_size=4),
            ReadonlyReductionTermRef(byte_offset=8, access_size=4),
        ),
    )
    prefix_ref = prefix_proof.lower_to_readonly_reduction_ref()
    seeded_ref = seeded_tail_proof.lower_to_readonly_reduction_ref()
    assert prefix_ref is not None
    assert seeded_ref is not None
    broad_conditions = [
        _cond("INT_NOTEQUAL", ptr_expr, Expression.constant(0, size=8)),
        _cond("INT_SLESS", _const(0), count_expr),
        _cond("INT_EQUAL", count_expr, _const(1), negated=True),
        _cond("INT_EQUAL", count_expr, _const(2), negated=True),
        _cond("INT_EQUAL", count_expr, _const(3), negated=True),
        _cond("INT_EQUAL", count_expr, _const(4), negated=True),
    ]
    specific_conditions = [
        _cond("INT_NOTEQUAL", ptr_expr, Expression.constant(0, size=8)),
        _cond("INT_SLESS", _const(3), count_expr),
        _cond("INT_EQUAL", count_expr, _const(4), negated=True),
    ]
    preserved_broad = ReturnInfo(
        address="0x1004",
        value=Expression.intrinsic(
            "READONLY_SUM",
            [ptr_expr, count_expr],
            size=4,
            runtime_ref=prefix_ref,
            opcode=READONLY_SUM_OPCODE,
        ),
        conditions=broad_conditions,
    )
    summary_specific = ReturnInfo(
        address="0x1004",
        value=Expression.intrinsic(
            "READONLY_SUM",
            [ptr_expr, count_expr],
            size=4,
            runtime_ref=seeded_ref,
            opcode=READONLY_SUM_OPCODE,
        ),
        conditions=specific_conditions,
    )
    summarizer = StructuralRecurrenceSummarizer(_FakeTracer("unused", _const(0)), debug=False)

    assert summarizer._readonly_summary_return_should_precede_preserved_return(
        summary_specific,
        preserved_broad,
        seeded_ref,
    )
    assert not summarizer._readonly_summary_return_should_precede_preserved_return(
        preserved_broad,
        summary_specific,
        prefix_ref,
    )


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


def test_readonly_reduction_detects_vector_pointer_loop_with_ptradd_tail(monkeypatch):
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
    monkeypatch.setattr(
        summarizer,
        "_vector_prefix_unit_term_positive_return_refs",
        lambda *_args, **_kwargs: (PcodeOpRef(address_offset=0x1000, seq_time=10, mnemonic="RETURN"),),
    )
    monkeypatch.setattr(
        summarizer,
        "_vector_prefix_lane_return_refs",
        lambda *_args, **_kwargs: (
            (PcodeOpRef(address_offset=0x1000, seq_time=10, mnemonic="RETURN"),),
            (PcodeOpRef(address_offset=0x1000, seq_time=9, mnemonic="INT_ADD"),),
        ),
    )

    proof = summarizer._detect_readonly_sum_accumulator_proof(
        high_function,
        analysis,
        params[0],
        params[1],
        counter_signed=True,
    )

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


def test_readonly_exact_return_witness_canonicalizes_proven_vectorized_prefix_completion(monkeypatch):
    pointer_param = {"name": "param_1", "index": 0, "data_type": "int *", "size": 8}
    count_param = {"name": "param_2", "index": 1, "data_type": "int", "size": 4, "is_signed": True}
    count_expr = Expression.parameter("param_2", index=1, data_type="int", size=4)
    proof = _readonly_accumulator_proof(
        base_ref=LocationBaseRef.parameter("param_1", index=0),
        count_expr=count_expr,
        stride=4,
        element_size=4,
        start_offset=12,
        start_index=3,
        seed_terms=(
            ReadonlyReductionTermRef(byte_offset=0, access_size=4),
            ReadonlyReductionTermRef(byte_offset=4, access_size=4),
            ReadonlyReductionTermRef(byte_offset=8, access_size=4),
        ),
    )
    value = Expression.binary_op(
        "INT_ADD",
        _mem("param_1", 12),
        Expression.binary_op(
            "INT_ADD",
            _mem("param_1", 0),
            Expression.binary_op(
                "INT_ADD",
                _mem("param_1", 4),
                Expression.binary_op(
                    "INT_ADD",
                    _mem("param_1", 8),
                    _mem("param_1", 16),
                ),
            ),
        ),
    )
    ret = ReturnInfo(
        address="0x2000",
        value=value,
        conditions=[_cond("INT_EQUAL", count_expr, _const(5))],
    )
    analysis = create_mock_analysis(
        "readonly_vector_prefix_completion",
        return_type="int",
        parameters=[pointer_param, count_param],
        returns=[ret],
    )
    summarizer = StructuralRecurrenceSummarizer(_FakeTracer("unused", Expression.unknown("unknown")), debug=False)

    monkeypatch.setattr(
        summarizer,
        "_extract_readonly_return_terms_and_bias",
        lambda *_args, **_kwargs: (
            (
                ReadonlyReductionTermRef(byte_offset=12, access_size=4),
                ReadonlyReductionTermRef(byte_offset=16, access_size=4),
            ),
            0,
        ),
    )

    witnesses = summarizer._extract_readonly_reduction_exact_witnesses(
        analysis,
        pointer_param,
        count_param,
        [ret],
        proof,
    )

    assert len(witnesses) == 1
    assert witnesses[0].exact_count == 5
    assert tuple(term.byte_offset for term in witnesses[0].terms) == (0, 4, 8, 12, 16)


def test_readonly_exact_return_witness_accepts_commuted_sum_terms():
    pointer_param = {"name": "param_1", "index": 0, "data_type": "int *", "size": 8}
    count_param = {"name": "param_2", "index": 1, "data_type": "int", "size": 4, "is_signed": True}
    count_expr = Expression.parameter("param_2", index=1, data_type="int", size=4)
    proof = _readonly_accumulator_proof(
        base_ref=LocationBaseRef.parameter("param_1", index=0),
        count_expr=count_expr,
        stride=4,
        element_size=4,
        start_offset=12,
        start_index=3,
        seed_terms=(
            ReadonlyReductionTermRef(byte_offset=0, access_size=4),
            ReadonlyReductionTermRef(byte_offset=8, access_size=4),
        ),
    )
    ret = ReturnInfo(
        address="0x2008",
        value=Expression.binary_op(
            "INT_ADD",
            _mem("param_1", 12),
            Expression.binary_op("INT_ADD", _mem("param_1", 8), _mem("param_1", 0)),
        ),
        conditions=[_cond("INT_EQUAL", count_expr, _const(4))],
    )
    analysis = create_mock_analysis(
        "readonly_commuted_wrong_tail_exact",
        return_type="int",
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

    assert len(witnesses) == 1
    assert witnesses[0].exact_count == 4
    assert tuple(term.byte_offset for term in witnesses[0].terms) == (0, 8, 12)


def test_readonly_exact_return_witness_accepts_self_consistent_scalar_prefix_when_proof_geometry_differs():
    summarizer = StructuralRecurrenceSummarizer(tracer=None, debug=False)
    pointer_param = {"name": "param_1", "index": 0, "data_type": "int *", "size": 8}
    count_param = {"name": "param_2", "index": 1, "data_type": "int", "size": 4, "is_signed": True}
    count_expr = Expression.parameter("param_2", index=1, data_type="int", size=4)
    proof = _readonly_accumulator_proof(
        base_ref=LocationBaseRef.parameter("param_1", index=0),
        count_expr=count_expr,
        stride=16,
        element_size=8,
        result_size=4,
        start_offset=12,
        start_index=3,
        index_scale=16,
    )
    ret = ReturnInfo(
        address="0x2004",
        value=Expression.binary_op(
            "INT_ADD",
            _mem("param_1", 0),
            Expression.binary_op(
                "INT_ADD",
                _mem("param_1", 4),
                _mem("param_1", 8),
            ),
        ),
        conditions=[_cond("INT_EQUAL", count_expr, _const(3))],
    )
    analysis = create_mock_analysis(
        "readonly_scalar_prefix_geometry_mismatch",
        return_type="int",
        parameters=[pointer_param, count_param],
        returns=[ret],
    )

    witnesses = summarizer._extract_readonly_reduction_exact_witnesses(
        analysis,
        pointer_param,
        count_param,
        [ret],
        proof,
    )

    assert len(witnesses) == 1
    assert witnesses[0].exact_count == 3
    assert tuple(term.byte_offset for term in witnesses[0].terms) == (0, 4, 8)


def test_reduction_accumulator_proof_normalizes_scalar_prefix_from_exact_witnesses():
    proof = _readonly_accumulator_proof(
        base_ref=LocationBaseRef.parameter("param_1", index=0),
        count_expr=Expression.parameter("param_2", index=1, data_type="int", size=4),
        stride=16,
        element_size=8,
        result_size=4,
        start_offset=12,
        start_index=3,
        index_scale=16,
    )
    exact_witnesses = tuple(
        ReadonlyReductionWitness(
            exact_count=count_value,
            terms=tuple(
                ReadonlyReductionTermRef(byte_offset=index * 4, access_size=4)
                for index in range(count_value)
            ),
        )
        for count_value in (1, 2, 3, 5, 6)
    )

    normalized = proof.with_runtime_evidence(
        limit_expr=Expression.parameter("param_2", index=1, data_type="int", size=4),
        result_size=4,
        loop_body_witnesses=(),
        exact_return_witnesses=exact_witnesses,
        guard_constraints=(),
        signed_counter=True,
    )

    assert normalized.stride == 4
    assert normalized.element_size == 4
    assert normalized.index_scale == 4
    assert normalized.start_offset == 0
    assert normalized.start_index == 0


def test_readonly_reduction_candidate_normalizes_until_true_fixpoint(monkeypatch):
    summarizer = StructuralRecurrenceSummarizer(tracer=None, debug=False)
    pointer_param = {"name": "param_1", "index": 0, "data_type": "int *", "size": 8, "is_signed": False}
    count_param = {"name": "param_2", "index": 1, "data_type": "int", "size": 4, "is_signed": True}
    count_expr = Expression.parameter("param_2", index=1, data_type="int", size=4)
    broad_ret = ReturnInfo(
        address="0x1400",
        conditions=[
            _cond("INT_NOTEQUAL", _param("param_1", size=8), _const(0, size=8)),
            _cond("INT_SLESS", _const(0), count_expr),
        ],
        value=Expression.unknown("phi_circular"),
    )
    analysis = FunctionReturnAnalysis(
        function_name="readonly_fixpoint_normalization_like",
        entry_point="0x1400",
        parameters=[pointer_param, count_param],
        returns=[broad_ret],
    )
    proof = _readonly_accumulator_proof(
        base_ref=LocationBaseRef.parameter("param_1", index=0),
        count_expr=count_expr,
        stride=4,
        element_size=4,
        start_offset=16,
        start_index=4,
    )

    def fake_with_runtime_evidence(
        self,
        *,
        limit_expr,
        result_size,
        loop_body_witnesses,
        exact_return_witnesses,
        guard_constraints,
        signed_counter,
    ):
        next_start = max(0, int(self.start_index) - 1)
        return replace(
            self,
            limit_expr=limit_expr,
            result_size=result_size,
            loop_body_witnesses=tuple(loop_body_witnesses),
            exact_return_witnesses=tuple(exact_return_witnesses),
            guard_constraints=tuple(guard_constraints),
            signed_counter=bool(signed_counter),
            start_index=next_start,
            start_offset=next_start * 4,
        )

    monkeypatch.setattr(ReductionAccumulatorProof, "with_runtime_evidence", fake_with_runtime_evidence)
    monkeypatch.setattr(
        summarizer,
        "_extract_readonly_reduction_exact_witnesses",
        lambda *_args, **_kwargs: (),
    )
    monkeypatch.setattr(
        summarizer,
        "_build_readonly_reduction_semantic_witnesses",
        lambda *_args, **_kwargs: (),
    )
    monkeypatch.setattr(
        summarizer,
        "_readonly_reduction_positive_conditions",
        lambda _analysis, _pointer_param, _count_param, loop_start_index=0, signed_counter=True: [
            _cond("INT_NOTEQUAL", _param("param_1", size=8), _const(0, size=8)),
            _cond("INT_SLESS", _const(int(loop_start_index)), count_expr),
        ],
    )
    monkeypatch.setattr(
        summarizer,
        "_readonly_reduction_replaceable_positive_returns",
        lambda *_args, **_kwargs: [broad_ret],
    )

    normalized = summarizer._normalize_readonly_reduction_candidate(
        analysis,
        pointer_param,
        count_param,
        broad_positive_conditions=[
            _cond("INT_NOTEQUAL", _param("param_1", size=8), _const(0, size=8)),
            _cond("INT_SLESS", _const(0), count_expr),
        ],
        positive_conditions=[
            _cond("INT_NOTEQUAL", _param("param_1", size=8), _const(0, size=8)),
            _cond("INT_SLESS", _const(4), count_expr),
        ],
        counter_signed=True,
        accumulator_proof=proof,
        overlapping_positive_returns=[broad_ret],
    )

    assert normalized is not None
    normalized_proof, normalized_conditions, normalized_returns, *_rest = normalized
    assert normalized_proof.start_index == 0
    assert [condition.to_string() for condition in normalized_conditions] == [
        "(param_1 != 0)",
        "(0 < param_2)",
    ]
    assert normalized_returns == [broad_ret]


def test_readonly_reduction_candidate_declines_non_convergent_normalization(monkeypatch):
    summarizer = StructuralRecurrenceSummarizer(tracer=None, debug=False)
    pointer_param = {"name": "param_1", "index": 0, "data_type": "int *", "size": 8, "is_signed": False}
    count_param = {"name": "param_2", "index": 1, "data_type": "int", "size": 4, "is_signed": True}
    count_expr = Expression.parameter("param_2", index=1, data_type="int", size=4)
    broad_ret = ReturnInfo(
        address="0x1410",
        conditions=[
            _cond("INT_NOTEQUAL", _param("param_1", size=8), _const(0, size=8)),
            _cond("INT_SLESS", _const(0), count_expr),
        ],
        value=Expression.unknown("phi_circular"),
    )
    analysis = FunctionReturnAnalysis(
        function_name="readonly_fixpoint_cycle_like",
        entry_point="0x1410",
        parameters=[pointer_param, count_param],
        returns=[broad_ret],
    )
    proof = _readonly_accumulator_proof(
        base_ref=LocationBaseRef.parameter("param_1", index=0),
        count_expr=count_expr,
        stride=4,
        element_size=4,
        start_offset=8,
        start_index=2,
    )

    def fake_with_runtime_evidence(
        self,
        *,
        limit_expr,
        result_size,
        loop_body_witnesses,
        exact_return_witnesses,
        guard_constraints,
        signed_counter,
    ):
        next_start = 1 if int(self.start_index) == 2 else 2
        return replace(
            self,
            limit_expr=limit_expr,
            result_size=result_size,
            loop_body_witnesses=tuple(loop_body_witnesses),
            exact_return_witnesses=tuple(exact_return_witnesses),
            guard_constraints=tuple(guard_constraints),
            signed_counter=bool(signed_counter),
            start_index=next_start,
            start_offset=next_start * 4,
        )

    monkeypatch.setattr(ReductionAccumulatorProof, "with_runtime_evidence", fake_with_runtime_evidence)
    monkeypatch.setattr(
        summarizer,
        "_extract_readonly_reduction_exact_witnesses",
        lambda *_args, **_kwargs: (),
    )
    monkeypatch.setattr(
        summarizer,
        "_build_readonly_reduction_semantic_witnesses",
        lambda *_args, **_kwargs: (),
    )
    monkeypatch.setattr(
        summarizer,
        "_readonly_reduction_positive_conditions",
        lambda _analysis, _pointer_param, _count_param, loop_start_index=0, signed_counter=True: [
            _cond("INT_NOTEQUAL", _param("param_1", size=8), _const(0, size=8)),
            _cond("INT_SLESS", _const(int(loop_start_index)), count_expr),
        ],
    )
    monkeypatch.setattr(
        summarizer,
        "_readonly_reduction_replaceable_positive_returns",
        lambda *_args, **_kwargs: [broad_ret],
    )

    assert summarizer._normalize_readonly_reduction_candidate(
        analysis,
        pointer_param,
        count_param,
        broad_positive_conditions=[
            _cond("INT_NOTEQUAL", _param("param_1", size=8), _const(0, size=8)),
            _cond("INT_SLESS", _const(0), count_expr),
        ],
        positive_conditions=[
            _cond("INT_NOTEQUAL", _param("param_1", size=8), _const(0, size=8)),
            _cond("INT_SLESS", _const(2), count_expr),
        ],
        counter_signed=True,
        accumulator_proof=proof,
        overlapping_positive_returns=[broad_ret],
    ) is None


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
    ) == [ReadonlyRoundedCountCandidate(rounded_vn, 8, 0)]


def test_round_down_candidate_tracks_peeled_prefix_through_count_minus_constant():
    count_expr = Expression.parameter("param_2", index=1, data_type="int", size=4)
    count_vn = _FakeVarnode("param_2", size=4, expr=count_expr)
    zext_vn = _FakeVarnode("count_zext", size=8, expr=Expression.unary_op("INT_ZEXT", count_expr))
    zext_op = _FakePcodeOp("INT_ZEXT", [count_vn], zext_vn)
    three_vn = _FakeVarnode("three", size=8, expr=Expression.constant(3, size=8))
    peeled_vn = _FakeVarnode(
        "peeled_count",
        size=8,
        expr=Expression.binary_op(
            "INT_SUB",
            Expression.unary_op("INT_ZEXT", count_expr),
            Expression.constant(3, size=8),
        ),
    )
    sub_op = _FakePcodeOp("INT_SUB", [zext_vn, three_vn], peeled_vn)
    mask_vn = _FakeVarnode("mask", size=8, expr=Expression.constant(0xFFFFFFF8, size=8))
    rounded_vn = _FakeVarnode("rounded", size=8)
    round_op = _FakePcodeOp("INT_AND", [peeled_vn, mask_vn], rounded_vn)
    summarizer = StructuralRecurrenceSummarizer(_FakeTracer("unused", _const(0)), debug=False)

    assert summarizer._readonly_round_down_candidates(
        [zext_op, sub_op, round_op],
        {"name": "param_2", "index": 1, "data_type": "int", "size": 4},
    ) == [ReadonlyRoundedCountCandidate(rounded_vn, 8, 3)]


def test_round_down_candidate_accepts_divide_multiply_form():
    count_expr = Expression.parameter("param_2", index=1, data_type="int", size=4)
    count_vn = _FakeVarnode("param_2", size=4, expr=count_expr)
    three_vn = _FakeVarnode("three", size=4, expr=Expression.constant(3, size=4))
    peeled_vn = _FakeVarnode(
        "peeled_count",
        size=4,
        expr=Expression.binary_op("INT_SUB", count_expr, Expression.constant(3, size=4)),
    )
    sub_op = _FakePcodeOp("INT_SUB", [count_vn, three_vn], peeled_vn)
    four_vn = _FakeVarnode("four", size=4, expr=Expression.constant(4, size=4))
    quotient_vn = _FakeVarnode("quotient", size=4)
    div_op = _FakePcodeOp("INT_DIV", [peeled_vn, four_vn], quotient_vn)
    rounded_vn = _FakeVarnode("rounded", size=4)
    mul_op = _FakePcodeOp("INT_MULT", [quotient_vn, four_vn], rounded_vn)
    summarizer = StructuralRecurrenceSummarizer(_FakeTracer("unused", _const(0)), debug=False)

    assert summarizer._readonly_round_down_candidates(
        [sub_op, div_op, mul_op],
        {"name": "param_2", "index": 1, "data_type": "int", "size": 4},
    ) == [ReadonlyRoundedCountCandidate(rounded_vn, 4, 3)]


def test_round_down_candidate_accepts_preadvanced_divide_multiply_form():
    count_expr = Expression.parameter("param_2", index=1, data_type="int", size=4)
    count_vn = _FakeVarnode("param_2", size=4, expr=count_expr)
    three_vn = _FakeVarnode("three", size=4, expr=Expression.constant(3, size=4))
    peeled_vn = _FakeVarnode(
        "peeled_count",
        size=4,
        expr=Expression.binary_op("INT_SUB", count_expr, Expression.constant(3, size=4)),
    )
    sub_op = _FakePcodeOp("INT_SUB", [count_vn, three_vn], peeled_vn)
    shift_vn = _FakeVarnode("shift", size=4, expr=Expression.constant(2, size=4))
    quotient_vn = _FakeVarnode("quotient", size=4)
    right_op = _FakePcodeOp("INT_RIGHT", [peeled_vn, shift_vn], quotient_vn)
    one_vn = _FakeVarnode("one", size=4, expr=Expression.constant(1, size=4))
    quotient_minus_one_vn = _FakeVarnode("quotient_minus_one", size=4)
    minus_one_op = _FakePcodeOp("INT_SUB", [quotient_vn, one_vn], quotient_minus_one_vn)
    four_vn = _FakeVarnode("four", size=4, expr=Expression.constant(4, size=4))
    rounded_vn = _FakeVarnode("rounded_preadvanced", size=4)
    mul_op = _FakePcodeOp("INT_MULT", [quotient_minus_one_vn, four_vn], rounded_vn)
    summarizer = StructuralRecurrenceSummarizer(_FakeTracer("unused", _const(0)), debug=False)

    assert summarizer._readonly_round_down_candidates(
        [sub_op, right_op, minus_one_op, mul_op],
        {"name": "param_2", "index": 1, "data_type": "int", "size": 4},
    ) == [ReadonlyRoundedCountCandidate(rounded_vn, 4, 3, 4, peeled_vn)]


def test_round_down_candidate_accepts_shift_pair_form():
    count_expr = Expression.parameter("param_2", index=1, data_type="int", size=4)
    count_vn = _FakeVarnode("param_2", size=4, expr=count_expr)
    three_vn = _FakeVarnode("three", size=4, expr=Expression.constant(3, size=4))
    peeled_vn = _FakeVarnode(
        "peeled_count",
        size=4,
        expr=Expression.binary_op("INT_SUB", count_expr, Expression.constant(3, size=4)),
    )
    sub_op = _FakePcodeOp("INT_SUB", [count_vn, three_vn], peeled_vn)
    shift_vn = _FakeVarnode("shift", size=4, expr=Expression.constant(2, size=4))
    quotient_vn = _FakeVarnode("quotient", size=4)
    right_op = _FakePcodeOp("INT_RIGHT", [peeled_vn, shift_vn], quotient_vn)
    rounded_vn = _FakeVarnode("rounded", size=4)
    left_op = _FakePcodeOp("INT_LEFT", [quotient_vn, shift_vn], rounded_vn)
    summarizer = StructuralRecurrenceSummarizer(_FakeTracer("unused", _const(0)), debug=False)

    assert summarizer._readonly_round_down_candidates(
        [sub_op, right_op, left_op],
        {"name": "param_2", "index": 1, "data_type": "int", "size": 4},
    ) == [ReadonlyRoundedCountCandidate(rounded_vn, 4, 3)]


def test_tail_start_from_peeled_rounded_count_accepts_object_offset():
    pointer_expr = Expression.parameter("param_1", index=0, data_type="int *", size=8)
    pointer_vn = _FakeVarnode("param_1", size=8, expr=pointer_expr)
    rounded_vn = _FakeVarnode("rounded", size=8)
    four_vn = _FakeVarnode("four", size=8, expr=Expression.constant(4, size=8))
    tail_start_vn = _FakeVarnode("tail_start", size=8)
    tail_start_op = _FakePcodeOp("PTRADD", [pointer_vn, rounded_vn, four_vn], tail_start_vn)
    twelve_vn = _FakeVarnode("twelve", size=8, expr=Expression.constant(12, size=8))
    peeled_tail_start_vn = _FakeVarnode("peeled_tail_start", size=8)
    add_op = _FakePcodeOp("INT_ADD", [tail_start_vn, twelve_vn], peeled_tail_start_vn)
    summarizer = StructuralRecurrenceSummarizer(_FakeTracer("unused", _const(0)), debug=False)

    assert summarizer._tail_start_varnodes_from_rounded_count(
        [tail_start_op, add_op],
        {"name": "param_1", "index": 0, "data_type": "int *", "size": 8},
        rounded_vn,
        element_size=4,
        start_offset=12,
    ) == (peeled_tail_start_vn,)


def test_tail_start_from_peeled_rounded_count_accepts_low_bit_or_index():
    pointer_expr = Expression.parameter("param_1", index=0, data_type="int *", size=8)
    pointer_vn = _FakeVarnode("param_1", size=8, expr=pointer_expr)
    count_expr = Expression.parameter("param_2", index=1, data_type="int", size=4)
    count_vn = _FakeVarnode("param_2", size=4, expr=count_expr)
    three_vn = _FakeVarnode("three", size=8, expr=Expression.constant(3, size=8))
    peeled_vn = _FakeVarnode("peeled", size=8)
    peeled_op = _FakePcodeOp("INT_SUB", [count_vn, three_vn], peeled_vn)
    mask_vn = _FakeVarnode("mask", size=8, expr=Expression.constant(0xFFFFFFFFFFFFFFF8, size=8))
    rounded_vn = _FakeVarnode("rounded", size=8)
    rounded_op = _FakePcodeOp("INT_AND", [peeled_vn, mask_vn], rounded_vn)
    rounded_or_three = _FakeVarnode("rounded_or_three", size=8)
    or_op = _FakePcodeOp("INT_OR", [rounded_vn, three_vn], rounded_or_three)
    four_vn = _FakeVarnode("four", size=8, expr=Expression.constant(4, size=8))
    tail_start_vn = _FakeVarnode("tail_start", size=8)
    tail_start_op = _FakePcodeOp("PTRADD", [pointer_vn, rounded_or_three, four_vn], tail_start_vn)
    summarizer = StructuralRecurrenceSummarizer(_FakeTracer("unused", _const(0)), debug=False)

    assert summarizer._tail_start_varnodes_from_rounded_count(
        [peeled_op, rounded_op, or_op, tail_start_op],
        {"name": "param_1", "index": 0, "data_type": "int *", "size": 8},
        rounded_vn,
        element_size=4,
        start_offset=12,
    ) == (tail_start_vn,)


def test_tail_start_from_peeled_rounded_count_accepts_scaled_low_bit_or_offset():
    pointer_expr = Expression.parameter("param_1", index=0, data_type="int *", size=8)
    pointer_vn = _FakeVarnode("param_1", size=8, expr=pointer_expr)
    count_expr = Expression.parameter("param_2", index=1, data_type="int", size=4)
    count_vn = _FakeVarnode("param_2", size=4, expr=count_expr)
    three_vn = _FakeVarnode("three", size=8, expr=Expression.constant(3, size=8))
    peeled_vn = _FakeVarnode("peeled", size=8)
    peeled_op = _FakePcodeOp("INT_SUB", [count_vn, three_vn], peeled_vn)
    mask_vn = _FakeVarnode("mask", size=8, expr=Expression.constant(0xFFFFFFFFFFFFFFF8, size=8))
    rounded_vn = _FakeVarnode("rounded", size=8)
    rounded_op = _FakePcodeOp("INT_AND", [peeled_vn, mask_vn], rounded_vn)
    rounded_or_three = _FakeVarnode("rounded_or_three", size=8)
    or_op = _FakePcodeOp("INT_OR", [rounded_vn, three_vn], rounded_or_three)
    two_vn = _FakeVarnode("two", size=8, expr=Expression.constant(2, size=8))
    scaled_vn = _FakeVarnode("scaled", size=8)
    scale_op = _FakePcodeOp("INT_LEFT", [rounded_or_three, two_vn], scaled_vn)
    tail_start_vn = _FakeVarnode("tail_start", size=8)
    tail_start_op = _FakePcodeOp("INT_ADD", [pointer_vn, scaled_vn], tail_start_vn)
    summarizer = StructuralRecurrenceSummarizer(_FakeTracer("unused", _const(0)), debug=False)

    assert summarizer._tail_start_varnodes_from_rounded_count(
        [peeled_op, rounded_op, or_op, scale_op, tail_start_op],
        {"name": "param_1", "index": 0, "data_type": "int *", "size": 8},
        rounded_vn,
        element_size=4,
        start_offset=12,
    ) == (tail_start_vn,)


def test_tail_start_from_peeled_rounded_count_accepts_tail_index_phi():
    pointer_expr = Expression.parameter("param_1", index=0, data_type="int *", size=8)
    pointer_vn = _FakeVarnode("param_1", size=8, expr=pointer_expr)
    count_expr = Expression.parameter("param_2", index=1, data_type="int", size=4)
    count_vn = _FakeVarnode("param_2", size=4, expr=count_expr)
    three_vn = _FakeVarnode("three", size=8, expr=Expression.constant(3, size=8))
    peeled_vn = _FakeVarnode("peeled", size=8)
    peeled_op = _FakePcodeOp("INT_SUB", [count_vn, three_vn], peeled_vn)
    mask_vn = _FakeVarnode("mask", size=8, expr=Expression.constant(0xFFFFFFFFFFFFFFF8, size=8))
    rounded_vn = _FakeVarnode("rounded", size=8)
    rounded_op = _FakePcodeOp("INT_AND", [peeled_vn, mask_vn], rounded_vn)
    rounded_or_three = _FakeVarnode("rounded_or_three", size=8)
    or_op = _FakePcodeOp("INT_OR", [rounded_vn, three_vn], rounded_or_three)
    tail_index_phi = _FakeVarnode("tail_index_phi", size=8)
    phi_op = _FakePcodeOp("MULTIEQUAL", [three_vn, rounded_or_three], tail_index_phi)
    four_vn = _FakeVarnode("four", size=8, expr=Expression.constant(4, size=8))
    tail_start_vn = _FakeVarnode("tail_start", size=8)
    tail_start_op = _FakePcodeOp("PTRADD", [pointer_vn, tail_index_phi, four_vn], tail_start_vn)
    summarizer = StructuralRecurrenceSummarizer(_FakeTracer("unused", _const(0)), debug=False)

    assert summarizer._tail_start_varnodes_from_rounded_count(
        [peeled_op, rounded_op, or_op, phi_op, tail_start_op],
        {"name": "param_1", "index": 0, "data_type": "int *", "size": 8},
        rounded_vn,
        element_size=4,
        start_offset=12,
    ) == (tail_start_vn,)


def test_rounded_count_source_accepts_large_peel_offsets():
    count_expr = Expression.parameter("param_2", index=1, data_type="int", size=4)
    count_vn = _FakeVarnode("param_2", size=8, expr=count_expr)
    large_peeled = 257
    peeled_sub_vn = _FakeVarnode("peeled", size=8)
    peeled_sub_op = _FakePcodeOp(
        "INT_SUB",
        [count_vn, _FakeVarnode("large_const", size=8, expr=Expression.constant(large_peeled, size=8))],
        peeled_sub_vn,
    )
    large_added = -257
    peeled_add_vn = _FakeVarnode("peeled_add", size=8)
    peeled_add_op = _FakePcodeOp(
        "INT_ADD",
        [count_vn, _FakeVarnode("large_neg", size=8, expr=Expression.constant(large_added, size=8))],
        peeled_add_vn,
    )
    summarizer = StructuralRecurrenceSummarizer(_FakeTracer("unused", _const(0)), debug=False)

    assert summarizer._rounded_count_source(
        peeled_sub_vn,
        {"name": "param_2", "index": 1, "data_type": "int", "size": 4},
    ) == (count_vn, large_peeled)
    assert summarizer._rounded_count_source(
        peeled_add_vn,
        {"name": "param_2", "index": 1, "data_type": "int", "size": 4},
    ) == (count_vn, abs(large_added))


def test_count_minus_rounded_accepts_tail_index_phi():
    count_expr = Expression.parameter("param_2", index=1, data_type="int", size=4)
    count_vn = _FakeVarnode("param_2", size=4, expr=count_expr)
    three_vn = _FakeVarnode("three", size=8, expr=Expression.constant(3, size=8))
    peeled_vn = _FakeVarnode("peeled", size=8)
    peeled_op = _FakePcodeOp("INT_SUB", [count_vn, three_vn], peeled_vn)
    mask_vn = _FakeVarnode("mask", size=8, expr=Expression.constant(0xFFFFFFFFFFFFFFF8, size=8))
    rounded_vn = _FakeVarnode("rounded", size=8)
    rounded_op = _FakePcodeOp("INT_AND", [peeled_vn, mask_vn], rounded_vn)
    rounded_or_three = _FakeVarnode("rounded_or_three", size=8)
    or_op = _FakePcodeOp("INT_OR", [rounded_vn, three_vn], rounded_or_three)
    tail_index_phi = _FakeVarnode("tail_index_phi", size=8)
    phi_op = _FakePcodeOp("MULTIEQUAL", [three_vn, rounded_or_three], tail_index_phi)
    remaining_vn = _FakeVarnode("remaining", size=8)
    remaining_op = _FakePcodeOp("INT_SUB", [count_vn, tail_index_phi], remaining_vn)
    summarizer = StructuralRecurrenceSummarizer(_FakeTracer("unused", _const(0)), debug=False)

    assert summarizer._varnode_is_count_minus_rounded(
        remaining_vn,
        {"name": "param_2", "index": 1, "data_type": "int", "size": 4},
        rounded_vn,
        start_index=3,
    )


def test_varnode_is_base_plus_scaled_counter_rejects_unlinked_tail_start_constant():
    pointer_expr = Expression.parameter("param_1", index=0, data_type="int *", size=8)
    pointer_vn = _FakeVarnode("param_1", size=8, expr=pointer_expr)
    rounded_vn = _FakeVarnode("rounded", size=8)
    three_vn = _FakeVarnode("three", size=8, expr=Expression.constant(3, size=8))
    four_vn = _FakeVarnode("four", size=8, expr=Expression.constant(4, size=8))
    tail_start_vn = _FakeVarnode("tail_start", size=8)
    _FakePcodeOp("PTRADD", [pointer_vn, three_vn, four_vn], tail_start_vn)
    summarizer = StructuralRecurrenceSummarizer(_FakeTracer("unused", _const(0)), debug=False)

    assert summarizer._varnode_is_base_plus_scaled_counter(
        tail_start_vn,
        {"name": "param_1", "index": 0, "data_type": "int *", "size": 8},
        rounded_vn,
        element_size=4,
        byte_offset=12,
    ) is False


def test_counter_low_bits_clear_allows_large_or_delta_without_heuristic_cap():
    count_expr = Expression.parameter("param_2", index=1, data_type="int", size=4)
    count_vn = _FakeVarnode("param_2", size=8, expr=count_expr)
    clear_bit = 1 << 8
    mask_value = (1 << 64) - 1 - clear_bit
    and_op = _FakePcodeOp(
        "INT_AND",
        [count_vn, _FakeVarnode("mask", size=8, expr=Expression.constant(mask_value, size=8))],
        _FakeVarnode("rounded", size=8),
    )
    rounded_vn = and_op.getOutput()
    summarizer = StructuralRecurrenceSummarizer(_FakeTracer("unused", _const(0)), debug=False)

    assert summarizer._counter_low_bits_clear_for_or_delta(rounded_vn, 256) is True


def test_counter_low_bits_clear_rejects_high_bit_or_delta_with_zext_counter():
    count_expr = Expression.parameter("param_2", index=1, data_type="int", size=4)
    count_vn = _FakeVarnode("param_2", size=4, expr=count_expr)
    zext_vn = _FakeVarnode("param_2_zext", size=8, expr=Expression.unary_op("INT_ZEXT", count_expr))
    zext_op = _FakePcodeOp("INT_ZEXT", [count_vn], zext_vn)
    clear_bit = 1 << 40
    mask_value = (1 << 64) - 1 - (clear_bit)
    mask_vn = _FakeVarnode("mask", size=8, expr=Expression.constant(mask_value, size=8))
    and_vn = _FakeVarnode("rounded", size=8)
    _FakePcodeOp("INT_AND", [zext_vn, mask_vn], and_vn)
    summarizer = StructuralRecurrenceSummarizer(_FakeTracer("unused", _const(0)), debug=False)

    assert summarizer._counter_low_bits_clear_for_or_delta(and_vn, clear_bit) is False


def test_vectorized_readonly_prefix_proof_records_seed_term_count(monkeypatch):
    pointer_param = {"name": "param_1", "index": 0, "data_type": "int *", "size": 8}
    count_param = {"name": "param_2", "index": 1, "data_type": "uint", "size": 4, "is_signed": False}
    analysis = create_mock_analysis(
        "sum_vectorized_seed_term_count",
        return_type="int",
        parameters=[pointer_param, count_param],
        returns=[
            ReturnInfo(
                address="0x1000",
                pcode_time=10,
                value=_const(0),
                conditions=[
                    _cond(
                        "INT_SLESS",
                        Expression.constant(0, size=4),
                        Expression.parameter("param_2", index=1, data_type="uint", size=4),
                    )
                ],
            )
        ],
    )

    large_start_index = 128_000
    rounded_vn = _FakeVarnode("rounded", size=8)
    summarizer = StructuralRecurrenceSummarizer(_FakeTracer("unused", _const(0)), debug=False)

    monkeypatch.setattr(
        summarizer,
        "_readonly_round_down_candidates",
        lambda *_args, **_kwargs: [ReadonlyRoundedCountCandidate(rounded_vn, 8, large_start_index)],
    )
    vector_phi = _FakeVarnode("vector_phi", size=8)
    monkeypatch.setattr(
        summarizer,
        "_match_vector_prefix_pointer",
        lambda *_args, **_kwargs: (vector_phi, 0, 0),
    )
    monkeypatch.setattr(
        summarizer,
        "_vector_prefix_lanes_cover_block",
        lambda *_args, **_kwargs: True,
    )
    monkeypatch.setattr(
        summarizer,
        "_vector_prefix_lanes_have_unit_terms_in_positive_return",
        lambda *_args, **_kwargs: True,
    )
    monkeypatch.setattr(
        summarizer,
        "_vector_prefix_lanes_contribute_additively_to_return",
        lambda *_args, **_kwargs: True,
    )
    monkeypatch.setattr(
        summarizer,
        "_vector_prefix_unit_term_positive_return_refs",
        lambda *_args, **_kwargs: (PcodeOpRef(address_offset=0x1000, seq_time=10, mnemonic="RETURN"),),
    )
    monkeypatch.setattr(
        summarizer,
        "_vector_prefix_lane_return_refs",
        lambda *_args, **_kwargs: (
            (PcodeOpRef(address_offset=0x1000, seq_time=10, mnemonic="RETURN"),),
            (PcodeOpRef(address_offset=0x1000, seq_time=9, mnemonic="INT_ADD"),),
        ),
    )
    monkeypatch.setattr(
        summarizer,
        "_has_vector_countdown_loop",
        lambda *_args, **_kwargs: False,
    )
    monkeypatch.setattr(
        summarizer,
        "_has_vector_loop_bound_to_rounded_count",
        lambda *_args, **_kwargs: True,
    )
    monkeypatch.setattr(
        summarizer,
        "_has_scalar_tail_from_rounded_count",
        lambda *_args, **_kwargs: True,
    )

    proof = summarizer._detect_vectorized_readonly_prefix_sum_accumulator_proof(
        [],
        pointer_param,
        count_param,
        LocationBaseRef.parameter("param_1", index=0),
        Expression.parameter("param_2", index=1, data_type="uint", size=4),
        analysis,
        counter_signed=False,
    )

    assert proof is not None
    assert proof.seed_terms == ()
    assert proof.seed_term_count == large_start_index
    assert proof.start_index == large_start_index
    assert proof.start_offset == large_start_index * 4
    assert proof.return_region_value_proven is True
    assert proof.return_value_op_refs
    assert proof.source == "vectorized_readonly_prefix_sum"
    assert proof.seed_terms_for_count_value(3) == (
        ReadonlyReductionTermRef(byte_offset=0, access_size=4),
        ReadonlyReductionTermRef(byte_offset=4, access_size=4),
        ReadonlyReductionTermRef(byte_offset=8, access_size=4),
    )
    assert proof.seed_terms_for_count_value(large_start_index + 1) == ()


def test_vectorized_readonly_prefix_proof_accepts_def_use_return_site_proof_without_exact_witness(monkeypatch):
    pointer_param = {"name": "param_1", "index": 0, "data_type": "int *", "size": 8}
    count_param = {"name": "param_2", "index": 1, "data_type": "int", "size": 4, "is_signed": True}
    analysis = create_mock_analysis(
        "sum_vectorized_def_use_region_proof",
        return_type="int",
        parameters=[pointer_param, count_param],
        returns=[
            ReturnInfo(
                address="0x2000",
                pcode_time=20,
                value=Expression.unknown("phi_circular"),
                conditions=[
                    _cond(
                        "INT_NOTEQUAL",
                        Expression.parameter("param_1", index=0, data_type="int *", size=8),
                        Expression.constant(0, size=8),
                    ),
                    _cond(
                        "INT_SLESS",
                        Expression.constant(0, size=4),
                        Expression.parameter("param_2", index=1, data_type="int", size=4),
                    ),
                ],
            )
        ],
    )

    rounded_vn = _FakeVarnode("rounded", size=8)
    summarizer = StructuralRecurrenceSummarizer(_FakeTracer("unused", _const(0)), debug=False)

    monkeypatch.setattr(
        summarizer,
        "_readonly_round_down_candidates",
        lambda *_args, **_kwargs: [ReadonlyRoundedCountCandidate(rounded_vn, 8, 3)],
    )
    vector_phi = _FakeVarnode("vector_phi", size=8)
    monkeypatch.setattr(
        summarizer,
        "_match_vector_prefix_pointer",
        lambda *_args, **_kwargs: (vector_phi, 0, 0),
    )
    monkeypatch.setattr(
        summarizer,
        "_vector_prefix_lanes_cover_block",
        lambda *_args, **_kwargs: True,
    )
    monkeypatch.setattr(
        summarizer,
        "_vector_prefix_lanes_have_unit_terms_in_positive_return",
        lambda *_args, **_kwargs: False,
    )
    monkeypatch.setattr(
        summarizer,
        "_vector_prefix_lanes_contribute_additively_to_return",
        lambda *_args, **_kwargs: True,
    )
    monkeypatch.setattr(
        summarizer,
        "_vector_prefix_unit_term_positive_return_refs",
        lambda *_args, **_kwargs: (),
    )
    monkeypatch.setattr(
        summarizer,
        "_vector_prefix_lane_return_refs",
        lambda *_args, **_kwargs: (
            (PcodeOpRef(address_offset=0x2000, seq_time=20, mnemonic="RETURN"),),
            (PcodeOpRef(address_offset=0x2000, seq_time=19, mnemonic="INT_ADD"),),
        ),
    )
    monkeypatch.setattr(
        summarizer,
        "_has_vector_countdown_loop",
        lambda *_args, **_kwargs: False,
    )
    monkeypatch.setattr(
        summarizer,
        "_has_vector_loop_bound_to_rounded_count",
        lambda *_args, **_kwargs: True,
    )
    monkeypatch.setattr(
        summarizer,
        "_has_scalar_tail_from_rounded_count",
        lambda *_args, **_kwargs: True,
    )

    proof = summarizer._detect_vectorized_readonly_prefix_sum_accumulator_proof(
        [],
        pointer_param,
        count_param,
        LocationBaseRef.parameter("param_1", index=0),
        Expression.parameter("param_2", index=1, data_type="int", size=4),
        analysis,
        counter_signed=True,
    )

    assert proof is not None
    assert proof.return_region_value_proven is True
    assert proof.return_op_refs == (PcodeOpRef(address_offset=0x2000, seq_time=20, mnemonic="RETURN"),)
    assert proof.return_value_op_refs == (PcodeOpRef(address_offset=0x2000, seq_time=19, mnemonic="INT_ADD"),)
    assert proof.start_index == 3
    assert proof.start_offset == 12
    assert proof.source == "vectorized_readonly_prefix_sum"


def test_pointer_progression_phi_tracks_peeled_pointer_seed_offset():
    pointer_expr = Expression.parameter("param_1", index=0, data_type="int *", size=8)
    pointer_vn = _FakeVarnode("param_1", size=8, expr=pointer_expr)
    three_vn = _FakeVarnode("three", size=8, expr=Expression.constant(3, size=8))
    four_vn = _FakeVarnode("four", size=8, expr=Expression.constant(4, size=8))
    init_vn = _FakeVarnode("init", size=8)
    init_op = _FakePcodeOp("PTRADD", [pointer_vn, three_vn, four_vn], init_vn)
    phi_vn = _FakeVarnode("ptr_phi", size=8, high=_FakeHighVar("ptr_phi"))
    next_vn = _FakeVarnode("next", size=8)
    next_op = _FakePcodeOp("PTRADD", [phi_vn, _FakeVarnode("one", size=8, expr=Expression.constant(1, size=8)), four_vn], next_vn)
    phi_op = _FakePcodeOp("MULTIEQUAL", [init_vn, next_vn], phi_vn)
    summarizer = StructuralRecurrenceSummarizer(_FakeTracer("unused", _const(0)), debug=False)

    assert init_op.getOutput() is init_vn
    assert next_op.getOutput() is next_vn
    assert summarizer._match_pointer_progression_phi(
        phi_op,
        {"name": "param_1", "index": 0, "data_type": "int *", "size": 8},
    ) == {
        "phi_op": phi_op,
        "phi_output": phi_vn,
        "stride": 4,
        "start_offset": 12,
        "start_index": 3,
        "index_step": 1,
        "index_scale": 4,
    }


def test_pointer_progression_phi_tracks_peeled_pointer_seed_offset_with_same_high():
    pointer_high = _FakeHighVar("param_1")
    pointer_expr = Expression.parameter("param_1", index=0, data_type="int *", size=8)
    pointer_vn = _FakeVarnode("param_1", size=8, expr=pointer_expr, high=pointer_high)
    three_vn = _FakeVarnode("three", size=8, expr=Expression.constant(3, size=8))
    four_vn = _FakeVarnode("four", size=8, expr=Expression.constant(4, size=8))
    init_vn = _FakeVarnode("init", size=8, high=pointer_high)
    init_op = _FakePcodeOp("PTRADD", [pointer_vn, three_vn, four_vn], init_vn)
    phi_vn = _FakeVarnode("ptr_phi", size=8, high=_FakeHighVar("ptr_phi"))
    next_vn = _FakeVarnode("next", size=8)
    next_op = _FakePcodeOp(
        "PTRADD",
        [phi_vn, _FakeVarnode("one", size=8, expr=Expression.constant(1, size=8)), four_vn],
        next_vn,
    )
    phi_op = _FakePcodeOp("MULTIEQUAL", [init_vn, next_vn], phi_vn)
    summarizer = StructuralRecurrenceSummarizer(_FakeTracer("unused", _const(0)), debug=False)

    assert init_op.getOutput() is init_vn
    assert next_op.getOutput() is next_vn
    assert summarizer._match_pointer_progression_phi(
        phi_op,
        {"name": "param_1", "index": 0, "data_type": "int *", "size": 8},
    ) == {
        "phi_op": phi_op,
        "phi_output": phi_vn,
        "stride": 4,
        "start_offset": 12,
        "start_index": 3,
        "index_step": 1,
        "index_scale": 4,
    }


def test_phi_input_resolution_keeps_cross_storage_parameter_seed_over_later_def():
    pointer_high = _FakeHighVar("param_1")
    end_high = _FakeHighVar("end_pointer")
    raw_param = _FakeVarnode("a0_param", size=8, high=pointer_high, storage_offset=0x20)
    end_pointer = _FakeVarnode("a0_end", size=8, high=end_high, storage_offset=0x20)
    cursor_phi = _FakeVarnode("cursor_phi", size=8, high=pointer_high, storage_offset=0x18)
    cursor_next = _FakeVarnode("cursor_next", size=8, high=pointer_high, storage_offset=0x18)
    one_vn = _FakeVarnode("one", size=8, expr=Expression.constant(1, size=8))
    four_vn = _FakeVarnode("four", size=8, expr=Expression.constant(4, size=8))

    end_def = _FakePcodeOp("PTRADD", [raw_param, one_vn, four_vn], end_pointer)
    phi_op = _FakePcodeOp("MULTIEQUAL", [raw_param, cursor_phi], cursor_phi)
    cursor_step = _FakePcodeOp("PTRADD", [cursor_phi, one_vn, four_vn], cursor_next)
    preheader = _FakeCfgBlock(0, [end_def])
    loop = _FakeCfgBlock(1, [phi_op, cursor_step])
    preheader.add_edge(loop)
    loop.add_edge(loop)
    summarizer = StructuralRecurrenceSummarizer(_FakeTracer("unused", _const(0)), debug=False)

    assert summarizer._phi_input_value_varnode(phi_op, 0) is raw_param
    assert summarizer._phi_input_value_varnode(phi_op, 1) is cursor_next


def test_vector_prefix_pointer_requires_peeled_seed_offset_object_link():
    pointer_expr = Expression.parameter("param_1", index=0, data_type="int *", size=8)
    pointer_vn = _FakeVarnode("param_1", size=8, expr=pointer_expr)
    three_vn = _FakeVarnode("three", size=8, expr=Expression.constant(3, size=8))
    four_vn = _FakeVarnode("four", size=8, expr=Expression.constant(4, size=8))
    seed_vn = _FakeVarnode("seed", size=8)
    seed_op = _FakePcodeOp("PTRADD", [pointer_vn, three_vn, four_vn], seed_vn)
    vector_phi = _FakeVarnode("vector_phi", size=8, high=_FakeHighVar("vector_phi"))
    vector_next = _FakeVarnode("vector_next", size=8)
    vector_step_op = _FakePcodeOp("PTRADD", [vector_phi, _FakeVarnode("eight", size=8, expr=Expression.constant(8, size=8)), four_vn], vector_next)
    vector_phi_op = _FakePcodeOp("MULTIEQUAL", [seed_vn, vector_next], vector_phi)
    ram_space = _FakeVarnode("ram", size=8, expr=Expression.constant(0, size=8))
    lane0 = _FakeVarnode("lane0", size=4)
    lane1_addr = _FakeVarnode("lane1_addr", size=8)
    lane1_addr_op = _FakePcodeOp("PTRADD", [vector_phi, _FakeVarnode("one", size=8, expr=Expression.constant(1, size=8)), four_vn], lane1_addr)
    lane1 = _FakeVarnode("lane1", size=4)
    load0_op = _FakePcodeOp("LOAD", [ram_space, vector_phi], lane0)
    load1_op = _FakePcodeOp("LOAD", [ram_space, lane1_addr], lane1)
    summarizer = StructuralRecurrenceSummarizer(_FakeTracer("unused", _const(0)), debug=False)

    assert summarizer._match_vector_prefix_pointer(
        [seed_op, vector_step_op, vector_phi_op, lane1_addr_op, load0_op, load1_op],
        {"name": "param_1", "index": 0, "data_type": "int *", "size": 8},
        vector_stride=32,
        element_size=4,
        expected_start_offset=16,
    ) is None
    assert summarizer._match_vector_prefix_pointer(
        [seed_op, vector_step_op, vector_phi_op, lane1_addr_op, load0_op, load1_op],
        {"name": "param_1", "index": 0, "data_type": "int *", "size": 8},
        vector_stride=32,
        element_size=4,
        expected_start_offset=12,
    ) == (vector_phi, 0, 12)


def test_vector_loop_bound_uses_postincrement_def_before_storage_alias():
    pointer_expr = Expression.parameter("param_1", index=0, data_type="int *", size=8)
    pointer_vn = _FakeVarnode("param_1", size=8, expr=pointer_expr)
    rounded_vn = _FakeVarnode("rounded", size=8)
    seven_vn = _FakeVarnode("seven", size=8, expr=Expression.constant(7, size=8))
    four_vn = _FakeVarnode("four", size=8, expr=Expression.constant(4, size=8))
    index_vn = _FakeVarnode("rounded_plus_seven", size=8)
    end_vn = _FakeVarnode("end", size=8)
    cursor_high = _FakeHighVar("cursor")
    cursor_phi = _FakeVarnode("cursor_phi", size=8, high=cursor_high, storage_offset=0x4010)
    cursor_next = _FakeVarnode("cursor_next", size=8, high=cursor_high, storage_offset=0x4010)
    cond_vn = _FakeVarnode("cond", size=1)
    index_op = _FakePcodeOp("INT_ADD", [rounded_vn, seven_vn], index_vn)
    end_op = _FakePcodeOp("PTRADD", [pointer_vn, index_vn, four_vn], end_vn)
    step_op = _FakePcodeOp(
        "PTRADD",
        [cursor_phi, _FakeVarnode("four_lanes", size=8, expr=Expression.constant(4, size=8)), four_vn],
        cursor_next,
    )
    compare_op = _FakePcodeOp("INT_NOTEQUAL", [end_vn, cursor_next], cond_vn)
    summarizer = StructuralRecurrenceSummarizer(_FakeTracer("unused", _const(0)), debug=False)

    assert index_op.getOutput() is index_vn
    assert end_op.getOutput() is end_vn
    assert step_op.getOutput() is cursor_next
    assert summarizer._has_vector_loop_bound_to_rounded_count(
        [index_op, end_op, step_op, compare_op],
        cursor_phi,
        {"name": "param_1", "index": 0, "data_type": "int *", "size": 8},
        rounded_vn,
        element_size=4,
        base_offset=12,
        vector_stride=16,
    )


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

    def capture_accumulator_proof(
        _high_function,
        _analysis,
        _pointer_param,
        _count_param,
        *,
        counter_signed,
        positive_conditions=(),
    ):
        captured["counter_signed"] = counter_signed
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


def test_readonly_sum_detection_prefers_vectorized_before_scalar_phi_match(monkeypatch):
    pointer_param = {"name": "param_1", "index": 0, "data_type": "int *", "size": 8}
    count_param = {"name": "param_2", "index": 1, "data_type": "uint", "size": 4, "is_signed": False}
    analysis = create_mock_analysis(
        "sum_vectorized_primacy",
        return_type="int",
        parameters=[pointer_param, count_param],
        returns=[
            ReturnInfo(
                address="0x1000",
                value=_const(0),
                conditions=[
                    _cond(
                        "INT_SLESS",
                        Expression.constant(0, size=4),
                        Expression.parameter("param_2", index=1, data_type="uint", size=4),
                    ),
                ],
            ),
        ],
    )
    high_function = _FakeHighFunction([])
    summarizer = StructuralRecurrenceSummarizer(_FakeTracer("unused", _const(0)), debug=False)
    invocation = {"vectorized": 0, "scalar": 0}

    expected = _readonly_accumulator_proof(
        base_ref=LocationBaseRef.parameter("param_1", index=0),
        count_expr=Expression.parameter("param_2", index=1, data_type="uint", size=4),
        stride=4,
        element_size=4,
    )

    def capture_vectorized(*_args, **_kwargs):
        invocation["vectorized"] += 1
        return expected

    def capture_scalar(*_args, **_kwargs):
        invocation["scalar"] += 1
        return expected

    monkeypatch.setattr(
        summarizer,
        "_analysis_mentions_parameter_in_conditions",
        lambda _analysis, _param_name: True,
    )
    monkeypatch.setattr(
        summarizer,
        "_detect_vectorized_readonly_prefix_sum_accumulator_proof",
        capture_vectorized,
    )
    monkeypatch.setattr(
        summarizer,
        "_match_accumulator_phi",
        capture_scalar,
    )

    actual = summarizer._detect_readonly_sum_accumulator_proof(
        high_function,
        analysis,
        pointer_param,
        count_param,
        counter_signed=True,
    )

    assert actual == expected
    assert invocation["vectorized"] == 1
    assert invocation["scalar"] == 0


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


def test_readonly_accumulator_proof_materializes_missing_small_prefix_from_larger_exact_witness():
    count_expr = Expression.parameter("param_2", index=1, data_type="int", size=4)
    proof = ReductionAccumulatorProof(
        reduction_kind="memory_sum",
        pointer_base_ref=LocationBaseRef.parameter("param_1", index=0),
        count_parameter_name="param_2",
        count_parameter_index=1,
        limit_expr=count_expr,
        result_size=4,
        stride=16,
        element_size=8,
        start_offset=4,
        start_index=0,
        index_step=1,
        index_scale=16,
        exact_return_witnesses=(
            ReadonlyReductionWitness(
                exact_count=1,
                terms=(ReadonlyReductionTermRef(byte_offset=0, access_size=4),),
            ),
            ReadonlyReductionWitness(
                exact_count=3,
                terms=(
                    ReadonlyReductionTermRef(byte_offset=0, access_size=4),
                    ReadonlyReductionTermRef(byte_offset=4, access_size=4),
                    ReadonlyReductionTermRef(byte_offset=8, access_size=4),
                ),
            ),
        ),
    )

    assert proof.loop_body_terms_for_count_value(2) is None
    assert tuple(term.byte_offset for term in (proof.full_terms_for_count_value(2) or ())) == (
        0,
        4,
    )
    assert proof.full_terms_for_count_value(5) is None


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


def test_return_analyzer_normalization_does_not_widen_readonly_summary_domain():
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

    analysis = create_mock_analysis(
        "readonly_partition_preserved_basic",
        return_type="int",
        parameters=params,
        returns=[corrupted],
    )

    analyzer._normalize_return_partition(analysis)

    normalized_conditions = [cond.to_string() for cond in analysis.returns[0].conditions]

    assert normalized_conditions == ["(0 < param_2)"]
    assert "(3 < param_2)" not in normalized_conditions


def test_return_analyzer_normalization_keeps_existing_readonly_lower_bound():
    analyzer = ReturnAnalyzer(program=None, debug=False)
    params = [
        {"name": "param_1", "index": 0, "data_type": "int *", "size": 8},
        {"name": "param_2", "index": 1, "data_type": "int", "size": 4, "is_signed": True},
    ]
    base_ref = LocationBaseRef.parameter("param_1", index=0)
    count_expr = _param("param_2", size=4)
    accumulator_proof = _readonly_accumulator_proof(
        base_ref=base_ref,
        count_expr=count_expr,
        stride=4,
        element_size=4,
        start_index=3,
    )
    reduction_expr = Expression.intrinsic(
        "READONLY_SUM",
        [
            Expression.parameter("param_1", index=0, data_type="int *", size=8),
            Expression.parameter("param_2", index=1, data_type="int", size=4),
        ],
        size=4,
        runtime_ref=ReadonlyReductionRef(
            reduction_kind="readonly_sum",
            pointer_base_ref=base_ref,
            count_parameter_name="param_2",
            count_parameter_index=1,
            stride=4,
            element_size=4,
            result_size=4,
            signed_counter=True,
            accumulator_proof=accumulator_proof,
        ),
        opcode=READONLY_SUM_OPCODE,
    )
    corrupted = ReturnInfo(
        address="0x1010",
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

    analysis = create_mock_analysis(
        "readonly_partition_preserved_with_start_index",
        return_type="int",
        parameters=params,
        returns=[corrupted],
    )

    analyzer._normalize_return_partition(analysis)

    normalized_conditions = [cond.to_string() for cond in analysis.returns[0].conditions]

    assert normalized_conditions == ["(0 < param_2)"]
    assert "(3 < param_2)" not in normalized_conditions


def test_structural_recurrence_positive_guard_uses_unsigned_compare_for_unsigned_count():
    summarizer = StructuralRecurrenceSummarizer(tracer=None, debug=False)
    pointer_param = {"name": "param_1", "index": 0, "data_type": "int *", "size": 8, "is_signed": False}
    count_param = {"name": "param_2", "index": 1, "data_type": "uint", "size": 4, "is_signed": False}

    conditions = summarizer._readonly_reduction_positive_conditions(
        analysis=None,
        pointer_param=pointer_param,
        count_param=count_param,
        loop_start_index=3,
    )

    assert len(conditions) == 2
    assert conditions[1].expression.operator == "INT_LESS"
    assert conditions[1].to_string() == "(3 < param_2)"
    assert (
        summarizer._readonly_reduction_count_compare_op(
            count_param,
            inclusive=True,
        )
        == "INT_LESSEQUAL"
    )


def test_structural_recurrence_prefers_local_signed_counter_evidence_over_declared_unsigned():
    summarizer = StructuralRecurrenceSummarizer(tracer=None, debug=False)
    analysis = FunctionReturnAnalysis(
        function_name="readonly_signed_counter_like",
        entry_point="0x1000",
        parameters=[
            {"name": "param_1", "index": 0, "data_type": "int *", "size": 8, "is_signed": False},
            {"name": "param_2", "index": 1, "data_type": "uint", "size": 4, "is_signed": False},
        ],
        returns=[
            ReturnInfo(
                address="0x1000",
                conditions=[_cond("INT_SLESS", _const(0), _param("param_2"))],
                value=_const(1),
            )
        ],
    )
    count_param = analysis.parameters[1]

    assert summarizer._readonly_reduction_counter_is_signed(analysis.returns, count_param) is True
    assert (
        summarizer._readonly_reduction_count_compare_op(
            count_param,
            signed_counter=True,
            inclusive=True,
        )
        == "INT_SLESSEQUAL"
    )


def test_structural_recurrence_leaves_counter_signedness_ambiguous_when_guards_conflict():
    summarizer = StructuralRecurrenceSummarizer(tracer=None, debug=False)
    analysis = FunctionReturnAnalysis(
        function_name="readonly_ambiguous_counter_like",
        entry_point="0x1000",
        parameters=[
            {"name": "param_1", "index": 0, "data_type": "int *", "size": 8, "is_signed": False},
            {"name": "param_2", "index": 1, "data_type": "uint", "size": 4, "is_signed": False},
        ],
        returns=[
            ReturnInfo(
                address="0x1000",
                conditions=[
                    _cond("INT_SLESS", _const(0), _param("param_2")),
                    _cond("INT_LESS", _const(3), _param("param_2")),
                ],
                value=_const(1),
            )
        ],
    )

    assert (
        summarizer._readonly_reduction_counter_is_signed(
            analysis.returns,
            analysis.parameters[1],
        )
        is None
    )


def test_structural_recurrence_counter_signedness_uses_only_relevant_returns():
    summarizer = StructuralRecurrenceSummarizer(tracer=None, debug=False)
    count_param = {"name": "param_2", "index": 1, "data_type": "uint", "size": 4, "is_signed": False}
    unrelated_signed = ReturnInfo(
        address="0x1000",
        conditions=[_cond("INT_SLESS", _const(0), _param("param_2"))],
        value=_const(1),
    )
    relevant_unsigned = ReturnInfo(
        address="0x1001",
        conditions=[_cond("INT_LESS", _const(3), _param("param_2"))],
        value=_const(2),
    )

    assert (
        summarizer._readonly_reduction_counter_is_signed(
            [unrelated_signed, relevant_unsigned],
            count_param,
        )
        is None
    )
    assert (
        summarizer._readonly_reduction_counter_is_signed(
            [relevant_unsigned],
            count_param,
        )
        is False
    )


def test_structural_recurrence_region_returns_require_per_return_signedness_evidence():
    summarizer = StructuralRecurrenceSummarizer(tracer=None, debug=False)
    count_param = {"name": "param_2", "index": 1, "data_type": "uint", "size": 4, "is_signed": False}
    analysis = FunctionReturnAnalysis(
        function_name="readonly_region_filter_like",
        entry_point="0x1000",
        parameters=[
            {"name": "param_1", "index": 0, "data_type": "int *", "size": 8, "is_signed": False},
            count_param,
        ],
        returns=[
            ReturnInfo(
                address="0x1000",
                conditions=[
                    _cond("INT_NOTEQUAL", _param("param_1", size=8), _const(0, size=8)),
                    _cond("INT_LESS", _const(0), _param("param_2")),
                ],
                value=_const(1),
            ),
            ReturnInfo(
                address="0x1001",
                conditions=[
                    _cond("INT_NOTEQUAL", _param("param_1", size=8), _const(0, size=8)),
                ],
                value=_const(2),
            ),
        ],
    )
    positive_conditions = [
        _cond("INT_NOTEQUAL", _param("param_1", size=8), _const(0, size=8)),
        _cond("INT_LESS", _const(0), _param("param_2")),
    ]

    relevant = summarizer._readonly_reduction_region_returns_with_signedness(
        analysis,
        count_param,
        positive_conditions,
        expected_signed=False,
    )

    assert [ret.address for ret in relevant] == ["0x1000"]


def test_structural_recurrence_declines_summary_when_counter_signedness_is_ambiguous(monkeypatch):
    summarizer = StructuralRecurrenceSummarizer(tracer=None, debug=False)
    analysis = FunctionReturnAnalysis(
        function_name="readonly_ambiguous_counter_like",
        entry_point="0x1000",
        parameters=[
            {"name": "param_1", "index": 0, "data_type": "int *", "size": 8, "is_signed": False},
            {"name": "param_2", "index": 1, "data_type": "uint", "size": 4, "is_signed": False},
        ],
        returns=[ReturnInfo(address="0x1000", conditions=[], value=_const(1))],
    )
    pointer_param = analysis.parameters[0]
    count_param = analysis.parameters[1]

    class _FakeFunction:
        def getName(self):
            return "readonly_ambiguous_counter_like"

    monkeypatch.setattr(
        summarizer,
        "_infer_readonly_pointer_reduction_parameters",
        lambda _analysis, _high_function: (pointer_param, count_param),
    )
    monkeypatch.setattr(
        summarizer,
        "_readonly_reduction_counter_is_signed",
        lambda _analysis, _count_param: None,
    )

    assert (
        summarizer._try_summarize_readonly_pointer_reduction(
            _FakeFunction(),
            object(),
            analysis,
        )
        is None
    )


def test_structural_recurrence_summary_uses_effective_declared_signedness_to_break_viable_tie(monkeypatch):
    summarizer = StructuralRecurrenceSummarizer(tracer=None, debug=False)
    pointer_param = {"name": "param_1", "index": 0, "data_type": "int *", "size": 8, "is_signed": False}
    count_param = {"name": "param_2", "index": 1, "data_type": "uint", "size": 4, "is_signed": False}
    count_expr = Expression.parameter("param_2", index=1, data_type="uint", size=4)
    positive_conditions = [
        _cond("INT_NOTEQUAL", _param("param_1", size=8), _const(0, size=8)),
        _cond("INT_LESS", _const(0), count_expr),
    ]
    positive_ret = ReturnInfo(address="0x1001", conditions=list(positive_conditions), value=_mem("param_1", 0))
    null_ret = ReturnInfo(
        address="0x1000",
        conditions=[_cond("INT_EQUAL", _param("param_1", size=8), _const(0, size=8))],
        value=_const(0),
    )
    analysis = create_mock_analysis(
        "readonly_signedness_tie_break",
        return_type="int",
        parameters=[pointer_param, count_param],
        returns=[null_ret, positive_ret],
    )
    proof = _readonly_accumulator_proof(
        base_ref=LocationBaseRef.parameter("param_1", index=0),
        count_expr=count_expr,
        stride=4,
        element_size=4,
    )

    monkeypatch.setattr(
        summarizer,
        "_infer_readonly_pointer_reduction_parameters",
        lambda _analysis, _high_function: (pointer_param, count_param),
    )
    monkeypatch.setattr(
        summarizer,
        "_readonly_reduction_positive_conditions",
        lambda *_args, **_kwargs: list(positive_conditions),
    )
    monkeypatch.setattr(
        summarizer,
        "_readonly_reduction_region_returns_with_signedness",
        lambda *_args, **_kwargs: [positive_ret],
    )
    monkeypatch.setattr(
        summarizer,
        "_detect_readonly_sum_accumulator_proof",
        lambda *_args, **_kwargs: proof,
    )
    monkeypatch.setattr(
        summarizer,
        "_readonly_reduction_replaceable_positive_returns",
        lambda *_args, **_kwargs: [positive_ret],
    )
    monkeypatch.setattr(
        summarizer,
        "_build_readonly_reduction_semantic_witnesses",
        lambda *_args, **_kwargs: (),
    )
    monkeypatch.setattr(
        summarizer,
        "_extract_readonly_reduction_exact_witnesses",
        lambda *_args, **_kwargs: (),
    )

    summary = summarizer._try_summarize_readonly_pointer_reduction(
        _FakeFunction("readonly_signedness_tie_break"),
        object(),
        analysis,
    )

    assert summary is not None
    summarized_returns, _note = summary
    readonly_ret = next(ret for ret in summarized_returns if getattr(ret.value, "opcode", None) == READONLY_SUM_OPCODE)
    assert readonly_ret.value.runtime_ref.signed_counter is False


def test_structural_recurrence_declines_when_viable_signedness_tie_has_no_local_declaration_winner(monkeypatch):
    summarizer = StructuralRecurrenceSummarizer(tracer=None, debug=False)
    pointer_param = {"name": "param_1", "index": 0, "data_type": "int *", "size": 8, "is_signed": False}
    count_param = {"name": "param_2", "index": 1, "data_type": "uint", "size": 4, "is_signed": None}
    count_expr = Expression.parameter("param_2", index=1, data_type="uint", size=4)
    positive_conditions = [
        _cond("INT_NOTEQUAL", _param("param_1", size=8), _const(0, size=8)),
        _cond("INT_LESS", _const(0), count_expr),
    ]
    positive_ret = ReturnInfo(address="0x1001", conditions=list(positive_conditions), value=_mem("param_1", 0))
    analysis = create_mock_analysis(
        "readonly_signedness_tie_decline",
        return_type="int",
        parameters=[pointer_param, count_param],
        returns=[positive_ret],
    )
    proof = _readonly_accumulator_proof(
        base_ref=LocationBaseRef.parameter("param_1", index=0),
        count_expr=count_expr,
        stride=4,
        element_size=4,
    )

    monkeypatch.setattr(
        summarizer,
        "_infer_readonly_pointer_reduction_parameters",
        lambda _analysis, _high_function: (pointer_param, count_param),
    )
    monkeypatch.setattr(
        summarizer,
        "_readonly_reduction_positive_conditions",
        lambda *_args, **_kwargs: list(positive_conditions),
    )
    monkeypatch.setattr(
        summarizer,
        "_readonly_reduction_region_returns_with_signedness",
        lambda *_args, **_kwargs: [positive_ret],
    )
    monkeypatch.setattr(
        summarizer,
        "_detect_readonly_sum_accumulator_proof",
        lambda *_args, **_kwargs: proof,
    )
    monkeypatch.setattr(
        summarizer,
        "_readonly_reduction_replaceable_positive_returns",
        lambda *_args, **_kwargs: [positive_ret],
    )

    assert (
        summarizer._try_summarize_readonly_pointer_reduction(
            _FakeFunction("readonly_signedness_tie_decline"),
            object(),
            analysis,
        )
        is None
    )


def test_structural_recurrence_preserves_exact_positive_return_as_partition_evidence(monkeypatch):
    summarizer = StructuralRecurrenceSummarizer(tracer=None, debug=False)
    pointer_param = {"name": "param_1", "index": 0, "data_type": "int *", "size": 8, "is_signed": False}
    count_param = {"name": "param_2", "index": 1, "data_type": "int", "size": 4, "is_signed": True}
    count_expr = Expression.parameter("param_2", index=1, data_type="int", size=4)
    positive_conditions = [
        _cond("INT_NOTEQUAL", _param("param_1", size=8), _const(0, size=8)),
        _cond("INT_SLESS", _const(0), count_expr),
    ]
    exact_ret = ReturnInfo(
        address="0x1000",
        value=_mem("param_1", 0),
        conditions=list(positive_conditions) + [_cond("INT_EQUAL", count_expr, _const(1))],
    )
    broad_ret = ReturnInfo(
        address="0x1004",
        value=Expression.binary_op(
            "INT_ADD",
            _mem("param_1", 0),
            _mem("param_1", 4),
        ),
        conditions=list(positive_conditions),
    )
    analysis = create_mock_analysis(
        "readonly_absorb_exact_positive_return",
        return_type="int",
        parameters=[pointer_param, count_param],
        returns=[exact_ret, broad_ret],
    )
    proof = _readonly_accumulator_proof(
        base_ref=LocationBaseRef.parameter("param_1", index=0),
        count_expr=count_expr,
        stride=4,
        element_size=4,
        result_size=4,
    )

    monkeypatch.setattr(
        summarizer,
        "_infer_readonly_pointer_reduction_parameters",
        lambda _analysis, _high_function: (pointer_param, count_param),
    )
    monkeypatch.setattr(
        summarizer,
        "_readonly_reduction_positive_conditions",
        lambda *_args, **_kwargs: list(positive_conditions),
    )
    monkeypatch.setattr(
        summarizer,
        "_readonly_reduction_region_returns",
        lambda _analysis, _conditions: [exact_ret, broad_ret],
    )
    monkeypatch.setattr(
        summarizer,
        "_detect_readonly_sum_accumulator_proof",
        lambda *_args, **_kwargs: proof,
    )
    monkeypatch.setattr(
        summarizer,
        "_readonly_reduction_replaceable_positive_returns",
        lambda *_args, **_kwargs: [exact_ret, broad_ret],
    )
    monkeypatch.setattr(
        summarizer,
        "_build_readonly_reduction_semantic_witnesses",
        lambda *_args, **_kwargs: (),
    )

    class _FakeFunction:
        def getName(self):
            return "readonly_absorb_exact_positive_return"

    summarized = summarizer._try_summarize_readonly_pointer_reduction(
        _FakeFunction(),
        object(),
        analysis,
    )

    assert summarized is not None
    summarized_returns, _note = summarized
    readonly_ret = next(
        ret for ret in summarized_returns
        if getattr(ret.value, "opcode", None) == READONLY_SUM_OPCODE
    )
    assert any(
        getattr(condition, "negated", False)
        and getattr(getattr(condition, "expression", None), "operator", None) == "INT_EQUAL"
        for condition in readonly_ret.conditions
    )
    assert exact_ret in summarized_returns


def test_structural_recurrence_summary_ignores_unrelated_early_return_signedness(monkeypatch):
    summarizer = StructuralRecurrenceSummarizer(tracer=None, debug=False)
    pointer_param = {"name": "param_1", "index": 0, "data_type": "int *", "size": 8, "is_signed": False}
    count_param = {"name": "param_2", "index": 1, "data_type": "uint", "size": 4, "is_signed": False}
    analysis = FunctionReturnAnalysis(
        function_name="readonly_unsigned_positive_region_like",
        entry_point="0x1000",
        parameters=[pointer_param, count_param],
        returns=[
            ReturnInfo(
                address="0x1000",
                conditions=[
                    _cond("INT_EQUAL", _param("param_1", size=8), _const(0, size=8)),
                    _cond("INT_SLESS", _const(0), _param("param_2")),
                ],
                value=_const(0),
            ),
            ReturnInfo(
                address="0x1001",
                conditions=[
                    _cond("INT_NOTEQUAL", _param("param_1", size=8), _const(0, size=8)),
                    _cond("INT_LESS", _const(0), _param("param_2")),
                ],
                value=_const(1),
            ),
        ],
    )
    expected_proof = _readonly_accumulator_proof(
        base_ref=LocationBaseRef.parameter("param_1", index=0),
        count_expr=_param("param_2"),
        stride=4,
        element_size=4,
    )

    class _FakeFunction:
        def getName(self):
            return "readonly_unsigned_positive_region_like"

    monkeypatch.setattr(
        summarizer,
        "_infer_readonly_pointer_reduction_parameters",
        lambda _analysis, _high_function: (pointer_param, count_param),
    )
    monkeypatch.setattr(
        summarizer,
        "_detect_readonly_sum_accumulator_proof",
        lambda *_args, **_kwargs: expected_proof,
    )
    monkeypatch.setattr(
        summarizer,
        "_build_readonly_reduction_semantic_witnesses",
        lambda *_args, **_kwargs: (),
    )
    monkeypatch.setattr(
        summarizer,
        "_extract_readonly_reduction_exact_witnesses",
        lambda *_args, **_kwargs: (),
    )

    summarized = summarizer._try_summarize_readonly_pointer_reduction(
        _FakeFunction(),
        object(),
        analysis,
    )

    assert summarized is not None
    summarized_returns, _label = summarized
    summary_return = next(
        ret for ret in summarized_returns
        if getattr(getattr(ret.value, "runtime_ref", None), "count_parameter_name", None) == "param_2"
    )
    assert summary_return.value.runtime_ref.signed_counter is False


def test_structural_recurrence_declines_summary_when_positive_region_returns_cannot_all_be_replaced(monkeypatch):
    summarizer = StructuralRecurrenceSummarizer(tracer=None, debug=False)
    pointer_param = {"name": "param_1", "index": 0, "data_type": "int *", "size": 8, "is_signed": False}
    count_param = {"name": "param_2", "index": 1, "data_type": "uint", "size": 4, "is_signed": False}
    analysis = FunctionReturnAnalysis(
        function_name="readonly_partial_positive_region_like",
        entry_point="0x1000",
        parameters=[pointer_param, count_param],
        returns=[
            ReturnInfo(
                address="0x1000",
                conditions=[
                    _cond("INT_NOTEQUAL", _param("param_1", size=8), _const(0, size=8)),
                    _cond("INT_LESS", _const(0), _param("param_2")),
                ],
                value=_const(1),
            ),
            ReturnInfo(
                address="0x1001",
                conditions=[
                    _cond("INT_NOTEQUAL", _param("param_1", size=8), _const(0, size=8)),
                    _cond("INT_LESS", _const(0), _param("param_2")),
                    _cond("INT_NOTEQUAL", _param("param_3", size=4), _const(0)),
                ],
                value=_const(2),
            ),
        ],
    )
    expected_proof = _readonly_accumulator_proof(
        base_ref=LocationBaseRef.parameter("param_1", index=0),
        count_expr=_param("param_2"),
        stride=4,
        element_size=4,
    )

    class _FakeFunction:
        def getName(self):
            return "readonly_partial_positive_region_like"

    monkeypatch.setattr(
        summarizer,
        "_infer_readonly_pointer_reduction_parameters",
        lambda _analysis, _high_function: (pointer_param, count_param),
    )
    monkeypatch.setattr(
        summarizer,
        "_detect_readonly_sum_accumulator_proof",
        lambda *_args, **_kwargs: expected_proof,
    )
    monkeypatch.setattr(
        summarizer,
        "_readonly_reduction_region_returns_with_signedness",
        lambda analysis, count_param, conditions, expected_signed: [
            ret for ret in (analysis.returns or []) if getattr(ret, "address", None) == "0x1000"
        ],
    )

    assert (
        summarizer._try_summarize_readonly_pointer_reduction(
            _FakeFunction(),
            object(),
            analysis,
        )
        is None
    )


def test_structural_recurrence_omitted_positive_return_requires_exact_readonly_witness(monkeypatch):
    summarizer = StructuralRecurrenceSummarizer(tracer=None, debug=False)
    pointer_param = {"name": "param_1", "index": 0, "data_type": "int *", "size": 8, "is_signed": False}
    count_param = {"name": "param_2", "index": 1, "data_type": "uint", "size": 4, "is_signed": False}
    analysis = FunctionReturnAnalysis(
        function_name="readonly_partial_positive_region_like",
        entry_point="0x1000",
        parameters=[pointer_param, count_param],
        returns=[
            ReturnInfo(
                address="0x1000",
                conditions=[
                    _cond("INT_NOTEQUAL", _param("param_1", size=8), _const(0, size=8)),
                    _cond("INT_LESS", _const(0), _param("param_2")),
                ],
                value=_const(1),
            ),
            ReturnInfo(
                address="0x1001",
                conditions=[
                    _cond("INT_NOTEQUAL", _param("param_1", size=8), _const(0, size=8)),
                    _cond("INT_EQUAL", _param("param_2"), _const(1)),
                ],
                value=_const(999),
            ),
        ],
    )
    proof = _readonly_accumulator_proof(
        base_ref=LocationBaseRef.parameter("param_1", index=0),
        count_expr=_param("param_2"),
        stride=4,
        element_size=4,
    )

    omitted = analysis.returns[1]

    assert (
        summarizer._readonly_positive_return_matches_accumulator_proof(
            analysis,
            pointer_param,
            count_param,
            omitted,
            proof,
        )
        is False
    )


def test_structural_recurrence_does_not_replace_overlap_only_positive_return():
    summarizer = StructuralRecurrenceSummarizer(tracer=None, debug=False)
    pointer_param = {"name": "param_1", "index": 0, "data_type": "int *", "size": 8, "is_signed": False}
    count_param = {"name": "param_2", "index": 1, "data_type": "int", "size": 4, "is_signed": True}
    analysis = FunctionReturnAnalysis(
        function_name="readonly_overlap_only_positive_region_like",
        entry_point="0x1000",
        parameters=[pointer_param, count_param],
        returns=[
            ReturnInfo(
                address="0x1000",
                conditions=[
                    _cond("INT_NOTEQUAL", _param("param_1", size=8), _const(0, size=8)),
                    _cond("INT_SLESS", _const(-10), _param("param_2")),
                ],
                value=_const(1),
            ),
        ],
    )
    proof = _readonly_accumulator_proof(
        base_ref=LocationBaseRef.parameter("param_1", index=0),
        count_expr=_param("param_2"),
        stride=4,
        element_size=4,
    )
    positive_conditions = summarizer._readonly_reduction_positive_conditions(
        analysis,
        pointer_param,
        count_param,
        signed_counter=True,
    )

    replaceable = summarizer._readonly_reduction_replaceable_positive_returns(
        analysis,
        pointer_param,
        count_param,
        positive_conditions,
        positive_conditions,
        expected_signed=True,
        accumulator_proof=proof,
    )

    assert replaceable == []


def test_structural_recurrence_declines_broad_positive_return_with_only_single_count_anchor():
    summarizer = StructuralRecurrenceSummarizer(tracer=None, debug=False)
    pointer_param = {"name": "param_1", "index": 0, "data_type": "int *", "size": 8, "is_signed": False}
    count_param = {"name": "param_2", "index": 1, "data_type": "int", "size": 4, "is_signed": True}
    broad_return = ReturnInfo(
        address="0x1008",
        pcode_time=17,
        conditions=[
            _cond("INT_NOTEQUAL", Expression.parameter("param_1", index=0, data_type="int *", size=8), _const(0, size=8)),
            _cond("INT_SLESS", _const(3), Expression.parameter("param_2", index=1, data_type="int", size=4)),
        ],
        value=Expression.binary_op(
            "INT_ADD",
            _mem("param_1", 12),
            Expression.binary_op(
                "INT_ADD",
                _mem("param_1", 0),
                Expression.binary_op(
                    "INT_ADD",
                    _mem("param_1", 4),
                    _mem("param_1", 8),
                ),
            ),
        ),
    )
    analysis = FunctionReturnAnalysis(
        function_name="readonly_loop_anchor_positive_region_like",
        entry_point="0x1000",
        parameters=[pointer_param, count_param],
        returns=[broad_return],
    )
    proof = _readonly_accumulator_proof(
        base_ref=LocationBaseRef.parameter("param_1", index=0),
        count_expr=Expression.parameter("param_2", index=1, data_type="int", size=4),
        stride=4,
        element_size=4,
        start_offset=12,
        start_index=3,
        seed_terms=(
            ReadonlyReductionTermRef(byte_offset=0, access_size=4),
            ReadonlyReductionTermRef(byte_offset=4, access_size=4),
            ReadonlyReductionTermRef(byte_offset=8, access_size=4),
        ),
        return_region_value_proven=False,
    )
    broad_positive_conditions = [
        _cond("INT_NOTEQUAL", Expression.parameter("param_1", index=0, data_type="int *", size=8), _const(0, size=8)),
        _cond("INT_SLESS", _const(0), Expression.parameter("param_2", index=1, data_type="int", size=4)),
    ]
    positive_conditions = broad_positive_conditions[:-1] + [
        _cond("INT_SLESS", _const(3), Expression.parameter("param_2", index=1, data_type="int", size=4)),
    ]

    replaceable = summarizer._readonly_reduction_replaceable_positive_returns(
        analysis,
        pointer_param,
        count_param,
        broad_positive_conditions,
        positive_conditions,
        expected_signed=True,
        accumulator_proof=proof,
    )

    assert replaceable == []


def test_structural_recurrence_replaces_broad_anchor_when_return_region_value_is_proven():
    summarizer = StructuralRecurrenceSummarizer(tracer=None, debug=False)
    pointer_param = {"name": "param_1", "index": 0, "data_type": "int *", "size": 8, "is_signed": False}
    count_param = {"name": "param_2", "index": 1, "data_type": "int", "size": 4, "is_signed": True}
    broad_return = ReturnInfo(
        address="0x1008",
        pcode_time=17,
        conditions=[
            _cond("INT_NOTEQUAL", Expression.parameter("param_1", index=0, data_type="int *", size=8), _const(0, size=8)),
            _cond("INT_SLESS", _const(3), Expression.parameter("param_2", index=1, data_type="int", size=4)),
        ],
        value=Expression.binary_op(
            "INT_ADD",
            _mem("param_1", 12),
            Expression.binary_op(
                "INT_ADD",
                _mem("param_1", 0),
                Expression.binary_op(
                    "INT_ADD",
                    _mem("param_1", 4),
                    _mem("param_1", 8),
                ),
            ),
        ),
    )
    analysis = FunctionReturnAnalysis(
        function_name="readonly_loop_anchor_region_proven_like",
        entry_point="0x1000",
        parameters=[pointer_param, count_param],
        returns=[broad_return],
    )
    proof = _readonly_accumulator_proof(
        base_ref=LocationBaseRef.parameter("param_1", index=0),
        count_expr=Expression.parameter("param_2", index=1, data_type="int", size=4),
        stride=4,
        element_size=4,
        start_offset=12,
        start_index=3,
        seed_terms=(
            ReadonlyReductionTermRef(byte_offset=0, access_size=4),
            ReadonlyReductionTermRef(byte_offset=4, access_size=4),
            ReadonlyReductionTermRef(byte_offset=8, access_size=4),
        ),
        return_op_refs=(PcodeOpRef(address_offset=0x1008, seq_time=17, mnemonic="RETURN"),),
        return_region_value_proven=True,
    )
    broad_positive_conditions = [
        _cond("INT_NOTEQUAL", Expression.parameter("param_1", index=0, data_type="int *", size=8), _const(0, size=8)),
        _cond("INT_SLESS", _const(0), Expression.parameter("param_2", index=1, data_type="int", size=4)),
    ]
    positive_conditions = broad_positive_conditions[:-1] + [
        _cond("INT_SLESS", _const(3), Expression.parameter("param_2", index=1, data_type="int", size=4)),
    ]

    replaceable = summarizer._readonly_reduction_replaceable_positive_returns(
        analysis,
        pointer_param,
        count_param,
        broad_positive_conditions,
        positive_conditions,
        expected_signed=True,
        accumulator_proof=proof,
    )

    assert broad_return in replaceable


def test_structural_recurrence_synthesizes_positive_anchor_from_object_proof():
    summarizer = StructuralRecurrenceSummarizer(tracer=None, debug=False)
    pointer_expr = Expression.parameter("param_1", index=0, data_type="int *", size=8)
    count_expr = Expression.parameter("param_2", index=1, data_type="int", size=4)
    positive_conditions = [
        _cond("INT_NOTEQUAL", pointer_expr, _const(0, size=8)),
        _cond("INT_SLESS", _const(0), count_expr),
    ]
    proof = _readonly_accumulator_proof(
        base_ref=LocationBaseRef.parameter("param_1", index=0),
        count_expr=count_expr,
        stride=4,
        element_size=4,
        return_value_op_refs=(
            PcodeOpRef(address_offset=0x1008, seq_time=47, seq_order=2, mnemonic="RETURN"),
        ),
        return_region_value_proven=True,
    )

    synthetic = summarizer._readonly_synthetic_positive_return_from_proof(
        proof,
        positive_conditions,
        result_size=4,
    )

    assert synthetic is not None
    assert synthetic.address == "00001008"
    assert synthetic.pcode_identity == "00001008:t47"
    assert synthetic.pcode_op_ref == proof.return_value_op_refs[0]
    assert synthetic.conditions == positive_conditions
    assert synthetic.value.expr_type == ExpressionType.CONSTANT


def test_structural_recurrence_refuses_synthetic_anchor_without_return_proof():
    summarizer = StructuralRecurrenceSummarizer(tracer=None, debug=False)
    count_expr = Expression.parameter("param_2", index=1, data_type="int", size=4)
    proof = _readonly_accumulator_proof(
        base_ref=LocationBaseRef.parameter("param_1", index=0),
        count_expr=count_expr,
        stride=4,
        element_size=4,
        return_region_value_proven=False,
    )

    synthetic = summarizer._readonly_synthetic_positive_return_from_proof(
        proof,
        [],
        result_size=4,
    )

    assert synthetic is None


def test_structural_recurrence_broadens_counter_only_region_when_return_value_proof_exists():
    summarizer = StructuralRecurrenceSummarizer(tracer=None, debug=False)
    pointer_param = {"name": "param_1", "index": 0, "data_type": "int *", "size": 8, "is_signed": False}
    count_param = {"name": "param_2", "index": 1, "data_type": "int", "size": 4, "is_signed": True}
    count_expr = Expression.parameter("param_2", index=1, data_type="int", size=4)
    broad_return = ReturnInfo(
        address="0x1018",
        pcode_time=41,
        conditions=[
            _cond("INT_NOTEQUAL", Expression.parameter("param_1", index=0, data_type="int *", size=8), _const(0, size=8)),
            _cond("INT_SLESS", _const(10), count_expr),
        ],
        value=Expression.binary_op(
            "INT_ADD",
            _mem("param_1", 12),
            Expression.binary_op(
                "INT_ADD",
                _mem("param_1", 0),
                Expression.binary_op(
                    "INT_ADD",
                    _mem("param_1", 4),
                    _mem("param_1", 8),
                ),
            ),
        ),
    )
    exact_one = ReturnInfo(
        address="0x1011",
        conditions=[
            _cond("INT_NOTEQUAL", Expression.parameter("param_1", index=0, data_type="int *", size=8), _const(0, size=8)),
            _cond("INT_EQUAL", count_expr, _const(1)),
        ],
        value=_mem("param_1", 0),
    )
    exact_two = ReturnInfo(
        address="0x1012",
        conditions=[
            _cond("INT_NOTEQUAL", Expression.parameter("param_1", index=0, data_type="int *", size=8), _const(0, size=8)),
            _cond("INT_EQUAL", count_expr, _const(2)),
        ],
        value=Expression.binary_op("INT_ADD", _mem("param_1", 0), _mem("param_1", 4)),
    )
    exact_three = ReturnInfo(
        address="0x1013",
        conditions=[
            _cond("INT_NOTEQUAL", Expression.parameter("param_1", index=0, data_type="int *", size=8), _const(0, size=8)),
            _cond("INT_EQUAL", count_expr, _const(3)),
        ],
        value=Expression.binary_op(
            "INT_ADD",
            _mem("param_1", 8),
            Expression.binary_op("INT_ADD", _mem("param_1", 0), _mem("param_1", 4)),
        ),
    )
    exact_four = ReturnInfo(
        address="0x1014",
        conditions=[
            _cond("INT_NOTEQUAL", Expression.parameter("param_1", index=0, data_type="int *", size=8), _const(0, size=8)),
            _cond("INT_EQUAL", count_expr, _const(4)),
        ],
        value=Expression.binary_op(
            "INT_ADD",
            _mem("param_1", 12),
            Expression.binary_op(
                "INT_ADD",
                _mem("param_1", 0),
                Expression.binary_op(
                    "INT_ADD",
                    _mem("param_1", 4),
                    _mem("param_1", 8),
                ),
            ),
        ),
    )
    analysis = FunctionReturnAnalysis(
        function_name="readonly_counter_only_region_proven_like",
        entry_point="0x1000",
        parameters=[pointer_param, count_param],
        returns=[broad_return, exact_one, exact_two, exact_three, exact_four],
    )
    proof = _readonly_accumulator_proof(
        base_ref=LocationBaseRef.parameter("param_1", index=0),
        count_expr=count_expr,
        stride=4,
        element_size=4,
        start_offset=12,
        start_index=3,
        seed_terms=(
            ReadonlyReductionTermRef(byte_offset=0, access_size=4),
            ReadonlyReductionTermRef(byte_offset=4, access_size=4),
            ReadonlyReductionTermRef(byte_offset=8, access_size=4),
        ),
        return_op_refs=(PcodeOpRef(address_offset=0x1018, seq_time=41, mnemonic="RETURN"),),
        return_region_value_proven=True,
    )
    broad_positive_conditions = [
        _cond("INT_NOTEQUAL", Expression.parameter("param_1", index=0, data_type="int *", size=8), _const(0, size=8)),
        _cond("INT_SLESS", _const(0), count_expr),
    ]
    positive_conditions = [
        _cond("INT_NOTEQUAL", Expression.parameter("param_1", index=0, data_type="int *", size=8), _const(0, size=8)),
        _cond("INT_SLESS", _const(3), count_expr),
    ]

    replaceable = summarizer._readonly_reduction_replaceable_positive_returns(
        analysis,
        pointer_param,
        count_param,
        broad_positive_conditions,
        positive_conditions,
        expected_signed=True,
        accumulator_proof=proof,
    )

    assert broad_return in replaceable


def test_structural_recurrence_accepts_proven_return_value_site_before_final_return():
    summarizer = StructuralRecurrenceSummarizer(tracer=None, debug=False)
    pointer_param = {"name": "param_1", "index": 0, "data_type": "int *", "size": 8, "is_signed": False}
    count_param = {"name": "param_2", "index": 1, "data_type": "int", "size": 4, "is_signed": True}
    broad_return = ReturnInfo(
        address="0x1008",
        pcode_time=23,
        conditions=[
            _cond("INT_NOTEQUAL", Expression.parameter("param_1", index=0, data_type="int *", size=8), _const(0, size=8)),
            _cond("INT_SLESS", _const(3), Expression.parameter("param_2", index=1, data_type="int", size=4)),
        ],
        value=Expression.binary_op(
            "INT_ADD",
            _mem("param_1", 12),
            Expression.binary_op(
                "INT_ADD",
                _mem("param_1", 0),
                Expression.binary_op(
                    "INT_ADD",
                    _mem("param_1", 4),
                    _mem("param_1", 8),
                ),
            ),
        ),
    )
    analysis = FunctionReturnAnalysis(
        function_name="readonly_loop_anchor_region_value_site_like",
        entry_point="0x1000",
        parameters=[pointer_param, count_param],
        returns=[broad_return],
    )
    proof = _readonly_accumulator_proof(
        base_ref=LocationBaseRef.parameter("param_1", index=0),
        count_expr=Expression.parameter("param_2", index=1, data_type="int", size=4),
        stride=4,
        element_size=4,
        start_offset=12,
        start_index=3,
        seed_terms=(
            ReadonlyReductionTermRef(byte_offset=0, access_size=4),
            ReadonlyReductionTermRef(byte_offset=4, access_size=4),
            ReadonlyReductionTermRef(byte_offset=8, access_size=4),
        ),
        return_op_refs=(PcodeOpRef(address_offset=0x1010, seq_time=29, mnemonic="RETURN"),),
        return_value_op_refs=(PcodeOpRef(address_offset=0x1008, seq_time=23, mnemonic="MULTIEQUAL"),),
        return_region_value_proven=True,
    )
    broad_positive_conditions = [
        _cond("INT_NOTEQUAL", Expression.parameter("param_1", index=0, data_type="int *", size=8), _const(0, size=8)),
        _cond("INT_SLESS", _const(0), Expression.parameter("param_2", index=1, data_type="int", size=4)),
    ]
    positive_conditions = broad_positive_conditions[:-1] + [
        _cond("INT_SLESS", _const(3), Expression.parameter("param_2", index=1, data_type="int", size=4)),
    ]

    replaceable = summarizer._readonly_reduction_replaceable_positive_returns(
        analysis,
        pointer_param,
        count_param,
        broad_positive_conditions,
        positive_conditions,
        expected_signed=True,
        accumulator_proof=proof,
    )

    assert broad_return in replaceable


def test_structural_recurrence_accepts_adjacent_copy_value_site():
    summarizer = StructuralRecurrenceSummarizer(tracer=None, debug=False)
    ret = ReturnInfo(
        address="0x1008",
        pcode_time=24,
        pcode_order=1,
        conditions=[],
        value=_const(0),
    )
    ref = PcodeOpRef(address_offset=0x1008, seq_time=23, seq_order=0, mnemonic="COPY")

    assert summarizer._return_info_matches_pcode_op_ref(ret, ref) is True


def test_structural_recurrence_matches_address_space_qualified_pcode_identity():
    summarizer = StructuralRecurrenceSummarizer(tracer=None, debug=False)
    ret = ReturnInfo(
        address="ram:00001000",
        pcode_identity="ram:00001000:t23:o1",
        conditions=[],
        value=_const(0),
    )
    ref = PcodeOpRef(address_offset=0x1000, seq_time=23, seq_order=1, mnemonic="RETURN")

    assert summarizer._return_info_matches_pcode_op_ref(ret, ref) is True


def test_structural_recurrence_builds_ref_from_address_space_qualified_identity():
    summarizer = StructuralRecurrenceSummarizer(tracer=None, debug=False)
    ret = ReturnInfo(
        address="unknown",
        pcode_identity="ram:00001000:t23:o1",
        conditions=[],
        value=_const(0),
    )

    ref = summarizer._pcode_op_ref_from_return_info(ret)

    assert ref == PcodeOpRef(address_offset=0x1000, seq_time=23, seq_order=1, mnemonic=None)


def test_structural_recurrence_matches_adjacent_copy_with_qualified_identity():
    summarizer = StructuralRecurrenceSummarizer(tracer=None, debug=False)
    ret = ReturnInfo(
        address="ram:00001000",
        pcode_identity="ram:00001000:t24:o1",
        conditions=[],
        value=_const(0),
    )
    ref = PcodeOpRef(address_offset=0x1000, seq_time=23, seq_order=0, mnemonic="COPY")

    assert summarizer._return_info_matches_pcode_op_ref(ret, ref) is True


def test_structural_recurrence_accepts_reachable_value_ref_for_return_region_proof():
    summarizer = StructuralRecurrenceSummarizer(tracer=None, debug=False)
    seed = _FakeVarnode("seed", size=4)
    add_out = _FakeVarnode("add_out", size=4)
    copy_out = _FakeVarnode("copy_out", size=4)
    add_op = _FakePcodeOp("INT_ADD", [seed, _FakeVarnode("one", size=4)], add_out)
    copy_op = _FakePcodeOp("COPY", [add_out], copy_out)
    return_op = _FakePcodeOp("RETURN", [copy_out], None)
    refs = {
        add_op: PcodeOpRef(address_offset=0x1008, seq_time=21, seq_order=0, block_index=6, mnemonic="INT_ADD"),
        copy_op: PcodeOpRef(address_offset=0x1008, seq_time=22, seq_order=0, block_index=6, mnemonic="COPY"),
        return_op: PcodeOpRef(address_offset=0x1008, seq_time=24, seq_order=1, block_index=6, mnemonic="RETURN"),
    }
    summarizer._make_pcode_op_ref = lambda op: refs.get(op)
    value_refs, return_refs = summarizer._reachable_return_value_and_return_refs_from_varnodes((seed,))

    ret = ReturnInfo(
        address="0x1008",
        pcode_time=24,
        pcode_order=1,
        pcode_op_ref=refs[return_op],
        conditions=[],
        value=_const(0),
    )
    proof = _readonly_accumulator_proof(
        base_ref=LocationBaseRef.parameter("param_1", index=0),
        count_expr=Expression.parameter("param_2", index=1, data_type="int", size=4),
        stride=4,
        element_size=4,
        return_op_refs=return_refs,
        return_value_op_refs=value_refs,
        return_region_value_proven=True,
    )

    assert refs[return_op] in return_refs
    assert refs[add_op] in value_refs
    assert summarizer._readonly_return_region_value_is_proven(ret, [], proof) is True


def test_structural_recurrence_direct_return_refs_reject_arithmetic_contribution():
    summarizer = StructuralRecurrenceSummarizer(tracer=None, debug=False)
    seed = _FakeVarnode("seed", size=4)
    other = _FakeVarnode("other", size=4)
    add_out = _FakeVarnode("add_out", size=4)
    copy_out = _FakeVarnode("copy_out", size=4)
    add_op = _FakePcodeOp("INT_ADD", [seed, other], add_out)
    copy_op = _FakePcodeOp("COPY", [add_out], copy_out)
    return_op = _FakePcodeOp("RETURN", [copy_out], None)
    refs = {
        add_op: PcodeOpRef(address_offset=0x1008, seq_time=21, seq_order=0, block_index=6, mnemonic="INT_ADD"),
        copy_op: PcodeOpRef(address_offset=0x1008, seq_time=22, seq_order=0, block_index=6, mnemonic="COPY"),
        return_op: PcodeOpRef(address_offset=0x1008, seq_time=24, seq_order=1, block_index=6, mnemonic="RETURN"),
    }
    summarizer._make_pcode_op_ref = lambda op: refs.get(op)

    reachable_value_refs, reachable_return_refs = summarizer._reachable_return_value_and_return_refs_from_varnodes((seed,))
    direct_value_refs, direct_return_refs = summarizer._direct_return_value_and_return_refs_from_varnodes((seed,))
    direct_full_value_refs, direct_full_return_refs = summarizer._direct_return_value_and_return_refs_from_varnodes((add_out,))

    assert refs[return_op] in reachable_return_refs
    assert refs[add_op] in reachable_value_refs
    assert direct_value_refs == ()
    assert direct_return_refs == ()
    assert direct_full_value_refs == (refs[copy_op],)
    assert direct_full_return_refs == (refs[return_op],)


def test_structural_recurrence_rejects_value_ref_without_reachable_return_ref():
    summarizer = StructuralRecurrenceSummarizer(tracer=None, debug=False)
    ret = ReturnInfo(
        address="0x1008",
        pcode_op_ref=PcodeOpRef(
            address_offset=0x1008,
            seq_time=24,
            seq_order=1,
            block_index=6,
            mnemonic="RETURN",
        ),
        conditions=[],
        value=_const(0),
    )
    proof = _readonly_accumulator_proof(
        base_ref=LocationBaseRef.parameter("param_1", index=0),
        count_expr=Expression.parameter("param_2", index=1, data_type="int", size=4),
        stride=4,
        element_size=4,
        return_value_op_refs=(
            PcodeOpRef(
                address_offset=0x1008,
                seq_time=21,
                seq_order=0,
                block_index=6,
                mnemonic="INT_ADD",
            ),
        ),
        return_region_value_proven=True,
    )

    assert summarizer._readonly_return_region_value_is_proven(ret, [], proof) is False


def test_structural_recurrence_rejects_address_only_region_value_site():
    summarizer = StructuralRecurrenceSummarizer(tracer=None, debug=False)
    ret = ReturnInfo(
        address="0x1008",
        conditions=[],
        value=_const(0),
    )
    ref = PcodeOpRef(address_offset=0x1008, mnemonic="RETURN")

    assert summarizer._return_info_matches_pcode_op_ref(ret, ref) is False


def test_structural_recurrence_rejects_region_value_boolean_without_site_refs():
    summarizer = StructuralRecurrenceSummarizer(tracer=None, debug=False)
    ret = ReturnInfo(
        address="0x1008",
        pcode_time=17,
        conditions=[],
        value=_const(0),
    )
    proof = _readonly_accumulator_proof(
        base_ref=LocationBaseRef.parameter("param_1", index=0),
        count_expr=Expression.parameter("param_2", index=1, data_type="int", size=4),
        stride=4,
        element_size=4,
        return_region_value_proven=True,
    )

    assert summarizer._readonly_return_region_value_is_proven(ret, [], proof) is False


def test_structural_recurrence_declines_region_value_proof_for_unmatched_return_site():
    summarizer = StructuralRecurrenceSummarizer(tracer=None, debug=False)
    pointer_param = {"name": "param_1", "index": 0, "data_type": "int *", "size": 8, "is_signed": False}
    count_param = {"name": "param_2", "index": 1, "data_type": "int", "size": 4, "is_signed": True}
    broad_return = ReturnInfo(
        address="0x1008",
        pcode_time=19,
        conditions=[
            _cond("INT_NOTEQUAL", Expression.parameter("param_1", index=0, data_type="int *", size=8), _const(0, size=8)),
            _cond("INT_SLESS", _const(3), Expression.parameter("param_2", index=1, data_type="int", size=4)),
        ],
        value=Expression.binary_op(
            "INT_ADD",
            _mem("param_1", 12),
            Expression.binary_op(
                "INT_ADD",
                _mem("param_1", 0),
                Expression.binary_op(
                    "INT_ADD",
                    _mem("param_1", 4),
                    _mem("param_1", 8),
                ),
            ),
        ),
    )
    analysis = FunctionReturnAnalysis(
        function_name="readonly_loop_anchor_region_wrong_return_site_like",
        entry_point="0x1000",
        parameters=[pointer_param, count_param],
        returns=[broad_return],
    )
    proof = _readonly_accumulator_proof(
        base_ref=LocationBaseRef.parameter("param_1", index=0),
        count_expr=Expression.parameter("param_2", index=1, data_type="int", size=4),
        stride=4,
        element_size=4,
        start_offset=12,
        start_index=3,
        seed_terms=(
            ReadonlyReductionTermRef(byte_offset=0, access_size=4),
            ReadonlyReductionTermRef(byte_offset=4, access_size=4),
            ReadonlyReductionTermRef(byte_offset=8, access_size=4),
        ),
        return_op_refs=(PcodeOpRef(address_offset=0x1010, seq_time=17, mnemonic="RETURN"),),
        return_region_value_proven=True,
    )
    broad_positive_conditions = [
        _cond("INT_NOTEQUAL", Expression.parameter("param_1", index=0, data_type="int *", size=8), _const(0, size=8)),
        _cond("INT_SLESS", _const(0), Expression.parameter("param_2", index=1, data_type="int", size=4)),
    ]
    positive_conditions = broad_positive_conditions[:-1] + [
        _cond("INT_SLESS", _const(3), Expression.parameter("param_2", index=1, data_type="int", size=4)),
    ]

    replaceable = summarizer._readonly_reduction_replaceable_positive_returns(
        analysis,
        pointer_param,
        count_param,
        broad_positive_conditions,
        positive_conditions,
        expected_signed=True,
        accumulator_proof=proof,
    )

    assert replaceable == []


def test_structural_recurrence_declines_loop_anchor_residual_when_only_single_count_is_covered():
    summarizer = StructuralRecurrenceSummarizer(tracer=None, debug=False)
    pointer_param = {"name": "param_1", "index": 0, "data_type": "int *", "size": 8, "is_signed": False}
    count_param = {"name": "param_2", "index": 1, "data_type": "long", "size": 8, "is_signed": False}
    count_expr = Expression.parameter("param_2", index=1, data_type="long", size=8)
    extra_counter_guard = _cond(
        "INT_NOTEQUAL",
        count_expr,
        _const(4, size=8),
    )
    broad_return = ReturnInfo(
        address="0x1010",
        conditions=[
            _cond("INT_NOTEQUAL", Expression.parameter("param_1", index=0, data_type="int *", size=8), _const(0, size=8)),
            _cond("INT_SLESS", _const(0, size=8), count_expr),
            _cond("INT_SLESS", _const(3, size=8), count_expr),
            extra_counter_guard,
        ],
        value=Expression.binary_op(
            "INT_ADD",
            _mem("param_1", 12),
            Expression.binary_op(
                "INT_ADD",
                _mem("param_1", 0),
                Expression.binary_op(
                    "INT_ADD",
                    _mem("param_1", 4),
                    _mem("param_1", 8),
                ),
            ),
        ),
    )
    exact_count_four_return = ReturnInfo(
        address="0x1014",
        conditions=[
            _cond("INT_NOTEQUAL", Expression.parameter("param_1", index=0, data_type="int *", size=8), _const(0, size=8)),
            _cond("INT_EQUAL", count_expr, _const(4, size=8)),
        ],
        value=broad_return.value,
    )
    analysis = FunctionReturnAnalysis(
        function_name="readonly_loop_anchor_mask_guard_like",
        entry_point="0x1000",
        parameters=[pointer_param, count_param],
        returns=[broad_return, exact_count_four_return],
    )
    proof = _readonly_accumulator_proof(
        base_ref=LocationBaseRef.parameter("param_1", index=0),
        count_expr=count_expr,
        stride=4,
        element_size=4,
        start_offset=12,
        start_index=3,
        seed_terms=(
            ReadonlyReductionTermRef(byte_offset=0, access_size=4),
            ReadonlyReductionTermRef(byte_offset=4, access_size=4),
            ReadonlyReductionTermRef(byte_offset=8, access_size=4),
        ),
        return_region_value_proven=False,
    )
    broad_positive_conditions = [
        _cond("INT_NOTEQUAL", Expression.parameter("param_1", index=0, data_type="int *", size=8), _const(0, size=8)),
        _cond("INT_SLESS", _const(0, size=8), count_expr),
    ]
    positive_conditions = broad_positive_conditions[:-1] + [
        _cond("INT_SLESS", _const(3, size=8), count_expr),
    ]

    replaceable = summarizer._readonly_reduction_replaceable_positive_returns(
        analysis,
        pointer_param,
        count_param,
        broad_positive_conditions,
        positive_conditions,
        expected_signed=True,
        accumulator_proof=proof,
    )

    assert replaceable == []


def test_structural_recurrence_declines_counter_only_residual_without_exact_coverage():
    summarizer = StructuralRecurrenceSummarizer(tracer=None, debug=False)
    pointer_param = {"name": "param_1", "index": 0, "data_type": "int *", "size": 8, "is_signed": False}
    count_param = {"name": "param_2", "index": 1, "data_type": "int", "size": 4, "is_signed": True}
    count_expr = Expression.parameter("param_2", index=1, data_type="int", size=4)
    broad_return = ReturnInfo(
        address="0x1014",
        conditions=[
            _cond("INT_NOTEQUAL", Expression.parameter("param_1", index=0, data_type="int *", size=8), _const(0, size=8)),
            _cond("INT_SLESS", _const(3), count_expr),
            _cond("INT_NOTEQUAL", count_expr, _const(4)),
        ],
        value=Expression.binary_op(
            "INT_ADD",
            _mem("param_1", 12),
            Expression.binary_op(
                "INT_ADD",
                _mem("param_1", 0),
                Expression.binary_op("INT_ADD", _mem("param_1", 4), _mem("param_1", 8)),
            ),
        ),
    )
    analysis = FunctionReturnAnalysis(
        function_name="readonly_loop_anchor_uncovered_residual_like",
        entry_point="0x1000",
        parameters=[pointer_param, count_param],
        returns=[broad_return],
    )
    proof = _readonly_accumulator_proof(
        base_ref=LocationBaseRef.parameter("param_1", index=0),
        count_expr=count_expr,
        stride=4,
        element_size=4,
        start_offset=12,
        start_index=3,
        seed_terms=(
            ReadonlyReductionTermRef(byte_offset=0, access_size=4),
            ReadonlyReductionTermRef(byte_offset=4, access_size=4),
            ReadonlyReductionTermRef(byte_offset=8, access_size=4),
        ),
    )
    positive_conditions = [
        _cond("INT_NOTEQUAL", Expression.parameter("param_1", index=0, data_type="int *", size=8), _const(0, size=8)),
        _cond("INT_SLESS", _const(3), count_expr),
    ]

    replaceable = summarizer._readonly_reduction_replaceable_positive_returns(
        analysis,
        pointer_param,
        count_param,
        positive_conditions,
        positive_conditions,
        expected_signed=True,
        accumulator_proof=proof,
    )

    assert replaceable == []


def test_structural_recurrence_declines_multi_return_shared_counter_residual_hole():
    summarizer = StructuralRecurrenceSummarizer(tracer=None, debug=False)
    pointer_param = {"name": "param_1", "index": 0, "data_type": "int *", "size": 8, "is_signed": False}
    count_param = {"name": "param_2", "index": 1, "data_type": "int", "size": 4, "is_signed": True}
    count_expr = Expression.parameter("param_2", index=1, data_type="int", size=4)
    value = Expression.binary_op(
        "INT_ADD",
        _mem("param_1", 12),
        Expression.binary_op(
            "INT_ADD",
            _mem("param_1", 0),
            Expression.binary_op("INT_ADD", _mem("param_1", 4), _mem("param_1", 8)),
        ),
    )
    shared_conditions = [
        _cond("INT_NOTEQUAL", Expression.parameter("param_1", index=0, data_type="int *", size=8), _const(0, size=8)),
        _cond("INT_SLESS", _const(3), count_expr),
        _cond("INT_NOTEQUAL", count_expr, _const(4)),
    ]
    returns = [
        ReturnInfo(address="0x1020", conditions=list(shared_conditions), value=value),
        ReturnInfo(address="0x1024", conditions=list(shared_conditions), value=value),
    ]
    analysis = FunctionReturnAnalysis(
        function_name="readonly_multi_return_shared_residual_hole_like",
        entry_point="0x1000",
        parameters=[pointer_param, count_param],
        returns=returns,
    )
    proof = _readonly_accumulator_proof(
        base_ref=LocationBaseRef.parameter("param_1", index=0),
        count_expr=count_expr,
        stride=4,
        element_size=4,
        start_offset=12,
        start_index=3,
        seed_terms=(
            ReadonlyReductionTermRef(byte_offset=0, access_size=4),
            ReadonlyReductionTermRef(byte_offset=4, access_size=4),
            ReadonlyReductionTermRef(byte_offset=8, access_size=4),
        ),
    )
    positive_conditions = [
        _cond("INT_NOTEQUAL", Expression.parameter("param_1", index=0, data_type="int *", size=8), _const(0, size=8)),
        _cond("INT_SLESS", _const(3), count_expr),
    ]

    replaceable = summarizer._readonly_reduction_replaceable_positive_returns(
        analysis,
        pointer_param,
        count_param,
        positive_conditions,
        positive_conditions,
        expected_signed=True,
        accumulator_proof=proof,
    )

    assert replaceable == []


def test_structural_recurrence_residual_coverage_proves_all_excluded_regions():
    summarizer = StructuralRecurrenceSummarizer(tracer=None, debug=False)
    pointer_param = {"name": "param_1", "index": 0, "data_type": "int *", "size": 8, "is_signed": False}
    count_param = {"name": "param_2", "index": 1, "data_type": "int", "size": 4, "is_signed": True}
    count_expr = Expression.parameter("param_2", index=1, data_type="int", size=4)
    value = Expression.binary_op(
        "INT_ADD",
        _mem("param_1", 12),
        Expression.binary_op(
            "INT_ADD",
            _mem("param_1", 0),
            Expression.binary_op("INT_ADD", _mem("param_1", 4), _mem("param_1", 8)),
        ),
    )
    broad_return = ReturnInfo(
        address="0x1030",
        conditions=[
            _cond("INT_NOTEQUAL", Expression.parameter("param_1", index=0, data_type="int *", size=8), _const(0, size=8)),
            _cond("INT_SLESS", _const(3), count_expr),
            _cond("INT_NOTEQUAL", count_expr, _const(4)),
            _cond("INT_NOTEQUAL", count_expr, _const(1000)),
        ],
        value=value,
    )
    exact_count_four_return = ReturnInfo(
        address="0x1034",
        conditions=[
            _cond("INT_NOTEQUAL", Expression.parameter("param_1", index=0, data_type="int *", size=8), _const(0, size=8)),
            _cond("INT_EQUAL", count_expr, _const(4)),
        ],
        value=value,
    )
    analysis = FunctionReturnAnalysis(
        function_name="readonly_residual_sampling_miss_like",
        entry_point="0x1000",
        parameters=[pointer_param, count_param],
        returns=[broad_return, exact_count_four_return],
    )
    proof = _readonly_accumulator_proof(
        base_ref=LocationBaseRef.parameter("param_1", index=0),
        count_expr=count_expr,
        stride=4,
        element_size=4,
        start_offset=12,
        start_index=3,
        seed_terms=(
            ReadonlyReductionTermRef(byte_offset=0, access_size=4),
            ReadonlyReductionTermRef(byte_offset=4, access_size=4),
            ReadonlyReductionTermRef(byte_offset=8, access_size=4),
        ),
    )
    positive_conditions = [
        _cond("INT_NOTEQUAL", Expression.parameter("param_1", index=0, data_type="int *", size=8), _const(0, size=8)),
        _cond("INT_SLESS", _const(3), count_expr),
    ]

    replaceable = summarizer._readonly_reduction_replaceable_positive_returns(
        analysis,
        pointer_param,
        count_param,
        positive_conditions,
        positive_conditions,
        expected_signed=True,
        accumulator_proof=proof,
    )

    assert replaceable == []


def test_structural_recurrence_declines_loop_anchor_when_prefix_region_is_uncovered():
    summarizer = StructuralRecurrenceSummarizer(tracer=None, debug=False)
    pointer_param = {"name": "param_1", "index": 0, "data_type": "int *", "size": 8, "is_signed": False}
    count_param = {"name": "param_2", "index": 1, "data_type": "int", "size": 4, "is_signed": True}
    count_expr = Expression.parameter("param_2", index=1, data_type="int", size=4)
    broad_return = ReturnInfo(
        address="0x1018",
        conditions=[
            _cond("INT_NOTEQUAL", Expression.parameter("param_1", index=0, data_type="int *", size=8), _const(0, size=8)),
            _cond("INT_SLESS", _const(0), count_expr),
            _cond("INT_NOTEQUAL", count_expr, _const(3)),
        ],
        value=Expression.binary_op(
            "INT_ADD",
            _mem("param_1", 12),
            Expression.binary_op(
                "INT_ADD",
                _mem("param_1", 0),
                Expression.binary_op(
                    "INT_ADD",
                    _mem("param_1", 4),
                    _mem("param_1", 8),
                ),
            ),
        ),
    )
    analysis = FunctionReturnAnalysis(
        function_name="readonly_loop_anchor_uncovered_prefix_like",
        entry_point="0x1000",
        parameters=[pointer_param, count_param],
        returns=[broad_return],
    )
    proof = _readonly_accumulator_proof(
        base_ref=LocationBaseRef.parameter("param_1", index=0),
        count_expr=count_expr,
        stride=4,
        element_size=4,
        start_offset=12,
        start_index=3,
        seed_terms=(
            ReadonlyReductionTermRef(byte_offset=0, access_size=4),
            ReadonlyReductionTermRef(byte_offset=4, access_size=4),
            ReadonlyReductionTermRef(byte_offset=8, access_size=4),
        ),
    )
    broad_positive_conditions = [
        _cond("INT_NOTEQUAL", Expression.parameter("param_1", index=0, data_type="int *", size=8), _const(0, size=8)),
        _cond("INT_SLESS", _const(0), count_expr),
    ]
    positive_conditions = broad_positive_conditions[:-1] + [
        _cond("INT_SLESS", _const(3), count_expr),
    ]

    replaceable = summarizer._readonly_reduction_replaceable_positive_returns(
        analysis,
        pointer_param,
        count_param,
        broad_positive_conditions,
        positive_conditions,
        expected_signed=True,
        accumulator_proof=proof,
    )

    assert replaceable == []


def test_readonly_positive_prefix_coverage_accepts_anchor_backed_prefix_returns(monkeypatch):
    summarizer = StructuralRecurrenceSummarizer(tracer=None, debug=False)
    pointer_param = {"name": "param_1", "index": 0, "data_type": "int *", "size": 8, "is_signed": False}
    count_param = {"name": "param_2", "index": 1, "data_type": "int", "size": 4, "is_signed": True}
    count_expr = _param("param_2")
    broad_ret = ReturnInfo(
        address="0x1300",
        conditions=[
            _cond("INT_NOTEQUAL", _param("param_1", size=8), _const(0, size=8)),
            _cond("INT_SLESS", _const(0), count_expr),
        ],
        value=Expression.unknown("phi_circular"),
    )
    exact_one = ReturnInfo(
        address="0x1301",
        conditions=[
            _cond("INT_NOTEQUAL", _param("param_1", size=8), _const(0, size=8)),
            _cond("INT_EQUAL", count_expr, _const(1)),
        ],
        value=_mem("param_1", 0),
    )
    exact_two = ReturnInfo(
        address="0x1302",
        conditions=[
            _cond("INT_NOTEQUAL", _param("param_1", size=8), _const(0, size=8)),
            _cond("INT_EQUAL", count_expr, _const(2)),
        ],
        value=Expression.binary_op("INT_ADD", _mem("param_1", 0), _mem("param_1", 4)),
    )
    exact_three = ReturnInfo(
        address="0x1303",
        conditions=[
            _cond("INT_NOTEQUAL", _param("param_1", size=8), _const(0, size=8)),
            _cond("INT_EQUAL", count_expr, _const(3)),
        ],
        value=Expression.binary_op(
            "INT_ADD",
            _mem("param_1", 8),
            Expression.binary_op("INT_ADD", _mem("param_1", 0), _mem("param_1", 4)),
        ),
    )
    analysis = FunctionReturnAnalysis(
        function_name="readonly_anchor_backed_prefix_coverage_like",
        entry_point="0x1300",
        parameters=[pointer_param, count_param],
        returns=[broad_ret, exact_one, exact_two, exact_three],
    )
    proof = _readonly_accumulator_proof(
        base_ref=LocationBaseRef.parameter("param_1", index=0),
        count_expr=count_expr,
        stride=4,
        element_size=4,
        start_offset=12,
        start_index=3,
        seed_terms=(
            ReadonlyReductionTermRef(byte_offset=0, access_size=4),
            ReadonlyReductionTermRef(byte_offset=4, access_size=4),
            ReadonlyReductionTermRef(byte_offset=8, access_size=4),
        ),
    )

    monkeypatch.setattr(
        summarizer,
        "_readonly_positive_return_matches_accumulator_proof",
        lambda *_args, **_kwargs: False,
    )
    monkeypatch.setattr(
        summarizer,
        "_readonly_positive_return_accumulator_anchor_count",
        lambda _analysis, _pointer_param, _count_param, ret, _proof: {
            "0x1301": 1,
            "0x1302": 2,
            "0x1303": 3,
        }.get(ret.address),
    )

    assert summarizer._readonly_positive_prefix_is_exactly_covered(
        analysis,
        pointer_param,
        count_param,
        broad_ret,
        proof,
    ) is True


def test_readonly_positive_prefix_coverage_accepts_materialized_count_specific_returns(monkeypatch):
    summarizer = StructuralRecurrenceSummarizer(tracer=None, debug=False)
    pointer_param = {"name": "param_1", "index": 0, "data_type": "int *", "size": 8, "is_signed": False}
    count_param = {"name": "param_2", "index": 1, "data_type": "int", "size": 4, "is_signed": True}
    count_expr = _param("param_2")
    broad_ret = ReturnInfo(
        address="0x1310",
        conditions=[
            _cond("INT_NOTEQUAL", _param("param_1", size=8), _const(0, size=8)),
            _cond("INT_SLESS", _const(0), count_expr),
        ],
        value=Expression.unknown("phi_circular"),
    )
    exact_one = ReturnInfo(
        address="0x1311",
        conditions=[
            _cond("INT_NOTEQUAL", _param("param_1", size=8), _const(0, size=8)),
            _cond("INT_EQUAL", count_expr, _const(1)),
        ],
        value=_mem("param_1", 0),
    )
    exact_two = ReturnInfo(
        address="0x1312",
        conditions=[
            _cond("INT_NOTEQUAL", _param("param_1", size=8), _const(0, size=8)),
            _cond("INT_EQUAL", count_expr, _const(2)),
        ],
        value=Expression.binary_op("INT_ADD", _mem("param_1", 0), _mem("param_1", 4)),
    )
    exact_three = ReturnInfo(
        address="0x1313",
        conditions=[
            _cond("INT_NOTEQUAL", _param("param_1", size=8), _const(0, size=8)),
            _cond("INT_EQUAL", count_expr, _const(3)),
        ],
        value=Expression.binary_op(
            "INT_ADD",
            _mem("param_1", 8),
            Expression.binary_op("INT_ADD", _mem("param_1", 0), _mem("param_1", 4)),
        ),
    )
    analysis = FunctionReturnAnalysis(
        function_name="readonly_materialized_prefix_coverage_like",
        entry_point="0x1310",
        parameters=[pointer_param, count_param],
        returns=[broad_ret, exact_one, exact_two, exact_three],
    )
    proof = _readonly_accumulator_proof(
        base_ref=LocationBaseRef.parameter("param_1", index=0),
        count_expr=count_expr,
        stride=4,
        element_size=4,
        start_offset=12,
        start_index=3,
        seed_terms=(
            ReadonlyReductionTermRef(byte_offset=0, access_size=4),
            ReadonlyReductionTermRef(byte_offset=4, access_size=4),
            ReadonlyReductionTermRef(byte_offset=8, access_size=4),
        ),
        return_region_value_proven=False,
    )

    monkeypatch.setattr(
        summarizer,
        "_readonly_positive_return_matches_accumulator_proof",
        lambda *_args, **_kwargs: False,
    )
    monkeypatch.setattr(
        summarizer,
        "_readonly_positive_return_accumulator_anchor_count",
        lambda *_args, **_kwargs: None,
    )

    assert summarizer._readonly_positive_prefix_is_exactly_covered(
        analysis,
        pointer_param,
        count_param,
        broad_ret,
        proof,
    ) is True


def test_structural_recurrence_accepts_materialized_exact_positive_return_without_exact_witness(monkeypatch):
    summarizer = StructuralRecurrenceSummarizer(tracer=None, debug=False)
    pointer_param = {"name": "param_1", "index": 0, "data_type": "int *", "size": 8, "is_signed": False}
    count_param = {"name": "param_2", "index": 1, "data_type": "int", "size": 4, "is_signed": True}
    count_expr = _param("param_2")
    broad_ret = ReturnInfo(
        address="0x1320",
        conditions=[
            _cond("INT_NOTEQUAL", _param("param_1", size=8), _const(0, size=8)),
            _cond("INT_SLESS", _const(0), count_expr),
        ],
        value=Expression.unknown("phi_circular"),
    )
    exact_one = ReturnInfo(
        address="0x1321",
        conditions=[
            _cond("INT_NOTEQUAL", _param("param_1", size=8), _const(0, size=8)),
            _cond("INT_EQUAL", count_expr, _const(1)),
        ],
        value=_mem("param_1", 0),
    )
    exact_two = ReturnInfo(
        address="0x1322",
        conditions=[
            _cond("INT_NOTEQUAL", _param("param_1", size=8), _const(0, size=8)),
            _cond("INT_EQUAL", count_expr, _const(2)),
        ],
        value=Expression.binary_op("INT_ADD", _mem("param_1", 0), _mem("param_1", 4)),
    )
    exact_three = ReturnInfo(
        address="0x1323",
        conditions=[
            _cond("INT_NOTEQUAL", _param("param_1", size=8), _const(0, size=8)),
            _cond("INT_EQUAL", count_expr, _const(3)),
        ],
        value=Expression.binary_op(
            "INT_ADD",
            _mem("param_1", 8),
            Expression.binary_op("INT_ADD", _mem("param_1", 0), _mem("param_1", 4)),
        ),
    )
    exact_four = ReturnInfo(
        address="0x1324",
        conditions=[
            _cond("INT_NOTEQUAL", _param("param_1", size=8), _const(0, size=8)),
            _cond("INT_EQUAL", count_expr, _const(4)),
        ],
        value=Expression.binary_op(
            "INT_ADD",
            _mem("param_1", 12),
            Expression.binary_op(
                "INT_ADD",
                _mem("param_1", 8),
                Expression.binary_op("INT_ADD", _mem("param_1", 0), _mem("param_1", 4)),
            ),
        ),
    )
    analysis = FunctionReturnAnalysis(
        function_name="readonly_materialized_exact_positive_like",
        entry_point="0x1320",
        parameters=[pointer_param, count_param],
        returns=[broad_ret, exact_one, exact_two, exact_three, exact_four],
    )
    proof = _readonly_accumulator_proof(
        base_ref=LocationBaseRef.parameter("param_1", index=0),
        count_expr=count_expr,
        stride=4,
        element_size=4,
        start_offset=12,
        start_index=3,
        seed_terms=(
            ReadonlyReductionTermRef(byte_offset=0, access_size=4),
            ReadonlyReductionTermRef(byte_offset=4, access_size=4),
            ReadonlyReductionTermRef(byte_offset=8, access_size=4),
        ),
        return_region_value_proven=False,
    )
    broad_positive_conditions = summarizer._readonly_reduction_positive_conditions(
        analysis,
        pointer_param,
        count_param,
        loop_start_index=0,
        signed_counter=True,
    )
    positive_conditions = summarizer._readonly_reduction_positive_conditions(
        analysis,
        pointer_param,
        count_param,
        loop_start_index=3,
        signed_counter=True,
    )

    monkeypatch.setattr(
        summarizer,
        "_readonly_positive_return_matches_accumulator_proof",
        lambda *_args, **_kwargs: False,
    )
    monkeypatch.setattr(
        summarizer,
        "_readonly_positive_return_accumulator_anchor_count",
        lambda *_args, **_kwargs: None,
    )

    replaceable = summarizer._readonly_reduction_replaceable_positive_returns(
        analysis,
        pointer_param,
        count_param,
        broad_positive_conditions,
        positive_conditions,
        expected_signed=True,
        accumulator_proof=proof,
    )

    assert replaceable == [broad_ret, exact_four]


def test_structural_recurrence_declines_partial_exact_count_carve_out():
    summarizer = StructuralRecurrenceSummarizer(tracer=None, debug=False)
    pointer_param = {"name": "param_1", "index": 0, "data_type": "int *", "size": 8, "is_signed": False}
    count_param = {"name": "param_2", "index": 1, "data_type": "int", "size": 4, "is_signed": True}
    positive_conditions = summarizer._readonly_reduction_positive_conditions(
        FunctionReturnAnalysis(
            function_name="dummy",
            entry_point="0x0",
            parameters=[pointer_param, count_param],
            returns=[],
        ),
        pointer_param,
        count_param,
        signed_counter=True,
    )
    partial_exact_return = ReturnInfo(
        address="0x1100",
        conditions=[
            _cond("INT_NOTEQUAL", _param("param_1", size=8), _const(0, size=8)),
            _cond("INT_EQUAL", _param("param_2"), _const(1)),
            _cond("INT_NOTEQUAL", _param("flag"), _const(0)),
        ],
        value=_const(7),
    )

    assert summarizer._readonly_exact_count_region_is_fully_covered_by_return(
        partial_exact_return,
        positive_conditions,
        count_param,
        1,
    ) is False


def test_structural_recurrence_prefix_coverage_requires_matching_non_count_guards(monkeypatch):
    summarizer = StructuralRecurrenceSummarizer(tracer=None, debug=False)
    pointer_param = {"name": "param_1", "index": 0, "data_type": "int *", "size": 8, "is_signed": False}
    count_param = {"name": "param_2", "index": 1, "data_type": "int", "size": 4, "is_signed": True}
    analysis = FunctionReturnAnalysis(
        function_name="readonly_prefix_guard_mismatch_like",
        entry_point="0x1200",
        parameters=[pointer_param, count_param],
        returns=[],
    )
    proof = _readonly_accumulator_proof(
        base_ref=LocationBaseRef.parameter("param_1", index=0),
        count_expr=_param("param_2"),
        stride=4,
        element_size=4,
        start_index=3,
    )
    broad_ret = ReturnInfo(
        address="0x1200",
        conditions=[
            _cond("INT_NOTEQUAL", _param("param_1", size=8), _const(0, size=8)),
            _cond("INT_SLESS", _const(0), _param("param_2")),
            _cond("INT_NOTEQUAL", _param("flag"), _const(0)),
        ],
        value=_const(1),
    )
    wrong_witness = ReturnInfo(
        address="0x1201",
        conditions=[
            _cond("INT_NOTEQUAL", _param("param_1", size=8), _const(0, size=8)),
            _cond("INT_EQUAL", _param("param_2"), _const(1)),
            _cond("INT_EQUAL", _param("flag"), _const(0)),
        ],
        value=_const(2),
    )
    analysis.returns = [broad_ret, wrong_witness]
    monkeypatch.setattr(
        summarizer,
        "_readonly_positive_return_matches_accumulator_proof",
        lambda *_args, **_kwargs: True,
    )

    assert summarizer._readonly_positive_prefix_is_exactly_covered(
        analysis,
        pointer_param,
        count_param,
        broad_ret,
        proof,
    ) is False


def test_return_analyzer_normalization_does_not_promote_vectorized_readonly_start():
    analyzer = ReturnAnalyzer(program=None, debug=False)
    params = [
        {"name": "param_1", "index": 0, "data_type": "int *", "size": 8},
        {"name": "param_2", "index": 1, "data_type": "int", "size": 4, "is_signed": True},
    ]
    base_ref = LocationBaseRef.parameter("param_1", index=0)
    count_expr = _param("param_2", size=4)
    accumulator_proof = _readonly_accumulator_proof(
        base_ref=base_ref,
        count_expr=count_expr,
        stride=4,
        element_size=4,
        start_index=3,
    )
    loop_summary = LoopSummaryRef(
        start_expr=Expression.constant(0, size=4),
        limit_expr=count_expr,
        step_expr=Expression.constant(1, size=4),
        term_descriptor=LoopTermDescriptorRef(kind="readonly_memory"),
    )
    reduction_expr = Expression.intrinsic(
        "READONLY_SUM",
        [
            Expression.parameter("param_1", index=0, data_type="int *", size=8),
            Expression.parameter("param_2", index=1, data_type="int", size=4),
        ],
        size=4,
        runtime_ref=ReadonlyReductionRef(
            reduction_kind="readonly_sum",
            pointer_base_ref=base_ref,
            count_parameter_name="param_2",
            count_parameter_index=1,
            stride=4,
            element_size=4,
            result_size=4,
            signed_counter=True,
            loop_summary=loop_summary,
            accumulator_proof=accumulator_proof,
        ),
        opcode=READONLY_SUM_OPCODE,
    )
    corrupted = ReturnInfo(
        address="0x1020",
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

    analysis = create_mock_analysis(
        "readonly_partition_preserved_vectorized_start_index",
        return_type="int",
        parameters=params,
        returns=[corrupted],
    )

    analyzer._normalize_return_partition(analysis)

    normalized_conditions = [cond.to_string() for cond in analysis.returns[0].conditions]

    assert normalized_conditions == ["(0 < param_2)"]
    assert "(3 < param_2)" not in normalized_conditions


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


def test_exact_counter_value_recovers_widened_affine_equality_selector():
    summarizer = StructuralRecurrenceSummarizer(_FakeTracer("unused", _const(0)), debug=False)
    count_expr = Expression.parameter("param_2", index=1, data_type="uint", size=4)
    widened_minus_start = Expression.binary_op(
        "INT_SUB",
        Expression.unary_op("INT_ZEXT", count_expr),
        Expression.constant(3, size=8),
    )
    selector = Condition(
        Expression.binary_op(
            "INT_NOTEQUAL",
            Expression.binary_op(
                "INT_ADD",
                widened_minus_start,
                Expression.constant(-1, size=8),
            ),
            Expression.constant(0, size=8),
        ),
        negated=True,
    )

    exact = summarizer._exact_counter_value_from_conditions(
        [
            _cond("INT_SLESS", _const(0), count_expr),
            _cond("INT_SLESS", widened_minus_start, Expression.constant(8, size=8)),
            _cond("INT_SLESS", count_expr, _const(4), negated=True),
            selector,
        ],
        "param_2",
    )

    assert exact == 4


def test_bounded_prefix_region_drops_only_singleton_counter_selector():
    summarizer = StructuralRecurrenceSummarizer(_FakeTracer("unused", _const(0)), debug=False)
    count_param = {"name": "param_2", "index": 1, "data_type": "ulong", "size": 8, "is_signed": False}
    count_expr = Expression.parameter("param_2", index=1, data_type="ulong", size=8)
    singleton_selector = Condition(
        Expression.binary_op(
            "INT_NOTEQUAL",
            Expression.binary_op(
                "INT_SUB",
                Expression.binary_op("INT_AND", count_expr, Expression.constant(0xFFFFFFFF, size=8)),
                Expression.constant(1, size=8),
            ),
            Expression.constant(0, size=8),
        ),
        negated=True,
    )
    conditions = [
        _cond("INT_NOTEQUAL", Expression.parameter("param_1", index=0, data_type="int *", size=8), _const(0, size=8)),
        _cond("INT_SLESS", _const(0, size=8), count_expr),
        _cond("INT_SLESS", count_expr, _const(4, size=8)),
        singleton_selector,
    ]

    bounded = summarizer._bounded_prefix_region_conditions_from_exact_anchor(
        conditions,
        count_param,
        exact_count=1,
        upper_bound=3,
    )

    assert bounded is not None
    rendered = [condition.to_string() for condition in bounded]
    assert singleton_selector.to_string() not in rendered
    assert "(param_1 != 0)" in rendered
    assert "(0 < param_2)" in rendered
    assert "(param_2 < 4)" in rendered
    assert summarizer._conditions_allow_counter_value(bounded, count_param, 2)
    assert summarizer._conditions_allow_counter_value(bounded, count_param, 3)
    assert not summarizer._conditions_allow_counter_value(bounded, count_param, 4)


def test_bounded_counter_region_coverage_accepts_exact_count_partition():
    summarizer = StructuralRecurrenceSummarizer(_FakeTracer("unused", _const(0)), debug=False)
    count_param = {"name": "param_2", "index": 1, "data_type": "int", "size": 4, "is_signed": True}
    count_expr = Expression.parameter("param_2", index=1, data_type="int", size=4)
    region = [
        _cond("INT_NOTEQUAL", Expression.parameter("param_1", index=0, data_type="int *", size=8), _const(0, size=8)),
        _cond("INT_SLESS", _const(0), count_expr),
        _cond("INT_SLESS", _const(3), count_expr, negated=True),
    ]
    exact_returns = [
        ReturnInfo(
            address="0x1000",
            value=_mem("param_1", (count_value - 1) * 4),
            conditions=region + [summarizer._counter_equality_condition(count_param, count_value)],
        )
        for count_value in (1, 2, 3)
    ]

    assert summarizer._readonly_bounded_counter_region_is_covered_by_exact_returns(
        region,
        exact_returns,
        count_param,
    )
    assert not summarizer._readonly_bounded_counter_region_is_covered_by_exact_returns(
        region,
        exact_returns[:2],
        count_param,
    )
