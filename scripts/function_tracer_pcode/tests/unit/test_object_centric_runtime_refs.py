# -*- coding: utf-8 -*-

from scripts.function_tracer_pcode.tests.unit._input_correspondence_support import comparison_of, echo_input_correspondence
from unittest.mock import Mock
from scripts.function_tracer_pcode.smt import ParallelSolverRunner

from scripts.function_tracer_pcode.analysis.effects.summary import (
    CanonicalLocation,
    summarize_store_effects,
    post_state_read_expression_for_location,
)
from scripts.function_tracer_pcode.analysis.condition.smt_oracle import ConditionSMTOracle
from scripts.function_tracer_pcode.core import (
    COUNTED_LOOP_SUM_OPCODE,
    CallTargetRef,
    Condition,
    ComposedLoopSummaryRef,
    DeferredCallInfo,
    CountedStateTransitionLoopSummaryRef,
    CountedLoopSummaryRef,
    Expression,
    FunctionReturnAnalysis,
    LocationBaseRef,
    LoopBodyEffectRef,
    LoopCaseRef,
    LoopSummaryComparisonResult,
    LoopSideEffectProfileRef,
    LoopSummaryRef,
    LoopTermDescriptorRef,
    LoopVariableIdentityRef,
    PcodeOpRef,
    PostStateReadRef,
    PostStateSnapshotRef,
    ReductionAccumulatorProof,
    ReadonlyReductionLowering,
    ReadonlyReductionRef,
    ReadonlyReductionTermRef,
    ReadonlyReductionWitness,
    ReturnInfo,
    StorageInfo,
    UnknownValueRef,
    coerce_call_target_ref,
    compare_loop_summaries,
    loop_summary_method_b_key,
)
from scripts.function_tracer_pcode.proof.strategies.pairwise import PairwiseStrategy
from scripts.function_tracer_pcode.proof.strategies import pairwise as pairwise_module
from scripts.function_tracer_pcode.proof.strategies.pairwise_models import ReturnCase
from scripts.function_tracer_pcode.proof.strategies.pairwise_query_builder import build_pair_query
from scripts.function_tracer_pcode.checker.unknown_reason import (
    UnknownReasonId,
    build_unknown_recovery_actions,
    get_unknown_recovery_plan,
    make_internal_v2_reason_diagnostic,
    make_unknown_reason,
)
from scripts.function_tracer_pcode.proof.formula.builder import FormulaBuilder
from scripts.function_tracer_pcode.tests.unit._loop_test_fixtures import (
    readonly_loop_summary as _readonly_loop_summary,
    readonly_sum_expr as _readonly_sum_expr,
)


def _typed_method_b_reason(target):
    return make_internal_v2_reason_diagnostic(
        "loop_summary_semantic_equality_unproven",
        stage="S_PAIRWISE",
        pair_or_case="(0,1)",
        evidence_refs=("loop_summary_guard_mismatch",),
        recovery_proof_obligations=get_unknown_recovery_plan(
            UnknownReasonId.METHOD_B_CLOSURE_BLOCKED
        ).proof_obligations,
        object_target_key=target,
    )
from scripts.function_tracer_pcode.proof.formula.returns import _readonly_refs_share_surface
from scripts.function_tracer_pcode.core.semantic_snapshot import semantic_projection


def _lowering_identity(expr):
    """loop lowering が SMT function 名に使う identity（凍結時に確定した値）。"""

    return semantic_projection(expr).loop_lowering.identity

from scripts.function_tracer_pcode.tests.conftest import create_mock_analysis


class _FakeAddressSpace:
    def __init__(self, name):
        self._name = name

    def getName(self):
        return self._name


class _FakeAddress:
    def __init__(self, space_name, offset):
        self._space = _FakeAddressSpace(space_name)
        self._offset = offset

    def getAddressSpace(self):
        return self._space

    def getOffset(self):
        return self._offset


class _FakeSeqnum:
    def __init__(self, target, time, order):
        self._target = target
        self._time = time
        self._order = order

    def getTarget(self):
        return self._target

    def getTime(self):
        return self._time

    def getOrder(self):
        return self._order


class _FakeVarnode:
    def __init__(self, size):
        self._size = size

    def getSize(self):
        return self._size


class _FakePcodeOp:
    def __init__(
        self,
        *,
        target_offset=0x1010,
        time=23,
        order=7,
        opcode=19,
        mnemonic="RETURN",
        parent=None,
        inputs=None,
    ):
        self._seqnum = _FakeSeqnum(_FakeAddress("ram", target_offset), time=time, order=order)
        self._opcode = opcode
        self._mnemonic = mnemonic
        self._inputs = tuple(inputs) if inputs is not None else (_FakeVarnode(8),)
        self._output = _FakeVarnode(4)
        self._parent = parent

    def getSeqnum(self):
        return self._seqnum

    def getOpcode(self):
        return self._opcode

    def getMnemonic(self):
        return self._mnemonic

    def getNumInputs(self):
        return len(self._inputs)

    def getInput(self, index):
        return self._inputs[index]

    def getOutput(self):
        return self._output

    def getParent(self):
        return self._parent


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
    def __init__(self, items):
        self._items = list(items)

    def getIterator(self):
        return _FakeIterator(self._items)


class _FakeEffectBlockInfo:
    def __init__(self, pcode_ops):
        self.pcode_ops = list(pcode_ops)


class _CompletePathTracker:
    def get_all_valid_paths_to_block(self, _block_info):
        return [[]]


class _PcodeRefTracer:
    def __init__(self, pcode_ref):
        self._pcode_ref = pcode_ref

    def _make_pcode_op_ref(self, pcode_op):
        return self._pcode_ref

    def resolve_call_target_ref(self, *_args, **_kwargs):
        return CallTargetRef.from_name("callee", program_id=1, entry_offset=0x401000)

    def trace_varnode(self, *_args, **_kwargs):
        return Expression.parameter("fp", index=0, size=8, data_type="int (*)(int)")


def test_coerce_call_target_ref_rejects_raw_strings():
    assert coerce_call_target_ref("callee") is None


def test_pcode_op_ref_full_key_uses_object_context_when_available():
    ref = PcodeOpRef.from_pcode_op(
        _FakePcodeOp(),
        binary_id="B11",
        function_entry=_FakeAddress("ram", 0x1000),
        local_op_ordinal=2,
    )

    assert ref is not None
    assert ref.stable_key() == (
        "pcode_op",
        "B11",
        ("function_entry", "ram", 0x1000),
        ("seq_target", "ram", 0x1010),
        23,
        7,
        19,
        2,
    )
    assert ref.to_dict()["function_entry_space"] == "ram"
    assert ref.to_dict()["target_space"] == "ram"


def test_pcode_op_ref_full_key_distinguishes_same_site_local_ordinals():
    first = PcodeOpRef(
        binary_id="B11",
        function_entry_space="ram",
        function_entry_offset=0x1000,
        target_space="ram",
        target_offset=0x1010,
        seq_time=23,
        seq_order=7,
        opcode=19,
        local_op_ordinal=0,
        mnemonic="RETURN",
    )
    second = PcodeOpRef(
        binary_id="B11",
        function_entry_space="ram",
        function_entry_offset=0x1000,
        target_space="ram",
        target_offset=0x1010,
        seq_time=23,
        seq_order=7,
        opcode=19,
        local_op_ordinal=1,
        mnemonic="RETURN",
    )

    assert first.stable_key() != second.stable_key()


def test_unknown_value_ref_phi_circular_keeps_pcode_origin():
    pcode_ref = PcodeOpRef(
        binary_id="B11",
        function_entry_space="ram",
        function_entry_offset=0x1000,
        target_space="ram",
        target_offset=0x1010,
        seq_time=23,
        seq_order=7,
        opcode=27,
        local_op_ordinal=1,
        mnemonic="MULTIEQUAL",
    )

    ref = UnknownValueRef.phi_circular(pcode_op_ref=pcode_ref)

    assert ref.stable_key() == (
        "opaque_unknown",
        "phi_circular",
        None,
        None,
        "multiequal_pcode_op",
        ("stable", pcode_ref.stable_key()),
    )
    assert ref.diagnostic_key() == ref.stable_key() + (
        ("diagnostic_origin", ("stable", pcode_ref.stable_key())),
    )
    assert ref.to_dict()["origin_kind"] == "multiequal_pcode_op"
    assert ref.to_dict()["origin_ref"]["kind"] == "pcode_op"


def test_pcode_op_ref_full_key_uses_seq_time_and_excludes_program_uid():
    ref = PcodeOpRef.from_pcode_op(
        _FakePcodeOp(time=23, order=7),
        binary_id="B11",
        program_uid=12345,
        function_entry=_FakeAddress("ram", 0x1000),
        local_op_ordinal=2,
    )
    same_import_ref = PcodeOpRef.from_pcode_op(
        _FakePcodeOp(time=23, order=7),
        binary_id="B11",
        program_uid=67890,
        function_entry=_FakeAddress("ram", 0x1000),
        local_op_ordinal=2,
    )
    moved_time_ref = PcodeOpRef.from_pcode_op(
        _FakePcodeOp(time=24, order=7),
        binary_id="B11",
        program_uid=12345,
        function_entry=_FakeAddress("ram", 0x1000),
        local_op_ordinal=2,
    )

    assert ref is not None
    assert same_import_ref is not None
    assert moved_time_ref is not None
    assert ref.stable_key() == same_import_ref.stable_key()
    assert ref.stable_key() != moved_time_ref.stable_key()
    assert ref.to_dict()["program_uid"] == 12345


def test_external_call_target_stable_key_marks_unscoped_symbol_without_library():
    ref = CallTargetRef.from_name("puts", is_external=True)
    other = CallTargetRef.from_name("printf", is_external=True)
    scoped = CallTargetRef.from_name("puts", is_external=True, library_name="libc")
    local_name_only = CallTargetRef.from_name("puts")

    assert ref.stable_key() == ("external_function_unscoped", "puts", None)
    assert ref.analysis_key() is None
    assert scoped.stable_key() == ("external_function", "libc", "puts", None)
    assert scoped.analysis_key() == scoped.stable_key()
    assert ref.stable_key() != other.stable_key()
    assert ref.stable_key() != scoped.stable_key()
    assert ref.stable_key() != local_name_only.stable_key()


def test_local_name_only_call_target_stable_key_distinguishes_symbol_but_not_analysis_key():
    first = CallTargetRef.from_name("a")
    second = CallTargetRef.from_name("b")
    scoped_name = CallTargetRef.from_name("a", program_id=123)

    assert first.stable_key() == ("function_name_only", None, "a")
    assert second.stable_key() == ("function_name_only", None, "b")
    assert scoped_name.stable_key() == ("function_name_only", 123, "a")
    assert first.stable_key() != second.stable_key()
    assert first.stable_key() != scoped_name.stable_key()
    assert first.analysis_key() is None
    assert second.analysis_key() is None


def test_pcode_op_ref_derives_local_ordinal_from_equivalent_parent_wrapper():
    first = _FakePcodeOp(target_offset=0x1000, order=1, opcode=10, mnemonic="COPY")
    equivalent_wrapper = _FakePcodeOp(target_offset=0x1010, order=7, opcode=19, mnemonic="RETURN")
    block = _FakeBlock([first, equivalent_wrapper])
    queried = _FakePcodeOp(target_offset=0x1010, order=7, opcode=19, mnemonic="RETURN", parent=block)

    ref = PcodeOpRef.from_pcode_op(
        queried,
        binary_id="B11",
        function_entry=_FakeAddress("ram", 0x1000),
    )

    assert ref is not None
    assert ref.local_op_ordinal == 1
    assert ref.stable_key() == (
        "pcode_op",
        "B11",
        ("function_entry", "ram", 0x1000),
        ("seq_target", "ram", 0x1010),
        23,
        7,
        19,
        1,
    )


def test_pcode_op_ref_ignores_mock_parent_iterator_with_non_boolean_has_next():
    parent = Mock()
    parent.getIterator.return_value = Mock()
    queried = _FakePcodeOp(target_offset=0x1010, order=7, opcode=19, mnemonic="RETURN", parent=parent)

    ref = PcodeOpRef.from_pcode_op(
        queried,
        binary_id="B11",
        function_entry=_FakeAddress("ram", 0x1000),
    )

    assert ref is not None
    assert ref.local_op_ordinal is None


def test_unsupported_call_effect_summary_uses_tracer_full_pcode_context():
    pcode_ref = PcodeOpRef(
        binary_id="B11",
        function_entry_space="ram",
        function_entry_offset=0x400000,
        target_space="ram",
        target_offset=0x401020,
        seq_time=31,
        seq_order=7,
        opcode=8,
        local_op_ordinal=2,
        mnemonic="CALLIND",
    )
    call_op = _FakePcodeOp(
        target_offset=0x401020,
        time=31,
        order=7,
        opcode=8,
        mnemonic="CALLIND",
    )
    summary = summarize_store_effects(
        [_FakeEffectBlockInfo([call_op])],
        _PcodeRefTracer(pcode_ref),
        _CompletePathTracker(),
        parameters=[],
        direct_call_summary=lambda _target_ref, _args: None,
    )

    assert summary.has_unsupported_call is True
    assert len(summary.unsupported_call_sites) == 1
    assert summary.unsupported_call_sites[0].pcode_op_ref.stable_key() == pcode_ref.stable_key()


def test_loop_summary_comparator_accepts_pure_object_centric_semantic_key():
    summary = LoopSummaryRef(
        start_expr=0,
        limit_expr="n",
        step_expr=1,
        term_descriptor=LoopTermDescriptorRef(kind="affine_residue"),
    )

    result = compare_loop_summaries(summary, summary)

    assert result.status == "equivalent"
    assert result.is_equivalent() is True


def test_loop_summary_comparator_rejects_different_side_effect_profiles():
    pure = LoopSummaryRef(
        start_expr=0,
        limit_expr="n",
        step_expr=1,
        term_descriptor=LoopTermDescriptorRef(kind="affine_residue"),
        side_effect_profile=LoopSideEffectProfileRef(profile="pure"),
    )
    effectful = LoopSummaryRef(
        start_expr=0,
        limit_expr="n",
        step_expr=1,
        term_descriptor=LoopTermDescriptorRef(kind="affine_residue"),
        side_effect_profile=LoopSideEffectProfileRef(
            profile="effect_aware",
            memory_writes=True,
            effect_count=1,
            effect_descriptors=(
                LoopBodyEffectRef(
                    kind="memory_write",
                    source="pcode_scan",
                    scope="loop",
                    order_key=1,
                ),
            ),
        ),
    )

    result = compare_loop_summaries(pure, effectful)

    assert result.status == "incompatible"
    assert result.is_equivalent() is None
    assert result.blocks_shortcut() is True


def test_loop_summary_comparator_emits_case_aware_solver_obligation():
    count = Expression.parameter("count", index=1, data_type="int", size=4)
    zero = Expression.constant(0, size=4)
    left = LoopSummaryRef(
        start_expr=zero,
        limit_expr=count,
        step_expr=Expression.constant(1, size=4),
        term_descriptor=LoopTermDescriptorRef(kind="affine_residue", residue_cases=((1, 0, 5, 0),)),
        side_effect_profile=LoopSideEffectProfileRef(profile="pure"),
    )
    right = LoopSummaryRef(
        start_expr=Expression.binary_op("INT_ADD", zero, Expression.constant(0, size=4)),
        limit_expr=count,
        step_expr=Expression.constant(1, size=4),
        term_descriptor=left.term_descriptor,
        side_effect_profile=left.side_effect_profile,
    )

    result = compare_loop_summaries(left, right)

    assert result.status == "unknown"
    assert result.proof_obligation is not None
    assert result.proof_obligation.proof_kind == "case_aware_loop_summary_solver_equality"
    assert result.proof_obligation.required_evidence == (
        "guard_partition",
        "transition_or_term_equality",
        "pure_side_effect_profile",
        "width_policy",
    )


def test_loop_summary_comparator_uses_injected_solver_prover():
    count = Expression.parameter("count", index=1, data_type="int", size=4)
    zero = Expression.constant(0, size=4)
    left = LoopSummaryRef(
        start_expr=zero,
        limit_expr=count,
        step_expr=Expression.constant(1, size=4),
        term_descriptor=LoopTermDescriptorRef(kind="affine_residue", residue_cases=((1, 0, 5, 0),)),
        side_effect_profile=LoopSideEffectProfileRef(profile="pure"),
    )
    right = LoopSummaryRef(
        start_expr=Expression.binary_op("INT_ADD", zero, Expression.constant(0, size=4)),
        limit_expr=count,
        step_expr=Expression.constant(1, size=4),
        term_descriptor=left.term_descriptor,
        side_effect_profile=left.side_effect_profile,
    )
    seen = []

    def prover(obligation):
        seen.append(obligation)
        return LoopSummaryComparisonResult(
            "equivalent",
            "unit-test solver proof",
            proof_obligation=obligation,
        )

    result = compare_loop_summaries(left, right, solver_prover=prover)

    assert result.status == "equivalent"
    assert result.is_equivalent() is True
    assert len(seen) == 1
    assert result.proof_obligation == seen[0]


def test_loop_summary_comparator_does_not_call_prover_for_incompatible_surfaces():
    pure = LoopSummaryRef(
        start_expr=0,
        limit_expr="n",
        step_expr=1,
        term_descriptor=LoopTermDescriptorRef(kind="affine_residue"),
        side_effect_profile=LoopSideEffectProfileRef(profile="pure"),
    )
    effectful = LoopSummaryRef(
        start_expr=0,
        limit_expr="n",
        step_expr=1,
        term_descriptor=LoopTermDescriptorRef(kind="affine_residue"),
        side_effect_profile=LoopSideEffectProfileRef(profile="effect_aware", memory_writes=True, effect_count=1),
    )
    prover = Mock()

    result = compare_loop_summaries(pure, effectful, solver_prover=prover)

    assert result.status == "incompatible"
    prover.assert_not_called()


def test_composed_loop_summary_ref_projects_current_surface_and_keys_handoff():
    prior = LoopSummaryRef(
        start_expr=Expression.constant(0, size=4),
        limit_expr=Expression.parameter("count", index=1, data_type="int", size=4),
        step_expr=Expression.constant(1, size=4),
        term_descriptor=LoopTermDescriptorRef(kind="affine_residue", residue_cases=((1, 0, 5, 0),)),
        side_effect_profile=LoopSideEffectProfileRef(profile="pure"),
    )
    current = LoopSummaryRef(
        start_expr=Expression.parameter("seed", index=2, data_type="int", size=4),
        limit_expr=Expression.parameter("count", index=1, data_type="int", size=4),
        step_expr=Expression.constant(1, size=4),
        term_descriptor=LoopTermDescriptorRef(kind="affine_residue", residue_cases=((1, 0, 1, 0),)),
        side_effect_profile=LoopSideEffectProfileRef(profile="pure"),
        guard_constraints=(Condition(Expression.binary_op("INT_SLESS", Expression.constant(0, size=4), Expression.parameter("count", index=1, data_type="int", size=4))),),
        loop_var_unit="induction_value",
    )
    handoff = (
        "prior_state_transition_handoff_proof_ref",
        ("proof_obligation_id", "prior_state_transition_handoff", ("target", "stable")),
        ("target", "stable"),
    )

    composed = ComposedLoopSummaryRef(prior=prior, current=current, handoff_proof_key=handoff)

    assert composed.start_expr is current.start_expr
    assert composed.term_descriptor is current.term_descriptor
    assert composed.guard_constraints == current.guard_constraints
    assert composed.stable_key() is not None
    assert composed.semantic_key() is not None
    assert composed.stable_key() != ComposedLoopSummaryRef(
        prior=prior,
        current=current,
        handoff_proof_key=("prior_state_transition_handoff_proof_ref", "other", ("target", "stable")),
    ).stable_key()


def test_composed_loop_summary_ref_is_excluded_from_method_b_fast_path():
    count = Expression.parameter("count", index=0, data_type="int", size=4)
    state = Expression.parameter("state", index=1, data_type="int", size=4)
    one = Expression.constant(1, size=4)
    zero = Expression.constant(0, size=4)

    def prior_transition(multiplier: int) -> CountedStateTransitionLoopSummaryRef:
        transition = Expression.binary_op("INT_MULT", state, Expression.constant(multiplier, size=4))
        return CountedStateTransitionLoopSummaryRef(
            initial_state=one,
            start_expr=zero,
            limit_expr=count,
            step_expr=one,
            transition_expr=transition,
            state_placeholder=state,
            transition_cases=(((), transition.structural_key()),),
            side_effect_profile=LoopSideEffectProfileRef(profile="pure"),
            state_size=4,
            result_size=4,
            signed_loop=True,
            handoff_proof_key=(
                "prior_state_transition_handoff_proof_ref",
                ("proof_obligation_id", "prior_state_transition_handoff", ("target", "stable")),
                ("target", "stable"),
            ),
        )

    current = LoopSummaryRef(
        start_expr=state,
        limit_expr=count,
        step_expr=one,
        term_descriptor=LoopTermDescriptorRef(kind="affine_residue", residue_cases=((1, 0, 1, 0),)),
        side_effect_profile=LoopSideEffectProfileRef(profile="pure"),
        loop_var_unit="induction_value",
    )
    left = ComposedLoopSummaryRef(
        prior=prior_transition(5),
        current=current,
        handoff_proof_key=("prior_state_transition_handoff_proof_ref", "left", ("target", "stable")),
    )
    right = ComposedLoopSummaryRef(
        prior=prior_transition(6),
        current=current,
        handoff_proof_key=("prior_state_transition_handoff_proof_ref", "right", ("target", "stable")),
    )

    assert loop_summary_method_b_key(left) is None
    assert loop_summary_method_b_key(right) is None
    result = compare_loop_summaries(left, right)
    assert result.status == "unknown"
    assert result.is_equivalent() is None


def _pure_counted_loop_summary() -> LoopSummaryRef:
    return LoopSummaryRef(
        start_expr=0,
        limit_expr="n",
        step_expr=1,
        term_descriptor=LoopTermDescriptorRef(kind="affine_residue"),
        side_effect_profile=LoopSideEffectProfileRef(profile="pure"),
    )


def _effect_aware_counted_loop_summary() -> LoopSummaryRef:
    return LoopSummaryRef(
        start_expr=0,
        limit_expr="n",
        step_expr=1,
        term_descriptor=LoopTermDescriptorRef(kind="affine_residue"),
        side_effect_profile=LoopSideEffectProfileRef(
            profile="effect_aware",
            memory_writes=True,
            effect_count=1,
            effect_descriptors=(
                LoopBodyEffectRef(
                    kind="memory_write",
                    source="pcode_scan",
                    scope="loop",
                    address_space="ram",
                    location="addr",
                    value_expr="value",
                    order_key=1,
                ),
            ),
        ),
    )


def _path_sensitive_counted_loop_summary() -> LoopSummaryRef:
    return LoopSummaryRef(
        start_expr=0,
        limit_expr="n",
        step_expr=1,
        term_descriptor=LoopTermDescriptorRef(kind="affine_residue"),
        cases=(
            LoopCaseRef(
                path_conditions=("i_is_even",),
                body_effect=LoopBodyEffectRef(kind="accumulator_update", value_expr="acc+i"),
                term_expr="i",
                case_kind="accumulator_delta",
            ),
        ),
    )


def test_parameter_location_semantic_key_requires_object_identity():
    assert LocationBaseRef.parameter("base").semantic_key() is None
    assert LocationBaseRef.parameter("base", index=0).semantic_key() == ("parameter", 0)


def test_parameter_location_negative_index_is_unresolved_not_identity():
    negative = LocationBaseRef.parameter("base", index=-1)
    missing = LocationBaseRef.parameter("base")
    indexed = LocationBaseRef.parameter("base", index=0)

    assert negative.parameter_index is None
    assert negative.semantic_key() is None
    assert negative.stable_key() == missing.stable_key()
    assert negative != missing
    assert negative != indexed
    assert negative.stable_key() != indexed.stable_key()


def test_readonly_contract_refuses_name_only_parameter_identity():
    indexed_count = Expression.parameter("count", index=1, data_type="int", size=4)
    indexed_proof = ReductionAccumulatorProof(
        reduction_kind="memory_sum",
        pointer_base_ref=LocationBaseRef.parameter("base", index=0),
        count_parameter_name="count",
        count_parameter_index=1,
        limit_expr=indexed_count,
        result_size=4,
        stride=4,
        element_size=4,
        index_scale=4,
        loop_body_witnesses=(
            ReadonlyReductionWitness(
                exact_count=1,
                terms=(ReadonlyReductionTermRef(byte_offset=0, access_size=4),),
            ),
        ),
    )
    name_only_proof = ReductionAccumulatorProof(
        reduction_kind="memory_sum",
        pointer_base_ref=LocationBaseRef.parameter("base"),
        count_parameter_name="count",
        count_parameter_index=None,
        limit_expr=Expression.parameter("count", data_type="int", size=4),
        result_size=4,
        stride=4,
        element_size=4,
        index_scale=4,
        loop_body_witnesses=(
            ReadonlyReductionWitness(
                exact_count=1,
                terms=(ReadonlyReductionTermRef(byte_offset=0, access_size=4),),
            ),
        ),
    )

    assert indexed_proof.readonly_term_sequence_contract_key() is not None
    assert name_only_proof.readonly_term_sequence_contract_key() is None


def test_loop_summary_semantic_key_refuses_name_only_memory_base_identity():
    summary = LoopSummaryRef(
        start_expr=Expression.constant(0, size=4),
        limit_expr=Expression.parameter("count", index=1, data_type="int", size=4),
        step_expr=Expression.constant(1, size=4),
        term_descriptor=LoopTermDescriptorRef(
            kind="memory_load",
            reduction_kind="sum",
            location_base_ref=LocationBaseRef.parameter("base"),
            start_offset=0,
            stride=4,
            element_size=4,
            result_size=4,
        ),
        side_effect_profile=LoopSideEffectProfileRef(profile="pure_memory_read", memory_reads=True),
    )

    assert summary.semantic_key() is None


def test_readonly_reduction_semantic_key_refuses_name_only_count_identity():
    loop_summary = _readonly_loop_summary(start=0)
    ref = ReadonlyReductionRef(
        reduction_kind="memory_sum",
        pointer_base_ref=LocationBaseRef.parameter("base", index=0),
        count_parameter_name="count",
        count_parameter_index=None,
        stride=4,
        element_size=4,
        result_size=4,
        signed_counter=True,
        loop_summary=loop_summary,
    )

    assert ref.semantic_key() is None


def test_pairwise_readonly_shortcut_requires_count_object_identity():
    loop_summary = _readonly_loop_summary(start=0)
    ref = ReadonlyReductionRef(
        reduction_kind="memory_sum",
        pointer_base_ref=LocationBaseRef.parameter("base", index=0),
        count_parameter_name="count",
        count_parameter_index=None,
        stride=4,
        element_size=4,
        result_size=4,
        signed_counter=True,
        loop_summary=loop_summary,
    )
    strategy = PairwiseStrategy(echo_input_correspondence(Mock()), Mock(), debug=False)

    decision = strategy._readonly_reduction_contract_shortcut_decision(
        ref,
        ref,
        requires_guard_equivalence=False,
        result_size=4,
    )

    assert strategy._readonly_count_identity_key(ref) is None
    assert decision.equivalent is False
    assert decision.reason == "readonly_contract_mismatch"


def test_storage_backed_pointer_and_count_identity_participates_in_readonly_shortcut():
    pointer_storage = StorageInfo(
        is_register=True,
        space_name="register",
        register_name="a0",
        base_register_name="a0",
        size=8,
        size_bits=64,
    )
    count_storage = StorageInfo(
        is_register=True,
        space_name="register",
        register_name="a1",
        base_register_name="a1",
        size=4,
        size_bits=32,
    )
    pointer_ref = LocationBaseRef.storage(
        space_id=0,
        space_name="register",
        offset=pointer_storage.base_register_offset,
        size=8,
        storage_identity_key=pointer_storage.storage_identity_key(),
        display_hint="a0",
    )
    count_expr_left = Expression.parameter(
        "renamed_count_left",
        data_type="int",
        size=4,
        storage_info=count_storage,
    )
    count_expr_right = Expression.parameter(
        "renamed_count_right",
        data_type="int",
        size=4,
        storage_info=count_storage,
    )
    left_ref = ReductionAccumulatorProof(
        reduction_kind="memory_sum",
        pointer_base_ref=pointer_ref,
        count_parameter_name="renamed_count_left",
        count_parameter_index=None,
        count_parameter_storage_identity_key=count_storage.storage_identity_key(),
        limit_expr=count_expr_left,
        result_size=4,
        stride=4,
        element_size=4,
    ).lower_to_readonly_reduction_ref()
    right_ref = ReductionAccumulatorProof(
        reduction_kind="memory_sum",
        pointer_base_ref=pointer_ref,
        count_parameter_name="renamed_count_right",
        count_parameter_index=None,
        count_parameter_storage_identity_key=count_storage.storage_identity_key(),
        limit_expr=count_expr_right,
        result_size=4,
        stride=4,
        element_size=4,
    ).lower_to_readonly_reduction_ref()
    strategy = PairwiseStrategy(echo_input_correspondence(Mock()), Mock(), debug=False)

    assert left_ref is not None
    assert right_ref is not None
    assert left_ref.semantic_key() == right_ref.semantic_key()
    assert strategy._readonly_count_identity_key(left_ref) == (
        "parameter_storage",
        count_storage.storage_identity_key(),
    )
    decision = strategy._readonly_reduction_contract_shortcut_decision(
        left_ref,
        right_ref,
        requires_guard_equivalence=False,
        result_size=4,
    )

    assert decision.equivalent is True
    assert decision.reason == "readonly_reduction_contract"


def test_storage_backed_count_identity_is_public_serialized_and_contract_keyed():
    count_storage = StorageInfo(
        is_register=True,
        space_name="register",
        register_name="a1",
        base_register_name="a1",
        size=4,
        size_bits=32,
    )
    count_storage_key = count_storage.storage_identity_key()
    proof = ReductionAccumulatorProof(
        reduction_kind="memory_sum",
        pointer_base_ref=LocationBaseRef.parameter("base", index=0),
        count_parameter_name="renamed_count",
        count_parameter_index=None,
        count_parameter_storage_identity_key=count_storage_key,
        limit_expr=Expression.parameter("renamed_count", data_type="int", size=4),
        result_size=4,
        stride=4,
        element_size=4,
        index_scale=4,
    )
    readonly_ref = proof.lower_to_readonly_reduction_ref()

    assert proof.count_parameter_semantic_identity() == ("parameter_storage", count_storage_key)
    assert proof.readonly_term_sequence_contract_key() is not None
    assert proof.to_dict()["count_parameter_storage_identity_key"] == count_storage_key
    assert readonly_ref is not None
    assert readonly_ref.count_parameter_semantic_identity() == ("parameter_storage", count_storage_key)
    assert readonly_ref.count_parameter_semantic_identities() == (
        ("parameter_storage", count_storage_key),
    )
    assert readonly_ref.semantic_key() is not None
    assert readonly_ref.to_dict()["count_parameter_storage_identity_key"] == count_storage_key


def test_storage_backed_count_identity_keeps_index_backcompat_for_readonly_consumers():
    count_storage = StorageInfo(
        is_register=True,
        space_name="register",
        register_name="a1",
        base_register_name="a1",
        size=4,
        size_bits=32,
    )
    count_storage_key = count_storage.storage_identity_key()
    count_with_storage = Expression.parameter(
        "renamed_count",
        index=1,
        data_type="int",
        size=4,
        storage_info=count_storage,
    )
    storage_backed_ref = ReductionAccumulatorProof(
        reduction_kind="memory_sum",
        pointer_base_ref=LocationBaseRef.parameter("base", index=0),
        count_parameter_name="renamed_count",
        count_parameter_index=1,
        count_parameter_storage_identity_key=count_storage_key,
        limit_expr=count_with_storage,
        result_size=4,
        stride=4,
        element_size=4,
        index_scale=4,
    ).lower_to_readonly_reduction_ref()
    legacy_ref = ReductionAccumulatorProof(
        reduction_kind="memory_sum",
        pointer_base_ref=LocationBaseRef.parameter("base", index=0),
        count_parameter_name="count",
        count_parameter_index=1,
        limit_expr=Expression.parameter("count", index=1, data_type="int", size=4),
        result_size=4,
        stride=4,
        element_size=4,
        index_scale=4,
    ).lower_to_readonly_reduction_ref()
    indexed_operand_without_storage = Expression.parameter("count", index=1, data_type="int", size=4)
    builder = FormulaBuilder()
    strategy = PairwiseStrategy(echo_input_correspondence(Mock()), Mock(), debug=False)

    assert storage_backed_ref is not None
    assert legacy_ref is not None
    assert storage_backed_ref.count_parameter_semantic_identity() == (
        "parameter_storage",
        count_storage_key,
    )
    assert storage_backed_ref.count_parameter_semantic_identities() == (
        ("parameter_storage", count_storage_key),
        ("parameter", 1),
    )
    assert builder._readonly_count_operand_matches_ref(
        indexed_operand_without_storage,
        storage_backed_ref,
    )
    assert strategy._readonly_count_identities_compatible(storage_backed_ref, legacy_ref)
    assert _readonly_refs_share_surface(storage_backed_ref, legacy_ref)
    storage_contract = storage_backed_ref.readonly_term_sequence_contract_key(result_size=4)
    legacy_contract = legacy_ref.readonly_term_sequence_contract_key(result_size=4)
    assert storage_contract is not None
    assert legacy_contract is not None
    assert storage_contract != legacy_contract
    assert strategy._readonly_reduction_contract_shortcut_decision(
        storage_backed_ref,
        legacy_ref,
        requires_guard_equivalence=False,
        result_size=4,
    ).equivalent


def test_readonly_contract_limit_key_compatibility_allows_storage_limit_to_legacy_index():
    count_storage = StorageInfo(
        is_register=True,
        space_name="register",
        register_name="a1",
        base_register_name="a1",
        size=4,
        size_bits=32,
    )
    count_storage_key = count_storage.storage_identity_key()
    storage_ref = ReductionAccumulatorProof(
        reduction_kind="memory_sum",
        pointer_base_ref=LocationBaseRef.parameter("base", index=0),
        count_parameter_name="renamed_count",
        count_parameter_index=1,
        count_parameter_storage_identity_key=count_storage_key,
        limit_expr=Expression.parameter(
            "renamed_count",
            index=1,
            data_type="int",
            size=4,
            storage_info=count_storage,
        ),
        result_size=4,
        stride=4,
        element_size=4,
        index_scale=4,
    ).lower_to_readonly_reduction_ref()
    legacy_ref = ReductionAccumulatorProof(
        reduction_kind="memory_sum",
        pointer_base_ref=LocationBaseRef.parameter("base", index=0),
        count_parameter_name="count",
        count_parameter_index=1,
        limit_expr=Expression.parameter("count", index=1, data_type="int", size=4),
        result_size=4,
        stride=4,
        element_size=4,
        index_scale=4,
    ).lower_to_readonly_reduction_ref()
    strategy = PairwiseStrategy(echo_input_correspondence(Mock()), Mock(), debug=False)

    assert storage_ref is not None
    assert legacy_ref is not None
    storage_contract = storage_ref.readonly_term_sequence_contract_key(result_size=4)
    legacy_contract = legacy_ref.readonly_term_sequence_contract_key(result_size=4)

    assert storage_contract is not None
    assert legacy_contract is not None
    assert strategy._readonly_contract_limit_keys_compatible(
        storage_contract[4],
        legacy_contract[4],
        storage_ref,
        legacy_ref,
    )
    assert strategy._readonly_contract_limit_keys_compatible(
        legacy_contract[4],
        storage_contract[4],
        legacy_ref,
        storage_ref,
    )


def test_readonly_contract_limit_key_compatibility_rejects_index_mismatch_or_conflicting_storage():
    count_storage = StorageInfo(
        is_register=True,
        space_name="register",
        register_name="a1",
        base_register_name="a1",
        size=4,
        size_bits=32,
    )
    other_storage = StorageInfo(
        is_register=True,
        space_name="register",
        register_name="a2",
        base_register_name="a2",
        size=4,
        size_bits=32,
    )
    storage_ref = ReadonlyReductionRef(
        reduction_kind="memory_sum",
        pointer_base_ref=LocationBaseRef.parameter("base", index=0),
        count_parameter_name="count",
        count_parameter_index=1,
        count_parameter_storage_identity_key=count_storage.storage_identity_key(),
    )
    legacy_ref = ReadonlyReductionRef(
        reduction_kind="memory_sum",
        pointer_base_ref=LocationBaseRef.parameter("base", index=0),
        count_parameter_name="count",
        count_parameter_index=1,
    )
    conflicting_storage_ref = ReadonlyReductionRef(
        reduction_kind="memory_sum",
        pointer_base_ref=LocationBaseRef.parameter("base", index=0),
        count_parameter_name="count",
        count_parameter_index=1,
        count_parameter_storage_identity_key=other_storage.storage_identity_key(),
    )
    storage_limit_key = (
        "loop_limit_parameter_storage",
        count_storage.storage_identity_key(),
    )
    legacy_limit_key = ("loop_limit_parameter", 1)
    mismatched_index_key = ("loop_limit_parameter", 2)
    strategy = PairwiseStrategy(echo_input_correspondence(Mock()), Mock(), debug=False)

    assert not strategy._readonly_contract_limit_keys_compatible(
        storage_limit_key,
        mismatched_index_key,
        storage_ref,
        legacy_ref,
    )
    assert not strategy._readonly_contract_limit_keys_compatible(
        storage_limit_key,
        legacy_limit_key,
        storage_ref,
        conflicting_storage_ref,
    )


def test_storage_backed_count_identity_conflict_rejects_index_fallback():
    count_storage = StorageInfo(
        is_register=True,
        space_name="register",
        register_name="a1",
        base_register_name="a1",
        size=4,
        size_bits=32,
    )
    other_count_storage = StorageInfo(
        is_register=True,
        space_name="register",
        register_name="a2",
        base_register_name="a2",
        size=4,
        size_bits=32,
    )
    count_storage_key = count_storage.storage_identity_key()
    other_count_storage_key = other_count_storage.storage_identity_key()
    left_ref = ReductionAccumulatorProof(
        reduction_kind="memory_sum",
        pointer_base_ref=LocationBaseRef.parameter("base", index=0),
        count_parameter_name="left_count",
        count_parameter_index=1,
        count_parameter_storage_identity_key=count_storage_key,
        limit_expr=Expression.parameter(
            "left_count",
            index=1,
            data_type="int",
            size=4,
            storage_info=count_storage,
        ),
        result_size=4,
        stride=4,
        element_size=4,
        index_scale=4,
    ).lower_to_readonly_reduction_ref()
    right_ref = ReductionAccumulatorProof(
        reduction_kind="memory_sum",
        pointer_base_ref=LocationBaseRef.parameter("base", index=0),
        count_parameter_name="right_count",
        count_parameter_index=1,
        count_parameter_storage_identity_key=other_count_storage_key,
        limit_expr=Expression.parameter(
            "right_count",
            index=1,
            data_type="int",
            size=4,
            storage_info=other_count_storage,
        ),
        result_size=4,
        stride=4,
        element_size=4,
        index_scale=4,
    ).lower_to_readonly_reduction_ref()
    conflicting_operand = Expression.parameter(
        "right_count",
        index=1,
        data_type="int",
        size=4,
        storage_info=other_count_storage,
    )
    builder = FormulaBuilder()
    strategy = PairwiseStrategy(echo_input_correspondence(Mock()), Mock(), debug=False)

    assert left_ref is not None
    assert right_ref is not None
    assert not builder._readonly_count_operand_matches_ref(conflicting_operand, left_ref)
    assert not _readonly_refs_share_surface(left_ref, right_ref)
    assert not strategy._readonly_count_identities_compatible(left_ref, right_ref)
    conflicting_parameters = [
        {
            "name": "right_count",
            "index": 1,
            "data_type": "int",
            "size": 4,
            "storage_info": other_count_storage,
        }
    ]
    assert strategy._reduction_count_parameter_descriptor(
        conflicting_parameters,
        left_ref.accumulator_proof,
    ) is None
    assert strategy._reduction_count_parameter_expression(
        conflicting_parameters,
        left_ref.accumulator_proof,
        32,
    ) is None
    decision = strategy._readonly_reduction_contract_shortcut_decision(
        left_ref,
        right_ref,
        requires_guard_equivalence=False,
        result_size=4,
    )
    assert not decision.equivalent
    assert decision.reason == "readonly_contract_mismatch"


def test_readonly_count_storage_relation_records_same_register_projection_without_compatibility():
    wide_count_storage = StorageInfo(
        is_register=True,
        space_name="register",
        register_name="a1",
        base_register_name="a1",
        base_register_offset=0x31D4,
        base_register_size_bits=64,
        bit_offset_in_base=0,
        size=8,
        size_bits=64,
    )
    narrow_count_storage = StorageInfo(
        is_register=True,
        space_name="register",
        register_name="a1_lo",
        base_register_name="a1",
        base_register_offset=0x31D4,
        base_register_size_bits=64,
        bit_offset_in_base=32,
        size=4,
        size_bits=32,
    )
    wide_ref = ReductionAccumulatorProof(
        reduction_kind="memory_sum",
        pointer_base_ref=LocationBaseRef.parameter("base", index=0),
        count_parameter_name="count",
        count_parameter_index=1,
        count_parameter_storage_identity_key=wide_count_storage.storage_identity_key(),
        limit_expr=Expression.parameter(
            "count",
            index=1,
            data_type="long",
            size=8,
            storage_info=wide_count_storage,
        ),
        result_size=4,
        stride=8,
        element_size=4,
        index_scale=8,
    ).lower_to_readonly_reduction_ref()
    narrow_ref = ReductionAccumulatorProof(
        reduction_kind="memory_sum",
        pointer_base_ref=LocationBaseRef.parameter("base", index=0),
        count_parameter_name="count",
        count_parameter_index=1,
        count_parameter_storage_identity_key=narrow_count_storage.storage_identity_key(),
        limit_expr=Expression.parameter(
            "count",
            index=1,
            data_type="int",
            size=4,
            storage_info=narrow_count_storage,
        ),
        result_size=4,
        stride=8,
        element_size=4,
        index_scale=4,
    ).lower_to_readonly_reduction_ref()
    strategy = PairwiseStrategy(echo_input_correspondence(Mock()), Mock(), debug=False)

    assert wide_ref is not None
    assert narrow_ref is not None
    assert not strategy._readonly_count_identities_compatible(wide_ref, narrow_ref)
    assert strategy._readonly_count_storage_relation_key(wide_ref, narrow_ref) == (
        "same_register_base_projection",
        ("base", (-1, 0x31D4, 64)),
        ("left_bits", 0, 64),
        ("right_bits", 32, 32),
        ("projection", "left_contains_right"),
    )


def test_method_b_closure_relation_records_one_sided_summary_exact_terms():
    base = Expression.parameter("base", index=0, data_type="int *", size=8)
    exact_expr = Expression.binary_op(
        "INT_ADD",
        Expression.memory(base, size=4),
        Expression.memory(
            Expression.binary_op("INT_ADD", base, Expression.constant(4, size=8)),
            size=4,
        ),
    )
    summary_expr = _readonly_sum_expr(_readonly_loop_summary(start=0, step=1))
    parameters = [
        {"name": "base", "index": 0, "data_type": "int *", "size": 8},
        {"name": "count", "index": 1, "data_type": "int", "size": 4},
    ]
    exact_case = ReturnCase(
        0,
        [],
        exact_expr,
        ReturnInfo(address="0x1000", value=exact_expr, conditions=[]),
        parameters=parameters,
    )
    summary_case = ReturnCase(
        1,
        [],
        summary_expr,
        ReturnInfo(address="0x1004", value=summary_expr, conditions=[]),
        parameters=parameters,
    )
    strategy = PairwiseStrategy(echo_input_correspondence(Mock()), Mock(), debug=False)

    relation = strategy._method_b_closure_relation_object_key(exact_case, summary_case)

    assert relation[0] == "method_b_closure_relation"
    assert ("kind", "one_sided_summary") in relation
    assert ("summary_side", "right") in relation
    assert ("exact_side", "left") in relation
    assert ("exact_terms", (("readonly_reduction_term", 0, 4), ("readonly_reduction_term", 4, 4))) in relation
    assert ("exact_constant_bias", 0) in relation


def test_method_b_covering_case_producer_records_only_covering_evidence():
    base = Expression.parameter("base", index=0, data_type="int *", size=8)
    exact_expr = Expression.binary_op(
        "INT_ADD",
        Expression.memory(base, size=4),
        Expression.memory(
            Expression.binary_op("INT_ADD", base, Expression.constant(4, size=8)),
            size=4,
        ),
    )
    summary_expr = _readonly_sum_expr(_readonly_loop_summary(start=0, step=1))
    parameters = [
        {"name": "base", "index": 0, "data_type": "int *", "size": 8},
        {"name": "count", "index": 1, "data_type": "int", "size": 4},
    ]
    exact_return = ReturnInfo(address="0x1000", value=exact_expr, conditions=[])
    summary_return = ReturnInfo(address="0x1004", value=summary_expr, conditions=[])
    exact_case = ReturnCase(0, [], exact_expr, exact_return, parameters=parameters)
    summary_case = ReturnCase(1, [], summary_expr, summary_return, parameters=parameters)
    analysis1 = FunctionReturnAnalysis(
        function_name="left",
        entry_point="0x1000",
        parameters=parameters,
        returns=[exact_return],
        return_type="int",
    )
    analysis2 = FunctionReturnAnalysis(
        function_name="right",
        entry_point="0x2000",
        parameters=parameters,
        returns=[summary_return],
        return_type="int",
    )
    strategy = PairwiseStrategy(echo_input_correspondence(Mock()), Mock(), debug=False)
    target = strategy._method_b_closure_object_target_key(
        base_ctx={"analysis1": analysis1, "analysis2": analysis2},
        case1=exact_case,
        case2=summary_case,
        pair_id="(0,1)",
    )
    reason = _typed_method_b_reason(target)

    strategy._record_completed_method_b_covering_case_proof_if_safe(
        reason,
        analysis1,
        exact_case,
        summary_case,
    )

    evidence = tuple(analysis1.completed_recovery_proof_evidence)
    assert len(evidence) == 1
    assert evidence[0]["proof_stage"] == "method_b_covering_case"
    assert evidence[0]["evidence_kind"] == "seed_compensation"
    assert evidence[0]["proof_content"]["term_sequence"] == "matched"
    assert evidence[0]["proof_content"]["exact_terms"] == (
        ("readonly_reduction_term", 0, 4),
        ("readonly_reduction_term", 4, 4),
    )
    assert strategy._method_b_closure_proof_is_complete(reason, analysis1, analysis2) is False


def test_method_b_guard_partition_producer_records_when_count_guard_is_proven():
    base = Expression.parameter("base", index=0, data_type="int *", size=8)
    count = Expression.parameter("count", index=1, data_type="int", size=4)
    count_is_two = Condition(
        Expression.binary_op("INT_EQUAL", count, Expression.constant(2, size=4)),
        False,
    )
    exact_expr = Expression.binary_op(
        "INT_ADD",
        Expression.memory(base, size=4),
        Expression.memory(
            Expression.binary_op("INT_ADD", base, Expression.constant(4, size=8)),
            size=4,
        ),
    )
    summary_expr = _readonly_sum_expr(_readonly_loop_summary(start=0, step=1))
    parameters = [
        {"name": "base", "index": 0, "data_type": "int *", "size": 8},
        {"name": "count", "index": 1, "data_type": "int", "size": 4},
    ]
    exact_return = ReturnInfo(address="0x1000", value=exact_expr, conditions=[count_is_two])
    summary_return = ReturnInfo(address="0x1004", value=summary_expr, conditions=[count_is_two])
    exact_case = ReturnCase(0, [count_is_two], exact_expr, exact_return, parameters=parameters)
    summary_case = ReturnCase(1, [count_is_two], summary_expr, summary_return, parameters=parameters)
    analysis1 = FunctionReturnAnalysis(
        function_name="left",
        entry_point="0x1000",
        parameters=parameters,
        returns=[exact_return],
        return_type="int",
    )
    analysis2 = FunctionReturnAnalysis(
        function_name="right",
        entry_point="0x2000",
        parameters=parameters,
        returns=[summary_return],
        return_type="int",
    )
    strategy = PairwiseStrategy(echo_input_correspondence(Mock()), Mock(), debug=False)
    target = strategy._method_b_closure_object_target_key(
        base_ctx={"analysis1": analysis1, "analysis2": analysis2},
        case1=exact_case,
        case2=summary_case,
        pair_id="(0,1)",
    )
    reason = _typed_method_b_reason(target)

    with comparison_of(analysis1, analysis2):
        strategy._record_completed_method_b_covering_case_proof_if_safe(
            reason,
            analysis1,
            exact_case,
            summary_case,
        )

        evidence = tuple(analysis1.completed_recovery_proof_evidence)
        assert [item["proof_stage"] for item in evidence] == [
            "method_b_covering_case",
            "method_b_guard_partition",
        ]
        assert evidence[1]["proof_content"]["guard_partition"] == "proven"
        assert evidence[1]["proof_content"]["partition_coverage_proof"] == "covered"
        assert strategy._method_b_closure_proof_is_complete(reason, analysis1, analysis2) is True

    # Issue #167: Method B の proof は比較の solver surface（relation が許可した書き換え）
    # から作るので、同じ analysis を別の relation で比べ直した比較では採用しない。
    widened = FunctionReturnAnalysis(
        function_name="left",
        entry_point="0x1000",
        parameters=[*parameters, {"name": "extra", "index": 2, "data_type": "int", "size": 4}],
        returns=[exact_return],
        return_type="int",
    )
    with comparison_of(widened, analysis2) as other_relation:
        assert {item["comparison_authority"] for item in evidence} != {other_relation.digest}
        assert strategy._method_b_closure_proof_is_complete(reason, analysis1, analysis2) is False
    assert strategy._method_b_closure_proof_is_complete(reason, analysis1, analysis2) is False


def test_method_b_guard_partition_producer_records_count_membership_when_range_is_proven():
    base = Expression.parameter("base", index=0, data_type="int *", size=8)
    count = Expression.parameter("count", index=1, data_type="int", size=4)
    count_gt_two = Condition(
        Expression.binary_op("INT_SLESS", Expression.constant(2, size=4), count),
        False,
    )
    count_lt_five = Condition(
        Expression.binary_op("INT_SLESS", count, Expression.constant(5, size=4)),
        False,
    )
    exact_expr = Expression.binary_op(
        "INT_ADD",
        Expression.memory(base, size=4),
        Expression.memory(
            Expression.binary_op("INT_ADD", base, Expression.constant(8, size=8)),
            size=4,
        ),
    )
    summary_expr = _readonly_sum_expr(_readonly_loop_summary(start=0, step=2))
    parameters = [
        {"name": "base", "index": 0, "data_type": "int *", "size": 8},
        {"name": "count", "index": 1, "data_type": "int", "size": 4},
    ]
    conditions = [count_gt_two, count_lt_five]
    exact_return = ReturnInfo(address="0x1000", value=exact_expr, conditions=conditions)
    summary_return = ReturnInfo(address="0x1004", value=summary_expr, conditions=conditions)
    exact_case = ReturnCase(0, conditions, exact_expr, exact_return, parameters=parameters)
    summary_case = ReturnCase(1, conditions, summary_expr, summary_return, parameters=parameters)
    analysis1 = FunctionReturnAnalysis(
        function_name="left",
        entry_point="0x1000",
        parameters=parameters,
        returns=[exact_return],
        return_type="int",
    )
    analysis2 = FunctionReturnAnalysis(
        function_name="right",
        entry_point="0x2000",
        parameters=parameters,
        returns=[summary_return],
        return_type="int",
    )
    strategy = PairwiseStrategy(echo_input_correspondence(Mock()), Mock(), debug=False)
    target = strategy._method_b_closure_object_target_key(
        base_ctx={"analysis1": analysis1, "analysis2": analysis2},
        case1=exact_case,
        case2=summary_case,
        pair_id="(0,1)",
    )
    reason = _typed_method_b_reason(target)

    with comparison_of(analysis1, analysis2):
        strategy._record_completed_method_b_covering_case_proof_if_safe(
            reason,
            analysis1,
            exact_case,
            summary_case,
        )

        evidence = tuple(analysis1.completed_recovery_proof_evidence)
        assert [item["proof_stage"] for item in evidence] == [
            "method_b_covering_case",
            "method_b_guard_partition",
        ]
        assert evidence[0]["proof_content"]["count_values"] == (3, 4)
        assert evidence[1]["proof_content"]["count_values"] == (3, 4)
        assert evidence[1]["proof_content"]["guard_evidence"] == "reduction_count_membership_implication"
        assert strategy._method_b_closure_proof_is_complete(reason, analysis1, analysis2) is True


def test_method_b_guard_partition_producer_rejects_open_count_range():
    base = Expression.parameter("base", index=0, data_type="int *", size=8)
    count = Expression.parameter("count", index=1, data_type="int", size=4)
    count_gt_two = Condition(
        Expression.binary_op("INT_SLESS", Expression.constant(2, size=4), count),
        False,
    )
    exact_expr = Expression.binary_op(
        "INT_ADD",
        Expression.memory(base, size=4),
        Expression.memory(
            Expression.binary_op("INT_ADD", base, Expression.constant(8, size=8)),
            size=4,
        ),
    )
    summary_expr = _readonly_sum_expr(_readonly_loop_summary(start=0, step=2))
    parameters = [
        {"name": "base", "index": 0, "data_type": "int *", "size": 8},
        {"name": "count", "index": 1, "data_type": "int", "size": 4},
    ]
    exact_return = ReturnInfo(address="0x1000", value=exact_expr, conditions=[count_gt_two])
    summary_return = ReturnInfo(address="0x1004", value=summary_expr, conditions=[count_gt_two])
    exact_case = ReturnCase(0, [count_gt_two], exact_expr, exact_return, parameters=parameters)
    summary_case = ReturnCase(1, [count_gt_two], summary_expr, summary_return, parameters=parameters)
    analysis1 = FunctionReturnAnalysis(
        function_name="left",
        entry_point="0x1000",
        parameters=parameters,
        returns=[exact_return],
        return_type="int",
    )
    analysis2 = FunctionReturnAnalysis(
        function_name="right",
        entry_point="0x2000",
        parameters=parameters,
        returns=[summary_return],
        return_type="int",
    )
    strategy = PairwiseStrategy(echo_input_correspondence(Mock()), Mock(), debug=False)
    target = strategy._method_b_closure_object_target_key(
        base_ctx={"analysis1": analysis1, "analysis2": analysis2},
        case1=exact_case,
        case2=summary_case,
        pair_id="(0,1)",
    )
    reason = _typed_method_b_reason(target)

    strategy._record_completed_method_b_covering_case_proof_if_safe(
        reason,
        analysis1,
        exact_case,
        summary_case,
    )

    evidence = tuple(analysis1.completed_recovery_proof_evidence)
    assert [item["proof_stage"] for item in evidence] == ["method_b_covering_case"]
    assert evidence[0]["proof_content"]["count_values"] == (3, 4)
    assert strategy._method_b_closure_proof_is_complete(reason, analysis1, analysis2) is False


def test_method_b_covering_case_producer_rejects_term_sequence_mismatch():
    base = Expression.parameter("base", index=0, data_type="int *", size=8)
    exact_expr = Expression.binary_op(
        "INT_ADD",
        Expression.memory(base, size=4),
        Expression.memory(
            Expression.binary_op("INT_ADD", base, Expression.constant(4, size=8)),
            size=4,
        ),
    )
    summary_expr = _readonly_sum_expr(_readonly_loop_summary(start=0, step=2))
    parameters = [
        {"name": "base", "index": 0, "data_type": "int *", "size": 8},
        {"name": "count", "index": 1, "data_type": "int", "size": 4},
    ]
    exact_return = ReturnInfo(address="0x1000", value=exact_expr, conditions=[])
    summary_return = ReturnInfo(address="0x1004", value=summary_expr, conditions=[])
    exact_case = ReturnCase(0, [], exact_expr, exact_return, parameters=parameters)
    summary_case = ReturnCase(1, [], summary_expr, summary_return, parameters=parameters)
    analysis1 = FunctionReturnAnalysis(
        function_name="left",
        entry_point="0x1000",
        parameters=parameters,
        returns=[exact_return],
        return_type="int",
    )
    analysis2 = FunctionReturnAnalysis(
        function_name="right",
        entry_point="0x2000",
        parameters=parameters,
        returns=[summary_return],
        return_type="int",
    )
    strategy = PairwiseStrategy(echo_input_correspondence(Mock()), Mock(), debug=False)
    target = strategy._method_b_closure_object_target_key(
        base_ctx={"analysis1": analysis1, "analysis2": analysis2},
        case1=exact_case,
        case2=summary_case,
        pair_id="(0,1)",
    )
    reason = _typed_method_b_reason(target)

    strategy._record_completed_method_b_covering_case_proof_if_safe(
        reason,
        analysis1,
        exact_case,
        summary_case,
    )

    assert analysis1.completed_recovery_proof_evidence == ()


def test_pairwise_parameter_identity_key_refuses_descriptor_name_fallback():
    strategy = PairwiseStrategy(echo_input_correspondence(Mock()), Mock(), debug=False)
    name_only_expr = Expression.parameter("count", data_type="int", size=4)
    indexed_expr = Expression.parameter("count", index=1, data_type="int", size=4)
    storage = StorageInfo(
        is_register=True,
        space_name="register",
        register_name="a1",
        base_register_name="a1",
        size=4,
        size_bits=32,
    )
    storage_expr = Expression.parameter("stale_count", data_type="int", size=4, storage_info=storage)
    parameters = [{"name": "count", "size": 4, "data_type": "int", "index": 1}]

    assert strategy._parameter_object_identity_key(name_only_expr, parameters) is None
    assert strategy._parameter_object_identity_key(indexed_expr, parameters) == ("parameter_index", 1, 32)
    assert strategy._parameter_object_identity_key(storage_expr, parameters) == (
        "parameter_storage",
        storage.storage_identity_key(),
        32,
    )


def test_pairwise_condition_symbols_do_not_alias_name_only_parameters():
    strategy = PairwiseStrategy(echo_input_correspondence(Mock()), Mock(), debug=False)
    left_count = Expression.parameter("count", data_type="int", size=4)
    right_count = Expression.parameter("count", data_type="int", size=4)
    conditions = [
        Condition(
            Expression.binary_op("INT_EQUAL", left_count, Expression.constant(1, size=4)),
            False,
        ),
        Condition(
            Expression.binary_op("INT_EQUAL", right_count, Expression.constant(2, size=4)),
            False,
        ),
    ]

    rewritten = strategy._conditions_with_object_identity_parameter_symbols(
        conditions,
        [{"name": "count", "size": 4, "data_type": "int", "index": 1}],
    )

    left_symbol = rewritten[0].expression.operands[0].name
    right_symbol = rewritten[1].expression.operands[0].name
    assert left_symbol != right_symbol
    assert ConditionSMTOracle.conjunction_is_unsat(rewritten) is not True


def test_pairwise_condition_symbols_preserve_low_subpiece_parameter_identity():
    strategy = PairwiseStrategy(echo_input_correspondence(Mock()), Mock(), debug=False)
    count = Expression.parameter(
        "param_2",
        index=1,
        size=4,
        runtime_ref=LocationBaseRef.parameter("param_2", index=1),
    )
    low = Expression.binary_op(
        "SUBPIECE",
        count,
        Expression.constant(0, size=4),
    ).clone_with(size=4)
    widened = Expression.unary_op("INT_SEXT", low).clone_with(size=8)
    conditions = [
        Condition(
            Expression.binary_op("INT_EQUAL", count, Expression.constant(2, size=4)),
            False,
        ),
        Condition(
            Expression.binary_op("INT_SLESS", Expression.constant(2, size=8), widened),
            False,
        ),
    ]

    rewritten = strategy._conditions_with_object_identity_parameter_symbols(
        conditions,
        [{"name": "param_2", "size": 4, "data_type": "int", "index": 1}],
    )

    assert ConditionSMTOracle.conjunction_is_unsat(rewritten) is True


def test_pairwise_materialized_readonly_term_refuses_unresolved_pointer_base(monkeypatch):
    strategy = PairwiseStrategy(echo_input_correspondence(Mock()), Mock(), debug=False)
    unresolved_base = LocationBaseRef.parameter("base")
    load_expr = Expression.memory(
        Expression.parameter("base", data_type="int *", size=8),
        size=4,
    )

    monkeypatch.setattr(
        pairwise_module,
        "canonicalize_location",
        lambda _addr_expr, _parameters, size=4: CanonicalLocation(
            base_ref=unresolved_base,
            offset=0,
            size=size,
        ),
    )

    descriptor = strategy._extract_readonly_reduction_term_descriptor(
        load_expr,
        [{"name": "base", "size": 8, "data_type": "int *"}],
        unresolved_base,
    )

    assert unresolved_base.semantic_key() is None
    assert descriptor is None


def test_pairwise_materialized_readonly_term_accepts_indexed_pointer_base(monkeypatch):
    strategy = PairwiseStrategy(echo_input_correspondence(Mock()), Mock(), debug=False)
    indexed_base = LocationBaseRef.parameter("base", index=0)
    load_expr = Expression.memory(
        Expression.parameter("base", index=0, data_type="int *", size=8),
        size=4,
    )

    monkeypatch.setattr(
        pairwise_module,
        "canonicalize_location",
        lambda _addr_expr, _parameters, size=4: CanonicalLocation(
            base_ref=indexed_base,
            offset=0,
            size=size,
        ),
    )

    descriptor = strategy._extract_readonly_reduction_term_descriptor(
        load_expr,
        [{"name": "base", "size": 8, "data_type": "int *", "index": 0}],
        indexed_base,
    )

    assert indexed_base.semantic_key() == ("parameter", 0)
    assert descriptor == ReadonlyReductionTermRef(byte_offset=0, access_size=4)


def test_reduction_accumulator_proof_lowers_to_readonly_reduction_ref_object_centrically():
    count_expr = Expression.parameter("count", index=1, data_type="int", size=4)
    proof = ReductionAccumulatorProof(
        reduction_kind="memory_sum",
        pointer_base_ref=LocationBaseRef.parameter("base", index=0),
        count_parameter_name="count",
        count_parameter_index=1,
        limit_expr=count_expr,
        result_size=4,
        stride=4,
        element_size=4,
        start_offset=12,
        start_index=3,
        index_step=1,
        index_scale=4,
        seed_terms=(
            ReadonlyReductionTermRef(byte_offset=0, access_size=4),
            ReadonlyReductionTermRef(byte_offset=4, access_size=4),
            ReadonlyReductionTermRef(byte_offset=8, access_size=4),
        ),
    ).with_runtime_evidence(
        limit_expr=count_expr,
        result_size=4,
        loop_body_witnesses=(
            ReadonlyReductionWitness(
                exact_count=4,
                terms=(ReadonlyReductionTermRef(byte_offset=12, access_size=4),),
            ),
        ),
        exact_return_witnesses=(
            ReadonlyReductionWitness(
                exact_count=3,
                terms=(
                    ReadonlyReductionTermRef(byte_offset=0, access_size=4),
                    ReadonlyReductionTermRef(byte_offset=4, access_size=4),
                    ReadonlyReductionTermRef(byte_offset=8, access_size=4),
                ),
            ),
        ),
        guard_constraints=(),
        signed_counter=True,
    )

    lowering = proof.lower_to_readonly_reduction()

    assert isinstance(lowering, ReadonlyReductionLowering)
    ref = lowering.readonly_reduction
    alias_ref = proof.lower_to_readonly_reduction_ref()
    assert alias_ref is not None
    assert alias_ref.stable_key() == ref.stable_key()
    assert lowering.loop_summary == ref.loop_summary
    assert lowering.stable_key() is not None
    assert ref is not None
    assert ref.accumulator_proof == proof
    assert ref.loop_summary is not None
    assert proof.full_terms_for_count_value(1) == (
        ReadonlyReductionTermRef(byte_offset=0, access_size=4),
    )
    assert proof.full_terms_for_count_value(2) == (
        ReadonlyReductionTermRef(byte_offset=0, access_size=4),
        ReadonlyReductionTermRef(byte_offset=4, access_size=4),
    )
    assert proof.full_terms_for_count_value(4) == (
        ReadonlyReductionTermRef(byte_offset=0, access_size=4),
        ReadonlyReductionTermRef(byte_offset=4, access_size=4),
        ReadonlyReductionTermRef(byte_offset=8, access_size=4),
        ReadonlyReductionTermRef(byte_offset=12, access_size=4),
    )
    assert loop_summary_method_b_key(ref.loop_summary) == loop_summary_method_b_key(_readonly_loop_summary(start=0))


def test_reduction_accumulator_proof_lowers_constant_bias_object_centrically():
    count_expr = Expression.parameter("count", index=1, data_type="int", size=4)
    proof = ReductionAccumulatorProof(
        reduction_kind="memory_sum",
        pointer_base_ref=LocationBaseRef.parameter("base", index=0),
        count_parameter_name="count",
        count_parameter_index=1,
        limit_expr=count_expr,
        result_size=4,
        stride=4,
        element_size=4,
        constant_bias=1,
    )
    unbiased = ReductionAccumulatorProof(
        reduction_kind="memory_sum",
        pointer_base_ref=LocationBaseRef.parameter("base", index=0),
        count_parameter_name="count",
        count_parameter_index=1,
        limit_expr=count_expr,
        result_size=4,
        stride=4,
        element_size=4,
    )
    biased_ref = proof.lower_to_readonly_reduction_ref()
    unbiased_ref = unbiased.lower_to_readonly_reduction_ref()

    assert biased_ref is not None
    assert unbiased_ref is not None
    assert biased_ref.constant_bias == 1
    assert biased_ref.loop_summary is not None
    assert biased_ref.loop_summary.constant_bias == 1
    assert biased_ref.semantic_key() != unbiased_ref.semantic_key()
    assert loop_summary_method_b_key(biased_ref.loop_summary) != loop_summary_method_b_key(unbiased_ref.loop_summary)


def test_readonly_constant_bias_is_width_normalized_object_centrically():
    count_expr = Expression.parameter("count", index=1, data_type="int", size=4)
    negative_bias = ReductionAccumulatorProof(
        reduction_kind="memory_sum",
        pointer_base_ref=LocationBaseRef.parameter("base", index=0),
        count_parameter_name="count",
        count_parameter_index=1,
        limit_expr=count_expr,
        result_size=4,
        stride=4,
        element_size=4,
        constant_bias=-1,
    ).lower_to_readonly_reduction_ref()
    unsigned_bias = ReductionAccumulatorProof(
        reduction_kind="memory_sum",
        pointer_base_ref=LocationBaseRef.parameter("base", index=0),
        count_parameter_name="count",
        count_parameter_index=1,
        limit_expr=count_expr,
        result_size=4,
        stride=4,
        element_size=4,
        constant_bias=0xFFFFFFFF,
    ).lower_to_readonly_reduction_ref()
    wrapped_zero = ReductionAccumulatorProof(
        reduction_kind="memory_sum",
        pointer_base_ref=LocationBaseRef.parameter("base", index=0),
        count_parameter_name="count",
        count_parameter_index=1,
        limit_expr=count_expr,
        result_size=4,
        stride=4,
        element_size=4,
        constant_bias=1 << 32,
    ).lower_to_readonly_reduction_ref()
    zero_bias = ReductionAccumulatorProof(
        reduction_kind="memory_sum",
        pointer_base_ref=LocationBaseRef.parameter("base", index=0),
        count_parameter_name="count",
        count_parameter_index=1,
        limit_expr=count_expr,
        result_size=4,
        stride=4,
        element_size=4,
    ).lower_to_readonly_reduction_ref()

    assert negative_bias is not None
    assert unsigned_bias is not None
    assert wrapped_zero is not None
    assert zero_bias is not None
    assert negative_bias.constant_bias == 0xFFFFFFFF
    assert negative_bias.semantic_key() == unsigned_bias.semantic_key()
    assert wrapped_zero.semantic_key() == zero_bias.semantic_key()


def test_readonly_ref_rejects_ref_level_bias_mismatch_with_loop_summary():
    count_expr = Expression.parameter("count", index=1, data_type="int", size=4)
    loop_summary = LoopSummaryRef(
        start_expr=Expression.constant(0, size=4),
        limit_expr=count_expr,
        step_expr=Expression.constant(1, size=4),
        term_descriptor=LoopTermDescriptorRef(
            kind="memory_load",
            reduction_kind="sum",
            location_base_ref=LocationBaseRef.parameter("base", index=0),
            start_offset=0,
            stride=4,
            element_size=4,
            result_size=4,
        ),
    )

    try:
        ReadonlyReductionRef(
            reduction_kind="memory_sum",
            pointer_base_ref=LocationBaseRef.parameter("base", index=0),
            count_parameter_name="count",
            count_parameter_index=1,
            stride=4,
            element_size=4,
            result_size=4,
            loop_summary=loop_summary,
            constant_bias=5,
        )
    except ValueError:
        pass
    else:
        raise AssertionError("bias mismatch must be rejected")


def test_readonly_ref_rejects_accumulator_proof_bias_mismatch():
    count_expr = Expression.parameter("count", index=1, data_type="int", size=4)
    loop_summary = LoopSummaryRef(
        start_expr=Expression.constant(0, size=4),
        limit_expr=count_expr,
        step_expr=Expression.constant(1, size=4),
        term_descriptor=LoopTermDescriptorRef(
            kind="memory_load",
            reduction_kind="sum",
            location_base_ref=LocationBaseRef.parameter("base", index=0),
            start_offset=0,
            stride=4,
            element_size=4,
            result_size=4,
        ),
        constant_bias=5,
    )
    proof = ReductionAccumulatorProof(
        reduction_kind="memory_sum",
        pointer_base_ref=LocationBaseRef.parameter("base", index=0),
        count_parameter_name="count",
        count_parameter_index=1,
        limit_expr=count_expr,
        result_size=4,
        stride=4,
        element_size=4,
        constant_bias=0,
    )

    try:
        ReadonlyReductionRef(
            reduction_kind="memory_sum",
            pointer_base_ref=LocationBaseRef.parameter("base", index=0),
            count_parameter_name="count",
            count_parameter_index=1,
            stride=4,
            element_size=4,
            result_size=4,
            loop_summary=loop_summary,
            accumulator_proof=proof,
            constant_bias=5,
        )
    except ValueError:
        pass
    else:
        raise AssertionError("proof/ref bias mismatch must be rejected")


def test_readonly_ref_rejects_result_width_mismatch_before_bias_sync():
    count_expr = Expression.parameter("count", index=1, data_type="int", size=4)
    loop_summary = LoopSummaryRef(
        start_expr=Expression.constant(0, size=4),
        limit_expr=count_expr,
        step_expr=Expression.constant(1, size=4),
        term_descriptor=LoopTermDescriptorRef(
            kind="memory_load",
            reduction_kind="sum",
            location_base_ref=LocationBaseRef.parameter("base", index=0),
            start_offset=0,
            stride=4,
            element_size=4,
            result_size=8,
        ),
        constant_bias=1 << 32,
    )
    proof = ReductionAccumulatorProof(
        reduction_kind="memory_sum",
        pointer_base_ref=LocationBaseRef.parameter("base", index=0),
        count_parameter_name="count",
        count_parameter_index=1,
        limit_expr=count_expr,
        result_size=4,
        stride=4,
        element_size=4,
        constant_bias=0,
    )

    try:
        ReadonlyReductionRef(
            reduction_kind="memory_sum",
            pointer_base_ref=LocationBaseRef.parameter("base", index=0),
            count_parameter_name="count",
            count_parameter_index=1,
            stride=4,
            element_size=4,
            result_size=4,
            loop_summary=loop_summary,
            accumulator_proof=proof,
            constant_bias=0,
        )
    except ValueError:
        pass
    else:
        raise AssertionError("result-width mismatch must be rejected before bias normalization")


def test_loop_summary_rejects_widthless_nonzero_bias_before_normalization():
    count_expr = Expression.parameter("count", index=1, data_type="int", size=4)

    try:
        LoopSummaryRef(
            start_expr=Expression.constant(0, size=4),
            limit_expr=count_expr,
            step_expr=Expression.constant(1, size=4),
            term_descriptor=LoopTermDescriptorRef(
                kind="memory_load",
                reduction_kind="sum",
                location_base_ref=LocationBaseRef.parameter("base", index=0),
                start_offset=0,
                stride=4,
                element_size=4,
                result_size=0,
            ),
            constant_bias=256,
        )
    except ValueError:
        pass
    else:
        raise AssertionError("widthless nonzero bias must not be normalized away")


def test_readonly_bias_to_dict_uses_normalized_bias_at_each_layer():
    count_expr = Expression.parameter("count", index=1, data_type="int", size=4)
    proof = ReductionAccumulatorProof(
        reduction_kind="memory_sum",
        pointer_base_ref=LocationBaseRef.parameter("base", index=0),
        count_parameter_name="count",
        count_parameter_index=1,
        limit_expr=count_expr,
        result_size=4,
        stride=4,
        element_size=4,
        constant_bias=-1,
    )
    lowering = proof.lower_to_readonly_reduction()

    assert lowering is not None
    assert proof.to_dict()["constant_bias"] == 0xFFFFFFFF
    assert lowering.loop_summary.to_dict()["constant_bias"] == 0xFFFFFFFF
    assert lowering.readonly_reduction.to_dict()["constant_bias"] == 0xFFFFFFFF
    assert lowering.to_dict()["proof"]["constant_bias"] == 0xFFFFFFFF
    assert lowering.to_dict()["readonly_reduction"]["constant_bias"] == 0xFFFFFFFF


def test_reduction_accumulator_proof_with_side_effects_does_not_lower_to_readonly_sum():
    count_expr = Expression.parameter("count", index=1, data_type="int", size=4)
    proof = ReductionAccumulatorProof(
        reduction_kind="memory_sum",
        pointer_base_ref=LocationBaseRef.parameter("base", index=0),
        count_parameter_name="count",
        count_parameter_index=1,
        limit_expr=count_expr,
        result_size=4,
        stride=4,
        element_size=4,
        side_effect_profile=LoopSideEffectProfileRef(
            profile="effect_aware",
            memory_reads=True,
            memory_writes=True,
        ),
    )

    assert proof.lower_to_loop_summary_ref() is None
    assert proof.lower_to_readonly_reduction_ref() is None


def test_reduction_accumulator_proof_preserves_independent_start_offset_in_loop_summary():
    count_expr = Expression.parameter("count", index=1, data_type="int", size=4)
    base_ref = LocationBaseRef.parameter("base", index=0)
    shifted = ReductionAccumulatorProof(
        reduction_kind="memory_sum",
        pointer_base_ref=base_ref,
        count_parameter_name="count",
        count_parameter_index=1,
        limit_expr=count_expr,
        result_size=4,
        stride=4,
        element_size=4,
        start_offset=4,
        start_index=0,
        index_step=1,
        index_scale=4,
    ).lower_to_loop_summary_ref()
    unshifted = ReductionAccumulatorProof(
        reduction_kind="memory_sum",
        pointer_base_ref=base_ref,
        count_parameter_name="count",
        count_parameter_index=1,
        limit_expr=count_expr,
        result_size=4,
        stride=4,
        element_size=4,
        start_offset=0,
        start_index=0,
        index_step=1,
        index_scale=4,
    ).lower_to_loop_summary_ref()

    assert shifted is not None
    assert unshifted is not None
    assert shifted.term_descriptor.start_offset == 4
    assert loop_summary_method_b_key(shifted) != loop_summary_method_b_key(unshifted)


def test_reduction_accumulator_proof_materializes_scalar_lane_terms():
    count_expr = Expression.parameter("count", index=1, data_type="int", size=4)
    proof = ReductionAccumulatorProof(
        reduction_kind="memory_sum",
        pointer_base_ref=LocationBaseRef.parameter("base", index=0),
        count_parameter_name="count",
        count_parameter_index=1,
        limit_expr=count_expr,
        result_size=4,
        stride=16,
        element_size=8,
        start_offset=0,
        start_index=0,
        index_step=1,
        index_scale=16,
        lane_terms=((0, 4), (4, 4), (8, 4), (12, 4)),
        loop_body_witnesses=(
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
        ),
    )

    assert proof.loop_var_unit() == "scalar_element_index"
    assert proof.loop_body_terms_for_count_value(2) == (
        ReadonlyReductionTermRef(byte_offset=0, access_size=4),
        ReadonlyReductionTermRef(byte_offset=4, access_size=4),
    )
    assert proof.loop_body_terms_for_count_value(5) == (
        ReadonlyReductionTermRef(byte_offset=0, access_size=4),
        ReadonlyReductionTermRef(byte_offset=4, access_size=4),
        ReadonlyReductionTermRef(byte_offset=8, access_size=4),
        ReadonlyReductionTermRef(byte_offset=12, access_size=4),
        ReadonlyReductionTermRef(byte_offset=16, access_size=4),
    )


def test_reduction_accumulator_proof_materializes_shifted_scalar_lane_terms():
    count_expr = Expression.parameter("count", index=1, data_type="int", size=4)
    proof = ReductionAccumulatorProof(
        reduction_kind="memory_sum",
        pointer_base_ref=LocationBaseRef.parameter("base", index=0),
        count_parameter_name="count",
        count_parameter_index=1,
        limit_expr=count_expr,
        result_size=4,
        stride=8,
        element_size=8,
        start_offset=4,
        start_index=0,
        index_step=1,
        index_scale=8,
        lane_terms=((4, 4), (8, 4)),
        loop_body_witnesses=(
            ReadonlyReductionWitness(
                exact_count=1,
                terms=(ReadonlyReductionTermRef(byte_offset=4, access_size=4),),
            ),
        ),
    )

    assert proof.lane_terms == ((0, 4), (4, 4))
    assert proof.loop_var_unit() == "scalar_element_index"
    assert proof.loop_body_terms_for_count_value(3) == (
        ReadonlyReductionTermRef(byte_offset=4, access_size=4),
        ReadonlyReductionTermRef(byte_offset=8, access_size=4),
        ReadonlyReductionTermRef(byte_offset=12, access_size=4),
    )


def test_reduction_accumulator_proof_infers_shifted_lane_terms_from_witnesses():
    count_expr = Expression.parameter("count", index=1, data_type="int", size=4)
    prefix_only = ReductionAccumulatorProof(
        reduction_kind="memory_sum",
        pointer_base_ref=LocationBaseRef.parameter("base", index=0),
        count_parameter_name="count",
        count_parameter_index=1,
        limit_expr=count_expr,
        result_size=4,
        stride=8,
        element_size=8,
        start_offset=4,
        start_index=0,
        index_step=1,
        index_scale=8,
    ).with_runtime_evidence(
        limit_expr=count_expr,
        result_size=4,
        loop_body_witnesses=(
            ReadonlyReductionWitness(
                exact_count=1,
                terms=(ReadonlyReductionTermRef(byte_offset=4, access_size=4),),
            ),
        ),
        exact_return_witnesses=(),
        guard_constraints=(),
        signed_counter=True,
    )
    full_prefix = ReductionAccumulatorProof(
        reduction_kind="memory_sum",
        pointer_base_ref=LocationBaseRef.parameter("base", index=0),
        count_parameter_name="count",
        count_parameter_index=1,
        limit_expr=count_expr,
        result_size=4,
        stride=8,
        element_size=8,
        start_offset=4,
        start_index=0,
        index_step=1,
        index_scale=8,
    ).with_runtime_evidence(
        limit_expr=count_expr,
        result_size=4,
        loop_body_witnesses=(
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
        ),
        exact_return_witnesses=(),
        guard_constraints=(),
        signed_counter=True,
    )

    assert prefix_only.lane_terms == ()
    assert prefix_only.loop_var_unit() == "element_index"
    assert full_prefix.lane_terms == ((0, 4), (4, 4))
    assert full_prefix.loop_var_unit() == "scalar_element_index"


def test_reduction_accumulator_proof_materializes_scalar_lane_terms_for_object_proof():
    count_expr = Expression.parameter("count", index=1, data_type="int", size=4)
    proof = ReductionAccumulatorProof(
        reduction_kind="memory_sum",
        pointer_base_ref=LocationBaseRef.parameter("base", index=0),
        count_parameter_name="count",
        count_parameter_index=1,
        limit_expr=count_expr,
        result_size=4,
        stride=16,
        element_size=8,
        start_offset=0,
        start_index=0,
        index_step=1,
        index_scale=16,
        lane_terms=((0, 4), (4, 4), (8, 4), (12, 4)),
    )

    assert proof.loop_var_unit() == "element_index"
    assert proof.loop_body_terms_for_count_value(2) == (
        ReadonlyReductionTermRef(byte_offset=0, access_size=4),
        ReadonlyReductionTermRef(byte_offset=4, access_size=4),
    )


def test_reduction_accumulator_proof_full_terms_materialize_seed_term_count_prefix():
    count_expr = Expression.parameter("count", index=1, data_type="int", size=4)
    proof = ReductionAccumulatorProof(
        reduction_kind="memory_sum",
        pointer_base_ref=LocationBaseRef.parameter("base", index=0),
        count_parameter_name="count",
        count_parameter_index=1,
        limit_expr=count_expr,
        result_size=4,
        stride=4,
        element_size=4,
        start_offset=12,
        start_index=3,
        index_step=1,
        index_scale=4,
        seed_term_count=3,
    )

    assert proof.seed_terms_for_count_value(2) == (
        ReadonlyReductionTermRef(byte_offset=0, access_size=4),
        ReadonlyReductionTermRef(byte_offset=4, access_size=4),
    )
    assert proof.seed_terms_for_count_value(3) == ()
    assert proof.full_terms_for_count_value(3) == (
        ReadonlyReductionTermRef(byte_offset=0, access_size=4),
        ReadonlyReductionTermRef(byte_offset=4, access_size=4),
        ReadonlyReductionTermRef(byte_offset=8, access_size=4),
    )
    assert proof.full_terms_for_count_value(4) == (
        ReadonlyReductionTermRef(byte_offset=0, access_size=4),
        ReadonlyReductionTermRef(byte_offset=4, access_size=4),
        ReadonlyReductionTermRef(byte_offset=8, access_size=4),
        ReadonlyReductionTermRef(byte_offset=12, access_size=4),
    )


def test_reduction_accumulator_proof_completes_seed_prefix_from_exact_witnesses():
    count_expr = Expression.parameter("count", index=1, data_type="int", size=4)
    proof = ReductionAccumulatorProof(
        reduction_kind="memory_sum",
        pointer_base_ref=LocationBaseRef.parameter("base", index=0),
        count_parameter_name="count",
        count_parameter_index=1,
        limit_expr=count_expr,
        result_size=4,
        stride=16,
        element_size=4,
        start_offset=12,
        start_index=0,
        index_step=1,
        index_scale=16,
        lane_terms=((0, 4), (4, 4), (8, 4), (12, 4)),
    ).with_runtime_evidence(
        limit_expr=count_expr,
        result_size=4,
        loop_body_witnesses=(),
        exact_return_witnesses=(
            ReadonlyReductionWitness(exact_count=1, terms=(ReadonlyReductionTermRef(byte_offset=0, access_size=4),)),
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
        ),
        guard_constraints=(),
        signed_counter=True,
    )

    assert proof.start_index == 3
    assert proof.seed_term_count is None
    assert proof.seed_terms == (
        ReadonlyReductionTermRef(byte_offset=0, access_size=4),
        ReadonlyReductionTermRef(byte_offset=4, access_size=4),
        ReadonlyReductionTermRef(byte_offset=8, access_size=4),
    )
    assert proof.full_terms_for_count_value(4) == (
        ReadonlyReductionTermRef(byte_offset=0, access_size=4),
        ReadonlyReductionTermRef(byte_offset=4, access_size=4),
        ReadonlyReductionTermRef(byte_offset=8, access_size=4),
        ReadonlyReductionTermRef(byte_offset=12, access_size=4),
    )


def test_readonly_reduction_semantic_key_scalarizes_proof_backed_vector_summary():
    count_expr = Expression.parameter("count", index=1, data_type="int", size=4)
    scalar_proof = ReductionAccumulatorProof(
        reduction_kind="memory_sum",
        pointer_base_ref=LocationBaseRef.parameter("base", index=0),
        count_parameter_name="count",
        count_parameter_index=1,
        limit_expr=count_expr,
        result_size=4,
        stride=4,
        element_size=4,
        start_offset=0,
        start_index=0,
        index_step=1,
        index_scale=4,
    ).with_runtime_evidence(
        limit_expr=count_expr,
        result_size=4,
        loop_body_witnesses=(),
        exact_return_witnesses=(),
        guard_constraints=(),
        signed_counter=True,
    )
    vector_proof = ReductionAccumulatorProof(
        reduction_kind="memory_sum",
        pointer_base_ref=LocationBaseRef.parameter("base", index=0),
        count_parameter_name="count",
        count_parameter_index=1,
        limit_expr=count_expr,
        result_size=4,
        stride=16,
        element_size=8,
        start_offset=0,
        start_index=0,
        index_step=1,
        index_scale=16,
        lane_terms=((0, 4), (4, 4), (8, 4), (12, 4)),
    ).with_runtime_evidence(
        limit_expr=count_expr,
        result_size=4,
        loop_body_witnesses=(),
        exact_return_witnesses=(),
        guard_constraints=(),
        signed_counter=True,
    )

    scalar_ref = scalar_proof.lower_to_readonly_reduction_ref()
    vector_ref = vector_proof.lower_to_readonly_reduction_ref()

    assert scalar_ref is not None
    assert vector_ref is not None
    assert scalar_ref.semantic_key() == vector_ref.semantic_key()


def _counted_loop_expr(loop_summary: LoopSummaryRef) -> Expression:
    return Expression.intrinsic(
        "COUNTED_LOOP_SUM",
        [Expression.constant(0), Expression.constant(0), Expression.parameter("n", size=4)],
        size=4,
        runtime_ref=CountedLoopSummaryRef(
            induction_step=1,
            result_size=4,
            signed_loop=True,
            residue_cases=((1, 0, 1, 0),),
            loop_summary=loop_summary,
        ),
        opcode=COUNTED_LOOP_SUM_OPCODE,
    )


def _return_case_for_expr(expr: Expression) -> ReturnCase:
    return ReturnCase(0, [], expr, ReturnInfo(address="0x1000", value=expr, conditions=[]))


def _analysis_with_return(function_name: str, value: Expression, conditions=()) -> FunctionReturnAnalysis:
    return FunctionReturnAnalysis(
        function_name=function_name,
        entry_point="0x1000",
        parameters=[
            {"name": "base", "index": 0, "data_type": "int *", "size": 8, "is_signed": False},
            {"name": "count", "index": 1, "data_type": "int", "size": 4, "is_signed": True},
        ],
        returns=[
            ReturnInfo(
                address="0x1000",
                value=value,
                conditions=list(conditions or ()),
            )
        ],
        return_type="int",
    )


def _pairwise_strategy_for_full_path() -> PairwiseStrategy:
    runner = ParallelSolverRunner(timeout=5)
    runner.run_sequential = Mock(wraps=runner.run_sequential)
    strategy = PairwiseStrategy(echo_input_correspondence(Mock()), runner, debug=False)
    strategy.formula_builder.build_base_context.return_value = {
        "header_lines": [],
        "params1": [],
        "params2": [],
        "extra_vars1": [],
        "extra_vars2": [],
        "constrained_fragments": [],
        "return_size1": 32,
        "return_size2": 32,
    }
    return strategy


def _nested_has_tag(value, tag):
    if isinstance(value, tuple):
        return (bool(value) and value[0] == tag) or any(_nested_has_tag(item, tag) for item in value)
    if isinstance(value, list):
        return any(_nested_has_tag(item, tag) for item in value)
    return False


def test_loop_summary_method_b_key_normalizes_seed_compensated_suffix():
    full = _readonly_loop_summary(start=0)
    suffix = _readonly_loop_summary(
        start=3,
        seed_terms=(
            ReadonlyReductionTermRef(byte_offset=0, access_size=4),
            ReadonlyReductionTermRef(byte_offset=4, access_size=4),
            ReadonlyReductionTermRef(byte_offset=8, access_size=4),
        ),
    )

    assert loop_summary_method_b_key(full) == loop_summary_method_b_key(suffix)
    result = compare_loop_summaries(full, suffix)
    assert result.status == "equivalent"
    assert result.is_equivalent() is True


def test_loop_summary_method_b_key_compensates_vector_lane_scalar_prefix_seed():
    full = _readonly_loop_summary(start=0)
    suffix = LoopSummaryRef(
        start_expr=Expression.constant(2, size=4),
        limit_expr=full.limit_expr,
        step_expr=full.step_expr,
        term_descriptor=LoopTermDescriptorRef(
            kind="memory_load",
            reduction_kind="sum",
            location_base_ref=LocationBaseRef.parameter("base", index=0),
            start_offset=0,
            stride=16,
            element_size=8,
            result_size=4,
            lane_terms=((0, 4), (4, 4), (8, 4), (12, 4)),
        ),
        seed_terms=(
            ReadonlyReductionTermRef(byte_offset=0, access_size=4),
            ReadonlyReductionTermRef(byte_offset=4, access_size=4),
        ),
        side_effect_profile=full.side_effect_profile,
        loop_var_unit="scalar_element_index",
    )

    assert loop_summary_method_b_key(full) == loop_summary_method_b_key(suffix)
    assert compare_loop_summaries(full, suffix).status == "equivalent"


def test_loop_summary_method_b_key_supports_seed_term_count_prefix():
    full = _readonly_loop_summary(start=0)
    suffix = LoopSummaryRef(
        start_expr=Expression.constant(3, size=4),
        limit_expr=full.limit_expr,
        step_expr=full.step_expr,
        term_descriptor=full.term_descriptor,
        seed_terms=(),
        seed_term_count=3,
        side_effect_profile=full.side_effect_profile,
        loop_var_unit=full.loop_var_unit,
    )

    assert loop_summary_method_b_key(full) == loop_summary_method_b_key(suffix)
    assert compare_loop_summaries(full, suffix).status == "equivalent"


def test_loop_summary_method_b_key_rejects_seed_term_count_mismatch():
    full = _readonly_loop_summary(start=0)
    suffix = _readonly_loop_summary(
        start=4,
        seed_terms=(
            ReadonlyReductionTermRef(byte_offset=0, access_size=4),
            ReadonlyReductionTermRef(byte_offset=4, access_size=4),
            ReadonlyReductionTermRef(byte_offset=8, access_size=4),
        ),
    )
    mismatch = LoopSummaryRef(
        start_expr=suffix.start_expr,
        limit_expr=suffix.limit_expr,
        step_expr=suffix.step_expr,
        term_descriptor=suffix.term_descriptor,
        seed_terms=(),
        seed_term_count=3,
        side_effect_profile=suffix.side_effect_profile,
        loop_var_unit=suffix.loop_var_unit,
    )

    assert loop_summary_method_b_key(full) != loop_summary_method_b_key(mismatch)
    result = compare_loop_summaries(full, mismatch)
    assert result.status == "unknown"
    assert result.is_equivalent() is None


def test_loop_summary_method_b_key_requires_seed_to_cover_omitted_prefix():
    full = _readonly_loop_summary(start=0)
    suffix_with_gap = _readonly_loop_summary(
        start=3,
        seed_terms=(
            ReadonlyReductionTermRef(byte_offset=0, access_size=4),
            ReadonlyReductionTermRef(byte_offset=4, access_size=4),
        ),
    )

    assert loop_summary_method_b_key(full) != loop_summary_method_b_key(suffix_with_gap)
    result = compare_loop_summaries(full, suffix_with_gap)
    assert result.status == "unknown"
    assert result.is_equivalent() is None


def test_loop_summary_method_b_key_ignores_witness_evidence_identity():
    left = _readonly_loop_summary(start=0)
    right = _readonly_loop_summary(start=0)
    right = LoopSummaryRef(
        start_expr=right.start_expr,
        limit_expr=right.limit_expr,
        step_expr=right.step_expr,
        term_descriptor=right.term_descriptor,
        seed_terms=right.seed_terms,
        witnesses=(object(),),
        side_effect_profile=right.side_effect_profile,
        guard_constraints=right.guard_constraints,
        cases=right.cases,
        loop_var_unit=right.loop_var_unit,
        source=right.source,
    )

    assert right.stable_key() is None
    assert loop_summary_method_b_key(left) == loop_summary_method_b_key(right)
    assert compare_loop_summaries(left, right).status == "equivalent"


def test_loop_summary_method_b_key_treats_guards_as_applicability_conditions():
    full = _readonly_loop_summary(start=0)
    suffix = _readonly_loop_summary(
        start=3,
        seed_terms=(
            ReadonlyReductionTermRef(byte_offset=0, access_size=4),
            ReadonlyReductionTermRef(byte_offset=4, access_size=4),
            ReadonlyReductionTermRef(byte_offset=8, access_size=4),
        ),
    )
    full = LoopSummaryRef(
        start_expr=full.start_expr,
        limit_expr=full.limit_expr,
        step_expr=full.step_expr,
        term_descriptor=full.term_descriptor,
        seed_terms=full.seed_terms,
        side_effect_profile=full.side_effect_profile,
        guard_constraints=("0 < count",),
        loop_var_unit=full.loop_var_unit,
    )
    suffix = LoopSummaryRef(
        start_expr=suffix.start_expr,
        limit_expr=suffix.limit_expr,
        step_expr=suffix.step_expr,
        term_descriptor=suffix.term_descriptor,
        seed_terms=suffix.seed_terms,
        side_effect_profile=suffix.side_effect_profile,
        guard_constraints=("3 < count",),
        loop_var_unit=suffix.loop_var_unit,
    )

    assert full.stable_key() != suffix.stable_key()
    assert loop_summary_method_b_key(full) == loop_summary_method_b_key(suffix)
    assert compare_loop_summaries(full, suffix).status == "equivalent"


def test_pairwise_readonly_runtime_values_use_method_b_seed_compensation():
    full = _readonly_sum_expr(_readonly_loop_summary(start=0))
    suffix = _readonly_sum_expr(
        _readonly_loop_summary(
            start=3,
            seed_terms=(
                ReadonlyReductionTermRef(byte_offset=0, access_size=4),
                ReadonlyReductionTermRef(byte_offset=4, access_size=4),
                ReadonlyReductionTermRef(byte_offset=8, access_size=4),
            ),
        )
    )
    strategy = PairwiseStrategy(None, None)

    assert strategy._intrinsic_runtime_values_equivalent(
        full,
        suffix,
        left_case=_return_case_for_expr(full),
        right_case=_return_case_for_expr(suffix),
    ) is True


def test_pairwise_full_path_prefers_method_b_loop_meaning_signature():
    full = _readonly_sum_expr(_readonly_loop_summary(start=0))
    suffix = _readonly_sum_expr(
        _readonly_loop_summary(
            start=3,
            seed_terms=(
                ReadonlyReductionTermRef(byte_offset=0, access_size=4),
                ReadonlyReductionTermRef(byte_offset=4, access_size=4),
                ReadonlyReductionTermRef(byte_offset=8, access_size=4),
            ),
        )
    )
    strategy = _pairwise_strategy_for_full_path()

    result = strategy.check(
        _analysis_with_return("full", full),
        _analysis_with_return("suffix", suffix),
    )

    assert result.is_equivalent is True
    assert result.total_pairs == 1
    assert result.unsat_pairs == 1
    assert result.unknown_pairs == 0
    strategy.solver_runner.run_sequential.assert_called()


def test_pairwise_full_path_falls_back_unknown_for_unproven_loop_summary():
    full = _readonly_sum_expr(_readonly_loop_summary(start=0))
    suffix_with_gap = _readonly_sum_expr(
        _readonly_loop_summary(
            start=3,
            seed_terms=(
                ReadonlyReductionTermRef(byte_offset=0, access_size=4),
                ReadonlyReductionTermRef(byte_offset=4, access_size=4),
            ),
        )
    )
    strategy = _pairwise_strategy_for_full_path()

    result = strategy.check(
        _analysis_with_return("full", full),
        _analysis_with_return("suffix_gap", suffix_with_gap),
    )

    assert result.is_equivalent is None
    assert result.total_pairs == 1
    assert result.unsat_pairs == 0
    assert result.unknown_pairs == 1
    strategy.solver_runner.run_sequential.assert_called()


def test_pairwise_method_b_unknown_carries_object_target_and_proof_ids():
    full = _readonly_sum_expr(_readonly_loop_summary(start=0))
    suffix_with_gap = _readonly_sum_expr(
        _readonly_loop_summary(
            start=3,
            seed_terms=(
                ReadonlyReductionTermRef(byte_offset=0, access_size=4),
                ReadonlyReductionTermRef(byte_offset=4, access_size=4),
            ),
        )
    )
    strategy = _pairwise_strategy_for_full_path()

    result = strategy.check(
        _analysis_with_return("full", full),
        _analysis_with_return("suffix_gap", suffix_with_gap),
    )

    assert result.is_equivalent is None
    assert len(result.unknown_reasons) == 1
    record = result.unknown_reasons[0]
    assert record.reason_id == "loop_summary_semantic_equality_unproven"
    assert record.object_target_key is not None
    assert record.object_target_key[0] == "method_b_closure"
    assert not _nested_has_tag(record.object_target_key, "reason")

    actions = build_unknown_recovery_actions(result.unknown_reasons)
    assert actions == ()


def test_monkeypatched_method_b_full_path_uses_canonical_solver_authority():
    base = Expression.parameter("base", index=0, data_type="int *", size=8)
    count = Expression.parameter("count", index=1, data_type="int", size=4)
    count_is_two = Condition(
        Expression.binary_op("INT_EQUAL", count, Expression.constant(2, size=4)),
        False,
    )
    exact = Expression.binary_op(
        "INT_ADD",
        Expression.memory(base, size=4),
        Expression.memory(
            Expression.binary_op("INT_ADD", base, Expression.constant(4, size=8)),
            size=4,
        ),
    )
    summary = _readonly_sum_expr(_readonly_loop_summary(start=0))
    exact_analysis = _analysis_with_return("exact", exact, conditions=[count_is_two])
    summary_analysis = _analysis_with_return("summary", summary, conditions=[count_is_two])
    strategy = _pairwise_strategy_for_full_path()
    strategy._collect_return_coverage_unsafety_reasons = Mock(return_value=[])
    strategy._cases_have_equivalent_runtime_reductions = Mock(return_value=False)
    strategy._case_pair_loop_summary_safe_fallback_reason = Mock(return_value="loop_summary_guard_mismatch")

    result = strategy.check(exact_analysis, summary_analysis)

    assert result.is_equivalent is True
    assert result.total_pairs == 1
    assert result.unsat_pairs == 1
    assert result.unknown_pairs == 0
    assert not exact_analysis.completed_recovery_proof_evidence
    strategy.solver_runner.run_sequential.assert_called()


def test_pairwise_full_path_recursively_falls_back_unknown_for_nested_unproven_loop_summary():
    full = Expression.binary_op(
        "INT_ADD",
        _readonly_sum_expr(_readonly_loop_summary(start=0)),
        Expression.parameter("bias", index=2, data_type="int", size=4),
    )
    suffix_with_gap = Expression.binary_op(
        "INT_ADD",
        _readonly_sum_expr(
            _readonly_loop_summary(
                start=3,
                seed_terms=(
                    ReadonlyReductionTermRef(byte_offset=0, access_size=4),
                    ReadonlyReductionTermRef(byte_offset=4, access_size=4),
                ),
            )
        ),
        Expression.parameter("bias", index=2, data_type="int", size=4),
    )
    strategy = _pairwise_strategy_for_full_path()

    result = strategy.check(
        _analysis_with_return("full", full),
        _analysis_with_return("suffix_gap", suffix_with_gap),
    )

    assert result.is_equivalent is None
    assert result.total_pairs == 1
    assert result.unsat_pairs == 0
    assert result.unknown_pairs == 1
    strategy.solver_runner.run_sequential.assert_called()


def test_pairwise_full_path_does_not_bypass_loop_guard_mismatch():
    count = Expression.parameter("count", index=1, data_type="int", size=4)
    full = _readonly_sum_expr(_readonly_loop_summary(start=0))
    suffix = _readonly_sum_expr(
        _readonly_loop_summary(
            start=3,
            seed_terms=(
                ReadonlyReductionTermRef(byte_offset=0, access_size=4),
                ReadonlyReductionTermRef(byte_offset=4, access_size=4),
                ReadonlyReductionTermRef(byte_offset=8, access_size=4),
            ),
        )
    )
    full_guard = Condition(Expression.binary_op("INT_SLESS", Expression.constant(0, size=4), count))
    suffix_guard = Condition(Expression.binary_op("INT_SLESS", Expression.constant(3, size=4), count))
    strategy = _pairwise_strategy_for_full_path()

    result = strategy.check(
        _analysis_with_return("full", full, conditions=[full_guard]),
        _analysis_with_return("suffix", suffix, conditions=[suffix_guard]),
    )

    assert result.is_equivalent is None
    assert result.total_pairs == 1
    assert result.unsat_pairs == 0
    assert result.unknown_pairs == 1
    strategy.solver_runner.run_sequential.assert_called()


def test_method_b_smt_identity_uses_seed_compensated_loop_summary():
    full = _readonly_sum_expr(_readonly_loop_summary(start=0))
    suffix = _readonly_sum_expr(
        _readonly_loop_summary(
            start=3,
            seed_terms=(
                ReadonlyReductionTermRef(byte_offset=0, access_size=4),
                ReadonlyReductionTermRef(byte_offset=4, access_size=4),
                ReadonlyReductionTermRef(byte_offset=8, access_size=4),
            ),
        )
    )
    suffix_with_gap = _readonly_sum_expr(
        _readonly_loop_summary(
            start=3,
            seed_terms=(
                ReadonlyReductionTermRef(byte_offset=0, access_size=4),
                ReadonlyReductionTermRef(byte_offset=4, access_size=4),
            ),
        )
    )

    assert _lowering_identity(full) == _lowering_identity(suffix)
    assert _lowering_identity(full) != _lowering_identity(suffix_with_gap)


def test_loop_side_effect_stable_key_distinguishes_function_context_descriptors():
    base_profile = LoopSideEffectProfileRef(
        profile="pure",
        context_memory_writes=True,
        context_descriptors=(
            LoopBodyEffectRef(
                kind="memory_write",
                source="function_effect_summary",
                scope="function",
                location="outside_a",
                value_expr=1,
            ),
        ),
    )
    other_context_profile = LoopSideEffectProfileRef(
        profile="pure",
        context_memory_writes=True,
        context_descriptors=(
            LoopBodyEffectRef(
                kind="memory_write",
                source="function_effect_summary",
                scope="function",
                location="outside_b",
                value_expr=2,
            ),
        ),
    )

    assert base_profile.stable_key() is not None
    assert other_context_profile.stable_key() is not None
    assert base_profile.stable_key() != other_context_profile.stable_key()


def test_loop_side_effect_profile_requires_effect_proof_for_context_level_unsafety():
    pure_profile_with_context = LoopSideEffectProfileRef(
        profile="pure",
        context_memory_writes=True,
        context_descriptors=(
            LoopBodyEffectRef(
                kind="memory_write",
                source="function_effect_summary",
                scope="function",
                location="outside",
                value_expr=1,
            ),
        ),
    )
    effect_aware_profile = LoopSideEffectProfileRef(
        profile="effect_aware",
        memory_reads=True,
    )
    read_only_pure_profile = LoopSideEffectProfileRef(profile="pure_memory_read", memory_reads=True)

    assert pure_profile_with_context.requires_effect_proof() is True
    assert effect_aware_profile.requires_effect_proof() is True
    assert read_only_pure_profile.requires_effect_proof() is False


def test_conditional_loop_guards_are_control_obligations_not_effect_proofs():
    guard_profile = LoopSideEffectProfileRef(
        profile="pure_conditional",
        conditional_guards=True,
        guard_count=1,
        effect_count=1,
        effect_descriptors=(
            LoopBodyEffectRef(
                kind="conditional_guard",
                source="pcode_scan",
                scope="loop",
                guard_constraints=("0 < n",),
                order_key=1,
            ),
        ),
    )
    context_guard_profile = LoopSideEffectProfileRef(
        profile="pure",
        context_conditional_guards=True,
        context_descriptors=(
            LoopBodyEffectRef(
                kind="conditional_guard",
                source="function_effect_summary",
                scope="function",
                guard_constraints=("0 < n",),
            ),
        ),
    )

    assert guard_profile.requires_effect_proof() is False
    assert context_guard_profile.requires_effect_proof() is False


def test_non_pure_guard_only_profiles_still_require_effect_proof():
    for profile in ("effect_aware", "effect_unknown"):
        guard_only_profile = LoopSideEffectProfileRef(
            profile=profile,
            conditional_guards=True,
            effect_descriptors=(
                LoopBodyEffectRef(
                    kind="conditional_guard",
                    source="pcode_scan",
                    scope="loop",
                    guard_constraints=("0 < n",),
                ),
            ),
        )
        context_guard_only_profile = LoopSideEffectProfileRef(
            profile=profile,
            context_conditional_guards=True,
            context_descriptors=(
                LoopBodyEffectRef(
                    kind="conditional_guard",
                    source="function_effect_summary",
                    scope="function",
                    guard_constraints=("0 < n",),
                ),
            ),
        )

        assert guard_only_profile.requires_effect_proof() is True
        assert context_guard_only_profile.requires_effect_proof() is True


def test_loop_summary_requires_path_proof_only_for_body_sensitive_cases():
    guard_partition = LoopSummaryRef(
        start_expr=0,
        limit_expr="n",
        step_expr=1,
        term_descriptor=LoopTermDescriptorRef(kind="affine_residue"),
        cases=(LoopCaseRef(path_conditions=("0 < n",), case_kind="guard_partition"),),
    )
    body_sensitive = LoopSummaryRef(
        start_expr=0,
        limit_expr="n",
        step_expr=1,
        term_descriptor=LoopTermDescriptorRef(kind="affine_residue"),
        cases=(
            LoopCaseRef(
                path_conditions=("i_is_even",),
                body_effect=LoopBodyEffectRef(kind="accumulator_update", value_expr="acc+i"),
                term_expr="i",
                case_kind="accumulator_delta",
            ),
        ),
    )

    assert guard_partition.requires_path_proof() is False
    assert body_sensitive.requires_path_proof() is True


def test_effect_aware_loop_summary_disables_exact_and_smt_shortcuts():
    summary = LoopSummaryRef(
        start_expr=0,
        limit_expr="n",
        step_expr=1,
        term_descriptor=LoopTermDescriptorRef(kind="affine_residue"),
        side_effect_profile=LoopSideEffectProfileRef(
            profile="effect_aware",
            memory_writes=True,
            effect_count=1,
            effect_descriptors=(
                LoopBodyEffectRef(
                    kind="memory_write",
                    source="pcode_scan",
                    scope="loop",
                    address_space="ram",
                    location="addr",
                    value_expr="value",
                    order_key=1,
                ),
            ),
        ),
    )
    ref = CountedLoopSummaryRef(
        induction_step=1,
        result_size=4,
        signed_loop=True,
        residue_cases=((1, 0, 1, 0),),
        loop_summary=summary,
    )
    expr = Expression.intrinsic("COUNTED_LOOP_SUM", [Expression.constant(0), Expression.constant(0), Expression.parameter("n")], runtime_ref=ref)

    assert summary.stable_key() is not None
    assert summary.pairwise_exact_key() is None
    assert ref.pairwise_exact_key() is None
    smt_identity = _lowering_identity(expr)
    assert smt_identity[0] == "opaque_loop_summary_identity"
    assert smt_identity[3] == "effect_proof_required"


def test_path_sensitive_loop_summary_disables_exact_and_smt_identity_shortcuts():
    loop_case = LoopCaseRef(
        path_conditions=("i_is_even",),
        body_effect=LoopBodyEffectRef(kind="accumulator_update", value_expr="acc+i"),
        term_expr="i",
        case_kind="accumulator_delta",
    )
    summary = LoopSummaryRef(
        start_expr=0,
        limit_expr="n",
        step_expr=1,
        term_descriptor=LoopTermDescriptorRef(kind="affine_residue"),
        cases=(loop_case,),
    )
    ref = CountedLoopSummaryRef(
        induction_step=1,
        result_size=4,
        signed_loop=True,
        residue_cases=((1, 0, 1, 0),),
        loop_summary=summary,
    )
    expr = Expression.intrinsic(
        "COUNTED_LOOP_SUM",
        [Expression.constant(0), Expression.constant(0), Expression.parameter("n")],
        runtime_ref=ref,
    )

    assert summary.stable_key() is not None
    assert summary.requires_path_proof() is True
    assert summary.pairwise_exact_key() is None
    assert ref.pairwise_exact_key() is None
    smt_identity = _lowering_identity(expr)
    assert smt_identity[0] == "opaque_loop_summary_identity"
    assert smt_identity[3] == "path_proof_required"


def test_counted_loop_update_cases_are_not_path_proof_obligations():
    loop_case = LoopCaseRef(
        path_conditions=(),
        body_effect=LoopBodyEffectRef(kind="accumulator_update", value_expr="acc+i"),
        term_expr=Expression.parameter("__loop_iv", size=4),
        case_kind="accumulator_delta",
        source="counted_loop_update_case",
    )
    summary = LoopSummaryRef(
        start_expr=0,
        limit_expr="n",
        step_expr=1,
        term_descriptor=LoopTermDescriptorRef(kind="affine_residue", residue_cases=((1, 0, 1, 0),)),
        cases=(loop_case,),
    )

    assert summary.requires_path_proof() is False
    assert summary.pairwise_exact_key() is not None


def test_counted_loop_update_case_requires_path_proof_without_descriptor_coverage():
    loop_case = LoopCaseRef(
        path_conditions=(),
        body_effect=LoopBodyEffectRef(kind="accumulator_update", value_expr="acc+i"),
        term_expr=Expression.parameter("__loop_iv", size=4),
        case_kind="accumulator_delta",
        source="counted_loop_update_case",
    )
    summary = LoopSummaryRef(
        start_expr=0,
        limit_expr="n",
        step_expr=1,
        term_descriptor=LoopTermDescriptorRef(kind="affine_residue"),
        cases=(loop_case,),
    )

    assert summary.requires_path_proof() is True
    assert summary.pairwise_exact_key() is None


def test_counted_loop_update_case_requires_path_proof_for_incomplete_residue_coverage():
    loop_case = LoopCaseRef(
        path_conditions=("i_mod_2_eq_0",),
        body_effect=LoopBodyEffectRef(kind="accumulator_update", value_expr="acc+i"),
        term_expr=Expression.parameter("__loop_iv", size=4),
        case_kind="accumulator_delta",
        source="counted_loop_update_case",
    )
    summary = LoopSummaryRef(
        start_expr=0,
        limit_expr="n",
        step_expr=1,
        term_descriptor=LoopTermDescriptorRef(kind="affine_residue", residue_cases=((2, 0, 1, 0),)),
        cases=(loop_case,),
    )

    assert summary.requires_path_proof() is True
    assert summary.pairwise_exact_key() is None


def test_loop_summary_comparator_blocks_different_path_cases():
    base = LoopSummaryRef(
        start_expr=0,
        limit_expr="n",
        step_expr=1,
        term_descriptor=LoopTermDescriptorRef(kind="affine_residue"),
        cases=(
            LoopCaseRef(
                path_conditions=("i_is_even",),
                term_expr="i",
                case_kind="accumulator_delta",
            ),
        ),
    )
    changed = LoopSummaryRef(
        start_expr=0,
        limit_expr="n",
        step_expr=1,
        term_descriptor=LoopTermDescriptorRef(kind="affine_residue"),
        cases=(
            LoopCaseRef(
                path_conditions=("i_is_odd",),
                term_expr="i",
                case_kind="accumulator_delta",
            ),
        ),
    )

    result = compare_loop_summaries(base, changed)

    assert result.status == "incompatible"
    assert result.blocks_shortcut() is True


def test_pairwise_query_records_loop_summary_cases_as_smt_comments():
    loop_case = LoopCaseRef(
        path_conditions=("i_is_even",),
        body_effect=LoopBodyEffectRef(kind="accumulator_update", value_expr="acc+i"),
        term_expr="i",
        case_kind="accumulator_delta",
    )
    summary = LoopSummaryRef(
        start_expr=0,
        limit_expr="n",
        step_expr=1,
        term_descriptor=LoopTermDescriptorRef(kind="affine_residue"),
        cases=(loop_case,),
    )
    expr = _counted_loop_expr(summary)
    return_case = _return_case_for_expr(expr)
    render = lambda value: value.to_smt() if hasattr(value, "to_smt") else str(value)

    query = build_pair_query(
        {"header_lines": [], "return_size1": 32, "return_size2": 32},
        return_case,
        return_case,
        render,
        render,
        "loop-case-comments",
    )

    assert "; Case1 loop summary cases: 1" in query
    assert "loop_case[0] kind=accumulator_delta path=[i_is_even] term=i" in query


def test_counted_loop_proof_does_not_bypass_effect_aware_summaries():
    left = _counted_loop_expr(_effect_aware_counted_loop_summary())
    right = _counted_loop_expr(_effect_aware_counted_loop_summary())
    strategy = PairwiseStrategy(None, None)

    assert strategy._counted_loop_values_are_provably_equivalent(
        left,
        right,
        left_case=_return_case_for_expr(left),
        right_case=_return_case_for_expr(right),
    ) is False


def test_counted_loop_proof_does_not_bypass_incompatible_loop_summaries():
    left = _counted_loop_expr(_pure_counted_loop_summary())
    right = _counted_loop_expr(_effect_aware_counted_loop_summary())
    strategy = PairwiseStrategy(None, None)

    assert strategy._counted_loop_values_are_provably_equivalent(
        left,
        right,
        left_case=_return_case_for_expr(left),
        right_case=_return_case_for_expr(right),
    ) is False


def test_intrinsic_runtime_values_equivalent_does_not_bypass_effect_loop_summaries():
    strategy = PairwiseStrategy(None, None)
    effect_left = _counted_loop_expr(_effect_aware_counted_loop_summary())
    effect_right = _counted_loop_expr(_effect_aware_counted_loop_summary())
    incompatible_left = _counted_loop_expr(_pure_counted_loop_summary())
    incompatible_right = _counted_loop_expr(_effect_aware_counted_loop_summary())

    assert strategy._intrinsic_runtime_values_equivalent(
        effect_left,
        effect_right,
        left_case=_return_case_for_expr(effect_left),
        right_case=_return_case_for_expr(effect_right),
    ) is False
    assert strategy._intrinsic_runtime_values_equivalent(
        incompatible_left,
        incompatible_right,
        left_case=_return_case_for_expr(incompatible_left),
        right_case=_return_case_for_expr(incompatible_right),
    ) is False


def test_counted_loop_proof_does_not_bypass_path_sensitive_summaries():
    left = _counted_loop_expr(_path_sensitive_counted_loop_summary())
    right = _counted_loop_expr(_path_sensitive_counted_loop_summary())
    strategy = PairwiseStrategy(None, None)

    assert strategy._counted_loop_values_are_provably_equivalent(
        left,
        right,
        left_case=_return_case_for_expr(left),
        right_case=_return_case_for_expr(right),
    ) is False


def test_intrinsic_runtime_values_equivalent_does_not_bypass_path_sensitive_summaries():
    strategy = PairwiseStrategy(None, None)
    path_left = _counted_loop_expr(_path_sensitive_counted_loop_summary())
    path_right = _counted_loop_expr(_path_sensitive_counted_loop_summary())
    mixed_left = _counted_loop_expr(_pure_counted_loop_summary())
    mixed_right = _counted_loop_expr(_path_sensitive_counted_loop_summary())

    assert strategy._intrinsic_runtime_values_equivalent(
        path_left,
        path_right,
        left_case=_return_case_for_expr(path_left),
        right_case=_return_case_for_expr(path_right),
    ) is False
    assert strategy._intrinsic_runtime_values_equivalent(
        mixed_left,
        mixed_right,
        left_case=_return_case_for_expr(mixed_left),
        right_case=_return_case_for_expr(mixed_right),
    ) is False


def test_method_b_loop_value_target_uses_semantic_runtime_key_not_program_id():
    class _RuntimeRef:
        loop_summary = None

        def __init__(self, owner_program_id):
            self.owner_program_id = owner_program_id

        def stable_key(self):
            return ("readonly_reduction", ("parameter", self.owner_program_id, 0x401000, 1))

        def pairwise_semantic_key(self):
            return ("readonly_reduction_semantic", ("parameter", 1))

    strategy = PairwiseStrategy(None, None)
    left_expr = Mock(runtime_ref=_RuntimeRef(111))
    right_expr = Mock(runtime_ref=_RuntimeRef(222))

    left_key = strategy._method_b_loop_value_object_key(left_expr)
    right_key = strategy._method_b_loop_value_object_key(right_expr)

    assert left_key == right_key
    assert left_key[1] == ("readonly_reduction_semantic", ("parameter", 1))
    assert left_key[3] == ("runtime_ref", ("readonly_reduction_semantic", ("parameter", 1)))
    assert "111" not in repr(left_key)
    assert "222" not in repr(right_key)


def test_counted_loop_method_b_match_does_not_bypass_guard_mismatch():
    strategy = PairwiseStrategy(None, None)
    left = _counted_loop_expr(_pure_counted_loop_summary())
    right = _counted_loop_expr(_pure_counted_loop_summary())
    n = Expression.parameter("n", size=4)
    left_case = ReturnCase(
        0,
        [Condition(Expression.binary_op("INT_SLESS", Expression.constant(0, size=4), n))],
        left,
        ReturnInfo(address="0x1000", value=left, conditions=[]),
    )
    right_case = ReturnCase(
        0,
        [Condition(Expression.binary_op("INT_SLESS", Expression.constant(1, size=4), n))],
        right,
        ReturnInfo(address="0x1004", value=right, conditions=[]),
    )

    assert strategy._intrinsic_runtime_values_equivalent(
        left,
        right,
        left_case=left_case,
        right_case=right_case,
    ) is False
    assert strategy._counted_loop_values_are_provably_equivalent(
        left,
        right,
        left_case=left_case,
        right_case=right_case,
    ) is False


def test_loop_summary_unkeyable_refs_disable_pairwise_exact_shortcut():
    unkeyable_summary = LoopSummaryRef(
        start_expr=object(),
        limit_expr="n",
        step_expr=1,
        term_descriptor=LoopTermDescriptorRef(kind="memory_load", stride=4, element_size=4),
    )
    readonly_ref = ReadonlyReductionRef(
        reduction_kind="memory_sum",
        pointer_base_ref=LocationBaseRef.parameter("ptr", index=0),
        count_parameter_name="n",
        count_parameter_index=1,
        stride=4,
        element_size=4,
        result_size=4,
        loop_summary=unkeyable_summary,
    )
    counted_ref = CountedLoopSummaryRef(
        induction_step=1,
        result_size=4,
        signed_loop=True,
        residue_cases=((1, 0, 1, 0),),
        loop_summary=unkeyable_summary,
    )

    assert unkeyable_summary.stable_key() is None
    assert readonly_ref.pairwise_exact_key() is None
    assert counted_ref.pairwise_exact_key() is None


def test_function_analysis_normalizes_deferred_calls_to_deferred_call_refs():
    info = DeferredCallInfo(
        placeholder_name="call_out_of_scope:callee#2",
        target_ref=CallTargetRef.from_name("callee"),
        sequence=2,
    )
    analysis = create_mock_analysis("wrapper")
    analysis.deferred_calls = {"legacy_placeholder": info}

    analysis.normalize_deferred_calls()

    assert list(analysis.deferred_calls) == [info.deferred_call_ref.stable_key()]


def test_location_base_parameter_identity_uses_index_not_name():
    left = LocationBaseRef.parameter("lhs", index=1)
    right = LocationBaseRef.parameter("rhs", index=1)

    assert left == right
    assert left.stable_key() == right.stable_key()


def test_location_base_parameter_identity_is_scoped_by_function_when_available():
    caller = LocationBaseRef.parameter(
        "param_2",
        index=1,
        owner_program_id=100,
        owner_entry_offset=0x401000,
    )
    callee = LocationBaseRef.parameter(
        "param_2",
        index=1,
        owner_program_id=100,
        owner_entry_offset=0x402000,
    )

    assert caller != callee
    assert caller.stable_key() != callee.stable_key()
    assert caller.semantic_key() == callee.semantic_key()


def test_loop_summary_method_b_key_uses_parameter_semantics_not_owner_identity():
    left_base = LocationBaseRef.parameter(
        "base",
        index=0,
        owner_program_id=100,
        owner_entry_offset=0x401000,
    )
    right_base = LocationBaseRef.parameter(
        "base",
        index=0,
        owner_program_id=200,
        owner_entry_offset=0x501000,
    )
    left = _readonly_loop_summary(start=0)
    right = _readonly_loop_summary(start=0)
    left = LoopSummaryRef(
        start_expr=left.start_expr,
        limit_expr=left.limit_expr,
        step_expr=left.step_expr,
        term_descriptor=LoopTermDescriptorRef(
            kind="memory_load",
            reduction_kind="sum",
            location_base_ref=left_base,
            start_offset=0,
            stride=4,
            element_size=4,
            result_size=4,
        ),
        side_effect_profile=left.side_effect_profile,
        loop_var_unit=left.loop_var_unit,
    )
    right = LoopSummaryRef(
        start_expr=right.start_expr,
        limit_expr=right.limit_expr,
        step_expr=right.step_expr,
        term_descriptor=LoopTermDescriptorRef(
            kind="memory_load",
            reduction_kind="sum",
            location_base_ref=right_base,
            start_offset=0,
            stride=4,
            element_size=4,
            result_size=4,
        ),
        side_effect_profile=right.side_effect_profile,
        loop_var_unit=right.loop_var_unit,
    )

    assert left.stable_key() != right.stable_key()
    assert loop_summary_method_b_key(left) == loop_summary_method_b_key(right)
    assert compare_loop_summaries(left, right).status == "equivalent"


def test_loop_summary_method_b_key_rejects_unresolved_variable_identity():
    summary = LoopSummaryRef(
        start_expr=Expression.constant(0, size=4),
        limit_expr=Expression.parameter("count", index=1, data_type="int", size=4),
        step_expr=Expression.constant(1, size=4),
        term_descriptor=LoopTermDescriptorRef(kind="affine_residue"),
        seed_terms=(Expression.variable("tmp", size=4),),
        side_effect_profile=LoopSideEffectProfileRef(profile="pure"),
    )

    assert loop_summary_method_b_key(summary) is None


def test_loop_summary_method_b_key_uses_variable_storage_identity_not_name():
    storage = StorageInfo(
        is_register=True,
        space_name="register",
        register_name="r7",
        base_register_name="r7",
        size=4,
        size_bits=32,
    )
    left = LoopSummaryRef(
        start_expr=Expression.constant(0, size=4),
        limit_expr=Expression.parameter("count", index=1, data_type="int", size=4),
        step_expr=Expression.constant(1, size=4),
        term_descriptor=LoopTermDescriptorRef(kind="affine_residue"),
        seed_terms=(Expression.variable("tmp", size=4, storage_info=storage),),
        side_effect_profile=LoopSideEffectProfileRef(profile="pure"),
    )
    right = LoopSummaryRef(
        start_expr=Expression.constant(0, size=4),
        limit_expr=Expression.parameter("count", index=1, data_type="int", size=4),
        step_expr=Expression.constant(1, size=4),
        term_descriptor=LoopTermDescriptorRef(kind="affine_residue"),
        seed_terms=(Expression.variable("renamed_tmp", size=4, storage_info=storage),),
        side_effect_profile=LoopSideEffectProfileRef(profile="pure"),
    )

    left_key = loop_summary_method_b_key(left)
    right_key = loop_summary_method_b_key(right)
    assert left_key is not None
    assert left_key == right_key


def _loop_bound_variable(
    *,
    role: str,
    ordinal: int,
    varnode_token: str,
    name: str,
) -> Expression:
    return Expression.variable(
        name,
        size=4,
        runtime_ref=LoopVariableIdentityRef(
            role=role,
            binder_ordinal=ordinal,
            varnode_key=("test_varnode", varnode_token),
        ),
    )


def test_loop_variable_identity_ref_has_no_standalone_semantic_key():
    ref = LoopVariableIdentityRef(
        role="state",
        binder_ordinal=0,
        varnode_key=("test_varnode", "state0"),
    )

    assert ref.semantic_key() is None
    assert ref.stable_key() is not None


def test_loop_summary_method_b_key_alpha_normalizes_loop_variable_binders():
    left = LoopSummaryRef(
        start_expr=Expression.constant(0, size=4),
        limit_expr=Expression.parameter("count", index=1, data_type="int", size=4),
        step_expr=Expression.constant(1, size=4),
        term_descriptor=LoopTermDescriptorRef(kind="affine_residue"),
        seed_terms=(
            _loop_bound_variable(role="state", ordinal=0, varnode_token="left_state", name="left_state"),
            _loop_bound_variable(role="state", ordinal=1, varnode_token="left_state_next", name="left_state_next"),
        ),
        side_effect_profile=LoopSideEffectProfileRef(profile="pure"),
    )
    right = LoopSummaryRef(
        start_expr=Expression.constant(0, size=4),
        limit_expr=Expression.parameter("count", index=1, data_type="int", size=4),
        step_expr=Expression.constant(1, size=4),
        term_descriptor=LoopTermDescriptorRef(kind="affine_residue"),
        seed_terms=(
            _loop_bound_variable(role="state", ordinal=0, varnode_token="right_state", name="right_state"),
            _loop_bound_variable(role="state", ordinal=1, varnode_token="right_state_next", name="right_state_next"),
        ),
        side_effect_profile=LoopSideEffectProfileRef(profile="pure"),
    )

    left_key = loop_summary_method_b_key(left)
    right_key = loop_summary_method_b_key(right)
    assert left_key is not None
    assert left_key == right_key


def test_loop_summary_method_b_key_rejects_duplicate_loop_variable_binder_slots():
    summary = LoopSummaryRef(
        start_expr=Expression.constant(0, size=4),
        limit_expr=Expression.parameter("count", index=1, data_type="int", size=4),
        step_expr=Expression.constant(1, size=4),
        term_descriptor=LoopTermDescriptorRef(kind="affine_residue"),
        seed_terms=(
            _loop_bound_variable(role="state", ordinal=0, varnode_token="state_a", name="state_a"),
            _loop_bound_variable(role="state", ordinal=0, varnode_token="state_b", name="state_b"),
        ),
        side_effect_profile=LoopSideEffectProfileRef(profile="pure"),
    )

    assert loop_summary_method_b_key(summary) is None


def test_method_b_smt_identity_uses_loop_semantics_across_owner_scoped_binaries():
    left_base = LocationBaseRef.parameter(
        "base",
        index=0,
        owner_program_id=100,
        owner_entry_offset=0x401000,
    )
    right_base = LocationBaseRef.parameter(
        "base",
        index=0,
        owner_program_id=200,
        owner_entry_offset=0x501000,
    )
    left_summary = _readonly_loop_summary(start=0)
    right_summary = _readonly_loop_summary(start=0)
    left_summary = LoopSummaryRef(
        start_expr=left_summary.start_expr,
        limit_expr=left_summary.limit_expr,
        step_expr=left_summary.step_expr,
        term_descriptor=LoopTermDescriptorRef(
            kind="memory_load",
            reduction_kind="sum",
            location_base_ref=left_base,
            start_offset=0,
            stride=4,
            element_size=4,
            result_size=4,
        ),
        side_effect_profile=left_summary.side_effect_profile,
        loop_var_unit=left_summary.loop_var_unit,
    )
    right_summary = LoopSummaryRef(
        start_expr=right_summary.start_expr,
        limit_expr=right_summary.limit_expr,
        step_expr=right_summary.step_expr,
        term_descriptor=LoopTermDescriptorRef(
            kind="memory_load",
            reduction_kind="sum",
            location_base_ref=right_base,
            start_offset=0,
            stride=4,
            element_size=4,
            result_size=4,
        ),
        side_effect_profile=right_summary.side_effect_profile,
        loop_var_unit=right_summary.loop_var_unit,
    )
    left_expr = Expression.intrinsic(
        "READONLY_SUM",
        [
            Expression.parameter("base", index=0, data_type="int *", size=8),
            Expression.parameter("count", index=1, data_type="int", size=4),
        ],
        size=4,
        runtime_ref=ReadonlyReductionRef(
            reduction_kind="memory_sum",
            pointer_base_ref=left_base,
            count_parameter_name="count",
            count_parameter_index=1,
            stride=4,
            element_size=4,
            result_size=4,
            signed_counter=True,
            loop_summary=left_summary,
        ),
    )
    right_expr = Expression.intrinsic(
        "READONLY_SUM",
        [
            Expression.parameter("base", index=0, data_type="int *", size=8),
            Expression.parameter("count", index=1, data_type="int", size=4),
        ],
        size=4,
        runtime_ref=ReadonlyReductionRef(
            reduction_kind="memory_sum",
            pointer_base_ref=right_base,
            count_parameter_name="count",
            count_parameter_index=1,
            stride=4,
            element_size=4,
            result_size=4,
            signed_counter=True,
            loop_summary=right_summary,
        ),
    )

    assert left_expr.runtime_ref.stable_key() != right_expr.runtime_ref.stable_key()
    assert left_expr.runtime_ref.semantic_key() == right_expr.runtime_ref.semantic_key()
    assert _lowering_identity(left_expr) == _lowering_identity(right_expr)


def test_loop_summary_method_b_key_keeps_vector_width_shape_distinct():
    scalar = _readonly_loop_summary(start=0)
    vector_like = LoopSummaryRef(
        start_expr=scalar.start_expr,
        limit_expr=scalar.limit_expr,
        step_expr=Expression.constant(1, size=4),
        term_descriptor=LoopTermDescriptorRef(
            kind="memory_load",
            reduction_kind="sum",
            location_base_ref=LocationBaseRef.parameter("base", index=0),
            start_offset=0,
            stride=16,
            element_size=8,
            result_size=4,
        ),
        side_effect_profile=scalar.side_effect_profile,
        loop_var_unit=scalar.loop_var_unit,
    )

    assert loop_summary_method_b_key(scalar) != loop_summary_method_b_key(vector_like)
    assert compare_loop_summaries(scalar, vector_like).status == "unknown"


def test_loop_summary_method_b_key_does_not_scalarize_vector_lanes_without_iteration_proof():
    scalar = _readonly_loop_summary(start=0)
    vector_lanes = LoopSummaryRef(
        start_expr=scalar.start_expr,
        limit_expr=scalar.limit_expr,
        step_expr=scalar.step_expr,
        term_descriptor=LoopTermDescriptorRef(
            kind="memory_load",
            reduction_kind="sum",
            location_base_ref=LocationBaseRef.parameter("base", index=0),
            start_offset=0,
            stride=16,
            element_size=8,
            result_size=4,
            lane_terms=((0, 4), (4, 4), (8, 4), (12, 4)),
        ),
        side_effect_profile=scalar.side_effect_profile,
        loop_var_unit=scalar.loop_var_unit,
    )

    assert loop_summary_method_b_key(scalar) != loop_summary_method_b_key(vector_lanes)
    assert compare_loop_summaries(scalar, vector_lanes).status == "unknown"


def test_loop_summary_method_b_key_scalarizes_vector_lanes_only_with_scalar_iteration_proof():
    scalar = _readonly_loop_summary(start=0)
    scalar_proven = LoopSummaryRef(
        start_expr=scalar.start_expr,
        limit_expr=scalar.limit_expr,
        step_expr=scalar.step_expr,
        term_descriptor=scalar.term_descriptor,
        side_effect_profile=scalar.side_effect_profile,
        loop_var_unit="scalar_element_index",
    )
    vector_lanes = LoopSummaryRef(
        start_expr=scalar.start_expr,
        limit_expr=scalar.limit_expr,
        step_expr=scalar.step_expr,
        term_descriptor=LoopTermDescriptorRef(
            kind="memory_load",
            reduction_kind="sum",
            location_base_ref=LocationBaseRef.parameter("base", index=0),
            start_offset=0,
            stride=16,
            element_size=8,
            result_size=4,
            lane_terms=((0, 4), (4, 4), (8, 4), (12, 4)),
        ),
        side_effect_profile=scalar.side_effect_profile,
        loop_var_unit="scalar_element_index",
    )

    assert loop_summary_method_b_key(scalar_proven) == loop_summary_method_b_key(vector_lanes)


def test_loop_summary_method_b_key_leaves_unstored_limit_width_to_smt_parameter_binding():
    int_count = _readonly_loop_summary(start=0)
    long_count = LoopSummaryRef(
        start_expr=Expression.constant(0, size=8),
        limit_expr=Expression.parameter("count64", index=1, data_type="ulong", size=8),
        step_expr=Expression.constant(1, size=8),
        term_descriptor=int_count.term_descriptor,
        side_effect_profile=int_count.side_effect_profile,
        loop_var_unit=int_count.loop_var_unit,
    )

    assert loop_summary_method_b_key(int_count) == loop_summary_method_b_key(long_count)
    assert compare_loop_summaries(int_count, long_count).status == "equivalent"


def test_loop_summary_method_b_key_preserves_stored_limit_width_identity():
    low_count_storage = StorageInfo(
        is_register=True,
        space_name="register",
        space_id=3,
        offset=0x10,
        size=4,
        size_bits=32,
        register_name="w0",
        register_offset=0x10,
        register_size=4,
        register_size_bits=32,
        base_register_name="x0",
        base_register_offset=0x10,
        base_register_size=8,
        base_register_size_bits=64,
        bit_offset_in_base=0,
    )
    wide_count_storage = StorageInfo(
        is_register=True,
        space_name="register",
        space_id=3,
        offset=0x10,
        size=8,
        size_bits=64,
        register_name="x0",
        register_offset=0x10,
        register_size=8,
        register_size_bits=64,
        base_register_name="x0",
        base_register_offset=0x10,
        base_register_size=8,
        base_register_size_bits=64,
        bit_offset_in_base=0,
    )
    int_count = _readonly_loop_summary(start=0)
    low_count = LoopSummaryRef(
        start_expr=Expression.constant(0, size=4),
        limit_expr=Expression.parameter("count", index=1, data_type="uint", size=4, storage_info=low_count_storage),
        step_expr=Expression.constant(1, size=4),
        term_descriptor=int_count.term_descriptor,
        side_effect_profile=int_count.side_effect_profile,
        loop_var_unit=int_count.loop_var_unit,
    )
    wide_count = LoopSummaryRef(
        start_expr=Expression.constant(0, size=8),
        limit_expr=Expression.parameter("count", index=1, data_type="ulong", size=8, storage_info=wide_count_storage),
        step_expr=Expression.constant(1, size=8),
        term_descriptor=int_count.term_descriptor,
        side_effect_profile=int_count.side_effect_profile,
        loop_var_unit=int_count.loop_var_unit,
    )

    assert loop_summary_method_b_key(low_count) != loop_summary_method_b_key(wide_count)


def test_storage_info_register_identity_uses_numeric_base_metadata():
    left = StorageInfo(
        is_register=True,
        space_name="register",
        space_id=3,
        offset=0x10,
        size=4,
        size_bits=32,
        register_name="w0",
        register_offset=0x10,
        register_size=4,
        register_size_bits=32,
        base_register_name="x0",
        base_register_offset=0x10,
        base_register_size=8,
        base_register_size_bits=64,
        bit_offset_in_base=0,
    )
    right = StorageInfo(
        is_register=True,
        space_name="register",
        space_id=3,
        offset=0x10,
        size=4,
        size_bits=32,
        register_name="arg0_low",
        register_offset=0x10,
        register_size=4,
        register_size_bits=32,
        base_register_name="param_alias",
        base_register_offset=0x10,
        base_register_size=8,
        base_register_size_bits=64,
        bit_offset_in_base=0,
    )

    assert left.shares_base_register_with(right) is True
    assert left.register_identity_key() == right.register_identity_key()


def test_storage_info_matches_base_register_by_name_when_numeric_offsets_differ():
    synthetic = StorageInfo(
        is_register=True,
        space_name="register",
        space_id=0,
        size=8,
        size_bits=64,
        register_name="v0",
        base_register_name="v0",
        base_register_offset=StorageInfo._synthetic_register_offset("v0"),
        base_register_size=8,
        base_register_size_bits=64,
        bit_offset_in_base=0,
    )
    concrete = StorageInfo(
        is_register=True,
        space_name="register",
        space_id=548,
        offset=0x10,
        size=8,
        size_bits=64,
        register_name="v0",
        register_offset=0x10,
        register_size=8,
        register_size_bits=64,
        base_register_name="v0",
        base_register_offset=0x10,
        base_register_size=8,
        base_register_size_bits=64,
        bit_offset_in_base=0,
    )

    assert synthetic.base_register_offset != concrete.base_register_offset
    assert synthetic.shares_base_register_with(concrete) is True


def test_post_state_symbolic_locations_bind_parameter_indices():
    parameters = [{"name": "trace", "index": 0, "size": 8}]
    expr = post_state_read_expression_for_location(
        CanonicalLocation(
            base_ref=LocationBaseRef.parameter("trace", index=0),
            offset=4,
            size=4,
        ),
        parameters,
        symbolic=True,
    )

    runtime_ref = expr.runtime_ref
    assert isinstance(runtime_ref, PostStateReadRef)
    assert runtime_ref.location.base_ref == LocationBaseRef.parameter("trace", index=0)
    assert runtime_ref.snapshot_ref == PostStateSnapshotRef.function_return()


def test_fp_readonly_reduction_contract_allows_narrow_result_surface():
    proof = ReductionAccumulatorProof(
        pointer_base_ref=LocationBaseRef.parameter("base", index=0),
        limit_expr=Expression.parameter("count", index=1, data_type="int", size=4),
        count_parameter_name="count",
        count_parameter_index=1,
        stride=4,
        element_size=4,
        result_size=16,
        start_index=0,
        start_offset=0,
        reduction_kind="fp_int2float_div_count_sum",
    )

    key = proof.readonly_term_sequence_contract_key(result_size=8)

    assert key is not None
    assert key[5] == 8


def test_readonly_count_identity_rejects_storage_mismatch_despite_matching_parameter_index():
    strategy = PairwiseStrategy(None, None, debug=False)
    left = ReadonlyReductionRef(
        reduction_kind="fp_int2float_div_count_sum",
        pointer_base_ref=LocationBaseRef.parameter("base", index=0),
        count_parameter_name="count",
        count_parameter_index=1,
        count_parameter_storage_identity_key=("register", "w0", 4),
        stride=4,
        element_size=4,
        result_size=16,
    )
    right = ReadonlyReductionRef(
        reduction_kind="fp_int2float_div_count_sum",
        pointer_base_ref=LocationBaseRef.parameter("base", index=0),
        count_parameter_name="count",
        count_parameter_index=1,
        count_parameter_storage_identity_key=("register", "a0", 4),
        stride=4,
        element_size=4,
        result_size=8,
    )

    assert not strategy._readonly_count_identities_compatible(left, right)


def test_readonly_count_identity_rejects_same_low_wide_narrow_projection_without_proof():
    low_count_storage = StorageInfo(
        is_register=True,
        space_name="register",
        space_id=3,
        offset=0x10,
        size=4,
        size_bits=32,
        register_name="w0",
        register_offset=0x10,
        register_size=4,
        register_size_bits=32,
        base_register_name="x0",
        base_register_offset=0x10,
        base_register_size=8,
        base_register_size_bits=64,
        bit_offset_in_base=0,
    )
    wide_count_storage = StorageInfo(
        is_register=True,
        space_name="register",
        space_id=3,
        offset=0x10,
        size=8,
        size_bits=64,
        register_name="x0",
        register_offset=0x10,
        register_size=8,
        register_size_bits=64,
        base_register_name="x0",
        base_register_offset=0x10,
        base_register_size=8,
        base_register_size_bits=64,
        bit_offset_in_base=0,
    )
    strategy = PairwiseStrategy(None, None, debug=False)
    low_ref = ReadonlyReductionRef(
        reduction_kind="fp_int2float_div_count_sum",
        pointer_base_ref=LocationBaseRef.parameter("base", index=0),
        count_parameter_name="count",
        count_parameter_index=1,
        count_parameter_storage_identity_key=low_count_storage.storage_identity_key(),
        stride=4,
        element_size=4,
        result_size=8,
    )
    wide_ref = ReadonlyReductionRef(
        reduction_kind="fp_int2float_div_count_sum",
        pointer_base_ref=LocationBaseRef.parameter("base", index=0),
        count_parameter_name="count",
        count_parameter_index=1,
        count_parameter_storage_identity_key=wide_count_storage.storage_identity_key(),
        stride=4,
        element_size=4,
        result_size=8,
    )

    assert strategy._readonly_count_storage_relation_key(low_ref, wide_ref) == (
        "same_register_base_projection",
        ("base", (3, 0x10, 64)),
        ("left_bits", 0, 32),
        ("right_bits", 0, 64),
        ("projection", "right_contains_left"),
    )
    assert not strategy._readonly_count_identities_compatible(low_ref, wide_ref)


def test_readonly_contract_shortcut_rejects_same_low_projection_without_extension_proof():
    low_count_storage = StorageInfo(
        is_register=True,
        space_name="register",
        space_id=3,
        offset=0x10,
        size=4,
        size_bits=32,
        register_name="w0",
        register_offset=0x10,
        register_size=4,
        register_size_bits=32,
        base_register_name="x0",
        base_register_offset=0x10,
        base_register_size=8,
        base_register_size_bits=64,
        bit_offset_in_base=0,
    )
    wide_count_storage = StorageInfo(
        is_register=True,
        space_name="register",
        space_id=3,
        offset=0x10,
        size=8,
        size_bits=64,
        register_name="x0",
        register_offset=0x10,
        register_size=8,
        register_size_bits=64,
        base_register_name="x0",
        base_register_offset=0x10,
        base_register_size=8,
        base_register_size_bits=64,
        bit_offset_in_base=0,
    )
    low_storage_key = low_count_storage.storage_identity_key()
    wide_storage_key = wide_count_storage.storage_identity_key()
    strategy = PairwiseStrategy(None, None, debug=False)
    low_ref = ReadonlyReductionRef(
        reduction_kind="memory_sum",
        pointer_base_ref=LocationBaseRef.parameter("base", index=0),
        count_parameter_name="count",
        count_parameter_index=1,
        count_parameter_storage_identity_key=low_storage_key,
    )
    wide_ref = ReadonlyReductionRef(
        reduction_kind="memory_sum",
        pointer_base_ref=LocationBaseRef.parameter("base", index=0),
        count_parameter_name="count",
        count_parameter_index=1,
        count_parameter_storage_identity_key=wide_storage_key,
    )
    common_tail = (
        4,
        0,
        1,
        0,
        4,
        True,
        (),
        (32, 0),
        ("loop_side_effect_profile", "pure_memory_read", True, False, False, False, False, False, False, False, False, 0, 0, (), ()),
    )
    low_contract = (
        "readonly_reduction_term_sequence_contract",
        "memory_sum",
        ("parameter", 0),
        ("parameter_storage", low_storage_key),
        ("loop_limit_parameter_storage", ("storage_identity", low_storage_key)),
        *common_tail,
    )
    wide_contract = (
        "readonly_reduction_term_sequence_contract",
        "memory_sum",
        ("parameter", 0),
        ("parameter_storage", wide_storage_key),
        ("loop_limit_parameter_storage", ("storage_identity", wide_storage_key)),
        *common_tail,
    )

    assert not strategy._readonly_count_identities_compatible(low_ref, wide_ref)
    assert not strategy._readonly_contract_count_identities_compatible(low_ref, wide_ref)
    assert not strategy._readonly_contract_limit_keys_compatible(low_contract[4], wide_contract[4], low_ref, wide_ref)
    assert not strategy._readonly_reduction_contract_keys_compatible(low_contract, wide_contract, low_ref, wide_ref)
    assert strategy._readonly_projection_contract_count_identities_compatible(low_ref, wide_ref)
    assert strategy._readonly_projection_contract_limit_keys_compatible(low_contract[4], wide_contract[4], low_ref, wide_ref)
