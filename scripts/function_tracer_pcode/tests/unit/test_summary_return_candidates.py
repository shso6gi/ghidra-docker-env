# -*- coding: utf-8 -*-

from dataclasses import replace

from scripts.function_tracer_pcode.analysis.effects.summary import EffectSummary
from scripts.function_tracer_pcode.analysis.recurrence.summarizer import (
    StructuralRecurrenceSummarizer,
)
from scripts.function_tracer_pcode.analysis.returns.summary_returns import (
    _canonicalize_conditions_for_analysis_parameters,
    _conditions_unsat,
    _conditions_imply_count_value,
    _extract_readonly_reduction_term_descriptor,
    _full_width_mask_singleton_condition,
    _reduction_count_parameter_expression,
    _return_info_identity_key,
    _return_is_exact_seed,
    _return_partition_covers_active_precondition,
    _readonly_reduction_exact_overlap_is_proved,
    accept_summary_return_candidates,
)
from scripts.function_tracer_pcode.proof.strategies.base import CheckStrategy
from scripts.function_tracer_pcode.checker.unknown_reason import (
    UnknownReasonId,
    get_unknown_reason_definition,
)
from scripts.function_tracer_pcode.core import (
    CallTargetRef,
    Condition,
    DeferredCallRef,
    Expression,
    ExpressionType,
    FunctionReturnAnalysis,
    LocationBaseRef,
    PcodeOpRef,
    ReductionAccumulatorProof,
    ReadonlyReductionTermRef,
    ReturnInfo,
    UnknownValueRef,
)


class _ReasonMappingHarness:
    _blocking_reason_kind = staticmethod(CheckStrategy._blocking_reason_kind)


class _FakeLoopSummaryRuntimeRef:
    def __init__(self, name: str = "barthe2big_counted_loop"):
        self.name = name

    def stable_key(self):
        return ("counted_loop_summary", self.name, "header", "latch", "exit")


class _ResolvedCallRuntimeRef:
    def stable_key(self):
        return ("resolved_call", "helper", 0x2000)

    def is_resolved_call(self) -> bool:
        return True


class _AnalysisKeyNoneResolvedCallRuntimeRef:
    def analysis_key(self):
        return None

    def stable_key(self):
        return ("resolved_call", "helper", 0x2000)

    def is_resolved_call(self) -> bool:
        return True


class _MarkerOnlyResolvedCallRuntimeRef:
    def is_resolved_call(self) -> bool:
        return True


class _PlaceholderResolvedCallRuntimeRef:
    def stable_key(self):
        return ("opaque", "resolved_call")

    def is_resolved_call(self) -> bool:
        return True


class _StringKeyResolvedCallRuntimeRef:
    def stable_key(self):
        return "resolved_call"

    def is_resolved_call(self) -> bool:
        return True


class _EmptyTupleKeyResolvedCallRuntimeRef:
    def stable_key(self):
        return ()

    def is_resolved_call(self) -> bool:
        return True


class _UnresolvedCallRuntimeRef:
    def is_unresolved_call(self) -> bool:
        return True


class _FakeStorageInfo:
    def __init__(self, key):
        self._key = tuple(key)

    def storage_identity_key(self):
        return self._key


class _FakeAccumulatorProof:
    def __init__(self, *, index=1, storage_key=None, name="count"):
        self.count_parameter_index = index
        self.count_parameter_storage_identity_key = storage_key
        self.count_parameter_name = name


_SUMMARY_SOURCE_KEY = (
    "counted_loop_summary_parts",
    ("start", "0"),
    ("limit", "n"),
    1,
    32,
    True,
    ((1, 0, 1, 0, ("none",)),),
    ("guard_constraints", ("n_gt_one",)),
    ("loop_side_effect_profile", "pure", False, False, False, False, False, False, False, False, False, 0, 0, (), ()),
    "unit_test",
)

_COUNTED_STATE_TRANSITION_SOURCE_KEY = (
    "counted_state_transition_loop_summary",
    ("expr", "initial_state"),
    ("expr", "start"),
    ("expr", "limit"),
    ("expr", "step"),
    ("expr", "transition"),
    ("expr", "state_placeholder"),
    ("loop_side_effect_profile", "pure", False, False, False, False, False, False, False, False, False, 0, 0, (), ()),
    ("guard_constraints", ("n_gt_one",)),
    32,
    32,
    True,
    "unit_test",
)

_STATE_TRANSITION_HANDOFF_TARGET_KEY = (
    "prior_state_transition_handoff_target",
    _COUNTED_STATE_TRANSITION_SOURCE_KEY,
    (
        "handoff_blocks",
        ("pcode_block", "B", ("function_entry", "ram", 0x1000), 3, 0x1008),
        ("pcode_block", "B", ("function_entry", "ram", 0x1000), 4, 0x100c),
        ("pcode_block", "B", ("function_entry", "ram", 0x1000), 4, 0x100c),
        "all_paths_clean_to_phi_predecessor",
    ),
    (
        "value_preserving_flow",
        ("varnode", "prior_output"),
        ("varnode", "current_acc_init"),
        (
            (
                "edge",
                "COPY",
                ("varnode", "prior_output"),
                ("varnode", "current_acc_init"),
                32,
                32,
                (
                    "edge_location",
                    ("pcode_op", "B", 0x100c, 9, 0),
                    ("pcode_block", "B", ("function_entry", "ram", 0x1000), 4, 0x100c),
                ),
            ),
        ),
    ),
    ("guard_handoff_proof", "identical_guard_domain", ("guard", "prior_entry"), ("guard", "prior_entry"), "proved", ("guard_constraints", ("n_gt_one",))),
    ("loop_identity", ("expr", "start"), ("expr", "limit"), 1, ("guard", "continue"), ("guard", "entry"), True, "bv_modular"),
    ("loop_side_effect_profile", "pure", False, False, False, False, False, False, False, False, False, 0, 0, (), ()),
    ("handoff_widths", 32, 32, 32, "same_width"),
)

_STATE_TRANSITION_HANDOFF_PROOF_ID = (
    "proof_obligation_id",
    "prior_state_transition_handoff",
    _STATE_TRANSITION_HANDOFF_TARGET_KEY,
)

_STATE_TRANSITION_HANDOFF_PROOF_KEY = (
    "prior_state_transition_handoff_proof_ref",
    _STATE_TRANSITION_HANDOFF_PROOF_ID,
    _STATE_TRANSITION_HANDOFF_TARGET_KEY,
)

_STATE_TRANSITION_HANDOFF_PROOF_EVIDENCE = {
    "object_derived": True,
    "status": "complete",
    "reason_id": "prior_state_transition_handoff",
    "recovery_proof_kind": "loop_recurrence_proof",
    "proof_stage": "prior_state_transition_handoff",
    "evidence_kind": "value_preserving_handoff",
    "object_target_key": _STATE_TRANSITION_HANDOFF_TARGET_KEY,
    "proof_obligation_id": _STATE_TRANSITION_HANDOFF_PROOF_ID,
    "proof_source": "unit_test",
    "proof_content": {
        "object_derived": True,
        "object_target_key": _STATE_TRANSITION_HANDOFF_TARGET_KEY,
        "handoff_status": "proved",
        "target_summary_key": _COUNTED_STATE_TRANSITION_SOURCE_KEY,
        "handoff_blocks": _STATE_TRANSITION_HANDOFF_TARGET_KEY[2],
        "value_flow": _STATE_TRANSITION_HANDOFF_TARGET_KEY[3],
        "guard_handoff": _STATE_TRANSITION_HANDOFF_TARGET_KEY[4],
        "loop_identity": _STATE_TRANSITION_HANDOFF_TARGET_KEY[5],
        "side_effect_profile": _STATE_TRANSITION_HANDOFF_TARGET_KEY[6],
        "widths": _STATE_TRANSITION_HANDOFF_TARGET_KEY[7],
        "checks": (
            ("phi_predecessor_edge", "proved"),
            ("clean_handoff_paths", "proved"),
            ("value_preserving_flow", "proved"),
            ("guard_handoff", "proved"),
            ("loop_identity", "proved"),
            ("widths", "proved"),
            ("side_effects", "proved"),
        ),
    },
}

_SUMMARY_TRANSITION_KEY = (
    "counted_loop_transition_evidence",
    ("header_block", ("pcode_block", "B", ("function_entry", "ram", 0x1000), 1, 0x1000)),
    ("latch_block", ("pcode_block", "B", ("function_entry", "ram", 0x1000), 2, 0x1004)),
    ("exit_block", ("pcode_block", "B", ("function_entry", "ram", 0x1000), 3, 0x1008)),
    ("induction_phi", ("pcode_op", "B", 0x1000, 1, 0)),
    ("accumulator_phi", ("pcode_op", "B", 0x1000, 2, 0)),
    ("exit_guard", ("pcode_op", "B", 0x1004, 3, 0)),
    ("exit_guard_binding", ("guard", "n")),
    ("bound_binding", ("param", "n")),
    ("accumulator_base", ("expr", "init"), ("expr", "init"), ("prior_summary_dependency", "none")),
    ("updates", ((("conditions", ()), ("expr", "acc_update"), ("expr", "delta")),)),
    ("loop_cases", (("loop_case", "accumulator_delta", (), ("body_effect",), ("term",), "unit_test"),)),
    ("replacement_obligation", "not_required_without_phi_circular"),
)


def _with_summary_proof(ret: ReturnInfo) -> ReturnInfo:
    ret.summary_candidate_source_key = _SUMMARY_SOURCE_KEY
    ret.summary_transition_evidence_key = _SUMMARY_TRANSITION_KEY
    return ret


def _with_return_region_summary_proof(
    ret: ReturnInfo,
    *,
    coverage_status: str = "proved",
    exact_witnesses_key=("exact_return_witnesses", ()),
    superseded_return_keys=(),
    content_superseded_return_keys=None,
):
    superseded_return_keys = tuple(superseded_return_keys or ())
    object_target_key = (
        "return_region_summary_target",
        ("summary_value", "unit_test"),
        ("summary_conditions", "unit_test"),
        exact_witnesses_key,
        ("coverage", "unit_test", coverage_status),
        ("source", "unit_test"),
    )
    if superseded_return_keys:
        object_target_key = object_target_key + (
            ("superseded_return_keys", superseded_return_keys),
        )
    proof_id = ("proof_obligation_id", "return_region_summary", object_target_key)
    proof_ref = ("return_region_summary_proof_ref", proof_id, object_target_key)
    content_superseded_return_keys = (
        superseded_return_keys
        if content_superseded_return_keys is None
        else tuple(content_superseded_return_keys or ())
    )
    evidence = {
        "proof_obligation_id": proof_id,
        "status": "complete",
        "proof_stage": "return_region_summary",
        "evidence_kind": "smt_value_equivalence",
        "object_target_key": object_target_key,
        "proof_content": {
            "proof_status": "proved",
            "object_target_key": object_target_key,
            "summary_value_key": object_target_key[1],
            "summary_conditions_key": object_target_key[2],
            "exact_witnesses_key": exact_witnesses_key,
            "coverage_key": object_target_key[4],
            "source_key": object_target_key[5],
            "superseded_return_keys": content_superseded_return_keys,
            "checks": (
                ("summary_value_equivalence", "proved"),
                ("summary_region_coverage", coverage_status),
                ("summary_side_effects", "pure"),
            ),
        },
    }
    ret.summary_candidate_source_key = _SUMMARY_SOURCE_KEY
    ret.summary_transition_evidence_key = proof_ref
    return ret, evidence


def _param(name: str = "n", index: int = 0, size: int = 4):
    return {
        "name": name,
        "index": index,
        "size": size,
        "data_type": "int",
        "is_signed": True,
    }


def _n() -> Expression:
    return Expression.parameter("n", 0, size=4)


def _const(value: int, size: int = 4) -> Expression:
    return Expression.constant(value, size)


def _summary_const(value: int, size: int = 4) -> Expression:
    return Expression.constant(
        value,
        size,
        runtime_ref=_FakeLoopSummaryRuntimeRef(),
    )


def _cond(op: str, left: Expression, right: Expression) -> Condition:
    return Condition(Expression.binary_op(op, left, right), False)


def _analysis_with_exact_returns(effect_summary=None) -> FunctionReturnAnalysis:
    n = _n()
    return FunctionReturnAnalysis(
        function_name="f",
        entry_point="0x1000",
        parameters=[_param()],
        returns=[
            ReturnInfo(
                address="0x1000",
                value=_const(0),
                conditions=[_cond("INT_SLESSEQUAL", n, _const(0))],
                pcode_identity="return:non_positive",
            ),
            ReturnInfo(
                address="0x1004",
                value=_const(1),
                conditions=[_cond("INT_EQUAL", n, _const(1))],
                pcode_identity="return:one",
            ),
        ],
        return_type="int",
        effect_summary=effect_summary,
        binary_id="barthe2big-test-binary",
    )


def test_unresolved_exact_return_is_not_used_as_summary_seed():
    ret = ReturnInfo(
        address="0x1000",
        value=Expression(ExpressionType.UNKNOWN, name="unresolved_return", size=4),
        return_kind="exact",
    )

    assert not _return_is_exact_seed(ret)


def test_cyclic_exact_return_expression_is_not_used_as_summary_seed():
    phi = Expression.phi([])
    phi.value.append((None, phi))
    ret = ReturnInfo(address="0x1000", value=phi, return_kind="exact")

    assert not _return_is_exact_seed(ret)


def test_resolved_call_exact_return_can_remain_summary_seed():
    ret = ReturnInfo(
        address="0x1000",
        value=Expression(
            ExpressionType.CALL,
            name="resolved_helper",
            operands=[Expression.parameter("x", 0, size=4)],
            runtime_ref=CallTargetRef.from_name("resolved_helper", entry_offset=0x2000),
        ),
        return_kind="exact",
    )

    assert _return_is_exact_seed(ret)


def test_call_without_runtime_ref_is_not_used_as_summary_seed():
    ret = ReturnInfo(
        address="0x1000",
        value=Expression.call("maybe_unresolved_helper", [Expression.parameter("x", 0, size=4)]),
        return_kind="exact",
    )

    assert not _return_is_exact_seed(ret)


def test_unknown_call_target_exact_return_is_not_used_as_summary_seed():
    ret = ReturnInfo(
        address="0x1000",
        value=Expression(
            ExpressionType.CALL,
            name="unknown_helper",
            operands=[Expression.parameter("x", 0, size=4)],
            runtime_ref=CallTargetRef.unknown("unknown_helper"),
        ),
        return_kind="exact",
    )

    assert not _return_is_exact_seed(ret)


def test_name_only_call_target_exact_return_is_not_used_as_summary_seed():
    ret = ReturnInfo(
        address="0x1000",
        value=Expression(
            ExpressionType.CALL,
            name="name_only_helper",
            operands=[Expression.parameter("x", 0, size=4)],
            runtime_ref=CallTargetRef.from_name("name_only_helper"),
        ),
        return_kind="exact",
    )

    assert not _return_is_exact_seed(ret)


def test_external_call_target_with_library_can_remain_summary_seed():
    ret = ReturnInfo(
        address="0x1000",
        value=Expression(
            ExpressionType.CALL,
            name="external_helper",
            operands=[Expression.parameter("x", 0, size=4)],
            runtime_ref=CallTargetRef.from_name("external_helper", is_external=True, library_name="libhelper"),
        ),
        return_kind="exact",
    )

    assert _return_is_exact_seed(ret)


def test_external_call_target_without_library_is_not_used_as_summary_seed():
    ret = ReturnInfo(
        address="0x1000",
        value=Expression(
            ExpressionType.CALL,
            name="external_helper",
            operands=[Expression.parameter("x", 0, size=4)],
            runtime_ref=CallTargetRef.from_name("external_helper", is_external=True),
        ),
        return_kind="exact",
    )

    assert not _return_is_exact_seed(ret)


def test_custom_resolved_call_runtime_ref_can_remain_summary_seed():
    ret = ReturnInfo(
        address="0x1000",
        value=Expression(
            ExpressionType.CALL,
            name="resolved_helper",
            operands=[Expression.parameter("x", 0, size=4)],
            runtime_ref=_ResolvedCallRuntimeRef(),
        ),
        return_kind="exact",
    )

    assert _return_is_exact_seed(ret)


def test_analysis_key_none_resolved_call_runtime_ref_is_not_used_as_summary_seed():
    ret = ReturnInfo(
        address="0x1000",
        value=Expression(
            ExpressionType.CALL,
            name="analysis_key_none_helper",
            operands=[Expression.parameter("x", 0, size=4)],
            runtime_ref=_AnalysisKeyNoneResolvedCallRuntimeRef(),
        ),
        return_kind="exact",
    )

    assert not _return_is_exact_seed(ret)


def test_marker_only_resolved_call_runtime_ref_is_not_used_as_summary_seed():
    ret = ReturnInfo(
        address="0x1000",
        value=Expression(
            ExpressionType.CALL,
            name="marker_only_helper",
            operands=[Expression.parameter("x", 0, size=4)],
            runtime_ref=_MarkerOnlyResolvedCallRuntimeRef(),
        ),
        return_kind="exact",
    )

    assert not _return_is_exact_seed(ret)


def test_placeholder_resolved_call_runtime_ref_is_not_used_as_summary_seed():
    ret = ReturnInfo(
        address="0x1000",
        value=Expression(
            ExpressionType.CALL,
            name="placeholder_helper",
            operands=[Expression.parameter("x", 0, size=4)],
            runtime_ref=_PlaceholderResolvedCallRuntimeRef(),
        ),
        return_kind="exact",
    )

    assert not _return_is_exact_seed(ret)


def test_string_key_resolved_call_runtime_ref_is_not_used_as_summary_seed():
    ret = ReturnInfo(
        address="0x1000",
        value=Expression(
            ExpressionType.CALL,
            name="string_key_helper",
            operands=[Expression.parameter("x", 0, size=4)],
            runtime_ref=_StringKeyResolvedCallRuntimeRef(),
        ),
        return_kind="exact",
    )

    assert not _return_is_exact_seed(ret)


def test_empty_tuple_key_resolved_call_runtime_ref_is_not_used_as_summary_seed():
    ret = ReturnInfo(
        address="0x1000",
        value=Expression(
            ExpressionType.CALL,
            name="empty_tuple_key_helper",
            operands=[Expression.parameter("x", 0, size=4)],
            runtime_ref=_EmptyTupleKeyResolvedCallRuntimeRef(),
        ),
        return_kind="exact",
    )

    assert not _return_is_exact_seed(ret)


def test_custom_unresolved_call_runtime_ref_is_not_used_as_summary_seed():
    ret = ReturnInfo(
        address="0x1000",
        value=Expression(
            ExpressionType.CALL,
            name="unresolved_helper",
            operands=[Expression.parameter("x", 0, size=4)],
            runtime_ref=_UnresolvedCallRuntimeRef(),
        ),
        return_kind="exact",
    )

    assert not _return_is_exact_seed(ret)


def test_deferred_call_exact_return_is_not_used_as_summary_seed():
    ret = ReturnInfo(
        address="0x1000",
        value=Expression(
            ExpressionType.CALL,
            name="deferred_helper",
            operands=[Expression.parameter("x", 0, size=4)],
            runtime_ref=UnknownValueRef.deferred_call(placeholder_name="deferred_helper"),
        ),
        return_kind="exact",
    )

    assert not _return_is_exact_seed(ret)


def test_deferred_call_ref_exact_return_is_not_used_as_summary_seed():
    ret = ReturnInfo(
        address="0x1000",
        value=Expression(
            ExpressionType.CALL,
            name="deferred_helper",
            operands=[Expression.parameter("x", 0, size=4)],
            runtime_ref=DeferredCallRef(
                target_ref=CallTargetRef.from_name("deferred_helper"),
                sequence=1,
            ),
        ),
        return_kind="exact",
    )

    assert not _return_is_exact_seed(ret)


def _empty_effect_summary() -> EffectSummary:
    return EffectSummary(parameter_names=["n"], effects=[])


def test_summary_candidate_acceptance_uses_proposed_partition_before_returns_merge():
    analysis = _analysis_with_exact_returns(effect_summary=_empty_effect_summary())
    n = _n()
    summary_return = _with_summary_proof(ReturnInfo(
        address="0x1008",
        value=_summary_const(2),
        conditions=[_cond("INT_SLESS", _const(1), n)],
        pcode_identity="summary:n_gt_one",
    ))

    result = accept_summary_return_candidates(
        analysis,
        [*analysis.returns, summary_return],
        summary_note="barthe2big_counted_loop_summary",
    )

    assert result.blockers == ()
    assert result.coverage_complete is True
    assert len(result.accepted_returns) == 3
    assert len(analysis.returns) == 2
    accepted_summary = result.accepted_returns[-1]
    assert accepted_summary.return_kind == "summary_derived"
    assert accepted_summary.acceptance_status == "accepted"
    assert accepted_summary.summary_candidate_id is not None


def test_summary_candidate_missing_effect_evidence_is_not_accepted_or_merged():
    analysis = _analysis_with_exact_returns(effect_summary=None)
    n = _n()
    summary_return = _with_summary_proof(ReturnInfo(
        address="0x1008",
        value=_summary_const(2),
        conditions=[_cond("INT_SLESS", _const(1), n)],
        pcode_identity="summary:n_gt_one",
    ))

    result = accept_summary_return_candidates(
        analysis,
        [*analysis.returns, summary_return],
        summary_note="barthe2big_counted_loop_summary",
    )

    assert result.accepted_returns == ()
    assert "summary_effect_unmodeled:effect_summary_missing" in result.blockers
    effect_occurrence = next(
        item for item in result.blocker_occurrences
        if item.source_code == "summary_effect_unmodeled:effect_summary_missing"
    )
    assert effect_occurrence.candidate_id == result.candidates[0].candidate_id
    assert effect_occurrence.peer_return_identity is None
    assert effect_occurrence.function_identity == analysis.outcome_function_identity()
    assert len(analysis.returns) == 2
    assert all(ret.return_kind == "exact" for ret in analysis.returns)


def test_summary_candidate_blocker_is_exposed_as_structured_reason():
    analysis = _analysis_with_exact_returns(effect_summary=None)
    n = _n()
    summary_return = _with_summary_proof(ReturnInfo(
        address="0x1008",
        value=_summary_const(2),
        conditions=[_cond("INT_SLESS", _const(1), n)],
        pcode_identity="summary:n_gt_one",
    ))

    result = accept_summary_return_candidates(
        analysis,
        [*analysis.returns, summary_return],
        summary_note="barthe2big_counted_loop_summary",
    )
    analysis.summary_return_candidates = result.candidates

    reason_ids = CheckStrategy._summary_return_candidate_blocker_reason_ids(analysis)

    assert reason_ids == (UnknownReasonId.SUMMARY_EFFECT_UNMODELED.value,)
    definition = get_unknown_reason_definition(UnknownReasonId.SUMMARY_EFFECT_UNMODELED)
    assert definition.target_regression == "summary_effect_unmodeled"
    mapped = CheckStrategy._unknown_reason_id_for_blocking_unsafety(
        _ReasonMappingHarness(),
        "function1:summary_effect_unmodeled",
    )
    assert mapped == UnknownReasonId.SUMMARY_EFFECT_UNMODELED


def test_summary_candidate_overlap_requires_value_equality_proof():
    analysis = _analysis_with_exact_returns(effect_summary=_empty_effect_summary())
    n = _n()
    overlapping_summary = _with_summary_proof(ReturnInfo(
        address="0x1008",
        value=_summary_const(2),
        conditions=[_cond("INT_SLESS", _const(0), n)],
        pcode_identity="summary:n_positive",
    ))

    result = accept_summary_return_candidates(
        analysis,
        [analysis.returns[0], overlapping_summary],
        summary_note="barthe2big_counted_loop_summary",
    )

    assert result.accepted_returns == ()
    assert "summary_return_overlap_unproven:value_equality_not_proved" in result.blockers
    overlap_occurrence = next(
        item for item in result.blocker_occurrences
        if item.source_code
        == "summary_return_overlap_unproven:value_equality_not_proved"
    )
    assert overlap_occurrence.candidate_id == result.candidates[0].candidate_id
    assert overlap_occurrence.peer_return_identity is not None
    assert overlap_occurrence.function_identity == analysis.outcome_function_identity()
    assert len(analysis.returns) == 2


def test_return_region_summary_proof_can_supersede_imprecise_exact_return():
    analysis = _analysis_with_exact_returns(effect_summary=_empty_effect_summary())
    n = _n()
    positive_summary, evidence = _with_return_region_summary_proof(
        ReturnInfo(
            address="0x1008",
            value=_summary_const(2),
            conditions=[_cond("INT_SLESS", _const(0), n)],
            pcode_identity="summary:n_positive",
        ),
        superseded_return_keys=(_return_info_identity_key(analysis.returns[1]),),
    )
    analysis.completed_recovery_proof_evidence = (evidence,)

    result = accept_summary_return_candidates(
        analysis,
        [analysis.returns[0], positive_summary],
        summary_note="multiplicative_phi_return_region_summary",
    )

    assert result.blockers == ()
    assert result.coverage_complete is True
    assert tuple(ret.pcode_identity for ret in result.accepted_returns) == (
        "return:non_positive",
        "summary:n_positive",
    )


def test_return_region_summary_superseded_key_proves_overlap_for_non_exact_witness_key():
    analysis = _analysis_with_exact_returns(effect_summary=_empty_effect_summary())
    n = _n()
    positive_summary, evidence = _with_return_region_summary_proof(
        ReturnInfo(
            address="0x1008",
            value=_summary_const(2),
            conditions=[_cond("INT_SLESS", _const(0), n)],
            pcode_identity="summary:n_positive",
        ),
        exact_witnesses_key=(
            "readonly_reduction_accumulator_witness",
            ("proof", "unit_test"),
            ("contract", "unit_test"),
            (),
            (),
        ),
        superseded_return_keys=(_return_info_identity_key(analysis.returns[1]),),
    )
    analysis.completed_recovery_proof_evidence = (evidence,)

    result = accept_summary_return_candidates(
        analysis,
        [analysis.returns[0], analysis.returns[1], positive_summary],
        summary_note="readonly_pointer_reduction_summary",
    )

    assert result.blockers == ()
    assert result.coverage_complete is True
    assert tuple(ret.pcode_identity for ret in result.accepted_returns) == (
        "return:non_positive",
        "summary:n_positive",
    )


def test_return_region_summary_supersede_requires_target_content_match():
    analysis = _analysis_with_exact_returns(effect_summary=_empty_effect_summary())
    n = _n()
    positive_summary, evidence = _with_return_region_summary_proof(
        ReturnInfo(
            address="0x1008",
            value=_summary_const(2),
            conditions=[_cond("INT_SLESS", _const(0), n)],
            pcode_identity="summary:n_positive",
        ),
        superseded_return_keys=(_return_info_identity_key(analysis.returns[1]),),
        content_superseded_return_keys=(_return_info_identity_key(analysis.returns[0]),),
    )
    analysis.completed_recovery_proof_evidence = (evidence,)

    result = accept_summary_return_candidates(
        analysis,
        [analysis.returns[0], positive_summary],
        summary_note="multiplicative_phi_return_region_summary",
    )

    assert result.accepted_returns == ()
    assert result.blockers


def test_return_region_production_object_proved_is_not_completed_coverage_proof():
    analysis = _analysis_with_exact_returns(effect_summary=_empty_effect_summary())
    n = _n()
    summary_return, evidence = _with_return_region_summary_proof(
        ReturnInfo(
            address="0x1008",
            value=_summary_const(2),
            conditions=[_cond("INT_SLESS", _const(1), n)],
            pcode_identity="summary:n_gt_one",
        ),
        coverage_status="production_object_proved",
    )
    analysis.completed_recovery_proof_evidence = (evidence,)

    result = accept_summary_return_candidates(
        analysis,
        [*analysis.returns, summary_return],
        summary_note="barthe2big_counted_loop_summary",
    )

    assert result.accepted_returns == ()
    assert "summary_return_candidate_invalid:transition_evidence_incomplete" in result.blockers


def test_return_region_proof_does_not_skip_overlap_value_for_non_witness_exact_return():
    analysis = _analysis_with_exact_returns(effect_summary=_empty_effect_summary())
    n = _n()
    overlapping_summary, evidence = _with_return_region_summary_proof(
        ReturnInfo(
            address="0x1008",
            value=_summary_const(2),
            conditions=[_cond("INT_SLESS", _const(0), n)],
            pcode_identity="summary:n_positive",
        ),
        coverage_status="proved",
        exact_witnesses_key=("exact_return_witnesses", ()),
    )
    analysis.completed_recovery_proof_evidence = (evidence,)

    result = accept_summary_return_candidates(
        analysis,
        [*analysis.returns, overlapping_summary],
        summary_note="barthe2big_counted_loop_summary",
    )

    assert result.accepted_returns == ()
    assert "summary_return_overlap_unproven:value_equality_not_proved" in result.blockers


def test_summary_candidate_non_total_partition_keeps_coverage_gap():
    analysis = _analysis_with_exact_returns(effect_summary=_empty_effect_summary())
    n = _n()
    only_large_n = _with_summary_proof(ReturnInfo(
        address="0x1008",
        value=_summary_const(2),
        conditions=[_cond("INT_SLESS", _const(2), n)],
        pcode_identity="summary:n_gt_two",
    ))

    result = accept_summary_return_candidates(
        analysis,
        [*analysis.returns, only_large_n],
        summary_note="barthe2big_counted_loop_summary",
    )

    assert result.accepted_returns == ()
    assert "summary_partition_not_total:active_precondition_not_covered" in result.blockers
    assert len(analysis.returns) == 2


def test_summary_candidate_partition_does_not_treat_return_region_proof_as_total_coverage():
    analysis = _analysis_with_exact_returns(effect_summary=_empty_effect_summary())
    n = _n()
    only_large_n, evidence = _with_return_region_summary_proof(ReturnInfo(
        address="0x1008",
        value=_summary_const(2),
        conditions=[_cond("INT_SLESS", _const(2), n)],
        pcode_identity="summary:n_gt_two",
    ))
    analysis.completed_recovery_proof_evidence = (evidence,)

    result = accept_summary_return_candidates(
        analysis,
        [*analysis.returns, only_large_n],
        summary_note="readonly_pointer_reduction_summary",
    )

    assert result.accepted_returns == ()
    assert result.coverage_complete is False
    assert "summary_partition_not_total:active_precondition_not_covered" in result.blockers


def test_summary_partition_coverage_rejects_duplicate_name_only_guard_canonicalization():
    indexed_n = Expression.parameter("n", index=1, size=4)
    name_only_n = Expression.parameter("n", index=-1, size=4)
    exact_nonpositive = ReturnInfo(
        address="0x1000",
        value=_const(0),
        conditions=[_cond("INT_SLESS", indexed_n, _const(1))],
        pcode_identity="return:n1_nonpositive",
    )
    summary_positive = ReturnInfo(
        address="0x1004",
        value=_summary_const(1),
        conditions=[_cond("INT_SLESSEQUAL", _const(1), name_only_n)],
        pcode_identity="summary:name_only_positive",
        return_kind="summary_derived",
    )
    parameters = [
        _param("n", index=0),
        _param("n", index=1),
    ]

    normalized_summary = _canonicalize_conditions_for_analysis_parameters(
        summary_positive.conditions,
        parameters,
    )

    assert normalized_summary[0].expression.operands[1].value == -1
    assert _return_partition_covers_active_precondition(
        (exact_nonpositive, summary_positive),
        (),
        parameters=parameters,
    ) is False


def test_summary_partition_coverage_accepts_full_width_masked_singleton_gap():
    pointer = Expression.parameter("param_1", index=0, size=8)
    count = Expression.parameter("param_2", index=1, size=4)
    pointer_nonnull = _cond("INT_NOTEQUAL", pointer, _const(0, size=8))
    pointer_null = _cond("INT_EQUAL", pointer, _const(0, size=8))
    count_positive = _cond("INT_SLESS", _const(0), count)
    count_nonpositive = Condition(count_positive.expression, negated=True)
    count_not_one = Condition(
        Expression.binary_op("INT_EQUAL", count, _const(1)),
        negated=True,
    )
    masked = Expression.binary_op("INT_AND", count, _const(0xFFFFFFFF))
    masked.size = 4
    masked_selector = Expression.binary_op(
        "INT_NOTEQUAL",
        Expression.binary_op("INT_SUB", masked, _const(1)),
        _const(0),
    )
    masked_selector.size = 1
    exact_one = ReturnInfo(
        address="0x1000",
        value=_const(1),
        conditions=[pointer_nonnull, count_positive, Condition(masked_selector, negated=True)],
        pcode_identity="return:count_one",
    )
    exact_null = ReturnInfo(
        address="0x1004",
        value=_const(0),
        conditions=[pointer_null],
        pcode_identity="return:null",
    )
    exact_nonpositive = ReturnInfo(
        address="0x1008",
        value=_const(0),
        conditions=[pointer_nonnull, count_nonpositive],
        pcode_identity="return:nonpositive",
    )
    summary = ReturnInfo(
        address="0x100c",
        value=_summary_const(2),
        conditions=[pointer_nonnull, count_positive, count_not_one],
        pcode_identity="summary:positive_not_one",
        return_kind="summary_derived",
    )
    parameters = [
        _param("param_1", index=0, size=8),
        _param("param_2", index=1, size=4),
    ]

    assert _return_partition_covers_active_precondition(
        (exact_one, exact_null, exact_nonpositive, summary),
        (),
        parameters=parameters,
    )


def test_summary_partition_coverage_does_not_canonicalize_partial_mask_singleton():
    count = Expression.parameter("param_2", index=1, size=4)
    masked = Expression.binary_op("INT_AND", count, _const(0xFFFF))
    masked.size = 4
    masked_selector = Expression.binary_op(
        "INT_NOTEQUAL",
        Expression.binary_op("INT_SUB", masked, _const(1)),
        _const(0),
    )
    masked_selector.size = 1

    assert _full_width_mask_singleton_condition(Condition(masked_selector, negated=True)) is None


def test_summary_partition_coverage_canonicalizes_commuted_mask_equal_sub_zero():
    count = Expression.parameter("param_2", index=1, size=4)
    masked = Expression.binary_op("INT_AND", _const(0xFFFFFFFF), count)
    masked.size = 4
    selector = Expression.binary_op(
        "INT_EQUAL",
        Expression.binary_op("INT_SUB", masked, _const(1)),
        _const(0),
    )
    selector.size = 1

    canonical = _full_width_mask_singleton_condition(Condition(selector, negated=False))

    assert canonical is not None
    assert canonical.to_string() == "(param_2 == 1)"


def test_masked_singleton_condition_implies_count_value_for_overlap_proof():
    count = Expression.parameter("param_2", index=1, size=4)
    masked = Expression.binary_op("INT_AND", _const(0xFFFFFFFF), count)
    masked.size = 4
    selector = Expression.binary_op(
        "INT_EQUAL",
        Expression.binary_op("INT_SUB", masked, _const(1)),
        _const(0),
    )
    selector.size = 1

    assert _conditions_imply_count_value([Condition(selector, negated=False)], count, 1)
    assert not _conditions_imply_count_value([Condition(selector, negated=False)], count, 2)


def test_count_value_proof_rejects_same_index_storage_mismatch():
    proof_count = Expression.parameter(
        "count",
        index=1,
        size=4,
        storage_info=_FakeStorageInfo(("register_storage", "a1")),
    )
    other_storage_count = Expression.parameter(
        "count",
        index=1,
        size=4,
        storage_info=_FakeStorageInfo(("register_storage", "a2")),
    )
    selector = _cond("INT_EQUAL", other_storage_count, _const(1))

    assert not _conditions_imply_count_value([selector], proof_count, 1)


def test_readonly_summary_overlap_proves_masked_count_one_exact_return():
    pointer = Expression.parameter("param_1", index=0, data_type="int *", size=8)
    count = Expression.parameter("param_2", index=1, data_type="int", size=4)
    proof = ReductionAccumulatorProof(
        reduction_kind="memory_sum",
        pointer_base_ref=LocationBaseRef.parameter("param_1", index=0),
        count_parameter_name="param_2",
        count_parameter_index=1,
        limit_expr=count,
        result_size=4,
        stride=4,
        element_size=4,
        start_offset=0,
        start_index=0,
        index_step=1,
        index_scale=4,
        guard_constraints=(_cond("INT_SLESS", _const(0), count),),
        signed_counter=True,
    )
    reduction_ref = proof.lower_to_readonly_reduction_ref()
    assert reduction_ref is not None
    summary_value = Expression.intrinsic("READONLY_SUM", [pointer, count], size=4, runtime_ref=reduction_ref)
    summary_ret = _with_summary_proof(ReturnInfo(
        address="0x1004",
        value=summary_value,
        conditions=[
            _cond("INT_NOTEQUAL", pointer, _const(0, size=8)),
            _cond("INT_SLESS", _const(0), count),
            Condition(Expression.binary_op("INT_EQUAL", count, _const(1)), negated=True),
        ],
        pcode_identity="summary:positive_not_one",
    ))
    masked = Expression.binary_op("INT_AND", _const(0xFFFFFFFF), count)
    masked.size = 4
    selector = Expression.binary_op(
        "INT_EQUAL",
        Expression.binary_op("INT_SUB", masked, _const(1)),
        _const(0),
    )
    selector.size = 1
    exact_ret = ReturnInfo(
        address="0x1000",
        value=Expression.binary_op("INT_ADD", Expression.memory(pointer, size=4), _const(0)),
        conditions=[
            _cond("INT_NOTEQUAL", pointer, _const(0, size=8)),
            _cond("INT_SLESS", _const(0), count),
            Condition(selector, negated=False),
        ],
        pcode_identity="return:count_one",
    )
    analysis = FunctionReturnAnalysis(
        function_name="f",
        entry_point="0x1000",
        parameters=[_param("param_1", index=0, size=8), _param("param_2", index=1, size=4)],
        returns=[exact_ret],
        return_type="int",
        effect_summary=_empty_effect_summary(),
    )

    assert _readonly_reduction_exact_overlap_is_proved(exact_ret, summary_ret, (), analysis)


def test_readonly_summary_overlap_uses_return_region_value_proof_for_same_site_artifact():
    pointer = Expression.parameter("param_1", index=0, data_type="int *", size=8)
    count = Expression.parameter("param_2", index=1, data_type="int", size=4)
    return_ref = PcodeOpRef(address_offset=0x1000, seq_time=30, seq_order=2, mnemonic="RETURN")
    value_ref = PcodeOpRef(address_offset=0x1000, seq_time=29, seq_order=1, mnemonic="COPY")
    proof = ReductionAccumulatorProof(
        reduction_kind="memory_sum",
        pointer_base_ref=LocationBaseRef.parameter("param_1", index=0),
        count_parameter_name="param_2",
        count_parameter_index=1,
        limit_expr=count,
        result_size=4,
        stride=4,
        element_size=4,
        start_offset=0,
        start_index=0,
        index_step=1,
        index_scale=4,
        guard_constraints=(_cond("INT_SLESS", _const(0), count),),
        signed_counter=True,
        return_op_refs=(return_ref,),
        return_value_op_refs=(value_ref,),
        return_region_value_proven=True,
    )
    reduction_ref = proof.lower_to_readonly_reduction_ref()
    assert reduction_ref is not None
    summary_ret = ReturnInfo(
        address="0x1000",
        value=Expression.intrinsic("READONLY_SUM", [pointer, count], size=4, runtime_ref=reduction_ref),
        conditions=[_cond("INT_NOTEQUAL", pointer, _const(0, size=8)), _cond("INT_SLESS", _const(0), count)],
        pcode_identity="summary:positive",
        return_kind="summary_derived",
    )
    same_site_artifact = ReturnInfo(
        address="0x1000",
        value=Expression.binary_op("INT_ADD", Expression.memory(pointer, size=4), _const(0)),
        conditions=[_cond("INT_NOTEQUAL", pointer, _const(0, size=8)), _cond("INT_SLESS", _const(0), count)],
        pcode_identity="0x1000:t30",
        pcode_time=30,
        pcode_order=2,
    )
    other_site_artifact = replace(same_site_artifact, address="0x2000", pcode_identity="0x2000:t30")
    analysis = FunctionReturnAnalysis(
        function_name="f",
        entry_point="0x1000",
        parameters=[_param("param_1", index=0, size=8), _param("param_2", index=1, size=4)],
        returns=[same_site_artifact],
        return_type="int",
        effect_summary=_empty_effect_summary(),
    )

    assert _readonly_reduction_exact_overlap_is_proved(same_site_artifact, summary_ret, (), analysis)
    assert not _readonly_reduction_exact_overlap_is_proved(other_site_artifact, summary_ret, (), analysis)


def test_ptradd_index_equality_implies_masked_count_singleton():
    base = Expression.parameter("param_1", index=0, size=8)
    count = Expression.parameter("param_2", index=1, data_type="int", size=8)
    low_count = Expression.binary_op("SUBPIECE", count, _const(0))
    low_count.size = 4
    masked = Expression.binary_op("INT_AND", low_count, _const(0xFFFFFFFF))
    masked.size = 4
    minus_one = Expression.binary_op("INT_SUB", masked, _const(1))
    minus_one.size = 4
    widened = Expression.unary_op("INT_ZEXT", minus_one)
    widened.size = 8
    index = Expression.binary_op("INT_ADD", _const(1, size=8), widened)
    index.size = 8
    dynamic_ptr = Expression.intrinsic("PTRADD", [base, index, _const(4, size=8)], size=8)
    fixed_ptr = Expression.intrinsic("PTRADD", [base, _const(1, size=8), _const(4, size=8)], size=8)
    selector = _cond("INT_EQUAL", dynamic_ptr, fixed_ptr)

    assert _conditions_imply_count_value([selector], count, 1)
    assert not _conditions_imply_count_value([selector], count, 2)


def test_ptradd_index_equality_does_not_match_different_base_or_scale():
    base = Expression.parameter("param_1", index=0, size=8)
    other_base = Expression.parameter("param_3", index=2, size=8)
    count = Expression.parameter("param_2", index=1, data_type="int", size=4)
    index = Expression.binary_op("INT_ADD", _const(1), Expression.binary_op("INT_SUB", count, _const(1)))
    index.size = 4
    dynamic_ptr = Expression.intrinsic("PTRADD", [base, index, _const(4, size=8)], size=8)
    different_base = Expression.intrinsic("PTRADD", [other_base, _const(1), _const(4, size=8)], size=8)
    different_scale = Expression.intrinsic("PTRADD", [base, _const(1), _const(8, size=8)], size=8)

    assert not _conditions_imply_count_value([_cond("INT_EQUAL", dynamic_ptr, different_base)], count, 1)
    assert not _conditions_imply_count_value([_cond("INT_EQUAL", dynamic_ptr, different_scale)], count, 1)


def test_resolved_phi_expansion_counts_as_exact_seed_for_partition_coverage():
    n = _n()
    analysis = FunctionReturnAnalysis(
        function_name="f",
        entry_point="0x1000",
        parameters=[_param()],
        returns=[
            ReturnInfo(
                address="0x1000",
                value=_const(0),
                conditions=[_cond("INT_SLESSEQUAL", n, _const(0))],
                pcode_identity="return:non_positive",
                return_kind="phi_expansion",
            ),
        ],
        return_type="int",
        effect_summary=_empty_effect_summary(),
    )
    positive_summary = _with_summary_proof(ReturnInfo(
        address="0x1008",
        value=_summary_const(2),
        conditions=[_cond("INT_SLESS", _const(0), n)],
        pcode_identity="summary:n_positive",
    ))

    result = accept_summary_return_candidates(
        analysis,
        [analysis.returns[0], positive_summary],
        summary_note="state_transition_loop_summary",
    )

    assert result.blockers == ()
    assert result.coverage_complete is True
    assert tuple(ret.pcode_identity for ret in result.accepted_returns) == (
        "return:non_positive",
        "summary:n_positive",
    )


def test_unresolved_phi_expansion_is_not_exact_seed_for_partition_coverage():
    n = _n()
    analysis = FunctionReturnAnalysis(
        function_name="f",
        entry_point="0x1000",
        parameters=[_param()],
        returns=[
            ReturnInfo(
                address="0x1000",
                value=Expression.unknown("phi_circular"),
                conditions=[_cond("INT_SLESSEQUAL", n, _const(0))],
                pcode_identity="return:non_positive",
                return_kind="phi_expansion",
            ),
        ],
        return_type="int",
        effect_summary=_empty_effect_summary(),
    )
    positive_summary = _with_summary_proof(ReturnInfo(
        address="0x1008",
        value=_summary_const(2),
        conditions=[_cond("INT_SLESS", _const(0), n)],
        pcode_identity="summary:n_positive",
    ))

    result = accept_summary_return_candidates(
        analysis,
        [analysis.returns[0], positive_summary],
        summary_note="state_transition_loop_summary",
    )

    assert result.accepted_returns == ()
    assert "summary_partition_not_total:active_precondition_not_covered" in result.blockers


def test_multiple_summary_candidates_overlap_requires_value_equality_proof():
    analysis = _analysis_with_exact_returns(effect_summary=_empty_effect_summary())
    n = _n()
    summary_one = _with_summary_proof(ReturnInfo(
        address="0x1008",
        value=_summary_const(1),
        conditions=[_cond("INT_SLESS", _const(1), n)],
        pcode_identity="summary:n_gt_one",
    ))
    summary_two = _with_summary_proof(ReturnInfo(
        address="0x100c",
        value=_summary_const(3),
        conditions=[_cond("INT_SLESS", _const(2), n)],
        pcode_identity="summary:n_gt_two",
    ))

    result = accept_summary_return_candidates(
        analysis,
        [*analysis.returns, summary_one, summary_two],
        summary_note="barthe2big_counted_loop_summary",
    )

    assert result.accepted_returns == ()
    assert "summary_return_overlap_unproven:value_equality_not_proved" in result.blockers
    assert len(analysis.returns) == 2


def test_direct_negated_fallback_does_not_conflate_width_mismatch():
    n32 = Expression.parameter("n", index=0, data_type="int", size=4)
    n64 = Expression.parameter("n", index=0, data_type="long", size=8)
    narrow_positive = _cond("INT_SLESS", _const(0, size=4), n32)
    wide_nonpositive = _cond("INT_SLESS", _const(0, size=8), n64).negate()

    assert _conditions_unsat([narrow_positive, wide_nonpositive]) is not True


def test_readonly_term_descriptor_rejects_width_changing_cast():
    pointer = Expression.parameter("p", index=0, data_type="int *", size=8)
    memory = Expression.memory(pointer, size=4)
    widening_cast = Expression.unary_op("CAST", memory)
    widening_cast.size = 8
    no_op_cast = Expression.unary_op("CAST", memory)
    no_op_cast.size = 4
    parameters = [{"name": "p", "index": 0, "size": 8, "data_type": "int *"}]
    base_ref = LocationBaseRef.parameter("p", index=0)

    assert _extract_readonly_reduction_term_descriptor(widening_cast, parameters, base_ref) is None
    descriptor = _extract_readonly_reduction_term_descriptor(no_op_cast, parameters, base_ref)
    assert descriptor is not None
    assert descriptor.stable_key() == ("readonly_reduction_term", 0, 4)


def test_reduction_count_parameter_expression_rejects_index_storage_mismatch():
    proof_storage = ("register_storage", "a1")
    other_storage = ("register_storage", "a2")
    proof = _FakeAccumulatorProof(index=1, storage_key=proof_storage, name="count")
    parameters = [
        {
            "name": "count",
            "index": 1,
            "size": 4,
            "storage_info": _FakeStorageInfo(other_storage),
        }
    ]

    assert _reduction_count_parameter_expression(parameters, proof) is None


def test_reduction_count_parameter_expression_matches_raw_storage_identity():
    proof_storage = ("register_storage", "a1")
    proof = _FakeAccumulatorProof(index=1, storage_key=proof_storage, name="count")
    parameters = [
        {
            "name": "count",
            "index": 1,
            "size": 4,
            "storage_info": _FakeStorageInfo(proof_storage),
        }
    ]

    expr = _reduction_count_parameter_expression(parameters, proof)

    assert expr is not None
    assert expr.name == "count"
    assert expr.value == 1


def test_reduction_count_parameter_expression_unwraps_legacy_storage_identity():
    proof_storage = ("register_storage", "a1")
    proof = _FakeAccumulatorProof(index=1, storage_key=proof_storage, name="count")
    parameters = [
        {
            "name": "count",
            "index": 1,
            "size": 4,
            "storage_identity_key": ("parameter_storage", proof_storage),
        }
    ]

    expr = _reduction_count_parameter_expression(parameters, proof)

    assert expr is not None
    assert expr.name == "count"


def test_summary_candidate_without_loop_identity_is_rejected():
    analysis = _analysis_with_exact_returns(effect_summary=_empty_effect_summary())
    n = _n()
    summary_return = ReturnInfo(
        address="0x1008",
        value=_const(2),
        conditions=[_cond("INT_SLESS", _const(1), n)],
        pcode_identity="summary:n_gt_one",
        return_kind="summary_derived",
    )

    result = accept_summary_return_candidates(
        analysis,
        [*analysis.returns, summary_return],
        summary_note="barthe2big_counted_loop_summary",
    )

    assert result.accepted_returns == ()
    assert "summary_return_candidate_invalid:loop_summary_identity_missing" in result.blockers
    assert "summary_return_candidate_invalid:transition_evidence_missing" in result.blockers
    assert len(analysis.returns) == 2


def test_summary_candidate_does_not_drop_original_exact_returns():
    analysis = _analysis_with_exact_returns(effect_summary=_empty_effect_summary())
    n = _n()
    summary_return = _with_summary_proof(ReturnInfo(
        address="0x1008",
        value=_summary_const(2),
        conditions=[_cond("INT_SLESS", _const(1), n)],
        pcode_identity="summary:n_gt_one",
    ))

    result = accept_summary_return_candidates(
        analysis,
        [analysis.returns[0], summary_return],
        summary_note="barthe2big_counted_loop_summary",
    )

    assert result.blockers == ()
    assert len(result.accepted_returns) == 3
    assert result.accepted_returns[0] is analysis.returns[0]
    assert result.accepted_returns[1] is analysis.returns[1]
    assert result.accepted_returns[2].return_kind == "summary_derived"


def test_summary_candidate_unmodeled_memory_read_is_rejected():
    analysis = _analysis_with_exact_returns(effect_summary=_empty_effect_summary())
    n = _n()
    memory_value = Expression.memory(Expression.parameter("p", 1, size=8), size=4)
    summary_value = Expression.binary_op("INT_ADD", memory_value, _summary_const(0))
    summary_return = _with_summary_proof(ReturnInfo(
        address="0x1008",
        value=summary_value,
        conditions=[_cond("INT_SLESS", _const(1), n)],
        pcode_identity="summary:n_gt_one",
    ))

    result = accept_summary_return_candidates(
        analysis,
        [*analysis.returns, summary_return],
        summary_note="barthe2big_counted_loop_summary",
    )

    assert result.accepted_returns == ()
    assert "summary_effect_unmodeled:memory_read_unmodeled" in result.blockers
    assert len(analysis.returns) == 2


def test_summary_candidate_respects_active_precondition_in_coverage_proof():
    analysis = _analysis_with_exact_returns(effect_summary=_empty_effect_summary())
    n = _n()
    analysis.active_function_preconditions = (
        _cond("INT_SLESS", _const(0), n),
    )
    summary_return = _with_summary_proof(ReturnInfo(
        address="0x1008",
        value=_summary_const(2),
        conditions=[_cond("INT_SLESS", _const(1), n)],
        pcode_identity="summary:n_gt_one",
    ))

    result = accept_summary_return_candidates(
        analysis,
        [summary_return],
        summary_note="barthe2big_counted_loop_summary",
    )

    assert result.blockers == ()
    assert len(result.accepted_returns) == 3


def test_pre_return_summary_anchor_is_not_merged_as_exact_return():
    n = _n()
    anchor = ReturnInfo(
        address="0x2000",
        value=Expression.unknown("pre_return_counted_loop_candidate"),
        conditions=[],
        pcode_identity="anchor",
        return_kind="summary_anchor",
        acceptance_status="anchor",
    )
    analysis = FunctionReturnAnalysis(
        function_name="f",
        entry_point="0x1000",
        parameters=[_param()],
        returns=[anchor],
        return_type="int",
        effect_summary=_empty_effect_summary(),
        binary_id="barthe2big-test-binary",
    )
    base_return = _with_summary_proof(ReturnInfo(
        address="0x2004",
        value=_summary_const(1),
        conditions=[_cond("INT_SLESSEQUAL", n, _const(0))],
        pcode_identity="summary:n_non_positive",
        return_kind="summary_derived",
    ))
    loop_return = _with_summary_proof(ReturnInfo(
        address="0x2008",
        value=_summary_const(2),
        conditions=[_cond("INT_SLESS", _const(0), n)],
        pcode_identity="summary:n_positive",
        return_kind="summary_derived",
    ))

    result = accept_summary_return_candidates(
        analysis,
        [base_return, loop_return],
        summary_note="pre_return_counted_loop_summary",
    )

    assert result.blockers == ()
    assert [ret.return_kind for ret in result.accepted_returns] == ["summary_derived", "summary_derived"]
    assert all(
        getattr(ret.value, "name", None) != "pre_return_counted_loop_candidate"
        for ret in result.accepted_returns
    )


def test_summary_candidate_without_transition_evidence_is_rejected():
    analysis = _analysis_with_exact_returns(effect_summary=_empty_effect_summary())
    n = _n()
    summary_return = ReturnInfo(
        address="0x1008",
        value=_summary_const(2),
        conditions=[_cond("INT_SLESS", _const(1), n)],
        pcode_identity="summary:n_gt_one",
        summary_candidate_source_key=_SUMMARY_SOURCE_KEY,
    )

    result = accept_summary_return_candidates(
        analysis,
        [*analysis.returns, summary_return],
        summary_note="barthe2big_counted_loop_summary",
    )

    assert result.accepted_returns == ()
    assert "summary_return_candidate_invalid:transition_evidence_missing" in result.blockers


def test_summary_candidate_without_accumulator_base_evidence_is_rejected():
    analysis = _analysis_with_exact_returns(effect_summary=_empty_effect_summary())
    n = _n()
    incomplete_transition_key = tuple(
        part
        for part in _SUMMARY_TRANSITION_KEY
        if not (isinstance(part, tuple) and part[:1] == ("accumulator_base",))
    )
    summary_return = _with_summary_proof(ReturnInfo(
        address="0x1008",
        value=_summary_const(2),
        conditions=[_cond("INT_SLESS", _const(1), n)],
        pcode_identity="summary:n_gt_one",
    ))
    summary_return.summary_transition_evidence_key = incomplete_transition_key

    result = accept_summary_return_candidates(
        analysis,
        [*analysis.returns, summary_return],
        summary_note="barthe2big_counted_loop_summary",
    )

    assert result.accepted_returns == ()
    assert "summary_return_candidate_invalid:transition_evidence_incomplete" in result.blockers


def test_summary_candidate_with_marker_only_transition_evidence_is_rejected():
    analysis = _analysis_with_exact_returns(effect_summary=_empty_effect_summary())
    n = _n()
    marker_only_transition_key = (
        "not_counted_loop_transition_evidence",
        "header_block latch_block exit_block induction_phi accumulator_phi exit_guard",
        "exit_guard_binding bound_binding accumulator_base updates loop_cases replacement_obligation",
    )
    summary_return = _with_summary_proof(ReturnInfo(
        address="0x1008",
        value=_summary_const(2),
        conditions=[_cond("INT_SLESS", _const(1), n)],
        pcode_identity="summary:n_gt_one",
    ))
    summary_return.summary_transition_evidence_key = marker_only_transition_key

    result = accept_summary_return_candidates(
        analysis,
        [*analysis.returns, summary_return],
        summary_note="barthe2big_counted_loop_summary",
    )

    assert result.accepted_returns == ()
    assert "summary_return_candidate_invalid:transition_evidence_incomplete" in result.blockers


def test_summary_candidate_with_nested_none_transition_metadata_is_rejected():
    analysis = _analysis_with_exact_returns(effect_summary=_empty_effect_summary())
    n = _n()
    incomplete_transition_key = tuple(
        ("accumulator_base", ("expr", "init"), ("expr", "loop_base"), None)
        if isinstance(part, tuple) and part[:1] == ("accumulator_base",)
        else part
        for part in _SUMMARY_TRANSITION_KEY
    )
    summary_return = _with_summary_proof(ReturnInfo(
        address="0x1008",
        value=_summary_const(2),
        conditions=[_cond("INT_SLESS", _const(1), n)],
        pcode_identity="summary:n_gt_one",
    ))
    summary_return.summary_transition_evidence_key = incomplete_transition_key

    result = accept_summary_return_candidates(
        analysis,
        [*analysis.returns, summary_return],
        summary_note="barthe2big_counted_loop_summary",
    )

    assert result.accepted_returns == ()
    assert "summary_return_candidate_invalid:transition_evidence_incomplete" in result.blockers


def test_summary_candidate_with_unscoped_block_transition_metadata_is_rejected():
    analysis = _analysis_with_exact_returns(effect_summary=_empty_effect_summary())
    n = _n()
    unscoped_transition_key = tuple(
        ("header_block", ("pcode_block", 1, 0x1000))
        if isinstance(part, tuple) and part[:1] == ("header_block",)
        else part
        for part in _SUMMARY_TRANSITION_KEY
    )
    summary_return = _with_summary_proof(ReturnInfo(
        address="0x1008",
        value=_summary_const(2),
        conditions=[_cond("INT_SLESS", _const(1), n)],
        pcode_identity="summary:n_gt_one",
    ))
    summary_return.summary_transition_evidence_key = unscoped_transition_key

    result = accept_summary_return_candidates(
        analysis,
        [*analysis.returns, summary_return],
        summary_note="barthe2big_counted_loop_summary",
    )

    assert result.accepted_returns == ()
    assert "summary_return_candidate_invalid:transition_evidence_incomplete" in result.blockers


def test_summary_candidate_rejects_changed_accumulator_base_without_prior_dependency():
    analysis = _analysis_with_exact_returns(effect_summary=_empty_effect_summary())
    n = _n()
    unproved_prior_transition_key = tuple(
        (
            "accumulator_base",
            ("expr", "init"),
            ("expr", "loop_base_from_prior_computation"),
            ("prior_summary_dependency", "none"),
        )
        if isinstance(part, tuple) and part[:1] == ("accumulator_base",)
        else part
        for part in _SUMMARY_TRANSITION_KEY
    )
    summary_return = _with_summary_proof(ReturnInfo(
        address="0x1008",
        value=_summary_const(2),
        conditions=[_cond("INT_SLESS", _const(1), n)],
        pcode_identity="summary:n_gt_one",
    ))
    summary_return.summary_transition_evidence_key = unproved_prior_transition_key

    result = accept_summary_return_candidates(
        analysis,
        [*analysis.returns, summary_return],
        summary_note="barthe2big_counted_loop_summary",
    )

    assert result.accepted_returns == ()
    assert "summary_return_candidate_invalid:transition_evidence_incomplete" in result.blockers


def test_summary_candidate_rejects_changed_accumulator_base_with_thin_prior_dependency():
    analysis = _analysis_with_exact_returns(effect_summary=_empty_effect_summary())
    n = _n()
    thin_prior_transition_key = tuple(
        (
            "accumulator_base",
            ("expr", "init"),
            ("expr", "loop_base_from_prior_computation"),
            ("counted_loop_summary_parts", "prior_loop", ("guard_constraints", ())),
        )
        if isinstance(part, tuple) and part[:1] == ("accumulator_base",)
        else part
        for part in _SUMMARY_TRANSITION_KEY
    )
    summary_return = _with_summary_proof(ReturnInfo(
        address="0x1008",
        value=_summary_const(2),
        conditions=[_cond("INT_SLESS", _const(1), n)],
        pcode_identity="summary:n_gt_one",
    ))
    summary_return.summary_transition_evidence_key = thin_prior_transition_key

    result = accept_summary_return_candidates(
        analysis,
        [*analysis.returns, summary_return],
        summary_note="barthe2big_counted_loop_summary",
    )

    assert result.accepted_returns == ()
    assert "summary_return_candidate_invalid:transition_evidence_incomplete" in result.blockers


def test_summary_candidate_accepts_changed_accumulator_base_with_complete_prior_dependency():
    analysis = _analysis_with_exact_returns(effect_summary=_empty_effect_summary())
    n = _n()
    proved_prior_transition_key = tuple(
        (
            "accumulator_base",
            ("expr", "init"),
            ("expr", "loop_base_from_prior_computation"),
            _SUMMARY_SOURCE_KEY,
        )
        if isinstance(part, tuple) and part[:1] == ("accumulator_base",)
        else part
        for part in _SUMMARY_TRANSITION_KEY
    )
    summary_return = _with_summary_proof(ReturnInfo(
        address="0x1008",
        value=_summary_const(2),
        conditions=[_cond("INT_SLESS", _const(1), n)],
        pcode_identity="summary:n_gt_one",
    ))
    summary_return.summary_transition_evidence_key = proved_prior_transition_key

    result = accept_summary_return_candidates(
        analysis,
        [*analysis.returns, summary_return],
        summary_note="barthe2big_counted_loop_summary",
    )

    assert result.blockers == ()
    assert result.coverage_complete is True
    assert [ret.return_kind for ret in result.accepted_returns] == [
        "exact",
        "exact",
        "summary_derived",
    ]


def test_summary_candidate_rejects_changed_accumulator_base_with_raw_state_transition_summary_key():
    analysis = _analysis_with_exact_returns(effect_summary=_empty_effect_summary())
    n = _n()
    raw_prior_transition_key = tuple(
        (
            "accumulator_base",
            ("expr", "init"),
            ("expr", "loop_base_from_prior_state_transition"),
            _COUNTED_STATE_TRANSITION_SOURCE_KEY,
        )
        if isinstance(part, tuple) and part[:1] == ("accumulator_base",)
        else part
        for part in _SUMMARY_TRANSITION_KEY
    )
    summary_return = _with_summary_proof(ReturnInfo(
        address="0x1008",
        value=_summary_const(2),
        conditions=[_cond("INT_SLESS", _const(1), n)],
        pcode_identity="summary:n_gt_one",
    ))
    summary_return.summary_transition_evidence_key = raw_prior_transition_key

    result = accept_summary_return_candidates(
        analysis,
        [*analysis.returns, summary_return],
        summary_note="barthe2big_counted_loop_summary",
    )

    assert result.accepted_returns == ()
    assert "summary_return_candidate_invalid:transition_evidence_incomplete" in result.blockers


def test_summary_candidate_accepts_changed_accumulator_base_with_completed_state_transition_handoff_proof():
    analysis = _analysis_with_exact_returns(effect_summary=_empty_effect_summary())
    analysis.completed_recovery_proof_evidence = (_STATE_TRANSITION_HANDOFF_PROOF_EVIDENCE,)
    n = _n()
    proved_prior_transition_key = tuple(
        (
            "accumulator_base",
            ("expr", "init"),
            ("expr", "loop_base_from_prior_state_transition"),
            _STATE_TRANSITION_HANDOFF_PROOF_KEY,
        )
        if isinstance(part, tuple) and part[:1] == ("accumulator_base",)
        else part
        for part in _SUMMARY_TRANSITION_KEY
    )
    summary_return = _with_summary_proof(ReturnInfo(
        address="0x1008",
        value=_summary_const(2),
        conditions=[_cond("INT_SLESS", _const(1), n)],
        pcode_identity="summary:n_gt_one",
    ))
    summary_return.summary_transition_evidence_key = proved_prior_transition_key

    result = accept_summary_return_candidates(
        analysis,
        [*analysis.returns, summary_return],
        summary_note="barthe2big_counted_loop_summary",
    )

    assert result.blockers == ()
    assert result.coverage_complete is True
    assert [ret.return_kind for ret in result.accepted_returns] == [
        "exact",
        "exact",
        "summary_derived",
    ]


def test_summary_candidate_rejects_completed_state_transition_handoff_when_completed_proofs_disabled():
    analysis = _analysis_with_exact_returns(effect_summary=_empty_effect_summary())
    analysis.completed_recovery_proof_evidence = (_STATE_TRANSITION_HANDOFF_PROOF_EVIDENCE,)
    n = _n()
    proved_prior_transition_key = tuple(
        (
            "accumulator_base",
            ("expr", "init"),
            ("expr", "loop_base_from_prior_state_transition"),
            _STATE_TRANSITION_HANDOFF_PROOF_KEY,
        )
        if isinstance(part, tuple) and part[:1] == ("accumulator_base",)
        else part
        for part in _SUMMARY_TRANSITION_KEY
    )
    summary_return = _with_summary_proof(ReturnInfo(
        address="0x1008",
        value=_summary_const(2),
        conditions=[_cond("INT_SLESS", _const(1), n)],
        pcode_identity="summary:n_gt_one",
    ))
    summary_return.summary_transition_evidence_key = proved_prior_transition_key

    result = accept_summary_return_candidates(
        analysis,
        [*analysis.returns, summary_return],
        summary_note="barthe2big_counted_loop_summary",
        enable_completed_recovery_proofs=False,
    )

    assert result.accepted_returns == ()
    assert "summary_return_candidate_invalid:transition_evidence_incomplete" in result.blockers


def test_state_transition_handoff_recorder_respects_completed_proof_disable_flag():
    analysis = _analysis_with_exact_returns(effect_summary=_empty_effect_summary())
    summarizer = StructuralRecurrenceSummarizer(
        tracer=None,
        enable_completed_recovery_proofs=False,
    )

    recorded = summarizer._record_completed_prior_state_transition_handoff_proof(
        analysis,
        proof_obligation_id=_STATE_TRANSITION_HANDOFF_PROOF_ID,
        object_target_key=_STATE_TRANSITION_HANDOFF_TARGET_KEY,
    )

    assert recorded is False
    assert analysis.completed_recovery_proof_evidence == ()


def test_summary_candidate_rejects_state_transition_handoff_ref_without_completed_evidence():
    analysis = _analysis_with_exact_returns(effect_summary=_empty_effect_summary())
    n = _n()
    proved_prior_transition_key = tuple(
        (
            "accumulator_base",
            ("expr", "init"),
            ("expr", "loop_base_from_prior_state_transition"),
            _STATE_TRANSITION_HANDOFF_PROOF_KEY,
        )
        if isinstance(part, tuple) and part[:1] == ("accumulator_base",)
        else part
        for part in _SUMMARY_TRANSITION_KEY
    )
    summary_return = _with_summary_proof(ReturnInfo(
        address="0x1008",
        value=_summary_const(2),
        conditions=[_cond("INT_SLESS", _const(1), n)],
        pcode_identity="summary:n_gt_one",
    ))
    summary_return.summary_transition_evidence_key = proved_prior_transition_key

    result = accept_summary_return_candidates(
        analysis,
        [*analysis.returns, summary_return],
        summary_note="barthe2big_counted_loop_summary",
    )

    assert result.accepted_returns == ()
    assert "summary_return_candidate_invalid:transition_evidence_incomplete" in result.blockers


def test_summary_candidate_rejects_state_transition_handoff_ref_with_mismatched_proof_id_target():
    analysis = _analysis_with_exact_returns(effect_summary=_empty_effect_summary())
    analysis.completed_recovery_proof_evidence = (_STATE_TRANSITION_HANDOFF_PROOF_EVIDENCE,)
    n = _n()
    alternate_target_key = tuple(
        ("guard_handoff_proof", "identical_guard_domain", ("guard", "prior_entry_alt"), ("guard", "prior_entry_alt"), "proved", ("guard_constraints", ("n_gt_one",)))
        if isinstance(part, tuple) and part[:1] == ("guard_handoff_proof",)
        else part
        for part in _STATE_TRANSITION_HANDOFF_TARGET_KEY
    )
    mismatched_proof_key = (
        "prior_state_transition_handoff_proof_ref",
        _STATE_TRANSITION_HANDOFF_PROOF_ID,
        alternate_target_key,
    )
    mismatched_prior_transition_key = tuple(
        (
            "accumulator_base",
            ("expr", "init"),
            ("expr", "loop_base_from_prior_state_transition"),
            mismatched_proof_key,
        )
        if isinstance(part, tuple) and part[:1] == ("accumulator_base",)
        else part
        for part in _SUMMARY_TRANSITION_KEY
    )
    summary_return = _with_summary_proof(ReturnInfo(
        address="0x1008",
        value=_summary_const(2),
        conditions=[_cond("INT_SLESS", _const(1), n)],
        pcode_identity="summary:n_gt_one",
    ))
    summary_return.summary_transition_evidence_key = mismatched_prior_transition_key

    result = accept_summary_return_candidates(
        analysis,
        [*analysis.returns, summary_return],
        summary_note="barthe2big_counted_loop_summary",
    )

    assert result.accepted_returns == ()
    assert "summary_return_candidate_invalid:transition_evidence_incomplete" in result.blockers


def test_summary_candidate_rejects_state_transition_handoff_evidence_with_mismatched_proof_id_target():
    analysis = _analysis_with_exact_returns(effect_summary=_empty_effect_summary())
    n = _n()
    alternate_target_key = tuple(
        ("guard_handoff_proof", "identical_guard_domain", ("guard", "prior_entry_alt"), ("guard", "prior_entry_alt"), "proved", ("guard_constraints", ("n_gt_one",)))
        if isinstance(part, tuple) and part[:1] == ("guard_handoff_proof",)
        else part
        for part in _STATE_TRANSITION_HANDOFF_TARGET_KEY
    )
    alternate_content = dict(_STATE_TRANSITION_HANDOFF_PROOF_EVIDENCE["proof_content"])
    alternate_content.update(
        {
            "object_target_key": alternate_target_key,
            "guard_handoff": alternate_target_key[4],
        }
    )
    analysis.completed_recovery_proof_evidence = ({
        **_STATE_TRANSITION_HANDOFF_PROOF_EVIDENCE,
        "object_target_key": alternate_target_key,
        "proof_obligation_id": _STATE_TRANSITION_HANDOFF_PROOF_ID,
        "proof_content": alternate_content,
    },)
    proved_prior_transition_key = tuple(
        (
            "accumulator_base",
            ("expr", "init"),
            ("expr", "loop_base_from_prior_state_transition"),
            _STATE_TRANSITION_HANDOFF_PROOF_KEY,
        )
        if isinstance(part, tuple) and part[:1] == ("accumulator_base",)
        else part
        for part in _SUMMARY_TRANSITION_KEY
    )
    summary_return = _with_summary_proof(ReturnInfo(
        address="0x1008",
        value=_summary_const(2),
        conditions=[_cond("INT_SLESS", _const(1), n)],
        pcode_identity="summary:n_gt_one",
    ))
    summary_return.summary_transition_evidence_key = proved_prior_transition_key

    result = accept_summary_return_candidates(
        analysis,
        [*analysis.returns, summary_return],
        summary_note="barthe2big_counted_loop_summary",
    )

    assert result.accepted_returns == ()
    assert "summary_return_candidate_invalid:transition_evidence_incomplete" in result.blockers


def test_summary_candidate_rejects_state_transition_handoff_evidence_with_missing_proof_content():
    analysis = _analysis_with_exact_returns(effect_summary=_empty_effect_summary())
    n = _n()
    analysis.completed_recovery_proof_evidence = ({
        **_STATE_TRANSITION_HANDOFF_PROOF_EVIDENCE,
        "proof_content": {
            "object_derived": True,
            "object_target_key": _STATE_TRANSITION_HANDOFF_TARGET_KEY,
            "handoff_status": "proved",
        },
    },)
    proved_prior_transition_key = tuple(
        (
            "accumulator_base",
            ("expr", "init"),
            ("expr", "loop_base_from_prior_state_transition"),
            _STATE_TRANSITION_HANDOFF_PROOF_KEY,
        )
        if isinstance(part, tuple) and part[:1] == ("accumulator_base",)
        else part
        for part in _SUMMARY_TRANSITION_KEY
    )
    summary_return = _with_summary_proof(ReturnInfo(
        address="0x1008",
        value=_summary_const(2),
        conditions=[_cond("INT_SLESS", _const(1), n)],
        pcode_identity="summary:n_gt_one",
    ))
    summary_return.summary_transition_evidence_key = proved_prior_transition_key

    result = accept_summary_return_candidates(
        analysis,
        [*analysis.returns, summary_return],
        summary_note="barthe2big_counted_loop_summary",
    )

    assert result.accepted_returns == ()
    assert "summary_return_candidate_invalid:transition_evidence_incomplete" in result.blockers


def test_summary_candidate_rejects_state_transition_handoff_evidence_with_content_mismatch():
    analysis = _analysis_with_exact_returns(effect_summary=_empty_effect_summary())
    n = _n()
    bad_content = dict(_STATE_TRANSITION_HANDOFF_PROOF_EVIDENCE["proof_content"])
    bad_content["value_flow"] = (
        "value_preserving_flow",
        ("varnode", "different_prior_output"),
        ("varnode", "current_acc_init"),
        (
            (
                "edge",
                "COPY",
                ("varnode", "different_prior_output"),
                ("varnode", "current_acc_init"),
                32,
                32,
                (
                    "edge_location",
                    ("pcode_op", "B", 0x100c, 9, 0),
                    ("pcode_block", "B", ("function_entry", "ram", 0x1000), 4, 0x100c),
                ),
            ),
        ),
    )
    analysis.completed_recovery_proof_evidence = ({
        **_STATE_TRANSITION_HANDOFF_PROOF_EVIDENCE,
        "proof_content": bad_content,
    },)
    proved_prior_transition_key = tuple(
        (
            "accumulator_base",
            ("expr", "init"),
            ("expr", "loop_base_from_prior_state_transition"),
            _STATE_TRANSITION_HANDOFF_PROOF_KEY,
        )
        if isinstance(part, tuple) and part[:1] == ("accumulator_base",)
        else part
        for part in _SUMMARY_TRANSITION_KEY
    )
    summary_return = _with_summary_proof(ReturnInfo(
        address="0x1008",
        value=_summary_const(2),
        conditions=[_cond("INT_SLESS", _const(1), n)],
        pcode_identity="summary:n_gt_one",
    ))
    summary_return.summary_transition_evidence_key = proved_prior_transition_key

    result = accept_summary_return_candidates(
        analysis,
        [*analysis.returns, summary_return],
        summary_note="barthe2big_counted_loop_summary",
    )

    assert result.accepted_returns == ()
    assert "summary_return_candidate_invalid:transition_evidence_incomplete" in result.blockers


def test_summary_candidate_rejects_state_transition_handoff_edge_outside_handoff_path():
    analysis = _analysis_with_exact_returns(effect_summary=_empty_effect_summary())
    n = _n()
    outside_flow = (
        "value_preserving_flow",
        ("varnode", "prior_output"),
        ("varnode", "current_acc_init"),
        (
            (
                "edge",
                "COPY",
                ("varnode", "prior_output"),
                ("varnode", "current_acc_init"),
                32,
                32,
                (
                    "edge_location",
                    ("pcode_op", "B", 0x2000, 9, 0),
                    ("pcode_block", "B", ("function_entry", "ram", 0x1000), 9, 0x2000),
                ),
            ),
        ),
    )
    outside_target_key = tuple(
        outside_flow
        if isinstance(part, tuple) and part[:1] == ("value_preserving_flow",)
        else part
        for part in _STATE_TRANSITION_HANDOFF_TARGET_KEY
    )
    outside_proof_id = ("proof_obligation_id", "prior_state_transition_handoff", outside_target_key)
    outside_content = dict(_STATE_TRANSITION_HANDOFF_PROOF_EVIDENCE["proof_content"])
    outside_content.update(
        {
            "object_target_key": outside_target_key,
            "value_flow": outside_flow,
        }
    )
    analysis.completed_recovery_proof_evidence = ({
        **_STATE_TRANSITION_HANDOFF_PROOF_EVIDENCE,
        "object_target_key": outside_target_key,
        "proof_obligation_id": outside_proof_id,
        "proof_content": outside_content,
    },)
    outside_proof_key = (
        "prior_state_transition_handoff_proof_ref",
        outside_proof_id,
        outside_target_key,
    )
    outside_prior_transition_key = tuple(
        (
            "accumulator_base",
            ("expr", "init"),
            ("expr", "loop_base_from_prior_state_transition"),
            outside_proof_key,
        )
        if isinstance(part, tuple) and part[:1] == ("accumulator_base",)
        else part
        for part in _SUMMARY_TRANSITION_KEY
    )
    summary_return = _with_summary_proof(ReturnInfo(
        address="0x1008",
        value=_summary_const(2),
        conditions=[_cond("INT_SLESS", _const(1), n)],
        pcode_identity="summary:n_gt_one",
    ))
    summary_return.summary_transition_evidence_key = outside_prior_transition_key

    result = accept_summary_return_candidates(
        analysis,
        [*analysis.returns, summary_return],
        summary_note="barthe2big_counted_loop_summary",
    )

    assert result.accepted_returns == ()
    assert "summary_return_candidate_invalid:transition_evidence_incomplete" in result.blockers


def test_summary_candidate_rejects_state_transition_handoff_proof_with_run_specific_identity():
    analysis = _analysis_with_exact_returns(effect_summary=_empty_effect_summary())
    n = _n()
    weak_flow = (
        "value_preserving_flow",
        ("varnode_id", 12345),
        ("varnode", "current_acc_init"),
        (
            (
                "edge",
                "COPY",
                ("varnode_id", 12345),
                ("varnode", "current_acc_init"),
                32,
                32,
                (
                    "edge_location",
                    ("pcode_op", "B", 0x100c, 9, 0),
                    ("pcode_block", "B", ("function_entry", "ram", 0x1000), 4, 0x100c),
                ),
            ),
        ),
    )
    weak_target_key = tuple(
        weak_flow
        if isinstance(part, tuple) and part[:1] == ("value_preserving_flow",)
        else part
        for part in _STATE_TRANSITION_HANDOFF_TARGET_KEY
    )
    weak_proof_key = (
        "prior_state_transition_handoff_proof_ref",
        ("proof_obligation_id", "prior_state_transition_handoff", weak_target_key),
        weak_target_key,
    )
    weak_prior_transition_key = tuple(
        (
            "accumulator_base",
            ("expr", "init"),
            ("expr", "loop_base_from_prior_state_transition"),
            weak_proof_key,
        )
        if isinstance(part, tuple) and part[:1] == ("accumulator_base",)
        else part
        for part in _SUMMARY_TRANSITION_KEY
    )
    summary_return = _with_summary_proof(ReturnInfo(
        address="0x1008",
        value=_summary_const(2),
        conditions=[_cond("INT_SLESS", _const(1), n)],
        pcode_identity="summary:n_gt_one",
    ))
    summary_return.summary_transition_evidence_key = weak_prior_transition_key

    result = accept_summary_return_candidates(
        analysis,
        [*analysis.returns, summary_return],
        summary_note="barthe2big_counted_loop_summary",
    )

    assert result.accepted_returns == ()
    assert "summary_return_candidate_invalid:unstable_transition_evidence" in result.blockers


def test_summary_candidate_rejects_state_transition_handoff_without_guard_implication_proof():
    analysis = _analysis_with_exact_returns(effect_summary=_empty_effect_summary())
    n = _n()
    weak_guard_target_key = tuple(
        ("guard_handoff_proof", "smt_implication", ("guard", "prior_exit"), ("guard", "current_entry"), "unknown", ("guard_constraints", ("n_gt_one",)))
        if isinstance(part, tuple) and part[:1] == ("guard_handoff_proof",)
        else part
        for part in _STATE_TRANSITION_HANDOFF_TARGET_KEY
    )
    weak_proof_id = ("proof_obligation_id", "prior_state_transition_handoff", weak_guard_target_key)
    weak_proof_key = (
        "prior_state_transition_handoff_proof_ref",
        weak_proof_id,
        weak_guard_target_key,
    )
    analysis.completed_recovery_proof_evidence = ({
        **_STATE_TRANSITION_HANDOFF_PROOF_EVIDENCE,
        "object_target_key": weak_guard_target_key,
        "proof_obligation_id": weak_proof_id,
        "proof_content": {
            "object_derived": True,
            "object_target_key": weak_guard_target_key,
            "handoff_status": "unproved",
        },
    },)
    weak_prior_transition_key = tuple(
        (
            "accumulator_base",
            ("expr", "init"),
            ("expr", "loop_base_from_prior_state_transition"),
            weak_proof_key,
        )
        if isinstance(part, tuple) and part[:1] == ("accumulator_base",)
        else part
        for part in _SUMMARY_TRANSITION_KEY
    )
    summary_return = _with_summary_proof(ReturnInfo(
        address="0x1008",
        value=_summary_const(2),
        conditions=[_cond("INT_SLESS", _const(1), n)],
        pcode_identity="summary:n_gt_one",
    ))
    summary_return.summary_transition_evidence_key = weak_prior_transition_key

    result = accept_summary_return_candidates(
        analysis,
        [*analysis.returns, summary_return],
        summary_note="barthe2big_counted_loop_summary",
    )

    assert result.accepted_returns == ()
    assert "summary_return_candidate_invalid:transition_evidence_incomplete" in result.blockers


def test_summary_candidate_rejects_prior_dependency_with_empty_guard_constraints():
    analysis = _analysis_with_exact_returns(effect_summary=_empty_effect_summary())
    n = _n()
    empty_guard_prior_key = tuple(
        ("guard_constraints", ())
        if isinstance(part, tuple) and part[:1] == ("guard_constraints",)
        else part
        for part in _SUMMARY_SOURCE_KEY
    )
    transition_key = tuple(
        (
            "accumulator_base",
            ("expr", "init"),
            ("expr", "loop_base_from_prior_computation"),
            empty_guard_prior_key,
        )
        if isinstance(part, tuple) and part[:1] == ("accumulator_base",)
        else part
        for part in _SUMMARY_TRANSITION_KEY
    )
    summary_return = _with_summary_proof(ReturnInfo(
        address="0x1008",
        value=_summary_const(2),
        conditions=[_cond("INT_SLESS", _const(1), n)],
        pcode_identity="summary:n_gt_one",
    ))
    summary_return.summary_transition_evidence_key = transition_key

    result = accept_summary_return_candidates(
        analysis,
        [*analysis.returns, summary_return],
        summary_note="barthe2big_counted_loop_summary",
    )

    assert result.accepted_returns == ()
    assert "summary_return_candidate_invalid:transition_evidence_incomplete" in result.blockers


def test_summary_candidate_runtime_ref_only_transition_evidence_is_missing():
    analysis = _analysis_with_exact_returns(effect_summary=_empty_effect_summary())
    n = _n()
    summary_return = ReturnInfo(
        address="0x1008",
        value=_summary_const(2),
        conditions=[_cond("INT_SLESS", _const(1), n)],
        pcode_identity="summary:n_gt_one",
        summary_candidate_source_key=_SUMMARY_SOURCE_KEY,
    )

    result = accept_summary_return_candidates(
        analysis,
        [*analysis.returns, summary_return],
        summary_note="barthe2big_counted_loop_summary",
    )

    assert result.accepted_returns == ()
    assert "summary_return_candidate_invalid:transition_evidence_missing" in result.blockers


def test_wrapping_guard_shape_is_not_total_without_active_no_overflow_precondition():
    analysis = _analysis_with_exact_returns(effect_summary=_empty_effect_summary())
    n = _n()
    n_plus_one = Expression.binary_op("INT_ADD", n, _const(1))
    wrapping_guard = _cond("INT_SLESS", _const(1), n_plus_one)
    summary_return = _with_summary_proof(ReturnInfo(
        address="0x1008",
        value=_summary_const(1),
        conditions=[wrapping_guard],
        pcode_identity="summary:one_lt_n_plus_one",
    ))

    result = accept_summary_return_candidates(
        analysis,
        [*analysis.returns, summary_return],
        summary_note="barthe2big_counted_loop_summary",
    )

    assert result.accepted_returns == ()
    assert "summary_partition_not_total:active_precondition_not_covered" in result.blockers


def test_summary_acceptance_preserves_resolved_proposed_disjoint_phi_expansion_seed():
    n = _n()
    analysis = FunctionReturnAnalysis(
        function_name="f",
        entry_point="0x1000",
        parameters=[_param()],
        returns=[
            ReturnInfo(
                address="0x1000",
                value=_const(0),
                conditions=[_cond("INT_SLESSEQUAL", n, _const(0))],
                pcode_identity="return:non_positive",
            ),
        ],
        return_type="int",
        effect_summary=_empty_effect_summary(),
        binary_id="barthe2big-test-binary",
    )
    proposed_phi_seed = ReturnInfo(
        address="0x1004",
        value=_const(1),
        conditions=[_cond("INT_EQUAL", n, _const(1))],
        pcode_identity="return:one",
        return_kind="phi_expansion",
    )
    summary_return = _with_summary_proof(ReturnInfo(
        address="0x1008",
        value=_summary_const(2),
        conditions=[_cond("INT_SLESS", _const(1), n)],
        pcode_identity="summary:n_gt_one",
    ))

    result = accept_summary_return_candidates(
        analysis,
        [analysis.returns[0], proposed_phi_seed, summary_return],
        summary_note="barthe2big_counted_loop_summary",
    )

    assert not result.blockers
    assert any(ret.pcode_identity == "return:one" for ret in result.accepted_returns)


def test_summary_partition_not_total_is_exposed_as_structured_reason():
    analysis = _analysis_with_exact_returns(effect_summary=_empty_effect_summary())
    analysis.analysis_notes.append(
        "summary_return_blocker:summary_partition_not_total:active_precondition_not_covered"
    )

    reason_ids = CheckStrategy._summary_return_candidate_blocker_reason_ids(analysis)

    assert reason_ids == (UnknownReasonId.SUMMARY_PARTITION_NOT_TOTAL.value,)
