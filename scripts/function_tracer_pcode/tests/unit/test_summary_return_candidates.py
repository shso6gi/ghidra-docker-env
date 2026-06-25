# -*- coding: utf-8 -*-

from scripts.function_tracer_pcode.analysis.effect_summary import EffectSummary
from scripts.function_tracer_pcode.analysis.summary_returns import accept_summary_return_candidates
from scripts.function_tracer_pcode.equivalence.strategies.base import CheckStrategy
from scripts.function_tracer_pcode.equivalence.unknown_reason import (
    UnknownReasonId,
    get_unknown_reason_definition,
)
from scripts.function_tracer_pcode.model import Condition, Expression, FunctionReturnAnalysis, ReturnInfo


class _ReasonMappingHarness:
    _blocking_reason_kind = staticmethod(CheckStrategy._blocking_reason_kind)


class _FakeLoopSummaryRuntimeRef:
    def __init__(self, name: str = "barthe2big_counted_loop"):
        self.name = name

    def stable_key(self):
        return ("counted_loop_summary", self.name, "header", "latch", "exit")


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
    assert len(analysis.returns) == 2


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


def test_summary_partition_not_total_is_exposed_as_structured_reason():
    analysis = _analysis_with_exact_returns(effect_summary=_empty_effect_summary())
    analysis.analysis_notes.append(
        "summary_return_blocker:summary_partition_not_total:active_precondition_not_covered"
    )

    reason_ids = CheckStrategy._summary_return_candidate_blocker_reason_ids(analysis)

    assert reason_ids == (UnknownReasonId.SUMMARY_PARTITION_NOT_TOTAL.value,)
