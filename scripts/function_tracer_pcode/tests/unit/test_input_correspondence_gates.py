# -*- coding: utf-8 -*-
"""Issue #167: 最終 InputCorrespondence の decisive gate（pairwise / monolithic、EQ / NOT_EQ）。

gate は ``InputCorrespondenceSet`` の型付き値だけを見る（診断文字列・``sat_pair_info``・
ログは読まない）。set が無い / query の relation が違う / 不十分なら既存の登録済み
reason（NOT_EQ 側 ``counterexample_analysis_safety_unproven``、EQ 側
``comparison_equivalence_closure_unproven``）と evidence-ref で UNKNOWN にする。
両側 0 parameter の EMPTY は十分。
"""

from __future__ import annotations

from unittest.mock import Mock

import pytest

from scripts.function_tracer_pcode.tests.unit._input_correspondence_support import echo_input_correspondence
from scripts.function_tracer_pcode.tests.unit._sat_decisiveness_fixtures import (
    FormulaBuilderResult,
    FunctionReturnAnalysis,
    MonolithicStrategy,
    PairwiseStrategy,
    ParallelResult,
    ReturnCase,
    ReturnInfo,
    SolverResult,
    SolverStatus,
    _const,
    _param,
    _solver_bound_query_result,
)
from scripts.function_tracer_pcode.core import Expression
from scripts.function_tracer_pcode.proof.formula.input_correspondence import (
    InputCorrespondenceStatus,
    build_input_correspondence_set,
)


def _formula_bound_sat_result(model):
    return _solver_bound_query_result(
        False, model=model, query="(assert (distinct (_ bv1 32) (_ bv2 32)))\n(check-sat)",
    )


def _analysis(name: str, entry: str, params, value) -> FunctionReturnAnalysis:
    return FunctionReturnAnalysis(
        function_name=name,
        entry_point=entry,
        parameters=list(params),
        returns=[ReturnInfo(address=entry, value=value, conditions=[])],
        return_type="int",
    )


def _same_width_pair():
    return (
        _analysis("f", "0x1000", [_param("x")], _const(1)),
        _analysis("f", "0x2000", [_param("x")], _const(2)),
    )


def _empty_pair():
    return (
        _analysis("f", "0x1000", [], _const(1)),
        _analysis("f", "0x2000", [], _const(2)),
    )


def _insufficient_pair():
    """左 int(32) / 右 long(64)。右は x を全幅で読むので R5 で wide 側が閉じない。"""

    wide = Expression.parameter("x", index=0, data_type="long", size=8)
    return (
        _analysis("f", "0x1000", [_param("x")], _const(1)),
        _analysis("f", "0x2000", [_param("x", size=8, data_type="long")], wide),
    )


def _base_context():
    from scripts.function_tracer_pcode.tests.unit._sat_decisiveness_fixtures import (
        _base_context_for_single_int_param,
    )

    return _base_context_for_single_int_param()


# ---------------------------------------------------------------------------
# gate unit
# ---------------------------------------------------------------------------


def test_gate_reports_missing_unbound_and_insufficient_relations_but_not_empty():
    strategy = PairwiseStrategy(Mock(), Mock(), debug=False)
    left, right = _same_width_pair()
    sufficient = build_input_correspondence_set(left, right)
    insufficient = build_input_correspondence_set(*_insufficient_pair())
    empty = build_input_correspondence_set(*_empty_pair())
    assert empty.status is InputCorrespondenceStatus.EMPTY

    gate = strategy._input_correspondence_unsafety_reasons
    assert gate(sufficient, authority_correspondence=sufficient) == []
    assert gate(empty, authority_correspondence=empty) == []
    assert gate(sufficient, authority_correspondence=None) == [
        "pair:input_correspondence:unavailable:authority"
    ]
    assert gate(None, authority_correspondence=sufficient) == [
        "pair:input_correspondence:unavailable:query"
    ]
    assert gate(insufficient, authority_correspondence=sufficient)[0].startswith(
        "pair:input_correspondence:unbound:"
    )
    (reason,) = gate(insufficient, authority_correspondence=insufficient)
    assert reason.startswith("pair:input_correspondence:param[0,0]:WIDTH_OVERLAP:wide_side_not_closed:right@32")


def test_gate_reasons_map_to_existing_registered_reasons_and_cannot_be_replay_discharged():
    strategy = PairwiseStrategy(Mock(), Mock(), debug=False)
    left, right = _insufficient_pair()
    (reason,) = strategy._input_correspondence_unsafety_reasons(
        build_input_correspondence_set(left, right),
        authority_correspondence=build_input_correspondence_set(left, right),
    )

    eq_reason = strategy._make_blocking_unsafety_unknown_reason(reason, left, right, stage="S_PAIRWISE")
    assert eq_reason.reason_id == "comparison_equivalence_closure_unproven"
    assert eq_reason.evidence_refs == (reason,)

    sat_reason = strategy._make_sat_unsafety_unknown_reason(
        [reason], left, right, case1=None, case2=None, pair_id="(0,0)", stage="S_PAIRWISE",
    )
    assert sat_reason.reason_id == "counterexample_analysis_safety_unproven"
    strategy.enable_completed_recovery_proofs = True
    strategy._record_completed_sat_counterexample_replay_proof(
        sat_reason, left, right, counterexample_raw={"x_1": 1}, fixed_model_assertion_count=1,
        replay_source="unit",
    )
    assert left.completed_recovery_proof_evidence == ()
    assert not strategy._sat_unsafety_resolution_proof_is_complete(
        sat_reason, left, right, current_counterexample_raw={"x_1": 1}
    )


# ---------------------------------------------------------------------------
# pairwise
# ---------------------------------------------------------------------------


def _run_pairwise(monkeypatch, analysis1, analysis2, *, sat: bool, builder):
    builder.build_base_context.return_value = _base_context()
    solver_runner = Mock()
    solver_runner.timeout = 5
    strategy = PairwiseStrategy(builder, solver_runner, debug=False)
    case1 = ReturnCase(
        index=0, conditions=[], value_expr=analysis1.returns[0].value,
        return_info=analysis1.returns[0], return_type="int", parameters=analysis1.parameters,
    )
    case2 = ReturnCase(
        index=0, conditions=[], value_expr=analysis2.returns[0].value,
        return_info=analysis2.returns[0], return_type="int", parameters=analysis2.parameters,
    )
    monkeypatch.setattr(strategy, "_extract_return_cases", lambda analysis: [case1] if analysis is analysis1 else [case2])
    monkeypatch.setattr(strategy, "_prune_unreachable_cases", lambda cases, *_a, **_k: cases)
    monkeypatch.setattr(strategy, "_cases_are_contradictory", lambda *_a, **_k: False)
    monkeypatch.setattr(strategy, "_case_contains_unresolved_expression", lambda *_a, **_k: False)
    monkeypatch.setattr(
        "scripts.function_tracer_pcode.proof.strategies.pairwise.validate_counterexample_across_cases",
        lambda *_a, **_k: True,
    )
    strategy._solve_query_after_guard = Mock(
        return_value=(
            _formula_bound_sat_result({"x_1": 0, "x_2": 0}) if sat
            else _solver_bound_query_result(True)
        )
    )
    return strategy.check(analysis1, analysis2)


def _reason_refs(result):
    return [ref for reason in result.unknown_reasons for ref in (reason.evidence_refs or ())]


@pytest.mark.parametrize("sat", [False, True])
def test_pairwise_sufficient_relation_keeps_the_decisive_outcome(monkeypatch, sat):
    result = _run_pairwise(monkeypatch, *_same_width_pair(), sat=sat, builder=echo_input_correspondence(Mock()))
    assert result.is_equivalent is (not sat)


@pytest.mark.parametrize("sat", [False, True])
def test_pairwise_valid_zero_parameter_empty_is_sufficient(monkeypatch, sat):
    result = _run_pairwise(monkeypatch, *_empty_pair(), sat=sat, builder=echo_input_correspondence(Mock()))
    assert result.is_equivalent is (not sat)


@pytest.mark.parametrize("sat", [False, True])
def test_pairwise_insufficient_relation_blocks_eq_and_not_eq(monkeypatch, sat):
    result = _run_pairwise(monkeypatch, *_insufficient_pair(), sat=sat, builder=echo_input_correspondence(Mock()))
    assert result.is_equivalent is None
    assert any("input_correspondence:param[0,0]:WIDTH_OVERLAP" in ref for ref in _reason_refs(result))
    expected = "counterexample_analysis_safety_unproven" if sat else "comparison_equivalence_closure_unproven"
    assert expected in {reason.reason_id for reason in result.unknown_reasons}


@pytest.mark.parametrize("sat", [False, True])
def test_pairwise_missing_relation_set_blocks_eq_and_not_eq(monkeypatch, sat):
    """builder が relation を報告しない（配線漏れ）→ fail-closed。"""

    result = _run_pairwise(monkeypatch, *_same_width_pair(), sat=sat, builder=Mock())
    assert result.is_equivalent is None
    assert "pair:input_correspondence:unavailable:query" in _reason_refs(result)


# ---------------------------------------------------------------------------
# monolithic
# ---------------------------------------------------------------------------


class _Runner:
    def __init__(self, status):
        self.timeout = 5
        self._status = status

    def run_parallel(self, _query, **_kwargs):
        model = {"x_1": 0, "x_2": 0} if self._status is SolverStatus.SAT else None
        return ParallelResult(results=[SolverResult("fake", self._status, elapsed_time=0.01, model=model)])

    run_sequential = run_parallel


def _run_monolithic(monkeypatch, analysis1, analysis2, *, status, builder):
    builder.build_equivalence_formula_extended.return_value = FormulaBuilderResult(
        formula="(set-logic QF_BV)\n(check-sat)", return_var1="return_1", return_var2="return_2",
        constrained_fragments=[], extra_vars1=[], extra_vars2=[], param_fragment_constrained=[],
    )
    builder.build_base_context.return_value = _base_context()
    strategy = MonolithicStrategy(builder, _Runner(status), debug=False)
    monkeypatch.setattr(strategy, "_collect_monolithic_return_coverage_unsafety_reasons", lambda *_a: [])
    monkeypatch.setattr(strategy, "_counterexample_is_decisive_across_case_split", lambda *_a: True)
    return strategy.check(analysis1, analysis2)


def test_monolithic_sufficient_and_empty_relations_keep_eq(monkeypatch):
    for pair in (_same_width_pair(), _empty_pair()):
        result = _run_monolithic(
            monkeypatch, *pair, status=SolverStatus.UNSAT, builder=echo_input_correspondence(Mock())
        )
        assert result.is_equivalent is True


def test_monolithic_insufficient_relation_blocks_eq(monkeypatch):
    result = _run_monolithic(
        monkeypatch, *_insufficient_pair(), status=SolverStatus.UNSAT, builder=echo_input_correspondence(Mock())
    )
    assert result.is_equivalent is None
    assert "comparison_equivalence_closure_unproven" in {reason.reason_id for reason in result.unknown_reasons}
    assert any("input_correspondence:param[0,0]:WIDTH_OVERLAP" in ref for ref in _reason_refs(result))


def test_monolithic_missing_relation_blocks_eq(monkeypatch):
    result = _run_monolithic(monkeypatch, *_same_width_pair(), status=SolverStatus.UNSAT, builder=Mock())
    assert result.is_equivalent is None
    assert "pair:input_correspondence:unavailable:query" in _reason_refs(result)


@pytest.mark.parametrize(("pair", "blocked"), [(_insufficient_pair, True), (_same_width_pair, False)])
def test_monolithic_not_eq_gate_carries_the_input_correspondence_reason(monkeypatch, pair, blocked):
    """SAT 側: 不十分な relation は SAT-safety reason に入り、replay で解消されない。"""

    result = _run_monolithic(
        monkeypatch, *pair(), status=SolverStatus.SAT, builder=echo_input_correspondence(Mock())
    )
    assert result.is_equivalent is not False or not blocked
    refs = _reason_refs(result)
    assert any("input_correspondence" in ref for ref in refs) is blocked
