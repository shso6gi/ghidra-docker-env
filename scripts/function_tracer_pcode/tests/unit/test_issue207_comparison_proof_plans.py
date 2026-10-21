# -*- coding: utf-8 -*-
"""Issue #207: 戻り値観測の proof plan は、それを登録した比較ごとに持つ。

1 つの pair の process では、raw pair の比較と再帰抽象化した pair の比較（``recurrence_stage``
の内側の ``check()``）が同じ production pilot session を使う。proof plan の値（ABI seed の
``surface_fact`` など）は比較の解析に依存するが、projection seed には依存しないので、seed だけを
key にした registry では 2 つ目の比較の登録が「drift」になり、pair 全体が ERROR になっていた。

守る契約（`abi_width_readonly.py` の登録と完了処理）:

* 登録は比較の binding（``ComparisonAuthorityBinding``）の下でだけ行う。binding が無ければ拒否する。
* 同じ比較の中で同じ seed に違う plan が来たら、今どおり drift として拒否する。
* 違う比較は同じ seed の plan を別々に持つ。
* ``return_abi_relation_unproven`` の occurrence は、その seed の plan を登録したすべての比較の
  relation が PROVED のときだけ完了する。完了の artifact は binding の digest 順の先頭の plan から
  作る（登録順に依存しない）。
"""

from __future__ import annotations

from types import SimpleNamespace

import pytest

from scripts.function_tracer_pcode.analysis.effects.models import EffectSummary
from scripts.function_tracer_pcode.authority.domains.abi_width_readonly import (
    ReturnAbiRelationStatus,
    ReturnObservationProjectionSeed,
    assess_return_abi_pair,
)
from scripts.function_tracer_pcode.authority.lifecycle.production_signals import production_signal_scope
from scripts.function_tracer_pcode.authority.lifecycle.stream import (
    DecisiveProofEventAuthority,
    EventIntent,
    EventType,
)
from scripts.function_tracer_pcode.core import ComparisonSurface
from scripts.function_tracer_pcode.proof.return_width.pipeline import (
    PreparedFunctionReturnWidths,
    build_pair_return_observation_seed,
    prepare_pair_return_observation,
)
from scripts.function_tracer_pcode.tests.unit import test_issue185_type_hypothesis_domain as recursive_cases
from scripts.function_tracer_pcode.tests.unit._input_correspondence_support import comparison_of
from scripts.function_tracer_pcode.tests.unit._production_check_harness import run_production_check
from scripts.function_tracer_pcode.tests.unit.test_void_effect_only_return_abi_issue104 import (
    _abi_facts,
    _session,
    _void_analysis,
    _width_seed,
)

_RELATION = "return_abi_relation_unproven"


def _analysis(side, *, summary, surface="return_value"):
    """int を返す解析。``summary=False`` は再帰抽象化の解析と同じく ``effect_summary`` が無い。"""

    analysis = _void_analysis(side, facts=_abi_facts(return_type="/int", type_length=4, storage="PRESENT"))
    analysis.comparison_surface = ComparisonSurface(
        kind=surface, explicit_bit_width=32, use_sign_extension=False, evidence={}
    )
    if not summary:
        analysis.effect_summary = None
    return analysis


def _raw_pair():
    return _analysis("left", summary=True), _analysis("right", summary=True)


def _abstract_proved_pair():
    return _analysis("left", summary=False), _analysis("right", summary=False)


def _abstract_unproven_pair():
    # 観測面の種類が左右で違う relation は PROVED にならない（UNPROVEN）
    return _analysis("left", summary=False), _analysis("right", summary=False, surface="memory_effect")


def _widths(left, right):
    return (
        _width_seed("left", function_identity=left.outcome_function_identity()),
        _width_seed("right", function_identity=right.outcome_function_identity()),
    )


def _prepare(left, right):
    left_width, right_width = _widths(left, right)
    left_case, right_case = object(), object()
    incomplete = SimpleNamespace(complete=False, blocker_kind="test-stop")
    prepare_pair_return_observation(
        left, right, left_case, right_case,
        PreparedFunctionReturnWidths({id(left_case): left_width}, {id(left_case): incomplete}),
        PreparedFunctionReturnWidths({id(right_case): right_width}, {id(right_case): incomplete}),
        return_coverage_ids=(),
    )


def _plan(left, right):
    left_width, right_width = _widths(left, right)
    pair_seed = build_pair_return_observation_seed(left_width, right_width)
    projection = ReturnObservationProjectionSeed.from_pair_seed(left_width, right_width, pair_seed)
    return projection, assess_return_abi_pair(left, right, left_width, right_width, pair_seed)


def _run(case_id, comparisons, *, in_comparison=True):
    """``comparisons`` の各 pair を順に、それぞれ自分の比較の範囲で production の producer に通し、
    domain を完了させてから EQ の証明で閉じる。最終 outcome・C_active・完了した artifact を返す。"""

    connector, encoder, session = _session(case_id)
    artifacts = []
    complete = encoder.complete_return_abi_relation

    def spy(session_, blocker, artifact):
        artifacts.append(artifact.artifact_digest)
        return complete(session_, blocker, artifact)

    encoder.complete_return_abi_relation = spy
    with production_signal_scope(session):
        for left, right in comparisons:
            if in_comparison:
                with comparison_of(left, right):
                    _prepare(left, right)
            else:
                _prepare(left, right)
        encoder.finalize_open_execution_history(session)
    active = tuple(row.reason_id for row in session.preview_lifecycle_projection().c_active_base)
    errors = tuple(session.domain_signal_error_kinds)
    session.emit(EventIntent(EventType.EQ_CLOSURE, DecisiveProofEventAuthority("issue207-eq")))
    try:
        evidence = connector.finish(
            session,
            SimpleNamespace(error_message=None, is_equivalent=True, failure_status=None,
                            failure_message=None, is_timeout=lambda: False),
            case_id=case_id,
        )
        outcome = evidence.pilot_result.candidate.decision_receipt.outcome.value
    except ValueError as exc:
        outcome = "ERROR: " + str(exc)
    return SimpleNamespace(
        outcome=outcome, active=active, errors=errors, artifacts=tuple(artifacts),
        plans=session.domain_signal_state.get("return_observation_proof_plans", {}),
    )


def test_the_fixture_plans_share_the_seed_and_differ_in_value():
    # 前提: raw と抽象の plan は同じ projection seed で、値（ABI seed）だけが違う（#207 の形）
    raw_seed, raw_plan = _plan(*_raw_pair())
    abs_seed, abs_plan = _plan(*_abstract_proved_pair())
    bad_seed, bad_plan = _plan(*_abstract_unproven_pair())
    assert raw_seed == abs_seed == bad_seed
    assert raw_plan != abs_plan
    assert raw_plan.left_seed.surface_fact[7] is True and abs_plan.left_seed.surface_fact[7] is False
    assert raw_plan.relation_assessment.status is ReturnAbiRelationStatus.PROVED
    assert abs_plan.relation_assessment.status is ReturnAbiRelationStatus.PROVED
    assert bad_plan.relation_assessment.status is ReturnAbiRelationStatus.UNPROVEN


def test_a_different_plan_for_the_same_seed_within_one_comparison_is_drift():
    connector, encoder, session = _session("issue207-drift")
    left, right = _raw_pair()
    seed, raw_plan = _plan(left, right)
    _same_seed, abstract_plan = _plan(*_abstract_proved_pair())
    with production_signal_scope(session), comparison_of(left, right):
        encoder.register_return_observation_proof_plan(session, seed, raw_plan)
        # 同じ plan の再登録は受理する
        encoder.register_return_observation_proof_plan(session, seed, raw_plan)
        with pytest.raises(ValueError, match="proof plan drifted"):
            encoder.register_return_observation_proof_plan(session, seed, abstract_plan)


def test_two_comparisons_may_register_different_plans_for_the_same_seed():
    # main (8a4fd93f) では 2 つ目の登録が "proof plan drifted" で拒否されていた
    connector, encoder, session = _session("issue207-two-comparisons")
    raw = _raw_pair()
    abstract = _abstract_proved_pair()
    seed, raw_plan = _plan(*raw)
    _same_seed, abstract_plan = _plan(*abstract)
    with production_signal_scope(session):
        with comparison_of(*raw) as raw_binding:
            encoder.register_return_observation_proof_plan(session, seed, raw_plan)
        with comparison_of(*abstract) as abstract_binding:
            encoder.register_return_observation_proof_plan(session, seed, abstract_plan)
    assert raw_binding != abstract_binding
    plans = session.domain_signal_state["return_observation_proof_plans"]
    assert plans == {seed.seed_digest: {
        raw_binding: (seed, raw_plan),
        abstract_binding: (seed, abstract_plan),
    }}


def test_a_registered_seed_digest_holding_another_seed_is_refused():
    # 同じ seed digest の下に別の seed があれば（digest の衝突・registry の破損）受理しない
    connector, encoder, session = _session("issue207-seed-collision")
    raw = _raw_pair()
    seed, raw_plan = _plan(*raw)
    other_left, other_right = _analysis("left2", summary=True), _analysis("right2", summary=True)
    other_seed, other_plan = _plan(other_left, other_right)
    assert other_seed != seed
    with production_signal_scope(session):
        with comparison_of(other_left, other_right) as other_binding:
            pass
        session.domain_signal_state["return_observation_proof_plans"] = {
            seed.seed_digest: {other_binding: (other_seed, other_plan)}
        }
        with comparison_of(*raw), pytest.raises(ValueError, match="seed collided"):
            encoder.register_return_observation_proof_plan(session, seed, raw_plan)


@pytest.mark.parametrize("order", ["raw_first", "abstract_first"])
def test_an_unproven_relation_of_any_comparison_keeps_the_shared_blocker(order):
    comparisons = [_raw_pair(), _abstract_unproven_pair()]
    if order == "abstract_first":
        comparisons.reverse()
    result = _run("issue207-unproven-" + order, comparisons)
    assert result.errors == ()
    assert result.artifacts == ()
    assert _RELATION in result.active
    assert result.outcome == "UNKNOWN"
    (by_comparison,) = result.plans.values()
    assert len(by_comparison) == 2


def test_both_proved_relations_complete_the_blocker_independent_of_registration_order():
    first = _run("issue207-proved", [_raw_pair(), _abstract_proved_pair()])
    second = _run("issue207-proved", [_abstract_proved_pair(), _raw_pair()])
    for result in (first, second):
        assert result.errors == ()
        assert _RELATION not in result.active
        assert result.outcome == "EQUIVALENT"
        assert len(result.artifacts) == 1
    assert first.artifacts == second.artifacts


def test_a_single_comparison_keeps_its_behaviour():
    proved = _run("issue207-single-proved", [_raw_pair()])
    assert proved.errors == () and _RELATION not in proved.active and proved.outcome == "EQUIVALENT"
    unproven = _run("issue207-single-unproven", [_abstract_unproven_pair()])
    assert unproven.errors == () and _RELATION in unproven.active and unproven.outcome == "UNKNOWN"


def test_registration_outside_a_comparison_is_refused_and_the_pair_is_an_error():
    result = _run("issue207-no-binding", [_raw_pair()], in_comparison=False)
    assert result.errors == ("ValueError",)
    assert result.plans == {}
    assert result.outcome.startswith("ERROR: production domain signal encoding is incomplete")
    assert "no comparison authority" in result.outcome


# ---------------------------------------------------------------------------
# production の check 経路（raw pair と再帰抽象化の比較が同じ session で登録する）
# ---------------------------------------------------------------------------


@pytest.mark.parametrize("case", ["A2", "A3"])
def test_a_recursive_pair_with_effect_summaries_is_not_an_error(case):
    # raw の解析には effect_summary があり、再帰抽象化の解析には無い（#207 の再現条件）。
    # main (8a4fd93f) では抽象化の比較の登録が drift になり ERROR（canonical_projection_exception）。
    left, right = recursive_cases._ABSTRACTION_CASES[case]()
    left.effect_summary = EffectSummary(["n"], [])
    right.effect_summary = EffectSummary(["m"], [])
    result = run_production_check(
        "issue207-" + case, left, right,
        left_architecture=recursive_cases.AARCH64, right_architecture=recursive_cases.AARCH64,
    )
    assert "S_ABSTRACT_RECURSIVE_SUMMARY" in result["stage_path"]
    assert result.get("failure_status") is None
    # 抽象化の比較は判定しない（Issue #185 T11b）ので、ERROR でなく UNKNOWN になる
    assert result["final_outcome"] == "UNKNOWN", result["final_outcome"]
