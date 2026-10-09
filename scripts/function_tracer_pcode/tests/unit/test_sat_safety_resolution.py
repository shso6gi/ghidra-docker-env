"""plan v4 PR-A (I5・Q6): counterexample の replay が解消してよいのは replay 型の理由だけ。

規則の owner は ``proof/sat_safety_resolution.py``。replay の証明を
記録する producer、証拠を証明として数える検証、reason を完了させる gate、別の
witness による supersede が、すべて同じ owner の述語を読むことをここで固定する。
production の経路（checker → monolithic）は ``test_counterexample_replay_binding``、
authority 層は ``test_unknown_taxonomy_v2_phase6_sat_safety`` が見る。
"""

from copy import deepcopy

import pytest

from scripts.function_tracer_pcode.tests.unit._sat_decisiveness_fixtures import *  # noqa: F401,F403
from scripts.function_tracer_pcode.tests.unit._sat_decisiveness_fixtures import (
    _sat_unsafety_resolution_action,
    _sat_unsafety_resolution_evidence,
)
from scripts.function_tracer_pcode.proof.sat_safety_resolution import (
    COUNTEREXAMPLE_REPLAY_MISSING_REF,
    SAT_SAFETY_REASON_RESOLUTION,
    SatSafetyResolution,
    replay_may_resolve_sat_safety_reason,
    sat_safety_completion_is_admissible,
    sat_safety_reason_id_for_refs,
    sat_safety_ref_resolution,
)
from scripts.function_tracer_pcode.authority.lifecycle.production_signals import (
    SAT_SAFETY_TYPED_REASON_IDS,
    SatCounterexampleEvidenceBinding,
)
from scripts.function_tracer_pcode.proof.strategies.pairwise import PairwiseStrategy
from scripts.function_tracer_pcode.proof.strategies.proof_gates import sat_safety as gates


ANALYSIS_REF = "function1:unsupported_call_effect_summary"
CORRESPONDENCE_REF = "pair:input_correspondence:r0_unmatched:0"


@pytest.fixture(autouse=True)
def _gate_runs_in_the_fixture_comparison():
    # fixture の比較の証拠は、それを作った比較の中でだけ採用される（Issue #167）。
    from scripts.function_tracer_pcode.tests.unit._sat_decisiveness_fixtures import (
        _fixture_comparison,
    )

    with _fixture_comparison():
        yield


# ---- owner の表と規則 -------------------------------------------------------


def test_every_typed_sat_reason_has_exactly_one_resolution_type():
    assert frozenset(SAT_SAFETY_REASON_RESOLUTION) == SAT_SAFETY_TYPED_REASON_IDS
    assert SAT_SAFETY_REASON_RESOLUTION == {
        "counterexample_replay_unproven": SatSafetyResolution.REPLAY,
        "counterexample_analysis_safety_unproven": SatSafetyResolution.ANALYSIS_UNSAFETY,
        "counterexample_partition_replay_ambiguous": SatSafetyResolution.PARTITION_AMBIGUITY,
    }


@pytest.mark.parametrize("ref", [
    "function1:counterexample_replay_missing",
    "counterexample_replay_missing:extra",
    "counterexample_replay",
    "function1:incomplete_control_flow",
    CORRESPONDENCE_REF,
    "",
    None,
    ("counterexample_replay_missing",),
])
def test_only_the_exact_replay_ref_is_replay_type(ref):
    # 部分文字列で型を推測しない。知らない ref は解析の不安全（fail-closed）。
    assert sat_safety_ref_resolution(ref) is SatSafetyResolution.ANALYSIS_UNSAFETY
    assert sat_safety_ref_resolution(COUNTEREXAMPLE_REPLAY_MISSING_REF) is SatSafetyResolution.REPLAY


@pytest.mark.parametrize(("refs", "expected"), [
    ((COUNTEREXAMPLE_REPLAY_MISSING_REF,), "counterexample_replay_unproven"),
    ((COUNTEREXAMPLE_REPLAY_MISSING_REF,) * 2, "counterexample_replay_unproven"),
    ((), "counterexample_analysis_safety_unproven"),
    ((ANALYSIS_REF,), "counterexample_analysis_safety_unproven"),
    ((CORRESPONDENCE_REF,), "counterexample_analysis_safety_unproven"),
    ((COUNTEREXAMPLE_REPLAY_MISSING_REF, ANALYSIS_REF), "counterexample_analysis_safety_unproven"),
    ((ANALYSIS_REF, COUNTEREXAMPLE_REPLAY_MISSING_REF), "counterexample_analysis_safety_unproven"),
    (("function1:return_width_observation_blocked",), "counterexample_analysis_safety_unproven"),
])
def test_reason_id_is_replay_only_when_every_ref_is_replay(refs, expected):
    assert sat_safety_reason_id_for_refs(refs) == expected
    assert sat_safety_reason_id_for_refs(iter(refs)) == expected


def test_replay_may_resolve_only_replay_reasons_whose_refs_agree():
    replay = (COUNTEREXAMPLE_REPLAY_MISSING_REF,)
    assert replay_may_resolve_sat_safety_reason("counterexample_replay_unproven", replay)
    # reason id と ref が食い違う record は解消しない（どちら向きでも）。
    assert not replay_may_resolve_sat_safety_reason("counterexample_replay_unproven", (ANALYSIS_REF,))
    assert not replay_may_resolve_sat_safety_reason(
        "counterexample_replay_unproven", (*replay, ANALYSIS_REF)
    )
    assert not replay_may_resolve_sat_safety_reason("counterexample_replay_unproven", ())
    assert not replay_may_resolve_sat_safety_reason("counterexample_analysis_safety_unproven", replay)
    assert not replay_may_resolve_sat_safety_reason("counterexample_analysis_safety_unproven", (ANALYSIS_REF,))
    assert not replay_may_resolve_sat_safety_reason("counterexample_partition_replay_ambiguous", replay)
    assert not replay_may_resolve_sat_safety_reason("unknown_reason", replay)
    assert not replay_may_resolve_sat_safety_reason(None, replay)


def test_only_replay_and_partition_causes_may_be_completed():
    assert sat_safety_completion_is_admissible("counterexample_replay_unproven")
    assert sat_safety_completion_is_admissible("counterexample_partition_replay_ambiguous")
    assert not sat_safety_completion_is_admissible("counterexample_analysis_safety_unproven")
    assert not sat_safety_completion_is_admissible("unknown_reason")
    assert not sat_safety_completion_is_admissible(None)


def test_every_copy_of_the_sat_reason_vocabulary_is_derived_from_the_table():
    from scripts.function_tracer_pcode.authority.domains.sat_safety import (
        SAT_SAFETY_REASON_REGISTRY,
    )
    from scripts.function_tracer_pcode.authority.domains.sat_safety_sites import (
        SAT_SAFETY_AMBIGUITY_OBSERVED_SITE,
        SAT_SAFETY_BLOCKER_OBSERVED_SITE,
    )
    from scripts.function_tracer_pcode.authority.lifecycle.pilot import PILOT_TYPED_CAUSE_KINDS
    from scripts.function_tracer_pcode.reporting import phase7_producer_manifest as manifest

    assert {item.reason_id for item in SAT_SAFETY_REASON_REGISTRY.snapshot()} == set(
        SAT_SAFETY_REASON_RESOLUTION
    )
    assert SAT_SAFETY_BLOCKER_OBSERVED_SITE.reason_ids == (
        "counterexample_analysis_safety_unproven",
        "counterexample_replay_unproven",
    )
    assert SAT_SAFETY_AMBIGUITY_OBSERVED_SITE.reason_ids == (
        "counterexample_partition_replay_ambiguous",
    )
    assert set(SAT_SAFETY_REASON_RESOLUTION) <= PILOT_TYPED_CAUSE_KINDS
    assert {
        reason_id: manifest._REASON_IDENTITY_SCOPES[reason_id]
        for reason_id in SAT_SAFETY_REASON_RESOLUTION
    } == dict.fromkeys(SAT_SAFETY_REASON_RESOLUTION, "RELATIONAL")


def test_replay_producers_use_the_owner_vocabulary():
    from scripts.function_tracer_pcode.proof.conditional_lane import COUNTEREXAMPLE_REPLAY_MISSING

    assert COUNTEREXAMPLE_REPLAY_MISSING is COUNTEREXAMPLE_REPLAY_MISSING_REF
    strategy = PairwiseStrategy(Mock(), Mock(), debug=False)
    analysis = raw_function_analysis(
        function_name="f", entry_point="0x1000", parameters=[], returns=[], return_type="int",
    )
    assert strategy._counterexample_replay_reasons(analysis, analysis) == (
        COUNTEREXAMPLE_REPLAY_MISSING_REF,
    )
    assert gates._v2_sat_safety_reason_for_ref(COUNTEREXAMPLE_REPLAY_MISSING_REF) == (
        "counterexample_replay_unproven"
    )
    assert gates._v2_sat_safety_reason_for_ref(ANALYSIS_REF) == "counterexample_analysis_safety_unproven"


# ---- producer（記録）・証拠の検証・gate（完了） ------------------------------


@pytest.mark.parametrize("refs", [
    (ANALYSIS_REF,),
    (CORRESPONDENCE_REF,),
    ("function1:return_coverage_gap",),
    (COUNTEREXAMPLE_REPLAY_MISSING_REF, ANALYSIS_REF),
])
def test_replay_recorder_records_nothing_for_non_replay_obligations(refs):
    strategy = PairwiseStrategy(echo_input_correspondence(Mock()), Mock(), debug=False)
    analysis1 = raw_function_analysis(
        function_name="f", entry_point="0x1000", parameters=[_param("x")],
        returns=[ReturnInfo(address="0x1000", value=_const(1), conditions=[])], return_type="int",
    )
    analysis2 = raw_function_analysis(
        function_name="f", entry_point="0x2000", parameters=[_param("x")],
        returns=[ReturnInfo(address="0x2000", value=_const(2), conditions=[])], return_type="int",
    )
    reason = strategy._make_sat_unsafety_unknown_reason(
        refs, analysis1, analysis2, case1=None, case2=None, pair_id="(0,0)", stage="S_PAIRWISE",
    )
    assert reason.reason_id == "counterexample_analysis_safety_unproven"
    model = {"x_1": 0, "x_2": 0}

    strategy._record_completed_sat_counterexample_replay_proof(
        reason, analysis1, analysis2, counterexample_raw=model,
        fixed_model_assertion_count=2, replay_source="pr-a-test",
    )

    assert not any(
        isinstance(item, dict) and item.get("proof_source") == "pr-a-test"
        for item in analysis1.completed_recovery_proof_evidence or ()
    )
    assert not strategy._sat_unsafety_resolution_proof_is_complete(
        reason, analysis1, analysis2, current_counterexample_raw=model,
    )


def test_replay_recorder_records_and_completes_the_replay_obligation():
    """対照: replay 型の obligation は、同じ producer が記録し、gate が完了させる。"""
    strategy = PairwiseStrategy(echo_input_correspondence(Mock()), Mock(), debug=False)
    analysis1 = raw_function_analysis(
        function_name="f", entry_point="0x1000", parameters=[_param("x")],
        returns=[ReturnInfo(address="0x1000", value=_const(1), conditions=[])], return_type="int",
    )
    analysis2 = raw_function_analysis(
        function_name="f", entry_point="0x2000", parameters=[_param("x")],
        returns=[ReturnInfo(address="0x2000", value=_const(2), conditions=[])], return_type="int",
    )
    reason = strategy._make_sat_unsafety_unknown_reason(
        (COUNTEREXAMPLE_REPLAY_MISSING_REF,), analysis1, analysis2,
        case1=None, case2=None, pair_id="(0,0)", stage="S_PAIRWISE",
    )
    model = {"x_1": 0, "x_2": 0}

    strategy._record_completed_sat_counterexample_replay_proof(
        reason, analysis1, analysis2, counterexample_raw=model,
        fixed_model_assertion_count=2, replay_source="pr-a-test",
    )

    assert any(
        isinstance(item, dict) and item.get("proof_source") == "pr-a-test"
        for item in analysis1.completed_recovery_proof_evidence or ()
    )
    assert strategy._sat_unsafety_resolution_proof_is_complete(
        reason, analysis1, analysis2, current_counterexample_raw=model,
    )


@pytest.mark.parametrize("refs", [(ANALYSIS_REF,), (CORRESPONDENCE_REF,)])
def test_evidence_claiming_to_discharge_analysis_unsafety_is_not_a_proof(refs):
    """以前の版の recorder が残した形の証拠（解析の不安全の obligation を replay で
    解消したと主張する）は、証明として数えない。"""
    action = _sat_unsafety_resolution_action(refs)
    assert action.reason_id == "counterexample_analysis_safety_unproven"
    evidence = _sat_unsafety_resolution_evidence(action)

    assert PairwiseStrategy._sat_unsafety_resolution_proof_id_from_evidence(evidence) is None


def test_replay_evidence_is_a_proof_only_for_the_refs_it_discharges():
    action = _sat_unsafety_resolution_action()
    assert action.reason_id == "counterexample_replay_unproven"
    # 対照: replay 型の証拠は証明になる。
    assert PairwiseStrategy._sat_unsafety_resolution_proof_id_from_evidence(
        _sat_unsafety_resolution_evidence(action)
    ) == action.proof_obligation_id

    widened = deepcopy(_sat_unsafety_resolution_evidence(action))
    widened["proof_content"]["active_unsafety_discharge"]["discharged_reason_refs"] = (
        COUNTEREXAMPLE_REPLAY_MISSING_REF, ANALYSIS_REF,
    )
    assert PairwiseStrategy._sat_unsafety_resolution_proof_id_from_evidence(widened) is None

    missing = deepcopy(_sat_unsafety_resolution_evidence(action))
    missing["proof_content"]["active_unsafety_discharge"].pop("discharged_reason_refs")
    assert PairwiseStrategy._sat_unsafety_resolution_proof_id_from_evidence(missing) is None


def test_gate_does_not_complete_analysis_unsafety_from_recorded_evidence():
    """gate（完了の判定）自身も規則を読む。証拠の検証が誤って通しても、解析の不安全の
    obligation は完了しない（多層の防御。各層の mutation は PR 本文に記録する）。"""
    strategy = PairwiseStrategy(echo_input_correspondence(Mock()), Mock(), debug=False)
    action = _sat_unsafety_resolution_action((ANALYSIS_REF,))
    reason = make_internal_v2_reason_diagnostic(
        action.reason_id,
        stage=action.stage,
        pair_or_case=action.pair_or_case,
        evidence_refs=action.evidence_refs,
        recovery_proof_kind=action.proof_kind,
        recovery_proof_obligations=(
            UnknownRecoveryProofObligation.create(
                action.proof_kind, action.proof_stage, required_evidence=action.required_evidence,
            ),
        ),
        proof_stage=action.proof_stage,
        evidence_kind=action.evidence_kind,
        object_target_key=action.object_target_key,
        proof_obligation_id=action.proof_obligation_id,
        action_status=UnknownRecoveryActionStatus.PENDING_PROOF.value,
    )
    analysis1 = raw_function_analysis(
        function_name="func1", entry_point="0x1000", parameters=[_param("x")],
        returns=[ReturnInfo(address="0x1000", value=_const(1), conditions=[])], return_type="int",
    )
    analysis2 = raw_function_analysis(
        function_name="func2", entry_point="0x2000", parameters=[_param("x")],
        returns=[ReturnInfo(address="0x2000", value=_const(2), conditions=[])], return_type="int",
    )
    analysis1.completed_recovery_proof_evidence = (_sat_unsafety_resolution_evidence(action),)
    model = {"x_1": 0, "x_2": 0}
    # 証拠の検証の層だけを外す: この証拠を obligation の証明として数える reader にする。
    strategy._sat_unsafety_resolution_proof_id_from_evidence = (
        lambda evidence: action.proof_obligation_id
    )

    assert not strategy._sat_unsafety_resolution_proof_is_complete(
        reason, analysis1, analysis2, current_counterexample_raw=model,
    )


def test_supersede_completes_only_replay_type_rejected_witness_blockers(monkeypatch):
    strategy = PairwiseStrategy(echo_input_correspondence(Mock()), Mock(), debug=False)
    analysis1 = raw_function_analysis(
        function_name="f", entry_point="0x1000", parameters=[_param("x")],
        returns=[ReturnInfo(address="0x1000", value=_const(1), conditions=[])], return_type="int",
    )
    analysis2 = raw_function_analysis(
        function_name="f", entry_point="0x2000", parameters=[_param("x")],
        returns=[ReturnInfo(address="0x2000", value=_const(2), conditions=[])], return_type="int",
    )
    completed = []
    monkeypatch.setattr(
        gates, "_emit_v2_sat_safety_blockers_completed_if_observed",
        lambda refs, target, **_k: completed.append(tuple(refs)),
    )
    decisive = SatCounterexampleEvidenceBinding("a" * 64, "b" * 64, "premise", (1, 0))
    for refs in ((ANALYSIS_REF,), (COUNTEREXAMPLE_REPLAY_MISSING_REF, ANALYSIS_REF)):
        reason = strategy._make_sat_unsafety_unknown_reason(
            refs, analysis1, analysis2, case1=None, case2=None, pair_id="(0,0)", stage="S_PAIRWISE",
        )
        assert strategy._supersede_rejected_witness_blocker(
            "replay", refs, analysis1, analysis2, case1=None, case2=None, pair_id="(0,0)",
            reason_record=reason, decisive_binding=decisive,
        ) is False
    assert completed == []

    replay_refs = (COUNTEREXAMPLE_REPLAY_MISSING_REF,)
    reason = strategy._make_sat_unsafety_unknown_reason(
        replay_refs, analysis1, analysis2, case1=None, case2=None, pair_id="(0,0)", stage="S_PAIRWISE",
    )
    assert strategy._supersede_rejected_witness_blocker(
        "replay", replay_refs, analysis1, analysis2, case1=None, case2=None, pair_id="(0,0)",
        reason_record=reason, decisive_binding=decisive,
    ) is True
    assert completed == [replay_refs]
