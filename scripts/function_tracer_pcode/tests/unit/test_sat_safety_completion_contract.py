"""plan v4 PR-A: SAT-safety の blocker の完了は、記録した観測の blocker で許可を決める。

契約（owner は ``proof/sat_safety_resolution.py``）:

* blocker は (reason id, evidence ref の組) の対で、整合する対だけが signal になる
  （構築時に分類する。呼び手が付けた id だけを信じない）。
* 完了は、記録した観測（公開済み、または deferred の約束）を同じ blocker として
  言い直し、その blocker が完了可能（replay 型 / partition の曖昧さ）なときだけ許す。
  解析の不安全は決して完了しない。
* 拒否は状態（観測・完了の台帳・deferred の約束と予約・Phase 7 の取引）を変えずに、
  domain signal の失敗として記録する（pair は ERROR。最終の NOT_EQ を許さない）。

経路: 構築 / 観測（通常・deferred）/ 完了（条件付き API・直接の signal）/ deferred の破棄と
予約の解放 / 束縛した counterexample による完了 / 最終 authority。各検査を外す mutation が、
その検査の欠落だけで落ちるように、経路ごとに独立した test を置く。
"""

from dataclasses import replace

import pytest

from scripts.function_tracer_pcode.authority.contracts import Outcome
from scripts.function_tracer_pcode.authority.domains.sat_safety_sites import (
    SAT_SAFETY_AMBIGUITY_COMPLETED_SITE,
    SAT_SAFETY_AMBIGUITY_OBSERVED_SITE,
    SAT_SAFETY_BLOCKER_COMPLETED_SITE,
    SAT_SAFETY_BLOCKER_OBSERVED_SITE,
)
from scripts.function_tracer_pcode.authority.lifecycle.production_signals import (
    SafeCounterexampleProductionSignal,
    SatSafetyBlockerProductionSignal,
    complete_observed_sat_safety_for_counterexample,
    emit_sat_safety_completion_if_observed,
    emit_sat_safety_signal,
    production_signal_scope,
)
from scripts.function_tracer_pcode.proof.obligations.pair_disposition import (
    emit_safe_counterexample_production_signal,
)
from scripts.function_tracer_pcode.proof.sat_safety_resolution import (
    COUNTEREXAMPLE_REPLAY_MISSING_REF,
    SatSafetyBlockerInconsistent,
)
from scripts.function_tracer_pcode.tests.unit.test_unknown_taxonomy_v2_phase6_sat_safety import (
    _LegacyResult,
    _connector,
    _manifest_connector,
    _safe_pairwise_receipt,
)


REPLAY = "counterexample_replay_unproven"
ANALYSIS = "counterexample_analysis_safety_unproven"
PARTITION = "counterexample_partition_replay_ambiguous"
R = COUNTEREXAMPLE_REPLAY_MISSING_REF
A = "function1:incomplete_control_flow"

_SITES = {
    REPLAY: (SAT_SAFETY_BLOCKER_OBSERVED_SITE, SAT_SAFETY_BLOCKER_COMPLETED_SITE),
    ANALYSIS: (SAT_SAFETY_BLOCKER_OBSERVED_SITE, SAT_SAFETY_BLOCKER_COMPLETED_SITE),
    PARTITION: (SAT_SAFETY_AMBIGUITY_OBSERVED_SITE, SAT_SAFETY_AMBIGUITY_COMPLETED_SITE),
}


def _observed(reason_id, refs, *, key=("contract",), defer=False, binding=None):
    return SatSafetyBlockerProductionSignal(
        action="OBSERVED",
        reason_id=reason_id,
        canonical_target_key=key,
        missing_semantic_fact=("counterexample_safety_gate_unproven", "contract"),
        evidence_refs=refs,
        producer_id=_SITES[reason_id][0].producer_id,
        counterexample_binding=binding,
        defer_until_terminal=defer,
    )


def _completion(observed, **changes):
    return replace(
        observed,
        action="COMPLETED",
        producer_id=_SITES[observed.reason_id][1].producer_id,
        proof_artifact_digest="contract-proof",
        defer_until_terminal=False,
        **changes,
    )


def _observe(observed):
    return emit_sat_safety_signal(
        observed, producer_site_manifest_id=_SITES[observed.reason_id][0].site_id,
    )


def _complete_conditionally(completion):
    return emit_sat_safety_completion_if_observed(
        completion, producer_site_manifest_id=_SITES[completion.reason_id][1].site_id,
    )


def _complete_directly(completion):
    return emit_sat_safety_signal(
        completion, producer_site_manifest_id=_SITES[completion.reason_id][1].site_id,
    )


def _state(session):
    """拒否で変わってはならない状態（観測・完了・deferred・予約・stream・Phase 7）。"""
    state = session.domain_signal_state
    runtime = getattr(session, "phase7_runtime", None)
    return {
        "observed": set(state.get("sat_safety_observed", set())),
        "completed": set(state.get("sat_safety_completed", set())),
        "observed_signals": dict(state.get("sat_safety_observed_signals", {})),
        "deferred": dict(state.get("sat_safety_deferred_observations", {})),
        "pending_tx": dict(state.get("sat_safety_pending_emission_transactions", {})),
        "reserved": session.event_contract.deferred_unpublished,
        "events": session.recorder.event_count,
        "phase7_pending": dict(getattr(runtime, "_pending", {}) or {}),
        "phase7_tx": dict(getattr(runtime, "_signal_transactions", {}) or {}),
    }


# ---- 構築: 整合しない対は signal にならない ---------------------------------


@pytest.mark.parametrize("action", ["OBSERVED", "COMPLETED"])
@pytest.mark.parametrize(("reason_id", "refs"), [
    (REPLAY, (A,)),                      # 指摘 1 の形
    (REPLAY, ("pair:input_correspondence:r0",)),
    (REPLAY, (R, A)),                    # 混在
    (REPLAY, ()),                        # 空
    (REPLAY, ("unknown-root",)),         # 未知の根拠
    (ANALYSIS, (R,)),                    # replay だけの根拠に解析の id
    (PARTITION, ()),
    (PARTITION, (R,)),
])
def test_an_inconsistent_pair_cannot_be_built_as_a_signal(action, reason_id, refs):
    extra = {"proof_artifact_digest": "contract-proof"} if action == "COMPLETED" else {}
    with pytest.raises(SatSafetyBlockerInconsistent):
        SatSafetyBlockerProductionSignal(
            action=action, reason_id=reason_id, canonical_target_key=("k",),
            missing_semantic_fact=("m",), evidence_refs=refs, producer_id="p", **extra,
        )


@pytest.mark.parametrize(("reason_id", "refs"), [
    (REPLAY, (R,)), (ANALYSIS, (A,)), (ANALYSIS, (R, A)), (ANALYSIS, ()), (ANALYSIS, ("unknown-root",)),
    (PARTITION, ("pairwise",)),
])
def test_consistent_pairs_are_signals(reason_id, refs):
    assert _observed(reason_id, refs).blocker.reason_id == reason_id


# ---- 通常経路: 公開済みの観測に対する完了 -----------------------------------


@pytest.mark.parametrize("entry", [_complete_conditionally, _complete_directly])
def test_a_published_analysis_cause_is_never_completed_and_nothing_changes(entry):
    session = _connector().begin({"phase": "pr-a", "case": "normal-analysis"})
    observed = _observed(ANALYSIS, (A,))
    with production_signal_scope(session):
        assert _observe(observed) == 1
        before = _state(session)
        assert entry(_completion(observed)) == 0
        assert _state(session) == before
        assert session.domain_signal_error_kinds == ["ValueError"]


@pytest.mark.parametrize("entry", [_complete_conditionally, _complete_directly])
@pytest.mark.parametrize(("reason_id", "observed_refs", "claimed_refs"), [
    (REPLAY, (R,), (R, R)),
    (PARTITION, ("pairwise",), ("monolithic",)),
])
def test_a_completion_that_swaps_the_recorded_evidence_is_refused(entry, reason_id, observed_refs, claimed_refs):
    """occurrence の identity は根拠を含まない。完了が根拠を差し替えても同じ
    occurrence を指すので、記録した観測と同じ blocker であることを要求する。"""
    session = _connector().begin({"phase": "pr-a", "case": "normal-swap"})
    observed = _observed(reason_id, observed_refs)
    with production_signal_scope(session):
        assert _observe(observed) == 1
        before = _state(session)
        assert entry(_completion(observed, evidence_refs=claimed_refs)) == 0
        assert _state(session) == before
        assert session.domain_signal_error_kinds == ["ValueError"]


@pytest.mark.parametrize("entry", [_complete_conditionally, _complete_directly])
@pytest.mark.parametrize(("reason_id", "refs"), [(REPLAY, (R,)), (PARTITION, ("pairwise",))])
def test_a_completion_that_restates_a_completable_observation_completes_it(entry, reason_id, refs):
    session = _connector().begin({"phase": "pr-a", "case": "normal-ok"})
    observed = _observed(reason_id, refs)
    with production_signal_scope(session):
        assert _observe(observed) == 1
        assert entry(_completion(observed)) == 1
        assert len(session.domain_signal_state["sat_safety_completed"]) == 1
        assert session.domain_signal_error_kinds == []


# ---- deferred 経路: 約束の破棄と予約の解放 ---------------------------------


def test_a_deferred_analysis_promise_is_not_dropped_and_keeps_its_reservation():
    session = _connector().begin({"phase": "pr-a", "case": "deferred-analysis"})
    observed = _observed(ANALYSIS, (A,), defer=True)
    with production_signal_scope(session):
        assert _observe(observed) == 0
        before = _state(session)
        assert before["reserved"] == 1 and len(before["deferred"]) == 1
        assert _complete_conditionally(_completion(observed)) == 0
        assert _state(session) == before
        assert session.domain_signal_error_kinds == ["ValueError"]


@pytest.mark.parametrize(("reason_id", "observed_refs", "claimed_refs"), [
    (REPLAY, (R,), (R, R)),
    (PARTITION, ("pairwise",), ("monolithic",)),
])
def test_a_deferred_promise_is_not_dropped_by_a_completion_that_swaps_its_evidence(reason_id, observed_refs, claimed_refs):
    session = _connector().begin({"phase": "pr-a", "case": "deferred-swap"})
    observed = _observed(reason_id, observed_refs, defer=True)
    with production_signal_scope(session):
        assert _observe(observed) == 0
        before = _state(session)
        assert _complete_conditionally(_completion(observed, evidence_refs=claimed_refs)) == 0
        assert _state(session) == before
        assert session.domain_signal_error_kinds == ["ValueError"]


def test_a_deferred_replay_promise_is_retired_by_its_own_completion():
    session = _connector().begin({"phase": "pr-a", "case": "deferred-replay"})
    observed = _observed(REPLAY, (R,), defer=True)
    with production_signal_scope(session):
        assert _observe(observed) == 0
        assert session.event_contract.deferred_unpublished == 1
        assert _complete_conditionally(_completion(observed)) == 0
        assert session.event_contract.deferred_unpublished == 0
        assert "sat_safety_deferred_observations" not in session.domain_signal_state
        assert session.domain_signal_error_kinds == []


# ---- 束縛した counterexample による完了 -------------------------------------


def test_the_bound_counterexample_completes_its_replay_cause_only_and_records_no_failure():
    receipt = _safe_pairwise_receipt()
    binding = SafeCounterexampleProductionSignal.from_pairwise_receipt(receipt).counterexample_binding
    session = _connector().begin({"phase": "pr-a", "case": "bound"})
    analysis = _observed(ANALYSIS, (A,), key=("bound", "analysis"), binding=binding)
    replay = _observed(REPLAY, (R,), key=("bound", "replay"), binding=binding)
    with production_signal_scope(session):
        assert _observe(analysis) == 1 and _observe(replay) == 1
        assert complete_observed_sat_safety_for_counterexample(
            SafeCounterexampleProductionSignal.from_pairwise_receipt(receipt)
        ) == 1
        # 解析の不安全は完了の signal を作らずに skip する（encoder の拒否に頼らない）。
        assert session.domain_signal_error_kinds == []
        assert len(session.domain_signal_state["sat_safety_completed"]) == 1


# ---- 最終 authority（監査済みの producer manifest を有効にした session） -------


def _finish(session, connector, case_id):
    return connector.finish(session, _LegacyResult(Outcome.NOT_EQ), case_id=case_id)


@pytest.mark.parametrize("defer", [False, True])
@pytest.mark.parametrize("swap", [False, True])
def test_with_the_audited_manifest_an_analysis_cause_never_reaches_not_eq(defer, swap):
    connector = _manifest_connector()
    session = connector.begin({"phase": "pr-a", "case": f"manifest-analysis-{defer}-{swap}"})
    observed = _observed(ANALYSIS, (A,), defer=defer)
    completion = _completion(observed, evidence_refs=("function2:other",) if swap else (A,))
    with production_signal_scope(session):
        _observe(observed)
        _complete_conditionally(completion)
        # Phase 7 の runtime は決め手の event を finish まで buffer する（戻り値は 0）。
        emit_safe_counterexample_production_signal(safety_receipt=_safe_pairwise_receipt())
    # 根拠を差し替えた完了も同じ occurrence を名指す（identity は根拠を含まない）ので、
    # どちらも拒否されて記録され、finish が encoding の失敗として止める（pair は ERROR）。
    message = "does not restate its recorded observation" if swap else "not admissible for an analysis-unsafety cause"
    with pytest.raises(ValueError, match=message):
        _finish(session, connector, "manifest-analysis")


def test_with_the_audited_manifest_an_analysis_cause_without_completion_is_unknown():
    """完了を試みない通常の形: 束縛した safe counterexample があっても cause は残り UNKNOWN。"""
    receipt = _safe_pairwise_receipt()
    binding = SafeCounterexampleProductionSignal.from_pairwise_receipt(receipt).counterexample_binding
    connector = _manifest_connector()
    session = connector.begin({"phase": "pr-a", "case": "manifest-analysis-open"})
    with production_signal_scope(session):
        _observe(_observed(ANALYSIS, (A,), binding=binding))
        complete_observed_sat_safety_for_counterexample(
            SafeCounterexampleProductionSignal.from_pairwise_receipt(receipt)
        )
        emit_safe_counterexample_production_signal(safety_receipt=receipt)
        assert session.domain_signal_error_kinds == []
    evidence = _finish(session, connector, "manifest-analysis-open")
    assert evidence.pilot_result.candidate.decision_receipt.outcome is Outcome.UNKNOWN
    assert [row.reason_id for row in evidence.pilot_result.reduction.projection.c_active_base] == [ANALYSIS]


def test_with_the_audited_manifest_a_replay_type_sat_is_not_eq():
    connector = _manifest_connector()
    session = connector.begin({"phase": "pr-a", "case": "manifest-replay"})
    observed = _observed(REPLAY, (R,))
    with production_signal_scope(session):
        _observe(observed)
        _complete_conditionally(_completion(observed))
        assert session.domain_signal_error_kinds == []
        # Phase 7 の runtime は決め手の event を finish まで buffer する（戻り値は 0）。
        emit_safe_counterexample_production_signal(safety_receipt=_safe_pairwise_receipt())
    evidence = _finish(session, connector, "manifest-replay")
    assert evidence.pilot_result.candidate.decision_receipt.outcome is Outcome.NOT_EQ


def test_with_the_audited_manifest_partition_ambiguity_keeps_its_own_completion():
    connector = _manifest_connector()
    session = connector.begin({"phase": "pr-a", "case": "manifest-partition"})
    observed = _observed(PARTITION, ("pairwise",))
    with production_signal_scope(session):
        _observe(observed)
        _complete_conditionally(_completion(observed))
        assert session.domain_signal_error_kinds == []
        # Phase 7 の runtime は決め手の event を finish まで buffer する（戻り値は 0）。
        emit_safe_counterexample_production_signal(safety_receipt=_safe_pairwise_receipt())
    evidence = _finish(session, connector, "manifest-partition")
    assert evidence.pilot_result.candidate.decision_receipt.outcome is Outcome.NOT_EQ


# ---- 構築を迂回した signal（多層の防御） -------------------------------------


def _bypassed(action, reason_id, refs, **extra):
    """``__post_init__`` を通らずに作った signal（in-process の迂回を模す）。"""
    signal = object.__new__(SatSafetyBlockerProductionSignal)
    fields = dict(
        action=action, reason_id=reason_id, canonical_target_key=("bypass",),
        missing_semantic_fact=("m",), evidence_refs=tuple(refs), producer_id="p",
        proof_artifact_digest=None, counterexample_binding=None, defer_until_terminal=False,
    )
    fields.update(extra)
    for name, value in fields.items():
        object.__setattr__(signal, name, value)
    return signal


def test_the_encoder_refuses_an_inconsistent_signal_that_bypassed_construction():
    session = _connector().begin({"phase": "pr-a", "case": "bypass-observe"})
    with production_signal_scope(session):
        before = _state(session)
        assert emit_sat_safety_signal(_bypassed("OBSERVED", REPLAY, (A,))) == 0
        assert _state(session) == before
        assert session.domain_signal_error_kinds == ["SatSafetyBlockerInconsistent"]


def test_the_bound_completion_records_an_inconsistent_recorded_observation_instead_of_completing():
    receipt = _safe_pairwise_receipt()
    safe = SafeCounterexampleProductionSignal.from_pairwise_receipt(receipt)
    session = _connector().begin({"phase": "pr-a", "case": "bypass-bound"})
    session.domain_signal_state["sat_safety_observed_signals"] = {
        "forged-occurrence": _bypassed(
            "OBSERVED", REPLAY, (A,), counterexample_binding=safe.counterexample_binding,
        ),
    }
    with production_signal_scope(session):
        assert complete_observed_sat_safety_for_counterexample(safe) == 0
        assert session.domain_signal_error_kinds == ["SatSafetyBlockerInconsistent"]
        assert "sat_safety_completed" not in session.domain_signal_state


# ---- 前提: producer は根拠を occurrence の対象に焼き込む ----------------------


def test_every_producer_binds_its_evidence_into_the_target_key(monkeypatch):
    """occurrence の identity は evidence ref を含まない。同じ対象を別の根拠で観測すると
    後の完了は「言い直していない」として拒否される（fail-closed）。それが起きないのは、
    producer が根拠を ``canonical_target_key`` に入れているからで、その前提をここで固定する。"""
    from scripts.function_tracer_pcode.authority.lifecycle import production_signals

    captured = []
    monkeypatch.setattr(production_signals, "emit_sat_safety_signal",
                        lambda signal, **_k: captured.append(signal) or 0)
    from scripts.function_tracer_pcode.tests.unit._input_correspondence_support import comparison_of
    from scripts.function_tracer_pcode.tests.unit.test_unknown_taxonomy_v2_phase6_sat_safety import (
        _strategy_and_surface,
    )

    strategy, analysis1, analysis2, case1, case2 = _strategy_and_surface()
    with comparison_of(analysis1, analysis2):
        # 実際の producer（blocker の観測は ref ごと、曖昧さの観測は pair の段）。
        strategy._make_sat_unsafety_unknown_reason(
            (A, R), analysis1, analysis2, case1=case1, case2=case2, pair_id="(0,1)", stage="S_MONOLITHIC_FALLBACK",
        )
        strategy._observe_v2_sat_counterexample_ambiguity(
            ("pairwise", "monolithic"), analysis1, analysis2, case1=case1, case2=case2, pair_id="(0,1)",
        )

    def flat(value):
        if isinstance(value, (tuple, list)):
            for item in value:
                yield from flat(item)
        else:
            yield value

    assert len(captured) == 3
    for signal in captured:
        assert set(signal.evidence_refs) <= set(flat(signal.canonical_target_key)), signal


# ---- 入口の検査: 状態変更・重複判定・deferred 登録より前に owner の規則 -----------
#
# 契約: SAT-safety の blocker を受け取る全ての入口は、identity の計算・重複判定・
# deferred の登録・Phase 7 の取引・完了の照合より前に (id, 根拠) を分類する。
# 不整合なら何も変えずに失敗を記録し（pair は ERROR）、決して黙って捨てない。

BAD_PAIRS = [
    pytest.param((A,), id="analysis-evidence"),
    pytest.param((R, A), id="mixed-evidence"),
    pytest.param((), id="empty-evidence"),
]


def _bad_replay(refs, *, action="OBSERVED", defer=False, key=("contract",)):
    """正常な replay 観測と同じ identity（id・対象・欠けた事実）で、根拠だけが不整合な signal。"""
    return _bypassed(
        action, REPLAY, refs,
        canonical_target_key=key,
        missing_semantic_fact=("counterexample_safety_gate_unproven", "contract"),
        producer_id=_SITES[REPLAY][0 if action == "OBSERVED" else 1].producer_id,
        proof_artifact_digest="contract-proof" if action == "COMPLETED" else None,
        defer_until_terminal=defer,
    )


def _entries():
    return {
        "observe": lambda s: _observe(s),
        "complete-conditionally": lambda s: _complete_conditionally(s),
        "complete-directly": lambda s: _complete_directly(s),
    }


@pytest.mark.parametrize("refs", BAD_PAIRS)
@pytest.mark.parametrize("situation", [
    "fresh", "deferred", "duplicate-of-published", "duplicate-of-deferred", "publication-of-deferred",
])
def test_an_inconsistent_observation_is_refused_before_dedupe_or_deferral(situation, refs):
    session = _connector().begin({"phase": "pr-a", "case": f"entry-{situation}"})
    good = _observed(REPLAY, (R,), defer=situation in {"duplicate-of-deferred", "publication-of-deferred"})
    with production_signal_scope(session):
        if situation.startswith(("duplicate", "publication")):
            _observe(good)
        before = _state(session)
        bad = _bad_replay(refs, defer=situation in {"deferred", "duplicate-of-deferred"})
        assert _observe(bad) == 0
        assert _state(session) == before
        assert session.domain_signal_error_kinds == ["SatSafetyBlockerInconsistent"]


@pytest.mark.parametrize("refs", BAD_PAIRS)
@pytest.mark.parametrize("entry", ["complete-conditionally", "complete-directly"])
@pytest.mark.parametrize("recorded", ["published", "deferred"])
def test_an_inconsistent_completion_is_refused_before_any_lookup(recorded, entry, refs):
    session = _connector().begin({"phase": "pr-a", "case": f"entry-complete-{recorded}"})
    good = _observed(REPLAY, (R,), defer=recorded == "deferred")
    with production_signal_scope(session):
        _observe(good)
        before = _state(session)
        assert _entries()[entry](_bad_replay(refs, action="COMPLETED")) == 0
        assert _state(session) == before
        assert session.domain_signal_error_kinds == ["SatSafetyBlockerInconsistent"]


def test_the_loop_handoff_consumer_refuses_an_inconsistent_handoff_before_dedupe():
    from scripts.function_tracer_pcode.authority.lifecycle.production_signals import (
        _consume_loop_sat_safety_handoffs,
    )

    # handoff の消費は route を持つ composite encoder を要る（監査済みの manifest の session）。
    session = _manifest_connector().begin({"phase": "pr-a", "case": "entry-loop-handoff"})
    with production_signal_scope(session):
        _observe(_observed(REPLAY, (R,)))
        before = _state(session)
        session.domain_signal_state["loop_sat_safety_handoffs"] = [_bad_replay((A,))]
        assert _consume_loop_sat_safety_handoffs(session) == 0
        session.domain_signal_state.pop("loop_sat_safety_handoffs", None)
        assert _state(session) == before
        assert session.domain_signal_error_kinds == ["SatSafetyBlockerInconsistent"]


@pytest.mark.parametrize("manifest", [False, True])
@pytest.mark.parametrize("defer", [False, True])
def test_an_inconsistent_duplicate_of_a_replay_observation_never_lets_the_pair_reach_not_eq(defer, manifest):
    """指摘の形: 正常な replay の観測と同じ identity で解析の根拠を持つ signal を再送し、
    replay を完了して safe counterexample を出す。以前は重複として捨てられ NOT_EQ だった。"""
    connector = _manifest_connector() if manifest else _connector()
    session = connector.begin({"phase": "pr-a", "case": f"dup-{defer}-{manifest}"})
    good = _observed(REPLAY, (R,), defer=defer)
    with production_signal_scope(session):
        _observe(good)
        _observe(_bad_replay((A,), defer=defer))
        _complete_conditionally(_completion(good))
        emit_safe_counterexample_production_signal(safety_receipt=_safe_pairwise_receipt())
    with pytest.raises(ValueError, match="does not match its evidence refs"):
        _finish(session, connector, "dup")


@pytest.mark.parametrize(("recorded_deferred", "defer"), [(False, False), (True, True), (True, False)])
def test_a_consistent_reobservation_with_other_evidence_is_a_recorded_collision(recorded_deferred, defer):
    """同じ identity を別の（整合した）根拠で観測し直すのは、重複として捨てずに衝突として記録する
    （公開済みの再観測・deferred の再登録・deferred の約束の公開の全て）。"""
    session = _connector().begin({"phase": "pr-a", "case": f"collision-{recorded_deferred}-{defer}"})
    with production_signal_scope(session):
        _observe(_observed(PARTITION, ("pairwise",), defer=recorded_deferred))
        before = _state(session)
        assert _observe(_observed(PARTITION, ("monolithic",), defer=defer)) == 0
        assert _state(session) == before
        assert session.domain_signal_error_kinds == ["ValueError"]


@pytest.mark.parametrize("defer", [False, True])
def test_an_exact_reobservation_is_still_a_silent_duplicate(defer):
    """対照: 同じ blocker の再観測（公開済み・deferred の再登録）は従来どおり重複。"""
    session = _connector().begin({"phase": "pr-a", "case": f"dup-ok-{defer}"})
    observed = _observed(REPLAY, (R,), defer=defer)
    with production_signal_scope(session):
        _observe(observed)
        before = _state(session)
        assert _observe(observed) == 0
        assert _state(session) == before
        assert session.domain_signal_error_kinds == []


def test_publishing_a_deferred_promise_is_not_a_duplicate():
    """対照（Issue #110）: deferred の約束を defer せずに観測すると公開される（重複ではない）。"""
    session = _connector().begin({"phase": "pr-a", "case": "publish-promise"})
    with production_signal_scope(session):
        _observe(_observed(REPLAY, (R,), defer=True))
        assert _observe(_observed(REPLAY, (R,))) == 1
        assert len(session.domain_signal_state["sat_safety_observed"]) == 1
        assert session.domain_signal_error_kinds == []
