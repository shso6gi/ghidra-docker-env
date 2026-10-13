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
        "promised_ids": set(session.event_contract._deferred_ids),
        "published_ids": set(session.event_contract._published_ids),
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
    session.domain_signal_state["sat_safety_observed"] = {"forged-occurrence"}
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
@pytest.mark.parametrize("manifest", [False, True], ids=["plain", "manifest"])
def test_an_inconsistent_observation_is_refused_before_dedupe_or_deferral(manifest, situation, refs):
    session = (_manifest_connector() if manifest else _connector()).begin(
        {"phase": "pr-a", "case": f"entry-{situation}"}
    )
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
@pytest.mark.parametrize("manifest", [False, True], ids=["plain", "manifest"])
def test_an_inconsistent_completion_is_refused_before_any_lookup(manifest, recorded, entry, refs):
    session = (_manifest_connector() if manifest else _connector()).begin(
        {"phase": "pr-a", "case": f"entry-complete-{recorded}"}
    )
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


# ---- authority 側の経路（production の入口を通らない generic な route） ----------


def test_the_identity_owner_refuses_an_inconsistent_pair_on_every_identity_api():
    """重複判定・deferred の登録・ABI の変換が使う identity は、検証済みの blocker からしか
    作れない（production の入口の検査を通らない route でも）。"""
    connector = _manifest_connector()
    session = connector.begin({"phase": "pr-a", "case": "identity-owner"})
    bad = _bad_replay((A,))
    encoder = session.domain_signal_encoder
    before = _state(session)
    for api in (encoder.has_observed, encoder.authority_for_signal, encoder.prepare_sat_safety_transformation):
        with pytest.raises(SatSafetyBlockerInconsistent):
            api(session, bad)
    assert _state(session) == before


def test_the_generic_route_refuses_to_complete_an_analysis_cause():
    """``session.emit_domain_signal`` へ直接渡した完了（production の入口を通らない）も、
    encoder が記録した観測に対して拒否する。"""
    session = _connector().begin({"phase": "pr-a", "case": "generic-complete"})
    observed = _observed(ANALYSIS, (A,))
    with production_signal_scope(session):
        assert _observe(observed) == 1
        before = _state(session)
        assert session.emit_domain_signal(_completion(observed)) == 0
        assert _state(session) == before
        assert session.domain_signal_error_kinds == ["ValueError"]


def test_a_deferred_reregistration_from_another_site_is_a_recorded_collision():
    """deferred の約束は (signal, site) ごと記録する。同じ blocker を別の site から約束し直すと
    衝突として記録する（約束の持ち主を黙って差し替えない）。"""
    session = _connector().begin({"phase": "pr-a", "case": "deferred-site"})
    observed = _observed(REPLAY, (R,), defer=True)
    with production_signal_scope(session):
        _observe(observed)
        before = _state(session)
        assert emit_sat_safety_signal(observed, producer_site_manifest_id="pairwise-loop-sat-safety-observed") == 0
        assert _state(session) == before
        assert session.domain_signal_error_kinds == ["ValueError"]


# ---- 同じ identity の衝突: 全ての重複判定の route で同じ規則 ----------------------


def test_a_colliding_loop_handoff_is_a_recorded_collision():
    from scripts.function_tracer_pcode.authority.lifecycle.production_signals import (
        _consume_loop_sat_safety_handoffs,
    )

    session = _manifest_connector().begin({"phase": "pr-a", "case": "loop-collision"})
    with production_signal_scope(session):
        _observe(_observed(ANALYSIS, (A,)))
        before = _state(session)
        session.domain_signal_state["loop_sat_safety_handoffs"] = [
            _observed(ANALYSIS, ("function2:other",)),
        ]
        assert _consume_loop_sat_safety_handoffs(session) == 0
        assert "loop_sat_safety_handoffs" not in session.domain_signal_state
        assert _state(session) == before
        assert session.domain_signal_error_kinds == ["ValueError"]


def test_a_colliding_observation_on_the_generic_route_is_a_recorded_collision():
    """``session.emit_domain_signal`` へ直接渡した観測（ABI の handoff・finalize の route）も、
    encoder の重複判定が同じ規則で衝突を記録する。"""
    session = _connector().begin({"phase": "pr-a", "case": "generic-collision"})
    with production_signal_scope(session):
        _observe(_observed(PARTITION, ("pairwise",)))
        before = _state(session)
        assert session.emit_domain_signal(_observed(PARTITION, ("monolithic",))) == 0
        assert _state(session) == before
        assert session.domain_signal_error_kinds == ["ValueError"]


def test_an_exact_observation_on_the_generic_route_is_still_a_duplicate():
    session = _connector().begin({"phase": "pr-a", "case": "generic-dup"})
    observed = _observed(PARTITION, ("pairwise",))
    with production_signal_scope(session):
        _observe(observed)
        assert session.emit_domain_signal(observed) == 0
        assert session.domain_signal_error_kinds == []


# ---- deferred の約束を公開した後の lifecycle ------------------------------------


def test_a_published_promise_leaves_the_deferred_ledger_and_its_reservation():
    session = _connector().begin({"phase": "pr-a", "case": "promise-published"})
    observed = _observed(REPLAY, (R,), defer=True)
    with production_signal_scope(session):
        _observe(observed)
        assert session.event_contract.deferred_unpublished == 1
        assert _observe(replace(observed, defer_until_terminal=False)) == 1
        assert "sat_safety_deferred_observations" not in session.domain_signal_state
        assert session.event_contract.deferred_unpublished == 0
        # 記録の正本は公開済みの観測: 再観測は重複、再 defer も重複。
        assert _observe(observed) == 0
        assert _observe(replace(observed, defer_until_terminal=False)) == 0
        assert session.domain_signal_error_kinds == []


@pytest.mark.parametrize(("reason_id", "refs", "outcome"), [
    (REPLAY, (R,), Outcome.NOT_EQ),
    (ANALYSIS, (A,), None),
])
def test_a_published_promise_is_completed_or_refused_as_a_published_cause(reason_id, refs, outcome):
    connector = _manifest_connector()
    session = connector.begin({"phase": "pr-a", "case": f"promise-lifecycle-{reason_id}"})
    observed = _observed(reason_id, refs, defer=True)
    with production_signal_scope(session):
        _observe(observed)
        _observe(replace(observed, defer_until_terminal=False))
        _complete_conditionally(_completion(observed))
        emit_safe_counterexample_production_signal(safety_receipt=_safe_pairwise_receipt())
    if outcome is None:
        with pytest.raises(ValueError, match="not admissible for an analysis-unsafety cause"):
            _finish(session, connector, "promise-lifecycle")
    else:
        evidence = _finish(session, connector, "promise-lifecycle")
        assert evidence.pilot_result.candidate.decision_receipt.outcome is outcome


def test_no_encoder_means_no_emission():
    from scripts.function_tracer_pcode.authority.lifecycle.pilot import ProductionDualWritePilotConnector
    from scripts.function_tracer_pcode.authority.lifecycle.reducer import ShadowLifecycleReducer
    from scripts.function_tracer_pcode.authority.domains.sat_safety import (
        SAT_SAFETY_RECOVERY_REGISTRY,
        SAT_SAFETY_REASON_REGISTRY,
    )

    session = ProductionDualWritePilotConnector(ShadowLifecycleReducer(
        reason_registry=SAT_SAFETY_REASON_REGISTRY, recovery_registry=SAT_SAFETY_RECOVERY_REGISTRY,
    )).begin({"phase": "pr-a", "case": "no-encoder"})
    with production_signal_scope(session):
        assert _observe(_observed(REPLAY, (R,))) == 0
        assert _complete_conditionally(_completion(_observed(REPLAY, (R,)))) == 0


def test_a_loop_handoff_colliding_with_a_deferred_promise_is_a_recorded_collision():
    from scripts.function_tracer_pcode.authority.lifecycle.production_signals import (
        _consume_loop_sat_safety_handoffs,
    )

    session = _manifest_connector().begin({"phase": "pr-a", "case": "loop-promise-collision"})
    with production_signal_scope(session):
        _observe(_observed(ANALYSIS, (A,), defer=True))
        before = _state(session)
        session.domain_signal_state["loop_sat_safety_handoffs"] = [
            _observed(ANALYSIS, ("function2:other",)),
        ]
        assert _consume_loop_sat_safety_handoffs(session) == 0
        assert "loop_sat_safety_handoffs" not in session.domain_signal_state
        assert _state(session) == before
        assert session.domain_signal_error_kinds == ["ValueError"]


def test_a_refused_publication_of_a_promise_keeps_the_promise(monkeypatch):
    """約束の公開が失敗したら（ここでは stream への追加の失敗）、約束も予約も残す。
    台帳を変えるのは event の commit が成功した後だけ（成功の確認 → 状態の変更の順）。"""
    session = _connector().begin({"phase": "pr-a", "case": "promise-refused"})
    promise = _observed(REPLAY, (R,), defer=True)
    with production_signal_scope(session):
        _observe(promise)
        before = _state(session)

        def fail_append(_intents, _commit_callback=None, **_k):
            raise RuntimeError("forced stream append failure")

        monkeypatch.setattr(session, "_emit_many_admitted", fail_append)
        assert _observe(replace(promise, defer_until_terminal=False)) == 0
        assert _state(session) == before
        assert session.domain_signal_error_kinds == ["RuntimeError"]

def test_a_non_restating_completion_of_a_completed_cause_is_refused_on_the_generic_route():
    session = _connector().begin({"phase": "pr-a", "case": "generic-completed-swap"})
    observed = _observed(PARTITION, ("pairwise",))
    with production_signal_scope(session):
        _observe(observed)
        assert _complete_conditionally(_completion(observed)) == 1
        before = _state(session)
        assert session.emit_domain_signal(_completion(observed, evidence_refs=("monolithic",))) == 0
        assert _state(session) == before
        assert session.domain_signal_error_kinds == ["ValueError"]


@pytest.mark.parametrize("route", ["entry", "generic"])
def test_a_reobservation_under_another_counterexample_binding_is_a_collision(route):
    receipt = _safe_pairwise_receipt()
    binding = SafeCounterexampleProductionSignal.from_pairwise_receipt(receipt).counterexample_binding
    session = _connector().begin({"phase": "pr-a", "case": f"binding-{route}"})
    with production_signal_scope(session):
        _observe(_observed(REPLAY, (R,), binding=binding))
        before = _state(session)
        other = _observed(REPLAY, (R,))
        assert (_observe(other) if route == "entry" else session.emit_domain_signal(other)) == 0
        assert _state(session) == before
        assert session.domain_signal_error_kinds == ["ValueError"]


# ---- review 5 の 3 件: 記録の正本は 1 つ（deferred の約束か公開済みの観測） ---------


@pytest.mark.parametrize("manifest", [False, True], ids=["plain", "manifest"])
@pytest.mark.parametrize("differs", ["evidence", "binding"])
def test_case1_the_generic_route_refuses_a_collision_with_a_deferred_promise(differs, manifest):
    receipt = _safe_pairwise_receipt()
    binding = SafeCounterexampleProductionSignal.from_pairwise_receipt(receipt).counterexample_binding
    session = (_manifest_connector() if manifest else _connector()).begin({"phase": "pr-a", "case": "case1"})
    promise = _observed(PARTITION, ("pairwise",), defer=True)
    other = (
        _observed(PARTITION, ("monolithic",)) if differs == "evidence"
        else _observed(PARTITION, ("pairwise",), binding=binding)
    )
    with production_signal_scope(session):
        _observe(promise)
        before = _state(session)
        assert session.emit_domain_signal(other) == 0
        assert _state(session) == before
        assert session.domain_signal_error_kinds == ["ValueError"]


@pytest.mark.parametrize("manifest", [False, True], ids=["plain", "manifest"])
def test_case2_a_promise_published_on_the_generic_route_is_completed_as_a_published_cause(manifest):
    connector = _manifest_connector() if manifest else _connector()
    session = connector.begin({"phase": "pr-a", "case": "case2"})
    promise = _observed(REPLAY, (R,), defer=True)
    with production_signal_scope(session):
        _observe(promise)
        if manifest:
            session.record_phase7_pre_emission_activation(
                _SITES[REPLAY][0].site_id, published := replace(promise, defer_until_terminal=False),
            )
        else:
            published = replace(promise, defer_until_terminal=False)
        session.emit_domain_signal(published)
        assert "sat_safety_deferred_observations" not in session.domain_signal_state
        assert session.event_contract.deferred_unpublished == 0
        _complete_conditionally(_completion(promise))
        assert len(session.domain_signal_state["sat_safety_completed"]) == 1
        emit_safe_counterexample_production_signal(safety_receipt=_safe_pairwise_receipt())
    evidence = _finish(session, connector, "case2")
    assert evidence.pilot_result.candidate.decision_receipt.outcome is Outcome.NOT_EQ


@pytest.mark.parametrize("manifest", [False, True], ids=["plain", "manifest"])
def test_case3_finalize_keeps_a_promise_whose_publication_is_refused(manifest, monkeypatch):
    """finalize は約束を公開の遷移で処理する。検証が公開を拒んだら約束も予約も消さない
    （拒否は記録済み）。予算による打切りとは区別する。"""
    from scripts.function_tracer_pcode.authority.lifecycle.production_signals import (
        finalize_deferred_sat_safety_observations,
    )

    session = (_manifest_connector() if manifest else _connector()).begin({"phase": "pr-a", "case": "case3"})
    promise = _observed(REPLAY, (R,), defer=True)
    with production_signal_scope(session):
        _observe(promise)
        # 公開を検証が拒む状況を、記録済みの約束の根拠を壊して作る（構築を迂回した記録）。
        pending = session.domain_signal_state["sat_safety_deferred_observations"]
        (occurrence_id, (recorded, site)), = pending.items()
        broken = _bad_replay((A,), defer=True)
        pending[occurrence_id] = (broken, site)
        before = _state(session)
        finalize_deferred_sat_safety_observations(session)
        assert _state(session) == before
        assert "SatSafetyBlockerInconsistent" in session.domain_signal_error_kinds


# ---- 状態 × 遷移 × 入口の行列（本番の API だけで作る。期待は台帳の契約の oracle から） ----

from scripts.function_tracer_pcode.authority.domains.sat_safety_ledger import (  # noqa: E402
    BlockerState,
    SatSafetyBlockerLedger,
)

_STATES = ["absent", "promised", "published", "published_from_promise", "completed"]
# safe receipt は scope の中で作ると event を出すので、束縛は scope の外で 1 回だけ作る。
_OTHER_BINDING = SafeCounterexampleProductionSignal.from_pairwise_receipt(
    _safe_pairwise_receipt(query="(assert (= y 1))\n(check-sat)")
).counterexample_binding
_LOOP_HANDOFF_PRODUCER = "loop-model-bound-refutation-handoff-v1"


def _generic(session, signal):
    """generic な route（ABI の handoff・finalize と同じく Phase 7 の activation を開いて emit）。"""
    if getattr(session, "phase7_runtime", None) is not None:
        site = _SITES[signal.reason_id][0 if signal.action == "OBSERVED" else 1].site_id
        session.record_phase7_pre_emission_activation(site, signal)
    return session.emit_domain_signal(signal)


def _handoff(session, signal):
    from scripts.function_tracer_pcode.authority.lifecycle.production_signals import (
        _consume_loop_sat_safety_handoffs,
    )

    session.domain_signal_state["loop_sat_safety_handoffs"] = [
        replace(signal, producer_id=_LOOP_HANDOFF_PRODUCER)
    ]
    try:
        return _consume_loop_sat_safety_handoffs(session)
    except ValueError:
        session.domain_signal_state.pop("loop_sat_safety_handoffs", None)
        raise


def _finalize(session, _signal):
    from scripts.function_tracer_pcode.authority.lifecycle.production_signals import (
        finalize_deferred_sat_safety_observations,
    )

    finalize_deferred_sat_safety_observations(session)


def _setup(session, state):
    promise = _observed(REPLAY, (R,), defer=True)
    published = replace(promise, defer_until_terminal=False)
    if state == "promised":
        _observe(promise)
    elif state == "published":
        _observe(published)
    elif state == "published_from_promise":
        _observe(promise)
        _observe(published)
    elif state == "completed":
        _observe(published)
        _complete_conditionally(_completion(published))
    return promise, published


def _ledger_state(session, signal):
    occurrence_id = session.domain_signal_encoder.authority_for_signal(session, signal).occurrence.occurrence_id
    return SatSafetyBlockerLedger(session).state_of(occurrence_id)[0]


def _entry_observe(_session, signal):
    return _observe(signal)


def _entry_complete_conditionally(_session, signal):
    return _complete_conditionally(signal)


def _entry_complete_directly(_session, signal):
    return _complete_directly(signal)


_OPS = {
    # name: (route, signal builder, expectation(state) -> (next_state, failure))
    "observe-defer-same/entry": (_entry_observe, lambda p, q: p),
    "observe-publish-same/entry": (_entry_observe, lambda p, q: q),
    "observe-publish-same/generic": (_generic, lambda p, q: q),
    "observe-publish-same/handoff": (_handoff, lambda p, q: q),
    "observe-collide-evidence/entry": (_entry_observe, lambda p, q: replace(q, evidence_refs=(R, R))),
    "observe-collide-evidence/generic": (_generic, lambda p, q: replace(q, evidence_refs=(R, R))),
    "observe-collide-evidence/handoff": (_handoff, lambda p, q: replace(q, evidence_refs=(R, R))),
    "observe-collide-binding/entry": (_entry_observe, lambda p, q: replace(q, counterexample_binding=_OTHER_BINDING)),
    "observe-collide-binding/generic": (_generic, lambda p, q: replace(q, counterexample_binding=_OTHER_BINDING)),
    "complete-same/conditional": (_entry_complete_conditionally, lambda p, q: _completion(q)),
    "complete-same/direct": (_entry_complete_directly, lambda p, q: _completion(q)),
    "complete-same/generic": (_generic, lambda p, q: _completion(q)),
    "complete-swapped/conditional": (_entry_complete_conditionally, lambda p, q: _completion(q, evidence_refs=(R, R))),
    "complete-swapped/direct": (_entry_complete_directly, lambda p, q: _completion(q, evidence_refs=(R, R))),
    "complete-swapped/generic": (_generic, lambda p, q: _completion(q, evidence_refs=(R, R))),
    "finalize": (_finalize, lambda p, q: None),
}


_FAILURE_MESSAGES = {
    "observe-collide": "collides with its recorded observation",
    "complete-swapped": "does not restate its recorded observation",
    "complete-nothing": "no observed active occurrence",
    "complete-generic-promise": "goes through the lifecycle entry",
    "phase7-noop": "discovered activation disposition is not site-sealed",
}


def _expected_message(state, op, manifest):
    now = "published" if state == "published_from_promise" else state
    kind, route = (op.split("/") + [""])[:2]
    if kind.startswith("observe-collide") and now != "absent":
        return _FAILURE_MESSAGES["observe-collide"]
    if kind in {"complete-same", "complete-swapped"} and now == "absent":
        return _FAILURE_MESSAGES["complete-nothing"]
    if kind == "complete-swapped":
        return _FAILURE_MESSAGES["complete-swapped"]
    if kind == "complete-same" and now == "promised" and route == "generic":
        return _FAILURE_MESSAGES["complete-generic-promise"]
    return _FAILURE_MESSAGES["phase7-noop"]


def _oracle(state, op, manifest=False):
    """台帳の契約から導いた (次の状態, 失敗を記録するか)。"""
    next_state, failure = _ledger_oracle(state, op)
    now = "published" if state == "published_from_promise" else state
    route = op.split("/")[1] if "/" in op else ""
    if manifest and route == "generic" and op.startswith("observe") and not failure and next_state == now:
        # Phase 7 の既存の契約: ELIGIBLE だけの観測の site で、event の無い no-op に
        # activation を開くと拒否される（本番の入口は重複に activation を開かない。generic な
        # route の本番の呼び手は約束の公開だけ）。完了の site は DECISIVE なので対象外。
        return now, True
    return next_state, failure


def _ledger_oracle(state, op):
    now = {"absent": "absent", "promised": "promised", "published": "published",
           "published_from_promise": "published", "completed": "completed"}[state]
    kind, route = (op.split("/") + [""])[:2]
    if kind == "observe-defer-same":
        return ("promised" if now == "absent" else now), False
    if kind == "observe-publish-same":
        return ("published" if now in {"absent", "promised"} else now), False
    if kind.startswith("observe-collide"):
        if now == "absent":
            return "published", False  # 記録が無ければ新しい観測（衝突ではない）
        return now, True
    if kind == "complete-same":
        if now == "absent":
            return "absent", route != "conditional"
        if now == "promised":
            # 未公開の約束の完了は event の無い遷移: lifecycle の入口だけが行う
            return ("absent", False) if route != "generic" else ("promised", True)
        return "completed", False
    if kind == "complete-swapped":
        if now == "absent":
            return "absent", route != "conditional"
        return now, True
    if kind == "finalize":
        return ("published" if now == "promised" else now), False
    raise AssertionError(op)


@pytest.mark.parametrize("op", list(_OPS))
@pytest.mark.parametrize("state", _STATES)
@pytest.mark.parametrize("manifest", [False, True], ids=["plain", "manifest"])
def test_every_transition_follows_the_ledger_contract(manifest, state, op):
    route, build = _OPS[op]
    if route is _handoff and not manifest:
        pytest.skip("the loop handoff consumer needs the routed (composite) encoder")
    session = (_manifest_connector() if manifest else _connector()).begin(
        {"phase": "pr-a", "case": f"matrix-{state}-{op}"}
    )
    with production_signal_scope(session):
        promise, published = _setup(session, state)
        assert session.domain_signal_error_kinds == []
        before = _state(session)
        expected_state, expected_failure = _oracle(state, op, manifest)
        route(session, build(promise, published))
        failures = session.domain_signal_error_kinds
        assert bool(failures) is expected_failure, failures
        if expected_failure:
            assert _state(session) == before, "a refusal must not change the ledger"
            # 拒否は、この cell の契約の検査による（後段の別の検査に救われていない）。
            message = _expected_message(state, op, manifest)
            assert len(failures) == 1
            assert message in session.domain_signal_error_details[0], session.domain_signal_error_details
        assert _ledger_state(session, published).value == {
            "absent": BlockerState.ABSENT, "promised": BlockerState.PROMISED,
            "published": BlockerState.PUBLISHED, "completed": BlockerState.COMPLETED,
        }[expected_state].value
        # 不変量: 約束と公開は共存しない（state_of が検査する）、予約の数 == 約束の数
        ledger = SatSafetyBlockerLedger(session)
        assert session.event_contract.deferred_unpublished == len(ledger.promises())


# ---- 入口をまたぐ連続操作の最終判定（監査済みの manifest） ------------------------


def _publish_via(session, route, promise):
    published = replace(promise, defer_until_terminal=False)
    if route == "entry":
        _observe(published)
    elif route == "generic":
        _generic(session, published)
    else:
        _finalize(session, None)


@pytest.mark.parametrize("complete_route", ["conditional", "direct"])
@pytest.mark.parametrize("publish_route", ["entry", "generic", "finalize"])
def test_a_promised_replay_cause_published_and_completed_across_entries_is_not_eq(publish_route, complete_route):
    connector = _manifest_connector()
    session = connector.begin({"phase": "pr-a", "case": f"xentry-{publish_route}-{complete_route}"})
    promise = _observed(REPLAY, (R,), defer=True)
    with production_signal_scope(session):
        _observe(promise)
        _publish_via(session, publish_route, promise)
        assert SatSafetyBlockerLedger(session).promises() == []
        completion = _completion(promise)
        (_complete_conditionally if complete_route == "conditional" else _complete_directly)(completion)
        emit_safe_counterexample_production_signal(safety_receipt=_safe_pairwise_receipt())
        assert session.domain_signal_error_kinds == []
    evidence = _finish(session, connector, "xentry")
    assert evidence.pilot_result.candidate.decision_receipt.outcome is Outcome.NOT_EQ


@pytest.mark.parametrize("complete_route", ["conditional", "direct"])
@pytest.mark.parametrize("publish_route", ["entry", "generic", "finalize"])
def test_a_promised_analysis_cause_never_completes_across_entries(publish_route, complete_route):
    connector = _manifest_connector()
    session = connector.begin({"phase": "pr-a", "case": f"xentry-analysis-{publish_route}-{complete_route}"})
    promise = _observed(ANALYSIS, (A,), defer=True)
    with production_signal_scope(session):
        _observe(promise)
        _publish_via(session, publish_route, promise)
        completion = _completion(promise)
        (_complete_conditionally if complete_route == "conditional" else _complete_directly)(completion)
        emit_safe_counterexample_production_signal(safety_receipt=_safe_pairwise_receipt())
        assert SatSafetyBlockerLedger(session).state_of(
            session.domain_signal_encoder.authority_for_signal(session, promise).occurrence.occurrence_id
        )[0] is BlockerState.PUBLISHED
    with pytest.raises(ValueError, match="not admissible for an analysis-unsafety cause"):
        _finish(session, connector, "xentry-analysis")


def test_the_ledger_refuses_to_read_a_promise_and_a_publication_of_one_occurrence():
    """台帳の不変量: 約束と公開は共存しない。共存を見つけたら片方を優先せずに止める。"""
    session = _connector().begin({"phase": "pr-a", "case": "ledger-both"})
    observed = _observed(REPLAY, (R,))
    with production_signal_scope(session):
        _observe(observed)
        occurrence_id = session.domain_signal_encoder.authority_for_signal(session, observed).occurrence.occurrence_id
        session.domain_signal_state["sat_safety_deferred_observations"] = {
            occurrence_id: (replace(observed, defer_until_terminal=True), "site"),
        }
        with pytest.raises(ValueError, match="both a promise and a publication"):
            SatSafetyBlockerLedger(session).state_of(occurrence_id)
        assert _complete_conditionally(_completion(observed)) == 0
        assert session.domain_signal_error_kinds == ["ValueError"]


# ---- 成功の確認 → 状態の確定: event の commit の後に取引が失敗したら台帳を戻す --------


@pytest.mark.parametrize("start", ["absent", "promised"])
def test_a_publication_that_fails_after_the_encoder_commit_restores_the_ledger(start, monkeypatch):
    """encoder の commit（台帳の遷移）の後で取引の別の commit（ここでは Phase 7）が失敗したら、
    台帳も予約も取引の前に戻る（公開されていない観測を公開済みとして残さない）。"""
    session = _manifest_connector().begin({"phase": "pr-a", "case": f"post-commit-{start}"})
    promise = _observed(REPLAY, (R,), defer=True)
    with production_signal_scope(session):
        if start == "promised":
            _observe(promise)
        before = _state(session)

        def fail_phase7_commit(_signal):
            raise RuntimeError("forced Phase 7 commit failure")

        monkeypatch.setattr(session, "_commit_phase7_signal_transaction", fail_phase7_commit)
        assert _observe(replace(promise, defer_until_terminal=False)) == 0
        assert _state(session) == before
        assert session.domain_signal_error_kinds == ["RuntimeError"]


def test_finalize_keeps_a_promise_whose_terminal_publication_is_refused(monkeypatch):
    """finalize の終端の公開が（打切りでなく）拒まれたら、約束・予約・約束の印を残す。"""
    from scripts.function_tracer_pcode.authority.lifecycle.production_signals import (
        finalize_deferred_sat_safety_observations,
    )

    session = _connector().begin({"phase": "pr-a", "case": "finalize-refused"})
    with production_signal_scope(session):
        _observe(_observed(REPLAY, (R,), defer=True))
        before = _state(session)

        def fail_append(_intents, _commit_callback=None, **_k):
            raise RuntimeError("forced stream append failure")

        monkeypatch.setattr(session, "_emit_many_admitted", fail_append)
        finalize_deferred_sat_safety_observations(session)
        assert not session.stream_truncated
        assert _state(session) == before
        assert session.domain_signal_error_kinds == ["RuntimeError"]


@pytest.mark.parametrize("defer", [False, True])
def test_a_truncated_stream_refuses_every_sat_signal_before_identity(defer, monkeypatch):
    """Issue #110: 切られた stream は（限界以外の）signal を identity を作る前に O(1) で拒む。
    観測・約束のどちらでも、台帳の判定（衝突の記録を含む）をしない。"""
    from scripts.function_tracer_pcode.tests.unit.test_issue110_metered_seal import (
        _sat_blocker,
        _truncated_session,
    )

    _connector_, session, _pending = _truncated_session(monkeypatch, f"pr-a-truncated-{defer}")
    encoder = session.domain_signal_encoder
    built = []
    real_authority = encoder.authority_for_signal
    monkeypatch.setattr(encoder, "authority_for_signal",
                        lambda owner, signal: built.append(signal) or real_authority(owner, signal),
                        raising=False)
    colliding = replace(_sat_blocker(0), evidence_refs=("issue110-other",), defer_until_terminal=defer)
    consequences = {k: dict(v) for k, v in session.truncation_consequences.items()}
    before = _state(session)
    with production_signal_scope(session):
        assert emit_sat_safety_signal(colliding, producer_site_manifest_id="sat-safety-blocker-observed") == 0
    assert built == []
    assert _state(session) == before
    assert session.truncation_consequences == consequences


# ---- ABI の取引の境界: commit の後の失敗は ABI と SAT-safety の全ての台帳を戻す ---------


def _abi_transaction_with_one_sat_handoff():
    """ABI の solver の取引（SAT-safety の観測への変換を 1 つ持つ）を、ABI の commit が読む
    形だけで作る。取引の識別は固定する（この test が見るのは commit と rollback の契約）。"""
    from scripts.function_tracer_pcode.authority.domains.abi_width_readonly import (
        AbiWidthReadonlyBlockerSignal,
        AbiWidthReadonlyPilotEncoder,
        AbiWidthReadonlySolverExecutionBatchSignal,
    )
    from scripts.function_tracer_pcode.authority.domains.sat_safety import SatSafetyPilotEncoder
    from scripts.function_tracer_pcode.authority.lifecycle.production_signals import (
        CompositeProductionSignalEncoder,
    )

    # commit と rollback は solver の実行の設定に依らない（実行の権限の配備は要らない）。
    abi = AbiWidthReadonlyPilotEncoder(enable_solver_execution=False)
    abi._solver_batch_transaction_key = lambda _session, _batch: ("abi-transaction",)
    abi._solver_batch_transaction_digest = lambda _session, _batch: "abi-transaction-digest"
    safety = SatSafetyPilotEncoder()
    composite = CompositeProductionSignalEncoder({
        AbiWidthReadonlyBlockerSignal: abi,
        AbiWidthReadonlySolverExecutionBatchSignal: abi,
        SatSafetyBlockerProductionSignal: safety,
        SafeCounterexampleProductionSignal: safety,
    })
    from scripts.function_tracer_pcode.authority.lifecycle.pilot import ProductionDualWritePilotConnector
    from scripts.function_tracer_pcode.authority.lifecycle.reducer import ShadowLifecycleReducer
    from scripts.function_tracer_pcode.authority.domains.sat_safety import (
        SAT_SAFETY_REASON_REGISTRY,
        SAT_SAFETY_RECOVERY_REGISTRY,
    )

    session = ProductionDualWritePilotConnector(
        ShadowLifecycleReducer(
            reason_registry=SAT_SAFETY_REASON_REGISTRY, recovery_registry=SAT_SAFETY_RECOVERY_REGISTRY,
        ),
        domain_signal_encoder=composite,
    ).begin({"phase": "pr-a", "case": "abi-transaction"})
    batch = object.__new__(AbiWidthReadonlySolverExecutionBatchSignal)
    handoff = replace(
        _observed(ANALYSIS, ("abi-model-bound-refutation",), key=("abi-handoff",)),
        producer_id="abi-width-model-bound-refutation-handoff-v1",
    )
    session.domain_signal_state["abi_width_pending_emission_transactions"] = {
        ("abi-transaction",): ("abi-transaction-digest", (), {
            "fresh_receipt_digests": {"receipt"},
            "decisive_conflict": None,
            "model_artifacts": ["model-artifact"],
            "sat_transformations": [("transformation", "proof", "artifact", handoff)],
        }),
    }
    return session, abi, batch, handoff


_ABI_TRANSACTION_KEYS = (
    "abi_width_solver_execution_receipts",
    "abi_width_model_bound_refutation_artifacts",
    "abi_width_high_bit_sat_transformations",
    "abi_width_committed_emission_transactions",
)


def test_an_abi_transaction_failing_after_its_commit_restores_the_sat_safety_ledger():
    session, abi, batch, handoff = _abi_transaction_with_one_sat_handoff()
    with production_signal_scope(session):
        before = _state(session)
        abi_before = {key: session.domain_signal_state.get(key) for key in _ABI_TRANSACTION_KEYS}
        with session.domain_signal_transaction():
            abi.commit_emitted_signal(session, batch, ())
            # commit は SAT-safety の観測を公開済みとして台帳に記録した。
            assert _ledger_state(session, handoff) is BlockerState.PUBLISHED
            # 同じ取引の後の commit（Phase 7 など）が失敗したときの、本番の呼び手の巻き戻し。
            abi.rollback_emitted_signal(session, batch)
        assert _ledger_state(session, handoff) is BlockerState.ABSENT
        assert "abi_width_committed_rollback_snapshots" not in session.domain_signal_state
        assert _state(session) == before
        assert {key: session.domain_signal_state.get(key) for key in _ABI_TRANSACTION_KEYS} == abi_before


def test_a_completed_abi_transaction_keeps_its_sat_safety_publication():
    """対照: 取引が成功したら（呼び手が巻き戻さない）、変換した観測の公開は残る。"""
    session, abi, batch, handoff = _abi_transaction_with_one_sat_handoff()
    with production_signal_scope(session):
        with session.domain_signal_transaction():
            abi.commit_emitted_signal(session, batch, ())
            abi.finish_emitted_signal(session, batch)
        assert _ledger_state(session, handoff) is BlockerState.PUBLISHED
        assert session.domain_signal_error_kinds == []
        # 取引の終わりがこの取引の写しを捨てた。
        assert "abi_width_committed_rollback_snapshots" not in session.domain_signal_state


def test_the_sat_safety_ledger_refuses_a_change_outside_the_session_transaction():
    """台帳の遷移は session の取引の境界の中でしか起きない（境界の外の commit は台帳を変えない）。"""
    session, abi, batch, handoff = _abi_transaction_with_one_sat_handoff()
    with production_signal_scope(session):
        before = _state(session)
        with pytest.raises(RuntimeError, match="outside the session transaction"):
            abi.commit_emitted_signal(session, batch, ())
        assert _state(session) == before
        assert _ledger_state(session, handoff) is BlockerState.ABSENT


def test_a_completion_that_fails_after_the_encoder_commit_restores_the_ledger(monkeypatch):
    """完了の event の commit の後で取引が失敗したら、cause は公開済み（未完了）のまま。再試行で完了できる。"""
    session = _manifest_connector().begin({"phase": "pr-a", "case": "post-commit-completion"})
    observed = _observed(REPLAY, (R,))
    with production_signal_scope(session):
        _observe(observed)
        before = _state(session)
        real_commit = session._commit_phase7_signal_transaction

        def fail_phase7_commit(_signal):
            raise RuntimeError("forced Phase 7 commit failure")

        monkeypatch.setattr(session, "_commit_phase7_signal_transaction", fail_phase7_commit)
        assert _complete_conditionally(_completion(observed)) == 0
        assert _state(session) == before
        assert session.domain_signal_error_kinds == ["RuntimeError"]
        assert _ledger_state(session, observed) is BlockerState.PUBLISHED
        monkeypatch.setattr(session, "_commit_phase7_signal_transaction", real_commit)
        _complete_conditionally(_completion(observed))
        assert _ledger_state(session, observed) is BlockerState.COMPLETED


def _patch_abi_transaction_identity(monkeypatch):
    """取引の識別を class でも固定する（emit_many の committed replay の判定は class method が読む）。"""
    from scripts.function_tracer_pcode.authority.domains.abi_width_readonly import (
        AbiWidthReadonlyPilotEncoder,
    )

    monkeypatch.setattr(AbiWidthReadonlyPilotEncoder, "_solver_batch_transaction_key",
                        staticmethod(lambda _session, _batch: ("abi-transaction",)))
    monkeypatch.setattr(AbiWidthReadonlyPilotEncoder, "_solver_batch_transaction_digest",
                        classmethod(lambda _cls, _session, _batch: "abi-transaction-digest"))


def _abi_batch_intents(session):
    """取引が出す event（別の blocker の観測。ここでは中身を問わない、有効な event であればよい）。"""
    from scripts.function_tracer_pcode.authority.lifecycle.stream import (
        CauseObservedEventAuthority,
        EventIntent,
        EventType,
    )

    other = _observed(PARTITION, ("abi-batch-event",), key=("abi-batch-event",))
    authority = session.domain_signal_encoder.authority_for_signal(session, other)
    return (EventIntent(EventType.CAUSE_OBSERVED, CauseObservedEventAuthority(authority)),)


def test_the_abi_batch_transaction_call_site_rolls_back_a_failed_encoding(monkeypatch):
    """encoding が取引を予約した後で失敗しても、予約は残らない（取引の境界の中の巻き戻し）。"""
    _patch_abi_transaction_identity(monkeypatch)
    session, abi, batch, handoff = _abi_transaction_with_one_sat_handoff()
    with production_signal_scope(session):
        pending = session.domain_signal_state["abi_width_pending_emission_transactions"]
        entry = pending.pop(("abi-transaction",))
        before = _state(session)

        def encode(_session, _batch):
            pending[("abi-transaction",)] = entry
            raise RuntimeError("forced encoding failure after the reservation")

        monkeypatch.setattr(abi, "_solver_batch_intents", encode)
        with pytest.raises(RuntimeError, match="forced encoding failure"):
            abi._emit_solver_batch_transaction(session, batch)
        assert ("abi-transaction",) not in pending
        assert _state(session) == before
        assert not session.holds_domain_signal_transaction()


@pytest.mark.parametrize("fails", [False, True], ids=["success", "phase7-commit-failure"])
def test_the_abi_batch_transaction_call_site_restores_or_keeps_every_ledger(fails, monkeypatch):
    """本番の呼び手（``_emit_solver_batch_transaction``）を本物の ``emit_many`` で通す。同じ取引の
    Phase 7 の commit が ABI の commit の後で失敗したら全ての台帳を取引の前へ戻し、成功したら
    変換した観測の公開を残して巻き戻し用の写しを捨てる。"""
    _patch_abi_transaction_identity(monkeypatch)
    session, abi, batch, handoff = _abi_transaction_with_one_sat_handoff()
    with production_signal_scope(session):
        intents = _abi_batch_intents(session)
        pending = session.domain_signal_state["abi_width_pending_emission_transactions"]
        digest, _intents, payload = pending[("abi-transaction",)]
        pending.pop(("abi-transaction",))
        before = _state(session)

        def encode(_session, _batch):
            # encoding が取引を予約する（本物の ``_solver_batch_intents`` と同じ形）。
            pending[("abi-transaction",)] = (digest, intents, payload)
            return intents

        monkeypatch.setattr(abi, "_solver_batch_intents", encode)
        abi_before = {key: session.domain_signal_state.get(key) for key in _ABI_TRANSACTION_KEYS}
        if fails:
            # Phase 7 の取引を持つ session と同じ順序（domain の commit → Phase 7 の commit）で、
            # Phase 7 の commit だけが失敗する。
            class _Phase7Runtime:
                def buffer_execution_intent(self, _intent):
                    pass

            def fail_phase7_commit(_transaction):
                raise RuntimeError("forced Phase 7 commit failure after the domain commit")

            monkeypatch.setattr(session, "phase7_runtime", _Phase7Runtime(), raising=False)
            monkeypatch.setattr(session, "_begin_phase7_transaction", lambda: object())
            monkeypatch.setattr(session, "_commit_phase7_transaction", fail_phase7_commit)
            monkeypatch.setattr(session, "_rollback_phase7_transaction", lambda _transaction: None)
            with pytest.raises(RuntimeError, match="forced Phase 7 commit failure"):
                abi._emit_solver_batch_transaction(session, batch)
            assert _ledger_state(session, handoff) is BlockerState.ABSENT
            assert _state(session) == before
            assert {key: session.domain_signal_state.get(key) for key in _ABI_TRANSACTION_KEYS} == abi_before
        else:
            abi._emit_solver_batch_transaction(session, batch)
            assert _ledger_state(session, handoff) is BlockerState.PUBLISHED
            assert session.recorder.event_count == before["events"] + 1
        assert "abi_width_committed_rollback_snapshots" not in session.domain_signal_state
        assert "sat_safety_committed_transactions" not in session.domain_signal_state or not (
            session.domain_signal_state["sat_safety_committed_transactions"]
        )


def test_a_later_abi_transaction_never_restores_an_earlier_transactions_snapshot():
    """写しはその取引の終わりで捨てられる。終わった取引の識別で後から巻き戻しても、その取引も
    その後の別の取引（SAT-safety の公開）も消えない。終わっていない取引の写しは、同じ識別の
    次の commit が上書きできない（上書きすれば先の取引を戻せなくなる）。"""
    session, abi, batch, handoff = _abi_transaction_with_one_sat_handoff()
    with production_signal_scope(session):
        payload_entry = dict(session.domain_signal_state["abi_width_pending_emission_transactions"])
        with session.domain_signal_transaction():
            abi.commit_emitted_signal(session, batch, ())
            abi.finish_emitted_signal(session, batch)  # 成功した取引の終わり
        other = _observed(REPLAY, (R,), key=("unrelated",))
        assert _observe(other) == 1
        with session.domain_signal_transaction():
            abi.rollback_emitted_signal(session, batch)
        assert _ledger_state(session, handoff) is BlockerState.PUBLISHED
        assert _ledger_state(session, other) is BlockerState.PUBLISHED

    session, abi, batch, handoff = _abi_transaction_with_one_sat_handoff()
    with production_signal_scope(session):
        with session.domain_signal_transaction():
            abi.commit_emitted_signal(session, batch, ())  # 終わっていない取引
            session.domain_signal_state["abi_width_pending_emission_transactions"] = dict(payload_entry)
            with pytest.raises(ValueError, match="already owns a committed rollback"):
                abi.commit_emitted_signal(session, batch, ())
            abi.rollback_emitted_signal(session, batch)
        assert _ledger_state(session, handoff) is BlockerState.ABSENT


# ---- 取引の境界: 並行する取引・commit の中からの入口 --------------------------------
#
# 契約: 判定から予約・encoding・公開・commit・巻き戻しまでが session の 1 つの取引で、
# 取引は互いに割り込まない。commit の後で失敗した取引はその取引の occurrence だけを
# 取引の前へ戻し（新規の観測は ABSENT、約束の公開は PROMISED、完了は PUBLISHED）、
# 別の取引が確定させた状態は残る。巻き戻しの写しはその取引の終わりでだけ捨てられる。
#
# 順序は Event で決める。取引 A を encoder の commit の後（同じ取引の Phase 7 の commit）で
# 止め、その間に別の thread で取引 B を始める。正しい直列化では B は A の終わりまで待つ
# ので、A を進める合図は B の進行に依らない（main thread が出す）。待ちの上限は失敗として扱う。

import threading

_WAIT_SECONDS = 30.0


def _in_thread(session, call):
    """``call`` を session の scope の中で別の thread で走らせる（scope は thread ごと）。"""
    outcome = {}
    entered = threading.Event()

    def body():
        with production_signal_scope(session):
            entered.set()
            try:
                outcome["value"] = call()
            except BaseException as exc:  # thread の例外を main thread で調べる
                outcome["error"] = exc

    thread = threading.Thread(target=body, daemon=True)
    thread.start()
    return thread, entered, outcome


def _hold_the_first_commit_of(session, monkeypatch, thread_ident, *, fail):
    """``thread_ident`` の最初の取引を encoder の commit の後で止める（合図で失敗か成功）。"""
    reached = threading.Event()
    release = threading.Event()
    held = []
    real = session._commit_phase7_signal_transaction

    def hook(signal):
        if threading.get_ident() == thread_ident[0] and not held:
            held.append(signal)
            reached.set()
            assert release.wait(_WAIT_SECONDS), "the held transaction was never released"
            if fail:
                raise RuntimeError("forced failure after the encoder commit")
        return real(signal)

    monkeypatch.setattr(session, "_commit_phase7_signal_transaction", hook)
    return reached, release


_A_KEY = ("transaction-a",)
_B_KEY = ("transaction-b",)


def _a_observe(session):
    observed = _observed(REPLAY, (R,), key=_A_KEY)
    return observed, (lambda: None), (lambda: _observe(observed)), BlockerState.ABSENT, BlockerState.PUBLISHED


def _a_publish_promise(session):
    promise = _observed(ANALYSIS, (A,), key=_A_KEY, defer=True)
    return (
        promise, (lambda: _observe(promise)), (lambda: _finalize(session, promise)),
        BlockerState.PROMISED, BlockerState.PUBLISHED,
    )


def _a_complete(session):
    observed = _observed(REPLAY, (R,), key=_A_KEY)
    return observed, (lambda: _observe(observed)), (
        lambda: _complete_conditionally(_completion(observed))
    ), BlockerState.PUBLISHED, BlockerState.COMPLETED


def _a_handoff(session):
    observed = replace(_observed(ANALYSIS, (A,), key=_A_KEY), producer_id=_LOOP_HANDOFF_PRODUCER)
    return (
        observed, (lambda: None), (lambda: _handoff(session, observed)),
        BlockerState.ABSENT, BlockerState.PUBLISHED,
    )


def _a_generic(session):
    observed = _observed(REPLAY, (R,), key=_A_KEY)
    return (
        observed, (lambda: None), (lambda: _generic(session, observed)),
        BlockerState.ABSENT, BlockerState.PUBLISHED,
    )


_A_TRANSACTIONS = {
    "observe": _a_observe,
    "publish-promise": _a_publish_promise,
    "complete": _a_complete,
    "loop-handoff": _a_handoff,
    "generic": _a_generic,
}

_B_TRANSACTIONS = {
    # (signal, call, 期待する状態, event の数, 約束の予約の数)
    "observe": lambda s: (_observed(PARTITION, ("pairwise",), key=_B_KEY), _observe, BlockerState.PUBLISHED, 1, 0),
    "promise": lambda s: (_observed(ANALYSIS, (A,), key=_B_KEY, defer=True), _observe, BlockerState.PROMISED, 0, 1),
    "generic": lambda s: (
        _observed(REPLAY, (R,), key=_B_KEY), lambda sig: _generic(s, sig), BlockerState.PUBLISHED, 1, 0,
    ),
}


@pytest.mark.parametrize("fails", [True, False], ids=["a-fails", "a-succeeds"])
@pytest.mark.parametrize("b_name", sorted(_B_TRANSACTIONS))
@pytest.mark.parametrize("a_name", sorted(_A_TRANSACTIONS))
@pytest.mark.parametrize("manifest", [False, True], ids=["plain", "phase7"])
def test_a_concurrent_transaction_neither_interleaves_nor_erases_the_other(
    a_name, b_name, fails, manifest, monkeypatch,
):
    if a_name == "loop-handoff" and not manifest:
        pytest.skip("the loop handoff site is audited only under the producer manifest")
    session = (_manifest_connector() if manifest else _connector()).begin(
        {"phase": "pr-a", "case": f"concurrent-{a_name}-{b_name}-{fails}-{manifest}"},
    )
    with production_signal_scope(session):
        a_signal, a_setup, a_call, a_before, a_after = _A_TRANSACTIONS[a_name](session)
        b_signal, b_entry, b_expected, b_events, b_promises = _B_TRANSACTIONS[b_name](session)
        # 既に確定した別の occurrence（A の巻き戻しが消してはならない）。
        settled = _observed(REPLAY, (R,), key=("settled-before",))
        assert _observe(settled) == 1
        a_setup()
        assert _ledger_state(session, a_signal) is a_before
        before = _state(session)
        errors_before = list(session.domain_signal_error_kinds)

    a_ident = [None]
    reached, release = _hold_the_first_commit_of(session, monkeypatch, a_ident, fail=fails)

    def run_a():
        a_ident[0] = threading.get_ident()
        return a_call()

    a_thread, _a_entered, a_outcome = _in_thread(session, run_a)
    assert reached.wait(_WAIT_SECONDS), "transaction A never reached its commit"
    # A は commit の後で止まっている。B を始める。
    b_thread, b_entered, b_outcome = _in_thread(session, lambda: b_entry(b_signal))
    assert b_entered.wait(_WAIT_SECONDS)
    b_thread.join(0.3)
    # 直列化: B は A が終わるまで取引に入れない（A の写しにも台帳にも触れない）。
    assert b_thread.is_alive(), ("transaction B ran inside transaction A", b_outcome)
    release.set()
    a_thread.join(_WAIT_SECONDS)
    b_thread.join(_WAIT_SECONDS)
    assert not a_thread.is_alive() and not b_thread.is_alive()
    assert "error" not in b_outcome, b_outcome
    if a_name == "loop-handoff" and fails:
        # handoff の消費は、公開も重複の証明も無ければ handoff を消費せずに止まる（既存の契約）。
        assert isinstance(a_outcome.get("error"), ValueError), a_outcome
        assert "neither emitted nor deduplicated" in str(a_outcome["error"])
    else:
        assert "error" not in a_outcome, a_outcome

    with production_signal_scope(session):
        # A: 失敗なら A の occurrence だけが取引の前へ戻り、失敗は 1 件記録される。
        assert _ledger_state(session, a_signal) is (a_before if fails else a_after)
        expected_errors = errors_before + (["RuntimeError"] if fails else [])
        assert session.domain_signal_error_kinds == expected_errors
        # B: A の成否に依らず確定し、A の巻き戻しで消えない。
        assert _ledger_state(session, b_signal) is b_expected
        assert _ledger_state(session, settled) is BlockerState.PUBLISHED
        after = _state(session)
        a_events = 0 if fails else 1
        assert after["events"] == before["events"] + a_events + b_events
        # 約束の予約（未公開の約束の数）: B の約束が増え、公開できた A の約束が減る。
        promised_delta = b_promises - (1 if a_name == "publish-promise" and not fails else 0)
        assert after["reserved"] == before["reserved"] + promised_delta
        # 進行中の取引の情報は残らない（写し・予約中の encoding・Phase 7 の取引）。
        assert "sat_safety_committed_transactions" not in session.domain_signal_state
        assert after["pending_tx"] == {}
        assert after["phase7_tx"] == {}
        assert not session.producer_commit_open()
        assert not session.holds_domain_signal_transaction()


@pytest.mark.parametrize("b_name", sorted(_B_TRANSACTIONS))
@pytest.mark.parametrize("fails", [True, False], ids=["a-fails", "a-succeeds"])
def test_a_producer_inside_another_transactions_commit_is_refused_without_state_change(
    b_name, fails, monkeypatch,
):
    """commit の callback（同じ thread・再入）から別の取引を始めると、その取引の巻き戻しの
    範囲に入る。入口は状態を変えずに拒否を記録し、外側の取引の成否と巻き戻しは変わらない。"""
    session = _connector().begin({"phase": "pr-a", "case": f"nested-{b_name}-{fails}"})
    with production_signal_scope(session):
        a_signal = _observed(REPLAY, (R,), key=_A_KEY)
        b_signal, b_entry, _b_expected, _b_events, _b_promises = _B_TRANSACTIONS[b_name](session)
        before = _state(session)
        real = session._commit_phase7_signal_transaction
        nested = []

        def hook(signal):
            if not nested:
                nested.append(b_entry(b_signal))
                if fails:
                    raise RuntimeError("forced failure after the encoder commit")
            return real(signal)

        monkeypatch.setattr(session, "_commit_phase7_signal_transaction", hook)
        _observe(a_signal)
        assert nested and not nested[0]
        assert _ledger_state(session, b_signal) is BlockerState.ABSENT
        assert _ledger_state(session, a_signal) is (BlockerState.ABSENT if fails else BlockerState.PUBLISHED)
        assert session.domain_signal_error_kinds == ["ProducerTransactionRefused"] + (["RuntimeError"] if fails else [])
        after = _state(session)
        assert after["promised_ids"] == before["promised_ids"]
        assert after["reserved"] == before["reserved"]
        assert after["events"] == before["events"] + (0 if fails else 1)
        assert "sat_safety_committed_transactions" not in session.domain_signal_state


def test_an_exception_inside_a_transaction_releases_the_boundary():
    """取引の中の例外でも境界は解放され、別の thread の取引が進む。"""
    session = _connector().begin({"phase": "pr-a", "case": "release-on-exception"})
    with pytest.raises(RuntimeError, match="inside the boundary"):
        with session.domain_signal_transaction():
            assert session.holds_domain_signal_transaction()
            raise RuntimeError("inside the boundary")
    assert not session.holds_domain_signal_transaction()
    observed = _observed(REPLAY, (R,), key=_B_KEY)
    thread, _entered, outcome = _in_thread(session, lambda: _observe(observed))
    thread.join(_WAIT_SECONDS)
    assert not thread.is_alive() and outcome == {"value": 1}


# ---- 写しの所有権（encoder・台帳の契約。境界に依らず成り立つ） --------------------


def _encode_and_commit(session, signal):
    encoder = session.domain_signal_encoder
    intents = tuple(encoder(session, signal))
    encoder.commit_emitted_signal(session, signal, intents)
    return intents


def test_another_encoding_never_discards_an_in_flight_transactions_rollback_state():
    """commit した取引 A の写しは A の終わりまで残る。その間に別の signal を encode しても
    A の写しは消えず、A の失敗は A の occurrence だけを戻す。"""
    session = _connector().begin({"phase": "pr-a", "case": "in-flight-snapshot"})
    a = _observed(REPLAY, (R,), key=_A_KEY)
    b = _observed(PARTITION, ("pairwise",), key=_B_KEY)
    encoder = session.domain_signal_encoder
    with production_signal_scope(session), session.domain_signal_transaction():
        _encode_and_commit(session, a)
        assert _ledger_state(session, a) is BlockerState.PUBLISHED
        tuple(encoder(session, b))  # 別の取引の encoding（A は終わっていない）
        encoder.rollback_emitted_signal(session, a)
        encoder.rollback_emitted_signal(session, b)
        assert _ledger_state(session, a) is BlockerState.ABSENT
        assert "sat_safety_committed_transactions" not in session.domain_signal_state


def test_an_unfinished_transactions_rollback_state_cannot_be_overwritten():
    session = _connector().begin({"phase": "pr-a", "case": "overwrite-snapshot"})
    a = _observed(REPLAY, (R,), key=_A_KEY)
    encoder = session.domain_signal_encoder
    with production_signal_scope(session), session.domain_signal_transaction():
        intents = _encode_and_commit(session, a)
        pending = session.domain_signal_state.setdefault("sat_safety_pending_emission_transactions", {})
        pending[id(a)] = (intents, "OBSERVED", "unused")
        with pytest.raises(ValueError, match="already owns a committed transaction"):
            encoder.commit_emitted_signal(session, a, intents)
        encoder.rollback_emitted_signal(session, a)
        assert _ledger_state(session, a) is BlockerState.ABSENT


def test_the_ledger_refuses_an_entry_transition_inside_another_transactions_commit(monkeypatch):
    """約束と約束の退役（event の無い入口の遷移）は、別の取引の commit window の中で台帳を変えない。"""
    from scripts.function_tracer_pcode.authority.domains.sat_safety_ledger import SatSafetyBlockerLedger

    session = _connector().begin({"phase": "pr-a", "case": "ledger-window"})
    a = _observed(REPLAY, (R,), key=_A_KEY)
    promise = _observed(ANALYSIS, (A,), key=_B_KEY, defer=True)
    real = session._commit_phase7_signal_transaction
    seen = []

    def hook(signal):
        ledger = SatSafetyBlockerLedger(session)
        with pytest.raises(RuntimeError, match="inside another producer transaction"):
            ledger.record_promise("occurrence-in-window", promise, None)
        seen.append(dict(session.domain_signal_state.get("sat_safety_deferred_observations", {})))
        return real(signal)

    monkeypatch.setattr(session, "_commit_phase7_signal_transaction", hook)
    with production_signal_scope(session):
        assert _observe(a) == 1
    assert seen == [{}]


def test_the_observed_check_and_its_emission_are_one_transaction(monkeypatch):
    """条件付きの公開は、観測の確認から公開までの間に別の取引を入れない。"""
    session = _connector().begin({"phase": "pr-a", "case": "if-observed-atomic"})
    observed = _observed(REPLAY, (R,), key=_A_KEY)
    with production_signal_scope(session):
        _observe(observed)
    encoder = session.domain_signal_encoder
    reached, release = threading.Event(), threading.Event()
    real = encoder.has_observed

    def held(session_, signal):
        if not reached.is_set():
            reached.set()
            assert release.wait(_WAIT_SECONDS)
        return real(session_, signal)

    monkeypatch.setattr(encoder, "has_observed", held)
    a_thread, _e, a_outcome = _in_thread(
        session, lambda: session.emit_domain_signal_if_observed(_completion(observed)),
    )
    assert reached.wait(_WAIT_SECONDS)
    other = _observed(PARTITION, ("pairwise",), key=_B_KEY)
    b_thread, b_entered, b_outcome = _in_thread(session, lambda: _generic(session, other))
    assert b_entered.wait(_WAIT_SECONDS)
    b_thread.join(0.3)
    assert b_thread.is_alive(), ("a transaction ran between the observed check and its emission", b_outcome)
    release.set()
    a_thread.join(_WAIT_SECONDS)
    b_thread.join(_WAIT_SECONDS)
    assert a_outcome == {"value": 1} and b_outcome == {"value": 1}
    with production_signal_scope(session):
        assert _ledger_state(session, observed) is BlockerState.COMPLETED
        assert _ledger_state(session, other) is BlockerState.PUBLISHED


def test_a_concurrent_consumer_never_drops_a_loop_handoff(monkeypatch):
    """loop の handoff の一覧は 1 つの取引で消費する。別の thread の消費が、公開中の handoff を
    消したり次の handoff を落としたりしない。"""
    from scripts.function_tracer_pcode.authority.lifecycle.production_signals import (
        _consume_loop_sat_safety_handoffs,
    )

    session = _manifest_connector().begin({"phase": "pr-a", "case": "handoff-consumers"})
    first = replace(_observed(ANALYSIS, (A,), key=("handoff-1",)), producer_id=_LOOP_HANDOFF_PRODUCER)
    second = replace(_observed(ANALYSIS, (A,), key=("handoff-2",)), producer_id=_LOOP_HANDOFF_PRODUCER)
    session.domain_signal_state["loop_sat_safety_handoffs"] = [first, second]
    a_ident = [None]
    reached, release = _hold_the_first_commit_of(session, monkeypatch, a_ident, fail=False)

    def run_a():
        a_ident[0] = threading.get_ident()
        return _consume_loop_sat_safety_handoffs(session)

    a_thread, _e, a_outcome = _in_thread(session, run_a)
    assert reached.wait(_WAIT_SECONDS)
    b_thread, b_entered, b_outcome = _in_thread(session, lambda: _consume_loop_sat_safety_handoffs(session))
    assert b_entered.wait(_WAIT_SECONDS)
    b_thread.join(0.3)
    release.set()
    a_thread.join(_WAIT_SECONDS)
    b_thread.join(_WAIT_SECONDS)
    assert "error" not in a_outcome and "error" not in b_outcome, (a_outcome, b_outcome)
    assert a_outcome["value"] + b_outcome["value"] == 2
    with production_signal_scope(session):
        assert _ledger_state(session, first) is BlockerState.PUBLISHED
        assert _ledger_state(session, second) is BlockerState.PUBLISHED
    assert "loop_sat_safety_handoffs" not in session.domain_signal_state


# ---- 取引の所有権: 同じ thread からの再入（review 8） ------------------------------
#
# 契約: 1 つの session で生きている producer の取引（attempt）は 1 つ。生きている取引の
# 準備（encoding）・commit・後始末の中から新しい取引や直接の公開を始めると、それは何も
# 取得せずに拒否され、拒否は記録される（pair は ERROR）。拒否は外側の取引の写し・Phase 7
# の取引・予約・lock を解放しない。外側の取引は自分の成否どおりに終わる。signal の object
# の同一性（同じ object・同じ内容の別 object・別の occurrence）に依らない。


def _nested_calls(session, outer, settled):
    """外側の取引の中から試す呼び出し（入口 × object・occurrence の関係）。"""
    other = _observed(PARTITION, ("pairwise",), key=_B_KEY)

    def direct_emit():
        authority = session.domain_signal_encoder.authority_for_signal(session, other)
        from scripts.function_tracer_pcode.authority.lifecycle.stream import (
            CauseObservedEventAuthority,
            EventIntent,
            EventType,
        )

        return session.emit(EventIntent(EventType.CAUSE_OBSERVED, CauseObservedEventAuthority(authority)))

    return {
        "same-object-generic": (lambda: session.emit_domain_signal(outer), outer),
        "same-object-entry": (lambda: _observe(outer), outer),
        "equal-object-generic": (lambda: session.emit_domain_signal(replace(outer)), outer),
        "other-occurrence-generic": (lambda: session.emit_domain_signal(other), other),
        "other-promise-entry": (lambda: _observe(replace(other, defer_until_terminal=True)), other),
        "direct-emit": (direct_emit, other),
        # Phase 7 の activation から始まる入口（activation は何も取得せず、受付が拒否する）。
        "activation-first-entry": (
            lambda: session.emit_domain_signal_if_observed(
                _completion(settled), SAT_SAFETY_BLOCKER_COMPLETED_SITE.site_id,
            ),
            settled,
        ),
    }


_NESTED = ["same-object-generic", "same-object-entry", "equal-object-generic",
           "other-occurrence-generic", "other-promise-entry", "direct-emit", "activation-first-entry"]


def _install_reentry(session, monkeypatch, stage, call, *, fail):
    """外側の取引の ``stage`` で ``call`` を 1 回だけ呼ぶ（commit の段では、その後で失敗させられる）。"""
    seen = []

    def run_nested():
        try:
            seen.append(("value", call()))
        except Exception as exc:  # 入れ子の結果を外側から調べる
            seen.append(("error", exc))

    if stage == "preparing":
        # session の encoder（composite でも SAT の encoder でも）の encoding の中。
        encoder_class = type(session.domain_signal_encoder)
        real_call = encoder_class.__call__

        def encoding(self, session_, signal):
            if not seen and session_ is session:
                run_nested()
            return real_call(self, session_, signal)

        monkeypatch.setattr(encoder_class, "__call__", encoding)
    elif stage == "committing":
        real_commit = session._commit_phase7_signal_transaction

        def committing(signal):
            if not seen:
                run_nested()
                if fail:
                    raise RuntimeError("forced failure after the encoder commit")
            return real_commit(signal)

        monkeypatch.setattr(session, "_commit_phase7_signal_transaction", committing)
    else:
        encoder = session.domain_signal_encoder
        real_finish = encoder.finish_emitted_signal

        def finishing(session_, signal):
            if not seen:
                run_nested()
            return real_finish(session_, signal)

        monkeypatch.setattr(encoder, "finish_emitted_signal", finishing)
    return seen


@pytest.mark.parametrize("manifest", [False, True], ids=["plain", "phase7"])
@pytest.mark.parametrize("nested", _NESTED)
@pytest.mark.parametrize(("stage", "fail"), [
    ("preparing", False), ("committing", False), ("committing", True), ("finishing", False),
], ids=["preparing", "committing", "committing-then-fails", "finishing"])
def test_a_reentrant_transaction_is_refused_without_touching_the_outer_one(
    stage, fail, nested, manifest, monkeypatch,
):
    connector = _manifest_connector() if manifest else _connector()
    session = connector.begin({"phase": "pr-a", "case": f"reentry-{stage}-{fail}-{nested}-{manifest}"})
    outer = _observed(REPLAY, (R,), key=_A_KEY)
    with production_signal_scope(session):
        settled = _observed(REPLAY, (R,), key=("settled-before",))
        assert _observe(settled) == 1
        call, nested_signal = _nested_calls(session, outer, settled)[nested]
        before = _state(session)
        seen = _install_reentry(session, monkeypatch, stage, call, fail=fail)
        published = _observe(outer)
        monkeypatch.undo()
        # 入れ子の試行は拒否された（何も公開せず、直接の公開は例外）。
        assert len(seen) == 1
        kind, result = seen[0]
        if nested == "direct-emit":
            assert kind == "error" and type(result).__name__ == "ProducerTransactionRefused"
        else:
            assert (kind, result) == ("value", 0)
        # 外側の取引は自分の成否どおり。拒否は外側の写し・Phase 7・予約・lock を解放しない。
        outer_failed = stage == "committing" and fail
        assert published == (0 if outer_failed else 1)
        assert _ledger_state(session, outer) is (BlockerState.ABSENT if outer_failed else BlockerState.PUBLISHED)
        if nested_signal is settled:
            assert _ledger_state(session, settled) is BlockerState.PUBLISHED  # 完了していない
        elif nested_signal is not outer:
            assert _ledger_state(session, nested_signal) is BlockerState.ABSENT
        assert _ledger_state(session, settled) is BlockerState.PUBLISHED
        after = _state(session)
        assert after["events"] == before["events"] + (0 if outer_failed else 1)
        assert after["reserved"] == before["reserved"] and after["promised_ids"] == before["promised_ids"]
        assert after["pending_tx"] == {} and after["phase7_tx"] == {}
        assert "sat_safety_committed_transactions" not in session.domain_signal_state
        assert session._phase7_signal_transactions == {}
        assert not session.producer_commit_open()
        assert not session.holds_domain_signal_transaction()
        assert session.domain_signal_error_kinds == (
            ["ProducerTransactionRefused"] + (["RuntimeError"] if outer_failed else [])
        )
        # stream の prefix の chain は正しい（入れ子の公開が混ざっていない）。
        session.preview_lifecycle_projection()
    # 拒否は記録されたので、最終判定は ERROR（encoding の失敗として止まる）。
    with pytest.raises(ValueError, match="encoding is incomplete"):
        _finish(session, connector, "reentry")


@pytest.mark.parametrize("manifest", [False, True], ids=["plain", "phase7"])
@pytest.mark.parametrize("stage", ["preparing", "committing", "finishing"])
def test_reentry_hooks_without_a_nested_call_change_nothing(stage, manifest, monkeypatch):
    """対照: 同じ hook で入れ子の呼び出しをしなければ、外側は普通に公開され失敗も無い。"""
    connector = _manifest_connector() if manifest else _connector()
    session = connector.begin({"phase": "pr-a", "case": f"reentry-control-{stage}-{manifest}"})
    outer = _observed(REPLAY, (R,), key=_A_KEY)
    with production_signal_scope(session):
        before = _state(session)
        seen = _install_reentry(session, monkeypatch, stage, lambda: None, fail=False)
        assert _observe(outer) == 1
        monkeypatch.undo()
        assert seen == [("value", None)]
        assert _ledger_state(session, outer) is BlockerState.PUBLISHED
        assert _state(session)["events"] == before["events"] + 1
        assert session.domain_signal_error_kinds == []
        session.preview_lifecycle_projection()
    _finish(session, connector, "reentry-control")


@pytest.mark.parametrize("manifest", [False, True], ids=["plain", "phase7"])
def test_a_failing_end_of_transaction_hook_keeps_the_publication_and_is_recorded(manifest, monkeypatch):
    connector = _manifest_connector() if manifest else _connector()
    session = connector.begin({"phase": "pr-a", "case": f"finish-failure-{manifest}"})
    outer = _observed(REPLAY, (R,), key=_A_KEY)
    encoder = session.domain_signal_encoder

    def failing_finish(_session, _signal):
        raise RuntimeError("forced end-of-transaction hook failure")

    with production_signal_scope(session):
        before = _state(session)
        monkeypatch.setattr(encoder, "finish_emitted_signal", failing_finish)
        with pytest.raises(RuntimeError, match="end-of-transaction hook failure"):
            _observe(outer)
        monkeypatch.undo()
        # 公開した event は残り、失敗は記録され、取引は終わっている（lock・window は解放）。
        assert _ledger_state(session, outer) is BlockerState.PUBLISHED
        assert _state(session)["events"] == before["events"] + 1
        assert session.domain_signal_error_kinds == ["ProducerTransactionFinishFailed"]
        assert not session.producer_commit_open()
        assert not session.holds_domain_signal_transaction()
        assert _observe(_observed(PARTITION, ("pairwise",), key=_B_KEY)) == 1
        session.preview_lifecycle_projection()
    with pytest.raises(ValueError, match="encoding is incomplete"):
        _finish(session, connector, "finish-failure")


def test_a_failing_rollback_still_ends_the_attempt_and_releases_the_boundary(monkeypatch):
    session = _connector().begin({"phase": "pr-a", "case": "rollback-failure"})
    outer = _observed(REPLAY, (R,), key=_A_KEY)
    encoder = session.domain_signal_encoder

    def failing_rollback(_session, _signal):
        raise RuntimeError("forced encoder rollback failure")

    def failing_phase7(_signal):
        raise RuntimeError("forced failure after the encoder commit")

    with production_signal_scope(session):
        monkeypatch.setattr(encoder, "rollback_emitted_signal", failing_rollback)
        monkeypatch.setattr(session, "_commit_phase7_signal_transaction", failing_phase7)
        assert _observe(outer) == 0
        monkeypatch.undo()
        assert session.domain_signal_error_kinds == ["RuntimeError"]
        assert "rollback failures" in session.domain_signal_error_details[0]
        assert not session.producer_commit_open()
        assert not session.holds_domain_signal_transaction()
        assert session._producer_boundary.has_live_attempt is False


def test_a_reentrant_abi_batch_transaction_is_refused_and_the_outer_one_rolls_back(monkeypatch):
    """ABI の batch の commit の中から同じ batch の取引を始めると拒否される。拒否は外側の写しを
    消さず、拒否で失敗した外側の取引は ABI と SAT-safety の全ての台帳を取引の前へ戻す。正当な
    入れ子（ABI の commit の中の SAT-safety の commit）は新しい取引ではないので拒否されない。"""
    _patch_abi_transaction_identity(monkeypatch)
    session, abi, batch, handoff = _abi_transaction_with_one_sat_handoff()
    with production_signal_scope(session):
        intents = _abi_batch_intents(session)
        pending = session.domain_signal_state["abi_width_pending_emission_transactions"]
        digest, _intents, payload = pending.pop(("abi-transaction",))
        before = _state(session)
        abi_before = {key: session.domain_signal_state.get(key) for key in _ABI_TRANSACTION_KEYS}

        def encode(_session, _batch):
            pending[("abi-transaction",)] = (digest, intents, payload)
            return intents

        monkeypatch.setattr(abi, "_solver_batch_intents", encode)
        real_commit = abi.commit_emitted_signal
        nested = []

        def commit_then_reenter(session_, batch_, intents_):
            real_commit(session_, batch_, intents_)
            assert _ledger_state(session, handoff) is BlockerState.PUBLISHED  # 正当な入れ子
            try:
                abi._emit_solver_batch_transaction(session, batch)
            except Exception as exc:
                nested.append(exc)
                raise

        monkeypatch.setattr(abi, "commit_emitted_signal", commit_then_reenter)
        with pytest.raises(Exception) as raised:
            abi._emit_solver_batch_transaction(session, batch)
        assert type(raised.value).__name__ == "ProducerTransactionRefused"
        assert [type(exc).__name__ for exc in nested] == ["ProducerTransactionRefused"]
        assert _ledger_state(session, handoff) is BlockerState.ABSENT
        assert _state(session) == before
        assert {key: session.domain_signal_state.get(key) for key in _ABI_TRANSACTION_KEYS} == abi_before
        assert "abi_width_committed_rollback_snapshots" not in session.domain_signal_state
        assert ("abi-transaction",) not in pending
        assert session.domain_signal_error_kinds == ["ProducerTransactionRefused"]
        assert not session.holds_domain_signal_transaction()


def test_a_safe_counterexample_that_fails_after_its_commit_can_be_published_again(monkeypatch):
    """決め手の counterexample の commit の後で同じ取引が失敗したら、印を commit の前へ戻す。
    印が残ると、再試行が重複として黙って捨てられ、決め手の event が出ない。"""
    session = _connector().begin({"phase": "pr-a", "case": "safe-counterexample-rollback"})
    real = session._commit_phase7_signal_transaction
    failures = []

    def fail_once(signal):
        if not failures:
            failures.append(signal)
            raise RuntimeError("forced failure after the counterexample commit")
        return real(signal)

    monkeypatch.setattr(session, "_commit_phase7_signal_transaction", fail_once)
    # safe receipt は scope の中で作ると event を出すので、scope の外で作る。
    first, retry = _safe_pairwise_receipt(), _safe_pairwise_receipt()
    with production_signal_scope(session):
        before = session.recorder.event_count
        emit_safe_counterexample_production_signal(safety_receipt=first)
        assert failures and session.recorder.event_count == before
        assert "sat_safety_safe_counterexample_committed" not in session.domain_signal_state
        assert "sat_safety_committed_transactions" not in session.domain_signal_state
        emit_safe_counterexample_production_signal(safety_receipt=retry)
        assert session.recorder.event_count == before + 1
        assert session.domain_signal_state.get("sat_safety_safe_counterexample_committed")
        assert "sat_safety_committed_transactions" not in session.domain_signal_state
    assert session.domain_signal_error_kinds == ["RuntimeError"]


def test_a_failing_rollback_of_a_batch_attempt_is_recorded_and_ends_the_attempt():
    """共通の取引（ABI・loop の batch）の巻き戻しの失敗は、打切りの後でも producer の誤りとして
    記録され、取引は終わり境界は解放される。"""
    session = _connector().begin({"phase": "pr-a", "case": "batch-rollback-failure"})
    batch = object()

    def encode():
        raise RuntimeError("forced encoding failure")

    def failing_rollback():
        raise RuntimeError("forced rollback failure")

    with pytest.raises(RuntimeError, match="forced rollback failure"):
        session.run_signal_transaction(batch, encode, lambda _intents: None, failing_rollback)
    assert session.domain_signal_error_kinds == ["ProducerRollbackFailed"]
    assert not session.holds_domain_signal_transaction()
    assert session._producer_boundary.has_live_attempt is False
    assert session.run_signal_transaction(object(), lambda: (), lambda _i: None, lambda: None) == ()


def test_a_committed_replay_of_a_batch_attempt_keeps_the_earlier_attempts_state(monkeypatch):
    """既に公開した batch をもう一度通すと公開しない。その state は前の取引のもので、この取引は
    巻き戻さない（後で失敗しても前の取引の確定を消さない）。"""
    _patch_abi_transaction_identity(monkeypatch)
    session, abi, batch, handoff = _abi_transaction_with_one_sat_handoff()
    with production_signal_scope(session):
        intents = _abi_batch_intents(session)
        pending = session.domain_signal_state["abi_width_pending_emission_transactions"]
        digest, _intents, payload = pending.pop(("abi-transaction",))

        def encode(_session, _batch):
            if ("abi-transaction",) not in session.domain_signal_state.get(
                "abi_width_committed_emission_transactions", {}
            ):
                pending[("abi-transaction",)] = (digest, intents, payload)
            return intents

        monkeypatch.setattr(abi, "_solver_batch_intents", encode)
        abi._emit_solver_batch_transaction(session, batch)
        committed = dict(session.domain_signal_state["abi_width_committed_emission_transactions"])
        events = session.recorder.event_count
        rolled_back = []
        real_rollback = abi.rollback_emitted_signal
        monkeypatch.setattr(abi, "rollback_emitted_signal",
                            lambda s_, b_: rolled_back.append(b_) or real_rollback(s_, b_))
        abi._emit_solver_batch_transaction(session, batch)  # committed replay
        assert rolled_back == []
        assert session.recorder.event_count == events
        assert session.domain_signal_state["abi_width_committed_emission_transactions"] == committed
        assert _ledger_state(session, handoff) is BlockerState.PUBLISHED
        assert session.domain_signal_error_kinds == []
