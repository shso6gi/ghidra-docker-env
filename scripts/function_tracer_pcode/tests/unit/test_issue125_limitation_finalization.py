# -*- coding: utf-8 -*-
"""Issue #125 PR-125-A: 限界が **最終化まで** どう効くか（E2E-1/2/3 + digest 契約）。

catch 単体ではなく、`checker.check` の handler → 帰属 → producer → canonical
projection → `finalize_decision` まで通して検証する。最重要は E2E-3
（未解消の限界が EQ へ抜けない）。
"""

import json
from pathlib import Path
from types import SimpleNamespace
from unittest.mock import patch

import pytest

from scripts.function_tracer_pcode.authority.contracts import Outcome
from scripts.function_tracer_pcode.authority.lifecycle.pilot import (
    ProductionDualWritePilotConnector,
)
from scripts.function_tracer_pcode.authority.lifecycle.production_signals import (
    CompositeProductionSignalEncoder,
    SatSafetyBlockerProductionSignal,
    emit_sat_safety_signal,
    issue_pending_eq_closure_authority,
    production_signal_scope,
)
from scripts.function_tracer_pcode.authority.lifecycle.reducer import (
    ShadowLifecycleReducer,
)
from scripts.function_tracer_pcode.authority.domains.analysis_limitation import (
    ANALYSIS_BUDGET_REASON_ID,
    ANALYSIS_LIMITATION_LEDGER_KEY,
    AnalysisLimitationBlockerSignal,
    AnalysisLimitationPilotEncoder,
)
from scripts.function_tracer_pcode.authority.domains.sat_safety import (
    SatSafetyPilotEncoder,
)
from scripts.function_tracer_pcode.authority.process.supervisor import (
    PROCESS_DURABLE_REASON_REGISTRY,
    PROCESS_DURABLE_RECOVERY_REGISTRY,
)
from scripts.function_tracer_pcode.authority.sites.runtime import (
    runtime_from_audited_manifest,
)
from scripts.function_tracer_pcode.checker import checker as checker_module
from scripts.function_tracer_pcode.checker.checker import EquivalenceChecker
from scripts.function_tracer_pcode.core.errors import DeadlineExceeded
from scripts.function_tracer_pcode.tests.unit.test_monolithic_region_split import (
    _analysis,
)


LIMITATION_SITE = "checker.checker.EquivalenceChecker.check"


def _manifest():
    root = Path(__file__).resolve().parents[4]
    return json.loads((root / (
        "artifacts/unknown_taxonomy_v2/phase7/producer-sites.json"
    )).read_text(encoding="utf-8"))


def _connector(*, with_phase7=True):
    encoders = {
        AnalysisLimitationBlockerSignal: AnalysisLimitationPilotEncoder(),
        SatSafetyBlockerProductionSignal: SatSafetyPilotEncoder(),
    }
    manifest = _manifest()
    return ProductionDualWritePilotConnector(
        ShadowLifecycleReducer(
            reason_registry=PROCESS_DURABLE_REASON_REGISTRY,
            recovery_registry=PROCESS_DURABLE_RECOVERY_REGISTRY,
        ),
        domain_signal_encoder=CompositeProductionSignalEncoder(encoders),
        phase7_runtime_factory=(
            (lambda identity: runtime_from_audited_manifest(manifest, identity))
            if with_phase7 else None
        ),
    )


def _sat_blocker():
    return SatSafetyBlockerProductionSignal(
        action="OBSERVED",
        reason_id="counterexample_analysis_safety_unproven",
        canonical_target_key=("issue125-other-producer",),
        missing_semantic_fact=("counterexample_safety_gate_unproven", "model"),
        evidence_refs=("issue125-other-producer",),
        producer_id="sat_unsafety_reason_producer",
    )


def _check_with_limitation(session, *, checker=None):
    """`assemble_equivalence_result` が限界を投げるようにして 1 件 check する。"""
    checker = checker or EquivalenceChecker(
        strategy="monolithic", timeout=5, monolithic_timeout=5,
        canonical_decision_cutover=False,
    )
    checker._active_v2_dual_write_pilot_session = session
    limitation = DeadlineExceeded(
        "analysis budget exhausted",
        site=LIMITATION_SITE,
        target_key=("left", "right"),
        evidence_refs=("issue125-budget",),
    )
    with patch.object(
        checker_module, "assemble_equivalence_result", side_effect=limitation,
    ):
        return checker.check(_analysis("left", 7), _analysis("right", 7), "L", "R")


def _legacy_view(result):
    """`connector.finish` が読む legacy 面だけを渡す（checker の結果そのもの）。"""
    return result


# --- E2E-1 ------------------------------------------------------------------

def test_limitation_before_any_producer_activation_is_unknown_with_its_reason():
    connector = _connector()
    session = connector.begin({"case": "issue125-e2e-1"})
    with production_signal_scope(session):
        result = _check_with_limitation(session)

    assert result.is_equivalent is None and result.error_message is None
    assert result.failure_status is None
    assert result.pairwise_debug_stats == {"analysis_limitation": 1}
    failure = result.diagnostics["failures"]["analysis_limitation"]
    assert failure["disposition"] == "ATTRIBUTED_NEW_CAUSE"
    assert failure["decision_effect"] == "blocks_decision"
    assert failure["site"] == LIMITATION_SITE

    evidence = connector.finish(session, _legacy_view(result), case_id="issue125-e2e-1")
    pilot = evidence.pilot_result
    assert pilot.candidate.decision_receipt.outcome is Outcome.UNKNOWN
    assert {
        row.reason_id for row in pilot.reduction.projection.c_active_base
    } == {ANALYSIS_BUDGET_REASON_ID}
    # 最終 canonical reason 集合に限界が残る（空 UNKNOWN にしない）。
    assert result.unknown_reason_projection_mode == "V2_CANONICAL"
    assert [reason.reason_id for reason in result.unknown_reasons] == [
        ANALYSIS_BUDGET_REASON_ID
    ]
    canonical = result.unknown_reasons[0]
    assert canonical.decision_effect == "blocks_decision"
    cause = canonical.to_dict()["object_evidence"]["cause"]
    assert cause["target_kind"] == "analysis_limitation"
    assert cause["producer_id"] == "analysis-limitation-producer-v1"
    assert tuple(cause["canonical_target_key"])[:3] == (
        "analysis_limitation_v1", ANALYSIS_BUDGET_REASON_ID, LIMITATION_SITE,
    )
    # legacy 診断側にも同じ reason が残る（PR-128-A の診断経路を壊さない）。
    assert [
        reason.reason_id for reason in result.legacy_unknown_reasons
    ] == [ANALYSIS_BUDGET_REASON_ID]


def test_limitation_without_producer_activation_fails_closed():
    """producer emit を 0 にした variant。UNKNOWN へ fail-open しない。"""
    connector = _connector()
    session = connector.begin({"case": "issue125-e2e-1-no-emit"})
    from scripts.function_tracer_pcode.authority.decision import limitation_attribution

    with production_signal_scope(session):
        with patch.object(
            limitation_attribution, "observe_analysis_limitation", return_value=0,
        ):
            result = _check_with_limitation(session)

    assert result.is_equivalent is None
    assert result.failure_status == "limitation_unattributed"
    assert result.error_message == "limitation_unattributed"
    assert result.unknown_reasons == []
    failure = result.diagnostics["failures"]["analysis_limitation"]
    assert failure["disposition"] == "UNATTRIBUTED"
    assert failure["decision_effect"] is None
    assert failure["cause_id"] is None and failure["occurrence_id"] is None


def test_unregistered_limitation_reason_fails_closed():
    from scripts.function_tracer_pcode.core.errors import AnalysisLimitation

    connector = _connector()
    session = connector.begin({"case": "issue125-e2e-1-unregistered"})
    checker = EquivalenceChecker(
        strategy="monolithic", timeout=5, monolithic_timeout=5,
        canonical_decision_cutover=False,
    )
    checker._active_v2_dual_write_pilot_session = session
    limitation = AnalysisLimitation(
        "not_a_sealed_reason_at_all", "nope", site=LIMITATION_SITE,
    )
    with production_signal_scope(session):
        with patch.object(
            checker_module, "assemble_equivalence_result", side_effect=limitation,
        ):
            result = checker.check(_analysis("left", 7), _analysis("right", 7))

    assert result.failure_status == "unregistered_reason"
    assert result.diagnostics["failures"]["analysis_limitation"]["disposition"] == (
        "UNREGISTERED"
    )
    # failure 経路では legacy 診断も UNKNOWN reason を主張しない
    # （canonical が ERROR なのに legacy が UNKNOWN 原因を持つ矛盾を作らない）。
    assert result.unknown_reasons == []
    assert session.recorder.event_count == 0


def test_the_same_limitation_twice_is_one_cause_not_an_error():
    """retry phase が同じ限界を再観測しても cause は 1 件、最終化まで UNKNOWN。

    reducer は同じ occurrence id の再観測を拒否するので、重複を落とさないと
    pair が不透明な ERROR になる。
    """
    connector = _connector()
    session = connector.begin({"case": "issue125-e2e-1-repeat"})
    checker = EquivalenceChecker(
        strategy="monolithic", timeout=5, monolithic_timeout=5,
        canonical_decision_cutover=False,
    )
    with production_signal_scope(session):
        first = _check_with_limitation(session, checker=checker)
        second = _check_with_limitation(session, checker=checker)

    for result in (first, second):
        assert result.failure_status is None
        assert result.diagnostics["failures"]["analysis_limitation"][
            "disposition"
        ] == "ATTRIBUTED_NEW_CAUSE"
    assert session.recorder.event_count == 1

    evidence = connector.finish(
        session, _legacy_view(second), case_id="issue125-e2e-1-repeat",
    )
    pilot = evidence.pilot_result
    assert pilot.candidate.decision_receipt.outcome is Outcome.UNKNOWN
    assert [
        row.reason_id for row in pilot.reduction.projection.c_active_base
    ] == [ANALYSIS_BUDGET_REASON_ID]


def test_a_different_limitation_site_is_a_different_cause():
    """限界ごとに別 cause（1 つのバケットに丸めない）。"""
    from scripts.function_tracer_pcode.authority.domains.analysis_limitation import (
        observe_analysis_limitation,
    )

    connector = _connector()
    session = connector.begin({"case": "issue125-two-sites"})
    with production_signal_scope(session):
        first = observe_analysis_limitation(
            reason_id=ANALYSIS_BUDGET_REASON_ID,
            limitation_site="analysis.tracer.trace",
            target_key=("left",),
        )
        second = observe_analysis_limitation(
            reason_id=ANALYSIS_BUDGET_REASON_ID,
            limitation_site="analysis.recurrence.summarizer.summarize",
            target_key=("left",),
        )
        # 同じ site・同じ target の再観測は新しい cause も event も作らない。
        repeat = observe_analysis_limitation(
            reason_id=ANALYSIS_BUDGET_REASON_ID,
            limitation_site="analysis.tracer.trace",
            target_key=("left",),
        )
    assert first and second and first != second
    assert repeat == first
    assert session.recorder.event_count == 2
    projection = session.preview_lifecycle_projection()
    assert len({row.cause_id for row in projection.c_active_base}) == 2
    assert {row.occurrence_id for row in projection.c_active_base} == {first, second}


def _limitation_occurrence_authority(session, *, site=LIMITATION_SITE, target_key=("left", "right")):
    """`_check_with_limitation` が観測するのと同じ occurrence authority を作る。"""
    signal = AnalysisLimitationBlockerSignal(
        declared_reason_id=ANALYSIS_BUDGET_REASON_ID,
        limitation_site=site,
        canonical_target_key=target_key,
        missing_semantic_fact=(
            "analysis_limitation_unresolved", ANALYSIS_BUDGET_REASON_ID,
        ),
        evidence_refs=("issue125-budget",),
    )
    return session.domain_signal_encoder.authority_for_signal(session, signal)


def _discharge_limitation_requirement(session):
    """限界 cause の唯一の requirement を完了させ、cause を active から外す。"""
    from scripts.function_tracer_pcode.authority.contracts import (
        RequirementCompletionReceipt,
    )
    from scripts.function_tracer_pcode.authority.lifecycle.stream import (
        EventIntent,
        EventType,
        RequirementCompletedEventAuthority,
    )

    authority = _limitation_occurrence_authority(session)
    occurrence = authority.occurrence
    bound = authority.bound_contract
    requirement_id = occurrence.proof_requirement_ids[0]
    receipt = RequirementCompletionReceipt(
        occurrence.cause_id.value,
        occurrence.occurrence_id,
        requirement_id,
        bound.contract_definition_id,
        bound.contract_version,
        bound.bound_expression_digest,
        "issue125-budget-proof-artifact",
        "issue125-budget-applicability",
    )
    session.emit(EventIntent(
        EventType.REQUIREMENT_COMPLETED,
        RequirementCompletedEventAuthority(receipt),
    ))
    return occurrence.occurrence_id


def test_a_discharged_limitation_reobserved_never_rides_the_old_cause():
    """discharge 済みの限界を再観測しても、履歴だけで成功扱いしない（blocker 回帰）。

    観測 → requirement 完了 → cause が `c_active_base` から消える → その状態で
    decisive proof が通り得る → **同じ限界を再観測**。ここで「一度観測した」を
    根拠に UNKNOWN 成功にすると、未解消の限界が EQUIVALENT へ黙って抜ける。
    """
    from scripts.function_tracer_pcode.authority.decision.decision import (
        DecisiveProofKind,
        DecisiveProofReceipt,
        FinalizationAuthority,
        finalize_decision,
    )
    from scripts.function_tracer_pcode.authority.decision.production_cutover import (
        issue_infrastructure_error_decision,
    )
    from scripts.function_tracer_pcode.authority.lifecycle.production_boundary import (
        LegacyBoundaryErrorKind,
        _issue_legacy_boundary_error,
    )

    connector = _connector()
    session = connector.begin({"case": "issue125-discharged-rearm"})
    checker = EquivalenceChecker(
        strategy="monolithic", timeout=5, monolithic_timeout=5,
        canonical_decision_cutover=False,
    )
    with production_signal_scope(session):
        first = _check_with_limitation(session, checker=checker)
        assert first.failure_status is None
        assert first.diagnostics["failures"]["analysis_limitation"][
            "disposition"
        ] == "ATTRIBUTED_NEW_CAUSE"
        observed_id = _discharge_limitation_requirement(session)

        # cause は active から消えた（= 未解消の blocker はもう無い）。
        after_discharge = session.preview_lifecycle_projection()
        assert observed_id not in {
            row.occurrence_id for row in after_discharge.c_active_base
        }
        assert after_discharge.c_active_base == ()

        second = _check_with_limitation(session, checker=checker)

    # 履歴 ledger には残っている（= かつて観測した）。それでも active ではない。
    ever_observed = session.domain_signal_state[ANALYSIS_LIMITATION_LEDGER_KEY]
    assert observed_id in ever_observed
    assert second.failure_status == "limitation_unattributed"
    failure = second.diagnostics["failures"]["analysis_limitation"]
    assert failure["disposition"] == "UNATTRIBUTED"
    assert "not active" in failure["detail"]
    assert failure["decision_effect"] is None
    assert second.unknown_reasons == []
    # 重複 event も作っていない（観測 1 + 完了 1）。producer-site discovery も
    # 再観測では開かれないので、activation と実 event が食い違わない。
    assert session.recorder.event_count == 2
    assert len(session.phase7_runtime._materialized) == 1
    assert session.phase7_runtime._pending == {}

    # production boundary はこれを canonical ERROR にするので EQUIVALENT へ抜けない。
    artifact = _issue_legacy_boundary_error(session, second)
    assert artifact.error_kind is LegacyBoundaryErrorKind.LIMITATION_UNATTRIBUTED
    decision = issue_infrastructure_error_decision(
        result_occurrence_id=session.identity.result_occurrence_id,
        error_kind=artifact.error_kind.value,
        error_artifact_digest=artifact.artifact_digest,
    )
    assert decision.outcome is Outcome.ERROR

    # 対比: active な blocker が無いので、限界を「帰属できた」と誤報告していたら
    # EQ closure がそのまま decisive になっていた。
    projection = session.reducer.replay(session.recorder.seal()).projection
    assert projection.c_active_base == ()
    would_have_been = finalize_decision(FinalizationAuthority(
        session.identity.result_occurrence_id,
        projection,
        (DecisiveProofReceipt.create(
            result_occurrence_id=session.identity.result_occurrence_id,
            lifecycle_projection_digest=projection.lifecycle_projection_digest,
            proof_kind=DecisiveProofKind.EQ_CLOSURE,
            proof_artifact_digest="issue125-eq-closure",
        ),),
    ))
    assert would_have_been.outcome is Outcome.EQUIVALENT


def test_an_active_limitation_reobserved_keeps_blocking():
    """active なままの限界を再観測しても cause は 1 件で、EQ は通らない。"""
    from scripts.function_tracer_pcode.authority.decision.decision import (
        DecisiveProofKind,
        DecisiveProofReceipt,
        FinalizationAuthority,
        finalize_decision,
    )

    connector = _connector()
    session = connector.begin({"case": "issue125-active-rearm"})
    checker = EquivalenceChecker(
        strategy="monolithic", timeout=5, monolithic_timeout=5,
        canonical_decision_cutover=False,
    )
    with production_signal_scope(session):
        first = _check_with_limitation(session, checker=checker)
        second = _check_with_limitation(session, checker=checker)

    for result in (first, second):
        assert result.failure_status is None
        failure = result.diagnostics["failures"]["analysis_limitation"]
        assert failure["disposition"] == "ATTRIBUTED_NEW_CAUSE"
        assert failure["decision_effect"] == "blocks_decision"
        assert failure["occurrence_id"] and failure["cause_id"]
    assert (
        first.diagnostics["failures"]["analysis_limitation"]["occurrence_id"]
        == second.diagnostics["failures"]["analysis_limitation"]["occurrence_id"]
    )
    assert session.recorder.event_count == 1
    assert len(session.phase7_runtime._materialized) == 1

    projection = session.reducer.replay(session.recorder.seal()).projection
    assert [row.reason_id for row in projection.c_active_base] == [
        ANALYSIS_BUDGET_REASON_ID
    ]
    blocked = finalize_decision(FinalizationAuthority(
        session.identity.result_occurrence_id,
        projection,
        (DecisiveProofReceipt.create(
            result_occurrence_id=session.identity.result_occurrence_id,
            lifecycle_projection_digest=projection.lifecycle_projection_digest,
            proof_kind=DecisiveProofKind.EQ_CLOSURE,
            proof_artifact_digest="issue125-eq-closure",
        ),),
    ))
    assert blocked.outcome is Outcome.UNKNOWN


# --- E2E-2 ------------------------------------------------------------------

def test_limitation_after_other_producer_activation_keeps_both_causes():
    connector = _connector()
    session = connector.begin({"case": "issue125-e2e-2"})
    with production_signal_scope(session):
        assert emit_sat_safety_signal(
            _sat_blocker(),
            producer_site_manifest_id="sat-safety-blocker-observed",
        ) == 1
        result = _check_with_limitation(session)

    evidence = connector.finish(session, _legacy_view(result), case_id="issue125-e2e-2")
    pilot = evidence.pilot_result
    assert pilot.candidate.decision_receipt.outcome is Outcome.UNKNOWN
    assert {
        row.reason_id for row in pilot.reduction.projection.c_active_base
    } == {ANALYSIS_BUDGET_REASON_ID, "counterexample_analysis_safety_unproven"}


# --- E2E-3（最重要） ---------------------------------------------------------

def test_limitation_after_eq_closure_receipt_never_yields_eq():
    """EQ closure を発行済みの session に新しい限界が出ても EQ へ抜けない。"""
    connector = _connector()
    session = connector.begin({"case": "issue125-e2e-3"})
    with production_signal_scope(session):
        trusted = EquivalenceChecker(
            strategy="monolithic", timeout=5, monolithic_timeout=5,
            canonical_decision_cutover=False,
        ).check(_analysis("left", 7), _analysis("right", 7))
        frame = trusted._prepared_dispatch_frame
        issue_pending_eq_closure_authority(session, frame.receipt, frame)
        result = _check_with_limitation(session)

    evidence = connector.finish(session, _legacy_view(result), case_id="issue125-e2e-3")
    pilot = evidence.pilot_result
    receipt = pilot.candidate.decision_receipt
    assert receipt.outcome is not Outcome.EQUIVALENT
    assert receipt.outcome is Outcome.UNKNOWN
    active = {row.reason_id for row in pilot.reduction.projection.c_active_base}
    assert ANALYSIS_BUDGET_REASON_ID in active
    semantics = pilot.candidate.decision_receipt
    assert semantics.outcome is Outcome.UNKNOWN
    # semantic projection の `c_active_semantics` にも限界 cause が載る。
    rows = {
        row.reason_id for row in pilot.reduction.projection.c_active_base
    }
    assert ANALYSIS_BUDGET_REASON_ID in rows


# --- digest 契約（独立 finalization 2 本） -------------------------------------

def _result_for_preimage():
    from scripts.function_tracer_pcode.checker.result import EquivalenceResult

    return EquivalenceResult(
        is_equivalent=True,
        function1_name="left",
        function2_name="right",
        binary1_name="left",
        binary2_name="right",
        solver_results=None,
    )


def _preimage(**overrides):
    payload = {
        "function1_name": "left",
        "function2_name": "right",
        "binary1_content_identity": "binary-1",
        "binary2_content_identity": "binary-2",
    }
    payload.update(overrides)
    return payload


def test_diagnostics_failures_change_preimage_not_semantic_fields(tmp_path, monkeypatch):
    """診断だけの変更: preimage は変わるが semantic projection は変わらない。

    2 本の finalization は session / evidence / bundle を共有しない
    （共有すると一致が vacuous になる）。実 run 間 digest は根拠に使わない。
    """
    from scripts.function_tracer_pcode.checker.diagnostics import (
        attach_failure_diagnostics,
    )
    from scripts.function_tracer_pcode.core.errors import (
        log_swallowed,
        reset_swallowed_exceptions,
    )
    from scripts.function_tracer_pcode.tests.unit._finalization_support import (
        _independent_finalization,
    )

    bundle_key = tmp_path / "canonical-bundle.key"
    bundle_key.write_bytes(b"k" * 32)
    monkeypatch.setenv("UNKNOWN_TAXONOMY_V2_SUPERVISOR_KEY_ID", "issue125-test-key")
    monkeypatch.setenv("UNKNOWN_TAXONOMY_V2_SUPERVISOR_KEY_FILE", str(bundle_key))
    monkeypatch.setenv(
        "UNKNOWN_TAXONOMY_V2_RESULT_ENTRY_OCCURRENCE_NONCE", "issue125-occurrence"
    )

    without_failures = _result_for_preimage()
    with_failures = _result_for_preimage()
    reset_swallowed_exceptions()
    try:
        log_swallowed("expression_semantics_unsupported", ValueError("x"), "analysis.tracer.trace")
        attach_failure_diagnostics(with_failures)
    finally:
        reset_swallowed_exceptions()

    payload_without = without_failures.to_dict()
    payload_with = with_failures.to_dict()

    # 差は diagnostics だけ、その中でも `failures` だけ。
    assert payload_with != payload_without
    assert {k: v for k, v in payload_with.items() if k != "diagnostics"} == {
        k: v for k, v in payload_without.items() if k != "diagnostics"
    }
    assert payload_with["diagnostics"]["failures"] != (
        payload_without["diagnostics"]["failures"]
    )
    assert {
        k: v for k, v in payload_with["diagnostics"].items() if k != "failures"
    } == {
        k: v for k, v in payload_without["diagnostics"].items() if k != "failures"
    }

    bundle_without, session_a, evidence_a = _independent_finalization(
        tmp_path, monkeypatch,
        case_id="issue125-without-failures",
        result_payload_preimage=payload_without,
    )
    bundle_with, session_b, evidence_b = _independent_finalization(
        tmp_path, monkeypatch,
        case_id="issue125-with-failures",
        result_payload_preimage=payload_with,
    )
    # 2 本は独立: session / evidence / bundle のどれも共有していない。
    assert session_a is not session_b
    assert evidence_a is not evidence_b
    assert evidence_a.pilot_result is not evidence_b.pilot_result
    assert bundle_without["sealed_event_stream"] and bundle_with["sealed_event_stream"]

    assert (
        bundle_without["canonical_result_payload_preimage_digest"]
        != bundle_with["canonical_result_payload_preimage_digest"]
    )
    assert (
        bundle_without["canonical_semantic_result_projection"]["payload"]
        == bundle_with["canonical_semantic_result_projection"]["payload"]
    )
    assert (
        bundle_without["canonical_semantic_result_projection"]["semantic_projection_digest"]
        == bundle_with["canonical_semantic_result_projection"]["semantic_projection_digest"]
    )


def test_error_kind_change_is_an_intentional_semantic_change():
    """generic ERROR の `error_kind` 変更は意図的な semantic 契約変更。

    outcome は両方 ERROR のまま、`_semantic_projection` の `error_kind` field が
    変わる。「不変」と主張しないための固定。
    """
    from scripts.function_tracer_pcode.authority.decision.canonical_result import (
        _semantic_projection,
    )
    from scripts.function_tracer_pcode.authority.decision.decision import (
        DecisiveProofKind,
        ErrorReceipt,
    )
    from scripts.function_tracer_pcode.authority.contracts import (
        VerifiedLifecycleProjection,
        authority_digest,
    )

    result_id = "result-issue125-error-kind"
    projection = VerifiedLifecycleProjection.seal(
        result_occurrence_id=result_id,
        snapshot_digest=authority_digest((result_id, "snapshot")),
        c_active_base=(),
        q_open_base=(),
        blocker_eligibility_base=(),
        satisfaction_projection=(),
    )

    def _pilot(error_kind):
        receipt = ErrorReceipt.create(
            result_occurrence_id=result_id,
            lifecycle_projection_digest=projection.lifecycle_projection_digest,
            error_kind=error_kind,
            error_artifact_digest="issue125-error-artifact",
        )
        return SimpleNamespace(
            reduction=SimpleNamespace(projection=projection),
            sealed_event_stream=SimpleNamespace(envelope=SimpleNamespace(
                source_snapshot_fingerprint="snapshot-issue125",
            )),
            candidate=SimpleNamespace(decision_receipt=SimpleNamespace(
                outcome=Outcome.ERROR,
            )),
            decisive_proof_receipts=(),
            terminal_timeout_receipts=(),
            error_receipts=(receipt,),
        )

    del DecisiveProofKind
    legacy = _semantic_projection(_preimage(), _pilot("legacy_compatibility_error"))
    typed = _semantic_projection(_preimage(), _pilot("internal_exception"))

    assert legacy["payload"]["canonical_outcome"] == "ERROR"
    assert typed["payload"]["canonical_outcome"] == "ERROR"
    assert legacy["payload"]["error_kind"] == "legacy_compatibility_error"
    assert typed["payload"]["error_kind"] == "internal_exception"
    assert (
        legacy["semantic_projection_digest"] != typed["semantic_projection_digest"]
    )
