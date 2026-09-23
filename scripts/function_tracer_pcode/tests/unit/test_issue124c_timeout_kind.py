# -*- coding: utf-8 -*-
"""Issue #124 PR-124-C: `timeout_kind` の分類テーブル（D13）。

契約:

* P（supervisor の process deadline）と S（子の solver timeout）を**独立に**評価する。
* payload の存在だけ・log の文字列・returncode 単独からは推定しない。
* 無関係な field が増えても分類は変わらない。有効な S 証拠を取り除けば S は未確認。
* 別 nonce / 無効 bundle / 証拠不整合は fail-closed（`unknown`）。
* 全 deadline disposition（`EXITED_*_AFTER_SIGKILL` を含む）を扱う。
"""

from __future__ import annotations

import copy
import json
import signal
from pathlib import Path

import pytest

from scripts.function_tracer_pcode.reporting.timeout_hotspot_summary import (
    EVIDENCE_ABSENT,
    EVIDENCE_CONFIRMED,
    EVIDENCE_INVALID,
    KIND_BOTH_SIGNALS,
    KIND_CHILD_SOLVER_TIMEOUT,
    KIND_NOT_APPLICABLE,
    KIND_PROCESS_WALL_CLOCK,
    KIND_UNKNOWN,
    classify_timeout_kind,
    child_solver_timeout_evidence,
    supervisor_deadline_evidence,
)
from scripts.function_tracer_pcode.proof.formula.input_correspondence import build_input_correspondence_set

OCCURRENCE = "production-pilot-0b193214248780a69165c124"
STREAM = f"stream-{OCCURRENCE}"
FINGERPRINT = "0b193214248780a69165c1240afa1251f3b5af91f9c50b0a8bcac4f064097cc3"


def _pair_status(**overrides):
    """supervisor deadline の TIMEOUT（実 run の pair-status と同じ形）。"""
    payload = {
        "canonical_outcome": "TIMEOUT",
        "supervisor_status": "TIMEOUT",
        "supervisor_authority_kind": "DurableTimeoutFinalizationBundle",
        "authority_kind": "DurableTimeoutFinalizationBundle",
        "child_exit_disposition": "EXITED_143_AFTER_SIGTERM",
        "child_returncode": 143,
        "child_returncode_observation_kind": "LIVE_PROCESS_WAIT",
        "classification_valid": True,
        "result_occurrence_id": OCCURRENCE,
        "stream_id": STREAM,
        "source_snapshot_fingerprint": FINGERPRINT,
        "error_kind": None,
    }
    payload.update(overrides)
    return payload


def _resolved_status(**overrides):
    """子が自分で finalize した（supervisor は RESOLVED）ときの pair-status。"""
    payload = {
        "canonical_outcome": "TIMEOUT",
        "supervisor_status": "RESOLVED",
        "supervisor_authority_kind": "SupervisorCanonicalResultResolvedReceipt",
        "child_returncode": 3,
        "classification_valid": True,
        "result_occurrence_id": OCCURRENCE,
        "stream_id": STREAM,
        "source_snapshot_fingerprint": FINGERPRINT,
    }
    payload.update(overrides)
    return payload


def _sidecar_evidence(**overrides):
    """cleanup 前に検証した子の terminal timeout 証拠（sidecar に入る形）。"""
    evidence = {
        "observed": True,
        "validated": True,
        "validation_error": None,
        "source": "checkpoint_result_envelope",
        "canonical_outcome": "TIMEOUT",
        "bundle_digest": "a" * 64,
        "result_occurrence_id": OCCURRENCE,
        "stream_id": STREAM,
        "source_snapshot_fingerprint": FINGERPRINT,
        "terminal_timeout_requirement_ids": ["loop_exact_term_relation"],
        "terminal_timeout_solver_invocation_id": "solver-invocation-1",
        "terminal_timeout_query_digest": "b" * 64,
    }
    evidence.update(overrides)
    return {"schema": "pair-stack-dump-status-v1", "child_timeout_evidence": evidence}


# ---------------------------------------------------------------------------
# P だけ
# ---------------------------------------------------------------------------


def test_process_deadline_only_is_process_wall_clock():
    report = classify_timeout_kind(_pair_status())
    assert report.kind == KIND_PROCESS_WALL_CLOCK
    assert report.process_deadline.status == EVIDENCE_CONFIRMED
    assert report.child_solver.status == EVIDENCE_ABSENT


@pytest.mark.parametrize("disposition,returncode", [
    ("SIGTERM_AFTER_DEADLINE", -15),
    ("SIGKILL_AFTER_DEADLINE", -9),
    ("EXITED_143_AFTER_SIGTERM", 143),
    ("EXITED_137_AFTER_SIGKILL", 137),
    ("EXITED_0_BEFORE_SIGTERM", 0),
    ("EXITED_3_BEFORE_SIGKILL", 3),
    ("EXITED_2", 2),
])
def test_every_deadline_disposition_is_accepted(disposition, returncode):
    """`_terminate_exact_process_group` が返し得る全 disposition を扱う。"""
    status = _pair_status(
        child_exit_disposition=disposition, child_returncode=returncode
    )
    assert classify_timeout_kind(status).kind == KIND_PROCESS_WALL_CLOCK


def test_durable_restart_without_child_status_is_still_process_deadline():
    status = _pair_status(
        child_returncode=None,
        child_returncode_observation_kind="DURABLE_RESTART_NO_CHILD_STATUS",
        child_exit_disposition="SIGKILL_AFTER_DEADLINE",
    )
    assert classify_timeout_kind(status).kind == KIND_PROCESS_WALL_CLOCK


@pytest.mark.parametrize("overrides", [
    {"supervisor_status": "RESOLVED"},
    {"supervisor_authority_kind": "SupervisorCanonicalResultResolvedReceipt"},
    {"classification_valid": False},
    {"child_exit_disposition": "KILLED_SOMEHOW"},
    {"child_exit_disposition": "EXIT_CODE_143"},
    {"child_returncode": 0},
    {"child_returncode_observation_kind": "GUESSED"},
])
def test_contradictory_deadline_evidence_is_invalid_not_confirmed(overrides):
    evidence = supervisor_deadline_evidence(_pair_status(**overrides))
    assert evidence.status == EVIDENCE_INVALID
    assert evidence.confirmed is False


def test_missing_deadline_fields_are_absent_not_invalid():
    status = _pair_status()
    for key in (
        "supervisor_status", "supervisor_authority_kind",
        "child_exit_disposition", "child_returncode",
        "child_returncode_observation_kind", "classification_valid",
    ):
        status.pop(key)
    evidence = supervisor_deadline_evidence(status)
    assert evidence.status == EVIDENCE_ABSENT
    assert "supervisor_status" in evidence.missing


def test_wildcard_prefix_alone_is_not_a_deadline_disposition():
    """`EXITED_` で始まるだけの文字列は受け付けない（完全一致で判定する）。"""
    evidence = supervisor_deadline_evidence(
        _pair_status(child_exit_disposition="EXITED_143_AFTER_SOMETHING")
    )
    assert evidence.status == EVIDENCE_INVALID


# ---------------------------------------------------------------------------
# S だけ
# ---------------------------------------------------------------------------


def test_child_solver_timeout_only_from_verified_sidecar_evidence():
    report = classify_timeout_kind(
        _resolved_status(), status_sidecar=_sidecar_evidence()
    )
    assert report.kind == KIND_CHILD_SOLVER_TIMEOUT
    assert report.child_solver.status == EVIDENCE_CONFIRMED
    assert report.process_deadline.confirmed is False


def test_resolved_with_returncode_three_alone_is_unknown():
    """`RESOLVED + returncode=3` だけでは solver 由来と断定しない。"""
    report = classify_timeout_kind(_resolved_status())
    assert report.kind == KIND_UNKNOWN
    assert report.child_solver.status == EVIDENCE_ABSENT


@pytest.mark.parametrize("overrides,expected", [
    ({"validated": False, "validation_error": "ValueError"}, EVIDENCE_INVALID),
    ({"result_occurrence_id": "production-pilot-other"}, EVIDENCE_INVALID),
    ({"stream_id": "stream-other"}, EVIDENCE_INVALID),
    ({"source_snapshot_fingerprint": "f" * 64}, EVIDENCE_INVALID),
    ({"canonical_outcome": "UNKNOWN"}, EVIDENCE_INVALID),
    ({"terminal_timeout_solver_invocation_id": None}, EVIDENCE_ABSENT),
])
def test_child_evidence_fails_closed(overrides, expected):
    sidecar = _sidecar_evidence(**overrides)
    evidence = child_solver_timeout_evidence(
        _resolved_status(), status_sidecar=sidecar
    )
    assert evidence.status == expected
    assert evidence.confirmed is False


def test_removing_the_solver_identification_makes_s_unconfirmed():
    """有効な S 証拠を取り除けば S は未確認になる（payload の有無とは別）。"""
    with_solver = classify_timeout_kind(
        _resolved_status(), status_sidecar=_sidecar_evidence()
    )
    without_solver = classify_timeout_kind(
        _resolved_status(),
        status_sidecar=_sidecar_evidence(terminal_timeout_solver_invocation_id=None),
    )
    assert with_solver.kind == KIND_CHILD_SOLVER_TIMEOUT
    assert without_solver.kind == KIND_UNKNOWN


def test_irrelevant_payload_does_not_change_the_classification():
    """無関係な field を足しても分類は変わらない。"""
    baseline = classify_timeout_kind(
        _resolved_status(), status_sidecar=_sidecar_evidence()
    )
    noisy_status = _resolved_status(
        some_new_diagnostic_block={"a": [1, 2, 3]},
        semantic_projection_digest="c" * 64,
        pair_status_signature="signature",
    )
    noisy_sidecar = _sidecar_evidence()
    noisy_sidecar["unrelated_diagnostic"] = {"frames": 12}
    noisy_sidecar["child_timeout_evidence"]["extra_note"] = "ignored"
    noisy = classify_timeout_kind(noisy_status, status_sidecar=noisy_sidecar)
    assert noisy.kind == baseline.kind == KIND_CHILD_SOLVER_TIMEOUT


# ---------------------------------------------------------------------------
# P と S が独立に成立
# ---------------------------------------------------------------------------


def test_child_timeout_followed_by_supervisor_deadline_is_both_signals():
    """子が TIMEOUT を確定したあと supervisor が deadline で終わらせた場合。"""
    report = classify_timeout_kind(
        _pair_status(), status_sidecar=_sidecar_evidence()
    )
    assert report.kind == KIND_BOTH_SIGNALS
    assert report.process_deadline.confirmed is True
    assert report.child_solver.confirmed is True


def test_both_signals_does_not_require_supervisor_status_to_be_two_values():
    """P と S は別 field から取る。1 つの `supervisor_status` に両立を求めない。"""
    report = classify_timeout_kind(
        _pair_status(child_exit_disposition="EXITED_3_AFTER_SIGTERM",
                     child_returncode=3),
        status_sidecar=_sidecar_evidence(),
    )
    assert report.kind == KIND_BOTH_SIGNALS
    assert report.process_deadline.detail["supervisor_status"] == "TIMEOUT"


# ---------------------------------------------------------------------------
# unknown / not_applicable
# ---------------------------------------------------------------------------


def test_timeout_without_either_evidence_is_unknown():
    status = _resolved_status(supervisor_authority_kind=None)
    report = classify_timeout_kind(status)
    assert report.kind == KIND_UNKNOWN


def test_non_timeout_outcome_is_not_applicable():
    for outcome in ("EQUIVALENT", "NOT_EQ", "UNKNOWN", "ERROR"):
        report = classify_timeout_kind(_pair_status(canonical_outcome=outcome))
        assert report.kind == KIND_NOT_APPLICABLE


def test_missing_outcome_is_unknown_not_not_applicable():
    status = _pair_status()
    status.pop("canonical_outcome")
    assert classify_timeout_kind(status).kind == KIND_UNKNOWN
    assert classify_timeout_kind({}).kind == KIND_UNKNOWN


def test_crash_like_dispositions_are_not_pulled_into_this_taxonomy():
    """#129 の異常終了分類へ範囲を広げない（outcome が TIMEOUT 以外なら NA）。"""
    report = classify_timeout_kind(_pair_status(
        canonical_outcome="ERROR", error_kind="operational_authority_invalid",
        child_exit_disposition="EXIT_CODE_134", child_returncode=134,
    ))
    assert report.kind == KIND_NOT_APPLICABLE


# ---------------------------------------------------------------------------
# 実 bundle を使った S の抽出
# ---------------------------------------------------------------------------


@pytest.fixture(scope="module")
def real_timeout_payload():
    """実際に production pilot を回して作った TIMEOUT の canonical payload。

    `terminal_timeout_receipts` と
    `terminal_timeout_candidate_selection_receipt.solver_invocation_id` を持つ
    本物の bundle でないと、S の抽出（bundle 検証込み）を検査したことにならない。
    """
    return _build_real_timeout_payload()


def _build_real_timeout_payload():
    import os
    from types import SimpleNamespace

    from scripts.function_tracer_pcode.authority.decision.canonical_result import (
        build_canonical_result_finalization_bundle,
    )
    from scripts.function_tracer_pcode.authority.domains.loop_recurrence import (
        LOOP_REASON_REGISTRY,
        LOOP_RECOVERY_REGISTRY,
        LoopBlockerProductionSignal,
        LoopRecurrencePilotEncoder,
        LoopSolverExecutionBatchSignal,
    )
    from scripts.function_tracer_pcode.authority.lifecycle.execution_authority import (
        activate_process_worker_execution_authority_deployment,
    )
    from scripts.function_tracer_pcode.authority.lifecycle.pilot import (
        ProductionDualWritePilotConnector,
    )
    from scripts.function_tracer_pcode.authority.lifecycle.production_signals import (
        CompositeProductionSignalEncoder,
        active_loop_requirement_for_signal,
        emit_loop_recurrence_signal,
        execute_loop_solver_rendered_query,
        production_signal_scope,
    )
    from scripts.function_tracer_pcode.authority.lifecycle.reducer import (
        ShadowLifecycleReducer,
    )
    from scripts.function_tracer_pcode.authority.sites.runtime import (
        runtime_from_audited_manifest,
    )
    from scripts.function_tracer_pcode.proof.strategies.pairwise_query_executor import (
        render_loop_v2_solver_query,
    )
    from scripts.function_tracer_pcode.smt.interface import SolverResult, SolverStatus
    from scripts.function_tracer_pcode.smt.parallel import ParallelResult
    from scripts.function_tracer_pcode.authority.lifecycle import (
        execution_authority as execution_module,
    )
    from scripts.function_tracer_pcode.tests.unit._loop_test_fixtures import (
        loop_exact_fixture,
    )

    key = b"w" * 32
    activate_process_worker_execution_authority_deployment(
        key_id="worker-key-v1", key=key, key_source_id="issue124c-timeout-kind",
    )
    previous = execution_module._PINNED_PARALLEL_RUN_IMPL
    execution_module._PINNED_PARALLEL_RUN_IMPL = (
        lambda _runner, _query, timeout: ParallelResult(results=[
            SolverResult("z3", SolverStatus.TIMEOUT, elapsed_time=timeout),
        ])
    )
    try:
        root = Path(__file__).resolve().parents[4]
        manifest = json.loads((
            root / "artifacts/unknown_taxonomy_v2/phase7/producer-sites.json"
        ).read_text(encoding="utf-8"))
        encoder = LoopRecurrencePilotEncoder()
        connector = ProductionDualWritePilotConnector(
            ShadowLifecycleReducer(
                reason_registry=LOOP_REASON_REGISTRY,
                recovery_registry=LOOP_RECOVERY_REGISTRY,
            ),
            domain_signal_encoder=CompositeProductionSignalEncoder({
                LoopBlockerProductionSignal: encoder,
                LoopSolverExecutionBatchSignal: encoder,
            }),
            phase7_runtime_factory=lambda identity: runtime_from_audited_manifest(
                manifest, identity
            ),
        )
        session = connector.begin({"case": "issue124c-timeout-kind"})
        blocker, _, _, _, exact_case, summary_case, left, right = (
            loop_exact_fixture()
        )
        with production_signal_scope(session):
            assert emit_loop_recurrence_signal(
                blocker, producer_site_manifest_id="pairwise-pending-loop-blocker",
            ) == 1
            requirement = active_loop_requirement_for_signal(
                blocker, "loop_exact_term_relation"
            )
            rendered = render_loop_v2_solver_query(
                blocker=blocker,
                requirement=requirement,
                analysis1=left,
                analysis2=right,
                input_correspondence=build_input_correspondence_set(left, right),
                case1=exact_case,
                case2=summary_case,
                pair_id="(issue124c,left,right)",
                execution_identity_digest=session.identity.execution_identity_digest,
            )
            assert execute_loop_solver_rendered_query(
                blocker, rendered, configured_timeout_ms=1000,
            ) == 1
        evidence = connector.finish(
            session,
            SimpleNamespace(
                is_equivalent=None, error_message=None, failure_status=None,
                failure_message=None, is_timeout=lambda: True,
            ),
            case_id="issue124c-timeout-kind",
        )
        preimage = {"final_outcome": "TIMEOUT", "total_time": 0.0}
        bundle = build_canonical_result_finalization_bundle(
            result_payload_preimage=preimage, evidence=evidence, session=session,
        )
    finally:
        execution_module._PINNED_PARALLEL_RUN_IMPL = previous
    payload = {**preimage, "canonical_result_finalization_bundle": bundle}
    identity = bundle["execution_identity"]
    return payload, identity


def _status_for(identity, **overrides):
    payload = {
        "canonical_outcome": "TIMEOUT",
        "supervisor_status": "RESOLVED",
        "supervisor_authority_kind": "SupervisorCanonicalResultResolvedReceipt",
        "child_returncode": 3,
        "classification_valid": True,
        "result_occurrence_id": identity["result_occurrence_id"],
        "stream_id": identity["stream_id"],
        "source_snapshot_fingerprint": identity["source_snapshot_fingerprint"],
    }
    payload.update(overrides)
    return payload


def test_real_child_bundle_is_verified_before_it_counts_as_s(real_timeout_payload):
    payload, identity = real_timeout_payload
    evidence = child_solver_timeout_evidence(
        _status_for(identity), result_payload=payload
    )
    assert evidence.status == EVIDENCE_CONFIRMED
    assert evidence.detail["source"] == "pair_log_result_payload"
    assert evidence.detail["canonical_outcome"] == "TIMEOUT"
    assert evidence.detail["terminal_timeout_solver_invocation_id"]
    assert classify_timeout_kind(
        _status_for(identity), result_payload=payload
    ).kind == KIND_CHILD_SOLVER_TIMEOUT


def test_real_bundle_bound_to_another_execution_is_rejected(real_timeout_payload):
    """別 nonce（別 execution）の bundle を S の証拠にしない。"""
    payload, identity = real_timeout_payload
    other = _status_for(identity, result_occurrence_id="production-pilot-other-nonce")
    evidence = child_solver_timeout_evidence(other, result_payload=payload)
    assert evidence.status == EVIDENCE_INVALID
    assert "execution_identity" in evidence.violations
    assert classify_timeout_kind(other, result_payload=payload).kind == KIND_UNKNOWN


def test_tampered_real_bundle_is_rejected(real_timeout_payload):
    """seal が合わない bundle は検証で落ちる（`invalid`、`confirmed` ではない）。"""
    payload, identity = real_timeout_payload
    tampered = copy.deepcopy(payload)
    tampered["canonical_result_finalization_bundle"]["bundle_digest"] = "0" * 64
    evidence = child_solver_timeout_evidence(
        _status_for(identity), result_payload=tampered
    )
    assert evidence.status == EVIDENCE_INVALID
    assert evidence.detail["validation_error"] == "ValueError"


def test_removing_the_terminal_timeout_receipts_makes_s_unconfirmed(
    real_timeout_payload,
):
    """有効な S 証拠の除去（無関係 payload の追加とは区別する）。"""
    payload, identity = real_timeout_payload
    stripped = copy.deepcopy(payload)
    bundle = stripped["canonical_result_finalization_bundle"]
    bundle["terminal_timeout_receipts"] = []
    evidence = child_solver_timeout_evidence(
        _status_for(identity), result_payload=stripped
    )
    # 受領書を抜くと bundle の seal も崩れるので、まず検証で落ちる。
    assert evidence.confirmed is False
    assert evidence.status == EVIDENCE_INVALID


def test_adding_an_unrelated_top_level_field_keeps_the_same_kind(real_timeout_payload):
    """pair-status に無関係 field を足しても S / 分類は変わらない。"""
    payload, identity = real_timeout_payload
    noisy = _status_for(identity, unrelated_block={"x": 1}, another_note="ignored")
    assert classify_timeout_kind(
        noisy, result_payload=payload
    ).kind == KIND_CHILD_SOLVER_TIMEOUT


def test_real_bundle_plus_supervisor_deadline_is_both_signals(real_timeout_payload):
    payload, identity = real_timeout_payload
    status = _status_for(
        identity,
        supervisor_status="TIMEOUT",
        supervisor_authority_kind="DurableTimeoutFinalizationBundle",
        child_exit_disposition="EXITED_137_AFTER_SIGKILL",
        child_returncode=137,
        child_returncode_observation_kind="LIVE_PROCESS_WAIT",
    )
    assert classify_timeout_kind(
        status, result_payload=payload
    ).kind == KIND_BOTH_SIGNALS


# ---------------------------------------------------------------------------
# 「どこまで検証したか」を混ぜない（sidecar 優先 / pair-log は署名未検証）
# ---------------------------------------------------------------------------


def _sealed_timeout_payload(tmp_path, monkeypatch, key=b"s" * 32):
    """supervisor signing key で封をした本物の TIMEOUT payload を作る。"""
    key_file = tmp_path / "supervisor.key"
    key_file.write_bytes(key)
    monkeypatch.setenv("UNKNOWN_TAXONOMY_V2_SUPERVISOR_KEY_ID", "supervisor-key-v1")
    monkeypatch.setenv("UNKNOWN_TAXONOMY_V2_SUPERVISOR_KEY_FILE", str(key_file))
    try:
        return _build_real_timeout_payload()
    finally:
        monkeypatch.delenv("UNKNOWN_TAXONOMY_V2_SUPERVISOR_KEY_ID", raising=False)
        monkeypatch.delenv("UNKNOWN_TAXONOMY_V2_SUPERVISOR_KEY_FILE", raising=False)


def test_a_sealed_bundle_without_the_key_is_not_verified_s_evidence(
    tmp_path, monkeypatch,
):
    """key を渡さない pair-log fallback は「supervisor-key verified」にしない。

    key 無しの `validate_canonical_result_finalization_bundle` は digest と
    event stream の replay しか見ず、`bundle_signature` を検査しない。
    封のある bundle をその状態で確定 S 証拠として採用してはいけない。
    """
    payload, identity = _sealed_timeout_payload(tmp_path, monkeypatch)
    evidence = child_solver_timeout_evidence(
        _status_for(identity), result_payload=payload
    )
    assert evidence.confirmed is False
    assert evidence.status == EVIDENCE_ABSENT
    assert "supervisor_key_verification" in evidence.missing
    assert evidence.detail["verification"] == "replay_only_unsigned"
    # 分類も S 未確認として扱う（P も無いので unknown）。
    assert classify_timeout_kind(
        _status_for(identity), result_payload=payload
    ).kind == KIND_UNKNOWN


def test_the_same_sealed_bundle_with_the_key_is_verified(tmp_path, monkeypatch):
    payload, identity = _sealed_timeout_payload(tmp_path, monkeypatch)
    evidence = child_solver_timeout_evidence(
        _status_for(identity), result_payload=payload,
        bundle_verification_key_id="supervisor-key-v1",
        bundle_verification_key=b"s" * 32,
    )
    assert evidence.status == EVIDENCE_CONFIRMED
    assert evidence.detail["verification"] == "supervisor_key_verified"
    assert classify_timeout_kind(
        _status_for(identity), result_payload=payload,
        bundle_verification_key_id="supervisor-key-v1",
        bundle_verification_key=b"s" * 32,
    ).kind == KIND_CHILD_SOLVER_TIMEOUT


def test_a_rebuilt_body_and_digest_with_a_stale_signature_is_rejected(
    tmp_path, monkeypatch,
):
    """body / digest を整合させて作り直しても、署名が合わなければ採用しない。

    digest だけを検査する経路は、body を書き換えて digest を再計算すれば通って
    しまう。key を渡す呼び出しでは署名で弾き、key を渡さない呼び出しでは
    そもそも「検証済み」と名乗らない。どちらの枝でも fail-closed。
    """
    from scripts.function_tracer_pcode.authority.contracts import authority_digest

    payload, identity = _sealed_timeout_payload(tmp_path, monkeypatch)
    tampered = copy.deepcopy(payload)
    bundle = tampered["canonical_result_finalization_bundle"]
    # 無関係に見える field を書き換え、digest だけ辻褄を合わせる。
    bundle["execution_payload"] = {"case": "tampered-by-the-test"}
    body = {
        key: value for key, value in bundle.items()
        if key not in {"bundle_digest", "bundle_signature"}
    }
    bundle["bundle_digest"] = authority_digest(body)
    # `bundle_signature` は元のまま = 新しい digest に対しては不正。

    with_key = child_solver_timeout_evidence(
        _status_for(identity), result_payload=tampered,
        bundle_verification_key_id="supervisor-key-v1",
        bundle_verification_key=b"s" * 32,
    )
    assert with_key.confirmed is False
    assert with_key.status == EVIDENCE_INVALID
    assert with_key.detail["validation_error"] == "ValueError"

    without_key = child_solver_timeout_evidence(
        _status_for(identity), result_payload=tampered
    )
    assert without_key.confirmed is False


def test_the_verified_sidecar_wins_over_the_pair_log(tmp_path, monkeypatch):
    """両方あるときは、署名まで検証済みの sidecar を採用する。"""
    payload, identity = _sealed_timeout_payload(tmp_path, monkeypatch)
    sidecar = _sidecar_evidence(
        result_occurrence_id=identity["result_occurrence_id"],
        stream_id=identity["stream_id"],
        source_snapshot_fingerprint=identity["source_snapshot_fingerprint"],
    )
    evidence = child_solver_timeout_evidence(
        _status_for(identity), result_payload=payload, status_sidecar=sidecar,
    )
    assert evidence.status == EVIDENCE_CONFIRMED
    assert evidence.detail["source"] == "diagnostic_status_sidecar"
    assert evidence.detail["verification"] == "supervisor_key_verified"


def test_an_unverified_sidecar_is_not_rescued_by_the_pair_log(tmp_path, monkeypatch):
    """sidecar が「検証できなかった」と言っているなら、log で上書きしない。"""
    payload, identity = _sealed_timeout_payload(tmp_path, monkeypatch)
    sidecar = _sidecar_evidence(
        validated=False, validation_error="ValueError",
        result_occurrence_id=identity["result_occurrence_id"],
        stream_id=identity["stream_id"],
        source_snapshot_fingerprint=identity["source_snapshot_fingerprint"],
    )
    evidence = child_solver_timeout_evidence(
        _status_for(identity), result_payload=payload, status_sidecar=sidecar,
    )
    assert evidence.confirmed is False
    assert evidence.status == EVIDENCE_INVALID
    assert evidence.detail["source"] == "diagnostic_status_sidecar"


def test_an_unsealed_bundle_is_labelled_as_such(real_timeout_payload):
    """封が無い bundle（env 未設定で作ったもの）は digest + replay が全て。"""
    payload, identity = real_timeout_payload
    evidence = child_solver_timeout_evidence(
        _status_for(identity), result_payload=payload
    )
    assert evidence.status == EVIDENCE_CONFIRMED
    assert evidence.detail["verification"] == "unsealed_bundle"


# ---------------------------------------------------------------------------
# 診断 artifact は reporting 専用（semantic authority へ接続しない）
# ---------------------------------------------------------------------------


def test_no_decision_path_reads_the_diagnostic_sidecar_or_the_hotspot_summary():
    """sidecar と hotspot 集計が authority / proof / decision から読まれない。

    sidecar 自体は署名されていない reporting-only artifact なので、判定側から
    読まれていないこと自体が契約になる（PR-124-B の journal と同じ扱い）。
    import 名で固定する。
    """
    import ast
    from pathlib import Path as _Path

    root = _Path(__file__).resolve().parents[2]
    forbidden = {"timeout_hotspot_summary", "read_stack_dump_status"}
    # 判定に関わる層。`authority/process` は sidecar の**書き手**なので除く。
    decision_dirs = ("authority/decision", "authority/domains", "authority/lifecycle",
                     "authority/sites", "proof", "checker", "semantics", "analysis")
    offenders = []
    for directory in decision_dirs:
        for path in (root / directory).rglob("*.py"):
            tree = ast.parse(path.read_text(encoding="utf-8"))
            names = set()
            for node in ast.walk(tree):
                if isinstance(node, ast.ImportFrom) and node.module:
                    names.update(node.module.split("."))
                    names.update(alias.name for alias in node.names)
                elif isinstance(node, ast.Import):
                    for alias in node.names:
                        names.update(alias.name.split("."))
            hit = names & forbidden
            if hit:
                offenders.append((str(path.relative_to(root)), sorted(hit)))
    assert not offenders, offenders


def test_the_hotspot_summary_does_not_import_decision_authority_writers():
    """集計側が judgement を書く面へ触っていない（読むだけ）。"""
    import ast
    from pathlib import Path as _Path

    source = (
        _Path(__file__).resolve().parents[2] / "reporting/timeout_hotspot_summary.py"
    ).read_text(encoding="utf-8")
    imported = set()
    for node in ast.walk(ast.parse(source)):
        if isinstance(node, ast.ImportFrom) and node.module:
            imported.update(alias.name for alias in node.names)
    # 使ってよいのは検証器と読み取りだけ。発行 / finalize 系は使わない。
    assert "validate_canonical_result_finalization_bundle" in imported
    assert not (imported & {
        "build_canonical_result_finalization_bundle",
        "persist_canonical_result_envelope",
        "finalize_decision",
        "attach_canonical_decision",
    }), sorted(imported)
