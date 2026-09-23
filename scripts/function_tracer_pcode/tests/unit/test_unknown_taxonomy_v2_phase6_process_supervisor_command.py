# -*- coding: utf-8 -*-
"""Issue #163: process supervisor の end-to-end 契約（実 child process）。

どの test も「実 worker child → production supervisor → durable store /
projection → production の ``classify_pair_status``」を通す。child・
supervisor・分類器のどれも mock しない。起動・鍵・identity・停止点は
``_supervisor_support`` の harness が持ち、ここは期待だけを書く。

固定している契約:

* launch-before-exec: child が本処理に入る時点で ``launch.json`` が durable で、
  それが child 自身の PID / start token を名指している（child 側で検証）。
  parent 側では child の観測・``launch.json``・projection の digest が一致する。
* canonical 結果の無い child 終了は ERROR（``EXIT_CODE_<rc>``）として分類が
  valid になる。runner の mode（``--allow-child-exit-resolution``）では
  RESOLVED にせず INVALID に倒す。
* checkpoint 無しの deadline は rc 124 / TIMEOUT / disposition を持ち、分類は
  TIMEOUT valid。
* child が production 経路で出した canonical TIMEOUT を supervisor は
  RESOLVED（``SupervisorCanonicalResultResolvedReceipt``）として受け、分類は
  TIMEOUT valid。envelope・resolved receipt・分類の digest が一致し、
  worker 鍵で署名された ``SOLVER_TIMEOUT`` が 1 件ある。UNKNOWN で代用しない。
* canonical UNKNOWN は同じ経路で UNKNOWN（positive control）。
* 封の壊れた envelope は exit 2 / INVALID で、分類も restart も fail-closed。
* start token は ``/proc/<pid>/stat`` の開始時刻に束縛される。
"""

from __future__ import annotations

import hashlib
import json
import os

import pytest

from scripts.function_tracer_pcode.authority.contracts import (
    CLI_EXIT_CODE_BY_OUTCOME,
    Outcome,
    authority_digest,
)
from scripts.function_tracer_pcode.authority.process.supervisor_command import (
    read_process_start_token,
)
from scripts.function_tracer_pcode.tests.unit._supervisor_support import (
    Checkpoint,
    ChildScript,
    Deadline,
    Envelope,
    Exit,
    Stop,
    classify,
    restart_supervisor,
    run_supervisor,
    supervisor_case,
)

RESOLVED_KIND = "SupervisorCanonicalResultResolvedReceipt"


def _launch(case):
    return json.loads((case.store_directory / "launch.json").read_text(encoding="utf-8"))


def _envelope(case):
    return json.loads(
        (case.store_directory / "canonical-result-envelope.json").read_text(encoding="utf-8")
    )


def _envelope_is_sealed(envelope):
    body = {key: value for key, value in envelope.items() if key != "envelope_digest"}
    return authority_digest(body) == envelope["envelope_digest"]


def _solver_timeout_events(bundle):
    return [
        event for event in bundle["sealed_event_stream"]["payload"]["events"]
        if event["header"]["event_type"] == "SOLVER_TIMEOUT"
    ]


def _assert_child_ran_under_this_launch(case, run):
    """実 child が起動し、本処理の前に自分を名指す durable launch を見た。

    parent 側では、supervisor が barrier を解放した瞬間に launch が既に durable
    だったことを観測している（child の起動速度に依存しない順序の証拠）。
    """

    launch = _launch(case)
    assert run.launch_durable_at_barrier_release is True
    evidence = run.launch_evidence
    assert evidence is not None, "worker child never reached its launch check"
    assert evidence["pid"] == launch["payload"]["child_pid"] != os.getpid()
    assert evidence["start_token"] == launch["payload"]["child_start_token"]
    assert evidence["launch_receipt_digest"] == launch["receipt_digest"]
    assert evidence["launch_sha256"] == hashlib.sha256(
        (case.store_directory / "launch.json").read_bytes()
    ).hexdigest()
    assert run.projection["launch_receipt_digest"] == launch["receipt_digest"]
    return launch


def test_process_start_token_is_bound_to_current_linux_process():
    token = read_process_start_token(os.getpid())
    assert token.startswith("linux-proc-starttime-")
    assert token.removeprefix("linux-proc-starttime-").isascii()
    assert token.removeprefix("linux-proc-starttime-").isdecimal()


def test_launch_is_durable_before_the_child_body_and_bundleless_exit_is_error(tmp_path):
    with supervisor_case(tmp_path, ChildScript((Exit(3),))) as case:
        run = run_supervisor(case)
        launch = _assert_child_ran_under_this_launch(case, run)
        # child は checkpoint を 1 つも持たない状態で起動した。
        assert run.launch_evidence["state_present_at_start"] is False

        assert run.exit_code == 3
        assert run.projection["status"] == "ERROR"
        assert run.projection["authority_kind"] == "DurableErrorFinalizationBundle"
        assert run.projection["child_exit_disposition"] == "EXIT_CODE_3"
        assert run.projection["child_returncode"] == 3
        classified = classify(case)
        assert classified["canonical_outcome"] == "ERROR"
        assert classified["classification_valid"] is True
        assert classified["error_kind"] == "operational_authority_invalid"
        assert classified["child_exit_disposition"] == "EXIT_CODE_3"
        assert classified["launch_receipt_digest"] == launch["receipt_digest"]
        assert classified["finalization_bundle_digest"] == (
            run.projection["finalization_bundle_digest"]
        )


def test_runner_mode_does_not_resolve_a_child_exit_without_a_canonical_result(tmp_path):
    with supervisor_case(
        tmp_path, ChildScript((Exit(0),)), allow_child_exit_resolution=True,
    ) as case:
        run = run_supervisor(case)
        _assert_child_ran_under_this_launch(case, run)
        assert run.exit_code == 2
        assert run.projection["status"] == "INVALID"
        assert run.projection["error_code"] == "CANONICAL_CHILD_RESULT_INVALID"
        assert run.projection["child_returncode"] == 0
        assert not run.store.has("canonical-resolved-receipt.json")
        with pytest.raises(ValueError, match="not a terminal authority"):
            classify(case)


@pytest.mark.parametrize(
    ("ignore_sigterm", "kill_grace", "disposition", "returncode"),
    (
        # SIGTERM で終わる child を grace 内に待つ。grace は上限で、child が
        # 終われば即座に戻るので、負荷下で SIGKILL へ落ちない長さにする。
        (False, 30.0, "SIGTERM_AFTER_DEADLINE", -15),
        # SIGTERM を無視する child は grace を使い切って SIGKILL になる。
        (True, 0.5, "SIGKILL_AFTER_DEADLINE", -9),
    ),
)
def test_deadline_without_a_checkpoint_is_a_durable_timeout(
    tmp_path, ignore_sigterm, kill_grace, disposition, returncode,
):
    script = ChildScript((Stop(ignore_sigterm=ignore_sigterm),))
    with supervisor_case(tmp_path, script, kill_grace=kill_grace) as case:
        run = run_supervisor(case, deadline=Deadline.AT_CHILD_STOP)
        launch = _assert_child_ran_under_this_launch(case, run)
        # deadline は child が止まった後に来て、その時点で checkpoint は無い。
        assert run.store_at_child_stop is not None
        assert run.store_at_child_stop.files == {"launch.json"}

        assert run.exit_code == 124
        assert run.projection["status"] == "TIMEOUT"
        assert run.projection["authority_kind"] == "DurableTimeoutFinalizationBundle"
        assert run.projection["child_exit_disposition"] == disposition
        assert run.projection["child_returncode"] == returncode
        classified = classify(case)
        assert classified["canonical_outcome"] == "TIMEOUT"
        assert classified["classification_valid"] is True
        assert classified["supervisor_status"] == "TIMEOUT"
        assert classified["child_exit_disposition"] == disposition
        assert classified["launch_receipt_digest"] == launch["receipt_digest"]
        assert classified["finalization_bundle_digest"] == (
            run.projection["finalization_bundle_digest"]
        )


def _canonical_case(tmp_path, outcome, *, corrupt=None, reseal=False):
    script = ChildScript((
        Checkpoint(), Envelope(outcome, corrupt=corrupt, reseal=reseal), Exit(),
    ))
    return supervisor_case(tmp_path, script, allow_child_exit_resolution=True)


def test_child_canonical_timeout_is_resolved_by_the_supervisor_and_classified_timeout(
    tmp_path,
):
    with _canonical_case(tmp_path, "TIMEOUT") as case:
        run = run_supervisor(case)
        launch = _assert_child_ran_under_this_launch(case, run)
        # child は decompile checkpoint を閉じてから結果を出した。
        assert run.store.state == "RESOLVED"

        timeout_code = CLI_EXIT_CODE_BY_OUTCOME[Outcome.TIMEOUT]
        assert run.exit_code == 0
        projection = run.projection
        assert projection["status"] == "RESOLVED"
        assert projection["authority_kind"] == RESOLVED_KIND
        assert projection["supervisor_authority_kind"] == RESOLVED_KIND
        assert projection["canonical_outcome"] == "TIMEOUT"
        assert projection["child_returncode"] == timeout_code

        classified = classify(case)
        assert classified["canonical_outcome"] == "TIMEOUT"
        assert classified["classification_valid"] is True
        assert classified["supervisor_status"] == "RESOLVED"
        assert classified["authority_kind"] == RESOLVED_KIND

        # envelope（child）/ resolved receipt（supervisor）/ 分類の digest が一致する。
        envelope = _envelope(case)
        assert _envelope_is_sealed(envelope)
        bundle = envelope["canonical_result_payload"]["canonical_result_finalization_bundle"]
        decision = bundle["decision_receipt"]["payload"]
        assert decision["outcome"] == "TIMEOUT"
        receipt = json.loads(
            (case.store_directory / "canonical-resolved-receipt.json").read_text(encoding="utf-8")
        )
        assert receipt["launch_receipt_digest"] == launch["receipt_digest"]
        assert receipt["child_returncode"] == timeout_code
        assert receipt["canonical_result_bundle_digest"] == bundle["bundle_digest"]
        assert receipt["decision_receipt_digest"] == decision["receipt_digest"]
        for key, value in (
            ("canonical_result_bundle_digest", envelope["canonical_result_bundle_digest"]),
            ("decision_receipt_digest", decision["receipt_digest"]),
            ("supervisor_final_authority_digest", receipt["receipt_digest"]),
        ):
            assert projection[key] == classified[key] == value, key
        # 分類器は pair log の結果 JSON と envelope を突き合わせた（log に結果がある）。
        assert "=== EQUIVALENCE_RESULT_JSON_BEGIN ===" in case.pair_log.read_text(
            encoding="utf-8"
        )

        # TIMEOUT の根拠は worker が署名した solver timeout 1 件（UNKNOWN の代用でない）。
        solver_timeouts = _solver_timeout_events(bundle)
        assert len(solver_timeouts) == 1
        assert solver_timeouts[0]["authority_payload"]["execution_receipt_authority"][
            "signing_key_id"
        ] == case.keys.worker_key_id
        selection = bundle["terminal_timeout_candidate_selection_receipt"]
        assert selection["producer_attempt_ordinal"] == 1


def test_child_canonical_unknown_is_resolved_and_classified_unknown(tmp_path):
    """positive control: 同じ経路で UNKNOWN は UNKNOWN のまま届く。"""

    with _canonical_case(tmp_path, "UNKNOWN") as case:
        run = run_supervisor(case)
        _assert_child_ran_under_this_launch(case, run)
        assert run.exit_code == 0
        assert run.projection["status"] == "RESOLVED"
        assert run.projection["authority_kind"] == RESOLVED_KIND
        assert run.projection["canonical_outcome"] == "UNKNOWN"
        assert run.projection["child_returncode"] == CLI_EXIT_CODE_BY_OUTCOME[Outcome.UNKNOWN]
        classified = classify(case)
        assert classified["canonical_outcome"] == "UNKNOWN"
        assert classified["classification_valid"] is True
        bundle = _envelope(case)["canonical_result_payload"][
            "canonical_result_finalization_bundle"
        ]
        assert classified["canonical_result_bundle_digest"] == bundle["bundle_digest"]
        assert _solver_timeout_events(bundle) == []


@pytest.mark.parametrize(
    ("field", "reseal"),
    (
        # 封だけが壊れる（bundle との join は正しい）: 封の検査だけが拒否の根拠。
        ("envelope_digest", False),
        # 封は正しく付け直す（bundle digest だけが食い違う）: join の検査だけが根拠。
        ("canonical_result_bundle_digest", True),
    ),
    ids=("seal-only", "bundle-join-only"),
)
def test_corrupt_canonical_envelope_fails_closed(tmp_path, field, reseal):
    """control と 1 文字だけ違う envelope は RESOLVED にならず、分類も通らない。"""

    with _canonical_case(tmp_path, "UNKNOWN", corrupt=field, reseal=reseal) as case:
        run = run_supervisor(case)
        _assert_child_ran_under_this_launch(case, run)
        envelope = _envelope(case)
        assert _envelope_is_sealed(envelope) is reseal
        bundle = envelope["canonical_result_payload"]["canonical_result_finalization_bundle"]
        assert (bundle["bundle_digest"] == envelope["canonical_result_bundle_digest"]) is (
            not reseal
        )

        assert run.exit_code == 2
        assert run.projection["status"] == "INVALID"
        assert run.projection["authority_kind"] == "InvalidSupervisorCommandProjection"
        assert run.projection["error_code"] == "CANONICAL_CHILD_RESULT_INVALID"
        assert not run.store.has("canonical-resolved-receipt.json")
        with pytest.raises(ValueError, match="not a terminal authority"):
            classify(case)

        # restart しても壊れた envelope は canonical RESOLVED にならず、分類も
        # 通らない。restart が projection に何を書くか（decompile checkpoint の
        # RESOLVED を pair の RESOLVED と読む既存不整合）は #165 が扱うので、
        # ここでは固定しない。
        restarted = restart_supervisor(case)
        assert not restarted.store.has("canonical-resolved-receipt.json")
        assert restarted.projection["authority_kind"] != RESOLVED_KIND
        with pytest.raises(
            ValueError, match="canonical result envelope|not a terminal authority",
        ):
            classify(case)
