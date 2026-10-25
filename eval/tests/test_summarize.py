# -*- coding: utf-8 -*-
"""eval/summarize.py の契約（評価計画 v2 PR-D）。

* 完了（COMPLETE）は ``completion`` だけが決める: 検証器の CLOSED・全 execution の fingerprint の
  一致・ledger の full verdict・HEAD の一致・wrapper の記録（終端・破損なし・execution との対応）・
  container が無いことの観測、のすべてのとき。どれかが欠ければ INCOMPLETE（理由と分類付き）、
  読めない・壊れている・観測していないなら UNVERIFIABLE。
* 集計の欄が作れなくても判定は変えず、``report`` は欄の失敗として報告し、exit 2 にする。
* 中断の突き合わせは SIGKILL だけから OOM と書かない（``records.oom_attribution``）。
* 未終端の pair（runner が INCOMPLETE と結論した pair / RUNNING のまま止まった pair）を、
  次の再開が消す前に列挙できる。

tree は PR-B の fixture（本番の writer と署名）、wrapper の記録は本番の wrapper（fake docker）で作る。
"""

from __future__ import annotations

import json
from pathlib import Path

import pytest

import records
import summarize
import wrapper
from harness import Harness
from scripts.function_tracer_pcode.reporting import execution_chain
from scripts.function_tracer_pcode.tests.unit import test_execution_chain as fixture


@pytest.fixture
def h(tmp_path, monkeypatch):
    harness = Harness(tmp_path, monkeypatch)
    yield harness
    try:
        harness.end_container(exit_code=137)
        harness.wait_released(timeout=60)
    except (OSError, ValueError, KeyError, AssertionError):
        pass


def _completion(h, monkeypatch, host=None):
    monkeypatch.setenv("EVAL_HOST_STATE", json.dumps(
        host if host is not None else {"container": "absent", "observed": True}))
    return summarize.completion(wrapper.REPO, h.ev.out, h.ev.wrapper, "neq")


def _codes(result):
    return {item["code"]: item["category"] for item in result["reasons"]}


def test_a_closed_tree_under_the_wrappers_conditions_is_complete(h, monkeypatch):
    h.complete_evaluation()
    result = _completion(h, monkeypatch)
    assert result["verdict"] == summarize.VERDICT_COMPLETE, result["reasons"]
    assert result["verify"]["verdict"] == execution_chain.VERDICT_CLOSED
    assert result["formal"]["full_verdict"] == "full_neq"
    report = summarize.report(wrapper.REPO, h.ev.out, h.ev.wrapper, "neq")
    assert report["verdict"] == result["verdict"] and report["reasons"] == result["reasons"]
    executions = report["census"]["execution_chain"]["executions"]
    assert [e["decided_pairs_attributed"] for e in executions] == [2, 2]
    assert report["raw"]["outcomes"] == {"NOT_EQ": 2, "UNKNOWN": 2}
    assert summarize.exit_code(report) == 0
    text = summarize.format_report(report)
    for heading in ("1. Census", "2. Gates", "3. Formal verdict", "4. Raw totals",
                    "5. NOT_EQ by ground truth", "7. Launches", "VERDICT: COMPLETE"):
        assert heading in text


@pytest.mark.parametrize("case, code, category", [
    ("foreign_fingerprint", "foreign_execution", "blocking"),
    ("open_chain", "chain_open", "resumable"),
    ("ledger_rejects", "no_full_verdict", "resumable"),
    ("container_running", "container_present", "blocking"),
    ("container_unobserved", "container_unobserved", "unverifiable"),
    ("not_head", "head_mismatch", "blocking"),
])
def test_any_missing_condition_keeps_the_evaluation_from_complete(h, monkeypatch, case, code, category):
    options = {}
    if case == "foreign_fingerprint":
        options["fingerprint"] = "eval-env-v1:" + "0" * 64
    if case == "ledger_rejects":
        options["end_overrides"] = {"run_pair_failures": "1"}
    if case == "not_head":
        options["commit"] = "b" * 40
    assert h.start() == wrapper.EXIT_OK
    h.build_tree(**options)
    h.end_container(exit_code=0)
    h.wait_released()
    if case == "open_chain":
        next(h.ev.out.rglob("*.pair-status.json")).unlink()
    host = {"container": "absent", "observed": True}
    if case == "container_running":
        host = {"container": "running", "observed": True}
    if case == "container_unobserved":
        host = {"container": "unobservable", "observed": False}
    result = _completion(h, monkeypatch, host)
    assert _codes(result).get(code) == category, result["reasons"]
    assert result["verdict"] != summarize.VERDICT_COMPLETE


def test_a_verifier_that_cannot_run_is_unverifiable_never_complete(h, monkeypatch):
    h.complete_evaluation()

    def broken(_root):
        raise RuntimeError("disk error")

    monkeypatch.setattr(execution_chain, "verify_execution_chain", broken)
    result = _completion(h, monkeypatch)
    assert result["verdict"] == summarize.VERDICT_UNVERIFIABLE
    assert _codes(result)["verify_failed"] == "unverifiable"


def test_missing_wrapper_meta_is_unverifiable(h, monkeypatch):
    h.complete_evaluation()
    (h.ev.wrapper / records.META).unlink()
    assert _completion(h, monkeypatch)["verdict"] == summarize.VERDICT_UNVERIFIABLE


def test_a_report_section_that_fails_does_not_change_the_verdict_but_fails_the_summary(h, monkeypatch):
    h.complete_evaluation()

    def broken(*_args, **_kwargs):
        raise OSError("unreadable status")

    monkeypatch.setattr(summarize, "raw_aggregate", broken)
    monkeypatch.setenv("EVAL_HOST_STATE", json.dumps({"container": "absent", "observed": True}))
    report = summarize.report(wrapper.REPO, h.ev.out, h.ev.wrapper, "neq")
    assert report["verdict"] == summarize.VERDICT_COMPLETE  # start と同じ判定のまま
    assert any("raw_aggregate" in error for error in report["report_errors"])
    assert summarize.exit_code(report) == 2
    assert "SUMMARY SECTION FAILED" in summarize.format_report(report)


def _receipt(directory: Path, stem: str, **fields) -> None:
    metrics = directory / ".runtime-metrics"
    metrics.mkdir(parents=True, exist_ok=True)
    body = {"run_id": "r" * 32, "execution_nonce": "n" * 24, **fields}
    (metrics / f"{stem}.progress.json").write_text(json.dumps(body))
    if body.get("state") == "COMPLETED":
        (metrics / f"{stem}.runtime.json").write_text(json.dumps(body))


def test_unterminated_pairs_are_listed_by_what_the_runner_recorded(tmp_path):
    out = tmp_path / "out"
    function = out / "S" / "f"
    _receipt(function, "f_N_B1_O_B1", state="COMPLETED", status="INCOMPLETE", child_returncode=-9,
             started_at_epoch=100.0, finished_at_epoch=160.0)
    _receipt(function, "f_N_B1_O_B2", state="RUNNING", status=None, started_at_epoch=150.0)
    _receipt(function, "f_N_B2_O_B2", state="COMPLETED", status="NOT_EQ", child_returncode=1)
    (function / ".runtime-metrics" / "f_N_B1_O_B1.classification-failure.json").write_text(
        json.dumps({"returncode": -9}))
    rows = {row["pair"]: row for row in summarize.unterminated_pairs(out)}
    assert set(rows) == {"S/f/f_N_B1_O_B1.pair-status.json", "S/f/f_N_B1_O_B2.pair-status.json"}
    assert rows["S/f/f_N_B1_O_B1.pair-status.json"]["kind"] == "concluded_incomplete"
    assert rows["S/f/f_N_B1_O_B1.pair-status.json"]["classification_failure"] == {"returncode": -9}
    assert rows["S/f/f_N_B1_O_B2.pair-status.json"]["kind"] == "interrupted_running"


def _launch(pairs, watch=(), oom_killed=False, finished=1000.0):
    return records.Launch(number=1, state=records.STATE_RELEASED,
                          exit={"oom_killed": oom_killed, "finished_at_epoch": finished},
                          evidence={"unterminated_pairs": pairs}, watch=list(watch))


KILLED = {"pair": "p", "kind": "concluded_incomplete", "child_returncode": -9,
          "started_at_epoch": 100.0, "finished_at_epoch": 160.0}


def _obs(at, oom_kill):
    return {"at_epoch": at, "observed": oom_kill is not None, "oom_kill": oom_kill}


def test_sigkill_alone_is_an_external_kill_not_an_oom():
    result = summarize.interruptions([_launch([KILLED], watch=[_obs(50, 0), _obs(400, 0)])])
    assert result["pairs"][0]["cause"] == "external_kill"
    assert result["pairs"][0]["possible_oom"] == records.OOM_NO


def test_an_external_kill_without_observations_is_unobserved_not_no():
    result = summarize.interruptions([_launch([KILLED], watch=[_obs(50, 0), _obs(120, None)])])
    assert result["pairs"][0]["possible_oom"] == records.OOM_UNOBSERVED


def test_a_container_oom_kill_marks_every_unterminated_pair_and_a_stop_is_not_a_kill():
    running = {"pair": "q", "kind": "interrupted_running", "child_returncode": None,
               "started_at_epoch": 100.0, "finished_at_epoch": None}
    assert summarize.interruptions([_launch([running], oom_killed=True)])["pairs"][0][
        "possible_oom"] == records.OOM_YES
    row = summarize.interruptions([_launch([running])])["pairs"][0]
    assert row["cause"] == "execution_stopped" and row["possible_oom"] == "not_applicable"


def test_raw_totals_keep_neq_core_and_unconfirmed_not_eq_apart(tmp_path):
    tree = fixture.ChainTree(tmp_path / "out", scope="FULL_NEQ", pairs=0)
    tree.pairs = [("CLEVER/UnchLoop/Neq/new-old", "foo", "N_B1", "O_B1"),
                  ("CLEVER/UnchLoop/Neq/new-old", "bar", "N_B1", "O_B1"),
                  ("REVE/x/Neq/newV-oldV", "f", "N_B1", "O_B1")]
    run = fixture._run_id(1)
    tree.start(run)
    for pair in tree.pairs:
        tree.decide(run, pair, outcome="NOT_EQ")
    raw = summarize.raw_aggregate(tree.root, "neq", None)
    assert raw["outcomes"] == {"NOT_EQ": 3}
    assert raw["neq_core"]["pairs"] == 2 and raw["neq_core"]["functions"] == 2
    # ground truth（function_diff_manifest.json）の無い Neq の NOT_EQ は確認済みに数えない。
    assert raw["not_eq_by_ground_truth"] == {"unconfirmed": 3}
