# -*- coding: utf-8 -*-
"""eval/summarize.py の契約（評価計画 v2 PR-D）。

* 完了（COMPLETE）は、検証器の CLOSED・全 execution の fingerprint の一致・ledger の full
  verdict・HEAD の一致・wrapper の記録の欠損なし・container なし、のすべてのときだけ。
  どれか 1 つでも欠ければ INCOMPLETE（理由付き）、検証器が動かなければ UNVERIFIABLE。
* 中断の突き合わせは SIGKILL だけから OOM と書かない。cgroup の ``oom_kill`` の増分が
  その pair の実行区間に重なるとき（または container 自体の OOMKilled）だけ ``possible_oom``。
* 未終端の pair（runner が INCOMPLETE と結論した pair / RUNNING のまま止まった pair）を、
  次の再開が消す前に列挙できる。

tree は PR-B の fixture（本番の writer と署名）で作る。
"""

from __future__ import annotations

import json
from pathlib import Path
import subprocess

import pytest

import summarize
from scripts.function_tracer_pcode.reporting import execution_chain
from scripts.function_tracer_pcode.tests.unit import test_execution_chain as fixture

FINGERPRINT = "eval-env-v1:" + "e" * 64


def _git_repo(path: Path) -> str:
    path.mkdir()
    for args in (["init", "-q"], ["config", "user.email", "t@example.com"],
                 ["config", "user.name", "t"]):
        subprocess.run(["git", "-C", str(path), *args], check=True)
    (path / "README").write_text("x\n")
    subprocess.run(["git", "-C", str(path), "add", "README"], check=True)
    subprocess.run(["git", "-C", str(path), "commit", "-q", "-m", "x"], check=True)
    return subprocess.run(["git", "-C", str(path), "rev-parse", "HEAD"], check=True,
                          capture_output=True, text=True).stdout.strip()


@pytest.fixture
def repo(tmp_path):
    """HEAD の一致を判定させる、SOURCE_ROOTS の汚れの無い git repo。"""
    path = tmp_path / "repo"
    return path, _git_repo(path)


def _tree(tmp_path, commit, *, fingerprints=(FINGERPRINT, FINGERPRINT), scope="FULL_NEQ"):
    """2 execution（1 回目は kill、2 回目が再開して封印）の FULL tree。"""
    tree = fixture.ChainTree(tmp_path / "logs" / "eval_x_neq", scope=scope)
    e1, e2 = fixture._run_id(1), fixture._run_id(2)
    tree.start(e1, environment_fingerprint=fingerprints[0], git_commit=commit, git_dirty="0")
    for pair in tree.pairs[:2]:
        tree.decide(e1, pair)
    tree.leave_incomplete(e1, tree.pairs[2])
    tree.start(e2, environment_fingerprint=fingerprints[1], git_commit=commit, git_dirty="0")
    for pair in tree.pairs[2:]:
        tree.decide(e2, pair, outcome="NOT_EQ")
    tree.finish(e2, reused=tree.pairs[:2])
    return tree


def _wrapper(tmp_path, *, launches=1, gaps=()):
    wrapper = tmp_path / "logs" / "eval_x_neq.wrapper"
    (wrapper / "launches").mkdir(parents=True)
    (wrapper / "meta.json").write_text(json.dumps({
        "schema": "eval-wrapper-meta-v1", "fingerprint": FINGERPRINT,
        "conditions": {"freeze_commit": "c" * 40}}))
    for number in range(1, launches + 1):
        directory = wrapper / "launches" / str(number)
        directory.mkdir()
        (directory / "launch.json").write_text(json.dumps({"launch": number, "kind": "first"}))
        if "exit" not in gaps:
            (directory / "exit.json").write_text(json.dumps({"exit_code": 0, "oom_killed": False}))
        if "evidence" not in gaps:
            (directory / "evidence.json").write_text(json.dumps({"unterminated_pairs": []}))
        if "log" not in gaps:
            (directory / "runner.log").write_text("ok\n")
    return wrapper


def _report(repo_path, tree, wrapper, monkeypatch, host=None):
    monkeypatch.setenv("EVAL_HOST_STATE", json.dumps(host or {"container": "absent"}))
    return summarize.report(repo_path, tree.root, wrapper, "neq")


def test_a_closed_tree_under_the_wrappers_conditions_is_complete(tmp_path, repo, monkeypatch):
    repo_path, commit = repo
    tree = _tree(tmp_path, commit)
    result = _report(repo_path, tree, _wrapper(tmp_path), monkeypatch)
    assert result["gates"]["execution_chain"]["verdict"] == execution_chain.VERDICT_CLOSED
    assert result["formal"]["full_verdict"] == "full_neq"
    assert result["verdict"] == summarize.VERDICT_COMPLETE, result["verdict_reasons"]
    assert [e["decided_pairs_attributed"] for e in result["census"]["execution_chain"]["executions"]] == [2, 2]
    assert result["raw"]["outcomes"] == {"NOT_EQ": 2, "UNKNOWN": 2}
    text = summarize.format_report(result)
    for heading in ("1. Census", "2. Gates", "3. Formal verdict", "4. Raw totals",
                    "5. NOT_EQ by ground truth", "VERDICT: COMPLETE"):
        assert heading in text


@pytest.mark.parametrize("case", ("foreign_fingerprint", "open_chain", "wrapper_gap",
                                  "container_running", "not_head"))
def test_any_missing_condition_keeps_the_evaluation_incomplete(tmp_path, repo, monkeypatch, case):
    repo_path, commit = repo
    fingerprints = (FINGERPRINT, FINGERPRINT)
    if case == "foreign_fingerprint":
        fingerprints = ("eval-env-v1:" + "0" * 64, FINGERPRINT)
    tree = _tree(tmp_path, commit if case != "not_head" else "b" * 40, fingerprints=fingerprints)
    if case == "open_chain":
        (tree.root / tree.relative(tree.pairs[0])).unlink()
    wrapper = _wrapper(tmp_path, gaps=("evidence",) if case == "wrapper_gap" else ())
    host = {"container": "running"} if case == "container_running" else None
    result = _report(repo_path, tree, wrapper, monkeypatch, host)
    assert result["verdict"] == summarize.VERDICT_INCOMPLETE
    expected = {
        "foreign_fingerprint": "did not run under this wrapper's conditions",
        "open_chain": "execution chain is OPEN",
        "wrapper_gap": "no post-run evidence",
        "container_running": "an evaluation container is running",
        "not_head": "not evidence about the code at HEAD",
    }[case]
    assert any(expected in reason for reason in result["verdict_reasons"]), result["verdict_reasons"]


def test_a_verifier_that_cannot_run_is_unverifiable_never_complete(tmp_path, repo, monkeypatch):
    repo_path, commit = repo
    tree = _tree(tmp_path, commit)

    def broken(_root):
        raise RuntimeError("disk error")

    monkeypatch.setattr(execution_chain, "verify_execution_chain", broken)
    result = _report(repo_path, tree, _wrapper(tmp_path), monkeypatch)
    assert result["verdict"] == summarize.VERDICT_UNVERIFIABLE
    assert summarize.EXIT_BY_VERDICT[result["verdict"]] == 2


def test_missing_wrapper_meta_is_unverifiable(tmp_path, repo, monkeypatch):
    repo_path, commit = repo
    tree = _tree(tmp_path, commit)
    wrapper = _wrapper(tmp_path)
    (wrapper / "meta.json").unlink()
    assert _report(repo_path, tree, wrapper, monkeypatch)["verdict"] == summarize.VERDICT_UNVERIFIABLE


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
    return {"launch": 1, "exit": {"oom_killed": oom_killed, "finished_at_epoch": finished},
            "evidence": {"unterminated_pairs": pairs}, "watch": list(watch)}


KILLED = {"pair": "p", "kind": "concluded_incomplete", "child_returncode": -9,
          "started_at_epoch": 100.0, "finished_at_epoch": 160.0}


def test_sigkill_alone_is_an_external_kill_not_an_oom():
    result = summarize.interruptions([_launch([KILLED], watch=[
        {"at_epoch": 50.0, "oom_kill_delta": 0}, {"at_epoch": 400.0, "oom_kill_delta": 0}])])
    assert result["pairs"][0]["cause"] == "external_kill"
    assert result["pairs"][0]["possible_oom"] is False
    assert result["totals"].get("possible_oom", 0) == 0


def test_an_oom_kill_increment_during_the_pair_marks_a_possible_oom():
    watch = [{"at_epoch": 150.0, "oom_kill_delta": 0}, {"at_epoch": 160.0, "oom_kill_delta": 1}]
    result = summarize.interruptions([_launch([KILLED], watch=watch)])
    assert result["pairs"][0]["possible_oom"] is True
    # 同じ増分でも、pair の区間から外れていれば OOM と結び付けない。
    late = [{"at_epoch": 900.0, "oom_kill_delta": 0}, {"at_epoch": 910.0, "oom_kill_delta": 1}]
    assert summarize.interruptions([_launch([KILLED], watch=late)])["pairs"][0]["possible_oom"] is False


def test_a_container_oom_kill_marks_every_unterminated_pair_and_a_stop_is_not_a_kill():
    running = {"pair": "q", "kind": "interrupted_running", "child_returncode": None,
               "started_at_epoch": 100.0, "finished_at_epoch": None}
    result = summarize.interruptions([_launch([running], oom_killed=True)])
    assert result["pairs"][0] == {**result["pairs"][0], "cause": "execution_stopped",
                                  "possible_oom": True}
    assert summarize.interruptions([_launch([running])])["pairs"][0]["possible_oom"] is False


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


def test_any_reader_that_fails_makes_the_summary_unverifiable(tmp_path, repo, monkeypatch):
    repo_path, commit = repo
    tree = _tree(tmp_path, commit)

    def broken(*_args, **_kwargs):
        raise OSError("unreadable status")

    monkeypatch.setattr(summarize, "raw_aggregate", broken)
    result = _report(repo_path, tree, _wrapper(tmp_path), monkeypatch)
    assert result["verdict"] == summarize.VERDICT_UNVERIFIABLE
    assert any("raw_aggregate failed" in reason for reason in result["verdict_reasons"])
