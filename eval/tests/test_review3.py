# -*- coding: utf-8 -*-
"""PR #278 review 3: 再開してよいかの判定は、どの経路でも省略できない（評価計画 v2 PR-D）。

運用契約: permanent が 1 件でもあれば、他の理由や出力の状態（無い・空・開始前・開始後）に
よらず、元の評価の ``start`` は何も書かずに拒否し（退避も launch も container の起動もしない）、
記録を残して別の ``--tag`` の評価を案内する。正常な開始前の中断（runner が開始の記録の前に
止まった出力）は、証拠を残したまま退避して再開できる。退避で確定した記録の欠損・破損や、
launch と execution の対応の食い違いを隠さない。

本番の wrapper（fake docker）と、永続化された記録で確かめる。
"""

from __future__ import annotations

import json
import os
from pathlib import Path
import signal

import pytest

import protocol
import records
import wrapper
from harness import Harness
from test_review2 import _execution


@pytest.fixture
def h(tmp_path, monkeypatch):
    harness = Harness(tmp_path, monkeypatch)
    yield harness
    try:
        harness.update(lambda d: d.update({"fail": {}, "respond": {}}))
        harness.end_container(exit_code=137)
        harness.wait_released(timeout=60)
    except (OSError, ValueError, KeyError, AssertionError):
        pass


def _preparation_files(h):
    """runner が manifest と開始の記録の前に書く準備の file（census・関数選択）。"""
    (h.ev.out / "CLEVER" / "LoopSub" / "Neq" / "new-old").mkdir(parents=True)
    (h.ev.out / "neq_source_pairs.tsv").write_text("CLEVER/LoopSub/Neq/new-old\tx\ty\n")
    (h.ev.out / "CLEVER" / "LoopSub" / "Neq" / "new-old" / "functions.txt").write_text("foo\n")


def _kill_supervisor(h):
    pid = (wrapper.lock_holders(h.ev) or [None])[0]
    os.kill(pid, signal.SIGKILL)
    h.wait_for(lambda: wrapper.lock_holders(h.ev) is None, message="the lock")


def _refused_without_anything(h, capsys, *, launches):
    before = h.snapshot()
    calls = len(h.read_state().get("calls", []))
    out_state = records.output_state(h.ev.out)
    assert h.start() == wrapper.EXIT_REFUSED
    err = capsys.readouterr().err
    assert h.snapshot() == before, "the output and the wrapper records must not change"
    assert not [c for c in h.read_state().get("calls", [])[calls:] if c[:2] == ["run", "-d"]]
    assert len(h.records().launches) == launches
    assert records.output_state(h.ev.out) == out_state
    assert not (h.ev.wrapper / "aborted-outputs").exists() or len(
        list((h.ev.wrapper / "aborted-outputs").iterdir())) == 0
    return err


# ---------------------------------------------------------------------------
# permanent は出力の状態によらず拒否する
# ---------------------------------------------------------------------------


@pytest.mark.parametrize("output", ["absent", "empty", "never_started", "started"])
def test_a_container_removed_outside_refuses_the_start_whatever_the_output(h, capsys, output):
    """review 3 の時系列: container を記録 → runner が準備の file を作る → manifest・開始の記録の
    前に container が外部で消される → stop が exit_unobserved を確定 → 次の start。"""
    assert h.start() == wrapper.EXIT_OK
    if output == "empty":
        h.ev.out.mkdir(parents=True)
    elif output == "never_started":
        _preparation_files(h)
    elif output == "started":
        _execution(h, "a" * 32)
    _kill_supervisor(h)
    h.remove_containers()
    assert h.run("stop") == wrapper.EXIT_OK
    (launch,) = h.records().launches
    assert launch.exit_kind == records.KIND_EXIT_UNOBSERVED and launch.terminal
    assert records.output_state(h.ev.out) == output
    err = _refused_without_anything(h, capsys, launches=1)
    assert "separate evaluation (another --tag)" in err and "exit_unobserved" in err


@pytest.mark.parametrize("output", ["absent", "never_started", "started"])
def test_a_launch_that_ran_without_a_container_record_is_not_called_not_started(h, capsys, output):
    """container の記録の前に supervisor が止まり、container は動いて外部で消された（出力が変わった）。"""
    mark = h.tmp / "crash.mark"
    h.cli("start", extra_env={"EVAL_TEST_CRASH": "start:supervise:before",
                              "EVAL_TEST_CRASH_MARK": str(mark)})
    assert mark.exists()
    if output == "never_started":
        _preparation_files(h)  # 記録されなかった container が書いた
    elif output == "started":
        _execution(h, "b" * 32)
    assert h.run("stop") == wrapper.EXIT_OK
    (launch,) = h.records().launches
    expected = records.KIND_NOT_STARTED if output == "absent" else records.KIND_EXIT_UNOBSERVED
    assert launch.exit_kind == expected, launch.exit
    if expected == records.KIND_EXIT_UNOBSERVED:
        _refused_without_anything(h, capsys, launches=1)
    else:
        assert h.start() == wrapper.EXIT_OK  # 本当に作られなかった launch は再試行できる


# ---------------------------------------------------------------------------
# 正常な開始前の中断は、証拠を残して退避・再開できる
# ---------------------------------------------------------------------------


def test_a_runner_killed_before_its_start_record_is_moved_aside_and_resumed(h, capsys):
    assert h.start() == wrapper.EXIT_OK
    _preparation_files(h)
    # 書きかけの開始の記録だけの execution の dir（開始の記録の確定の前に止まった）。
    debris = h.ev.out / ".executions" / ("c" * 32)
    debris.mkdir(parents=True)
    (debris / ".run_manifest.start.txt.uncommitted-abc").write_text("partial")
    h.end_container(exit_code=137)  # docker kill
    h.wait_released()
    (first,) = h.records().launches
    assert first.exit_kind == records.KIND_RAN and first.exit["runtime_run_ids"] == []
    assert records.output_state(h.ev.out) == "never_started"
    assert h.start() == wrapper.EXIT_OK
    launch2 = json.loads((h.ev.launch_dir(2) / records.LAUNCH).read_text())
    aside = Path(launch2["moved_aside_output"])
    assert (aside / "neq_source_pairs.tsv").exists() and (aside / ".executions" / ("c" * 32)).is_dir()
    assert not h.ev.out.exists()
    h.end_container(exit_code=0)
    h.wait_released()
    check = h.records()
    assert not check.problems
    assert records.attribution_problems(check, records.started_executions(h.ev.out)) == []
    assert (h.ev.launch_dir(1) / records.EVIDENCE).exists()  # 1 回目の証拠は残る
    capsys.readouterr()
    h.run("summary", "--json")
    result = json.loads(capsys.readouterr().out)
    assert result["verdict"] != "UNVERIFIABLE", result["reasons"]


def test_a_launch_whose_docker_run_failed_keeps_the_output_and_the_next_start_moves_it(h):
    assert h.start() == wrapper.EXIT_OK
    _preparation_files(h)
    h.end_container(exit_code=137)
    h.wait_released()
    h.fail("run-d", 1)
    h.start()
    h.wait_released()
    second = h.records().launches[1]
    # 2 回目の start は判定の後に開始前の出力を退避してから launch を要求し、docker run が失敗した。
    # 出力は要求の時点（退避の後）のままなので「作られなかった」と記録し、再試行できる。
    assert second.launch["moved_aside_output"]
    assert second.exit_kind == records.KIND_NOT_STARTED
    assert records.output_state(h.ev.out) == "absent"
    assert h.start() == wrapper.EXIT_OK
    third = json.loads((h.ev.launch_dir(3) / records.LAUNCH).read_text())
    assert third["moved_aside_output"] is None
    assert len(list((h.ev.wrapper / "aborted-outputs").iterdir())) == 1  # 証拠は 1 つ残っている


# ---------------------------------------------------------------------------
# 退避で破損を隠さない
# ---------------------------------------------------------------------------


@pytest.mark.parametrize("damage", ["evidence_deleted", "start_record_deleted"])
def test_damage_is_not_hidden_by_moving_the_output_aside(h, capsys, damage):
    assert h.start() == wrapper.EXIT_OK
    _execution(h, "d" * 32)
    h.end_container(exit_code=137)
    h.wait_released()
    if damage == "evidence_deleted":
        (h.ev.launch_dir(1) / records.EVIDENCE).unlink()
        _preparation_files(h)
        (h.ev.out / "run_manifest.txt").unlink()
        (h.ev.out / ".executions" / ("d" * 32) / "run_manifest.start.txt").unlink()
    else:
        # launch が記録した execution の開始の記録と manifest を消す: 出力は「開始前」に見える。
        (h.ev.out / "run_manifest.txt").unlink()
        (h.ev.out / ".executions" / ("d" * 32) / "run_manifest.start.txt").unlink()
    assert records.output_state(h.ev.out) == "never_started"
    err = _refused_without_anything(h, capsys, launches=1)
    assert "cannot be judged" in err


# ---------------------------------------------------------------------------
# 判定は省略できない
# ---------------------------------------------------------------------------


def test_the_start_decision_refuses_a_missing_or_partial_judgement():
    assert protocol.start_decision(None)[0] == protocol.DECISION_REFUSE
    partial = {"schema": protocol.COMPLETION_SCHEMA, "verdict": "INCOMPLETE",
               "reasons": [{"code": "output_never_started", "category": "resumable", "detail": "x"}],
               "output_state": "never_started"}
    assert protocol.start_decision(partial)[0] == protocol.DECISION_REFUSE


@pytest.mark.parametrize("dropped", protocol.MANDATORY_CHECKS)
def test_a_completion_without_a_mandatory_check_cannot_start_anything(h, capsys, dropped):
    h.finished_launch()
    _preparation_files(h)
    h.update(lambda d: d.setdefault("respond", {}).update({"completion": {
        "times": 1, "drop_check": dropped}}))
    err = _refused_without_anything(h, capsys, launches=1)
    assert "cannot judge the evaluation" in err


def test_the_first_start_goes_through_the_same_judgement(h):
    assert h.start() == wrapper.EXIT_OK
    readers = [c for c in h.read_state()["calls"] if c[:2] == ["run", "--rm"]
               and "completion" in c]
    assert len(readers) == 1, "the first start must be judged by completion too"
    launch = json.loads((h.ev.launch_dir(1) / records.LAUNCH).read_text())
    assert [r["code"] for r in launch["completion_before"]["reasons"]] == [
        "evaluation_not_started", "output_absent"]


def test_an_output_started_from_another_analysis_source_refuses_the_start(h, capsys):
    assert h.start() == wrapper.EXIT_OK
    directory = h.ev.out / ".executions" / ("e" * 32)
    directory.mkdir(parents=True)
    text = (f"runtime_run_id={'e' * 32}\nenvironment_fingerprint={h.meta()['fingerprint']}\n"
            f"analysis_source_digest_start={'0' * 64}\n")
    (h.ev.out / "run_manifest.txt").write_text(text)
    (directory / "run_manifest.start.txt").write_text(text)
    h.end_container(exit_code=0)
    h.wait_released()
    err = _refused_without_anything(h, capsys, launches=1)
    assert "source_differs" in err and "separate evaluation (another --tag)" in err
