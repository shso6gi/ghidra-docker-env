# -*- coding: utf-8 -*-
"""PR #278 review 1 の 4 指摘の regression（CLI と記録の file だけで確かめる）。

旧実装（aca0a3cd）でも同じ harness で動く形にしてあり、旧実装ではすべて落ちる（PR 本文に記録）。

* P1-1: chain が CLOSED でも ledger が正式性を拒否する tree で、start が「完了済み」にしない
* P1-2: 起動の要求の確定後・supervisor の起動前に止まった launch を、stop が回収する。
  launch の dir ごとの欠損を、summary が判定不能として報告する
* P1-3: docker logs の失敗の出力を runner.log として保存せず、container を消さない
* P2: OOM の増分を、直前の保存行ではなく直前の有効な観測からの区間に結び付ける
"""

from __future__ import annotations

import json
import shutil
import time

import pytest

import wrapper
from harness import Harness


@pytest.fixture
def h(tmp_path, monkeypatch):
    harness = Harness(tmp_path, monkeypatch)
    yield harness
    try:
        harness.update(lambda d: d.update({"fail": {}}))
        harness.end_container(exit_code=137)
        harness.wait_released(timeout=60)
    except (OSError, ValueError, KeyError, AssertionError):
        pass


def test_p1_1_a_closed_chain_the_ledger_rejects_is_not_reported_complete(h, capsys):
    h.complete_evaluation(end_overrides={"run_pair_failures": "1"})
    launched = len(h.detached_runs())
    capsys.readouterr()
    assert h.start() == wrapper.EXIT_OK
    assert len(h.detached_runs()) == launched + 1, "start must resume, not call it complete"


def test_p1_2_a_launch_stopped_before_its_supervisor_is_recovered_by_stop(h):
    mark = h.tmp / "crash.mark"
    h.cli("start", extra_env={"EVAL_TEST_CRASH": "start:supervise:before",
                              "EVAL_TEST_CRASH_MARK": str(mark)})
    assert mark.exists()
    assert (h.ev.launch_dir(1) / "launch.json").exists()
    assert h.run("stop") == wrapper.EXIT_OK
    assert (h.ev.launch_dir(1) / "exit.json").exists(), "stop must record the interrupted launch"


def test_p1_2_a_whole_launch_directory_lost_is_reported(h, capsys):
    h.complete_evaluation(end_overrides={"run_pair_failures": "1"})
    assert h.start() == wrapper.EXIT_OK
    h.end_container(exit_code=0)
    h.wait_released()
    shutil.rmtree(h.ev.launch_dir(1))
    capsys.readouterr()
    assert h.run("summary", "--json") == 2, "a lost launch record must make the summary unverifiable"


def test_p1_3_a_failed_docker_logs_is_not_saved_and_the_container_is_kept(h):
    assert h.start() == wrapper.EXIT_OK
    h.fail("logs", 1)
    h.end_container(exit_code=0)
    h.wait_released()
    log = h.ev.launch_dir(1) / "runner.log"
    assert not (log.exists() and "Error response" in log.read_text()), "the error was saved as the log"
    assert [c["status"] for c in h.containers()] == ["exited"], "the container must be kept"


def test_p2_an_oom_increment_is_not_attributed_to_a_pair_that_ended_before_the_last_observation(
        tmp_path, monkeypatch, capsys):
    h = Harness(tmp_path, monkeypatch, poll="0.2", period="30")  # 観測 0.2 秒・保存（旧）30 秒
    cgroup = h.cgroup / f"{1:064x}"
    cgroup.mkdir(parents=True)

    def counter(value):
        (cgroup / "memory.events").write_text(f"low 0\nhigh 0\nmax 0\noom 0\noom_kill {value}\n")
        (cgroup / "memory.peak").write_text("1000\n")
        (cgroup / "memory.current").write_text("1000\n")

    counter(0)
    assert h.start() == wrapper.EXIT_OK
    begin = time.time()
    run_id = "e" * 32
    (h.ev.out / ".executions" / run_id).mkdir(parents=True)  # この launch の execution
    (h.ev.out / ".executions" / run_id / "run_manifest.start.txt").write_text(
        f"runtime_run_id={run_id}\n")
    metrics = h.ev.out / "S" / "Neq" / "f" / ".runtime-metrics"
    metrics.mkdir(parents=True)
    receipt = {"run_id": run_id, "execution_nonce": "n" * 24, "state": "COMPLETED",
               "status": "INCOMPLETE", "child_returncode": -9,
               "started_at_epoch": begin, "finished_at_epoch": begin + 0.3}
    for suffix in ("progress", "runtime"):
        (metrics / f"f_N_B1_O_B1.{suffix}.json").write_text(json.dumps(receipt))
    time.sleep(3.0)          # pair は終わっている。この間の観測は増分 0
    counter(1)               # その後の OOM kill（別の pair）
    time.sleep(1.0)
    h.end_container(exit_code=1)
    h.wait_released()
    capsys.readouterr()
    h.run("summary", "--json")
    result = json.loads(capsys.readouterr().out)
    (row,) = [r for r in result["interruptions"]["pairs"] if r["pair"].endswith("f_N_B1_O_B1.pair-status.json")]
    assert row["possible_oom"] not in (True, "yes"), row
