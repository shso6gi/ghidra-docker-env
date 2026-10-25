# -*- coding: utf-8 -*-
"""中断からの回復（評価計画 v2 PR-D、review 1 P1-2）。

本番の wrapper を別 process で動かし、記録の確定点（link / replace / rename / mkdir / write）と
外部操作（Popen）の **すべての境界** で、前または後に強制終了させる（``crashguard``）。残った
状態から ``stop`` で回収し、次の ``start`` が正常に launch し終端できることを確かめる:

* 記録の破損として報告される状態が残らない（正常な中断は破損ではない）
* 未完了の launch が残らない（``stop`` が続きから回収する）
* 評価の container が残らない（終了と証拠を記録してから消す）
* その後の ``start`` → 終了 → 終端が成り立つ

境界の数は数えずに、発火しなくなるまで n を増やす（発火しなかった = 境界を使い切った）。
"""

from __future__ import annotations

import os
import signal

import pytest

import records
import wrapper
from harness import Harness


def _harness(tmp_path, monkeypatch, name):
    root = tmp_path / name
    root.mkdir()
    # 観測は最初の 1 回だけにする（境界の数を時間に依らず決めるため）。
    return Harness(root, monkeypatch, poll="1000", period="1000")


def _recover_and_check(h, label):
    """中断の後: container を終わらせ、supervisor を待ち、stop で回収し、不変条件を確かめる。"""
    h.end_container(exit_code=137)
    h.wait_released(timeout=60)
    stopped = h.cli("stop", "--wait", "60")
    assert stopped.returncode == 0, f"{label}: stop failed: {stopped.stderr[-800:]}"
    check = h.records()
    assert not check.problems, f"{label}: {check.problems}"
    assert check.unfinished is None, f"{label}: launch left {check.unfinished.state}"
    assert h.containers() == [], f"{label}: container left: {h.containers()}"
    # 回復した評価は、そのまま次の launch を始めて終端できる。
    started = h.cli("start")
    assert started.returncode == 0, f"{label}: start after recovery: {started.stderr[-800:]}"
    h.end_container(exit_code=0)
    h.wait_released(timeout=60)
    check = h.records()
    assert not check.problems and check.unfinished is None, f"{label}: {check.problems}"
    assert all(launch.terminal for launch in check.launches)
    assert check.launches[-1].exit_kind == records.KIND_RAN
    assert h.containers() == []


def _sweep(tmp_path, monkeypatch, role, prepare, act):
    fired = 0
    for when in ("before", "after"):
        for index in range(1, 200):
            h = _harness(tmp_path, monkeypatch, f"{role}-{when}-{index}")
            prepare(h)
            mark = h.tmp / "crash.mark"
            act(h, {"EVAL_TEST_CRASH": f"{role}:{index}:{when}",
                    "EVAL_TEST_CRASH_MARK": str(mark)})
            if not mark.exists():
                break
            fired += 1
            _recover_and_check(h, f"{role} {when} boundary {index} ({mark.read_text().strip()})")
        else:
            pytest.fail(f"{role}: more than 200 boundaries")
    assert fired >= 10, f"{role}: only {fired} boundaries were exercised"


def test_a_start_stopped_at_any_boundary_is_recovered(tmp_path, monkeypatch):
    def prepare(h):
        pass

    def act(h, env):
        h.cli("start", extra_env=env)

    _sweep(tmp_path, monkeypatch, "start", prepare, act)


def test_a_resuming_start_stopped_at_any_boundary_is_recovered(tmp_path, monkeypatch):
    """2 回目の start（tmp の残骸の削除と、開始の記録の前に止まった出力先の退避を含む）。"""
    def prepare(h):
        assert h.start() == wrapper.EXIT_OK
        h.end_container(exit_code=137)
        h.wait_released()
        (h.ev.tmp / "neqbench-run.OLD" / "pair.x").mkdir(parents=True)
        (h.ev.out / "CLEVER").mkdir(parents=True)
        (h.ev.out / "neq_source_pairs.tsv").write_text("x\n")

    def act(h, env):
        h.cli("start", extra_env=env)

    _sweep(tmp_path, monkeypatch, "start", prepare, act)


def test_a_supervisor_stopped_at_any_boundary_is_recovered(tmp_path, monkeypatch):
    def prepare(h):
        pass

    def act(h, env):
        h.cli("start", extra_env=env)
        h.end_container(exit_code=0)
        h.wait_released(timeout=60)

    _sweep(tmp_path, monkeypatch, "_supervise", prepare, act)


def test_a_recovery_stopped_at_any_boundary_is_recovered(tmp_path, monkeypatch):
    def prepare(h):
        assert h.start() == wrapper.EXIT_OK
        pid = (wrapper.lock_holders(h.ev) or [None])[0]
        os.kill(pid, signal.SIGKILL)
        h.wait_for(lambda: wrapper.lock_holders(h.ev) is None, message="the lock")
        h.end_container(exit_code=0)

    def act(h, env):
        h.cli("stop", "--wait", "30", extra_env=env)

    _sweep(tmp_path, monkeypatch, "stop", prepare, act)
