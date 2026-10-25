# -*- coding: utf-8 -*-
"""PR #278 review 2 の 3 指摘の regression（CLI と記録の file だけで確かめる）。

旧実装（106c1c35）でも同じ harness で動く形にしてあり、旧実装ではすべて落ちる（PR 本文に記録）。
詳しい組合せと時系列は ``test_review2.py``。
"""

from __future__ import annotations

import json
import os
import signal

import pytest

import wrapper
from harness import Harness
from test_review2 import E1, E2, _execution, _receipt


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


def test_r2_1_a_failed_reader_with_valid_json_is_not_recorded_and_the_container_is_kept(h):
    assert h.start() == wrapper.EXIT_OK
    h.respond("launch-evidence", returncode=1)  # 非 0 終了 + 正しい形の JSON
    h.end_container(exit_code=0)
    h.wait_released()
    assert not (h.ev.launch_dir(1) / "evidence.json").exists()
    assert [c["status"] for c in h.containers()] == ["exited"]


def test_r2_2_a_permanent_reason_with_a_resumable_one_refuses_the_resume(h):
    assert h.start() == wrapper.EXIT_OK
    h.build_tree()
    next(h.ev.out.rglob("*.pair-status.json")).unlink()  # 連鎖を OPEN（resumable）に
    pid = (wrapper.lock_holders(h.ev) or [None])[0]
    os.kill(pid, signal.SIGKILL)
    h.wait_for(lambda: wrapper.lock_holders(h.ev) is None, message="the lock")
    h.remove_containers()  # container の終了を観測できない（permanent）
    assert h.run("stop") == wrapper.EXIT_OK
    launched = len(h.detached_runs())
    assert h.start() == wrapper.EXIT_REFUSED
    assert len(h.detached_runs()) == launched


def test_r2_3_a_kill_left_by_e1_is_not_recounted_or_tied_to_the_oom_of_e2(h, capsys):
    assert h.start() == wrapper.EXIT_OK
    _execution(h, E1)
    _receipt(h, E1, "n1")
    h.end_container(exit_code=0)
    h.wait_released()
    assert h.start() == wrapper.EXIT_OK
    _execution(h, E2)
    h.end_container(exit_code=137, oom_killed=True)
    h.wait_released()
    capsys.readouterr()
    h.run("summary", "--json")
    rows = json.loads(capsys.readouterr().out)["interruptions"]["pairs"]
    assert len(rows) == 1, rows
    assert rows[0]["possible_oom"] not in (True, "yes"), rows
