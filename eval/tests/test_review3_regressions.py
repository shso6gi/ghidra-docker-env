# -*- coding: utf-8 -*-
"""PR #278 review 3 の regression（CLI と記録の file だけで確かめる）。

旧実装（457eedda）でも同じ harness で動く形にしてあり、旧実装ではすべて落ちる（PR 本文に記録）。
詳しい組合せは ``test_review3.py``。
"""

from __future__ import annotations

import json
import os
import signal

import pytest

import protocol
import wrapper
from harness import Harness


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
    (h.ev.out / "CLEVER" / "x").mkdir(parents=True)
    (h.ev.out / "neq_source_pairs.tsv").write_text("x\n")


def _exit_kind(h, number):
    return json.loads((h.ev.launch_dir(number) / "exit.json").read_text()).get("kind")


def test_r3_1_a_permanent_record_refuses_a_start_whose_output_would_be_moved_aside(h):
    assert h.start() == wrapper.EXIT_OK
    _preparation_files(h)  # runner が manifest・開始の記録の前に作る準備の file
    pid = (wrapper.lock_holders(h.ev) or [None])[0]
    os.kill(pid, signal.SIGKILL)
    h.wait_for(lambda: wrapper.lock_holders(h.ev) is None, message="the lock")
    h.remove_containers()  # container が外部で消された
    assert h.run("stop") == wrapper.EXIT_OK
    assert _exit_kind(h, 1) == "exit_unobserved"
    launched = len(h.detached_runs())
    before = h.snapshot()
    assert h.start() == wrapper.EXIT_REFUSED
    assert len(h.detached_runs()) == launched
    assert h.snapshot() == before
    assert (h.ev.out / "neq_source_pairs.tsv").exists()


def test_r3_2_a_never_started_execution_dir_does_not_break_the_records_after_the_move(h, capsys):
    assert h.start() == wrapper.EXIT_OK
    _preparation_files(h)
    debris = h.ev.out / ".executions" / ("c" * 32)
    debris.mkdir(parents=True)
    (debris / ".run_manifest.start.txt.uncommitted-abc").write_text("partial")
    h.end_container(exit_code=137)
    h.wait_released()
    assert h.start() == wrapper.EXIT_OK  # 開始前の出力を退避して再開
    h.end_container(exit_code=0)
    h.wait_released()
    capsys.readouterr()
    h.run("summary", "--json")
    result = json.loads(capsys.readouterr().out)
    assert result["verdict"] != "UNVERIFIABLE", result["reasons"]


def test_r3_3_a_launch_whose_unrecorded_container_changed_the_output_is_not_not_started(h):
    mark = h.tmp / "crash.mark"
    h.cli("start", extra_env={"EVAL_TEST_CRASH": "start:supervise:before",
                              "EVAL_TEST_CRASH_MARK": str(mark)})
    assert mark.exists()
    _preparation_files(h)  # 記録されなかった container が書いた
    assert h.run("stop") == wrapper.EXIT_OK
    assert _exit_kind(h, 1) == "exit_unobserved"


def test_r3_4_the_start_decision_does_not_accept_an_omitted_judgement():
    assert protocol.start_decision(None)[0] == protocol.DECISION_REFUSE
