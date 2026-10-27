# -*- coding: utf-8 -*-
"""PR #278 review 4 の 2 指摘の regression（CLI と記録の file だけで確かめる）。

旧実装（7b502fc0）でも同じ harness で動く形にしてあり、旧実装では挙動の誤りで落ちる（PR 本文）。

* R4-1: schema の不正な meta で、別の profile の条件の start が受理され、保存済みの条件で
  container が起動した（条件の照合を迂回）
* R4-2: issue を確定した後、wrapper の終了の記録の前に manifest と開始の記録が消えた出力を、
  開始前として退避して再開した（実行中の観測の有無の 2 通り）
* R4-3: launch の要求の条件と meta の条件が食い違っても、supervisor が container を起動した
"""

from __future__ import annotations

import json

import pytest

import wrapper
from harness import COMMIT, PROFILE, Harness, repo_head
from scripts.function_tracer_pcode.reporting.execution_identity import source_tree_digest
from scripts.function_tracer_pcode.tests.unit import test_execution_chain as fixture


def _cleanup(h):
    try:
        h.update(lambda d: d.update({"fail": {}}))
        h.end_container(exit_code=137)
        h.wait_released(timeout=60)
    except (OSError, ValueError, KeyError, AssertionError):
        pass


def _detached(h):
    return [c for c in h.read_state()["calls"] if c[:2] == ["run", "-d"]]


def test_r4_1_a_meta_with_a_bad_schema_does_not_bypass_the_conditions(tmp_path, monkeypatch):
    h = Harness(tmp_path, monkeypatch)
    try:
        h.finished_launch()
        path = h.ev.wrapper / "meta.json"
        meta = json.loads(path.read_text())
        meta.pop("schema")
        path.write_text(json.dumps(meta))
        h.profile.write_text(PROFILE.replace("PARALLEL_JOBS=2", "PARALLEL_JOBS=3"))
        runs = len(_detached(h))
        assert h.start() == wrapper.EXIT_REFUSED, "a start under other conditions was accepted"
        assert len(_detached(h)) == runs, "a container was started"
    finally:
        _cleanup(h)


@pytest.mark.parametrize("observed", [True, False])
def test_r4_2_committed_issues_without_their_start_record_are_not_moved_aside(
        tmp_path, monkeypatch, observed):
    h = Harness(tmp_path, monkeypatch, poll="0.2" if observed else "60")
    try:
        assert h.start() == wrapper.EXIT_OK
        watch = h.ev.launch_dir(1) / "watch.jsonl"
        if not observed:
            h.wait_for(watch.exists, message="the first observation")
        original = fixture.SOURCE
        fixture.SOURCE = source_tree_digest(wrapper.REPO)
        try:
            tree = fixture.ChainTree(h.ev.out)
            run_id = fixture._run_id(1)
            tree.start(run_id, environment_fingerprint=h.meta()["fingerprint"],
                       git_commit=repo_head(), git_dirty="0")
            tree.leave_incomplete(run_id, tree.pairs[0])  # issue は確定、status は無い
        finally:
            fixture.SOURCE = original
        if observed:
            h.wait_for(lambda: run_id in watch.read_text(), timeout=10,
                       message="an observation of the execution")
        (h.ev.out / "run_manifest.txt").unlink()
        (h.ev.out / ".executions" / run_id / "run_manifest.start.txt").unlink()
        h.end_container(exit_code=137)
        h.wait_released()
        runs = len(_detached(h))
        assert h.start() == wrapper.EXIT_REFUSED, "the damaged output was resumed"
        assert h.ev.out.is_dir() and not (h.ev.wrapper / "aborted-outputs").exists(), \
            "the damaged output was moved aside"
        assert len(_detached(h)) == runs
    finally:
        _cleanup(h)


def test_r4_3_the_supervisor_does_not_start_a_launch_requested_under_other_conditions(
        tmp_path, monkeypatch):
    h = Harness(tmp_path, monkeypatch)
    try:
        mark = h.tmp / "crash.mark"
        h.cli("start", extra_env={"EVAL_TEST_CRASH": "start:supervise:before",
                                  "EVAL_TEST_CRASH_MARK": str(mark)})
        assert mark.exists()
        path = h.ev.launch_dir(1) / "launch.json"
        payload = json.loads(path.read_text())
        payload["fingerprint"] = "eval-env-v1:" + "f" * 64
        path.write_text(json.dumps(payload))
        # 起動の試み（calls に残る）だけを見る: 起動は失敗させ、旧実装でも supervisor が返るように。
        h.fail("run-d", 1)
        lock = wrapper.open_lock(h.ev)
        assert wrapper.try_lock(lock)
        wrapper.main(["--matrix", "neq", "_supervise", "--freeze", COMMIT, "--launch", "1",
                      "--lock-fd", str(lock)])
        assert _detached(h) == [], "a container was started under other conditions"
    finally:
        _cleanup(h)
