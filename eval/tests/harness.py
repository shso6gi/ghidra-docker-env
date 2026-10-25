# -*- coding: utf-8 -*-
"""eval/ の test が共有する harness: fake docker・本番の writer で作る tree・待ち合わせ。"""

from __future__ import annotations

import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
import time

import wrapper
import records
from scripts.function_tracer_pcode.reporting.execution_identity import source_tree_digest
from scripts.function_tracer_pcode.tests.unit import test_execution_chain as fixture

TESTS = Path(__file__).resolve().parent
COMMIT = "c" * 40
IMAGE_ID = "sha256:" + "1" * 64
PROBE = {"python_version": "3.10.12", "ghidra_version": "12.0.1", "java_version": "openjdk 21",
         "z3_version": "Z3 4.16.0", "cgroup_memory_max": "25769803776",
         "cgroup_cpu_max": "max 100000"}
PROFILE = """IMAGE=ghidra-docker-env:latest
CONTAINER_MEMORY=24g
STOP_GRACE_SECONDS=120
PARALLEL_JOBS=2
NEQ_RUN_SCOPE=FULL_NEQ
"""


def repo_head() -> str:
    return subprocess.run(["git", "-C", str(wrapper.REPO), "rev-parse", "HEAD"], check=True,
                          capture_output=True, text=True).stdout.strip()


class Harness:
    def __init__(self, tmp_path: Path, monkeypatch, *, poll: str = "0.2", period: str = "1"):
        self.tmp = tmp_path
        self.main = tmp_path / "main"
        (self.main / "logs" / "EqBench").mkdir(parents=True)
        (self.main / "targets").mkdir()
        (self.main / ".git").mkdir()
        self.state = tmp_path / "docker.json"
        self.write_state({"images": {"ghidra-docker-env:latest": IMAGE_ID}, "probe": PROBE})
        docker = tmp_path / "docker"
        docker.write_text(f"#!/bin/sh\nexec {sys.executable} -B {TESTS / 'fake_docker.py'} \"$@\"\n")
        docker.chmod(0o755)
        self.profile = tmp_path / "profile.env"
        self.profile.write_text(PROFILE)
        self.cgroup = tmp_path / "cgroup"
        self.environment = {
            "EVAL_DOCKER": str(docker), "FAKE_DOCKER_STATE": str(self.state),
            "EVAL_MAIN_CHECKOUT": str(self.main), "EVAL_PROFILE": str(self.profile),
            "EVAL_LOCK_FILE": str(tmp_path / "lock" / "eval.lock"),
            "EVAL_CGROUP_TEMPLATE": str(self.cgroup / "{id}"),
            "EVAL_WATCH_POLL_SECONDS": poll, "EVAL_WATCH_PERIOD_SECONDS": period,
            "EVAL_MIN_FREE_GIB": "0", "EVAL_REPO": str(wrapper.REPO),
        }
        for key, value in self.environment.items():
            monkeypatch.setenv(key, value)
        monkeypatch.delenv("EVAL_LOG_ROOT", raising=False)
        monkeypatch.delenv("EVAL_TAG", raising=False)
        # 評価用の worktree が clean で HEAD が freeze に一致すること（別の test で確かめる）。
        monkeypatch.setattr(wrapper, "worktree_state", lambda ev: None)
        self.ev = wrapper.resolve("neq", freeze=COMMIT, tag="", require_freeze=True)

    # -- fake docker ---------------------------------------------------------------
    def _locked(self):
        import fcntl

        fd = os.open(self.state.with_suffix(".lock"), os.O_RDWR | os.O_CREAT, 0o644)
        fcntl.flock(fd, fcntl.LOCK_EX)
        return fd

    def read_state(self) -> dict:
        fd = self._locked()
        try:
            return json.loads(self.state.read_text())
        finally:
            os.close(fd)

    def write_state(self, data: dict) -> None:
        temporary = self.state.with_suffix(".tmp-harness")
        temporary.write_text(json.dumps(data))
        os.replace(temporary, self.state)

    def update(self, change) -> None:
        """fake docker と同じ lock の下で読み・変え・書く（並行する docker の呼び出しと競合しない）。"""
        fd = self._locked()
        try:
            data = json.loads(self.state.read_text())
            change(data)
            self.write_state(data)
        finally:
            os.close(fd)

    def fail(self, operation: str, times: int = 1) -> None:
        self.update(lambda d: d.setdefault("fail", {}).update({operation: times}))

    def detached_runs(self) -> list:
        return self.read_state().get("containers_started", [])

    def containers(self) -> list:
        return self.read_state().get("containers", [])

    def end_container(self, exit_code=0, oom_killed=False) -> None:
        def change(data):
            for container in data.get("containers", []):
                if container["status"] == "running":
                    container.update({"status": "exited", "exit_code": exit_code,
                                      "oom_killed": oom_killed,
                                      "finished_at": "2026-10-25T00:05:00.000000000Z"})
        self.update(change)

    def remove_containers(self) -> None:
        self.update(lambda d: d.update({"containers": []}))

    # -- commands ------------------------------------------------------------------
    def run(self, command, *args) -> int:
        return wrapper.main(["--matrix", "neq", command, "--freeze", COMMIT, *args])

    def start(self) -> int:
        return self.run("start")

    def cli(self, command, *args, extra_env=None, timeout=120) -> subprocess.CompletedProcess:
        """wrapper を別 process で動かす（中断の注入用）。"""
        environment = {**os.environ, **self.environment, **(extra_env or {}),
                       "PYTHONPATH": os.pathsep.join([str(TESTS / "crashguard"),
                                                      str(wrapper.EVAL_DIR), str(wrapper.REPO)])}
        # worktree の検査だけを外す（別の test が確かめる）。本番の code に test 用の分岐は足さない。
        launcher = ("import sys, wrapper; wrapper.worktree_state = lambda ev: None; "
                    "sys.exit(wrapper.main(sys.argv[1:]))")
        return subprocess.run(
            [sys.executable, "-B", "-c", launcher, "--matrix", "neq", command, "--freeze", COMMIT,
             *args], env=environment, capture_output=True, text=True, timeout=timeout)

    def lock_free(self) -> bool:
        lock = wrapper.open_lock(self.ev)
        try:
            if wrapper.try_lock(lock):
                return True
            return False
        finally:
            os.close(lock)

    def wait_released(self, timeout=30.0) -> None:
        deadline = time.monotonic() + timeout
        while not self.lock_free():
            assert time.monotonic() < deadline, "the supervisor did not release the lock"
            time.sleep(0.1)

    def wait_for(self, predicate, timeout=30.0, message="condition") -> None:
        deadline = time.monotonic() + timeout
        while not predicate():
            assert time.monotonic() < deadline, f"timed out waiting for {message}"
            time.sleep(0.1)

    def records(self) -> records.RecordCheck:
        return records.read_records(self.ev.wrapper)

    def journal(self) -> list:
        rows, _bad, _exists = records.read_jsonl(self.ev.wrapper / records.JOURNAL)
        return [row["event"] for row in rows]

    def snapshot(self) -> dict:
        """出力先と wrapper の dir の全 entry と内容の digest。"""
        result = {}
        for root in (self.ev.out, self.ev.wrapper):
            if not root.exists():
                result[str(root)] = None
                continue
            for path in sorted(root.rglob("*")):
                result[str(path)] = (hashlib.sha256(path.read_bytes()).hexdigest()
                                     if path.is_file() else "dir")
        return result

    def meta(self) -> dict:
        return json.loads((self.ev.wrapper / records.META).read_text())

    # -- 本番の writer で作る tree ----------------------------------------------------
    def build_tree(self, *, fingerprint=None, end_overrides=None, commit=None, scope="FULL_NEQ"):
        """出力先に、本番の writer と署名で 2 execution（1 回目は kill、2 回目が封印）の tree を作る。

        launch の実行中に呼ぶと、その launch の execution として記録される（終了の記録が
        ``.executions`` の増分を数える）。
        """
        fingerprint = fingerprint or self.meta()["fingerprint"]
        commit = commit or repo_head()
        original = fixture.SOURCE
        fixture.SOURCE = source_tree_digest(wrapper.REPO)
        try:
            tree = fixture.ChainTree(self.ev.out, scope=scope)
            e1, e2 = fixture._run_id(1), fixture._run_id(2)
            fields = dict(environment_fingerprint=fingerprint, git_commit=commit, git_dirty="0")
            tree.start(e1, **fields)
            for pair in tree.pairs[:2]:
                tree.decide(e1, pair)
            tree.leave_incomplete(e1, tree.pairs[2])
            tree.start(e2, **fields)
            for pair in tree.pairs[2:]:
                tree.decide(e2, pair, outcome="NOT_EQ")
            tree.finish(e2, reused=tree.pairs[:2], end_overrides=end_overrides)
        finally:
            fixture.SOURCE = original
        return tree

    def finished_launch(self) -> None:
        """1 回の launch を始めて、container を終わらせ、終端まで待つ。"""
        assert self.start() == wrapper.EXIT_OK
        self.end_container(exit_code=0)
        self.wait_released()

    def complete_evaluation(self, **tree_options) -> None:
        """launch の中で tree を作り（execution が launch に結び付く）、終端まで待つ。"""
        assert self.start() == wrapper.EXIT_OK
        self.build_tree(**tree_options)
        self.end_container(exit_code=0)
        self.wait_released()
