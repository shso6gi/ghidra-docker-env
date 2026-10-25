# -*- coding: utf-8 -*-
"""eval/wrapper.py の契約（評価計画 v2 PR-D）。docker は ``fake_docker.py`` で置き換える。

* preflight の拒否（lock・slot の container・条件の違い・wrapper の記録の無い出力先・
  他の条件で動いた execution）は、出力先にも wrapper の dir にも何も書かない。
* 完了済み（検証器が CLOSED、fingerprint が一致）の ``start`` は何も書かず、container を
  起動しない。
* lock は背景の supervisor が container の終了・記録・削除の確認まで保持する。
* 終了の記録（exit code・runner の出力）を書けなければ container を消さない（証拠を失わない）。
  post-run の証拠を取れなければ、その欠損を記録する（summary が成功にしない）。
* ``stop`` は profile の猶予で docker stop し、supervisor が居なければ自分で終了を記録する。
* ``status`` / ``summary`` は出力先と wrapper の dir を変えない。
* 前回までの run tmpdir は、次の ``start`` が lock と container の不在を確かめた後でだけ消す。
"""

from __future__ import annotations

import hashlib
import json
import os
from pathlib import Path
import signal
import subprocess
import sys
import time

import pytest

import wrapper
import summarize
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


class Harness:
    def __init__(self, tmp_path: Path, monkeypatch):
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
        environment = {
            "EVAL_DOCKER": str(docker), "FAKE_DOCKER_STATE": str(self.state),
            "EVAL_MAIN_CHECKOUT": str(self.main), "EVAL_PROFILE": str(self.profile),
            "EVAL_LOCK_FILE": str(tmp_path / "lock" / "eval.lock"),
            "EVAL_CGROUP_TEMPLATE": str(self.cgroup / "{id}"),
            "EVAL_WATCH_POLL_SECONDS": "0.2", "EVAL_WATCH_PERIOD_SECONDS": "1",
            "EVAL_MIN_FREE_GIB": "0", "EVAL_REPO": str(wrapper.REPO),
        }
        for key, value in environment.items():
            monkeypatch.setenv(key, value)
        monkeypatch.delenv("EVAL_LOG_ROOT", raising=False)
        monkeypatch.delenv("EVAL_TAG", raising=False)
        # 評価用の worktree が clean で HEAD が freeze に一致すること（別の test で確かめる）。
        monkeypatch.setattr(wrapper, "worktree_state", lambda ev: None)
        self.ev = wrapper.resolve("neq", freeze=COMMIT, tag="", require_freeze=True)

    # -- fake docker ---------------------------------------------------------------
    def read_state(self) -> dict:
        return json.loads(self.state.read_text())

    def write_state(self, data: dict) -> None:
        self.state.write_text(json.dumps(data))

    def update(self, change) -> None:
        data = self.read_state()
        change(data)
        self.write_state(data)

    def detached_runs(self) -> list:
        return self.read_state().get("containers_started", [])

    def end_container(self, exit_code=0, oom_killed=False) -> None:
        def change(data):
            for container in data["containers"]:
                if container["status"] == "running":
                    container.update({"status": "exited", "exit_code": exit_code,
                                      "oom_killed": oom_killed,
                                      "finished_at": "2026-10-25T00:05:00.000000000Z"})
        self.update(change)

    # -- commands ------------------------------------------------------------------
    def run(self, command, *args) -> int:
        return wrapper.main(["--matrix", "neq", command, "--freeze", COMMIT, *args])

    def start(self) -> int:
        return self.run("start")

    def wait_released(self, timeout=30.0) -> None:
        lock = wrapper.open_lock(self.ev)
        try:
            deadline = time.monotonic() + timeout
            while not wrapper.try_lock(lock):
                assert time.monotonic() < deadline, "the supervisor did not release the lock"
                time.sleep(0.1)
        finally:
            os.close(lock)

    def snapshot(self) -> dict:
        """出力先と wrapper の dir の全 entry と内容の digest。"""
        result = {}
        for root in (self.ev.out, self.ev.wrapper):
            if not root.exists():
                result[str(root)] = None
                continue
            for path in sorted(root.rglob("*")):
                key = str(path)
                result[key] = (hashlib.sha256(path.read_bytes()).hexdigest()
                               if path.is_file() else "dir")
        return result


@pytest.fixture
def h(tmp_path, monkeypatch):
    harness = Harness(tmp_path, monkeypatch)
    yield harness
    # 後始末: 残った supervisor を止める（fake の container を終わらせる）。
    try:
        harness.end_container(exit_code=137)
    except (OSError, ValueError, KeyError):
        pass


# ---------------------------------------------------------------------------
# profile
# ---------------------------------------------------------------------------


@pytest.mark.parametrize("text, message", [
    ("CONTAINER_MEMORY=24g\nSTOP_GRACE_SECONDS=120\n", "IMAGE is required"),
    (PROFILE + "OUTPUT_BASE_DIR=/x\n", "set by the wrapper"),
    (PROFILE + "PARALLEL_JOBS=3\n", "set twice"),
    (PROFILE.replace("STOP_GRACE_SECONDS=120", "STOP_GRACE_SECONDS=60"), "above"),
    (PROFILE + "export X=1\n", "not a KEY=VALUE line"),
    (PROFILE.replace("24g", "lots"), "CONTAINER_MEMORY"),
])
def test_a_malformed_profile_is_rejected(tmp_path, text, message):
    path = tmp_path / "profile.env"
    path.write_text(text)
    with pytest.raises(wrapper.WrapperError, match=message):
        wrapper.load_profile(path)


def test_the_production_profile_is_the_plans_fixed_conditions():
    values, _sha = wrapper.load_profile(wrapper.EVAL_DIR / "profile.env")
    assert values["PARALLEL_JOBS"] == "30"
    assert values["CONTAINER_MEMORY"] == "110g"
    assert values["EQBENCH_RESOURCE_ADMISSION"] == "0"
    assert values["EQBENCH_DEBUG"] == "0"
    assert values["EQBENCH_IDENTICAL_FAST_PATH"] == "1"
    assert values["SKIP_COMPLETED_RESULTS"] == "1" and values["ERROR_ONLY_RERUN"] == "0"
    assert values["NEQ_RUN_SCOPE"] == "FULL_NEQ" and values["EQBENCH_RUN_SCOPE"] == "FULL_EQBENCH"
    assert values["NEQ_BUILD_POLICY"] == "REUSE_OR_COMPILE"
    assert values["EQBENCH_BUILD_POLICY"] == "PREBUILT_ONLY"
    # FT_* は runner の既定（config identity に入る）。profile では上書きしない。
    assert not [key for key in values if key.startswith("FT_")]
    # docker stop の猶予は runner の停止の確認（PR-A の上限）より長い。
    from scripts.eqbench.runner_processes import KILL_WAIT_SECONDS
    assert int(values["STOP_GRACE_SECONDS"]) > KILL_WAIT_SECONDS


def test_the_worktree_must_be_clean_and_at_the_freeze_commit(tmp_path):
    repo = tmp_path / "wt"
    repo.mkdir()
    for args in (["init", "-q"], ["config", "user.email", "t@e"], ["config", "user.name", "t"]):
        subprocess.run(["git", "-C", str(repo), *args], check=True)
    (repo / "a").write_text("1")
    subprocess.run(["git", "-C", str(repo), "add", "a"], check=True)
    subprocess.run(["git", "-C", str(repo), "commit", "-q", "-m", "a"], check=True)
    head = subprocess.run(["git", "-C", str(repo), "rev-parse", "HEAD"], check=True,
                          capture_output=True, text=True).stdout.strip()

    def ev(commit):
        return wrapper.Evaluation("neq", repo, tmp_path, commit, "", tmp_path, tmp_path,
                                  tmp_path / "l", "docker")

    wrapper.worktree_state(ev(head))
    with pytest.raises(wrapper.Refused, match="not the freeze commit"):
        wrapper.worktree_state(ev("0" * 40))
    (repo / "untracked").write_text("x")
    with pytest.raises(wrapper.Refused, match="not clean"):
        wrapper.worktree_state(ev(head))


def test_start_needs_an_explicit_freeze_commit(h, capsys):
    assert wrapper.main(["--matrix", "neq", "start"]) == wrapper.EXIT_REFUSED
    assert "--freeze" in capsys.readouterr().err


# ---------------------------------------------------------------------------
# start: 初回・lock・記録
# ---------------------------------------------------------------------------


def test_a_first_start_records_the_conditions_and_hands_them_to_the_runner(h):
    assert h.start() == wrapper.EXIT_OK
    meta = json.loads((h.ev.wrapper / "meta.json").read_text())
    (run,) = h.detached_runs()
    env = run["env"]
    assert env["EQBENCH_ENVIRONMENT_FINGERPRINT"] == meta["fingerprint"]
    assert meta["fingerprint"] == wrapper.fingerprint_of(meta["conditions"])
    assert meta["conditions"]["probe"] == PROBE
    assert meta["conditions"]["image"]["id"] == IMAGE_ID
    assert env["OUTPUT_BASE_DIR"] == "/workspace/logs/EqBench/" + h.ev.name
    assert env["EQBENCH_TMPDIR"] == f"/workspace/logs/EqBench/{h.ev.name}.wrapper/tmp"
    assert env["EQBENCH_PRIVATE_AUTHORITY_ROOT"] == f"/workspace/logs/EqBench/{h.ev.name}.wrapper/authority"
    assert env["PARALLEL_JOBS"] == "2" and "CONTAINER_MEMORY" not in env and "IMAGE" not in env
    assert run["image"] == IMAGE_ID and run["command"] == ["bash", "neqbench_run_all_32jobs.sh"]
    assert run["labels"] == {"ghidra-eval.slot": "1", "ghidra-eval.eval": h.ev.eval_id,
                             "ghidra-eval.launch": "1"}
    assert run["memory"] == "24g" and run["stop_timeout"] == "120"
    # 管理 file は出力先の外。出力先は runner が作る（FULL の FRESH 受理を壊さない）。
    assert not h.ev.out.exists()
    assert h.ev.wrapper.parent == h.ev.out.parent
    from scripts.function_tracer_pcode.reporting.execution_receipt import (
        OUTPUT_ADMISSION_FRESH,
        full_scope_output_admission,
    )
    candidate = h.tmp / "candidate.txt"
    h.end_container(exit_code=0)
    h.wait_released()
    tree = fixture.ChainTree.__new__(fixture.ChainTree)
    tree.scope, tree.prefilter, tree.config_overrides = "FULL_NEQ", ["targets/x.c"], {}
    candidate.write_text("".join(
        f"{k}={v}\n" for k, v in tree.start_fields(
            fixture._run_id(1), analysis_source_digest_start=source_tree_digest(wrapper.REPO)
        ).items()))
    kind, _reason = full_scope_output_admission(h.ev.out, candidate_manifest=candidate,
                                                repo_root=wrapper.REPO)
    assert kind == OUTPUT_ADMISSION_FRESH


def test_the_lock_is_held_in_the_background_until_the_container_is_recorded_and_removed(h, capsys):
    assert h.start() == wrapper.EXIT_OK
    lock = wrapper.open_lock(h.ev)
    try:
        assert not wrapper.try_lock(lock), "a second flock -n must fail while the run is going"
    finally:
        os.close(lock)
    before = h.snapshot()
    assert h.start() == wrapper.EXIT_REFUSED
    assert "lock" in capsys.readouterr().err
    assert h.snapshot() == before
    assert wrapper.lock_holders(h.ev), "status names the process holding the lock"
    h.end_container(exit_code=0)
    h.wait_released()
    directory = h.ev.launch_dir(1)
    exit_record = json.loads((directory / "exit.json").read_text())
    assert exit_record["exit_code"] == 0 and exit_record["oom_killed"] is False
    assert (directory / "runner.log").read_text().startswith("fake runner output")
    assert json.loads((directory / "evidence.json").read_text())["schema"] == "eval-launch-evidence-v1"
    assert h.read_state()["containers"] == []
    events = [json.loads(line)["event"] for line in
              (h.ev.wrapper / "events.jsonl").read_text().splitlines()]
    assert events == ["launch_requested", "container_started", "container_exited",
                      "evidence_saved", "released"]
    # 証拠は container を消す前に取る（記録者が途中で止まっても、回収が続きから行える）。
    calls = h.read_state()["calls"]
    evidence_call = max(i for i, c in enumerate(calls) if c[:2] == ["run", "--rm"])
    remove_call = max(i for i, c in enumerate(calls) if c[0] == "rm")
    assert evidence_call < remove_call
    assert wrapper.lock_holders(h.ev) is None


def test_the_watch_records_oom_kill_increments_as_they_happen(h):
    assert h.start() == wrapper.EXIT_OK
    (run,) = h.detached_runs()
    cgroup = h.cgroup / run["id"]
    cgroup.mkdir(parents=True)

    def write(oom_kill, peak):
        (cgroup / "memory.events").write_text(f"low 0\nhigh 0\nmax 3\noom 1\noom_kill {oom_kill}\n")
        (cgroup / "memory.peak").write_text(f"{peak}\n")
        (cgroup / "memory.current").write_text("1000\n")

    write(0, 5000)
    time.sleep(1.0)
    write(2, 9000)
    time.sleep(1.0)
    h.end_container(exit_code=1)
    h.wait_released()
    rows = [json.loads(line) for line in
            (h.ev.launch_dir(1) / "watch.jsonl").read_text().splitlines()]
    changes = [row for row in rows if row["kind"] == "oom_kill_change"]
    assert [row["oom_kill_delta"] for row in changes] == [2]
    exit_record = json.loads((h.ev.launch_dir(1) / "exit.json").read_text())
    assert exit_record["last_cgroup_sample"]["memory_peak"] == 9000


# ---------------------------------------------------------------------------
# preflight の拒否は何も書かない
# ---------------------------------------------------------------------------


def _finished_first_launch(h):
    assert h.start() == wrapper.EXIT_OK
    h.end_container(exit_code=0)
    h.wait_released()


@pytest.mark.parametrize("change, message", [
    ("profile", "profile.sha256"),
    ("memory", "container.memory"),
    ("image", "image.id"),
    ("probe", "probe.java_version"),
])
def test_other_conditions_are_refused_without_writing_anything(h, capsys, change, message):
    _finished_first_launch(h)
    if change == "profile":
        h.profile.write_text(PROFILE.replace("PARALLEL_JOBS=2", "PARALLEL_JOBS=3"))
    elif change == "memory":
        h.profile.write_text(PROFILE.replace("24g", "32g"))
    elif change == "image":
        h.update(lambda d: d["images"].update({"ghidra-docker-env:latest": "sha256:" + "2" * 64}))
    else:
        h.update(lambda d: d["probe"].update({"java_version": "openjdk 22"}))
    before = h.snapshot()
    calls = len(h.read_state()["calls"])
    assert h.start() == wrapper.EXIT_REFUSED
    err = capsys.readouterr().err
    assert "nothing was written" in err and message in err
    assert h.snapshot() == before
    assert not [c for c in h.read_state()["calls"][calls:] if c[:2] == ["run", "-d"]]


def test_a_slot_container_left_behind_is_refused(h, capsys):
    h.update(lambda d: d.setdefault("containers", []).append({
        "id": "f" * 64, "name": "ghidra-eval-other", "status": "exited",
        "labels": {"ghidra-eval.slot": "1", "ghidra-eval.eval": "other"}}))
    before = h.snapshot()
    assert h.start() == wrapper.EXIT_REFUSED
    assert "ghidra-eval-other (exited)" in capsys.readouterr().err
    assert h.snapshot() == before


def test_an_output_without_wrapper_records_is_refused(h, capsys):
    h.ev.out.mkdir(parents=True)
    (h.ev.out / "run_manifest.txt").write_text("run_kind=x\n")
    before = h.snapshot()
    assert h.start() == wrapper.EXIT_REFUSED
    assert "no wrapper record" in capsys.readouterr().err
    assert h.snapshot() == before


def _closed_tree(h, fingerprint):
    """wrapper の出力先に、本番の writer で作った 2 execution の CLOSED な FULL tree を置く。"""
    digest = source_tree_digest(wrapper.REPO)
    original = fixture.SOURCE
    fixture.SOURCE = digest
    try:
        tree = fixture.ChainTree(h.ev.out, scope="FULL_NEQ")
        e1, e2 = fixture._run_id(1), fixture._run_id(2)
        tree.start(e1, environment_fingerprint=fingerprint)
        for pair in tree.pairs[:2]:
            tree.decide(e1, pair)
        tree.start(e2, environment_fingerprint=fingerprint)
        for pair in tree.pairs[2:]:
            tree.decide(e2, pair)
        tree.finish(e2, reused=tree.pairs[:2])
    finally:
        fixture.SOURCE = original
    return tree


def test_a_complete_evaluation_is_not_started_again_and_nothing_is_written(h, capsys):
    _finished_first_launch(h)
    meta = json.loads((h.ev.wrapper / "meta.json").read_text())
    _closed_tree(h, meta["fingerprint"])
    before = h.snapshot()
    calls = len(h.read_state()["calls"])
    assert h.start() == wrapper.EXIT_OK
    assert "already complete" in capsys.readouterr().out
    assert h.snapshot() == before
    assert not [c for c in h.read_state()["calls"][calls:] if c[:2] == ["run", "-d"]]


def test_an_execution_under_other_conditions_in_the_output_is_refused(h, capsys):
    _finished_first_launch(h)
    _closed_tree(h, "eval-env-v1:" + "9" * 64)
    before = h.snapshot()
    assert h.start() == wrapper.EXIT_REFUSED
    assert "did not run under this evaluation's conditions" in capsys.readouterr().err
    assert h.snapshot() == before


# ---------------------------------------------------------------------------
# 再開・tmp の残骸
# ---------------------------------------------------------------------------


def test_leftover_run_tmpdirs_are_removed_only_by_the_next_start(h, capsys):
    _finished_first_launch(h)
    leftover = h.ev.tmp / "neqbench-run.ABC123"
    (leftover / "pair.x").mkdir(parents=True)
    (leftover / "pair.x" / "store").write_text("x" * 100)
    before = h.snapshot()
    assert h.run("status") == wrapper.EXIT_OK
    assert "1 left by earlier executions" in capsys.readouterr().out
    assert h.snapshot() == before
    assert h.start() == wrapper.EXIT_OK
    assert not leftover.exists()
    launch = json.loads((h.ev.launch_dir(2) / "launch.json").read_text())
    assert launch["removed_leftovers"] == [{"name": "neqbench-run.ABC123", "kind": "run_tmpdir",
                                            "bytes": 100}]
    assert launch["kind"] == "first"  # 出力先に execution の記録はまだ無い（fake の runner）
    # 実行中に作られた tmp は「実行中のもの」で、残骸と区別する。
    (h.ev.tmp / "neqbench-run.NEW").mkdir()
    state = wrapper.container_state(h.ev)
    state["started_at"] = "2000-01-01T00:00:00.000000000Z"
    assert wrapper.tmp_entries(h.ev, state) == [{"name": "neqbench-run.NEW", "state": "current"}]


# ---------------------------------------------------------------------------
# stop と回収
# ---------------------------------------------------------------------------


def test_stop_uses_the_profiles_grace_and_waits_for_the_record(h, capsys):
    assert h.start() == wrapper.EXIT_OK
    assert h.run("stop") == wrapper.EXIT_OK
    stops = [c for c in h.read_state()["calls"] if c[0] == "stop"]
    assert stops == [["stop", "-t", "120", h.ev.container_name]]
    exit_record = json.loads((h.ev.launch_dir(1) / "exit.json").read_text())
    assert exit_record["exit_code"] == 143
    assert exit_record["runner_exit_meaning"] == "stopped (TERM)"
    assert "runner exit 143" in capsys.readouterr().out


def test_stop_records_the_end_itself_when_the_supervisor_is_gone(h, capsys):
    assert h.start() == wrapper.EXIT_OK
    pid = (wrapper.lock_holders(h.ev) or [None])[0]
    assert pid is not None
    os.kill(pid, signal.SIGKILL)
    deadline = time.monotonic() + 10
    while wrapper.lock_holders(h.ev) is not None and time.monotonic() < deadline:
        time.sleep(0.1)
    # supervisor が居ない間も、slot の container が残っているので start は拒否される。
    assert h.start() == wrapper.EXIT_REFUSED
    assert h.run("stop") == wrapper.EXIT_OK
    assert "supervisor of launch 1 is gone" in capsys.readouterr().out
    assert json.loads((h.ev.launch_dir(1) / "exit.json").read_text())["exit_code"] == 143
    assert h.read_state()["containers"] == []


def test_a_container_whose_end_cannot_be_recorded_is_kept(h):
    assert h.start() == wrapper.EXIT_OK
    directory = h.ev.launch_dir(1)
    directory.chmod(0o500)
    try:
        h.end_container(exit_code=0)
        h.wait_released()
        assert not (directory / "exit.json").exists()
        assert [c["status"] for c in h.read_state()["containers"]] == ["exited"]
    finally:
        directory.chmod(0o700)
    # 残った container が次の start を止める（記録の無い終了を見落とさない）。
    assert h.start() == wrapper.EXIT_REFUSED


def test_missing_post_run_evidence_is_recorded_as_a_gap(h):
    h.update(lambda d: d.update({"fail_reader": True}))
    assert h.start() == wrapper.EXIT_OK
    h.end_container(exit_code=0)
    h.wait_released()
    assert not (h.ev.launch_dir(1) / "evidence.json").exists()
    events = [json.loads(line)["event"] for line in
              (h.ev.wrapper / "events.jsonl").read_text().splitlines()]
    assert "evidence_failed" in events
    launches, gaps = summarize._launches(h.ev.wrapper)
    assert gaps == ["launch 1: no post-run evidence"]


# ---------------------------------------------------------------------------
# status / summary は読むだけ
# ---------------------------------------------------------------------------


def test_status_and_summary_write_nothing(h, capsys):
    _finished_first_launch(h)
    meta = json.loads((h.ev.wrapper / "meta.json").read_text())
    _closed_tree(h, meta["fingerprint"])
    before = h.snapshot()
    assert h.run("status", "--verify") == wrapper.EXIT_OK
    assert "CLOSED_SAME_IDENTITY" in capsys.readouterr().out
    code = h.run("summary")
    out = capsys.readouterr().out
    assert "VERDICT:" in out and code in (0, 1)
    assert h.run("summary", "--json") in (0, 1)
    assert json.loads(capsys.readouterr().out)["schema"] == "eval-summary-v1"
    assert h.snapshot() == before
    readers = [c for c in h.read_state()["calls"] if c[:2] == ["run", "--rm"]]
    assert readers and all(f"{h.main / 'logs'}:/workspace/logs:ro" in c for c in readers)


def test_a_launch_whose_container_never_started_is_recorded_and_is_not_a_gap(h):
    h.update(lambda d: d.update({"fail_detached": True}))
    assert h.start() == wrapper.EXIT_FAILED
    h.wait_released()
    exit_record = json.loads((h.ev.launch_dir(1) / "exit.json").read_text())
    assert exit_record["container_started"] is False and "cannot start" in exit_record["error"]
    assert summarize._launches(h.ev.wrapper)[1] == []
    h.update(lambda d: d.update({"fail_detached": False}))
    assert h.start() == wrapper.EXIT_OK  # 同じ条件でそのまま再試行できる


def test_a_lost_docker_wait_does_not_end_the_watch(h):
    h.update(lambda d: d.update({"wait_fails_once": True}))
    assert h.start() == wrapper.EXIT_OK
    time.sleep(1.0)
    assert wrapper.lock_holders(h.ev), "the supervisor keeps watching the running container"
    h.end_container(exit_code=0)
    h.wait_released()
    rows = [json.loads(line) for line in
            (h.ev.launch_dir(1) / "watch.jsonl").read_text().splitlines()]
    assert "wait_restarted" in [row["kind"] for row in rows]
    assert json.loads((h.ev.launch_dir(1) / "exit.json").read_text())["exit_code"] == 0


def test_recording_resumes_after_a_recorder_stopped_between_record_and_removal(h):
    h.update(lambda d: d.update({"fail_rm_once": True}))
    assert h.start() == wrapper.EXIT_OK
    h.end_container(exit_code=0)
    h.wait_released()
    directory = h.ev.launch_dir(1)
    first = (directory / "exit.json").read_bytes()
    assert (directory / "evidence.json").exists()
    assert [c["status"] for c in h.read_state()["containers"]] == ["exited"]
    assert h.run("stop") == wrapper.EXIT_OK
    assert h.read_state()["containers"] == []
    assert (directory / "exit.json").read_bytes() == first  # 記録は書き直さない


def test_an_output_stopped_before_its_start_record_is_moved_aside_not_deleted(h, capsys):
    _finished_first_launch(h)
    # 初回の execution が関数選択の途中で止まった出力先: manifest も開始の記録も pair も無い。
    (h.ev.out / "CLEVER" / "x").mkdir(parents=True)
    (h.ev.out / "neq_source_pairs.tsv").write_text("x\n")
    (h.ev.out / "pair-status-verification-key.json").write_text("{}")
    assert wrapper.never_recorded_a_start(h.ev.out)
    assert h.start() == wrapper.EXIT_OK
    aside = h.ev.wrapper / "aborted-outputs" / "before-launch-2"
    assert (aside / "neq_source_pairs.tsv").read_text() == "x\n"
    assert not h.ev.out.exists()
    launch = json.loads((h.ev.launch_dir(2) / "launch.json").read_text())
    assert launch["moved_aside_output"] == str(aside)
    assert "moved it aside" in capsys.readouterr().out


def test_an_output_with_a_start_record_or_a_pair_is_never_moved_aside(h):
    out = h.ev.out
    (out / ".executions" / ("a" * 32)).mkdir(parents=True)
    (out / ".executions" / ("a" * 32) / "run_manifest.start.txt").write_text("x=1\n")
    assert not wrapper.never_recorded_a_start(out)
    (out / ".executions" / ("a" * 32) / "run_manifest.start.txt").unlink()
    (out / "S" / "f").mkdir(parents=True)
    (out / "S" / "f" / "f_B1_B2.pair-status.json").write_text("{}")
    assert not wrapper.never_recorded_a_start(out)
    (out / "S" / "f" / "f_B1_B2.pair-status.json").unlink()
    (out / "run_manifest.txt").write_text("x=1\n")
    assert not wrapper.never_recorded_a_start(out)


def test_a_refused_start_leaves_the_leftovers_of_earlier_executions_alone(h):
    _finished_first_launch(h)
    leftover = h.ev.tmp / "neqbench-run.KEEP"
    leftover.mkdir()
    h.profile.write_text(PROFILE.replace("PARALLEL_JOBS=2", "PARALLEL_JOBS=3"))
    assert h.start() == wrapper.EXIT_REFUSED
    assert leftover.is_dir()
