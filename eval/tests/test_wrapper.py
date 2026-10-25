# -*- coding: utf-8 -*-
"""eval/wrapper.py の契約（評価計画 v2 PR-D）。docker は ``fake_docker.py`` で置き換える。

* preflight の拒否（lock・slot の container・条件の違い・wrapper の記録の無い出力先・
  他の条件で動いた execution・未完了の launch・破損した記録）は、何も書かない。
* ``start`` の「完了済み」は ``summary`` と同じ判定（``summarize.completion``）。chain が CLOSED
  でも ledger が拒否する tree では、完了とせずに再開する（review 1 P1-1）。
* launch は 起動の要求 → container → 終了の記録 → 証拠 → 削除の確認 の順に 1 回ずつ確定する。
  container は終了と証拠を記録するまで消さない。外部操作が失敗・観測不能なら記録せず、
  container を残し、``stop`` が続きから回収する（review 1 P1-2・P1-3）。
* lock は背景の supervisor（と ``docker run`` の CLI）が、launch が終端するまで保持する。
* ``status`` / ``summary`` は出力先と wrapper の dir を変えない。
* 前回までの run tmpdir は、次の ``start`` が lock と container の不在を確かめた後でだけ消す。
"""

from __future__ import annotations

import json
import os
from pathlib import Path
import signal
import subprocess
import time

import pytest

import records
import summarize
import wrapper
from harness import COMMIT, IMAGE_ID, PROBE, PROFILE, Harness, repo_head
from scripts.function_tracer_pcode.reporting.execution_identity import source_tree_digest
from scripts.function_tracer_pcode.tests.unit import test_execution_chain as fixture


@pytest.fixture
def h(tmp_path, monkeypatch):
    harness = Harness(tmp_path, monkeypatch)
    yield harness
    # 後始末: 残った supervisor を止める（fake の container を終わらせる）。
    try:
        harness.update(lambda d: d.update({"fail": {}}))
        harness.end_container(exit_code=137)
        harness.wait_released(timeout=60)
    except (OSError, ValueError, KeyError, AssertionError):
        pass


def _runs_since(h, calls):
    return [c for c in h.read_state()["calls"][calls:] if c[:2] == ["run", "-d"]]


# ---------------------------------------------------------------------------
# profile と worktree
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
# start: 初回・lock・記録の順序
# ---------------------------------------------------------------------------


def test_a_first_start_records_the_conditions_and_hands_them_to_the_runner(h):
    assert h.start() == wrapper.EXIT_OK
    meta = h.meta()
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
    # docker run の CLI も lock を持つ: supervisor が途中で死んでも、作成中は回収が lock を取れない。
    assert run["cli_holds_eval_lock"] is True
    # 管理 file は出力先の外。出力先は runner が作る（FULL の FRESH 受理を壊さない）。
    assert not h.ev.out.exists()
    from scripts.function_tracer_pcode.reporting.execution_receipt import (
        OUTPUT_ADMISSION_FRESH,
        full_scope_output_admission,
    )
    h.end_container(exit_code=0)
    h.wait_released()
    tree = fixture.ChainTree.__new__(fixture.ChainTree)
    tree.scope, tree.prefilter, tree.config_overrides = "FULL_NEQ", ["targets/x.c"], {}
    candidate = h.tmp / "candidate.txt"
    candidate.write_text("".join(
        f"{k}={v}\n" for k, v in tree.start_fields(
            fixture._run_id(1), analysis_source_digest_start=source_tree_digest(wrapper.REPO)
        ).items()))
    kind, _reason = full_scope_output_admission(h.ev.out, candidate_manifest=candidate,
                                                repo_root=wrapper.REPO)
    assert kind == OUTPUT_ADMISSION_FRESH


def test_a_launch_is_recorded_in_order_and_ends_released(h, capsys):
    assert h.start() == wrapper.EXIT_OK
    lock = wrapper.open_lock(h.ev)
    try:
        assert not wrapper.try_lock(lock), "a second flock -n must fail while the run is going"
    finally:
        os.close(lock)
    def snapshot():  # 実行中の supervisor が書く観測の行は除く
        return {k: v for k, v in h.snapshot().items() if not k.endswith(records.WATCH)}

    before = snapshot()
    assert h.start() == wrapper.EXIT_REFUSED
    assert "lock" in capsys.readouterr().err
    assert snapshot() == before
    assert wrapper.lock_holders(h.ev), "status names the process holding the lock"
    h.end_container(exit_code=0)
    h.wait_released()
    check = h.records()
    assert not check.problems and check.unfinished is None
    (launch,) = check.launches
    assert launch.state == records.STATE_RELEASED and launch.exit_kind == records.KIND_RAN
    assert launch.exit["exit_code"] == 0 and launch.exit["oom_killed"] is False
    assert launch.exit["container_id"] == launch.container["container_id"]
    log = (h.ev.launch_dir(1) / records.RUNNER_LOG).read_text()
    assert log == "fake runner output\nfake runner error line\n"
    assert launch.evidence["schema"] == records.EVIDENCE_SCHEMA
    assert h.containers() == []
    assert h.journal() == ["start_requested", "launch_requested", "container_recorded",
                           "exit_recorded", "evidence_recorded", "released"]
    # 証拠は container を消す前に取る（記録者が途中で止まっても、回収が続きから行える）。
    calls = h.read_state()["calls"]
    evidence_call = max(i for i, c in enumerate(calls) if c[:2] == ["run", "--rm"])
    remove_call = max(i for i, c in enumerate(calls) if c[0] == "rm")
    assert evidence_call < remove_call
    assert wrapper.lock_holders(h.ev) is None


def test_every_cgroup_observation_is_kept_including_the_unobserved_ones(h):
    assert h.start() == wrapper.EXIT_OK
    (run,) = h.detached_runs()
    cgroup = h.cgroup / run["id"]

    def write(oom_kill, peak):
        cgroup.mkdir(parents=True, exist_ok=True)
        (cgroup / "memory.events").write_text(f"low 0\nhigh 0\nmax 3\noom 1\noom_kill {oom_kill}\n")
        (cgroup / "memory.peak").write_text(f"{peak}\n")
        (cgroup / "memory.current").write_text("1000\n")

    time.sleep(0.5)  # cgroup が無い間の観測
    write(0, 5000)
    time.sleep(1.0)
    write(2, 9000)
    time.sleep(1.0)
    h.end_container(exit_code=1)
    h.wait_released()
    (launch,) = h.records().launches
    assert any(row["observed"] is False for row in launch.watch)
    counters = [row["oom_kill"] for row in launch.watch if row["observed"]]
    assert counters[0] == 0 and counters[-1] == 2 and counters == sorted(counters)
    assert launch.exit["last_observation"]["memory_peak"] == 9000
    assert sum(i.delta or 0 for i in records.counter_intervals(launch.watch)) == 2


# ---------------------------------------------------------------------------
# preflight の拒否は何も書かない
# ---------------------------------------------------------------------------


@pytest.mark.parametrize("change, message", [
    ("profile", "profile.sha256"),
    ("memory", "container.memory"),
    ("image", "image.id"),
    ("probe", "probe.java_version"),
])
def test_other_conditions_are_refused_without_writing_anything(h, capsys, change, message):
    h.finished_launch()
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
    assert not _runs_since(h, calls)


def test_a_slot_container_left_behind_is_refused(h, capsys):
    h.update(lambda d: d.setdefault("containers", []).append({
        "id": "f" * 64, "name": "ghidra-eval-other", "status": "exited",
        "labels": {"ghidra-eval.slot": "1", "ghidra-eval.eval": "other"}}))
    before = h.snapshot()
    assert h.start() == wrapper.EXIT_REFUSED
    assert "ghidra-eval-other (exited)" in capsys.readouterr().err
    assert h.snapshot() == before


def test_unobservable_slot_containers_refuse_the_start(h, capsys):
    h.fail("ps", -1)
    assert h.start() == wrapper.EXIT_REFUSED
    assert "cannot observe the evaluation-slot containers" in capsys.readouterr().err
    assert not h.ev.wrapper.exists()


def test_an_output_without_wrapper_records_is_refused(h, capsys):
    h.ev.out.mkdir(parents=True)
    (h.ev.out / "run_manifest.txt").write_text("run_kind=x\n")
    before = h.snapshot()
    assert h.start() == wrapper.EXIT_REFUSED
    assert "no wrapper record" in capsys.readouterr().err
    assert h.snapshot() == before


# ---------------------------------------------------------------------------
# 完了の判定は summary と同じ（review 1 P1-1）
# ---------------------------------------------------------------------------


def test_a_complete_evaluation_is_not_started_again_and_nothing_is_written(h, capsys):
    h.complete_evaluation()
    capsys.readouterr()
    assert h.run("summary", "--json") == 0
    assert json.loads(capsys.readouterr().out)["verdict"] == "COMPLETE"
    before = h.snapshot()
    calls = len(h.read_state()["calls"])
    assert h.start() == wrapper.EXIT_OK
    assert "The evaluation is complete" in capsys.readouterr().out
    assert h.snapshot() == before
    assert not _runs_since(h, calls)


def test_a_closed_chain_that_the_ledger_rejects_is_resumed_not_called_complete(h, capsys):
    """review 1 P1-1: chain は CLOSED でも ledger が正式性を拒否すれば完了ではない。"""
    h.complete_evaluation(end_overrides={"run_pair_failures": "1"})
    capsys.readouterr()
    assert h.run("summary", "--json") == 1
    result = json.loads(capsys.readouterr().out)
    assert result["gates"]["execution_chain"]["verdict"] == "CLOSED_SAME_IDENTITY"
    assert result["verdict"] == "INCOMPLETE"
    assert [r["code"] for r in result["reasons"]] == ["no_full_verdict"]
    calls = len(h.read_state()["calls"])
    assert h.start() == wrapper.EXIT_OK
    assert "The evaluation is complete" not in capsys.readouterr().out
    assert len(_runs_since(h, calls)) == 1


def test_start_and_summary_give_the_same_verdict_for_every_shape(h, capsys, monkeypatch):
    """start の判断は summarize.completion の verdict と理由の分類だけから決まる。"""
    seen = {}
    original = wrapper.start_decision

    def spy(completion):
        seen["completion"] = completion
        return original(completion)

    monkeypatch.setattr(wrapper, "start_decision", spy)
    h.complete_evaluation()
    assert h.start() == wrapper.EXIT_OK
    assert seen["completion"]["verdict"] == "COMPLETE"
    capsys.readouterr()
    assert h.run("summary", "--json") == 0
    summary = json.loads(capsys.readouterr().out)
    assert summary["verdict"] == seen["completion"]["verdict"]
    assert summary["reasons"] == seen["completion"]["reasons"] == []


@pytest.mark.parametrize("completion, decision", [
    (None, "launch"),
    ({"verdict": "COMPLETE", "reasons": []}, "complete"),
    ({"verdict": "INCOMPLETE", "reasons": [{"code": "chain_open", "category": "resumable"}]}, "launch"),
    ({"verdict": "INCOMPLETE", "reasons": [{"code": "chain_open", "category": "resumable"},
                                           {"code": "exit_unobserved", "category": "permanent"}]},
     "launch"),
    ({"verdict": "INCOMPLETE", "reasons": [{"code": "exit_unobserved", "category": "permanent"}]},
     "refuse"),
    ({"verdict": "INCOMPLETE", "reasons": [{"code": "chain_open", "category": "resumable"},
                                           {"code": "foreign_execution", "category": "blocking"}]},
     "refuse"),
    ({"verdict": "UNVERIFIABLE", "reasons": [{"code": "records_damaged", "category": "unverifiable"}]},
     "refuse"),
    ({"verdict": "INCOMPLETE", "reasons": [{"code": "x", "category": "something new"}]}, "refuse"),
])
def test_the_start_decision_reads_only_the_completion_categories(completion, decision):
    assert wrapper.start_decision(completion)[0] == decision


def test_an_execution_under_other_conditions_in_the_output_is_refused(h, capsys):
    assert h.start() == wrapper.EXIT_OK
    h.build_tree(fingerprint="eval-env-v1:" + "9" * 64)
    h.end_container(exit_code=0)
    h.wait_released()
    before = h.snapshot()
    assert h.start() == wrapper.EXIT_REFUSED
    assert "did not run under this evaluation's conditions" in capsys.readouterr().err
    assert h.snapshot() == before


# ---------------------------------------------------------------------------
# 再開・tmp の残骸
# ---------------------------------------------------------------------------


def test_leftover_run_tmpdirs_are_removed_only_by_the_next_start(h, capsys):
    h.finished_launch()
    leftover = h.ev.tmp / "neqbench-run.ABC123"
    (leftover / "pair.x").mkdir(parents=True)
    (leftover / "pair.x" / "store").write_text("x" * 100)
    before = h.snapshot()
    assert h.run("status") == wrapper.EXIT_OK
    assert "1 left by earlier executions" in capsys.readouterr().out
    assert h.snapshot() == before
    assert h.start() == wrapper.EXIT_OK
    assert not leftover.exists()
    launch = json.loads((h.ev.launch_dir(2) / records.LAUNCH).read_text())
    assert launch["removed_leftovers"] == [{"name": "neqbench-run.ABC123", "kind": "run_tmpdir",
                                            "bytes": 100}]
    (h.ev.tmp / "neqbench-run.NEW").mkdir()
    state = wrapper.container_state(h.ev)
    state["started_at"] = "2000-01-01T00:00:00.000000000Z"
    assert wrapper.tmp_entries(h.ev, state) == [{"name": "neqbench-run.NEW", "state": "current"}]


def test_a_refused_start_leaves_the_leftovers_of_earlier_executions_alone(h):
    h.finished_launch()
    leftover = h.ev.tmp / "neqbench-run.KEEP"
    leftover.mkdir()
    h.profile.write_text(PROFILE.replace("PARALLEL_JOBS=2", "PARALLEL_JOBS=3"))
    assert h.start() == wrapper.EXIT_REFUSED
    assert leftover.is_dir()


def test_an_output_stopped_before_its_start_record_is_moved_aside_not_deleted(h, capsys):
    h.finished_launch()
    (h.ev.out / "CLEVER" / "x").mkdir(parents=True)
    (h.ev.out / "neq_source_pairs.tsv").write_text("x\n")
    (h.ev.out / "pair-status-verification-key.json").write_text("{}")
    assert wrapper.never_recorded_a_start(h.ev.out)
    assert h.start() == wrapper.EXIT_OK
    launch = json.loads((h.ev.launch_dir(2) / records.LAUNCH).read_text())
    aside = Path(launch["moved_aside_output"])
    assert aside.parent == h.ev.wrapper / "aborted-outputs"
    assert (aside / "neq_source_pairs.tsv").read_text() == "x\n"
    assert not h.ev.out.exists()
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


# ---------------------------------------------------------------------------
# stop・失敗・回収（review 1 P1-2・P1-3）
# ---------------------------------------------------------------------------


def test_stop_uses_the_profiles_grace_and_waits_for_the_record(h, capsys):
    assert h.start() == wrapper.EXIT_OK
    assert h.run("stop") == wrapper.EXIT_OK
    stops = [c for c in h.read_state()["calls"] if c[0] == "stop"]
    assert stops == [["stop", "-t", "120", h.ev.container_name]]
    (launch,) = h.records().launches
    assert launch.state == records.STATE_RELEASED and launch.exit["exit_code"] == 143
    assert launch.exit["runner_exit_meaning"] == "stopped (TERM)"
    assert "runner exit 143" in capsys.readouterr().out


def test_a_failed_docker_stop_records_nothing_and_says_so(h, capsys):
    assert h.start() == wrapper.EXIT_OK
    h.fail("stop", 1)
    assert h.run("stop", "--wait", "2") == wrapper.EXIT_FAILED
    assert "docker stop failed" in capsys.readouterr().err
    assert h.records().unfinished is not None
    assert [c["status"] for c in h.containers()] == ["running"]


def test_stop_records_the_end_itself_when_the_supervisor_is_gone(h, capsys):
    assert h.start() == wrapper.EXIT_OK
    pid = (wrapper.lock_holders(h.ev) or [None])[0]
    assert pid is not None
    os.kill(pid, signal.SIGKILL)
    h.wait_for(lambda: wrapper.lock_holders(h.ev) is None, message="the lock to be released")
    # supervisor が居ない間も、slot の container が残っているので start は拒否される。
    assert h.start() == wrapper.EXIT_REFUSED
    assert h.run("stop") == wrapper.EXIT_OK
    assert "Recording launch 1" in capsys.readouterr().out
    (launch,) = h.records().launches
    assert launch.state == records.STATE_RELEASED and launch.exit["exit_code"] == 143
    assert h.containers() == []


@pytest.mark.parametrize("operation, kept", [("logs", "exit"), ("run-rm", "evidence"),
                                             ("rm", "released")])
def test_a_failed_external_operation_keeps_the_container_and_stop_continues(h, capsys, operation, kept):
    """review 1 P1-3: 取得できなかった結果は保存せず、container を残し、再試行できる。"""
    assert h.start() == wrapper.EXIT_OK
    h.fail(operation, 1)
    h.end_container(exit_code=0)
    h.wait_released()
    check = h.records()
    assert not check.problems
    assert check.unfinished is not None, f"a failed {operation} must leave the launch unfinished"
    assert [c["status"] for c in h.containers()] == ["exited"], "the container must be kept"
    directory = h.ev.launch_dir(1)
    if operation == "logs":
        assert not (directory / records.RUNNER_LOG).exists(), "the failure output must not be saved"
        assert check.unfinished.state == records.STATE_CONTAINER
    # 残った container が次の start を止める（記録の無い終了を見落とさない）。
    assert h.start() == wrapper.EXIT_REFUSED
    assert h.run("stop") == wrapper.EXIT_OK
    (launch,) = h.records().launches
    assert launch.state == records.STATE_RELEASED
    assert (directory / records.RUNNER_LOG).read_text().startswith("fake runner output")
    assert h.containers() == []


def test_an_unobservable_container_state_is_never_taken_as_absent(h):
    assert h.start() == wrapper.EXIT_OK
    h.fail("inspect", 3)
    h.end_container(exit_code=0)
    h.wait_released()
    (launch,) = h.records().launches
    # inspect が観測できない間は終了とせず、観測できてから記録する（exit_unobserved にしない）。
    assert launch.exit_kind == records.KIND_RAN
    assert launch.state == records.STATE_RELEASED


def test_a_container_whose_end_cannot_be_written_is_kept(h):
    assert h.start() == wrapper.EXIT_OK
    directory = h.ev.launch_dir(1)
    directory.chmod(0o500)
    try:
        h.end_container(exit_code=0)
        h.wait_released()
        assert not (directory / records.EXIT).exists()
        assert [c["status"] for c in h.containers()] == ["exited"]
    finally:
        directory.chmod(0o700)
    assert h.start() == wrapper.EXIT_REFUSED
    assert h.run("stop") == wrapper.EXIT_OK
    assert h.records().launches[0].state == records.STATE_RELEASED


def test_a_container_removed_outside_the_wrapper_is_recorded_as_unobserved(h, capsys):
    assert h.start() == wrapper.EXIT_OK
    h.build_tree()  # この launch の execution
    pid = (wrapper.lock_holders(h.ev) or [None])[0]
    os.kill(pid, signal.SIGKILL)
    h.wait_for(lambda: wrapper.lock_holders(h.ev) is None, message="the lock to be released")
    h.remove_containers()
    assert h.run("stop") == wrapper.EXIT_OK
    (launch,) = h.records().launches
    assert launch.state == records.STATE_RELEASED
    assert launch.exit_kind == records.KIND_EXIT_UNOBSERVED
    assert launch.exit["runtime_run_ids"] == [fixture._run_id(1), fixture._run_id(2)]
    capsys.readouterr()
    assert h.run("summary", "--json") == 1
    result = json.loads(capsys.readouterr().out)
    assert {r["code"]: r["category"] for r in result["reasons"]} == {"exit_unobserved": "permanent"}
    # 走らせても直らないので、start は何も書かずに拒否する（完了とも言わない）。
    before = h.snapshot()
    assert h.start() == wrapper.EXIT_REFUSED
    assert "running the runner again cannot fix it" in capsys.readouterr().err
    assert h.snapshot() == before


def test_a_launch_whose_container_never_started_is_recorded_and_retried(h):
    h.fail("run-d", 1)
    assert h.start() == wrapper.EXIT_FAILED
    h.wait_released()
    (launch,) = h.records().launches
    assert launch.state == records.STATE_RELEASED and launch.exit_kind == records.KIND_NOT_STARTED
    assert not h.records().problems  # 欠損ではない（記録は終端）
    assert h.start() == wrapper.EXIT_OK  # 同じ条件でそのまま再試行できる
    assert h.records().launches[1].container is not None


def test_a_container_created_by_a_failed_docker_run_is_found_and_recorded(h):
    h.update(lambda d: d.update({"create_on_failed_run": True}))
    h.fail("run-d", 1)
    h.start()  # docker run は失敗したが container は作られた: inspect で見つけて記録する
    h.wait_released()
    (launch,) = h.records().launches
    assert launch.state == records.STATE_RELEASED and launch.exit_kind == records.KIND_RAN
    assert launch.exit["runner_exit_meaning"] == "never started (created only)"
    assert "found by inspect" in launch.container["how"]
    assert h.containers() == []


def test_a_lost_docker_wait_does_not_end_the_watch(h):
    h.fail("wait", 1)
    assert h.start() == wrapper.EXIT_OK
    time.sleep(1.0)
    assert wrapper.lock_holders(h.ev), "the supervisor keeps watching the running container"
    h.end_container(exit_code=0)
    h.wait_released()
    (launch,) = h.records().launches
    assert launch.exit["exit_code"] == 0 and launch.state == records.STATE_RELEASED


def test_stop_refuses_damaged_records_and_changes_nothing(h, capsys):
    assert h.start() == wrapper.EXIT_OK
    pid = (wrapper.lock_holders(h.ev) or [None])[0]
    os.kill(pid, signal.SIGKILL)
    h.wait_for(lambda: wrapper.lock_holders(h.ev) is None, message="the lock to be released")
    h.end_container(exit_code=0)
    (h.ev.launch_dir(1) / records.CONTAINER).write_text("{broken")
    before = h.snapshot()
    assert h.run("stop") == wrapper.EXIT_FAILED
    assert "damaged" in capsys.readouterr().err
    assert h.snapshot() == before
    assert [c["status"] for c in h.containers()] == ["exited"]


# ---------------------------------------------------------------------------
# status / summary は読むだけ
# ---------------------------------------------------------------------------


def test_status_and_summary_write_nothing(h, capsys):
    h.complete_evaluation()
    before = h.snapshot()
    assert h.run("status", "--verify") == wrapper.EXIT_OK
    assert "CLOSED_SAME_IDENTITY" in capsys.readouterr().out
    assert h.run("summary") == 0
    assert "VERDICT: COMPLETE" in capsys.readouterr().out
    assert h.run("summary", "--json") == 0
    assert json.loads(capsys.readouterr().out)["schema"] == summarize.SUMMARY_SCHEMA
    assert h.snapshot() == before
    readers = [c for c in h.read_state()["calls"] if c[:2] == ["run", "--rm"]]
    assert readers and all(f"{h.main / 'logs'}:/workspace/logs:ro" in c for c in readers)


def test_summary_without_an_observed_container_state_cannot_judge(h, capsys):
    h.complete_evaluation()
    h.fail("inspect", -1)
    capsys.readouterr()
    assert h.run("summary", "--json") == 2
    result = json.loads(capsys.readouterr().out)
    assert result["verdict"] == "UNVERIFIABLE"
    assert "container_unobserved" in [r["code"] for r in result["reasons"]]


def test_observations_that_cannot_be_saved_are_counted_not_hidden(h):
    assert h.start() == wrapper.EXIT_OK
    watch = h.ev.launch_dir(1) / records.WATCH
    h.wait_for(watch.exists, message="the first observation")
    watch.chmod(0o400)
    time.sleep(1.0)
    h.end_container(exit_code=0)
    h.wait_released()
    watch.chmod(0o600)
    (launch,) = h.records().launches
    assert launch.state == records.STATE_RELEASED
    assert launch.exit["watch_write_failures"] > 0
    assert summarize._launch_view(launch)["watch_write_failures"] == launch.exit["watch_write_failures"]


def test_a_supervisor_without_the_lock_does_nothing(h, tmp_path):
    h.finished_launch()
    other = os.open(tmp_path / "not-the-lock", os.O_WRONLY | os.O_CREAT, 0o644)
    try:
        before = h.snapshot()
        assert wrapper.command_supervise(h.ev, 1, other) == wrapper.EXIT_FAILED
        assert h.snapshot() == before
    finally:
        os.close(other)


def test_start_refuses_while_a_launch_is_unfinished(h, capsys):
    mark = h.tmp / "crash.mark"
    h.cli("start", extra_env={"EVAL_TEST_CRASH": "start:supervise:before",
                              "EVAL_TEST_CRASH_MARK": str(mark)})
    before = h.snapshot()
    assert h.start() == wrapper.EXIT_REFUSED
    assert "launch 1 is unfinished (requested); run `stop`" in capsys.readouterr().err
    assert h.snapshot() == before
    assert h.run("stop") == wrapper.EXIT_OK
    (launch,) = h.records().launches
    assert launch.exit_kind == records.KIND_NOT_STARTED and launch.terminal
