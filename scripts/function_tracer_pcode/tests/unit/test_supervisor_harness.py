# -*- coding: utf-8 -*-
"""Issue #163: 共有 supervisor harness 自身の契約。

harness は #165（authority / recovery / crash 境界）の test が状態を**作る**
ための基盤なので、次のことを実 process で固定する。

* 名指した durable 境界で本当に止まる。
* supervisor の crash 後に restart できる。
* 孤児になった worker を必ず止める。
* launch の無い child は本処理に入らない。
* ``SupervisorRun`` は 1 回の invocation だけの観測で、crash / restart を
  挟んでも別 invocation の値（barrier 観測・projection・停止点・分類の対象）を
  引き継がない。
* 公開操作は、それが名乗る production 経路へ入れる durable state でだけ合法。
  restart は durable launch があるときだけで、無ければ何も起動せずに拒否する
  （fresh start へ黙って落ちない）。

ここでは supervisor がその状態から**どう判定すべきか**は固定しない（それは
#165 の test の責務で、harness に期待値を埋め込まない）。
"""

from __future__ import annotations

import json
import os
import subprocess

import pytest

from scripts.function_tracer_pcode.authority.process.supervisor_command import (
    CHILD_ENV_LAUNCH,
    CHILD_ENV_NONCE,
    CHILD_ENV_ROOT,
    CHILD_ENV_SUPERVISOR_KEY_FILE,
    CHILD_ENV_SUPERVISOR_KEY_ID,
    CHILD_ENV_WORKER_KEY_FILE,
    CHILD_ENV_WORKER_KEY_ID,
)
from scripts.function_tracer_pcode.tests.unit._supervisor_support import (
    LAUNCH_EVIDENCE_EXIT,
    REPO_ROOT,
    Checkpoint,
    ChildScript,
    ChildStopped,
    Deadline,
    Exit,
    FileBoundary,
    HarnessRecords,
    NoProjectionToClassify,
    NoWorkerStarted,
    ProjectionWrite,
    StaleRunObservation,
    Stop,
    SupervisorEntry,
    SupervisorEntryRefused,
    SupervisorPathMismatch,
    WorkerOutlivedSupervisor,
    classify,
    crash_at,
    launch_evidence,
    restart_supervisor,
    run_supervisor,
    stop_at,
    supervisor_case,
    worker_alive,
)


@pytest.mark.parametrize(
    ("boundary", "state", "present", "absent"),
    (
        # ACTIVE: 観測と ACTIVE checkpoint が commit され、continuation はまだ。
        (
            FileBoundary("continuation-stream.json", side="before"), "ACTIVE",
            {"checkpoint.json", "state.json"},
            {"continuation-stream.json", "continuation.json", "ready.json"},
        ),
        # continuation が durable で、state の CAS はまだ。
        (
            FileBoundary("continuation.json"), "ACTIVE",
            {"continuation-stream.json", "continuation.json"}, {"ready.json"},
        ),
        # READY へ CAS した直後、RESOLVED へはまだ。
        (
            FileBoundary("state.json", occurrence=2), "COMPLETION_READY",
            {"continuation.json", "ready.json"}, set(),
        ),
        # 停止点なし: checkpoint を閉じてから止まる。
        (None, "RESOLVED", {"continuation.json", "ready.json"}, set()),
    ),
    ids=("active", "continuation-before-cas", "ready", "resolved"),
)
def test_child_stops_at_the_named_durable_boundary(
    tmp_path, boundary, state, present, absent,
):
    faults = () if boundary is None else (stop_at(boundary),)
    script = ChildScript((Checkpoint(), Stop()), faults=faults)
    with supervisor_case(tmp_path, script) as case:
        run = run_supervisor(case, deadline=Deadline.AT_CHILD_STOP)
        at_stop = run.store_at_child_stop
        assert at_stop is not None, "the deadline did not wait for the child"
        assert at_stop.state == state
        assert present <= at_stop.files
        assert not absent & at_stop.files
        expected_fired = () if boundary is None else ({
            "role": "child", "pid": run.launch_evidence["pid"],
            "point": boundary.describe(), "action": "stop",
        },)
        assert run.faults_fired == expected_fired


def test_a_file_boundary_names_a_path_inside_the_store(tmp_path):
    """同名の file でも store 直下と history を取り違えない。

    2 つ目の checkpoint は 1 つ目の RESOLVED checkpoint を history へ移してから
    ACTIVE を書く。history 側の ``state.json`` が公開された直後に止めると、
    store 直下にはまだ ``state.json`` が無い（移した直後、新 ACTIVE の前）。
    """

    boundary = FileBoundary("checkpoint-history/*/state.json")
    script = ChildScript((Checkpoint(), Checkpoint(), Stop()), faults=(stop_at(boundary),))
    with supervisor_case(tmp_path, script) as case:
        run = run_supervisor(case, deadline=Deadline.AT_CHILD_STOP)
        at_stop = run.store_at_child_stop
        assert at_stop is not None
        assert [entry["point"] for entry in run.faults_fired] == [boundary.describe()]
        history = {name for name in at_stop.files if name.startswith("checkpoint-history/")}
        assert any(name.endswith("/state.json") for name in history)
        assert "state.json" not in at_stop.files


def test_supervisor_crash_at_a_durable_boundary_leaves_it_for_restart(tmp_path):
    with supervisor_case(tmp_path, ChildScript((Stop(),))) as case:
        run = run_supervisor(
            case, deadline=Deadline.AT_CHILD_STOP,
            faults=(crash_at(FileBoundary("claimed.json")),),
        )
        assert run.crashed is True
        assert run.exit_code is None
        assert run.projection is None
        assert [entry["role"] for entry in run.faults_fired] == ["supervisor"]
        assert run.faults_fired[0]["point"] == "after:claimed.json#1"
        assert run.store.has("claimed.json") and run.store.state == "ACTIVE"
        with pytest.raises(SupervisorEntryRefused, match="use restart_supervisor"):
            run_supervisor(case)

        restarted = restart_supervisor(case)
        assert restarted.crashed is False
        assert restarted.projection is not None
        launch = json.loads(
            (case.store_directory / "launch.json").read_text(encoding="utf-8")
        )
        assert restarted.projection["launch_receipt_digest"] == launch["receipt_digest"]


def test_worker_orphaned_by_a_supervisor_crash_is_stopped_when_the_case_closes(tmp_path):
    with pytest.raises(RuntimeError, match="test body failed"):
        with supervisor_case(tmp_path, ChildScript((Stop(),))) as case:
            run = run_supervisor(case, faults=(crash_at(ChildStopped()),))
            assert run.crashed is True
            assert worker_alive(run), "the crash should have orphaned the worker"
            raise RuntimeError("test body failed")
    assert not worker_alive(run)


def _worker_environment(case):
    environment = {
        key: value for key, value in os.environ.items()
        if not key.startswith("UNKNOWN_TAXONOMY_V2_")
    }
    config = case.config
    environment.update({
        CHILD_ENV_ROOT: str(config.checkpoint_root),
        CHILD_ENV_NONCE: config.execution_nonce,
        CHILD_ENV_LAUNCH: str(case.store_directory / "launch.json"),
        CHILD_ENV_SUPERVISOR_KEY_ID: config.supervisor_signing_key_id,
        CHILD_ENV_SUPERVISOR_KEY_FILE: str(config.supervisor_signing_key_file),
        CHILD_ENV_WORKER_KEY_ID: config.worker_signing_key_id,
        CHILD_ENV_WORKER_KEY_FILE: str(config.worker_signing_key_file),
    })
    return environment


def test_the_child_does_not_run_without_a_launch_that_names_it(tmp_path):
    """launch-before-exec の child 側検査が空虚でないこと。

    supervisor を通さずに同じ child を起こすと、(a) launch 無し、(b) 別 process
    （先に終わった worker）を名指す launch、のどちらでも本処理に入らない。
    """

    with supervisor_case(tmp_path, ChildScript((Exit(0),))) as case:
        finished = run_supervisor(case)
        assert finished.launch_evidence is not None
        assert launch_evidence(case, finished.child.pid) == (finished.launch_evidence,)

        bare = {
            key: value for key, value in os.environ.items()
            if not key.startswith("UNKNOWN_TAXONOMY_V2_")
        }
        for environment, reason in (
            (bare, b"launch.json is not durable at child start"),
            (_worker_environment(case), b"worker process identity differs from supervisor launch"),
        ):
            process = subprocess.Popen(
                case.config.child_command, cwd=REPO_ROOT, env=environment,
                stdout=subprocess.PIPE, stderr=subprocess.PIPE,
            )
            _, stderr = process.communicate(timeout=120)
            assert process.returncode == LAUNCH_EVIDENCE_EXIT, stderr
            assert reason in stderr, stderr
            assert launch_evidence(case, process.pid) == ()


# ---------------------------------------------------------------------------
# run identity と寿命: SupervisorRun は 1 回の invocation だけの観測
# ---------------------------------------------------------------------------


def test_a_restart_does_not_inherit_the_barrier_observation_of_a_crashed_run(tmp_path):
    with supervisor_case(tmp_path, ChildScript((Stop(),))) as case:
        first = run_supervisor(
            case, deadline=Deadline.AT_CHILD_STOP,
            faults=(crash_at(FileBoundary("claimed.json")),),
        )
        assert first.crashed is True
        assert first.launch_durable_at_barrier_release is True
        assert first.child is not None and first.launch_evidence is not None

        restarted = restart_supervisor(case)
        assert restarted.invocation != first.invocation
        # restart は barrier も worker も持たない。crash した run の値を読まない。
        assert restarted.launch_durable_at_barrier_release is None
        assert restarted.child is None
        assert restarted.launch_evidence is None
        assert restarted.store_at_child_stop is None
        assert restarted.faults_fired == ()


def test_a_run_that_crashes_before_projecting_reports_no_projection(tmp_path):
    """前の invocation の projection が残っていても、それを今の run の結果にしない。"""

    with supervisor_case(tmp_path, ChildScript((Exit(3),))) as case:
        first = run_supervisor(case)
        assert first.projection is not None
        assert case.config.authority_output.exists()

        crashed = restart_supervisor(case, faults=(crash_at(ProjectionWrite()),))
        assert crashed.crashed is True
        assert [entry["point"] for entry in crashed.faults_fired] == [
            ProjectionWrite().describe()
        ]
        assert crashed.projection is None
        # case の projection file はまだ前の invocation のもの（それを返さない）。
        left_behind = json.loads(case.config.authority_output.read_text(encoding="utf-8"))
        assert left_behind["projection_digest"] == first.projection["projection_digest"]


def test_every_invocation_has_its_own_identity_and_records(tmp_path):
    """crash -> crash -> restart でも identity と記録が衝突しない。"""

    with supervisor_case(tmp_path, ChildScript((Stop(),))) as case:
        first = run_supervisor(
            case, deadline=Deadline.AT_CHILD_STOP,
            faults=(crash_at(FileBoundary("state.json", occurrence=2)),),
        )
        second = restart_supervisor(case, faults=(crash_at(FileBoundary("timeout.json")),))
        third = restart_supervisor(case)
        runs = (first, second, third)
        assert [run.crashed for run in runs] == [True, True, False]
        assert len({run.invocation for run in runs}) == 3
        assert first.invocation < second.invocation < third.invocation
        assert [run.launch_durable_at_barrier_release for run in runs] == [True, None, None]
        assert [[entry["point"] for entry in run.faults_fired] for run in runs] == [
            ["after:state.json#2"], ["after:timeout.json#1"], [],
        ]
        assert [run.projection is None for run in runs] == [True, True, False]
        assert [run.exit_code for run in runs][:2] == [None, None]


def test_classification_names_the_run_it_classifies(tmp_path):
    """分類の対象は run。別の run の projection で代わりに分類しない。"""

    with supervisor_case(tmp_path, ChildScript((Exit(3),))) as case:
        first = run_supervisor(case)
        first_status = classify(first)
        assert first_status["canonical_outcome"] == "ERROR"
        assert first_status["classification_valid"] is True

        crashed = restart_supervisor(case, faults=(crash_at(ProjectionWrite()),))
        with pytest.raises(NoProjectionToClassify, match=str(crashed.invocation)):
            classify(crashed)

        restarted = restart_supervisor(case)
        assert restarted.projection is not None
        restarted_status = classify(restarted)
        assert restarted.invocation > crashed.invocation > first.invocation
        assert restarted_status["supervisor_projection_digest"] == (
            restarted.projection["projection_digest"]
        )
        assert restarted_status["canonical_outcome"] == "ERROR"
        # 2 つの run の projection は別物（restart は child の rc を持たない）で、
        # 前の run を分類し直しても後の run の projection を使わない。
        assert restarted.projection["projection_digest"] != first.projection["projection_digest"]
        assert classify(first)["supervisor_projection_digest"] == (
            first.projection["projection_digest"]
        )

        # ここまでの restart は store と pair log を変えないので first の組は
        # そのまま残っている（変わっていれば StaleRunObservation になる）。
        # あとで durable store が変われば、どの run の観測も分類の根拠にしない。
        (case.store_directory / "state.json").write_text("{}", encoding="utf-8")
        with pytest.raises(StaleRunObservation, match=str(restarted.invocation)):
            classify(restarted)


def test_a_crash_right_after_projecting_keeps_that_projection(tmp_path):
    """公開した直後に落ちた run の projection は、その run が公開した bytes。"""

    with supervisor_case(tmp_path, ChildScript((Exit(3),))) as case:
        run = run_supervisor(case, faults=(crash_at(ProjectionWrite(side="after")),))
        assert run.crashed is True and run.exit_code is None
        on_disk = json.loads(case.config.authority_output.read_text(encoding="utf-8"))
        assert run.projection == on_disk
        assert classify(run)["canonical_outcome"] == "ERROR"


def _allocate(root):
    return HarnessRecords(root).allocate_invocation().invocation.ordinal


def test_invocation_identities_stay_unique_across_concurrent_processes(tmp_path):
    """並行に起動した supervisor（#165 T15）でも identity が重複しない。"""

    import multiprocessing

    with multiprocessing.get_context("fork").Pool(8) as pool:
        ordinals = pool.map(_allocate, [tmp_path] * 32)
    assert sorted(ordinals) == list(range(32))


# ---------------------------------------------------------------------------
# 公開操作の state contract: 操作は、名乗る production 経路へ入れる durable
# state でだけ合法（「過去に invocation があった」ことは条件にしない）
# ---------------------------------------------------------------------------


def test_a_restart_is_refused_without_a_durable_launch(tmp_path):
    """launch を公開する前に落ちた case は、invocation があっても restart できない。"""

    with supervisor_case(tmp_path, ChildScript((Exit(3),))) as case:
        first = run_supervisor(
            case, faults=(crash_at(FileBoundary("launch.json", side="before")),),
        )
        assert first.crashed is True
        assert first.child is not None  # worker は起こした
        assert not first.store.has("launch.json")  # launch は durable でない
        with pytest.raises(SupervisorEntryRefused, match="use run_supervisor"):
            restart_supervisor(case)
        # 拒否は何も起動せず identity も消費しない。production と同じく次は fresh start。
        fresh = run_supervisor(case)
        assert fresh.invocation.ordinal == first.invocation.ordinal + 1
        assert fresh.entry is SupervisorEntry.FRESH_START
        assert fresh.child is not None and fresh.child != first.child
        assert fresh.launch_durable_at_barrier_release is True


def test_a_restart_resumes_once_the_launch_is_durable(tmp_path):
    with supervisor_case(tmp_path, ChildScript((Exit(3),))) as case:
        first = run_supervisor(
            case, faults=(crash_at(FileBoundary("launch.json", side="after")),),
        )
        assert first.crashed is True and first.store.has("launch.json")
        with pytest.raises(SupervisorEntryRefused, match="use restart_supervisor"):
            run_supervisor(case)
        restarted = restart_supervisor(case)
        assert restarted.entry is SupervisorEntry.RESUME
        assert restarted.child is None
        assert restarted.launch_durable_at_barrier_release is None
        with pytest.raises(NoWorkerStarted):
            worker_alive(restarted)


def test_restart_eligibility_does_not_depend_on_the_projection(tmp_path):
    """projection の有無は分類の可否で、restart の可否は durable launch で決まる。"""

    with supervisor_case(tmp_path, ChildScript((Exit(3),))) as case:
        first = run_supervisor(case, faults=(crash_at(ProjectionWrite()),))
        assert first.crashed is True and first.projection is None
        with pytest.raises(NoProjectionToClassify):
            classify(first)
        restarted = restart_supervisor(case)
        assert restarted.entry is SupervisorEntry.RESUME
        assert classify(restarted)["classification_valid"] is True


def test_requests_that_no_durable_state_allows_are_refused_before_starting(tmp_path):
    with supervisor_case(tmp_path, ChildScript((Exit(0),))) as case:
        with pytest.raises(SupervisorEntryRefused, match="use run_supervisor"):
            restart_supervisor(case)
        with pytest.raises(ValueError, match="only crash the supervisor"):
            run_supervisor(case, faults=(stop_at(FileBoundary("launch.json")),))
        # どの拒否も identity を消費していない。
        assert run_supervisor(case).invocation.ordinal == 0
        with pytest.raises(ValueError, match="no worker child to stop"):
            restart_supervisor(case, faults=(crash_at(ChildStopped()),))


def test_a_deadline_at_the_worker_stop_is_not_replaced_by_another_path(tmp_path):
    """worker が止まらなかった run を「止まった瞬間の deadline」の run と呼ばない。"""

    with supervisor_case(tmp_path, ChildScript((Exit(0),))) as case:
        with pytest.raises(SupervisorPathMismatch, match="never stopped"):
            run_supervisor(case, deadline=Deadline.AT_CHILD_STOP)


@pytest.mark.parametrize(
    ("script", "faults"),
    (
        # supervisor 側: 公開されない file / 回数に届かない公開 / 止まらない worker
        (ChildScript((Exit(3),)), (crash_at(FileBoundary("no-such.json")),)),
        (ChildScript((Exit(3),)), (crash_at(FileBoundary("launch.json", occurrence=5)),)),
        (ChildScript((Exit(3),)), (crash_at(ChildStopped()),)),
        # worker 側: 公開されない file で止まるはずだった worker
        (ChildScript((Exit(3),), faults=(stop_at(FileBoundary("no-such.json")),)), ()),
    ),
    ids=("unpublished-file", "unreached-occurrence", "worker-never-stops", "worker-point"),
)
def test_a_run_that_reaches_none_of_its_stop_points_is_not_a_normal_run(
    tmp_path, script, faults,
):
    """停止点を要求した run が停止点の無い経路を通ったら、それを返さない。"""

    with supervisor_case(tmp_path, script) as case:
        with pytest.raises(SupervisorPathMismatch, match="reached none"):
            run_supervisor(case, faults=faults)


def test_an_unknown_deadline_mode_is_refused_before_starting(tmp_path):
    with supervisor_case(tmp_path, ChildScript((Exit(0),))) as case:
        with pytest.raises(ValueError, match="unknown deadline mode"):
            run_supervisor(case, deadline="at_child_stop")
        assert run_supervisor(case).invocation.ordinal == 0


def test_a_worker_left_alive_by_a_returning_supervisor_is_reported(tmp_path, monkeypatch):
    """production の後始末を壊すと、harness は run を返さずに知らせる。

    監視の途中で例外を起こして ``_resume()`` へ逃がし、``finally`` の後始末を
    外す（test 側の monkeypatch。fork 先へ継承される）。止まった worker が
    生きたまま supervisor が戻る。
    """

    from scripts.function_tracer_pcode.authority.process import supervisor_command

    def _monitor_fails(self, process, diagnostic, deadline):
        raise RuntimeError("monitor failed")

    monkeypatch.setattr(
        supervisor_command.ProcessSupervisorCommand, "_wait_for_child_until_deadline",
        _monitor_fails,
    )
    monkeypatch.setattr(
        supervisor_command.ProcessSupervisorCommand, "_cleanup_exact_process_group",
        lambda self, process, start_token: "SKIPPED_BY_TEST",
    )
    with supervisor_case(tmp_path, ChildScript((Stop(),))) as case:
        with pytest.raises(WorkerOutlivedSupervisor, match="alive after the supervisor returned"):
            run_supervisor(case)
