# -*- coding: utf-8 -*-
"""Issue #163: 共有 supervisor harness 自身の契約。

harness は #165（authority / recovery / crash 境界）の test が状態を**作る**
ための基盤なので、「名指した durable 境界で本当に止まる」「supervisor の
crash 後に restart できる」「孤児になった worker を必ず止める」「launch の無い
child は本処理に入らない」を実 process で固定する。

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
    Stop,
    crash_at,
    launch_evidence_path,
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
        with pytest.raises(AssertionError, match="use restart_supervisor"):
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
            assert worker_alive(case), "the crash should have orphaned the worker"
            raise RuntimeError("test body failed")
    assert not worker_alive(case)


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
        evidence = set(case.records.glob("launch-evidence-*.json"))
        assert evidence == {
            launch_evidence_path(case.records, finished.launch_evidence["pid"])
        }

        bare = {
            key: value for key, value in os.environ.items()
            if not key.startswith("UNKNOWN_TAXONOMY_V2_")
        }
        for environment in (bare, _worker_environment(case)):
            process = subprocess.run(
                case.config.child_command, cwd=REPO_ROOT, env=environment,
                capture_output=True, timeout=120,
            )
            assert process.returncode == LAUNCH_EVIDENCE_EXIT, process.stderr
            assert set(case.records.glob("launch-evidence-*.json")) == evidence
