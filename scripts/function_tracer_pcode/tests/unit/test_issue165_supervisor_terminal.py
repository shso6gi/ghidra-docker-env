# -*- coding: utf-8 -*-
"""Issue #165: 実 child / 実 supervisor process での終端 authority と crash 復旧（T01〜T17）。

状態は PR #193 の共有 harness（``_supervisor_support``）だけで作る。worker は
production の broker / store / canonical 経路、supervisor は fork した
production の ``ProcessSupervisorCommand.run()``、分類は production の
``classify_pair_status``。どれも mock しない。

期待終端は ``tests/fixtures/issue165/terminal_model.py`` の oracle
（``expected_terminal``）から作る。oracle は ``next_step`` ではなく「child が
どこまで進み、どう終わり、E が durable になったか、mode、envelope」だけから
終端を決めるので、model の到達集合と実 store の結果は同じ仕様で照合される。

crash 復旧の決定性（T02 / T03 / T04 / T07）は、E が durable になった直後の
store を保存し、同じ場所へ戻してから各公開境界で supervisor を落として
restart する。どの境界から復旧しても projection は bytes まで同じ。
"""

from __future__ import annotations

import hashlib
import json
import os
from pathlib import Path
import shutil
import signal
import time

import pytest

from scripts.function_tracer_pcode.authority.contracts import authority_digest
from scripts.function_tracer_pcode.authority.process import terminal_evidence as te
from scripts.function_tracer_pcode.authority.process import terminal_recovery as tr
from scripts.function_tracer_pcode.authority.process.checkpoint_archive import (
    CHAIN_MEMBER_NAMES,
    live_chain_members,
)
from scripts.function_tracer_pcode.tests.fixtures.issue165 import terminal_model as model
from scripts.function_tracer_pcode.tests.unit._supervisor_store import inspect_store
from scripts.function_tracer_pcode.tests.unit._supervisor_support import (
    Checkpoint,
    ChildScript,
    Deadline,
    Envelope,
    Exit,
    FileBoundary,
    ProjectionWrite,
    Stop,
    SupervisorEntry,
    classify,
    crash_at,
    pause_at,
    restart_supervisor,
    run_supervisor,
    start_supervisor,
    stop_at,
    supervisor_case,
    worker_alive,
)

WORKER_CLOSED_MEMBERS = tuple(
    name for name in CHAIN_MEMBER_NAMES if name != "recovery-resolution.json"
)
ERROR_MEMBERS = model.ERROR_MEMBERS
HARNESS_CRASH_RC = 86


# ---------------------------------------------------------------------------
# 共通の観測
# ---------------------------------------------------------------------------


def _mode(runner: bool) -> tr.ExitMode:
    return (
        tr.ExitMode.CANONICAL_RESULT_REQUIRED if runner else tr.ExitMode.SUPERVISOR_ONLY
    )


def _expected(termination, *, runner, phase, envelope=None, exit_durable=True):
    """model の oracle（``next_step`` を通らない仕様）から期待終端を作る。"""

    scenario = model.Scenario(0, 0, termination, _mode(runner), envelope, exit_durable)
    return model.expected_terminal(scenario, phase)


def _store_json(case, name):
    path = case.store_directory / name
    return json.loads(path.read_text(encoding="utf-8")) if path.exists() else None


def _evidence(case):
    deadline = _store_json(case, te.DEADLINE_FILENAME)
    child_exit = _store_json(case, te.CHILD_EXIT_FILENAME)
    return (
        None if deadline is None else deadline,
        None if child_exit is None else child_exit,
    )


def _assert_terminal(run, expected):
    """projection・supervisor の rc・分類が期待終端（oracle）と一致する。"""

    kind, detail = expected
    projection = run.projection
    if kind == "INVALID":
        assert projection["status"] == "INVALID", projection
        assert projection["error_code"] == detail, projection
        assert projection["error_detail"]
        assert run.exit_code == 2
        with pytest.raises(ValueError, match="not a terminal authority"):
            classify(run)
        return None
    classified = classify(run)
    assert classified["classification_valid"] is True
    if kind == "TIMEOUT":
        assert (run.exit_code, projection["status"]) == (124, "TIMEOUT")
        assert classified["canonical_outcome"] == "TIMEOUT"
    elif kind == "ERROR":
        assert projection["status"] == "ERROR"
        assert classified["canonical_outcome"] == "ERROR"
        error = _store_json(run.case, "operational-error.json")
        assert error["payload"]["deadline_stage"] == detail
    else:
        assert (run.exit_code, projection["status"]) == (0, "RESOLVED")
    # 終端の projection の rc は E が観測した rc そのもの。
    _deadline, child_exit = _evidence(run.case)
    assert projection["child_returncode"] == child_exit["payload"]["child_returncode"]
    return classified


def _factory(case):
    from scripts.function_tracer_pcode.authority.process.supervisor import (
        ProcessSupervisorAuthorityFactory,
    )

    keys = case.keys
    return ProcessSupervisorAuthorityFactory(
        supervisor_signing_key_id=keys.supervisor_key_id,
        supervisor_signing_key=keys.supervisor_key_file.read_bytes(),
        worker_signing_key_id=keys.worker_key_id,
        worker_signing_key=keys.worker_key_file.read_bytes(),
        terminal_evidence_signing_key_id=keys.terminal_evidence_key_id,
        terminal_evidence_signing_key=keys.terminal_evidence_key_file.read_bytes(),
    )


def _store(case):
    from scripts.function_tracer_pcode.authority.process.supervisor import (
        DurableCheckpointStore,
    )

    return DurableCheckpointStore(
        case.config.checkpoint_root, _factory(case), case.config.execution_nonce,
    )


def _save_store(case):
    saved = case.directory / "saved-store"
    shutil.rmtree(saved, ignore_errors=True)
    shutil.copytree(case.store_directory, saved)
    return saved


def _restore_store(case, saved):
    shutil.rmtree(case.store_directory)
    shutil.copytree(saved, case.store_directory)


def _restart_unchanged(case, expected_code):
    """INVALID を返す restart は store に何も書かない（書込み前の拒否）。"""

    before = inspect_store(case.store_directory).digests
    run = restart_supervisor(case)
    assert run.projection["status"] == "INVALID", run.projection
    assert run.projection["error_code"] == expected_code, run.projection
    assert inspect_store(case.store_directory).digests == before
    return run


def _history_directories(case):
    root = case.store_directory / "checkpoint-history"
    return sorted(path for path in root.iterdir()) if root.is_dir() else []


# ---------------------------------------------------------------------------
# T01: D + E × checkpoint の段階 → TIMEOUT
# ---------------------------------------------------------------------------

#: child が deadline の瞬間に止まっていた場所（worker の公開境界）と model の段階。
CHECKPOINT_STAGES = {
    "none": ((Stop(),), (), "NONE"),
    "active": ((Checkpoint(), Stop()), (stop_at(FileBoundary("state.json", 1)),), "ACTIVE"),
    "active-continuation": (
        (Checkpoint(), Stop()), (stop_at(FileBoundary("continuation.json")),), "ACTIVE_CONT",
    ),
    # worker が ready.json を公開し state を READY へ替える前（worker の READY を採る）。
    "ready-before-cas": (
        (Checkpoint(), Stop()), (stop_at(FileBoundary("ready.json")),), "ACTIVE_CONT",
    ),
    "ready": (
        (Checkpoint(), Stop()), (stop_at(FileBoundary("state.json", 2)),), "COMPLETION_READY",
    ),
    "resolved": ((Checkpoint(), Stop()), (), "RESOLVED"),
}


@pytest.mark.parametrize("stage", tuple(CHECKPOINT_STAGES))
def test_t01_deadline_and_exit_evidence_timeout_at_every_checkpoint_stage(tmp_path, stage):
    steps, faults, phase = CHECKPOINT_STAGES[stage]
    with supervisor_case(
        tmp_path, ChildScript(steps, faults=faults), allow_child_exit_resolution=True,
    ) as case:
        run = run_supervisor(case, deadline=Deadline.AT_CHILD_STOP)
        _assert_terminal(run, _expected("deadline", runner=True, phase=phase))
        deadline, child_exit = _evidence(case)
        assert deadline is not None and child_exit is not None
        assert child_exit["payload"]["deadline_receipt_digest"] == deadline["receipt_digest"]
        assert child_exit["payload"]["child_returncode"] == -15
        assert child_exit["payload"]["child_exit_disposition"] == "SIGTERM_AFTER_DEADLINE"
        assert child_exit["payload"]["signal_actions"] == [
            {"signal": "SIGTERM", "result": "sent"},
        ]
        assert run.projection["child_exit_disposition"] == "SIGTERM_AFTER_DEADLINE"
        assert run.projection["child_returncode_observation_kind"] == "LIVE_PROCESS_WAIT"
        # D も E も terminal-evidence 鍵で署名されている（worker の鍵ではない）。
        assert deadline["signing_key_id"] == child_exit["signing_key_id"] == (
            case.keys.terminal_evidence_key_id
        )


# ---------------------------------------------------------------------------
# T02 / T03 / T04: timeout transaction の各公開境界からの復旧
# ---------------------------------------------------------------------------

BOOTSTRAP_BOUNDARIES = (
    FileBoundary("pending-active-transaction.json", side="before"),
    FileBoundary("pending-active-transaction.json"),
    *(FileBoundary(f"checkpoint-history/*/{name}") for name in WORKER_CLOSED_MEMBERS),
    FileBoundary("checkpoint-prefix-stream.json"),
    FileBoundary("checkpoint.json"),
    FileBoundary("state.json", 1),
)
CLAIM_BOUNDARIES = (
    FileBoundary("claimed.json", side="before"),
    FileBoundary("claimed.json"),
    FileBoundary("state.json", 2, side="before"),
    FileBoundary("state.json", 2),
)
FINALIZE_BOUNDARIES = (
    FileBoundary("timeout.json"),
    FileBoundary("terminal-segment.json"),
    FileBoundary("terminal-stream.json"),
    FileBoundary("state.json", 3, side="before"),
    FileBoundary("state.json", 3),
    ProjectionWrite(side="before"),
    ProjectionWrite(side="after"),
)


def _deadline_case_after_exit(tmp_path):
    """RESOLVED checkpoint の child を deadline で止め、E が durable の直後で落とす。"""

    context = supervisor_case(
        tmp_path, ChildScript((Checkpoint(), Stop())), allow_child_exit_resolution=True,
    )
    case = context.__enter__()
    first = run_supervisor(
        case, deadline=Deadline.AT_CHILD_STOP,
        faults=(crash_at(FileBoundary(te.CHILD_EXIT_FILENAME)),),
    )
    assert first.crashed and first.store.has(te.CHILD_EXIT_FILENAME)
    return context, case


def _projection_from_every_boundary(case, boundaries, expected):
    saved = _save_store(case)
    control = restart_supervisor(case)
    _assert_terminal(control, expected)
    results = {}
    for boundary in boundaries:
        _restore_store(case, saved)
        crashed = restart_supervisor(case, faults=(crash_at(boundary),))
        assert crashed.crashed, boundary
        resumed = restart_supervisor(case)
        _assert_terminal(resumed, expected)
        results[boundary.describe()] = resumed.projection
    for point, projection in results.items():
        assert projection == control.projection, point
    return control


@pytest.mark.parametrize(("test_id", "boundaries"), (
    ("T02-bootstrap", BOOTSTRAP_BOUNDARIES),
    ("T03-claim", CLAIM_BOUNDARIES),
    ("T04-finalize-and-projection", FINALIZE_BOUNDARIES),
))
def test_t02_t03_t04_timeout_transaction_recovers_the_same_terminal_from_every_boundary(
    tmp_path, test_id, boundaries,
):
    context, case = _deadline_case_after_exit(tmp_path)
    try:
        control = _projection_from_every_boundary(
            case, boundaries, _expected("deadline", runner=True, phase="RESOLVED"),
        )
        # bootstrap の前任（child の RESOLVED chain）は history にある。
        assert len(_history_directories(case)) == 1
        assert control.projection["child_exit_disposition"] == "SIGTERM_AFTER_DEADLINE"
    finally:
        context.__exit__(None, None, None)


def test_t03_a_different_durable_claim_is_rejected_not_overwritten(tmp_path):
    from scripts.function_tracer_pcode.authority.process.supervisor import (
        _TRANSITION_CAPABILITY_TOKEN,
        CheckpointState,
    )

    with supervisor_case(
        tmp_path, ChildScript((Checkpoint(), Stop()),
                              faults=(stop_at(FileBoundary("state.json", 1)),)),
        allow_child_exit_resolution=True,
    ) as case:
        first = run_supervisor(
            case, deadline=Deadline.AT_CHILD_STOP,
            faults=(crash_at(FileBoundary("claimed.json", side="before")),),
        )
        assert first.crashed
        store = _store(case)
        active = store.read_state()
        other = store.factory._issue_transition(
            prior=active, next_state=CheckpointState.TIMED_OUT_CLAIMED,
            lock_directory_digest=store.lock_directory_digest,
            kill_disposition="SIGKILL_AFTER_DEADLINE",
            _capability=_TRANSITION_CAPABILITY_TOKEN,
        )
        (case.store_directory / "claimed.json").write_bytes(store._bytes(other))
        run = _restart_unchanged(case, "TERMINAL_AUTHORITY_CONFLICT")
        assert "claim disposition" in run.projection["error_detail"]


# ---------------------------------------------------------------------------
# T05 / T06: 自然終了（envelope 無し）
# ---------------------------------------------------------------------------

#: child の自然終了（step の Exit、または worker の公開境界での os._exit）。
NATURAL_EXITS = {
    "no-checkpoint": ((Exit(3),), (), "NONE", 3),
    "resolved": ((Checkpoint(), Exit(1)), (), "RESOLVED", 1),
    "ready": ((Checkpoint(), Stop()), (crash_at(FileBoundary("state.json", 2)),),
              "COMPLETION_READY", HARNESS_CRASH_RC),
    "active-continuation": ((Checkpoint(), Stop()),
                            (crash_at(FileBoundary("continuation.json")),),
                            "ACTIVE_CONT", HARNESS_CRASH_RC),
    "ready-before-cas": ((Checkpoint(), Stop()), (crash_at(FileBoundary("ready.json")),),
                         "ACTIVE_CONT", HARNESS_CRASH_RC),
    "active": ((Checkpoint(), Stop()), (crash_at(FileBoundary("state.json", 1)),),
               "ACTIVE", HARNESS_CRASH_RC),
    "pending": ((Checkpoint(), Stop()),
                (crash_at(FileBoundary("pending-active-transaction.json")),),
                "PENDING", HARNESS_CRASH_RC),
}


@pytest.mark.parametrize("runner", (False, True), ids=("supervisor-only", "runner"))
@pytest.mark.parametrize("scenario", tuple(NATURAL_EXITS))
def test_t05_t06_natural_exit_without_envelope(tmp_path, scenario, runner):
    steps, faults, phase, rc = NATURAL_EXITS[scenario]
    expected = _expected("natural", runner=runner, phase=phase)
    with supervisor_case(
        tmp_path, ChildScript(steps, faults=faults), allow_child_exit_resolution=runner,
    ) as case:
        run = run_supervisor(case)
        _assert_terminal(run, expected)
        _deadline, child_exit = _evidence(case)
        assert _deadline is None
        assert child_exit["payload"]["child_returncode"] == rc
        assert child_exit["payload"]["child_exit_disposition"] == f"EXIT_CODE_{rc}"
        assert child_exit["payload"]["signal_actions"] == []
        archive = _store_json(case, te.ARCHIVE_INTENT_FILENAME)
        if expected == ("ERROR", tr.STAGE_NON_DECOMPILATION):
            # 閉じた chain を A で固定して history へ移し、live に chain は残らない。
            assert archive is not None and archive["payload"]["error_stage"] == expected[1]
            assert live_chain_members(case.store_directory) == ()
            destination = case.store_directory / archive["payload"]["destination"]
            assert sorted(p.name for p in destination.iterdir()) == sorted(
                member["name"] for member in archive["payload"]["members"]
            )
            assert run.projection["child_exit_disposition"] == f"EXIT_CODE_{rc}"
        else:
            # ERROR にしない終わり方（BEFORE_CHECKPOINT の ERROR 以外）は A を作らない。
            assert archive is None
        if expected[0] == "INVALID":
            assert not any(case.store_directory.joinpath(m).exists() for m in ERROR_MEMBERS)
            assert run.projection["child_returncode"] == rc


# ---------------------------------------------------------------------------
# T07 / T08 / T09: archive transaction
# ---------------------------------------------------------------------------

ARCHIVE_BOUNDARIES = (
    FileBoundary(te.ARCHIVE_INTENT_FILENAME, side="before"),
    FileBoundary(te.ARCHIVE_INTENT_FILENAME),
    *(FileBoundary(f"checkpoint-history/*/{name}") for name in WORKER_CLOSED_MEMBERS),
    *(FileBoundary(name) for name in ERROR_MEMBERS),
    ProjectionWrite(side="before"),
    ProjectionWrite(side="after"),
)


def _archive_case(tmp_path, *, checkpoints=1, crash=FileBoundary(te.CHILD_EXIT_FILENAME)):
    context = supervisor_case(
        tmp_path, ChildScript(tuple(Checkpoint() for _ in range(checkpoints)) + (Exit(1),)),
    )
    case = context.__enter__()
    first = run_supervisor(case, faults=(crash_at(crash),))
    assert first.crashed
    return context, case


def test_t07_archive_and_error_recover_the_same_error_from_every_boundary(tmp_path):
    context, case = _archive_case(tmp_path)
    try:
        expected = _expected("natural", runner=False, phase="RESOLVED")
        control = _projection_from_every_boundary(case, ARCHIVE_BOUNDARIES, expected)
        assert control.projection["child_exit_disposition"] == "EXIT_CODE_1"
        assert _store_json(case, "operational-error.json")["payload"]["deadline_stage"] == (
            tr.STAGE_NON_DECOMPILATION
        )
    finally:
        context.__exit__(None, None, None)


def _tamper_history_member(case):
    target = _history_directories(case)[0] / "checkpoint.json"
    target.write_bytes(target.read_bytes().replace(b'"', b"'", 1))


def _delete_moved_member(case):
    (_history_directories(case)[0] / "checkpoint-prefix-stream.json").unlink()


def _live_copy_differs(case):
    (case.store_directory / "checkpoint.json").write_text("{}", encoding="utf-8")


def _tamper_signed(name, field):
    def mutate(case):
        path = case.store_directory / name
        body = json.loads(path.read_text(encoding="utf-8"))
        payload = body["payload"]
        if field == "members":
            payload["members"][0]["sha256"] = "0" * 64
        else:
            payload[field] = 0
        path.write_text(json.dumps(body, sort_keys=True), encoding="utf-8")
    return mutate


@pytest.mark.parametrize(("mutate", "code"), (
    (_tamper_history_member, "ARCHIVE_UNION_CONFLICT"),
    (_delete_moved_member, "ARCHIVE_UNION_CONFLICT"),
    (_live_copy_differs, "ARCHIVE_UNION_CONFLICT"),
    (_tamper_signed(te.ARCHIVE_INTENT_FILENAME, "members"), "TERMINAL_EVIDENCE_INVALID"),
    (_tamper_signed(te.CHILD_EXIT_FILENAME, "child_returncode"), "TERMINAL_EVIDENCE_INVALID"),
), ids=("history-member", "both-sides-missing", "live-history-mismatch", "manifest", "exit"))
def test_t08_a_tampered_archive_is_rejected_before_any_write(tmp_path, mutate, code):
    context, case = _archive_case(
        tmp_path, crash=FileBoundary("checkpoint-history/*/continuation-stream.json"),
    )
    try:
        mutate(case)
        _restart_unchanged(case, code)
    finally:
        context.__exit__(None, None, None)


def test_t09_a_live_chain_outside_the_anchor_is_protected_and_invalid(tmp_path):
    """E が観測した chain（c2）でない live chain（c1 を戻したもの）は書き換えない。"""

    context, case = _archive_case(tmp_path, checkpoints=2)
    try:
        store_dir = case.store_directory
        (history,) = _history_directories(case)
        aside = case.directory / "c2-aside"
        aside.mkdir()
        for name in live_chain_members(store_dir):
            os.replace(store_dir / name, aside / name)
        for name in WORKER_CLOSED_MEMBERS:
            shutil.copy2(history / name, store_dir / name)
        _restart_unchanged(case, "ANCHOR_OUTSIDE_LIVE_CHAIN")
    finally:
        context.__exit__(None, None, None)


def test_t09_a_new_live_chain_during_archive_stops_the_archive(tmp_path):
    context, case = _archive_case(
        tmp_path, checkpoints=2,
        crash=FileBoundary("checkpoint-history/*/continuation.json"),
    )
    try:
        store_dir = case.store_directory
        histories = {path.name: sorted(p.name for p in path.iterdir())
                     for path in _history_directories(case)}
        archive = _store_json(case, te.ARCHIVE_INTENT_FILENAME)
        c1 = next(
            path for path in _history_directories(case)
            if path.name != archive["payload"]["destination"].split("/")[-1]
        )
        # 移動済みの checkpoint.json の名前に、別の chain（c1）の checkpoint が現れる。
        shutil.copy2(c1 / "checkpoint.json", store_dir / "checkpoint.json")
        _restart_unchanged(case, "ARCHIVE_UNION_CONFLICT")
        assert {path.name: sorted(p.name for p in path.iterdir())
                for path in _history_directories(case)} == histories
    finally:
        context.__exit__(None, None, None)


@pytest.mark.parametrize("deadline", (False, True), ids=("error", "timeout"))
def test_t09_unrelated_old_history_is_not_associated(tmp_path, deadline):
    steps = (Checkpoint(), Checkpoint()) + ((Stop(),) if deadline else (Exit(1),))
    with supervisor_case(tmp_path, ChildScript(steps)) as case:
        run = run_supervisor(case, deadline=Deadline.AT_CHILD_STOP if deadline else Deadline.TIMER)
        phase = "RESOLVED"
        _assert_terminal(run, _expected(
            "deadline" if deadline else "natural", runner=False, phase=phase,
        ))
        _deadline, child_exit = _evidence(case)
        anchor = child_exit["payload"]["checkpoint_anchor"]
        # E が名指すのは最後の chain（c2）。c1 の history は別 chain のまま残る。
        assert anchor["kind"] == "CHAIN"
        assert len(_history_directories(case)) == 2


# ---------------------------------------------------------------------------
# T10 / T16: D だけの restart、D / E 書込み窓（kill の前後、自然終了の前後）
# ---------------------------------------------------------------------------


def test_t10_deadline_only_restart_with_the_child_alive_is_invalid_and_does_not_kill(tmp_path):
    with supervisor_case(tmp_path, ChildScript((Stop(),)), allow_child_exit_resolution=True) as case:
        first = run_supervisor(
            case, deadline=Deadline.AT_CHILD_STOP,
            faults=(crash_at(FileBoundary(te.DEADLINE_FILENAME)),),
        )
        assert first.crashed and worker_alive(first)
        run = _restart_unchanged(case, "DEADLINE_WITHOUT_EXIT_OBSERVATION")
        assert run.projection["child_returncode"] is None
        assert run.projection["diagnostics"]["child_alive_at_decision"] is True
        assert run.projection["diagnostics"]["child_pid"] == first.child.pid
        assert worker_alive(first), "the restart must not kill or reap the orphan"
        assert not run.store.has(te.CHILD_EXIT_FILENAME)


def test_t10_deadline_only_restart_with_the_child_dead_is_invalid(tmp_path):
    with supervisor_case(tmp_path, ChildScript((Stop(),)), allow_child_exit_resolution=True) as case:
        first = run_supervisor(
            case, deadline=Deadline.AT_CHILD_STOP,
            faults=(crash_at(FileBoundary(te.CHILD_EXIT_FILENAME, side="before")),),
        )
        assert first.crashed and not worker_alive(first)
        run = _restart_unchanged(case, "DEADLINE_WITHOUT_EXIT_OBSERVATION")
        assert run.projection["child_returncode"] is None
        assert run.projection["diagnostics"]["child_alive_at_decision"] is False


@pytest.mark.parametrize(("termination", "boundary", "exit_durable", "alive_after"), (
    ("deadline", FileBoundary(te.DEADLINE_FILENAME, side="before"), False, True),
    ("deadline", FileBoundary(te.DEADLINE_FILENAME), False, True),
    ("deadline", FileBoundary(te.CHILD_EXIT_FILENAME, side="before"), False, False),
    ("deadline", FileBoundary(te.CHILD_EXIT_FILENAME), True, False),
    ("natural", FileBoundary(te.CHILD_EXIT_FILENAME, side="before"), False, False),
    ("natural", FileBoundary(te.CHILD_EXIT_FILENAME), True, False),
), ids=("before-D", "after-D", "after-kill-before-E", "after-E",
        "natural-before-E", "natural-after-E"))
def test_t16_exit_observation_windows_around_eof_and_kill(
    tmp_path, termination, boundary, exit_durable, alive_after,
):
    steps = (Stop(),) if termination == "deadline" else (Exit(3),)
    runner = termination == "deadline"
    with supervisor_case(tmp_path, ChildScript(steps), allow_child_exit_resolution=runner) as case:
        first = run_supervisor(
            case,
            deadline=Deadline.AT_CHILD_STOP if termination == "deadline" else Deadline.TIMER,
            faults=(crash_at(boundary),),
        )
        assert first.crashed
        expected = _expected(termination, runner=runner, phase="NONE", exit_durable=exit_durable)
        if boundary.path == te.DEADLINE_FILENAME and boundary.side == "before":
            # D が durable になる前: restart から見れば終了の観測が 1 つも無い。
            expected = ("INVALID", "EXIT_NOT_OBSERVED")
        restarted = restart_supervisor(case)
        _assert_terminal(restarted, expected)
        assert worker_alive(first) is alive_after
        if exit_durable:
            _deadline, child_exit = _evidence(case)
            rc = child_exit["payload"]["child_returncode"]
            assert rc == (-15 if termination == "deadline" else 3)
            assert restarted.projection["child_returncode"] == rc


# ---------------------------------------------------------------------------
# T11: race A / B / C（D の直後で supervisor を止める）
# ---------------------------------------------------------------------------


def _zombie(pid: int) -> bool:
    stat = Path(f"/proc/{pid}/stat").read_text(encoding="utf-8")
    return stat[stat.rfind(")") + 2] == "Z"


@pytest.mark.parametrize(("race", "stop", "disposition", "rc", "signals"), (
    ("A-exit-before-signal", Stop(exit_on_sigusr1=2), "EXITED_2", 2, []),
    ("B-exit-after-signal", Stop(exit_on_sigterm=2), "EXITED_2_AFTER_SIGTERM", 2,
     [{"signal": "SIGTERM", "result": "sent"}]),
    ("C-signal-death", Stop(), "SIGTERM_AFTER_DEADLINE", -15,
     [{"signal": "SIGTERM", "result": "sent"}]),
), ids=lambda value: value if isinstance(value, str) and value[0] in "ABC" else None)
def test_t11_deadline_races_keep_the_observed_disposition_and_do_not_adopt_the_envelope(
    tmp_path, race, stop, disposition, rc, signals,
):
    script = ChildScript((Checkpoint(), Envelope("UNKNOWN"), stop))
    with supervisor_case(tmp_path, script, allow_child_exit_resolution=True) as case:
        point = FileBoundary(te.DEADLINE_FILENAME)
        with start_supervisor(
            case, entry=SupervisorEntry.FRESH_START, deadline=Deadline.AT_CHILD_STOP,
            faults=(pause_at(point),),
        ) as handle:
            handle.wait_until_paused(point.describe())
            # D は durable、signal はまだ。
            assert (case.store_directory / te.DEADLINE_FILENAME).exists()
            child = handle.child()
            if race.startswith("A"):
                os.kill(child.pid, signal.SIGUSR1)
                limit = time.monotonic() + 30
                while not _zombie(child.pid):
                    assert time.monotonic() < limit, "the child did not exit"
                    time.sleep(0.01)
            handle.release()
            run = handle.wait()
        _assert_terminal(run, _expected("deadline", runner=True, phase="RESOLVED"))
        assert run.projection["child_exit_disposition"] == disposition
        assert run.projection["child_returncode"] == rc
        _deadline, child_exit = _evidence(case)
        assert child_exit["payload"]["signal_actions"] == signals
        # 有効な envelope が durable にあっても、D が先なので RESOLVED にしない（P-T）。
        assert child_exit["payload"]["envelope_observation"]["present"] is True
        assert not run.store.has("canonical-resolved-receipt.json")


# ---------------------------------------------------------------------------
# T12 / T17: canonical 結果（CLI join）と対照
# ---------------------------------------------------------------------------


@pytest.mark.parametrize(("steps", "expected"), (
    ((Checkpoint(), Envelope("UNKNOWN"), Exit()), ("RESOLVED", None)),
    ((Checkpoint(), Envelope("UNKNOWN"), Exit(0)), ("INVALID", "CANONICAL_CHILD_RESULT_INVALID")),
    ((Checkpoint(), Envelope("UNKNOWN", corrupt="envelope_digest"), Exit()),
     ("INVALID", "CANONICAL_CHILD_RESULT_INVALID")),
    ((Checkpoint(), Envelope("UNKNOWN", corrupt="canonical_result_bundle_digest", reseal=True),
      Exit()), ("INVALID", "CANONICAL_CHILD_RESULT_INVALID")),
), ids=("cli-join", "cli-mismatch", "corrupt-seal", "corrupt-join"))
def test_t12_only_a_valid_envelope_that_joins_the_observed_rc_resolves(tmp_path, steps, expected):
    with supervisor_case(tmp_path, ChildScript(steps), allow_child_exit_resolution=True) as case:
        run = run_supervisor(case)
        _assert_terminal(run, expected)
        restarted = restart_supervisor(case)
        assert restarted.projection == run.projection


@pytest.mark.parametrize("outcome", ("UNKNOWN", "TIMEOUT", "ERROR"))
def test_t17_canonical_child_results_resolve_with_the_observed_exit(tmp_path, outcome):
    script = ChildScript((Checkpoint(), Envelope(outcome), Exit()))
    with supervisor_case(tmp_path, script, allow_child_exit_resolution=True) as case:
        run = run_supervisor(case)
        classified = _assert_terminal(run, ("RESOLVED", None))
        assert classified["canonical_outcome"] == outcome
        deadline, child_exit = _evidence(case)
        assert deadline is None
        envelope = (case.store_directory / "canonical-result-envelope.json").read_bytes()
        assert child_exit["payload"]["envelope_observation"] == {
            "present": True, "sha256": hashlib.sha256(envelope).hexdigest(),
        }
        receipt = _store_json(case, "canonical-resolved-receipt.json")
        assert receipt["child_returncode"] == child_exit["payload"]["child_returncode"]
        assert run.projection["supervisor_final_authority_digest"] == receipt["receipt_digest"]
        if outcome == "ERROR":
            assert classified["error_kind"] == "supervisor_harness_error"


# ---------------------------------------------------------------------------
# T13: 競合と改ざん（完成した終端があっても先に INVALID）
# ---------------------------------------------------------------------------


def _forge_error_receipt(case, *, disposition):
    from scripts.function_tracer_pcode.authority.process.supervisor import (
        _OPERATIONAL_ERROR_CAPABILITY_TOKEN,
    )

    store = _store(case)
    launch = store._read_launch()
    error = store.factory._issue_operational_error(
        launch=launch, error_kind="operational_authority_invalid",
        deadline_stage="BEFORE_CHECKPOINT", child_exit_disposition=disposition,
        _capability=_OPERATIONAL_ERROR_CAPABILITY_TOKEN,
    )
    (case.store_directory / "operational-error.json").write_bytes(store._bytes(error))


def _forge_deadline(case):
    store = _store(case)
    launch = store._read_launch()
    deadline = store.factory.issue_terminal_evidence(
        te.DEADLINE_RECEIPT_KIND,
        te.deadline_payload(launch, configured_timeout_seconds=60.0,
                            deadline_detected_offset_seconds=60.0),
    )
    (case.store_directory / te.DEADLINE_FILENAME).write_bytes(store._bytes(deadline))


def _edit_byte(name):
    def mutate(case):
        path = case.store_directory / name
        data = path.read_bytes()
        index = data.index(b'"', 10) + 1
        path.write_bytes(data[:index] + (b"0" if data[index:index + 1] != b"0" else b"1")
                         + data[index + 1:])
    return mutate


TIMEOUT_CASE = ((Stop(),), True, Deadline.AT_CHILD_STOP)
ERROR_CASE = ((Exit(3),), False, Deadline.TIMER)
RESOLVED_CASE = ((Checkpoint(), Envelope("UNKNOWN"), Exit()), True, Deadline.TIMER)


@pytest.mark.parametrize(("setup", "mutate", "code"), (
    (TIMEOUT_CASE, lambda case: _forge_error_receipt(case, disposition="SIGTERM_AFTER_DEADLINE"),
     "TERMINAL_AUTHORITY_CONFLICT"),
    (RESOLVED_CASE, lambda case: _forge_error_receipt(case, disposition="EXIT_CODE_2"),
     "TERMINAL_AUTHORITY_CONFLICT"),
    (ERROR_CASE, _forge_deadline, "TERMINAL_EVIDENCE_INVALID"),
    (RESOLVED_CASE, _forge_deadline, "TERMINAL_EVIDENCE_INVALID"),
    (TIMEOUT_CASE, lambda case: (case.store_directory / "canonical-resolved-receipt.json")
     .write_text("{}", encoding="utf-8"), "TERMINAL_EVIDENCE_INVALID"),
    (TIMEOUT_CASE, _edit_byte("timeout.json"), "TERMINAL_EVIDENCE_INVALID"),
    (TIMEOUT_CASE, _edit_byte(te.CHILD_EXIT_FILENAME), "TERMINAL_EVIDENCE_INVALID"),
    (ERROR_CASE, _edit_byte("operational-error-bundle.json"), "TERMINAL_EVIDENCE_INVALID"),
    (RESOLVED_CASE, _edit_byte("canonical-resolved-receipt.json"), "TERMINAL_EVIDENCE_INVALID"),
), ids=("timeout+error", "resolved+error", "error+deadline", "resolved+deadline",
        "timeout+resolved-receipt", "timeout-member", "exit-receipt", "error-bundle",
        "resolved-receipt"))
def test_t13_conflicts_and_tampering_beat_a_complete_terminal(tmp_path, setup, mutate, code):
    steps, runner, deadline = setup
    with supervisor_case(tmp_path, ChildScript(steps), allow_child_exit_resolution=runner) as case:
        complete = run_supervisor(case, deadline=deadline)
        assert complete.projection["status"] in {"TIMEOUT", "ERROR", "RESOLVED"}
        mutate(case)
        _restart_unchanged(case, code)


def _projection_file(tmp_path, projection, **changes):
    body = {key: value for key, value in projection.items() if key != "projection_digest"}
    body.update(changes)
    body["projection_digest"] = authority_digest(body)
    path = tmp_path / "swapped-projection.json"
    path.write_text(json.dumps(body, sort_keys=True), encoding="utf-8")
    return path


@pytest.mark.parametrize(("setup", "claimed_status", "kind"), (
    (ERROR_CASE, "TIMEOUT", "DurableTimeoutFinalizationBundle"),
    (TIMEOUT_CASE, "ERROR", "DurableErrorFinalizationBundle"),
), ids=("timeout-projection-on-error", "error-projection-on-timeout"))
def test_t13_a_projection_that_names_another_terminal_is_not_classified(
    tmp_path, setup, claimed_status, kind,
):
    from scripts.function_tracer_pcode.authority.decision.canonical_result import (
        classify_pair_status,
    )

    steps, runner, deadline = setup
    with supervisor_case(tmp_path / "case", ChildScript(steps),
                         allow_child_exit_resolution=runner) as case:
        run = run_supervisor(case, deadline=deadline)
        swapped = _projection_file(
            tmp_path, run.projection, status=claimed_status, authority_kind=kind,
            supervisor_authority_kind=kind, canonical_outcome=claimed_status,
        )
        config = case.config
        with pytest.raises(ValueError, match="not the durable terminal authority"):
            classify_pair_status(
                case.pair_log, swapped, checkpoint_root=config.checkpoint_root,
                execution_nonce=config.execution_nonce,
                supervisor_signing_key_id=config.supervisor_signing_key_id,
                supervisor_signing_key_file=config.supervisor_signing_key_file,
                worker_signing_key_id=config.worker_signing_key_id,
                worker_signing_key_file=config.worker_signing_key_file,
                terminal_evidence_signing_key_id=config.terminal_evidence_signing_key_id,
                terminal_evidence_signing_key_file=config.terminal_evidence_signing_key_file,
            )
        # restart は既存の projection を読まず、durable authority から作り直す。
        config.authority_output.write_bytes(swapped.read_bytes())
        restarted = restart_supervisor(case)
        assert restarted.projection == run.projection


# ---------------------------------------------------------------------------
# T14: legacy（E の無い store）
# ---------------------------------------------------------------------------


def _drop_evidence(case):
    for name in (te.DEADLINE_FILENAME, te.CHILD_EXIT_FILENAME):
        (case.store_directory / name).unlink(missing_ok=True)


@pytest.mark.parametrize(("setup", "faults", "code"), (
    (TIMEOUT_CASE, (), "TERMINAL_WITHOUT_EXIT_OBSERVATION"),
    (ERROR_CASE, (), "TERMINAL_WITHOUT_EXIT_OBSERVATION"),
    (TIMEOUT_CASE, (crash_at(FileBoundary("claimed.json")),),
     "TERMINAL_WITHOUT_EXIT_OBSERVATION"),
), ids=("complete-timeout", "complete-error", "claimed"))
def test_t14_legacy_terminal_authority_without_an_exit_observation_is_invalid(
    tmp_path, setup, faults, code,
):
    steps, runner, deadline = setup
    with supervisor_case(tmp_path, ChildScript(steps), allow_child_exit_resolution=runner) as case:
        run_supervisor(case, deadline=deadline, faults=faults)
        _drop_evidence(case)
        _restart_unchanged(case, code)


@pytest.mark.parametrize(("steps", "child_faults", "runner"), (
    ((Checkpoint(), Stop()), (crash_at(FileBoundary("pending-active-transaction.json")),), False),
    ((Checkpoint(), Envelope("UNKNOWN"), Exit()), (), True),
), ids=("worker-pending", "valid-envelope"))
def test_t14_a_child_result_without_an_exit_observation_is_invalid(
    tmp_path, steps, child_faults, runner,
):
    with supervisor_case(
        tmp_path, ChildScript(steps, faults=child_faults), allow_child_exit_resolution=runner,
    ) as case:
        first = run_supervisor(
            case, faults=(crash_at(FileBoundary(te.CHILD_EXIT_FILENAME, side="before")),),
        )
        assert first.crashed
        _restart_unchanged(case, "EXIT_NOT_OBSERVED")


# ---------------------------------------------------------------------------
# T15: 冪等な drive と 2 つの supervisor の競合
# ---------------------------------------------------------------------------


def test_t15_driving_a_terminal_store_again_changes_nothing(tmp_path):
    with supervisor_case(tmp_path, ChildScript((Checkpoint(), Stop())),
                         allow_child_exit_resolution=True) as case:
        first = run_supervisor(case, deadline=Deadline.AT_CHILD_STOP)
        runs = [restart_supervisor(case) for _ in range(3)]
        for run in runs:
            assert run.projection == first.projection
            assert run.store.digests == first.store.digests


def test_t15_two_restarts_serialize_on_ownership_and_derive_one_terminal(tmp_path):
    context, case = _deadline_case_after_exit(tmp_path)
    try:
        point = FileBoundary("claimed.json")
        with start_supervisor(case, entry=SupervisorEntry.RESUME,
                              faults=(pause_at(point),)) as first:
            first.wait_until_paused(point.describe())
            with start_supervisor(case, entry=SupervisorEntry.RESUME) as second:
                second.wait_until_blocked_on_ownership()
                first.release()
                a = first.wait()
                b = second.wait()
        expected = _expected("deadline", runner=True, phase="RESOLVED")
        _assert_terminal(b, expected)
        assert a.projection == b.projection
        # 後の supervisor は何も書き足さない（署名の二重発行・上書き無し）。
        assert a.store.digests == b.store.digests
    finally:
        context.__exit__(None, None, None)


def test_t15_a_restart_waits_for_the_running_supervisor_and_agrees(tmp_path):
    with supervisor_case(tmp_path, ChildScript((Checkpoint(), Stop())),
                         allow_child_exit_resolution=True) as case:
        point = FileBoundary(te.DEADLINE_FILENAME)
        with start_supervisor(case, entry=SupervisorEntry.FRESH_START,
                              deadline=Deadline.AT_CHILD_STOP,
                              faults=(pause_at(point),)) as original:
            original.wait_until_paused(point.describe())
            with start_supervisor(case, entry=SupervisorEntry.RESUME) as restart:
                restart.wait_until_blocked_on_ownership()
                original.release()
                a = original.wait()
                b = restart.wait()
        _assert_terminal(b, _expected("deadline", runner=True, phase="RESOLVED"))
        assert a.projection == b.projection
        assert a.store.digests == b.store.digests


# ---------------------------------------------------------------------------
# 署名鍵の分離（計画 §6.2: D / E / A の鍵を child に渡さない）
# ---------------------------------------------------------------------------


def test_the_terminal_evidence_key_never_reaches_the_child(tmp_path):
    with supervisor_case(tmp_path, ChildScript((Exit(3),))) as case:
        run = run_supervisor(case)
        evidence = run.launch_evidence
        needle = str(case.keys.terminal_evidence_key_file)
        visible = list(evidence["environment"].values()) + list(evidence["argv"])
        assert all(needle not in value for value in visible)
        assert all(case.keys.terminal_evidence_key_id not in value for value in visible)
        key = case.keys.terminal_evidence_key_file.read_bytes().decode("latin-1")
        assert all(key not in value for value in visible)
