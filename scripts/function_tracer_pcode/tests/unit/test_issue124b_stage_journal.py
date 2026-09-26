# -*- coding: utf-8 -*-
"""Issue #124 PR-124-B: kill 耐性の stage journal と stack dump handler の契約。

PR-124-A の `StageClock` は結果 JSON に**まとめて**載るので、結果 JSON が出ない
pair（TIMEOUT / SIGKILL）には計測が 1 行も残らなかった。この PR が足すのは、
同じ region / stage を 1 行ずつ書いて毎回 flush する append-only JSONL と、
その journal に「stack dump handler を登録できた」事実を残す経路だけ。

ここで固定するのは次の 6 点で、判定の意味は 1 つも変えない:

* flush 済みの行は SIGKILL 後も残る（mock の `flush.called` ではなく実子プロセス）
* journal が正本として書く dump path は **cleanup 後も有効な run dir 側**で、
  checkpoint 内の一時 path は別 key（`dump_path_tmp`）
* `result_emit` は `to_dict()` の**前**から JSON 書き出し完了までを囲む
* `handler_registered` の根拠は `faulthandler.register()` の成功**だけ**
  （`SigCgt` を ready 風に偽装しても、register が失敗すれば ready にしない）
* region の再入・solver counter の意味は PR-124-A のまま（journal で二重加算しない）
* journal の I/O 失敗は判定にも計測にも影響しない

PR-124-C（supervisor からの SIGUSR1 送信・dump 退避・`timeout_kind`・hotspot）は
この PR の対象外で、ここでも一切送信しない。
"""

from __future__ import annotations

import ast
import json
import re
import os
import signal
import subprocess
import sys
import time
from pathlib import Path
from types import SimpleNamespace

import pytest

from scripts.function_tracer_pcode.cli import pair_diagnostics
from scripts.function_tracer_pcode.cli.args import build_parser
from scripts.function_tracer_pcode.cli.pair_diagnostics import (
    PairDiagnostics,
    STACK_DUMP_SIGNAL,
    install_pair_diagnostics,
    jvm_already_started,
    register_stack_dump_handler,
)
from scripts.function_tracer_pcode.core.stage_clock import StageClock, stage_region
from scripts.function_tracer_pcode.core.stage_journal import (
    EVENT_COUNTER,
    EVENT_HANDLER_REGISTERED,
    EVENT_NOTE,
    EVENT_STAGE_END,
    EVENT_STAGE_START,
    JOURNAL_EVENTS,
    STAGE_JOURNAL_SCHEMA,
    StageJournal,
    active_stage_journal,
    close_active_stage_journal,
    journal_note,
    set_active_stage_journal,
)

REPO_ROOT = Path(__file__).resolve().parents[4]
PACKAGE_ROOT = Path(__file__).resolve().parents[2]

#: 行の必須 key（`schema` は「途中で切れた file でも 1 行で解釈できる」ため）。
REQUIRED_LINE_KEYS = frozenset({
    "schema", "seq", "event", "stage", "seconds", "t_monotonic", "t_epoch",
    "pid", "payload",
})


def read_journal(path):
    """(解釈できた行, 壊れていた行数) を返す。壊れた行で読み取りを止めない。"""
    rows = []
    broken = 0
    text = Path(path).read_text(encoding="utf-8", errors="replace")
    for line in text.splitlines():
        if not line.strip():
            continue
        try:
            rows.append(json.loads(line))
        except json.JSONDecodeError:
            broken += 1
    return rows, broken


def events(rows, event=None, stage=None):
    return [
        row for row in rows
        if (event is None or row.get("event") == event)
        and (stage is None or row.get("stage") == stage)
    ]


def seq_of(rows, predicate):
    for row in rows:
        if predicate(row):
            return row["seq"]
    raise AssertionError(f"no journal row matched; rows={[r.get('event') for r in rows]}")


@pytest.fixture
def journal(tmp_path):
    """active journal を張り替え、test の後で必ず元へ戻す。"""
    handle = StageJournal(tmp_path / "pair.stage.jsonl")
    previous = set_active_stage_journal(handle)
    try:
        yield handle
    finally:
        set_active_stage_journal(previous)
        handle.close()


@pytest.fixture
def restore_sigusr1():
    """本物の登録を試す test の後始末（他の test へ handler を残さない）。"""
    import faulthandler

    yield
    try:
        faulthandler.unregister(STACK_DUMP_SIGNAL)
    except (RuntimeError, ValueError):
        pass


# --------------------------------------------------------------------------
# 1. 行 schema と seq
# --------------------------------------------------------------------------


def test_journal_lines_carry_the_v1_schema_and_a_monotonic_seq(tmp_path):
    path = tmp_path / "pair.stage.jsonl"
    handle = StageJournal(path)
    handle.append(EVENT_STAGE_START, stage="check")
    handle.append(EVENT_COUNTER, stage="solver", payload={"backend_run_id": 1})
    handle.append(EVENT_STAGE_END, stage="check", seconds=0.25)
    handle.close()

    rows, broken = read_journal(path)
    assert broken == 0
    assert [row["seq"] for row in rows] == [1, 2, 3]
    for row in rows:
        assert set(row) == REQUIRED_LINE_KEYS
        assert row["schema"] == STAGE_JOURNAL_SCHEMA
        assert row["event"] in JOURNAL_EVENTS
        assert row["pid"] == os.getpid()
        assert isinstance(row["t_monotonic"], float)
        assert isinstance(row["t_epoch"], float)
    assert rows[0]["seconds"] is None
    assert rows[2]["seconds"] == pytest.approx(0.25)
    assert rows[1]["payload"] == {"backend_run_id": 1}


def test_journal_seq_stays_monotonic_across_threads(tmp_path):
    import threading

    path = tmp_path / "pair.stage.jsonl"
    handle = StageJournal(path)

    def worker(index):
        for _ in range(20):
            handle.append(EVENT_COUNTER, stage=f"w{index}")

    threads = [threading.Thread(target=worker, args=(i,)) for i in range(4)]
    for thread in threads:
        thread.start()
    for thread in threads:
        thread.join()
    handle.close()

    rows, broken = read_journal(path)
    assert broken == 0
    assert len(rows) == 80
    assert [row["seq"] for row in rows] == sorted(row["seq"] for row in rows)
    assert [row["seq"] for row in rows] == list(range(1, 81))


# --------------------------------------------------------------------------
# 2. kill 耐性（実子プロセス）
# --------------------------------------------------------------------------


_KILL_CHILD = """
import sys, time
sys.path.insert(0, "__REPO_ROOT__")
from scripts.function_tracer_pcode.core.stage_journal import StageJournal

journal = StageJournal(sys.argv[1])
for index in range(5):
    assert journal.append("stage_start", stage="s%d" % index) == index + 1
# close() も flush() も明示的には呼ばない。ここまでで file に残っていなければ
# append ごとの flush ができていない。
open(sys.argv[2], "w").write("ready")
while True:
    time.sleep(0.05)
"""


def test_stage_journal_flushes_each_event_and_survives_sigkill(tmp_path):
    """SIGKILL された子プロセスの journal に、すでに書いた行が残ること。

    `flush.called` の mock ではなく実プロセスを殺す。close も flush も呼ばれない
    まま SIGKILL されるので、append ごとの flush が抜けていれば file は空になる。
    """
    path = tmp_path / "killed.stage.jsonl"
    ready = tmp_path / "ready"
    script = tmp_path / "child.py"
    script.write_text(_KILL_CHILD.replace("__REPO_ROOT__", str(REPO_ROOT)), encoding="utf-8")

    child = subprocess.Popen([sys.executable, "-B", str(script), str(path), str(ready)])
    try:
        deadline = time.monotonic() + 30
        while time.monotonic() < deadline and not ready.exists():
            time.sleep(0.02)
        assert ready.exists(), "child never reported ready"
        assert child.poll() is None
        os.kill(child.pid, signal.SIGKILL)
    finally:
        child.wait(timeout=30)

    assert child.returncode == -signal.SIGKILL
    rows, broken = read_journal(path)
    assert broken == 0
    assert [row["stage"] for row in rows] == ["s0", "s1", "s2", "s3", "s4"]
    assert [row["seq"] for row in rows] == [1, 2, 3, 4, 5]
    assert {row["pid"] for row in rows} == {child.pid}


def test_a_truncated_tail_line_does_not_hide_the_earlier_events(tmp_path):
    """途中で切れた行があっても、それより前の行はそのまま読めること。"""
    path = tmp_path / "partial.stage.jsonl"
    handle = StageJournal(path)
    handle.append(EVENT_STAGE_START, stage="check")
    handle.append(EVENT_STAGE_END, stage="check", seconds=1.0)
    handle.close()
    with open(path, "a", encoding="utf-8") as broken_writer:
        broken_writer.write('{"schema": "pair-stage-journal-v1", "seq": 3, "eve')

    rows, broken = read_journal(path)
    assert broken == 1
    assert [row["event"] for row in rows] == [EVENT_STAGE_START, EVENT_STAGE_END]


# --------------------------------------------------------------------------
# 3. dump path 契約（正本は run dir 側の artifact）
# --------------------------------------------------------------------------


def _dump_paths(tmp_path):
    checkpoint = tmp_path / "process-authority" / "nonce-1"
    run_dir = tmp_path / "logs" / "REVE" / "sample" / "f"
    artifact_dir = run_dir / ".runtime-metrics"
    artifact_dir.mkdir(parents=True)
    return checkpoint / "stack-dump.txt", artifact_dir / "f_B1_B2.stack-dump.txt"


def test_journal_records_persistent_artifact_path_not_checkpoint_tmp(
    tmp_path, journal, restore_sigusr1
):
    """`handler_registered` の正本 path は cleanup 後も有効な artifact path。"""
    dump_tmp, dump_artifact = _dump_paths(tmp_path)
    state = install_pair_diagnostics(
        SimpleNamespace(
            stage_journal=None,
            stack_dump_file=str(dump_tmp),
            stack_dump_artifact=str(dump_artifact),
        )
    )
    assert state.handler_registered is True

    rows, _ = read_journal(journal.path)
    registered = events(rows, EVENT_HANDLER_REGISTERED)
    assert len(registered) == 1
    payload = registered[0]["payload"]

    assert payload["dump_artifact_path"] == str(dump_artifact)
    assert payload["dump_path_tmp"] == str(dump_tmp)
    assert payload["dump_artifact_path"] != payload["dump_path_tmp"]
    assert payload["dump_artifact_path_status"] == "declared"
    # 正本は checkpoint の下に無い（cleanup で消える path を正本にしない）。
    checkpoint_root = str(tmp_path / "process-authority")
    assert not payload["dump_artifact_path"].startswith(checkpoint_root)
    assert payload["dump_path_tmp"].startswith(checkpoint_root)
    # PR-124-C の cleanup 相当（checkpoint ごと消す）をしても正本は残る側。
    import shutil

    shutil.rmtree(checkpoint_root)
    assert not Path(payload["dump_path_tmp"]).parent.exists()
    assert Path(payload["dump_artifact_path"]).parent.exists()


def test_relative_dump_paths_are_recorded_as_absolute(tmp_path, journal, monkeypatch):
    """曖昧な相対 path を契約 path として出さない。"""
    monkeypatch.chdir(tmp_path)
    (tmp_path / "cp").mkdir()
    (tmp_path / "rt").mkdir()
    state = install_pair_diagnostics(
        SimpleNamespace(
            stage_journal=None,
            stack_dump_file="cp/stack-dump.txt",
            stack_dump_artifact="rt/pair.stack-dump.txt",
        )
    )
    try:
        assert state.handler_registered is True
        rows, _ = read_journal(journal.path)
        payload = events(rows, EVENT_HANDLER_REGISTERED)[0]["payload"]
        assert Path(payload["dump_path_tmp"]).is_absolute()
        assert Path(payload["dump_artifact_path"]).is_absolute()
    finally:
        import faulthandler

        faulthandler.unregister(STACK_DUMP_SIGNAL)


def test_missing_artifact_path_is_unset_not_the_checkpoint_path(
    tmp_path, journal, restore_sigusr1
):
    dump_tmp, _artifact = _dump_paths(tmp_path)
    install_pair_diagnostics(
        SimpleNamespace(
            stage_journal=None,
            stack_dump_file=str(dump_tmp),
            stack_dump_artifact=None,
        )
    )
    rows, _ = read_journal(journal.path)
    payload = events(rows, EVENT_HANDLER_REGISTERED)[0]["payload"]
    # 「artifact が無い」を tmp path で埋めない。
    assert payload["dump_artifact_path"] is None
    assert payload["dump_artifact_path_status"] == "unset"
    assert payload["dump_path_tmp"] == str(dump_tmp)


# --------------------------------------------------------------------------
# 4. readiness は register の成功だけ
# --------------------------------------------------------------------------


class _RecordingFaulthandler:
    def __init__(self, error=None):
        self.calls = []
        self.error = error

    def register(self, signum, file=None, all_threads=None, chain=None):
        self.calls.append(
            {"signum": signum, "file": file, "all_threads": all_threads, "chain": chain}
        )
        if self.error is not None:
            raise self.error


def _state(tmp_path):
    dump_tmp, dump_artifact = _dump_paths(tmp_path)
    return PairDiagnostics(
        dump_path_tmp=str(dump_tmp), dump_artifact_path=str(dump_artifact)
    )


def test_handler_registered_written_on_registration_success_only(
    tmp_path, journal, monkeypatch
):
    stub = _RecordingFaulthandler()
    monkeypatch.setattr(pair_diagnostics, "faulthandler", stub)

    state = register_stack_dump_handler(_state(tmp_path))

    assert state.handler_registered is True
    assert state.registration_error is None
    # 契約どおりの登録（SIGUSR1 / all_threads / chain=False）。
    assert len(stub.calls) == 1
    assert stub.calls[0]["signum"] == STACK_DUMP_SIGNAL == signal.SIGUSR1
    assert stub.calls[0]["all_threads"] is True
    assert stub.calls[0]["chain"] is False

    rows, _ = read_journal(journal.path)
    registered = events(rows, EVENT_HANDLER_REGISTERED)
    assert len(registered) == 1
    payload = registered[0]["payload"]
    assert payload["readiness_basis"] == "faulthandler_register_returned"
    assert payload["pid"] == os.getpid()
    assert payload["registered_before_jvm"] is True
    assert payload["signal"] == "SIGUSR1"
    assert payload["all_threads"] is True
    assert payload["chain"] is False
    assert "start_token" in payload
    assert not [
        row for row in rows
        if row["event"] == EVENT_NOTE
        and str(row["payload"].get("note", "")).startswith("handler_registration_failed")
    ]


def test_registration_failure_writes_a_note_and_no_handler_registered(
    tmp_path, journal, monkeypatch
):
    stub = _RecordingFaulthandler(error=RuntimeError("cannot install handler"))
    monkeypatch.setattr(pair_diagnostics, "faulthandler", stub)

    state = register_stack_dump_handler(_state(tmp_path))

    assert state.handler_registered is False
    assert state.registration_error == "RuntimeError"
    rows, _ = read_journal(journal.path)
    assert events(rows, EVENT_HANDLER_REGISTERED) == []
    notes = [row for row in rows if row["event"] == EVENT_NOTE]
    assert len(notes) == 1
    assert notes[0]["payload"]["note"] == "handler_registration_failed:RuntimeError"
    assert notes[0]["payload"]["phase"] == "register"


def test_an_unopenable_dump_file_never_claims_readiness(tmp_path, journal, monkeypatch):
    stub = _RecordingFaulthandler()
    monkeypatch.setattr(pair_diagnostics, "faulthandler", stub)
    state = PairDiagnostics(
        dump_path_tmp=str(tmp_path),  # ディレクトリなので open できない
        dump_artifact_path=str(tmp_path / "artifact.txt"),
    )

    register_stack_dump_handler(state)

    assert state.handler_registered is False
    assert stub.calls == []  # register まで到達しない
    rows, _ = read_journal(journal.path)
    assert events(rows, EVENT_HANDLER_REGISTERED) == []
    notes = [row for row in rows if row["event"] == EVENT_NOTE]
    assert notes[0]["payload"]["phase"] == "open_dump_file"
    assert notes[0]["payload"]["note"].startswith("handler_registration_failed:")


def test_a_ready_looking_sigcgt_does_not_make_a_failed_registration_ready(
    tmp_path, journal, monkeypatch
):
    """`SigCgt` を「SIGUSR1 を捕捉済み」に偽装しても readiness にしない。"""
    monkeypatch.setattr(
        pair_diagnostics, "faulthandler",
        _RecordingFaulthandler(error=OSError("sigaction failed")),
    )
    monkeypatch.setattr(
        pair_diagnostics, "_sigcgt_probe",
        lambda signal_number: {
            "sigcgt": "ffffffffffffffff", "signal_bit_set": True, "authoritative": False
        },
    )

    state = register_stack_dump_handler(_state(tmp_path))

    assert state.handler_registered is False
    rows, _ = read_journal(journal.path)
    assert events(rows, EVENT_HANDLER_REGISTERED) == []


def test_sigcgt_is_only_auxiliary_on_the_success_path(tmp_path, journal, monkeypatch):
    monkeypatch.setattr(pair_diagnostics, "faulthandler", _RecordingFaulthandler())
    monkeypatch.setattr(
        pair_diagnostics, "_sigcgt_probe",
        lambda signal_number: {"sigcgt": "0", "signal_bit_set": False, "authoritative": False},
    )

    register_stack_dump_handler(_state(tmp_path))

    rows, _ = read_journal(journal.path)
    payload = events(rows, EVENT_HANDLER_REGISTERED)[0]["payload"]
    # register が成功していれば、probe が「立っていない」でも ready。
    assert payload["sigcgt_probe"]["signal_bit_set"] is False
    assert payload["sigcgt_probe"]["authoritative"] is False
    assert payload["readiness_basis"] == "faulthandler_register_returned"


def test_a_real_registration_writes_the_event_and_keeps_the_process_alive(
    tmp_path, journal, restore_sigusr1
):
    """本物の `faulthandler.register` で登録し、SIGUSR1 で死なないこと。"""
    dump_tmp, dump_artifact = _dump_paths(tmp_path)
    state = register_stack_dump_handler(
        PairDiagnostics(dump_path_tmp=str(dump_tmp), dump_artifact_path=str(dump_artifact))
    )
    assert state.handler_registered is True

    os.kill(os.getpid(), signal.SIGUSR1)
    time.sleep(0.1)
    dump = Path(dump_tmp).read_text(encoding="utf-8", errors="replace")
    assert "Current thread" in dump or "Thread 0x" in dump
    assert 'File "' in dump


# --------------------------------------------------------------------------
# 5. JVM 起動前であること
# --------------------------------------------------------------------------


def test_jvm_probe_is_false_without_jpype(monkeypatch):
    monkeypatch.delitem(sys.modules, "jpype", raising=False)
    assert jvm_already_started() is False


def test_registered_before_jvm_reflects_the_probe_not_a_constant(
    tmp_path, journal, monkeypatch
):
    """JVM が既に動いていれば `registered_before_jvm` を true と主張しない。"""
    monkeypatch.setattr(pair_diagnostics, "faulthandler", _RecordingFaulthandler())
    monkeypatch.setitem(
        sys.modules, "jpype", SimpleNamespace(isJVMStarted=lambda: True)
    )

    register_stack_dump_handler(_state(tmp_path))

    rows, _ = read_journal(journal.path)
    payload = events(rows, EVENT_HANDLER_REGISTERED)[0]["payload"]
    assert payload["registered_before_jvm"] is False


def _called_names_in_order(function_node):
    names = []
    for node in ast.walk(function_node):
        if isinstance(node, ast.Call):
            target = node.func
            if isinstance(target, ast.Name):
                names.append((node.lineno, target.id))
            elif isinstance(target, ast.Attribute):
                names.append((node.lineno, target.attr))
    return [name for _line, name in sorted(names)]


def test_the_handler_is_installed_before_the_jvm_starts_in_the_cli():
    """`run_equivalence_check` の呼び出し順（JVM 起動より前）を source で固定。"""
    source = (
        PACKAGE_ROOT / "cli" / "commands" / "equivalence.py"
    ).read_text(encoding="utf-8")
    tree = ast.parse(source)
    function = next(
        node for node in tree.body
        if isinstance(node, ast.FunctionDef) and node.name == "run_equivalence_check"
    )
    order = _called_names_in_order(function)
    assert "install_pair_diagnostics" in order
    assert "start_headless_pyghidra" in order
    assert order.index("install_pair_diagnostics") < order.index("start_headless_pyghidra")


# --------------------------------------------------------------------------
# 6. region / solver の journal は PR-124-A の計測意味を変えない
# --------------------------------------------------------------------------


def test_reentrant_regions_are_journaled_once_with_a_reentry_counter(journal):
    clock = StageClock()
    with clock.scope():
        with stage_region("check"):
            with stage_region("check"):  # 再入（最外の区間だけが時間を持つ）
                time.sleep(0.01)

    regions = clock.region_snapshot()
    # PR-124-A の意味は不変: calls は実回数、reentrant_calls は再入回数。
    assert regions["check"]["calls"] == 2
    assert regions["check"]["reentrant_calls"] == 1

    rows, _ = read_journal(journal.path)
    assert len(events(rows, EVENT_STAGE_START, "check")) == 1
    assert len(events(rows, EVENT_STAGE_END, "check")) == 1
    reentries = events(rows, EVENT_COUNTER, "check")
    assert len(reentries) == 1
    assert reentries[0]["payload"]["kind"] == "region_reentry"
    # journal の end の秒数は clock の inclusive と同じ実測値（別定義にしない）。
    assert events(rows, EVENT_STAGE_END, "check")[0]["seconds"] == pytest.approx(
        regions["check"]["seconds_inclusive"], abs=1e-4
    )


def test_only_the_declared_regions_are_journaled(journal):
    """`condition_simplify` のような高頻度 region まで 1 行ずつ書かない。"""
    clock = StageClock()
    with clock.scope():
        with stage_region("branch_plan_orchestration"):
            with stage_region("check"):
                with stage_region("condition_simplify"):
                    pass
                with stage_region("obligation_build"):
                    pass

    rows, _ = read_journal(journal.path)
    journaled = {row["stage"] for row in rows if row["event"] == EVENT_STAGE_START}
    assert journaled == {"branch_plan_orchestration", "check", "obligation_build"}
    # 計測そのものは従来どおり全 region に残る。
    regions = clock.region_snapshot()
    check = regions["branch_plan_orchestration"]["children"]["check"]["children"]
    assert set(check) == {"condition_simplify", "obligation_build"}


def test_analysis_regions_are_journaled_per_side_with_decompile(journal):
    clock = StageClock()
    with clock.scope():
        with stage_region("analysis_regions"), stage_region("function2"):
            with stage_region("decompile"):
                pass

    rows, _ = read_journal(journal.path)
    starts = events(rows, EVENT_STAGE_START)
    assert [row["stage"] for row in starts] == [
        "analysis_regions", "function2", "decompile"
    ]
    decompile = events(rows, EVENT_STAGE_END, "decompile")[0]
    assert decompile["payload"]["side"] == "function2"
    assert decompile["payload"]["path"] == ["analysis_regions", "function2", "decompile"]


def test_flat_cli_stages_are_journaled_so_a_kill_before_check_is_visible(journal):
    clock = StageClock()
    with clock.timed("auto_analyze_binary1"):
        time.sleep(0.01)

    rows, _ = read_journal(journal.path)
    assert [row["event"] for row in rows] == [EVENT_STAGE_START, EVENT_STAGE_END]
    assert rows[1]["stage"] == "auto_analyze_binary1"
    assert rows[1]["payload"]["kind"] == "stage"
    assert rows[1]["seconds"] == pytest.approx(
        clock.seconds["auto_analyze_binary1"], abs=1e-4
    )


def _solver_class(label, status, delay):
    from scripts.function_tracer_pcode.smt.interface import SolverResult

    class _FakeSolver:
        name = label

        def __init__(self, timeout=10):
            self.timeout = timeout

        def check_availability(self):
            return True, "available"

        def set_timeout(self, seconds):
            self.timeout = seconds

        def check_equivalence_direct(self, smt_script, cancellation_token=None):
            time.sleep(delay)
            return SolverResult(solver_name=label, status=status, elapsed_time=delay)

    return _FakeSolver


def test_solver_journal_keeps_the_four_counters_unchanged(journal):
    from scripts.function_tracer_pcode.smt.interface import SolverStatus
    from scripts.function_tracer_pcode.smt.parallel import (
        ParallelSolverRunner,
        reset_solver_counters,
        solver_counter_snapshot,
    )

    runner = ParallelSolverRunner(
        timeout=5,
        solver_classes=[
            _solver_class("s1", SolverStatus.UNKNOWN, 0.02),
            _solver_class("s2", SolverStatus.UNKNOWN, 0.02),
            _solver_class("s3", SolverStatus.UNKNOWN, 0.02),
        ],
    )
    reset_solver_counters()
    runner.run_parallel("(check-sat)")
    counters = solver_counter_snapshot()
    # PR-124-A の意味は不変。
    assert counters["logical_queries"] == 1
    assert counters["backend_runs"] == 3

    rows, _ = read_journal(journal.path)
    starts = events(rows, EVENT_STAGE_START, "solver")
    ends = events(rows, EVENT_STAGE_END, "solver")
    backends = events(rows, EVENT_COUNTER, "solver")
    # 論理的な問い合わせ 1 本の start/end と、backend 3 本の counter。
    assert len(starts) == len(ends) == 1
    assert starts[0]["payload"]["kind"] == "run_parallel"
    query_id = starts[0]["payload"]["query_id"]
    assert len(backends) == 3
    assert {row["payload"]["query_id"] for row in backends} == {query_id}
    assert sorted(row["payload"]["backend_run_id"] for row in backends) == [1, 2, 3]
    assert {row["payload"]["orchestrated"] for row in backends} == {True}
    assert {row["payload"]["solver"] for row in backends} == {"s1", "s2", "s3"}
    reset_solver_counters()


def test_a_directly_called_run_single_is_journaled_as_its_own_query(journal):
    from scripts.function_tracer_pcode.smt.interface import SolverStatus
    from scripts.function_tracer_pcode.smt.parallel import (
        ParallelSolverRunner,
        reset_solver_counters,
        solver_counter_snapshot,
    )

    runner = ParallelSolverRunner(
        timeout=5, solver_classes=[_solver_class("d1", SolverStatus.UNSAT, 0.01)]
    )
    reset_solver_counters()
    runner.run_single(runner._solvers[0], "(check-sat)")
    counters = solver_counter_snapshot()
    assert counters["logical_queries"] == 1
    assert counters["backend_runs"] == 1

    rows, _ = read_journal(journal.path)
    assert len(events(rows, EVENT_STAGE_START, "solver")) == 1
    assert len(events(rows, EVENT_STAGE_END, "solver")) == 1
    assert events(rows, EVENT_COUNTER, "solver") == []
    payload = events(rows, EVENT_STAGE_START, "solver")[0]["payload"]
    assert payload["kind"] == "run_single"
    assert payload["orchestrated"] is False
    reset_solver_counters()


def test_run_sequential_is_journaled_as_one_query_with_backend_counters(journal):
    from scripts.function_tracer_pcode.smt.interface import SolverStatus
    from scripts.function_tracer_pcode.smt.parallel import (
        ParallelSolverRunner,
        reset_solver_counters,
    )

    runner = ParallelSolverRunner(
        timeout=5,
        solver_classes=[
            _solver_class("q1", SolverStatus.UNKNOWN, 0.01),
            _solver_class("q2", SolverStatus.UNSAT, 0.01),
        ],
    )
    reset_solver_counters()
    runner.run_sequential("(check-sat)")

    rows, _ = read_journal(journal.path)
    starts = events(rows, EVENT_STAGE_START, "solver")
    assert len(starts) == 1
    assert starts[0]["payload"]["kind"] == "run_sequential"
    assert len(events(rows, EVENT_COUNTER, "solver")) == 2
    reset_solver_counters()


def test_boundary_finalize_and_conditional_lane_are_journaled(journal, monkeypatch):
    from scripts.function_tracer_pcode.tests.unit.test_issue124_stage_regions import (
        _boundary_environment,
    )

    boundary, checker = _boundary_environment(
        monkeypatch, finalize_seconds=0.05, lane_seconds=0.05
    )
    result = boundary.run_check_from_binaries_with_v2_pilot(
        checker, object(), object(), "left", "right"
    )
    seconds = result.diagnostics["boundary_seconds"]

    rows, _ = read_journal(journal.path)
    for stage in ("authority_finalize", "conditional_lane"):
        assert len(events(rows, EVENT_STAGE_START, stage)) == 1
        end = events(rows, EVENT_STAGE_END, stage)
        assert len(end) == 1
        # journal の秒数は boundary_seconds と同じ 1 回の計測から書く。
        assert end[0]["seconds"] == pytest.approx(seconds[stage], abs=1e-5)


# --------------------------------------------------------------------------
# 7. `result_emit` は to_dict の前から JSON 書き出し後まで
# --------------------------------------------------------------------------


def _fake_equivalence_environment(monkeypatch, tmp_path, journal_path):
    """`run_equivalence_check` を判定抜きで通すための最小の偽物一式。"""
    from scripts.function_tracer_pcode import checker as checker_package
    from scripts.function_tracer_pcode.authority.decision import canonical_result
    from scripts.function_tracer_pcode.checker import cause_aggregate
    from scripts.function_tracer_pcode.cli.commands import equivalence as module

    binary1 = tmp_path / "left.bin"
    binary2 = tmp_path / "right.bin"
    binary1.write_bytes(b"\x7fELF-left")
    binary2.write_bytes(b"\x7fELF-right")

    written = []

    class _FakeResult:
        def __init__(self):
            self.diagnostics = {}
            self.is_equivalent = True
            self.smt_formula = None
            self.decision_receipt = None
            self._canonical_finalization_context = None

        def to_string(self, verbose=False, show_phase_usage=False):
            journal_note("probe:to_string")
            return "RESULT TEXT"

        def to_dict(self):
            journal_note("probe:to_dict")
            return {"canonical_outcome": "EQUIVALENT"}

    result = _FakeResult()

    class _FakeChecker:
        def __init__(self, **_kwargs):
            self.solver_runner = SimpleNamespace(
                get_available_solvers=lambda: ["z3"]
            )

        def check_from_binaries(self, *_args, **_kwargs):
            return result

    class _FakeContext:
        def __enter__(self):
            return self

        def __exit__(self, *_exc):
            return False

    fake_pyghidra = SimpleNamespace(
        open_project=lambda *_a, **_k: _FakeContext(),
        analyze=lambda _program: None,
    )

    monkeypatch.setattr(module, "apply_runtime_environment",
                        lambda: SimpleNamespace(ghidra_install_dir=None))
    monkeypatch.setattr(module, "load_pyghidra", lambda: fake_pyghidra)
    monkeypatch.setattr(module, "start_headless_pyghidra", lambda *_a, **_k: None)
    monkeypatch.setattr(module, "get_target_functions", lambda _args: ["f"])
    monkeypatch.setattr(
        module, "_load_program_context",
        lambda *_a, **_k: (_FakeContext(), SimpleNamespace(
            getPrimaryDomainObject=lambda: object()
        )),
    )
    monkeypatch.setattr(checker_package, "EquivalenceChecker", _FakeChecker)
    monkeypatch.setattr(checker_package, "TypeFixerConfig", lambda *_a, **_k: object())
    monkeypatch.setattr(cause_aggregate, "attach_cause_aggregate", lambda _result: None)
    monkeypatch.setattr(
        canonical_result, "persist_canonical_result_envelope", lambda _payload, **_kw: None
    )

    def _record_output(content, output_path, quiet):
        written.append(content)
        if "EQUIVALENCE_RESULT_JSON_BEGIN" in content:
            journal_note("probe:json_write")

    monkeypatch.setattr(module, "output_result", _record_output)

    args = SimpleNamespace(
        equiv=[str(binary1), str(binary2)],
        binary_ids=["B1", "B2"],
        functions=["f"],
        equiv_timeout=10,
        timeout=60,
        save_formula=False,
        verbose=False,
        quiet=True,
        debug=False,
        output=None,
        emit_result_json=True,
        no_retry_phases=False,
        strategy="pairwise",
        stage_journal=str(journal_path),
        stack_dump_file=None,
        stack_dump_artifact=None,
    )
    return module, args, written


def test_result_emit_journal_starts_before_to_dict(tmp_path, monkeypatch):
    """`stage_start(result_emit)` は `to_dict()` より前、`stage_end` は JSON 書き出し後。"""
    journal_path = tmp_path / "emit.stage.jsonl"
    module, args, written = _fake_equivalence_environment(
        monkeypatch, tmp_path, journal_path
    )
    previous = active_stage_journal()
    try:
        with pytest.raises(SystemExit) as exit_info:
            module.run_equivalence_check(args)
    finally:
        close_active_stage_journal()
        set_active_stage_journal(previous)
    assert exit_info.value.code == 0

    rows, broken = read_journal(journal_path)
    assert broken == 0

    def note(text):
        return seq_of(rows, lambda row: row["payload"].get("note") == text)

    start = seq_of(
        rows,
        lambda row: row["event"] == EVENT_STAGE_START and row["stage"] == "result_emit",
    )
    end = seq_of(
        rows,
        lambda row: row["event"] == EVENT_STAGE_END and row["stage"] == "result_emit",
    )
    # 既存の添付順（to_string -> to_dict -> JSON 書き出し）は壊さない。
    assert start < note("probe:to_string") < note("probe:to_dict")
    assert note("probe:to_dict") < note("probe:json_write") < end
    assert any("EQUIVALENCE_RESULT_JSON_BEGIN" in content for content in written)


def test_the_pair_journal_records_the_pair_identity_at_open(tmp_path, monkeypatch):
    journal_path = tmp_path / "identity.stage.jsonl"
    module, args, _written = _fake_equivalence_environment(
        monkeypatch, tmp_path, journal_path
    )
    previous = active_stage_journal()
    try:
        with pytest.raises(SystemExit):
            module.run_equivalence_check(args)
    finally:
        close_active_stage_journal()
        set_active_stage_journal(previous)

    rows, _ = read_journal(journal_path)
    opened = [
        row for row in rows
        if row["event"] == EVENT_NOTE
        and row["payload"].get("note") == "pair_journal_opened"
    ]
    assert len(opened) == 1
    assert opened[0]["payload"]["binary_ids"] == ["B1", "B2"]
    assert opened[0]["payload"]["functions"] == ["f"]
    # kill された pair でも「どの pair の journal か」が 1 行目から分かる。
    assert opened[0]["seq"] == 1


# --------------------------------------------------------------------------
# 8. 失敗しても判定へ影響しない / authority の入力にならない
# --------------------------------------------------------------------------


class _BrokenHandle:
    def write(self, _text):
        raise OSError("no space left on device")

    def flush(self):
        raise OSError("no space left on device")

    def close(self):
        raise OSError("no space left on device")


def test_journal_write_failures_do_not_disturb_the_clock_or_the_caller(tmp_path):
    handle = StageJournal(tmp_path / "broken.stage.jsonl")
    handle._handle = _BrokenHandle()
    previous = set_active_stage_journal(handle)
    try:
        clock = StageClock()
        with clock.scope():
            with stage_region("branch_plan_orchestration"):
                with stage_region("check"):
                    time.sleep(0.01)
        regions = clock.region_snapshot()
    finally:
        set_active_stage_journal(previous)

    # 計測は journal の成否に依存しない。
    orchestration = regions["branch_plan_orchestration"]
    assert orchestration["calls"] == 1
    assert orchestration["children"]["check"]["calls"] == 1
    assert orchestration["seconds_inclusive"] > 0.0
    # 失敗は journal 自身が数えるだけ（例外は外へ出ない）。
    assert handle.write_failures >= 2
    assert "OSError" in handle.last_error


def test_an_unopenable_journal_is_a_silent_no_op(tmp_path):
    handle = StageJournal(tmp_path)  # ディレクトリは開けない
    assert handle.is_open is False
    assert handle.append(EVENT_NOTE, stage="x") is None
    assert handle.write_failures == 1


def test_no_module_reads_the_journal_to_decide_anything():
    """journal は書くだけ。authority / proof / checker が読む経路を作らない。"""
    import ast as ast_module

    write_only = {
        "EVENT_HANDLER_REGISTERED", "EVENT_STAGE_START", "EVENT_STAGE_END",
        "EVENT_COUNTER", "EVENT_NOTE", "STAGE_JOURNAL_SCHEMA",
        "journal_event", "journal_stage_start", "journal_stage_end",
        "journal_counter", "journal_note", "journal_region_start",
        "journal_region_end", "journal_region_reentry",
    }
    # journal を「開いて所有する」ことが許されるのは CLI の設置点と再公開だけ。
    owners = {"cli.pair_diagnostics", "checker.diagnostics"}
    seen = {}
    for path in sorted(PACKAGE_ROOT.rglob("*.py")):
        relative = path.relative_to(PACKAGE_ROOT)
        if relative.parts[0] == "tests" or relative.parts[-1] == "stage_journal.py":
            continue
        module = ".".join(relative.with_suffix("").parts)
        tree = ast_module.parse(path.read_text(encoding="utf-8"))
        for node in ast_module.walk(tree):
            if not isinstance(node, ast_module.ImportFrom):
                continue
            if not (node.module or "").endswith("core.stage_journal"):
                continue
            names = {alias.name for alias in node.names}
            seen[module] = seen.get(module, set()) | names
    assert seen, "no module imports the journal API"
    for module, names in seen.items():
        if module in owners:
            continue
        extra = names - write_only
        assert not extra, (
            f"{module} imports {sorted(extra)} from core.stage_journal; "
            "the journal is a write-only diagnostic surface"
        )


# --------------------------------------------------------------------------
# 9. CLI / runner の配線
# --------------------------------------------------------------------------


def test_cli_exposes_the_three_diagnostic_paths():
    parsed = build_parser().parse_args(
        ["--equiv", "a", "b", "-f", "f",
         "--stage-journal", "/run/p.stage.jsonl",
         "--stack-dump-file", "/cp/stack-dump.txt",
         "--stack-dump-artifact", "/run/.runtime-metrics/p.stack-dump.txt"]
    )
    assert parsed.stage_journal == "/run/p.stage.jsonl"
    assert parsed.stack_dump_file == "/cp/stack-dump.txt"
    assert parsed.stack_dump_artifact == "/run/.runtime-metrics/p.stack-dump.txt"

    default = build_parser().parse_args(["--equiv", "a", "b", "-f", "f"])
    assert default.stage_journal is None
    assert default.stack_dump_file is None
    assert default.stack_dump_artifact is None


@pytest.mark.parametrize("runner", ["eqbench_run_all_32jobs.sh", "neqbench_run_all_32jobs.sh"])
def test_runners_pass_a_journal_and_both_dump_paths(runner):
    source = (REPO_ROOT / runner).read_text(encoding="utf-8")
    assert "--stage-journal" in source
    assert "--stack-dump-file" in source
    assert "--stack-dump-artifact" in source
    # journal は log の隣、artifact は run dir の .runtime-metrics、
    # 一時 dump は checkpoint の下（cleanup で消える側）。
    assert ".stage.jsonl" in source
    assert ".runtime-metrics" in source
    assert "stack-dump.txt" in source


# --------------------------------------------------------------------------
# 10. 実子プロセス + JVM（opt-in）
# --------------------------------------------------------------------------


_JVM_CHILD = """
import sys, threading, time
sys.path.insert(0, "__REPO_ROOT__")
from pathlib import Path
from types import SimpleNamespace

from scripts.function_tracer_pcode.cli.pair_diagnostics import install_pair_diagnostics
from scripts.function_tracer_pcode.config import apply_runtime_environment
from scripts.function_tracer_pcode.ghidra.pyghidra_support import (
    load_pyghidra, start_headless_pyghidra,
)

journal_path, dump_path, artifact_path, ready_path, stop_path = sys.argv[1:6]

# 実装と同じ順序: handler 登録 -> JVM 起動。
state = install_pair_diagnostics(SimpleNamespace(
    stage_journal=journal_path,
    stack_dump_file=dump_path,
    stack_dump_artifact=artifact_path,
))
assert state.handler_registered is True

def _idle():
    while not Path(stop_path).exists():
        time.sleep(0.05)

worker = threading.Thread(target=_idle, name="probe-worker", daemon=True)
worker.start()

runtime_env = apply_runtime_environment()
pyghidra = load_pyghidra()
start_headless_pyghidra(pyghidra, install_dir=(
    Path(runtime_env.ghidra_install_dir) if runtime_env.ghidra_install_dir else None
))

# 「start を呼んだ」ではなく「JVM が実際に上がっている」ことを記録する。
import jpype
from scripts.function_tracer_pcode.core.stage_journal import journal_note

journal_note("jvm_state_after_launch", {
    "jvm_started": bool(jpype.isJVMStarted()),
    "python_threads": threading.active_count(),
})

Path(ready_path).write_text("ready")
deadline = time.monotonic() + 180
while time.monotonic() < deadline and not Path(stop_path).exists():
    time.sleep(0.05)
sys.exit(7)
"""


def _run_jvm_child(tmp_path, label, *, send_signal):
    journal_path = tmp_path / f"{label}.stage.jsonl"
    dump_path = tmp_path / f"{label}.stack-dump.txt"
    artifact_path = tmp_path / ".runtime-metrics" / f"{label}.stack-dump.txt"
    ready = tmp_path / f"{label}.ready"
    stop = tmp_path / f"{label}.stop"
    script = tmp_path / f"{label}.py"
    script.write_text(_JVM_CHILD.replace("__REPO_ROOT__", str(REPO_ROOT)), encoding="utf-8")

    child = subprocess.Popen(
        [sys.executable, "-B", str(script), str(journal_path), str(dump_path),
         str(artifact_path), str(ready), str(stop)],
        cwd=str(REPO_ROOT),
    )
    dump_before = dump_after = 0
    try:
        deadline = time.monotonic() + 300
        while time.monotonic() < deadline and not ready.exists() and child.poll() is None:
            time.sleep(0.1)
        assert ready.exists(), f"{label}: child never started the JVM"
        if send_signal:
            dump_before = dump_path.stat().st_size if dump_path.exists() else 0
            os.kill(child.pid, signal.SIGUSR1)
            observed = time.monotonic() + 30
            while time.monotonic() < observed:
                dump_after = dump_path.stat().st_size if dump_path.exists() else 0
                if dump_after > dump_before:
                    break
                time.sleep(0.1)
            # 診断 signal でプロセスが死んでいないこと。
            assert child.poll() is None, f"{label}: the diagnostic signal killed the child"
    finally:
        stop.write_text("stop")
        child.wait(timeout=120)
    return SimpleNamespace(
        returncode=child.returncode,
        journal_path=journal_path,
        dump_path=dump_path,
        dump_before=dump_before,
        dump_after=dump_after,
    )


@pytest.mark.skipif(
    os.environ.get("RUN_PYGHIDRA_REGRESSIONS") != "1",
    reason="needs a real Ghidra/PyGhidra install (RUN_PYGHIDRA_REGRESSIONS=1)",
)
def test_child_registers_handler_before_jvm_and_survives_signal(tmp_path):
    """実装と同じ起動順序で JVM を上げ、外から SIGUSR1 を送って確認する。

    1. JVM 起動前に handler を登録する
    2. PyGhidra / JVM を起動する
    3. 親から子 PID へ SIGUSR1 を送る
    4. dump file が増える（Python の全 thread stack が取れる）
    5. 子は signal で終了していない
    6. signal 無しの対照と最終 returncode が一致する
    """
    signalled = _run_jvm_child(tmp_path, "signalled", send_signal=True)
    control = _run_jvm_child(tmp_path, "control", send_signal=False)

    # 4: dump が実際に増えた
    assert signalled.dump_after > signalled.dump_before
    dump = signalled.dump_path.read_text(encoding="utf-8", errors="replace")
    # 5 (all_threads=True): main thread 以外の Python thread も入っている
    assert dump.count("Thread 0x") + dump.count("Current thread") >= 2
    assert 'File "' in dump

    # 6: signal あり / なしで最終状態が一致（disposition を変えない）
    assert signalled.returncode == control.returncode == 7
    assert not control.dump_path.exists() or control.dump_path.stat().st_size == 0

    # 1 / 2: 登録は JVM より前だった、という事実が journal に残る
    rows, broken = read_journal(signalled.journal_path)
    assert broken == 0
    registered = events(rows, EVENT_HANDLER_REGISTERED)
    assert len(registered) == 1
    payload = registered[0]["payload"]
    assert payload["registered_before_jvm"] is True
    assert payload["readiness_basis"] == "faulthandler_register_returned"
    assert payload["signal"] == "SIGUSR1"
    assert payload["start_token"] is not None

    # 2 の裏取り: signal を送った時点で JVM は本当に動いていた
    # （`start_headless_pyghidra` を呼んだ、では JVM の横取りを試したことに
    #  ならない）。handler 登録はその JVM 起動より前の行として残っている。
    jvm_rows = [
        row for row in rows
        if row["event"] == EVENT_NOTE
        and row["payload"].get("note") == "jvm_state_after_launch"
    ]
    assert len(jvm_rows) == 1
    assert jvm_rows[0]["payload"]["jvm_started"] is True
    assert jvm_rows[0]["payload"]["python_threads"] >= 2
    assert registered[0]["seq"] < jvm_rows[0]["seq"]


# --------------------------------------------------------------------------
# 11. runner: 1 journal = 1 execution（再実行で前回の行を残さない）
# --------------------------------------------------------------------------
#
# journal path は pair 固定（`${log%.log}.stage.jsonl`）で、`StageJournal` は
# 追記で開く。同じ pair をもう一度実行したときに前回の journal が残っていると、
# 1 file の中で `seq` が 1..N -> 1..M と巻き戻り、古い `handler_registered` /
# pid / start_token が current execution の evidence に見えてしまう。
#
# 契約: runner は「この pair を新しく実行する」と確定したあと（skip 判定は済み）、
# child を起こす前に既存 journal を捨てる。`.log` を `>` で開き直すのと同じ境界。
#
# ここでは runner の **実際の `run_pair`** を取り出して bash で走らせる。
# 呼び先はすべて stub にするので途中で失敗してよい（`|| true`）。判定するのは
# 「journal が消えたか」と「消えたのは最初の child 起動より前か」だけなので、
# `rm` を child 起動より後ろへ動かすとこの test が落ちる。

RUNNERS = ("eqbench_run_all_32jobs.sh", "neqbench_run_all_32jobs.sh")


def _extract_shell_function(source: str, name: str) -> str:
    """`name() {` から、桁 0 の `}` までを取り出す（runner の関数定義の形）。"""
    lines = source.splitlines()
    start = next(
        index for index, line in enumerate(lines) if line.startswith(f"{name}() {{")
    )
    for index in range(start + 1, len(lines)):
        if lines[index] == "}":
            return "\n".join(lines[start:index + 1])
    raise AssertionError(f"unterminated shell function {name}")


_RUN_PAIR_HARNESS = """
set -u
export PATH="__STUBS__:$PATH"

# runner が run_pair の外で用意する変数（この test で意味を持つものだけ）。
EQBENCH_RUN_TMPDIR="__TMP__/runtmp"
RUN_TMP="__TMP__/runtmp"
SCRIPT_DIR="__TMP__"
OUTPUT_BASE_DIR="__TMP__/out"
PYTHON_BIN="__STUBS__/python-probe"
EQUIV_TIMEOUT=10; DECOMPILE_TIMEOUT=60; PAIRWISE_TIMEOUT=5; PAIRWISE_TIMEOUT_HARD=30
PAIR_PROCESS_TIMEOUT_SECONDS=240; PAIR_PROCESS_KILL_AFTER_SECONDS=30
PAIR_PROCESS_TIMEOUT=240s; PAIR_PROCESS_KILL_AFTER=30s
PAIR_PROCESS_DEADLINE_POLICY_DIGEST=deadbeef
PROCESS_SUPERVISOR_KEY_ID=k; PROCESS_SUPERVISOR_KEY_FILE=/dev/null
PROCESS_WORKER_KEY_ID=k; PROCESS_WORKER_KEY_FILE=/dev/null
SUPERVISOR_KEY_ID=k; SUPERVISOR_KEY=/dev/null
WORKER_KEY_ID=k; WORKER_KEY=/dev/null
PAIR_STATUS_SIGNING_PRIVATE_KEY_FILE=/dev/null
PAIR_STATUS_VERIFICATION_KEY_FILE=/dev/null
PAIR_PRIVATE_KEY=/dev/null; PAIR_PUBLIC_KEY=/dev/null
EQBENCH_DEBUG=0; EQBENCH_PROGRESS_INTERVAL_SECONDS=1
FT_EXPANDER_DEDUP_CASE_LIMIT=0; FT_CALLEE_UNBOUND_REUSE=0
FT_CALLEE_UNBOUND_REUSE_SHADOW=0
EQBENCH_TMPDIR="__TMP__/runtmp"; PROCESS_CLEANUP_FAILURES="__TMP__/cleanup-failures"
SOURCE_PAIR_COUNT=1

# runner の他の関数はこの test の対象ではないので握り潰す。
write_pair_progress_receipt() { :; }
supervisor_projection_is_terminal() { return 0; }
validate_current_pair_status() { printf 'UNKNOWN'; }
cleanup_pair_process_authority_with_run_health() { return 0; }
progress_update() { :; }

__FUNCTION__

run_pair __ARGS__ || true
"""

_PYTHON_PROBE = """#!/bin/sh
# 最初に child 側の python が呼ばれた時点で、前回 execution の成果物が
# 残っていたら記録する（journal と、journal が正本として宣言する dump 退避先）。
if [ ! -f "$PROBE_MARKER" ]; then
  state=""
  if [ -f "$PROBE_JOURNAL" ]; then state="journal_present"; else state="journal_absent"; fi
  if [ -f "$PROBE_ARTIFACT" ]; then
    state="$state artifact_present"
  else
    state="$state artifact_absent"
  fi
  echo "$state" > "$PROBE_MARKER"
fi
echo "stub"
exit 0
"""


def _run_pair_harness(tmp_path, runner, journal, extra_env=None):
    """runner の実 `run_pair` を stub 環境で 1 回走らせる。"""
    stubs = tmp_path / "stubs"
    stubs.mkdir(exist_ok=True)
    probe = stubs / "python-probe"
    probe.write_text(_PYTHON_PROBE, encoding="utf-8")
    probe.chmod(0o755)
    # /usr/bin/time は eq runner が直接叩くので、同名 stub を PATH ではなく
    # 関数で潰せない。存在しなくても run_pair は先へ進めないだけで、判定には
    # 影響しない（journal の削除はそれより前）。
    (tmp_path / "runtmp").mkdir(exist_ok=True)
    (tmp_path / "out").mkdir(exist_ok=True)

    source = (REPO_ROOT / runner).read_text(encoding="utf-8")
    function = _extract_shell_function(source, "run_pair")
    out_dir = journal.parent
    if runner.startswith("eq"):
        args = ('"sample" "f" "B1" "B2" "/left" "/right" "%s" 1 1 "/target"' % out_dir)
    else:
        args = ('"sample" "f" "N_B1" "O_B2" "/left" "/right" "%s" 1 1 "/target" 1 1 1'
                % out_dir)
    script = (
        _RUN_PAIR_HARNESS
        .replace("__STUBS__", str(stubs))
        .replace("__TMP__", str(tmp_path))
        .replace("__FUNCTION__", function)
        .replace("__ARGS__", args)
    )
    marker = tmp_path / "probe-marker"
    if marker.exists():
        marker.unlink()
    env = dict(os.environ)
    env.update({
        "PROBE_MARKER": str(marker),
        "PROBE_JOURNAL": str(journal),
        "PROBE_ARTIFACT": str(_pair_artifact_path(journal)),
    })
    env.update(extra_env or {})
    subprocess.run(["bash", "-c", script], env=env, capture_output=True, timeout=120)
    return marker


def _pair_artifact_path(journal):
    """journal が正本として宣言する dump 退避先（run dir の `.runtime-metrics`）。"""
    name = journal.name[: -len(".stage.jsonl")]
    return journal.parent / ".runtime-metrics" / f"{name}.stack-dump.txt"


def _pair_journal_path(tmp_path, runner):
    out = tmp_path / "out" / "sample" / "f"
    out.mkdir(parents=True, exist_ok=True)
    name = "f_B1_B2" if runner.startswith("eq") else "f_N_B1_O_B2"
    return out / f"{name}.stage.jsonl"


@pytest.mark.parametrize("runner", RUNNERS)
def test_runner_drops_the_previous_journal_before_relaunching_a_pair(tmp_path, runner):
    """再実行する pair の journal は、child を起こす前に捨てられる。"""
    journal = _pair_journal_path(tmp_path, runner)
    log = journal.with_name(journal.name[: -len(".stage.jsonl")] + ".log")
    # 前回 execution の journal（seq 1..3、古い pid / handler_registered つき）。
    previous = StageJournal(journal)
    previous.append(EVENT_HANDLER_REGISTERED, stage="stack_dump_handler",
                    payload={"pid": 424242, "start_token": "linux-proc-starttime-1"})
    previous.append(EVENT_STAGE_START, stage="check")
    previous.append(EVENT_STAGE_END, stage="check", seconds=1.0)
    previous.close()
    log.write_text("previous execution log\n", encoding="utf-8")
    # 前回 execution の dump 退避先も置いておく（PR-124-C が読む正本 path）。
    artifact = _pair_artifact_path(journal)
    artifact.parent.mkdir(parents=True, exist_ok=True)
    artifact.write_text("stack dump from the previous execution\n", encoding="utf-8")
    assert journal.exists()
    old_rows, _ = read_journal(journal)
    assert len(old_rows) == 3

    marker = _run_pair_harness(tmp_path, runner, journal)

    # 1. 前回の journal も、正本として宣言する dump 退避先の残骸も残っていない。
    assert not journal.exists(), (
        f"{runner}: run_pair left the previous execution's journal in place"
    )
    assert not artifact.exists(), (
        f"{runner}: run_pair left the previous execution's dump artifact in place"
    )
    # 2. 消えたのは最初の child 起動より前（= 古い行 / 古い dump が current の
    #    evidence になる窓が無い）。
    assert marker.exists(), f"{runner}: run_pair never reached a child launch"
    assert marker.read_text().split() == ["journal_absent", "artifact_absent"]


@pytest.mark.parametrize("runner", RUNNERS)
def test_only_run_pair_removes_a_stage_journal(runner):
    """journal を消すのは `run_pair`（= 新規実行が確定した経路）だけ。

    skip した pair の journal を消す経路を作らないことの静的な裏付け。
    skip 側の実挙動そのものは固定 subset の再実行（PR 本文の E1）で確認する。
    """
    source = (REPO_ROOT / runner).read_text(encoding="utf-8")
    # journal path を持つ変数名を assignment から拾う（名前を test に埋めない）。
    holders = set(re.findall(r'(\w+)="\$\{log[^"]*%\.log\}\.stage\.jsonl"', source))
    assert holders, "no shell variable holds the pair journal path"
    removals = [
        line.strip() for line in source.splitlines()
        if line.strip().startswith("rm ")
        and any(f'"${holder}"' in line for holder in holders)
    ]
    assert len(removals) == 1, removals
    run_pair = _extract_shell_function(source, "run_pair")
    assert removals[0] in run_pair
    # dump 退避先の残骸も同じ関数の中で 1 回だけ捨てる。
    artifact_holders = set(
        re.findall(r'^\s*(?:local\s+)?(\w+)=.*\.stack-dump\.txt', source, re.M)
    ) & set(re.findall(r'rm -f -- "\$(\w+)"', source))
    assert len(artifact_holders) == 1, artifact_holders
    # 削除は supervisor / equiv コマンドの組み立てより前にある。
    assert run_pair.index(removals[0]) < run_pair.index("supervisor_cmd")


@pytest.mark.parametrize("runner", RUNNERS)
def test_a_fresh_journal_restarts_the_sequence_at_one(tmp_path, runner):
    """削除後に同じ path へ書き直すと seq は 1 から始まる（巻き戻りが無い）。"""
    journal = _pair_journal_path(tmp_path, runner)
    stale = StageJournal(journal)
    for _ in range(4):
        stale.append(EVENT_STAGE_START, stage="check")
    stale.close()
    assert [row["seq"] for row in read_journal(journal)[0]] == [1, 2, 3, 4]

    _run_pair_harness(tmp_path, runner, journal)
    assert not journal.exists()

    # 新しい child が同じ path を開き直した後の journal。
    fresh = StageJournal(journal)
    fresh.append(EVENT_NOTE, payload={"note": "pair_journal_opened"})
    fresh.append(EVENT_HANDLER_REGISTERED, stage="stack_dump_handler")
    fresh.close()
    rows, broken = read_journal(journal)
    assert broken == 0
    assert [row["seq"] for row in rows] == [1, 2]
    # 1 journal = 1 execution: 開始行はちょうど 1 本。
    opened = [
        row for row in rows
        if row["event"] == EVENT_NOTE and row["payload"].get("note") == "pair_journal_opened"
    ]
    assert len(opened) == 1 and opened[0]["seq"] == 1


def test_a_journal_holding_two_executions_is_detectable(tmp_path):
    """混在した journal は「検出できる」形にしておく（回帰時に黙って通さない）。"""
    journal = tmp_path / "mixed.stage.jsonl"
    first = StageJournal(journal)
    first.append(EVENT_NOTE, payload={"note": "pair_journal_opened"})
    first.append(EVENT_STAGE_END, stage="check", seconds=1.0)
    first.close()
    second = StageJournal(journal)  # 削除せずに開き直す = 回帰したときの姿
    second.append(EVENT_NOTE, payload={"note": "pair_journal_opened"})
    second.close()

    rows, _ = read_journal(journal)
    seqs = [row["seq"] for row in rows]
    opened = [
        row for row in rows
        if row["event"] == EVENT_NOTE and row["payload"].get("note") == "pair_journal_opened"
    ]
    # 検出条件はこの 2 つ（実 run の evidence でも同じ 2 つを数える）。
    assert seqs != sorted(seqs) or len(set(seqs)) != len(seqs)
    assert len(opened) == 2


def test_registered_before_jvm_is_a_probe_observation_not_a_proof(monkeypatch):
    """`jvm_already_started()` は判断できないとき False を返す（= 観測しなかった）。

    したがって `registered_before_jvm: true` は「probe で JVM started を観測
    しなかった」であって、それ単独で「JVM より前だった」ことの証明ではない。
    production path の根拠は呼び出し順（`test_the_handler_is_installed_before_
    the_jvm_starts_in_the_cli`）と実 JVM 子プロセス test の行順序。
    """
    # jpype が無い -> 観測できない -> False
    monkeypatch.delitem(sys.modules, "jpype", raising=False)
    assert jvm_already_started() is False
    # jpype はあるが probe が壊れている -> 観測できない -> False（true とは言わない）
    class _Broken:
        @staticmethod
        def isJVMStarted():
            raise RuntimeError("jvm probe unavailable")

    monkeypatch.setitem(sys.modules, "jpype", _Broken)
    assert jvm_already_started() is False
    # probe が「起動済み」と答えたときだけ True
    monkeypatch.setitem(sys.modules, "jpype", SimpleNamespace(isJVMStarted=lambda: True))
    assert jvm_already_started() is True


def test_chain_false_is_documented_as_no_chaining_not_as_override_protection():
    """`chain=False` の説明が「後からの上書きを防ぐ」になっていないこと。"""
    source = (PACKAGE_ROOT / "cli" / "pair_diagnostics.py").read_text(encoding="utf-8")
    assert "previous handler へ連鎖しない" in source
    assert "あとから別の handler が" in source
    assert "防ぐ設定ではない" in source
