# -*- coding: utf-8 -*-
"""Issue #124 PR-124-C: 非ブロッキング deadline 制御と診断 worker（D1〜D11）。

固定している契約:

* deadline は **開始時に 1 回だけ**決まり、診断の完了・失敗・ハングで延びない。
* kill 開始は `deadline` 以降かつ `deadline + 0.5s` 以内。
* readiness を確認できなければ SIGUSR1 を送らない（fail-closed）。
* 送信は child PID だけ（process group へは送らない）。
* 診断 worker を join しない。
"""

from __future__ import annotations

import json
import os
import signal
import subprocess
import sys
import threading
import time
from pathlib import Path

import pytest

from scripts.function_tracer_pcode.authority.process import stack_dump_diagnostic as diag
from scripts.function_tracer_pcode.authority.process.stack_dump_diagnostic import (
    DEADLINE_JITTER_ALLOWANCE_SECONDS,
    POLL_SLICE_SECONDS,
    StackDumpDiagnostic,
    StackDumpDiagnosticConfig,
)
from scripts.function_tracer_pcode.core.stage_journal import (
    EVENT_HANDLER_REGISTERED,
    STAGE_JOURNAL_SCHEMA,
)

CHILD_PID = 4242
START_TOKEN = "linux-proc-starttime-1234"


# ---------------------------------------------------------------------------
# journal / config の組み立て
# ---------------------------------------------------------------------------


def _row(seq, event, *, stage=None, pid=CHILD_PID, payload=None, seconds=None):
    return json.dumps({
        "schema": STAGE_JOURNAL_SCHEMA,
        "seq": seq,
        "event": event,
        "stage": stage,
        "seconds": seconds,
        "t_monotonic": float(seq),
        "t_epoch": 1000.0 + seq,
        "pid": pid,
        "payload": payload or {},
    }, sort_keys=True)


def handler_payload(dump_tmp, artifact, *, pid=CHILD_PID, token=START_TOKEN):
    return {
        "pid": pid,
        "start_token": token,
        "dump_path_tmp": str(dump_tmp),
        "dump_artifact_path": None if artifact is None else str(artifact),
        "dump_artifact_path_status": "declared" if artifact else "unset",
        "registered_before_jvm": True,
        "signal": "SIGUSR1",
        "signal_number": int(signal.SIGUSR1),
        "all_threads": True,
        "chain": False,
        "readiness_basis": "faulthandler_register_returned",
        "sigcgt_probe": {"authoritative": False},
    }


def write_journal(path, payload, *, opened=True, extra_rows=()):
    lines = []
    seq = 0
    if opened:
        seq += 1
        lines.append(_row(seq, "note", payload={
            "note": "pair_journal_opened", "journal_path": str(path),
        }))
    if payload is not None:
        seq += 1
        lines.append(_row(
            seq, EVENT_HANDLER_REGISTERED, stage="stack_dump_handler", payload=payload,
        ))
    for row in extra_rows:
        seq += 1
        lines.append(_row(seq, row[0], stage=row[1], payload=row[2] if len(row) > 2 else None))
    Path(path).write_text("\n".join(lines) + "\n", encoding="utf-8")
    return seq


@pytest.fixture()
def pair(tmp_path):
    journal = tmp_path / "pair.stage.jsonl"
    checkpoint = tmp_path / "checkpoint"
    checkpoint.mkdir()
    dump_tmp = checkpoint / "stack-dump.txt"
    dump_tmp.write_bytes(b"")
    metrics = tmp_path / ".runtime-metrics"
    metrics.mkdir()
    artifact = metrics / "pair.stack-dump.txt"
    status = metrics / "pair.stack-dump.status.json"
    write_journal(journal, handler_payload(dump_tmp, artifact))
    return {
        "journal": journal, "dump_tmp": dump_tmp, "artifact": artifact,
        "status": status, "checkpoint": checkpoint,
    }


def _config(pair, *, lead=2.0, observe=0.2, artifact=True, status=True, journal=True):
    return StackDumpDiagnosticConfig(
        journal_path=str(pair["journal"]) if journal else None,
        dump_path_tmp=str(pair["dump_tmp"]),
        dump_artifact_path=str(pair["artifact"]) if artifact else None,
        status_output_path=str(pair["status"]) if status else None,
        lead_seconds=lead,
        observe_seconds=observe,
    )


def _diagnostic(pair, *, timeout=10.0, alive=True, **kwargs):
    return StackDumpDiagnostic(
        _config(pair, **kwargs),
        child_pid=CHILD_PID,
        start_token=START_TOKEN,
        timeout_seconds=timeout,
        identity_verifier=lambda: alive,
    )


class _RecordingSender:
    """`os.pidfd_open` / `signal.pidfd_send_signal` の差し替え。"""

    def __init__(self, *, fail=None):
        self.opened = []
        self.sent = []
        self.fail = fail

    def open(self, pid, flags):
        self.opened.append((pid, flags))
        return os.open(os.devnull, os.O_RDONLY)

    def send(self, fd, number):
        if self.fail is not None:
            raise self.fail
        self.sent.append(number)


@pytest.fixture()
def sender(monkeypatch):
    recorder = _RecordingSender()
    monkeypatch.setattr(os, "pidfd_open", recorder.open, raising=False)
    monkeypatch.setattr(signal, "pidfd_send_signal", recorder.send, raising=False)
    return recorder


# ---------------------------------------------------------------------------
# readiness / 送信（D8 / D9 と、送信契約）
# ---------------------------------------------------------------------------


def test_signal_is_sent_only_with_registered_handler_and_matching_identity(pair, sender):
    diagnostic = _diagnostic(pair)
    diagnostic.request_async()
    _join_worker(diagnostic)
    assert diagnostic.handler_registered is True
    assert diagnostic.signal_sent is True
    assert sender.sent == [int(signal.SIGUSR1)]
    # 送信先は child PID だけ。process group（負の pid）へは送らない。
    assert sender.opened == [(CHILD_PID, 0)]
    assert diagnostic.unavailable_reason is None


def test_no_signal_without_handler_registered_row(pair, sender):
    """D8: registration が確認できない journal には送らない。"""
    write_journal(pair["journal"], None)
    diagnostic = _diagnostic(pair)
    diagnostic.request_async()
    _join_worker(diagnostic)
    assert diagnostic.signal_sent is False
    assert sender.sent == []
    assert diagnostic.unavailable_reason == "handler_not_registered"


def test_no_signal_when_registration_failed_note_only(pair, sender):
    """register 失敗時の `note` だけでは ready にしない。"""
    Path(pair["journal"]).write_text("\n".join([
        _row(1, "note", payload={"note": "pair_journal_opened"}),
        _row(2, "note", payload={
            "note": "handler_registration_failed:OSError", "phase": "register",
        }),
    ]) + "\n", encoding="utf-8")
    diagnostic = _diagnostic(pair)
    diagnostic.request_async()
    _join_worker(diagnostic)
    assert diagnostic.signal_sent is False
    assert diagnostic.unavailable_reason == "handler_not_registered"


def test_sigcgt_probe_alone_does_not_make_it_ready(pair, sender):
    """SigCgt のビットが立っていても register 由来の行が無ければ送らない。"""
    Path(pair["journal"]).write_text("\n".join([
        _row(1, "note", payload={"note": "pair_journal_opened"}),
        _row(2, "note", payload={
            "note": "sigcgt_probe",
            "sigcgt_probe": {"sigcgt": "0000000000000202", "signal_bit_set": True},
        }),
    ]) + "\n", encoding="utf-8")
    diagnostic = _diagnostic(pair)
    diagnostic.request_async()
    _join_worker(diagnostic)
    assert diagnostic.signal_sent is False
    assert sender.sent == []


@pytest.mark.parametrize("pid,token,expected", [
    (CHILD_PID + 1, START_TOKEN, "process_identity_changed"),
    (CHILD_PID, "linux-proc-starttime-9999", "process_identity_changed"),
])
def test_no_signal_on_pid_or_start_token_mismatch(pair, sender, pid, token, expected):
    """D9: pid / start_token が current child と違えば送らない。"""
    write_journal(
        pair["journal"],
        handler_payload(pair["dump_tmp"], pair["artifact"], pid=pid, token=token),
    )
    diagnostic = _diagnostic(pair)
    diagnostic.request_async()
    _join_worker(diagnostic)
    assert diagnostic.signal_sent is False
    assert sender.sent == []
    assert diagnostic.unavailable_reason == expected


def test_no_signal_when_declared_dump_path_is_not_this_pair(pair, sender, tmp_path):
    """別 pair の dump 先を宣言している行を readiness に使わない。"""
    payload = handler_payload(tmp_path / "other" / "stack-dump.txt", pair["artifact"])
    write_journal(pair["journal"], payload)
    diagnostic = _diagnostic(pair)
    diagnostic.request_async()
    _join_worker(diagnostic)
    assert diagnostic.signal_sent is False
    assert diagnostic.unavailable_reason == "dump_path_mismatch"


def test_signal_failure_is_recorded_and_does_not_raise(pair, monkeypatch):
    """D4: `os.kill` 相当が失敗しても例外にせず理由を残す。"""
    recorder = _RecordingSender(fail=PermissionError(1, "denied"))
    monkeypatch.setattr(os, "pidfd_open", recorder.open, raising=False)
    monkeypatch.setattr(signal, "pidfd_send_signal", recorder.send, raising=False)
    diagnostic = _diagnostic(pair)
    diagnostic.request_async()
    _join_worker(diagnostic)
    assert diagnostic.signal_sent is False
    assert diagnostic.unavailable_reason == "signal_failed:PermissionError"


def test_no_signal_when_pidfd_binding_is_unavailable(pair, monkeypatch):
    """pidfd が無い環境では送らない（PID 再利用と競合し得るため）。"""
    monkeypatch.delattr(os, "pidfd_open", raising=False)
    monkeypatch.delattr(signal, "pidfd_send_signal", raising=False)
    diagnostic = _diagnostic(pair)
    diagnostic.request_async()
    _join_worker(diagnostic)
    assert diagnostic.signal_sent is False
    assert diagnostic.unavailable_reason == "identity_binding_unavailable"


def test_no_signal_after_child_exited(pair, sender):
    """D5: 診断中に child が終了していたら送らない。"""
    diagnostic = _diagnostic(pair, alive=False)
    diagnostic.request_async()
    _join_worker(diagnostic)
    assert diagnostic.signal_sent is False
    assert sender.sent == []
    assert diagnostic.unavailable_reason == "process_exited"


def test_cancel_before_send_stops_the_worker(pair, sender):
    diagnostic = _diagnostic(pair)
    diagnostic.cancel_future_requests()
    diagnostic.request_async()
    assert diagnostic.requested is False
    assert sender.sent == []


def test_broken_journal_is_reported_not_raised(pair, sender):
    """D4: journal が壊れていても例外にしない。"""
    Path(pair["journal"]).write_text("{not json\n", encoding="utf-8")
    diagnostic = _diagnostic(pair)
    diagnostic.request_async()
    _join_worker(diagnostic)
    assert diagnostic.signal_sent is False
    assert diagnostic.unavailable_reason == "journal_empty"


def test_non_regular_journal_is_not_opened(tmp_path, pair, sender):
    fifo = tmp_path / "fifo.stage.jsonl"
    os.mkfifo(fifo)
    config = StackDumpDiagnosticConfig(
        journal_path=str(fifo),
        dump_path_tmp=str(pair["dump_tmp"]),
        dump_artifact_path=str(pair["artifact"]),
        status_output_path=str(pair["status"]),
        lead_seconds=1.0,
    )
    diagnostic = StackDumpDiagnostic(
        config, child_pid=CHILD_PID, start_token=START_TOKEN,
        timeout_seconds=10.0, identity_verifier=lambda: True,
    )
    diagnostic.request_async()
    _join_worker(diagnostic)
    assert diagnostic.unavailable_reason == "journal_not_regular_file"
    assert diagnostic.signal_sent is False


def test_disabled_when_lead_is_not_before_the_deadline(pair):
    """D10: `lead >= timeout` は `disabled`。待ち方の構造は変わらない。"""
    diagnostic = _diagnostic(pair, timeout=1.0, lead=2.0)
    assert diagnostic.enabled is False
    assert diagnostic.unavailable_reason == "disabled"
    diagnostic.request_async()
    assert diagnostic.requested is False


def test_disabled_without_journal_or_dump_path(pair):
    diagnostic = _diagnostic(pair, journal=False)
    assert diagnostic.enabled is False
    assert diagnostic.unavailable_reason == "disabled"


# ---------------------------------------------------------------------------
# dump の観測と退避（D6 / D7）
# ---------------------------------------------------------------------------


def test_dump_growth_is_observed_and_persisted(pair, sender):
    """D6: dump が増えれば観測し、artifact へ退避する。"""
    def _grow():
        time.sleep(0.02)
        Path(pair["dump_tmp"]).write_text("Thread 0x1 (most recent call first):\n")

    diagnostic = _diagnostic(pair, observe=1.0)
    thread = threading.Thread(target=_grow)
    thread.start()
    diagnostic.request_async()
    _join_worker(diagnostic)
    thread.join()
    assert diagnostic.dump_observed is True
    assert diagnostic.sent_but_unobserved is False
    assert diagnostic.persist_artifact() == "copied"
    assert Path(pair["artifact"]).read_text().startswith("Thread 0x1")


def test_sent_but_unobserved_is_not_the_same_as_missing(pair, sender):
    """D7: 観測できなかったことと、dump が無いことを混同しない。"""
    diagnostic = _diagnostic(pair, observe=0.05)
    diagnostic.request_async()
    _join_worker(diagnostic)
    assert diagnostic.signal_sent is True
    assert diagnostic.dump_observed is False
    assert diagnostic.sent_but_unobserved is True
    # 観測後に child が書いた dump も、退避時に拾って `copied` になる。
    Path(pair["dump_tmp"]).write_text("Thread 0x1 (most recent call first):\n")
    assert diagnostic.persist_artifact() == "copied"
    payload = diagnostic.status_payload()
    assert payload["sent_but_unobserved"] is True
    assert payload["artifact_status"] == "copied"


def test_missing_is_claimed_only_after_checking_the_destination(pair, sender):
    diagnostic = _diagnostic(pair, observe=0.02)
    diagnostic.request_async()
    _join_worker(diagnostic)
    assert diagnostic.persist_artifact() == "missing"
    assert diagnostic.status_payload()["artifact_status"] == "missing"


def test_artifact_is_persisted_regardless_of_outcome(pair, sender):
    """診断を要求すらしていない（= 正常終了した）pair の dump も保存する。"""
    Path(pair["dump_tmp"]).write_text("Current thread 0x1 (most recent call first):\n")
    diagnostic = _diagnostic(pair)
    assert diagnostic.requested is False
    assert diagnostic.persist_artifact() == "copied"
    assert Path(pair["artifact"]).exists()


def test_handler_registration_is_unknown_until_the_worker_looks(pair, sender):
    """要求していない pair の `handler_registered` は `False` ではなく `None`。

    観測していないことを「handler が無かった」と読ませない（集計側は
    `(unknown)` bucket に入れる）。
    """
    diagnostic = _diagnostic(pair)
    assert diagnostic.handler_registered is None
    assert diagnostic.status_payload()["handler_registered"] is None
    # worker が journal を見て readiness を確認できなければ False になる。
    write_journal(pair["journal"], None)
    looked = _diagnostic(pair)
    looked.request_async()
    _join_worker(looked)
    assert looked.handler_registered is False


def test_artifact_status_is_unset_without_a_destination(pair):
    diagnostic = _diagnostic(pair, artifact=False)
    Path(pair["dump_tmp"]).write_text("Current thread 0x1:\n")
    assert diagnostic.persist_artifact() == "unset"


def test_status_sidecar_round_trips(pair, sender):
    diagnostic = _diagnostic(pair, observe=0.02)
    diagnostic.request_async()
    _join_worker(diagnostic)
    diagnostic.persist_artifact()
    written = diagnostic.write_status()
    assert written == str(pair["status"])
    payload = diag.read_stack_dump_status(pair["status"])
    assert payload["schema"] == "pair-stack-dump-status-v1"
    assert payload["child_pid"] == CHILD_PID
    assert payload["child_start_token"] == START_TOKEN
    assert payload["handler_registered"] is True
    assert payload["signal_sent"] is True
    assert payload["dump_observed"] is False
    assert payload["sent_but_unobserved"] is True
    assert payload["artifact_status"] == "missing"


def _join_worker(diagnostic, timeout=5.0):
    """**production では join しない**。test だけが worker の完了を待つ。"""
    thread = diagnostic._thread
    if thread is not None:
        thread.join(timeout)
        assert not thread.is_alive()


# ---------------------------------------------------------------------------
# deadline ループ（D1〜D5 / D10 / D11）
# ---------------------------------------------------------------------------


class _FakeProcess:
    """`subprocess.Popen` の、監視ループが触る面だけを持つ stub。"""

    def __init__(self, *, exits_after=None, pid=CHILD_PID):
        self.pid = pid
        self.returncode = None
        self._exit_at = None if exits_after is None else time.monotonic() + exits_after
        self.wait_calls = []
        self.max_wait_timeout = 0.0

    def poll(self):
        if self._exit_at is not None and time.monotonic() >= self._exit_at:
            self.returncode = 0
        return self.returncode

    def wait(self, timeout=None):
        self.wait_calls.append(timeout)
        if timeout is not None:
            self.max_wait_timeout = max(self.max_wait_timeout, timeout)
        limit = time.monotonic() + (timeout or 0.0)
        while time.monotonic() < limit:
            if self.poll() is not None:
                return self.returncode
            time.sleep(0.005)
        if self.poll() is not None:
            return self.returncode
        raise subprocess.TimeoutExpired("child", timeout)


class _Command:
    """`_wait_for_child_until_deadline` を切り出して呼ぶための最小 host。"""

    _wait_for_child_until_deadline = (
        __import__(
            "scripts.function_tracer_pcode.authority.process.supervisor_command",
            fromlist=["ProcessSupervisorCommand"],
        ).ProcessSupervisorCommand._wait_for_child_until_deadline
    )

    def __init__(self, timeout_seconds, lead_seconds):
        self.config = type("Config", (), {
            "timeout_seconds": timeout_seconds,
            "stack_dump_lead_seconds": lead_seconds,
        })()


class _DiagnosticProbe:
    """監視ループから見える面だけを持つ診断 stub。"""

    def __init__(self, *, work=None):
        self.requested = False
        self.cancelled = 0
        self.deadline = None
        self.finalization_start = None
        self.kill_signal = None
        self._work = work
        self.thread = None
        self.request_monotonic = None

    def note_deadline(self, deadline):
        self.deadline = deadline

    def note_deadline_finalization_start(self, value):
        self.finalization_start = value

    def note_kill_signal(self, name, value):
        self.kill_signal = (name, value)

    def cancel_future_requests(self):
        self.cancelled += 1

    def request_async(self):
        assert self.requested is False, "診断要求は 1 回だけ"
        self.requested = True
        self.request_monotonic = time.monotonic()
        if self._work is not None:
            self.thread = threading.Thread(target=self._work, daemon=True)
            self.thread.start()


def _run_loop(timeout, lead, process, probe):
    """`run()` と同じ順序で deadline を決めてからループへ入る。

    deadline は **呼び出し側が 1 回だけ**決めてループへ渡す（production では
    barrier 解放の直後）。ループは deadline を作り直さない。
    """
    command = _Command(timeout, lead)
    started = time.monotonic()
    deadline = started + timeout
    return_code = command._wait_for_child_until_deadline(process, probe, deadline)
    finished = time.monotonic()
    return {
        "return_code": return_code,
        "deadline": deadline,
        "started": started,
        "finished": finished,
        "offset": finished - deadline,
    }


def test_d1_fast_diagnostic_does_not_delay_the_kill(tmp_path):
    """D1: 診断が lead より短く終わっても kill 開始は deadline + 0.5s 以内。"""
    probe = _DiagnosticProbe(work=lambda: time.sleep(0.05))
    result = _run_loop(0.6, 0.3, _FakeProcess(), probe)
    assert result["return_code"] is None
    assert probe.requested is True
    assert 0.0 <= result["offset"] <= DEADLINE_JITTER_ALLOWANCE_SECONDS


def test_d2_slow_diagnostic_does_not_delay_the_kill():
    """D2: 診断が lead の 3 倍かかっても deadline は延びない。"""
    probe = _DiagnosticProbe(work=lambda: time.sleep(0.9))
    result = _run_loop(0.6, 0.3, _FakeProcess(), probe)
    assert result["return_code"] is None
    assert 0.0 <= result["offset"] <= DEADLINE_JITTER_ALLOWANCE_SECONDS
    assert probe.thread.is_alive() is True  # ループは worker を待っていない


def test_d3_hanging_diagnostic_does_not_block_the_loop():
    """D3: 診断がハングしても kill 開始は deadline + 0.5s 以内。"""
    stop = threading.Event()
    probe = _DiagnosticProbe(work=lambda: stop.wait(30))
    try:
        result = _run_loop(0.6, 0.3, _FakeProcess(), probe)
        assert result["return_code"] is None
        assert 0.0 <= result["offset"] <= DEADLINE_JITTER_ALLOWANCE_SECONDS
        assert probe.thread.is_alive() is True
    finally:
        stop.set()


@pytest.mark.parametrize("failure", [
    RuntimeError("can't start new thread"),
    MemoryError(),
    OSError(11, "Resource temporarily unavailable"),
])
def test_d4_raising_diagnostic_request_does_not_stop_the_deadline(failure):
    """D4: 診断要求そのものが例外でも、deadline 到達まで監視を続ける。

    `threading.Thread.start()` は thread を作れないと `RuntimeError` を投げる。
    それがループを抜けると `run()` の `except Exception` -> `_resume()` へ移り、
    **診断の都合で outcome / exit code が変わってしまう**。診断は
    diagnostic-only なので、ここは握り潰して deadline 監視を続ける。
    """
    class _Raising(_DiagnosticProbe):
        def request_async(self):
            self.requested = True
            raise failure

    probe = _Raising()
    result = _run_loop(0.6, 0.3, _FakeProcess(), probe)
    # deadline に到達し、既存の kill 経路へ渡している。
    assert result["return_code"] is None
    assert probe.requested is True
    assert probe.cancelled >= 1
    assert 0.0 <= result["offset"] <= DEADLINE_JITTER_ALLOWANCE_SECONDS


def test_a_failing_diagnostic_request_is_not_retried_every_slice():
    """失敗した要求をループが毎 slice 作り直さない（監視の仕事を増やさない）。"""
    calls = []

    class _Raising(_DiagnosticProbe):
        def request_async(self):
            calls.append(time.monotonic())
            raise RuntimeError("can't start new thread")

    _run_loop(0.6, 0.5, _FakeProcess(), _Raising())
    assert len(calls) == 1, calls


def test_the_production_diagnostic_never_raises_from_request_async(pair, monkeypatch):
    """実装側の `request_async` は、thread を作れなくても例外を出さない。"""
    def _explode(*args, **kwargs):
        raise RuntimeError("can't start new thread")

    monkeypatch.setattr(threading, "Thread", _explode)
    diagnostic = _diagnostic(pair)
    diagnostic.request_async()          # 例外にならない
    assert diagnostic.requested is True
    assert diagnostic.signal_sent is False
    assert diagnostic.unavailable_reason == "diagnostic_start_failed:RuntimeError"


def test_a_failed_thread_start_is_recorded_without_sending(pair, monkeypatch, sender):
    """`Thread.start()` の失敗も理由として残り、送信は起きない。"""
    class _DeadThread:
        def __init__(self, *args, **kwargs):
            self.daemon = True

        def start(self):
            raise RuntimeError("can't start new thread")

        def is_alive(self):
            return False

    monkeypatch.setattr(threading, "Thread", _DeadThread)
    diagnostic = _diagnostic(pair)
    diagnostic.request_async()
    assert diagnostic.unavailable_reason == "diagnostic_start_failed:RuntimeError"
    assert sender.sent == []


def test_d5_child_exit_during_diagnostic_is_a_normal_resolution():
    """D5: 診断中に child が終了したら正常終了として返す（TIMEOUT にしない）。"""
    probe = _DiagnosticProbe(work=lambda: time.sleep(0.5))
    process = _FakeProcess(exits_after=0.4)
    result = _run_loop(2.0, 1.8, process, probe)
    assert result["return_code"] == 0
    assert probe.cancelled >= 1
    assert probe.finalization_start is None
    assert probe.kill_signal is None


def test_exit_before_the_lead_never_requests_a_diagnostic():
    probe = _DiagnosticProbe()
    process = _FakeProcess(exits_after=0.05)
    result = _run_loop(2.0, 0.3, process, probe)
    assert result["return_code"] == 0
    assert probe.requested is False
    assert probe.cancelled == 1


def test_exit_just_after_the_lead_is_still_a_normal_resolution():
    probe = _DiagnosticProbe()
    process = _FakeProcess(exits_after=0.45)
    result = _run_loop(0.8, 0.5, process, probe)
    assert result["return_code"] == 0
    assert probe.requested is True
    assert probe.cancelled >= 1


def test_the_loop_never_waits_longer_than_one_poll_slice():
    """ループの 1 回の待ちは poll slice 以下（同期 I/O も入れない）。"""
    probe = _DiagnosticProbe()
    process = _FakeProcess()
    _run_loop(0.4, 0.2, process, probe)
    assert process.wait_calls, "wait() が呼ばれていない"
    assert process.max_wait_timeout <= POLL_SLICE_SECONDS + 1e-9


def test_the_loop_never_derives_a_deadline_of_its_own():
    """ループは deadline を受け取るだけで、作りも延ばしもしない。

    `deadline` への代入や `timeout_seconds` の読み出しがループ本体に無いことを
    AST で固定する（あると、診断を足した分だけ起点がずれる余地が残る）。
    """
    import ast
    import inspect
    from scripts.function_tracer_pcode.authority.process.supervisor_command import (
        ProcessSupervisorCommand,
    )

    tree = ast.parse(inspect.getsource(
        ProcessSupervisorCommand._wait_for_child_until_deadline
    ).lstrip())
    assigned = {
        target.id for node in ast.walk(tree) if isinstance(node, ast.Assign)
        for target in node.targets if isinstance(target, ast.Name)
    }
    assert "deadline" not in assigned, assigned
    attributes = {
        node.attr for node in ast.walk(tree) if isinstance(node, ast.Attribute)
    }
    assert "timeout_seconds" not in attributes, sorted(attributes)


def test_the_deadline_origin_is_fixed_before_the_diagnostic_is_built():
    """`run()` は barrier 解放の直後に deadline を固定してから診断を組む。

    診断 object の生成時間が timeout budget の外へ逃げると、診断を入れた分だけ
    child の実効予算が伸びる。順序を source で固定する。
    """
    import re
    from pathlib import Path as _Path

    source = (
        _Path(__file__).resolve().parents[4]
        / "scripts/function_tracer_pcode/authority/process/supervisor_command.py"
    ).read_text(encoding="utf-8")
    body = source[source.index("    def run(self) -> int:"):]
    barrier = body.index('os.write(write_fd, b"1")')
    origin = body.index("deadline = time.monotonic() + float(self.config.timeout_seconds)")
    build = body.index("diagnostic = self._build_stack_dump_diagnostic(")
    wait = body.index("self._wait_for_child_until_deadline(")
    assert barrier < origin < build < wait
    # 起点は 1 回だけ。
    assert len(re.findall(
        r"deadline = time\.monotonic\(\) \+ float\(self\.config\.timeout_seconds\)",
        source,
    )) == 1


def test_the_loop_uses_the_deadline_it_was_given():
    probe = _DiagnosticProbe()
    result = _run_loop(0.5, 0.2, _FakeProcess(), probe)
    assert probe.deadline == pytest.approx(result["deadline"])
    assert result["deadline"] - result["started"] == pytest.approx(0.5, abs=0.05)


def test_diagnostic_presence_does_not_change_the_kill_timing():
    """D1/D2/D10: 診断あり / 無効の両方で kill 開始の遅れが同じ許容内。"""
    with_diagnostic = _run_loop(
        0.6, 0.3, _FakeProcess(), _DiagnosticProbe(work=lambda: time.sleep(0.5))
    )
    disabled = _run_loop(0.6, 0.0, _FakeProcess(), _DiagnosticProbe())
    for result in (with_diagnostic, disabled):
        assert 0.0 <= result["offset"] <= DEADLINE_JITTER_ALLOWANCE_SECONDS


def test_zero_lead_never_requests_the_diagnostic():
    """lead=0 でも構造は同じで、要求だけが起きない。"""
    probe = _DiagnosticProbe()
    result = _run_loop(0.4, 0.0, _FakeProcess(), probe)
    assert result["return_code"] is None
    assert probe.requested is False


# ---------------------------------------------------------------------------
# D11: 既存契約の不変（source レベルの固定）
# ---------------------------------------------------------------------------


SUPERVISOR_SOURCE = Path(
    "scripts/function_tracer_pcode/authority/process/supervisor_command.py"
).resolve()


def _supervisor_source():
    root = Path(__file__).resolve().parents[4]
    return (
        root / "scripts/function_tracer_pcode/authority/process/supervisor_command.py"
    ).read_text(encoding="utf-8")


def test_d11_kill_sequence_and_dispositions_are_unchanged():
    """SIGTERM -> grace -> SIGKILL と disposition 文字列を変えていない。"""
    source = _supervisor_source()
    for fragment in (
        'os.killpg(process.pid, signal.SIGTERM)',
        'process.wait(timeout=self.config.kill_grace_seconds)',
        'os.killpg(process.pid, signal.SIGKILL)',
        '"SIGTERM_AFTER_DEADLINE"',
        '"SIGKILL_AFTER_DEADLINE"',
        'f"EXITED_{process.returncode}_AFTER_SIGTERM"',
        'f"EXITED_{process.returncode}_AFTER_SIGKILL"',
    ):
        assert fragment in source, fragment


def test_d11_diagnostic_signal_never_goes_to_a_process_group():
    """診断 signal は child PID だけ。`killpg` を診断に使っていない。"""
    import ast

    source = (
        Path(__file__).resolve().parents[4]
        / "scripts/function_tracer_pcode/authority/process/stack_dump_diagnostic.py"
    ).read_text(encoding="utf-8")
    # 文字列検査だと docstring の説明に当たるので、呼び出し名を AST で見る。
    attributes = {
        node.attr for node in ast.walk(ast.parse(source))
        if isinstance(node, ast.Attribute)
    }
    names = {
        node.id for node in ast.walk(ast.parse(source)) if isinstance(node, ast.Name)
    }
    assert "killpg" not in attributes and "killpg" not in names
    assert "kill" not in attributes
    assert "pidfd_send_signal" in source


def test_d11_deadline_policy_digest_is_not_derived_from_diagnostic_settings():
    """`deadline_policy_digest` と manifest preimage は診断設定を含まない。"""
    from scripts.function_tracer_pcode.authority.process.supervisor_command import (
        SupervisorCommandConfig,
    )

    base = dict(
        checkpoint_root=Path("cp"), authority_output=Path("out.json"),
        working_directory=Path("."), execution_nonce="nonce",
        result_occurrence_id="occ", source_snapshot_fingerprint="fp",
        stream_id="stream", deadline_policy_digest="digest",
        supervisor_signing_key_id="sup", supervisor_signing_key_file=Path("s.key"),
        worker_signing_key_id="wrk", worker_signing_key_file=Path("w.key"),
        timeout_seconds=10.0, kill_grace_seconds=1.0,
        child_command=("true",),
    )
    without = SupervisorCommandConfig(**base)
    with_diagnostic = SupervisorCommandConfig(
        **base,
        stage_journal_path=Path("pair.stage.jsonl"),
        stack_dump_file=Path("cp/stack-dump.txt"),
        stack_dump_artifact=Path("rt/pair.stack-dump.txt"),
        diagnostic_status_output=Path("rt/pair.stack-dump.status.json"),
        stack_dump_lead_seconds=3.0,
    )
    assert (
        without.manifest_entry_preimage_digest
        == with_diagnostic.manifest_entry_preimage_digest
    )


def test_diagnostic_paths_reject_non_path_arguments():
    from scripts.function_tracer_pcode.authority.process.supervisor_command import (
        SupervisorCommandConfig,
    )

    with pytest.raises(TypeError):
        SupervisorCommandConfig(
            checkpoint_root=Path("cp"), authority_output=Path("out.json"),
            working_directory=Path("."), execution_nonce="nonce",
            result_occurrence_id="occ", source_snapshot_fingerprint="fp",
            stream_id="stream", deadline_policy_digest="digest",
            supervisor_signing_key_id="sup", supervisor_signing_key_file=Path("s.key"),
            worker_signing_key_id="wrk", worker_signing_key_file=Path("w.key"),
            timeout_seconds=10.0, kill_grace_seconds=1.0,
            child_command=("true",),
            stage_journal_path=object(),
        )


def test_the_monitoring_loop_does_not_join_the_diagnostic_worker():
    """ループの本体に join / 同期 I/O が無いことを source で固定する。"""
    import ast
    import inspect
    from scripts.function_tracer_pcode.authority.process.supervisor_command import (
        ProcessSupervisorCommand,
    )

    tree = ast.parse(inspect.getsource(
        ProcessSupervisorCommand._wait_for_child_until_deadline
    ).lstrip())
    called = {
        node.func.attr for node in ast.walk(tree)
        if isinstance(node, ast.Call) and isinstance(node.func, ast.Attribute)
    }
    for forbidden in ("join", "stat", "read", "read_text", "open", "glob", "is_file"):
        assert forbidden not in called, forbidden
    assert {"poll", "wait", "monotonic"} <= called


def test_the_diagnostic_worker_never_touches_the_popen_object():
    """worker の identity 確認が `Popen` に触らない。

    `Popen.poll()` / `Popen.wait()` は `_waitpid_lock` を取って `waitpid` を
    呼ぶので、worker thread から呼ぶと監視ループの終了検出と競合する。
    identity は `/proc/<pid>/stat` の start token だけで確かめる。
    """
    import ast
    import inspect
    from scripts.function_tracer_pcode.authority.process.supervisor_command import (
        ProcessSupervisorCommand,
    )

    tree = ast.parse(
        inspect.getsource(ProcessSupervisorCommand._stack_dump_diagnostic).lstrip()
    )
    lambdas = [node for node in ast.walk(tree) if isinstance(node, ast.Lambda)]
    assert lambdas, "identity verifier の lambda が見つからない"
    called = {
        node.func.attr for node in ast.walk(lambdas[0])
        if isinstance(node, ast.Call) and isinstance(node.func, ast.Attribute)
    }
    assert not (called & {"poll", "wait", "_same_process"}), sorted(called)
    names = {
        node.func.id for node in ast.walk(lambdas[0])
        if isinstance(node, ast.Call) and isinstance(node.func, ast.Name)
    }
    assert "read_process_start_token" in names


# ---------------------------------------------------------------------------
# cancel と送信の競合（sleep に頼らず決定的に再現する）
# ---------------------------------------------------------------------------


def test_cancel_between_the_readiness_check_and_the_send_stops_the_signal(
    pair, monkeypatch,
):
    """worker が pidfd を開いた**あと**に cancel されたら、もう送らない。

    `cancel_future_requests()` は lock を取らない（監視ループを worker の lock
    保持で待たせないため）ので、入口で 1 回見るだけでは
    「確認 -> pidfd_open -> 送信」の間に入った cancel を取りこぼす。
    ここでは `os.pidfd_open` の中で worker を止め、監視側に相当する main thread
    から cancel してから再開させる。sleep には頼らない。
    """
    opened = threading.Event()
    release = threading.Event()
    sent = []

    def _open(pid, flags):
        opened.set()
        assert release.wait(5.0), "テストが worker を再開させられなかった"
        return os.open(os.devnull, os.O_RDONLY)

    monkeypatch.setattr(os, "pidfd_open", _open, raising=False)
    monkeypatch.setattr(
        signal, "pidfd_send_signal", lambda fd, number: sent.append(number),
        raising=False,
    )

    diagnostic = _diagnostic(pair)
    diagnostic.request_async()
    assert opened.wait(5.0), "worker が pidfd_open まで到達しなかった"
    # ここが「監視ループが child の終了 / deadline 到達を見た」瞬間に相当する。
    diagnostic.cancel_future_requests()
    release.set()
    _join_worker(diagnostic)

    assert sent == [], "cancel 後に SIGUSR1 を送っている"
    assert diagnostic.signal_sent is False
    assert diagnostic.unavailable_reason == "cancelled"
    assert diagnostic.dump_observed is False


def test_cancel_before_the_worker_reads_the_journal_stops_the_signal(pair, sender):
    """cancel が先に立っていれば worker は送らない（入口の関門）。"""
    diagnostic = _diagnostic(pair)
    diagnostic.cancel_future_requests()
    # cancel 済みでも worker を直接動かして、送信側の関門だけを見る。
    diagnostic._diagnose()
    assert diagnostic.signal_sent is False
    assert sender.sent == []
    assert diagnostic.unavailable_reason == "cancelled"


def test_the_send_gate_checks_cancel_last(pair):
    """`_send_signal` の最後の判断が cancel であることを AST で固定する。"""
    import ast
    import inspect

    tree = ast.parse(inspect.getsource(StackDumpDiagnostic._send_signal).lstrip())
    sends = [
        node for node in ast.walk(tree)
        if isinstance(node, ast.Call) and isinstance(node.func, ast.Name)
        and node.func.id == "pidfd_send"
    ]
    assert len(sends) == 1
    send_line = sends[0].lineno
    cancel_checks = [
        node.lineno for node in ast.walk(tree)
        if isinstance(node, ast.Call) and isinstance(node.func, ast.Attribute)
        and node.func.attr == "is_set"
    ]
    assert cancel_checks, "cancel の確認が無い"
    # 送信の直前にも cancel を見ている。
    assert max(cancel_checks) < send_line
    assert send_line - max(cancel_checks) < 12, (cancel_checks, send_line)


# ---------------------------------------------------------------------------
# kill 開始時刻は「termination path へ入った時刻」ではなく実 signal
# ---------------------------------------------------------------------------


def test_kill_start_offset_tracks_the_actual_signal_not_the_path_entry(pair):
    """`kill_start_offset_seconds` は実際に SIGTERM を送れた時刻に対応する。"""
    diagnostic = _diagnostic(pair)
    deadline = 1000.0
    diagnostic.note_deadline(deadline)
    diagnostic.note_deadline_finalization_start(deadline + 0.01)
    diagnostic.note_kill_signal("SIGTERM", deadline + 0.30)
    payload = diagnostic.status_payload()
    assert payload["deadline_finalization_offset_seconds"] == pytest.approx(0.01)
    assert payload["kill_start_offset_seconds"] == pytest.approx(0.30)
    assert payload["kill_signal"] == "SIGTERM"


def test_no_kill_start_is_claimed_when_no_signal_was_sent(pair):
    """deadline 後・signal 前に child が終了した pair は kill を名乗らない。"""
    diagnostic = _diagnostic(pair)
    diagnostic.note_deadline(1000.0)
    diagnostic.note_deadline_finalization_start(1000.02)
    payload = diagnostic.status_payload()
    assert payload["deadline_finalization_offset_seconds"] == pytest.approx(0.02)
    assert payload["kill_start_offset_seconds"] is None
    assert payload["kill_signal"] is None
    assert payload["kill_signal_monotonic"] is None


def test_the_first_signal_hook_fires_only_after_a_delivered_sigterm():
    """`_terminate_exact_process_group` の hook は送れたときだけ呼ばれる。

    終了確認・identity 検証で signal を送らずに戻る枝では呼ばれないことを、
    source の位置関係で固定する（hook が早すぎると、送っていない kill を
    「開始した」と記録してしまう）。
    """
    import ast
    import inspect
    from scripts.function_tracer_pcode.authority.process.supervisor_command import (
        ProcessSupervisorCommand,
    )

    source = inspect.getsource(
        ProcessSupervisorCommand._terminate_exact_process_group
    ).lstrip()
    tree = ast.parse(source)
    killpg_lines = [
        node.lineno for node in ast.walk(tree)
        if isinstance(node, ast.Call) and isinstance(node.func, ast.Attribute)
        and node.func.attr == "killpg"
    ]
    hook_lines = [
        node.lineno for node in ast.walk(tree)
        if isinstance(node, ast.Call) and isinstance(node.func, ast.Name)
        and node.func.id == "on_first_signal"
    ]
    assert len(killpg_lines) == 2, killpg_lines      # SIGTERM と SIGKILL
    assert len(hook_lines) == 1, hook_lines
    # hook は最初の killpg より後（= 送れたあと）、grace 待ちより前。
    assert hook_lines[0] > min(killpg_lines)
    assert hook_lines[0] < max(killpg_lines)
