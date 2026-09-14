# -*- coding: utf-8 -*-
"""Issue #124 PR-124-C: supervisor recovery で混ざった journal の fail-closed 読み。

PR-124-B の handoff（2026-09-14 の Issue #124 comment）が読み手側に残した契約:

* current child の PID / start_token に**一意に**結び付く execution segment だけ使う
* 混在の検出条件は seq 巻き戻り / `pair_journal_opened` 複数 / identity 不一致
* 一意に選べなければ stage も dump も推測せず `unavailable` にする
* 前の execution の `handler_registered` を current の readiness に使わない
* 前の execution の stage を current の hotspot に混ぜない（合算しない）
"""

from __future__ import annotations

import json
import os
import signal
from pathlib import Path

import pytest

from scripts.function_tracer_pcode.core.stage_journal import STAGE_JOURNAL_SCHEMA
from scripts.function_tracer_pcode.core.stage_journal_reader import (
    UNAVAILABLE_AMBIGUOUS,
    UNAVAILABLE_EMPTY,
    UNAVAILABLE_IDENTITY_CHANGED,
    UNAVAILABLE_NOT_REGULAR_FILE,
    UNAVAILABLE_NO_HANDLER,
    UNAVAILABLE_NO_PATH,
    read_stage_journal,
    segment_stages,
    select_current_segment,
)

FIRST_PID = 1001
SECOND_PID = 2002
FIRST_TOKEN = "linux-proc-starttime-111"
SECOND_TOKEN = "linux-proc-starttime-222"


def _row(seq, event, *, stage=None, pid, payload=None, seconds=None, monotonic=None):
    return json.dumps({
        "schema": STAGE_JOURNAL_SCHEMA,
        "seq": seq,
        "event": event,
        "stage": stage,
        "seconds": seconds,
        "t_monotonic": float(seq if monotonic is None else monotonic),
        "t_epoch": 1000.0 + seq,
        "pid": pid,
        "payload": payload or {},
    }, sort_keys=True)


def _handler(pid, token, *, dump="/cp/stack-dump.txt"):
    return {
        "pid": pid,
        "start_token": token,
        "dump_path_tmp": dump,
        "dump_artifact_path": "/run/.runtime-metrics/pair.stack-dump.txt",
        "signal_number": int(signal.SIGUSR1),
        "all_threads": True,
        "chain": False,
        "readiness_basis": "faulthandler_register_returned",
    }


def _execution(pid, token, *, stages, start_seq=1):
    """1 execution 分の行（開始 note -> handler -> stage 群）。"""
    seq = start_seq
    rows = [_row(seq, "note", pid=pid, payload={"note": "pair_journal_opened"})]
    seq += 1
    rows.append(_row(
        seq, "handler_registered", stage="stack_dump_handler",
        pid=pid, payload=_handler(pid, token),
    ))
    for stage, seconds in stages:
        seq += 1
        rows.append(_row(
            seq, "stage_start", stage=stage, pid=pid,
            payload={"kind": "region", "path": [stage]},
        ))
        if seconds is not None:
            seq += 1
            rows.append(_row(
                seq, "stage_end", stage=stage, pid=pid, seconds=seconds,
                payload={"kind": "region", "path": [stage]},
            ))
    return rows, seq


def _write(path, *executions):
    lines = []
    for rows, _ in executions:
        lines.extend(rows)
    Path(path).write_text("\n".join(lines) + "\n", encoding="utf-8")


# ---------------------------------------------------------------------------
# 単一 execution
# ---------------------------------------------------------------------------


def test_single_execution_is_selected_by_identity(tmp_path):
    journal = tmp_path / "pair.stage.jsonl"
    _write(journal, _execution(FIRST_PID, FIRST_TOKEN, stages=[("check", 1.0)]))
    read = read_stage_journal(journal)
    assert read.multi_execution is False
    segment, reason = select_current_segment(
        read, pid=FIRST_PID, start_token=FIRST_TOKEN
    )
    assert reason is None
    assert segment is not None
    assert segment.handler_pid == FIRST_PID
    assert segment.start_token == FIRST_TOKEN


def test_single_execution_is_selected_without_identity_for_offline_reading(tmp_path):
    """run 終了後は launch receipt が無い。混在の兆候が無ければ 1 本を使う。"""
    journal = tmp_path / "pair.stage.jsonl"
    _write(journal, _execution(FIRST_PID, FIRST_TOKEN, stages=[("check", 1.0)]))
    segment, reason = select_current_segment(read_stage_journal(journal))
    assert reason is None and segment is not None


# ---------------------------------------------------------------------------
# 混在（recovery が child を再起動した journal）
# ---------------------------------------------------------------------------


def _mixed(tmp_path, *, second_pid=SECOND_PID, second_token=SECOND_TOKEN):
    journal = tmp_path / "pair.stage.jsonl"
    first, _ = _execution(
        FIRST_PID, FIRST_TOKEN,
        stages=[("decompile", 3.0), ("check", 120.0)],
    )
    second, _ = _execution(
        second_pid, second_token, stages=[("decompile", 2.0), ("check", None)],
    )
    Path(journal).write_text("\n".join(first + second) + "\n", encoding="utf-8")
    return journal


def test_mixed_journal_is_detected_by_all_three_conditions(tmp_path):
    read = read_stage_journal(_mixed(tmp_path))
    assert read.multi_execution is True
    assert len(read.segments) == 2
    assert read.seq_rollbacks == 1
    assert read.opened_notes == 2


def test_current_execution_segment_is_selected_uniquely(tmp_path):
    """current child の identity が分かれば、混在していても一意に選べる。"""
    read = read_stage_journal(_mixed(tmp_path))
    segment, reason = select_current_segment(
        read, pid=SECOND_PID, start_token=SECOND_TOKEN
    )
    assert reason is None
    assert segment is not None
    assert segment.handler_pid == SECOND_PID
    stages = segment_stages(segment)
    # 前 execution の `check` 120s を混ぜない。current の最長は decompile 2.0s。
    assert stages.last_completed_stage == "decompile"
    assert stages.longest_completed_seconds == pytest.approx(2.0)
    assert stages.in_progress_stage == "check"


def test_previous_execution_handler_row_is_never_used_for_the_current_child(tmp_path):
    """前 execution の `handler_registered` を current の readiness にしない。"""
    read = read_stage_journal(_mixed(tmp_path))
    segment, reason = select_current_segment(
        read, pid=FIRST_PID, start_token=FIRST_TOKEN
    )
    # 1 本目は selectable だが、それは「current が 1 本目のとき」だけ。
    assert reason is None and segment.handler_pid == FIRST_PID
    # current が 3 つ目のプロセスなら、どちらの行も使わない。
    segment, reason = select_current_segment(
        read, pid=3003, start_token="linux-proc-starttime-333"
    )
    assert segment is None
    assert reason == UNAVAILABLE_IDENTITY_CHANGED


def test_ambiguous_mixed_journal_is_unavailable_without_identity(tmp_path):
    """identity が無い（run 終了後）状態で混在していれば unavailable。"""
    segment, reason = select_current_segment(read_stage_journal(_mixed(tmp_path)))
    assert segment is None
    assert reason == UNAVAILABLE_AMBIGUOUS


def test_two_segments_with_the_same_identity_are_ambiguous(tmp_path):
    """同じ pid / start_token の segment が 2 本なら一意に選べない。"""
    journal = _mixed(tmp_path, second_pid=FIRST_PID, second_token=FIRST_TOKEN)
    segment, reason = select_current_segment(
        read_stage_journal(journal), pid=FIRST_PID, start_token=FIRST_TOKEN
    )
    assert segment is None
    assert reason == UNAVAILABLE_AMBIGUOUS


def test_seq_rollback_alone_splits_executions(tmp_path):
    """開始 note が無くても seq の巻き戻りで segment を切る。"""
    journal = tmp_path / "pair.stage.jsonl"
    rows = [
        _row(1, "stage_start", stage="check", pid=FIRST_PID),
        _row(2, "stage_end", stage="check", pid=FIRST_PID, seconds=1.0),
        _row(1, "stage_start", stage="check", pid=SECOND_PID),
    ]
    Path(journal).write_text("\n".join(rows) + "\n", encoding="utf-8")
    read = read_stage_journal(journal)
    assert read.seq_rollbacks == 1
    assert len(read.segments) == 2
    assert read.multi_execution is True
    segment, reason = select_current_segment(read)
    assert segment is None and reason == UNAVAILABLE_AMBIGUOUS


# ---------------------------------------------------------------------------
# 壊れた journal
# ---------------------------------------------------------------------------


def test_partial_final_line_is_counted_separately_from_malformed(tmp_path):
    journal = tmp_path / "pair.stage.jsonl"
    rows, _ = _execution(FIRST_PID, FIRST_TOKEN, stages=[("check", 1.0)])
    text = "\n".join(rows) + "\n" + '{"schema": "pair-stage-journal-v1", "seq": 9, "eve'
    Path(journal).write_text(text, encoding="utf-8")
    read = read_stage_journal(journal)
    assert read.partial_final_line is True
    assert read.malformed_lines == 0
    segment, reason = select_current_segment(
        read, pid=FIRST_PID, start_token=FIRST_TOKEN
    )
    assert reason is None and segment is not None


def test_malformed_rows_are_counted_and_skipped(tmp_path):
    journal = tmp_path / "pair.stage.jsonl"
    rows, _ = _execution(FIRST_PID, FIRST_TOKEN, stages=[("check", 1.0)])
    rows.insert(2, "{not json}")
    rows.insert(3, json.dumps({"schema": "other-schema", "seq": 1, "event": "x"}))
    Path(journal).write_text("\n".join(rows) + "\n", encoding="utf-8")
    read = read_stage_journal(journal)
    assert read.malformed_lines == 2
    segment, reason = select_current_segment(
        read, pid=FIRST_PID, start_token=FIRST_TOKEN
    )
    assert reason is None and segment is not None


def test_missing_and_non_regular_journals_are_unavailable(tmp_path):
    assert read_stage_journal(None).unavailable_reason == UNAVAILABLE_NO_PATH
    assert read_stage_journal(
        tmp_path / "absent.jsonl"
    ).unavailable_reason == UNAVAILABLE_NOT_REGULAR_FILE
    fifo = tmp_path / "fifo.jsonl"
    os.mkfifo(fifo)
    assert read_stage_journal(fifo).unavailable_reason == UNAVAILABLE_NOT_REGULAR_FILE
    empty = tmp_path / "empty.jsonl"
    empty.write_text("", encoding="utf-8")
    assert read_stage_journal(empty).unavailable_reason == UNAVAILABLE_EMPTY


def test_journal_without_any_handler_row_reports_handler_not_registered(tmp_path):
    journal = tmp_path / "pair.stage.jsonl"
    Path(journal).write_text("\n".join([
        _row(1, "note", pid=FIRST_PID, payload={"note": "pair_journal_opened"}),
        _row(2, "stage_start", stage="check", pid=FIRST_PID),
    ]) + "\n", encoding="utf-8")
    segment, reason = select_current_segment(
        read_stage_journal(journal), pid=FIRST_PID, start_token=FIRST_TOKEN
    )
    assert segment is None
    assert reason == UNAVAILABLE_NO_HANDLER


def test_read_limit_marks_truncation_without_raising(tmp_path):
    journal = tmp_path / "pair.stage.jsonl"
    rows, _ = _execution(FIRST_PID, FIRST_TOKEN, stages=[("check", 1.0)])
    Path(journal).write_text("\n".join(rows) + "\n", encoding="utf-8")
    read = read_stage_journal(journal, max_bytes=80)
    assert read.truncated is True


# ---------------------------------------------------------------------------
# stage の取り出し
# ---------------------------------------------------------------------------


def test_reentered_region_pairs_by_path_not_only_by_name(tmp_path):
    journal = tmp_path / "pair.stage.jsonl"
    rows = [
        _row(1, "note", pid=FIRST_PID, payload={"note": "pair_journal_opened"}),
        _row(2, "stage_start", stage="check", pid=FIRST_PID,
             payload={"kind": "region", "path": ["check"]}),
        _row(3, "stage_start", stage="obligation_build", pid=FIRST_PID,
             payload={"kind": "region", "path": ["check", "obligation_build"]}),
        _row(4, "stage_end", stage="obligation_build", pid=FIRST_PID, seconds=0.5,
             payload={"kind": "region", "path": ["check", "obligation_build"]}),
        _row(5, "stage_start", stage="solver", pid=FIRST_PID,
             payload={"kind": "region", "path": ["check", "solver"]}),
    ]
    Path(journal).write_text("\n".join(rows) + "\n", encoding="utf-8")
    segment, reason = select_current_segment(read_stage_journal(journal))
    assert reason is None
    stages = segment_stages(segment)
    assert stages.last_completed_stage == "obligation_build"
    assert stages.in_progress_stage == "solver"
    assert stages.in_progress_path == ("check", "solver")
    assert stages.started == 3 and stages.completed == 1


def test_longest_completed_stage_is_reported_next_to_the_last_one(tmp_path):
    """kill 後の teardown が最後になっても、時間の所在は別 column で分かる。"""
    journal = tmp_path / "pair.stage.jsonl"
    rows = [
        _row(1, "note", pid=FIRST_PID, payload={"note": "pair_journal_opened"}),
        _row(2, "stage_start", stage="analysis_regions", pid=FIRST_PID),
        _row(3, "stage_end", stage="analysis_regions", pid=FIRST_PID, seconds=214.9),
        _row(4, "stage_start", stage="close_programs", pid=FIRST_PID),
        _row(5, "stage_end", stage="close_programs", pid=FIRST_PID, seconds=0.00002),
    ]
    Path(journal).write_text("\n".join(rows) + "\n", encoding="utf-8")
    segment, _ = select_current_segment(read_stage_journal(journal))
    stages = segment_stages(segment)
    assert stages.last_completed_stage == "close_programs"
    assert stages.longest_completed_stage == "analysis_regions"
    assert stages.longest_completed_seconds == pytest.approx(214.9)


# ---------------------------------------------------------------------------
# 診断 worker が混在 journal をどう扱うか
# ---------------------------------------------------------------------------


def _diagnostic_for(journal, tmp_path, *, pid, token, sender_calls):
    from scripts.function_tracer_pcode.authority.process.stack_dump_diagnostic import (
        StackDumpDiagnostic,
        StackDumpDiagnosticConfig,
    )

    dump_tmp = tmp_path / "cp" / "stack-dump.txt"
    dump_tmp.parent.mkdir(exist_ok=True)
    dump_tmp.write_bytes(b"")
    config = StackDumpDiagnosticConfig(
        journal_path=str(journal),
        dump_path_tmp="/cp/stack-dump.txt",
        dump_artifact_path="/run/.runtime-metrics/pair.stack-dump.txt",
        status_output_path=str(tmp_path / "status.json"),
        lead_seconds=1.0,
        observe_seconds=0.01,
    )
    return StackDumpDiagnostic(
        config, child_pid=pid, start_token=token,
        timeout_seconds=10.0, identity_verifier=lambda: True,
    )


@pytest.fixture()
def recording_sender(monkeypatch):
    calls = []

    def _open(pid, flags):
        calls.append(pid)
        return os.open(os.devnull, os.O_RDONLY)

    monkeypatch.setattr(os, "pidfd_open", _open, raising=False)
    monkeypatch.setattr(
        signal, "pidfd_send_signal", lambda fd, number: calls.append(number),
        raising=False,
    )
    return calls


def _run(diagnostic):
    diagnostic.request_async()
    thread = diagnostic._thread
    if thread is not None:
        thread.join(5.0)
        assert not thread.is_alive()


def test_worker_sends_only_for_the_current_execution_segment(tmp_path, recording_sender):
    """混在していても current の segment が一意なら送る。"""
    journal = _mixed(tmp_path)
    diagnostic = _diagnostic_for(
        journal, tmp_path, pid=SECOND_PID, token=SECOND_TOKEN,
        sender_calls=recording_sender,
    )
    _run(diagnostic)
    assert diagnostic.signal_sent is True
    assert recording_sender[0] == SECOND_PID
    assert diagnostic.journal_state["multi_execution"] is True


def test_worker_refuses_to_send_when_the_current_segment_is_ambiguous(
    tmp_path, recording_sender,
):
    """同じ identity の segment が 2 本 = 一意に選べない -> 送らない。"""
    journal = _mixed(tmp_path, second_pid=FIRST_PID, second_token=FIRST_TOKEN)
    diagnostic = _diagnostic_for(
        journal, tmp_path, pid=FIRST_PID, token=FIRST_TOKEN,
        sender_calls=recording_sender,
    )
    _run(diagnostic)
    assert diagnostic.signal_sent is False
    assert recording_sender == []
    assert diagnostic.unavailable_reason == UNAVAILABLE_AMBIGUOUS
    assert diagnostic.handler_registered is False


def test_worker_does_not_reuse_a_previous_execution_handler_row(
    tmp_path, recording_sender,
):
    """current child が 3 つ目なら、前の 2 本の readiness を使わない。"""
    journal = _mixed(tmp_path)
    diagnostic = _diagnostic_for(
        journal, tmp_path, pid=3003, token="linux-proc-starttime-333",
        sender_calls=recording_sender,
    )
    _run(diagnostic)
    assert diagnostic.signal_sent is False
    assert recording_sender == []
    assert diagnostic.unavailable_reason == UNAVAILABLE_IDENTITY_CHANGED


# ---------------------------------------------------------------------------
# stack dump を撮った瞬間で切る（teardown で region が閉じる前）
# ---------------------------------------------------------------------------


def _teardown_journal(tmp_path):
    """SIGTERM を受けたあと後始末まで走った pair と同じ形の journal。"""
    journal = tmp_path / "pair.stage.jsonl"
    rows = [
        _row(1, "note", pid=FIRST_PID, payload={"note": "pair_journal_opened"},
             monotonic=0.0),
        _row(2, "handler_registered", stage="stack_dump_handler", pid=FIRST_PID,
             payload=_handler(FIRST_PID, FIRST_TOKEN), monotonic=0.1),
        _row(3, "stage_start", stage="analysis_regions", pid=FIRST_PID,
             payload={"kind": "region", "path": ["analysis_regions"]}, monotonic=1.0),
        _row(4, "stage_start", stage="function1", pid=FIRST_PID,
             payload={"kind": "region", "path": ["analysis_regions", "function1"]},
             monotonic=1.1),
        _row(5, "stage_end", stage="decompile", pid=FIRST_PID, seconds=0.4,
             payload={"kind": "region",
                      "path": ["analysis_regions", "function1", "decompile"]},
             monotonic=2.0),
        # ここまでが dump を撮った瞬間（t_epoch 1005）。以降は kill 後の後始末。
        _row(6, "stage_end", stage="function1", pid=FIRST_PID, seconds=200.0,
             payload={"kind": "region", "path": ["analysis_regions", "function1"]},
             monotonic=9.0),
        _row(7, "stage_end", stage="analysis_regions", pid=FIRST_PID, seconds=200.1,
             payload={"kind": "region", "path": ["analysis_regions"]}, monotonic=9.1),
        _row(8, "stage_start", stage="close_programs", pid=FIRST_PID, monotonic=9.2),
        _row(9, "stage_end", stage="close_programs", pid=FIRST_PID, seconds=0.00002,
             monotonic=9.3),
    ]
    Path(journal).write_text("\n".join(rows) + "\n", encoding="utf-8")
    return journal


def test_as_of_epoch_keeps_the_region_that_was_open_at_the_dump(tmp_path):
    """journal の末尾では閉じている region が、dump の瞬間では開いている。"""
    segment, _ = select_current_segment(read_stage_journal(_teardown_journal(tmp_path)))
    at_end = segment_stages(segment)
    assert at_end.in_progress_stage is None
    assert at_end.last_completed_stage == "close_programs"
    # seq 5 の t_epoch = 1005。そこで切ると function1 が開いたまま。
    at_dump = segment_stages(segment, as_of_epoch=1005.0)
    assert at_dump.in_progress_stage == "function1"
    assert at_dump.in_progress_path == ("analysis_regions", "function1")
    assert at_dump.last_completed_stage == "decompile"


def test_as_of_epoch_before_anything_started_reports_no_stage(tmp_path):
    segment, _ = select_current_segment(read_stage_journal(_teardown_journal(tmp_path)))
    early = segment_stages(segment, as_of_epoch=1000.5)
    assert early.in_progress_stage is None
    assert early.last_completed_stage is None
    assert early.started == 0
