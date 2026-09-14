# -*- coding: utf-8 -*-
"""Issue #124 PR-124-C: hotspot 集計・artifact 永続性・health summary（D12 / D14）。

固定している契約:

* stack dump は **全 thread** の block から候補 frame を取る（`Current thread` だけ
  に限定しない）。待機 frame には `waiting` 印を付けるが root cause と断定しない。
* checkpoint の cleanup 後でも、run dir に残る file だけで同じ表を再生成できる。
* 件数はどの次元も TIMEOUT pair 数と総和が一致する。観測できなかった pair は
  `(unknown)` に入り、0 件へ潰されない。
* `run_health_summary` の既存 section は壊さず、節が無い run では 1 行も足さない。
"""

from __future__ import annotations

import json
import shutil
import signal
from pathlib import Path

import pytest

from scripts.function_tracer_pcode.authority.process.stack_dump_diagnostic import (
    STACK_DUMP_STATUS_SCHEMA,
)
from scripts.function_tracer_pcode.core.stage_journal import STAGE_JOURNAL_SCHEMA
from scripts.function_tracer_pcode.reporting import timeout_hotspot_summary as hotspot
from scripts.function_tracer_pcode.reporting.result_summary import (
    TIMEOUT_DIAGNOSTICS_KEY,
    format_run_health_summary,
    timeout_diagnostics_from_health,
)

CHILD_PID = 7777
START_TOKEN = "linux-proc-starttime-777"
OCCURRENCE = "production-pilot-issue124c"

DUMP_TEXT = """\
Thread 0x00007f1111111111 (most recent call first):
  File "/workspace/scripts/function_tracer_pcode/smt/parallel.py", line 140 in run_single
  File "/usr/lib/python3.10/concurrent/futures/thread.py", line 58 in run

Thread 0x00007f2222222222 (most recent call first):
  File "/usr/lib/python3.10/threading.py", line 320 in wait
  File "/usr/lib/python3.10/queue.py", line 171 in get

Current thread 0x00007f3333333333 (most recent call first):
  File "/workspace/scripts/function_tracer_pcode/proof/obligations/runtime.py", line 514 in schedule
  File "/workspace/scripts/function_tracer_pcode/checker/checker.py", line 700 in check
"""


# ---------------------------------------------------------------------------
# stack dump の解析（D14）
# ---------------------------------------------------------------------------


def test_candidate_frames_come_from_every_thread_block(tmp_path):
    dump = tmp_path / "pair.stack-dump.txt"
    dump.write_text(DUMP_TEXT, encoding="utf-8")
    read = hotspot.read_stack_dump(dump)
    assert read.present is True
    assert read.thread_blocks == 3
    assert read.dump_sections == 1
    functions = [frame.function for frame in read.candidate_frames]
    # worker thread の frame も `Current thread` の frame も両方ある。
    assert functions == ["run_single", "wait", "schedule"]
    assert [frame.current_thread for frame in read.candidate_frames] == [
        False, False, True,
    ]


def test_waiting_frames_are_marked_but_not_called_a_root_cause(tmp_path):
    dump = tmp_path / "pair.stack-dump.txt"
    dump.write_text(DUMP_TEXT, encoding="utf-8")
    read = hotspot.read_stack_dump(dump)
    waiting = {frame.function: frame.waiting for frame in read.candidate_frames}
    assert waiting == {"run_single": False, "wait": True, "schedule": False}
    # 出力には「候補であって原因ではない」注記が必ず付く。
    report = hotspot.TimeoutHotspotReport(roots=(), rows=(), total_pairs=0)
    note = report.health_section()["candidate_frames_note"]
    assert "not a root cause" in note


def test_missing_and_empty_dumps_are_distinguished(tmp_path):
    assert hotspot.read_stack_dump(None).unavailable_reason == (
        "stack_dump_not_configured"
    )
    assert hotspot.read_stack_dump(tmp_path / "absent.txt").unavailable_reason == (
        "stack_dump_missing"
    )
    empty = tmp_path / "empty.txt"
    empty.write_text("", encoding="utf-8")
    assert hotspot.read_stack_dump(empty).unavailable_reason == "stack_dump_empty"
    garbage = tmp_path / "garbage.txt"
    garbage.write_text("not a dump\n", encoding="utf-8")
    assert hotspot.read_stack_dump(garbage).unavailable_reason == (
        "stack_dump_has_no_thread_block"
    )


def test_repeated_dumps_keep_only_the_last_section(tmp_path):
    dump = tmp_path / "pair.stack-dump.txt"
    dump.write_text(DUMP_TEXT + "\n" + DUMP_TEXT, encoding="utf-8")
    read = hotspot.read_stack_dump(dump)
    assert read.dump_sections == 2
    assert read.thread_blocks == 3


# ---------------------------------------------------------------------------
# run tree の組み立て
# ---------------------------------------------------------------------------


def _row(seq, event, *, stage=None, payload=None, seconds=None):
    return json.dumps({
        "schema": STAGE_JOURNAL_SCHEMA, "seq": seq, "event": event, "stage": stage,
        "seconds": seconds, "t_monotonic": float(seq), "t_epoch": 1000.0 + seq,
        "pid": CHILD_PID, "payload": payload or {},
    }, sort_keys=True)


def _pair_status(outcome="TIMEOUT"):
    return {
        "canonical_outcome": outcome,
        "supervisor_status": "TIMEOUT" if outcome == "TIMEOUT" else "RESOLVED",
        "supervisor_authority_kind": (
            "DurableTimeoutFinalizationBundle" if outcome == "TIMEOUT"
            else "SupervisorCanonicalResultResolvedReceipt"
        ),
        "child_exit_disposition": "EXITED_143_AFTER_SIGTERM",
        "child_returncode": 143 if outcome == "TIMEOUT" else 2,
        "child_returncode_observation_kind": "LIVE_PROCESS_WAIT",
        "classification_valid": True,
        "result_occurrence_id": OCCURRENCE,
        "stream_id": f"stream-{OCCURRENCE}",
        "source_snapshot_fingerprint": "f" * 64,
        "pair_execution_target": {
            "sample_identity": "REVE/sample/Eq/new",
            "function_name": "f",
            "left_binary_id": "B1",
            "right_binary_id": "B2",
        },
    }


def _status_sidecar(**overrides):
    payload = {
        "schema": STACK_DUMP_STATUS_SCHEMA,
        "child_pid": CHILD_PID,
        "child_start_token": START_TOKEN,
        "enabled": True,
        "requested": True,
        "handler_registered": True,
        "signal": "SIGUSR1",
        "signal_number": int(signal.SIGUSR1),
        "signal_sent": True,
        "dump_observed": True,
        "sent_but_unobserved": False,
        "unavailable_reason": None,
        "artifact_status": "copied",
        "artifact_bytes": len(DUMP_TEXT),
        "journal": {},
        "journal_current_segment_selected": True,
        "kill_start_offset_seconds": 0.11,
        "child_timeout_evidence": None,
    }
    payload.update(overrides)
    return payload


def _build_run(tmp_path, *, outcome="TIMEOUT", with_sidecar=True, with_dump=True):
    root = tmp_path / "run" / "eq"
    pair_dir = root / "REVE" / "sample" / "Eq" / "new" / "f"
    pair_dir.mkdir(parents=True)
    metrics = pair_dir / ".runtime-metrics"
    metrics.mkdir()
    stem = "f_B1_B2"
    (pair_dir / f"{stem}.pair-status.json").write_text(
        json.dumps(_pair_status(outcome)), encoding="utf-8"
    )
    (pair_dir / f"{stem}.log").write_text("no result json here\n", encoding="utf-8")
    (pair_dir / f"{stem}.stage.jsonl").write_text("\n".join([
        _row(1, "note", payload={"note": "pair_journal_opened"}),
        _row(2, "handler_registered", stage="stack_dump_handler", payload={
            "pid": CHILD_PID, "start_token": START_TOKEN,
            "signal_number": int(signal.SIGUSR1), "all_threads": True,
            "readiness_basis": "faulthandler_register_returned",
        }),
        _row(3, "stage_start", stage="check", payload={
            "kind": "region", "path": ["check"]}),
        _row(4, "stage_start", stage="obligation_build", payload={
            "kind": "region", "path": ["check", "obligation_build"]}),
        _row(5, "stage_end", stage="obligation_build", seconds=12.5, payload={
            "kind": "region", "path": ["check", "obligation_build"]}),
        _row(6, "stage_start", stage="solver", payload={
            "kind": "region", "path": ["check", "solver"]}),
    ]) + "\n", encoding="utf-8")
    if with_dump:
        (metrics / f"{stem}.stack-dump.txt").write_text(DUMP_TEXT, encoding="utf-8")
    if with_sidecar:
        (metrics / f"{stem}.stack-dump.status.json").write_text(
            json.dumps(_status_sidecar()), encoding="utf-8"
        )
    checkpoint = tmp_path / "checkpoint" / "nonce"
    checkpoint.mkdir(parents=True)
    (checkpoint / "stack-dump.txt").write_text(DUMP_TEXT, encoding="utf-8")
    (checkpoint / "state.json").write_text("{}", encoding="utf-8")
    return root, checkpoint


# ---------------------------------------------------------------------------
# 集計（D12）
# ---------------------------------------------------------------------------


def test_report_counts_every_dimension_for_each_timeout_pair(tmp_path):
    root, _ = _build_run(tmp_path)
    report = hotspot.build_timeout_hotspot_report([root])
    section = report.health_section()
    assert section["pairs"] == 1
    assert section["total_pairs"] == 1
    for dimension in (
        "timeout_kind", "handler_registered", "signal_sent", "dump_observed",
        "sent_but_unobserved", "unavailable_reason", "artifact_status",
        "last_completed_stage", "in_progress_stage", "longest_completed_stage",
    ):
        assert sum(section[dimension].values()) == section["pairs"], dimension
    assert section["timeout_kind"] == {hotspot.KIND_PROCESS_WALL_CLOCK: 1}
    assert section["handler_registered"] == {"true": 1}
    assert section["signal_sent"] == {"true": 1}
    assert section["dump_observed"] == {"true": 1}
    assert section["artifact_status"] == {"copied": 1}
    assert section["last_completed_stage"] == {"obligation_build": 1}
    assert section["in_progress_stage"] == {"solver": 1}
    # hotspot 行は候補 frame ごとに 1 本（全 thread ぶん）。
    assert sum(section["timeout_hotspots"].values()) == 3


def test_non_timeout_pairs_are_not_rows_but_are_counted_in_the_total(tmp_path):
    root, _ = _build_run(tmp_path, outcome="UNKNOWN")
    report = hotspot.build_timeout_hotspot_report([root])
    assert report.timeout_pairs == 0
    assert report.total_pairs == 1
    section = report.health_section()
    assert section["timeout_kind"] == {}


def test_a_run_without_the_sidecar_reads_as_unknown_not_zero(tmp_path):
    """PR-124-C 以前の run。`false` ではなく `(unknown)` にする。"""
    root, _ = _build_run(tmp_path, with_sidecar=False, with_dump=False)
    section = hotspot.build_timeout_hotspot_report([root]).health_section()
    assert section["handler_registered"] == {"(unknown)": 1}
    assert section["signal_sent"] == {"(unknown)": 1}
    assert section["dump_observed"] == {"(unknown)": 1}
    assert section["sent_but_unobserved"] == {"(unknown)": 1}
    assert section["unavailable_reason"] == {"(unknown)": 1}
    assert section["artifact_status"] == {"(unknown)": 1}
    assert section["evidence"]["diagnostic_status_missing"] == 1
    assert section["evidence"]["stack_dump_missing"] == 1


def test_d12_artifact_and_table_survive_checkpoint_cleanup(tmp_path):
    """D12: cleanup で checkpoint が消えても run dir の artifact で再集計できる。"""
    root, checkpoint = _build_run(tmp_path)
    before = hotspot.build_timeout_hotspot_report([root]).health_section()
    # runner が pair 直後に呼ぶ cleanup 相当（checkpoint の中身が消える）。
    shutil.rmtree(checkpoint)
    assert not checkpoint.exists()
    after = hotspot.build_timeout_hotspot_report([root]).health_section()
    assert after == before
    assert after["timeout_hotspots"]
    stem = "f_B1_B2"
    dump = (
        root / "REVE/sample/Eq/new/f/.runtime-metrics" / f"{stem}.stack-dump.txt"
    )
    assert dump.is_file()


def test_offline_rerun_reproduces_the_same_table(tmp_path):
    """run 中に書いた JSON と、run 終了後に再実行した JSON が一致する。"""
    root, checkpoint = _build_run(tmp_path)
    during = tmp_path / "during.json"
    assert hotspot.main([str(root), "--json", str(during)]) == 0
    shutil.rmtree(checkpoint)
    after = tmp_path / "after.json"
    assert hotspot.main([str(root), "--json", str(after)]) == 0
    first = json.loads(during.read_text(encoding="utf-8"))
    second = json.loads(after.read_text(encoding="utf-8"))
    assert first == second


def test_ambiguous_multi_execution_journal_does_not_guess_a_stage(tmp_path):
    """混在 journal では stage を推測せず、unknown へ落とす（合算しない）。"""
    root, _ = _build_run(tmp_path, with_sidecar=False)
    journal = root / "REVE/sample/Eq/new/f/f_B1_B2.stage.jsonl"
    journal.write_text(journal.read_text(encoding="utf-8") + "\n".join([
        _row(1, "note", payload={"note": "pair_journal_opened"}),
        _row(2, "stage_start", stage="decompile", payload={
            "kind": "region", "path": ["decompile"]}),
    ]) + "\n", encoding="utf-8")
    row = hotspot.build_timeout_hotspot_report([root]).rows[0]
    assert row.journal_unavailable_reason == "ambiguous_multi_execution"
    assert row.last_completed_stage is None
    assert row.in_progress_stage is None
    section = hotspot.build_timeout_hotspot_report([root]).health_section()
    assert section["last_completed_stage"] == {"(unknown)": 1}


def test_multi_execution_journal_uses_only_the_current_segment_with_a_sidecar(tmp_path):
    """sidecar が current の pid / start_token を持てば一意に選べる。"""
    root, _ = _build_run(tmp_path)
    journal = root / "REVE/sample/Eq/new/f/f_B1_B2.stage.jsonl"
    stale = "\n".join([
        _row(1, "note", payload={"note": "pair_journal_opened"}),
        json.dumps({
            "schema": STAGE_JOURNAL_SCHEMA, "seq": 2, "event": "handler_registered",
            "stage": "stack_dump_handler", "seconds": None, "t_monotonic": 2.0,
            "t_epoch": 1002.0, "pid": 1, "payload": {
                "pid": 1, "start_token": "linux-proc-starttime-1",
                "signal_number": int(signal.SIGUSR1), "all_threads": True,
                "readiness_basis": "faulthandler_register_returned",
            },
        }, sort_keys=True),
        _row(3, "stage_end", stage="stale_stage", seconds=999.0, payload={
            "kind": "region", "path": ["stale_stage"]}),
    ])
    journal.write_text(stale + "\n" + journal.read_text(encoding="utf-8"), encoding="utf-8")
    row = hotspot.build_timeout_hotspot_report([root]).rows[0]
    assert row.journal_unavailable_reason is None
    # 前 execution の 999s を current の最長として拾わない。
    assert row.longest_completed_stage == "obligation_build"
    assert row.last_completed_stage == "obligation_build"


# ---------------------------------------------------------------------------
# run_health_summary への merge
# ---------------------------------------------------------------------------


def test_health_summary_gains_timeout_sections_without_touching_the_others(tmp_path):
    root, _ = _build_run(tmp_path)
    health_json = tmp_path / "run_health_summary.json"
    health_text = tmp_path / "run_health_summary.txt"
    baseline_health = {
        "total_results": 1,
        "final_result_counts": {"TIMEOUT": 1},
        "unknown_by_reason": {"loop_recurrence_unproven": 1},
        "benchmark_validation": {
            "gate": "PASS", "pairs": 1,
            "hard_violations": {}, "suspicious": {}, "benign": {},
        },
    }
    health_json.write_text(json.dumps(baseline_health), encoding="utf-8")
    before_text = format_run_health_summary(baseline_health)
    assert hotspot.main([
        str(root),
        "--health-summary-json", str(health_json),
        "--health-summary-text", str(health_text),
    ]) == 0
    merged = json.loads(health_json.read_text(encoding="utf-8"))
    # 既存 key はそのまま残っている。
    for key in baseline_health:
        assert merged[key] == baseline_health[key]
    rendered = health_text.read_text(encoding="utf-8")
    assert rendered.startswith(before_text.split("\n", 1)[0])
    for line in before_text.splitlines():
        assert line in rendered
    assert "  timeout_kind:" in rendered
    assert "  timeout_hotspots:" in rendered
    assert "    - process_wall_clock: 1" in rendered


def test_health_summary_without_the_section_is_byte_identical(tmp_path):
    """節を持たない health（PR-124-C 以前 / 集計していない run）は 1 行も増えない。"""
    health = {"total_results": 0, "final_result_counts": {}}
    rendered = format_run_health_summary(health)
    assert "timeout_kind" not in rendered
    assert "timeout_hotspots" not in rendered
    assert timeout_diagnostics_from_health(health) is None


def test_zero_timeout_pairs_render_as_none_not_unknown(tmp_path):
    root, _ = _build_run(tmp_path, outcome="UNKNOWN")
    report = hotspot.build_timeout_hotspot_report([root])
    health = {TIMEOUT_DIAGNOSTICS_KEY: report.health_section()}
    rendered = format_run_health_summary(health)
    assert "  timeout_diagnostics: pairs=0 / 1" in rendered
    assert "  timeout_kind:\n    (none)" in rendered


def test_run_health_summary_cli_merges_the_report(tmp_path):
    from scripts.function_tracer_pcode.reporting import run_health_summary

    root, _ = _build_run(tmp_path)
    report_json = tmp_path / "timeout_hotspot_summary.json"
    assert hotspot.main([str(root), "--json", str(report_json)]) == 0
    overall = tmp_path / "overall_summary.txt"
    overall.write_text(
        "Overall totals: TOTAL= 1, EQ= 0, NOT_EQ= 0, ERROR= 0, UNKNOWN= 0, "
        "TIMEOUT= 1, INCOMPLETE= 0\n",
        encoding="utf-8",
    )
    output_json = tmp_path / "health.json"
    output_text = tmp_path / "health.txt"
    assert run_health_summary.main([
        "--overall-summary", str(overall),
        "--output-json", str(output_json),
        "--output-text", str(output_text),
        "--timeout-hotspots-json", str(report_json),
    ]) == 0
    merged = json.loads(output_json.read_text(encoding="utf-8"))
    assert merged[TIMEOUT_DIAGNOSTICS_KEY]["timeout_kind"] == {
        hotspot.KIND_PROCESS_WALL_CLOCK: 1
    }
    assert "timeout_hotspots" in output_text.read_text(encoding="utf-8")


def test_run_health_summary_without_the_option_adds_no_section(tmp_path):
    from scripts.function_tracer_pcode.reporting import run_health_summary

    overall = tmp_path / "overall_summary.txt"
    overall.write_text(
        "Overall totals: TOTAL= 0, EQ= 0, NOT_EQ= 0, ERROR= 0, UNKNOWN= 0, "
        "TIMEOUT= 0, INCOMPLETE= 0\n",
        encoding="utf-8",
    )
    output_json = tmp_path / "health.json"
    assert run_health_summary.main([
        "--overall-summary", str(overall), "--output-json", str(output_json),
    ]) == 0
    assert TIMEOUT_DIAGNOSTICS_KEY not in json.loads(
        output_json.read_text(encoding="utf-8")
    )


def test_unreadable_report_does_not_invent_a_section(tmp_path):
    from scripts.function_tracer_pcode.reporting import run_health_summary

    broken = tmp_path / "broken.json"
    broken.write_text("{not json", encoding="utf-8")
    health = run_health_summary.merge_timeout_diagnostics({}, broken)
    assert TIMEOUT_DIAGNOSTICS_KEY not in health


# ---------------------------------------------------------------------------
# 結果 JSON の抽出
# ---------------------------------------------------------------------------


def test_result_payload_is_read_from_the_last_block_of_the_log(tmp_path):
    log = tmp_path / "pair.log"
    log.write_text(
        "noise\n"
        "=== EQUIVALENCE_RESULT_JSON_BEGIN ===\n"
        '{"final_outcome": "OLD"}\n'
        "=== EQUIVALENCE_RESULT_JSON_END ===\n"
        "more noise\n"
        "=== EQUIVALENCE_RESULT_JSON_BEGIN ===\n"
        '{"final_outcome": "TIMEOUT"}\n'
        "=== EQUIVALENCE_RESULT_JSON_END ===\n",
        encoding="utf-8",
    )
    assert hotspot.read_result_payload(log) == {"final_outcome": "TIMEOUT"}


def test_missing_or_broken_result_payload_is_none(tmp_path):
    assert hotspot.read_result_payload(tmp_path / "absent.log") is None
    log = tmp_path / "pair.log"
    log.write_text("no markers\n", encoding="utf-8")
    assert hotspot.read_result_payload(log) is None
    broken = tmp_path / "broken.log"
    broken.write_text(
        "=== EQUIVALENCE_RESULT_JSON_BEGIN ===\n{oops\n"
        "=== EQUIVALENCE_RESULT_JSON_END ===\n",
        encoding="utf-8",
    )
    assert hotspot.read_result_payload(broken) is None


def test_pair_paths_are_derived_from_the_pair_status_path(tmp_path):
    status = tmp_path / "dir" / "f_B1_B2.pair-status.json"
    paths = hotspot.pair_paths(status)
    assert paths.log.name == "f_B1_B2.log"
    assert paths.journal.name == "f_B1_B2.stage.jsonl"
    assert paths.stack_dump.parent.name == ".runtime-metrics"
    assert paths.stack_dump.name == "f_B1_B2.stack-dump.txt"
    assert paths.diagnostic_status.name == "f_B1_B2.stack-dump.status.json"
