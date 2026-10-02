# -*- coding: utf-8 -*-
"""Issue #106 PR-106-B: the measured basis of ``ANALYSIS_TIMEOUT_MARGIN``.

``reporting/deadline_margin_summary.py`` splits the life of a pair the deadline
cut into consecutive intervals read from that pair's own records.  These tests
pin that the intervals do not overlap and add up to the supervisor's wall minus
the budget (no interval is counted twice), that the post-trip parts come from
the journal's stage intervals, and that pairs which cannot be measured are
counted apart instead of being folded into the statistics.
"""
from __future__ import annotations

import json
from pathlib import Path

import pytest

from scripts.function_tracer_pcode.reporting import deadline_margin_summary as margin

T0_EPOCH = 1_000_000.0
T0_MONO = 500.0


def _row(seq, event, at, stage=None, seconds=None, payload=None):
    return {
        "schema": "pair-stage-journal-v1", "seq": seq, "event": event, "stage": stage,
        "seconds": seconds, "t_monotonic": T0_MONO + at, "t_epoch": T0_EPOCH + at,
        "pid": 1, "payload": payload or {},
    }


def _journal(budget=30.0, origin_at=20.0, overrun=1.5, finalize=0.4, emit=0.3, tail_at=None):
    """A child that opens its journal at t=0, starts the deadline at ``origin_at``."""

    trip_at = origin_at + budget + overrun
    finalize_start = trip_at + 0.2
    rows = [
        _row(1, "note", 0.0, payload={"note": "pair_journal_opened"}),
        _row(2, "stage_end", 7.0, "jvm_start", 7.0),
        _row(3, "note", trip_at, payload={
            "note": "deadline_tripped", "stage": "solver", "budget_seconds": budget,
            "elapsed_seconds": budget + overrun,
        }),
        _row(4, "stage_start", finalize_start, "authority_finalize"),
        _row(5, "stage_end", finalize_start + finalize, "authority_finalize", finalize),
        _row(6, "stage_start", finalize_start + finalize + 0.1, "result_emit"),
        _row(7, "stage_end", finalize_start + finalize + 0.1 + emit, "result_emit", emit),
    ]
    return rows, finalize_start + finalize + 0.1 + emit


def _runtime(wall, finished_at):
    return {"elapsed_seconds": wall, "finished_at_epoch": T0_EPOCH + finished_at}


def test_the_intervals_are_consecutive_and_add_up_to_wall_minus_budget():
    rows, last_at = _journal()
    supervisor_started_at = -3.0  # the supervisor and the CLI start before the journal opens
    finished_at = last_at + 2.5
    wall = finished_at - supervisor_started_at
    pair = margin.pair_margin("k", "UNKNOWN", rows, _runtime(wall, finished_at))

    assert pair.pre == pytest.approx(23.0)      # supervisor start -> deadline origin
    assert pair.pre_child == pytest.approx(20.0)
    assert pair.overrun == pytest.approx(1.5)
    assert pair.tail == pytest.approx(2.5)
    assert pair.needed == pytest.approx(wall - 30.0)
    assert pair.pre + pair.overrun + pair.post_trip + pair.tail == pytest.approx(pair.needed)


def test_the_post_trip_parts_cover_the_post_trip_interval_once():
    rows, _ = _journal(finalize=0.4, emit=0.3)
    pair = margin.pair_margin("k", "UNKNOWN", rows, None)
    parts = pair.post_trip_parts

    assert parts["unwind"] == pytest.approx(0.2)
    assert parts["authority_finalize"] == pytest.approx(0.4)
    assert parts["result_emit"] == pytest.approx(0.3)
    assert parts["other"] == pytest.approx(0.1)
    assert sum(parts.values()) == pytest.approx(pair.post_trip)


def test_without_a_runtime_receipt_only_the_journal_intervals_exist():
    rows, _ = _journal()
    pair = margin.pair_margin("k", "UNKNOWN", rows, None)

    assert pair.needed is None and pair.pre is None and pair.tail is None
    assert pair.overrun == pytest.approx(1.5)


def test_only_the_last_execution_of_a_journal_is_read():
    old, _ = _journal(overrun=40.0)
    new, last_at = _journal(overrun=0.5)
    pair = margin.pair_margin("k", "UNKNOWN", old + new, None)

    assert pair.overrun == pytest.approx(0.5)


def test_a_pair_that_did_not_trip_has_no_margin_row():
    rows = [_row(1, "note", 0.0, payload={"note": "pair_journal_opened"})]

    assert margin.pair_margin("k", "EQUIVALENT", rows, _runtime(10.0, 10.0)) is None


def _write_pair(root: Path, stem: str, outcome: str, journal=None, runtime=None):
    folder = root / "sample" / "fn"
    folder.mkdir(parents=True, exist_ok=True)
    (folder / f"{stem}.pair-status.json").write_text(
        json.dumps({"canonical_outcome": outcome}), encoding="utf-8")
    if journal is not None:
        (folder / f"{stem}.stage.jsonl").write_text(
            "".join(json.dumps(row) + "\n" for row in journal), encoding="utf-8")
    if runtime is not None:
        (folder / ".runtime-metrics").mkdir(exist_ok=True)
        (folder / ".runtime-metrics" / f"{stem}.runtime.json").write_text(
            json.dumps(runtime), encoding="utf-8")


def test_a_run_tree_is_summarised_and_the_unmeasurable_pairs_are_counted_apart(tmp_path):
    root = tmp_path / "eq"
    root.mkdir()
    (root / "run_manifest.txt").write_text(
        "analysis_timeout=30\npair_stack_dump_lead=2s\n", encoding="utf-8")
    rows, last_at = _journal()
    _write_pair(root, "fn_B1_B2", "UNKNOWN", rows, _runtime(last_at + 5.0, last_at + 2.0))
    _write_pair(root, "fn_B3_B4", "EQUIVALENT",
                [_row(1, "note", 0.0, payload={"note": "pair_journal_opened"})],
                _runtime(10.0, 10.0))
    _write_pair(root, "fn_B5_B6", "TIMEOUT")
    _write_pair(root, "fn_B7_B8", "UNKNOWN", None, None)  # no journal at all

    payload = margin.report_dict(margin.summarize_roots([root]))

    assert payload["tripped_pairs"] == 1
    assert payload["finished_before_deadline"] == 1
    assert payload["process_timeouts"] == ["sample/fn/fn_B5_B6"]
    assert [row[0] for row in payload["unreadable"]] == ["sample/fn/fn_B7_B8"]
    assert payload["pair_stack_dump_lead_seconds"] == 2.0
    assert payload["intervals"]["needed"]["n"] == 1
    assert "p99" not in payload["intervals"]["needed"]  # too few samples to name a p99
    assert "Deadline margin summary:" in margin.format_report(payload)


def test_a_run_without_a_deadline_is_not_measured(tmp_path):
    root = tmp_path / "eq"
    root.mkdir()
    (root / "run_manifest.txt").write_text("analysis_timeout=0\n", encoding="utf-8")
    rows, last_at = _journal()
    _write_pair(root, "fn_B1_B2", "UNKNOWN", rows, _runtime(last_at, last_at))

    payload = margin.report_dict(margin.summarize_roots([root]))

    assert payload["tripped_pairs"] == 0
    assert payload["without_deadline"] == 1


def test_percentiles_are_nearest_rank_and_p99_needs_enough_samples():
    values = [float(index) for index in range(1, 101)]
    row = margin.describe(values)

    assert row == {"n": 100, "median": 50.0, "p90": 90.0, "max": 100.0, "p99": 99.0}
    assert "p99" not in margin.describe(values[:99])
