# -*- coding: utf-8 -*-
"""Issue #106 PR-106-B: the measured basis of ``ANALYSIS_TIMEOUT_MARGIN``.

``reporting/deadline_margin_summary.py`` splits the life of a pair the deadline
cut into consecutive intervals on the supervisor's clock (the deadline origin
and the child exit the supervisor observed, from its status sidecar).  These
tests pin that the intervals add up to the time charged against
``PAIR_PROCESS_TIMEOUT`` minus the budget, that only the current execution of a
journal is read, that the formula needs every interval, and that pairs which
cannot be measured are counted apart instead of being folded into the numbers.
(The reviewer's regressions are in ``test_issue106b_review1_regressions.py``.)
"""
from __future__ import annotations

import pytest

from scripts.function_tracer_pcode.core.stage_journal_reader import JournalRow, JournalSegment
from scripts.function_tracer_pcode.reporting import deadline_margin_summary as margin
from scripts.function_tracer_pcode.tests.unit.test_issue106b_review1_regressions import (
    _resolved_unknown,
    _root,
    _row,
    _sidecar,
    _trip,
    _write_pair,
)


def _segment(rows):
    return JournalSegment(index=0, rows=tuple(
        JournalRow(
            line_number=index, seq=row["seq"], event=row["event"], stage=row["stage"],
            seconds=row["seconds"], t_monotonic=row["t_monotonic"], t_epoch=row["t_epoch"],
            pid=row["pid"], payload=row["payload"],
        )
        for index, row in enumerate(rows, start=1)
    ))


def _journal(origin_at=20.0, budget=100.0, overrun=1.5, finalize=0.4, emit=0.3):
    trip_at = origin_at + budget + overrun
    finalize_start = trip_at + 0.2
    rows = [
        _row(1, "note", 0.0, payload={"note": "pair_journal_opened"}),
        _trip(2, trip_at, origin_at=origin_at),
        _row(3, "stage_start", finalize_start, "authority_finalize"),
        _row(4, "stage_end", finalize_start + finalize, "authority_finalize", finalize),
        _row(5, "stage_start", finalize_start + finalize + 0.1, "result_emit"),
        _row(6, "stage_end", finalize_start + finalize + 0.1 + emit, "result_emit", emit),
    ]
    return rows, finalize_start + finalize + 0.1 + emit


def test_the_intervals_add_up_to_the_time_charged_minus_the_budget():
    rows, last_at = _journal()
    pair = margin.pair_margin("k", "UNKNOWN", _segment(rows), _sidecar(last_at + 2.5))

    assert pair.pre == pytest.approx(20.0)
    assert pair.overrun == pytest.approx(1.5)
    assert pair.tail == pytest.approx(2.5)
    assert pair.needed == pytest.approx(last_at + 2.5 - 100.0)
    assert pair.pre + pair.overrun + pair.post_trip + pair.tail == pytest.approx(pair.needed)
    assert sum(pair.post_trip_parts.values()) == pytest.approx(pair.post_trip)


def test_a_pair_that_did_not_trip_has_no_margin_row():
    rows = [_row(1, "note", 0.0, payload={"note": "pair_journal_opened"})]

    assert margin.pair_margin("k", "EQUIVALENT", _segment(rows), _sidecar(10.0)) is None


def test_a_sidecar_without_the_deadline_is_unmeasurable_not_zero():
    rows, last_at = _journal()
    sidecar = _sidecar(last_at + 1.0)
    del sidecar["deadline_monotonic"]

    with pytest.raises(ValueError):
        margin.pair_margin("k", "UNKNOWN", _segment(rows), sidecar)


def test_a_journal_with_two_executions_and_no_child_identity_is_not_measured(tmp_path):
    root = _root(tmp_path)
    old, _ = _journal(overrun=40.0)
    new, last_at = _journal(overrun=0.5)
    _write_pair(root, "f_B1_B2", _resolved_unknown(), journal=old + new,
                sidecar=_sidecar(last_at + 1.0))
    payload = margin.report_dict(margin.summarize_roots([root]))

    # the old execution's 40 s overrun is never read as the current one's
    assert payload["tripped_pairs"] == 0
    assert [row[0] for row in payload["unreadable"]] == ["REVE/sample/Eq/new/f/f_B1_B2"]


def test_a_run_tree_is_summarised_and_the_unmeasurable_pairs_are_counted_apart(tmp_path):
    root = _root(tmp_path)
    rows, last_at = _journal()
    _write_pair(root, "f_B1_B2", _resolved_unknown(), journal=rows, sidecar=_sidecar(last_at + 2.0))
    _write_pair(root, "f_B3_B4", {"canonical_outcome": "EQUIVALENT"},
                journal=[_row(1, "note", 0.0, payload={"note": "pair_journal_opened"})],
                sidecar=_sidecar(10.0))
    _write_pair(root, "f_B5_B6", _resolved_unknown(), journal=rows)          # no sidecar
    _write_pair(root, "f_B7_B8", _resolved_unknown())                        # no journal

    payload = margin.report_dict(margin.summarize_roots([root]), margin_seconds=125.0)

    assert payload["tripped_pairs"] == 1
    assert payload["finished_before_deadline"] == 1
    assert sorted(row[0] for row in payload["unreadable"]) == [
        "REVE/sample/Eq/new/f/f_B5_B6", "REVE/sample/Eq/new/f/f_B7_B8",
    ]
    assert payload["lead_seconds"] == 2.0
    assert "p99" not in payload["intervals"]["needed"]
    one = payload["pairs"][0]
    assert payload["required_margin_seconds"] == pytest.approx(
        one["pre"] + one["overrun"] + one["post_trip"] + one["tail"] + 2.0
    )
    assert payload["margin_holds"] is False      # an unmeasurable pair is not a pass
    assert "Deadline margin summary:" in margin.format_report(payload)


def test_the_margin_holds_only_when_every_pair_fits(tmp_path):
    root = _root(tmp_path)
    rows, last_at = _journal()
    _write_pair(root, "f_B1_B2", _resolved_unknown(), journal=rows, sidecar=_sidecar(last_at + 2.0))
    report = margin.summarize_roots([root])
    needed = report.pairs[0].needed

    assert margin.report_dict(report, margin_seconds=needed + 102.0)["margin_holds"] is True
    tight = margin.report_dict(report, margin_seconds=needed + 1.0)
    assert tight["margin_holds"] is False
    assert tight["pairs_over_margin"] == ["REVE/sample/Eq/new/f/f_B1_B2"]


def test_a_run_without_a_deadline_is_not_measured(tmp_path):
    root = _root(tmp_path)
    (root / "run_manifest.txt").write_text("analysis_timeout=0\n", encoding="utf-8")
    rows, last_at = _journal()
    _write_pair(root, "f_B1_B2", _resolved_unknown(), journal=rows, sidecar=_sidecar(last_at))

    payload = margin.report_dict(margin.summarize_roots([root]))

    assert payload["tripped_pairs"] == 0
    assert payload["without_deadline"] == 1
    assert payload["required_margin_seconds"] is None   # no samples: no formula


def test_percentiles_are_nearest_rank_and_p99_needs_enough_samples():
    values = [float(index) for index in range(1, 101)]
    row = margin.describe(values)

    assert row == {"n": 100, "median": 50.0, "p90": 90.0, "max": 100.0, "p99": 99.0}
    assert "p99" not in margin.describe(values[:99])


def test_the_load_pool_feeds_pre_and_overrun_only(tmp_path):
    """``pre`` / ``overrun`` come from every observed run (load), ``post_trip`` /
    ``tail`` only from the profile's runs (they grow with the deadline)."""

    profile = _root(tmp_path / "profile")
    rows, last_at = _journal(origin_at=20.0, overrun=1.0)
    _write_pair(profile, "f_B1_B2", _resolved_unknown(), journal=rows, sidecar=_sidecar(last_at + 2.0))
    load = _root(tmp_path / "load")
    heavy, heavy_last = _journal(origin_at=50.0, overrun=9.0, finalize=30.0)
    _write_pair(load, "f_B1_B2", _resolved_unknown(), journal=heavy,
                sidecar=_sidecar(heavy_last + 20.0))

    alone = margin.report_dict(margin.summarize_roots([profile]))
    pooled = margin.report_dict(
        margin.summarize_roots([profile]), load_report=margin.summarize_roots([load]),
    )
    p = alone["pairs"][0]

    assert alone["required_margin_seconds"] == pytest.approx(
        p["pre"] + p["overrun"] + p["post_trip"] + p["tail"] + 2.0)
    # the load run's pre (50) and overrun (9) count; its post_trip (30.6) and tail (20) do not
    assert pooled["required_margin_seconds"] == pytest.approx(
        50.0 + 9.0 + p["post_trip"] + p["tail"] + 2.0)


def test_the_fixed_cost_pool_feeds_pre_only(tmp_path):
    profile = _root(tmp_path / "profile")
    rows, last_at = _journal(origin_at=20.0, overrun=1.0)
    _write_pair(profile, "f_B1_B2", _resolved_unknown(), journal=rows, sidecar=_sidecar(last_at + 2.0))
    other = _root(tmp_path / "other")
    heavy, heavy_last = _journal(origin_at=70.0, overrun=30.0)
    _write_pair(other, "f_B1_B2", _resolved_unknown(), journal=heavy, sidecar=_sidecar(heavy_last + 1.0))

    pooled = margin.report_dict(
        margin.summarize_roots([profile]), pre_report=margin.summarize_roots([other]),
    )
    p = pooled["pairs"][0]

    # the other run's pre (70) counts; its overrun (30) does not
    assert pooled["required_margin_seconds"] == pytest.approx(
        70.0 + p["overrun"] + p["post_trip"] + p["tail"] + 2.0)
