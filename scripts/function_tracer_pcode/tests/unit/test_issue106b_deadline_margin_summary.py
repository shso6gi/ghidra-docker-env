# -*- coding: utf-8 -*-
"""Issue #106 PR-106-B: the measured basis of ``ANALYSIS_TIMEOUT_MARGIN``.

``reporting/deadline_margin_summary.py`` splits the life of a pair the deadline
cut into consecutive intervals on the supervisor's clock (the deadline origin
and the child exit the supervisor observed, from its status sidecar).  These
tests pin that the intervals add up to the time charged against
``PAIR_PROCESS_TIMEOUT`` minus the budget, that only the current execution of a
journal is read, that each interval is measured on its own (one that cannot be
measured keeps its reason and does not erase the others), and which pool feeds
which term of the formula.  (The reviewers' regressions are in
``test_issue106b_review1_regressions.py`` and the verdict matrix in
``test_issue106b_margin_acceptance.py``.)
"""
from __future__ import annotations

import pytest

from scripts.function_tracer_pcode.core.stage_journal_reader import JournalRow, JournalSegment
from scripts.function_tracer_pcode.reporting import deadline_margin_acceptance as acceptance
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


def _observe(rows, sidecar, outcome="UNKNOWN"):
    return margin.observe_pair(
        "k", outcome, termination="resolved", timeout_kind=None,
        segment=_segment(rows), segment_reason=None, sidecar=sidecar,
    )


def _profile(margin_seconds=140.0):
    return acceptance.MarginProfile(
        name="t", deadline_seconds=100.0, margin_seconds=margin_seconds,
        pair_process_timeout_seconds=240.0, machinery_commits=frozenset({"a" * 40}),
    )


def _run(root):
    (root / "run_manifest.txt").write_text(
        "analysis_timeout=100\npair_process_timeout_seconds=240\n"
        f"git_commit={'a' * 40}\ngit_dirty=0\n", encoding="utf-8")
    return margin.observe_run(root)


def test_the_intervals_add_up_to_the_time_charged_minus_the_budget():
    rows, last_at = _journal()
    pair = _observe(rows, _sidecar(last_at + 2.5))

    assert pair.cut is True and pair.missing == {}
    assert pair.values["pre"] == pytest.approx(20.0)
    assert pair.values["overrun"] == pytest.approx(1.5)
    assert pair.values["tail"] == pytest.approx(2.5)
    assert pair.needed == pytest.approx(last_at + 2.5 - 100.0)
    assert sum(pair.values.values()) == pytest.approx(pair.needed)
    assert sum(pair.post_trip_parts.values()) == pytest.approx(pair.values["post_trip"])


def test_a_pair_that_did_not_trip_is_not_cut_and_has_no_intervals():
    rows = [_row(1, "note", 0.0, payload={"note": "pair_journal_opened"})]
    pair = _observe(rows, _sidecar(10.0), outcome="EQUIVALENT")

    assert pair.cut is False
    assert pair.values == {} and pair.missing == {}


def test_a_sidecar_without_the_deadline_loses_only_the_intervals_that_need_it():
    rows, last_at = _journal()
    sidecar = _sidecar(last_at + 1.0)
    del sidecar["deadline_monotonic"]
    pair = _observe(rows, sidecar)

    assert sorted(pair.values) == ["overrun", "post_trip"]
    assert pair.missing == {
        "pre": "sidecar has no usable deadline_monotonic",
        "tail": "sidecar has no usable deadline_monotonic",
    }
    assert pair.needed is None


def test_a_journal_with_two_executions_and_no_child_identity_is_not_read(tmp_path):
    root = _root(tmp_path)
    old, _ = _journal(overrun=40.0)
    new, last_at = _journal(overrun=0.5)
    _write_pair(root, "f_B1_B2", _resolved_unknown(), journal=old + new,
                sidecar=_sidecar(last_at + 1.0))
    (pair,) = margin.observe_run(root).pairs

    # the old execution's 40 s overrun is never read as the current one's
    assert pair.cut is None
    assert pair.cut_unknown_reason == "journal: ambiguous_multi_execution"
    assert pair.values == {}


def test_a_run_tree_keeps_every_pair_and_its_reason(tmp_path):
    root = _root(tmp_path)
    rows, last_at = _journal()
    _write_pair(root, "f_B1_B2", _resolved_unknown(), journal=rows, sidecar=_sidecar(last_at + 2.0))
    _write_pair(root, "f_B3_B4", {"canonical_outcome": "EQUIVALENT"},
                journal=[_row(1, "note", 0.0, payload={"note": "pair_journal_opened"})],
                sidecar=_sidecar(10.0))
    _write_pair(root, "f_B5_B6", _resolved_unknown(), journal=rows)          # no sidecar
    _write_pair(root, "f_B7_B8", _resolved_unknown())                        # no journal
    pairs = {pair.key[-7:]: pair for pair in margin.observe_run(root).pairs}

    assert sorted(pairs) == ["f_B1_B2", "f_B3_B4", "f_B5_B6", "f_B7_B8"]
    assert pairs["f_B1_B2"].cut is True and pairs["f_B1_B2"].missing == {}
    assert pairs["f_B3_B4"].cut is False
    assert pairs["f_B5_B6"].missing == {
        "pre": "no stack-dump status sidecar", "tail": "no stack-dump status sidecar",
    }
    assert pairs["f_B7_B8"].cut is None
    assert pairs["f_B7_B8"].cut_unknown_reason.startswith("journal: ")


def test_the_run_facts_come_from_the_manifest(tmp_path):
    root = tmp_path / "eq"
    root.mkdir()
    _write_pair(root, "f_B1_B2", {"canonical_outcome": "EQUIVALENT"},
                journal=[_row(1, "note", 0.0, payload={"note": "pair_journal_opened"})])
    (root / "run_manifest.txt").write_text(
        "analysis_timeout=410\npair_process_timeout_seconds=600\nparallel_jobs=32\n"
        "git_commit=abc\ngit_dirty=0\n", encoding="utf-8")
    facts = margin.observe_run(root).facts

    assert (facts.deadline_seconds, facts.pair_process_timeout_seconds, facts.parallel_jobs,
            facts.git_commit, facts.git_dirty) == (410.0, 600.0, 32, "abc", False)
    assert facts.samples == frozenset({"REVE/sample/Eq/new"})
    (root / "run_manifest.txt").write_text("analysis_timeout=0\n", encoding="utf-8")
    assert margin.observe_run(root).facts.deadline_off is True


def test_a_manifest_without_the_deadline_takes_the_single_trip_budget(tmp_path):
    root = tmp_path / "eq"
    root.mkdir()
    rows, last_at = _journal()
    _write_pair(root, "f_B1_B2", _resolved_unknown(), journal=rows, sidecar=_sidecar(last_at))
    (root / "run_manifest.txt").write_text("git_commit=abc\n", encoding="utf-8")
    facts = margin.observe_run(root).facts

    assert facts.deadline_seconds == 100.0
    assert facts.deadline_note.startswith("deadline_tripped budget_seconds")


def test_percentiles_are_nearest_rank_and_p99_needs_enough_samples():
    values = [float(index) for index in range(1, 101)]
    row = margin.describe(values)

    assert row == {"n": 100, "median": 50.0, "p90": 90.0, "max": 100.0, "p99": 99.0}
    assert "p99" not in margin.describe(values[:99])


def test_the_load_pool_feeds_pre_and_overrun_only(tmp_path):
    """``pre`` / ``overrun`` come from every observed run (load), ``post_trip`` /
    ``tail`` only from the profile's runs (they grow with the deadline)."""

    profile = _root(tmp_path / "profile")
    rows, last_at = _journal(origin_at=20.0, overrun=1.0)      # post_trip 1.0, tail 2.0
    _write_pair(profile, "f_B1_B2", _resolved_unknown(), journal=rows, sidecar=_sidecar(last_at + 2.0))
    load = _root(tmp_path / "load")
    heavy, heavy_last = _journal(origin_at=50.0, overrun=9.0, finalize=30.0)
    _write_pair(load, "f_B1_B2", _resolved_unknown(), journal=heavy,
                sidecar=_sidecar(heavy_last + 20.0))

    alone = acceptance.evaluate_margin(_profile(), {"P": [_run(profile)]})
    pooled = acceptance.evaluate_margin(_profile(), {"P": [_run(profile)], "L": [_run(load)]})

    assert alone.status == "holds", alone
    assert alone.required_margin_seconds == pytest.approx(20.0 + 1.0 + 1.0 + 2.0 + 2.0)
    # the load run's pre (50) and overrun (9) count; its post_trip (30.6) and tail (20) do not
    assert pooled.status == "holds", pooled
    assert pooled.required_margin_seconds == pytest.approx(50.0 + 9.0 + 1.0 + 2.0 + 2.0)


def test_the_fixed_cost_pool_feeds_pre_only(tmp_path):
    profile = _root(tmp_path / "profile")
    rows, last_at = _journal(origin_at=20.0, overrun=1.0)
    _write_pair(profile, "f_B1_B2", _resolved_unknown(), journal=rows, sidecar=_sidecar(last_at + 2.0))
    other = _root(tmp_path / "other")
    heavy, heavy_last = _journal(origin_at=70.0, overrun=30.0)
    _write_pair(other, "f_B1_B2", _resolved_unknown(), journal=heavy, sidecar=_sidecar(heavy_last + 1.0))

    pooled = acceptance.evaluate_margin(_profile(), {"P": [_run(profile)], "F": [_run(other)]})

    # the other run's pre (70) counts; its overrun (30) does not
    assert pooled.status == "holds", pooled
    assert pooled.required_margin_seconds == pytest.approx(70.0 + 1.0 + 1.0 + 2.0 + 2.0)
