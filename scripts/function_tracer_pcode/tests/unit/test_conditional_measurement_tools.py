# -*- coding: utf-8 -*-
"""Issue #20 PR-A: outcome_transition and soundness_gate report conditional apart.

Both tools keep their unconditional semantics exactly -- ``--fail-on-change``
still means the unconditional outcome moved, and the soundness verdict line of
a run without a conditional lane is unchanged -- while an assumption-dependent
result gets its own matrix, its own counts, and its own failure switch.
"""
from __future__ import annotations

import json

import pytest

from scripts.function_tracer_pcode.reporting import outcome_transition, soundness_gate
from scripts.function_tracer_pcode.reporting.outcome_transition import (
    CONDITIONAL_NONE,
    build_transition,
    format_transition,
)
from scripts.function_tracer_pcode.reporting.pair_outcomes import (
    OUTCOME_MISSING,
    load_pair_outcomes,
)

from scripts.function_tracer_pcode.tests.unit.test_benchmark_validation_gate import (
    EQ,
    NEQ,
    write_pair_status,
)


def _status(root, sample, function, left, right, outcome, conditional=None):
    path = write_pair_status(root, sample, function, left, right, outcome)
    if conditional is not None:
        payload = json.loads(path.read_text(encoding="utf-8"))
        payload["conditional_outcome"] = conditional
        path.write_text(json.dumps(payload), encoding="utf-8")
    return path


# --- outcome_transition -----------------------------------------------------


def test_transition_without_a_conditional_lane_is_unchanged(tmp_path):
    before, after = tmp_path / "before", tmp_path / "after"
    for root in (before, after):
        _status(root, EQ, "f", "B1", "B2", "UNKNOWN")
        _status(root, EQ, "f", "B1", "B3", "EQUIVALENT")
    report = build_transition(load_pair_outcomes(before), load_pair_outcomes(after))
    assert report.conditional_rows == ()
    assert "conditional" not in report.as_dict()
    text = format_transition(report)
    assert "Conditional" not in text
    assert "Pairs compared: 2 (changed: 0)" in text


def test_conditional_transition_is_a_separate_matrix(tmp_path):
    before, after = tmp_path / "before", tmp_path / "after"
    # Unchanged unconditionally; the conditional column is what moves.
    _status(before, EQ, "f", "B1", "B2", "UNKNOWN")
    _status(after, EQ, "f", "B1", "B2", "UNKNOWN", conditional="EQUIVALENT")
    _status(before, EQ, "f", "B1", "B3", "UNKNOWN", conditional="UNKNOWN")
    _status(after, EQ, "f", "B1", "B3", "UNKNOWN", conditional="EQUIVALENT")
    _status(before, EQ, "f", "B1", "B4", "UNKNOWN", conditional="EQUIVALENT")
    _status(after, EQ, "f", "B1", "B4", "UNKNOWN", conditional="EQUIVALENT")
    _status(before, EQ, "f", "B1", "B5", "UNKNOWN")
    _status(after, EQ, "f", "B1", "B5", "UNKNOWN")

    report = build_transition(load_pair_outcomes(before), load_pair_outcomes(after))
    # The unconditional matrix is untouched by any of it.
    assert report.changed_rows == ()
    assert report.matrix == {("UNKNOWN", "UNKNOWN"): 4}

    assert len(report.conditional_rows) == 3
    assert len(report.conditional_changed_rows) == 2
    assert report.conditional_matrix == {
        (CONDITIONAL_NONE, "EQUIVALENT"): 1,
        ("UNKNOWN", "EQUIVALENT"): 1,
        ("EQUIVALENT", "EQUIVALENT"): 1,
    }
    payload = report.as_dict()
    assert payload["changed"] == 0
    assert payload["conditional"]["pairs"] == 3
    assert payload["conditional"]["changed"] == 2
    assert {row["pair_id"] for row in payload["conditional"]["rows"]} == {
        "B1_B2", "B1_B3", "B1_B4",
    }
    text = format_transition(report)
    assert "Conditional transition matrix" in text
    assert "Pairs with a conditional result: 3 (changed: 2)" in text


def test_a_pair_missing_on_one_side_shows_missing_on_the_conditional_axis(tmp_path):
    before, after = tmp_path / "before", tmp_path / "after"
    _status(before, EQ, "f", "B1", "B2", "UNKNOWN", conditional="EQUIVALENT")
    report = build_transition(load_pair_outcomes(before), load_pair_outcomes(after))
    row = report.rows[0]
    assert (row.before, row.after) == ("UNKNOWN", OUTCOME_MISSING)
    assert (row.conditional_before, row.conditional_after) == (
        "EQUIVALENT", OUTCOME_MISSING,
    )
    assert report.conditional_changed_rows == (row,)


def test_fail_on_change_keeps_its_unconditional_meaning(tmp_path, capsys):
    before, after = tmp_path / "before", tmp_path / "after"
    _status(before, EQ, "f", "B1", "B2", "UNKNOWN")
    _status(after, EQ, "f", "B1", "B2", "UNKNOWN", conditional="EQUIVALENT")

    # A conditional-only change does not trip --fail-on-change ...
    assert outcome_transition.main([
        "--before", str(before), "--after", str(after), "--fail-on-change",
    ]) == 0
    capsys.readouterr()
    # ... and has its own switch.
    assert outcome_transition.main([
        "--before", str(before), "--after", str(after),
        "--fail-on-conditional-change",
    ]) == 3
    capsys.readouterr()
    # Both switches together still report the unconditional exit first.
    _status(after, EQ, "f", "B1", "B3", "NOT_EQ")
    _status(before, EQ, "f", "B1", "B3", "UNKNOWN")
    assert outcome_transition.main([
        "--before", str(before), "--after", str(after),
        "--fail-on-change", "--fail-on-conditional-change",
    ]) == 2
    capsys.readouterr()


# --- soundness_gate ---------------------------------------------------------
#
# Issue #15 PR-15-B replaced the gate's label-only rule with verified
# function-level relations, so the conditional *verdict* is covered by
# ``test_soundness_gate_v2.py`` against real conditional receipts.  What stays
# here is the part this file owns: a run without a conditional lane reads
# exactly as before, and a conditional column that arrives without its receipt
# is refused instead of being counted.


def test_a_run_without_a_conditional_lane_reports_no_conditional_row(tmp_path):
    root = tmp_path / "results"
    _status(root, EQ, "f", "B1", "B2", "EQUIVALENT")
    _status(root, NEQ, "g", "N_B1", "O_B1", "NOT_EQ")

    report = soundness_gate.build_gate_report([root])

    assert report.accumulator.compatibility_unknown_rows == []
    assert report.accumulator.config_integrity_violations == []
    assert report.passed is True
    assert soundness_gate.format_gate_report(report).rstrip().endswith("GATE: PASS")


def test_a_conditional_column_without_its_receipt_is_refused(tmp_path):
    """The signed status cannot carry one without the other; a tree that does is broken."""

    root = tmp_path / "results"
    _status(root, NEQ, "g", "N_B1", "O_B1", "UNKNOWN", conditional="EQUIVALENT")

    report = soundness_gate.build_gate_report([root])

    assert [row["detail"] for row in report.accumulator.config_integrity_violations] == [
        "conditional_column_half_written",
    ]
    assert report.passed is False
    assert soundness_gate.main([str(root)]) == soundness_gate.EXIT_VIOLATION
