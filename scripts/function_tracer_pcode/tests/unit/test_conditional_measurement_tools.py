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


def test_gate_without_a_conditional_lane_is_unchanged(tmp_path):
    root = tmp_path / "results"
    _status(root, EQ, "f", "B1", "B2", "EQUIVALENT")
    _status(root, NEQ, "g", "N_B1", "O_B1", "NOT_EQ")
    report = soundness_gate.build_gate_report([root])
    assert report.conditional_records == ()
    assert report.passed is True
    assert report.unconditional_passed is True
    payload = report.as_dict()
    assert "conditional" not in payload
    assert "unconditional_passed" not in payload
    text = soundness_gate.format_gate_report(report)
    assert text.rstrip().endswith("GATE: PASS")
    assert "Conditional" not in text

    _status(root, EQ, "f", "B1", "B4", "NOT_EQ")
    failing = soundness_gate.build_gate_report([root])
    assert soundness_gate.format_gate_report(failing).rstrip().endswith(
        "GATE: FAIL (1 violations)"
    )


@pytest.mark.parametrize("sample,function,unconditional,conditional", [
    (EQ, "f", "UNKNOWN", "NOT_EQ"),
    (NEQ, "g", "UNKNOWN", "EQUIVALENT"),
])
def test_gate_fails_on_a_conditional_violation_in_both_directions(
    tmp_path, sample, function, unconditional, conditional,
):
    root = tmp_path / "results"
    _status(root, sample, function, "B1", "B2", unconditional, conditional=conditional)
    report = soundness_gate.build_gate_report([root])

    # The unconditional lane saw only UNKNOWN and passes on its own.
    assert report.violations == ()
    assert report.unconditional_passed is True
    assert len(report.conditional_violations) == 1
    assert report.passed is False

    payload = report.as_dict()
    assert payload["violations"] == 0
    assert payload["violation_rows"] == []
    assert payload["unconditional_passed"] is True
    assert payload["conditional"]["violations"] == 1
    assert payload["conditional"]["passed"] is False
    assert payload["conditional"]["violation_rows"][0]["outcome"] == conditional
    assert payload["conditional"]["counts"] == [
        {"label": report.records[0].label, "outcome": conditional, "count": 1},
    ]
    # The unconditional count table never sees the conditional outcome.
    assert all(row["outcome"] == unconditional for row in payload["counts"])

    text = soundness_gate.format_gate_report(report)
    assert "Conditional (assumption-dependent) outcomes by benchmark label:" in text
    assert "unconditional verdict: PASS" in text
    assert text.rstrip().endswith("GATE: FAIL (0 violations, 1 conditional violations)")
    assert soundness_gate.main([str(root)]) == soundness_gate.EXIT_VIOLATION


def test_a_sound_conditional_result_passes_but_is_still_counted(tmp_path):
    root = tmp_path / "results"
    _status(root, EQ, "f", "B1", "B2", "UNKNOWN", conditional="EQUIVALENT")
    _status(root, NEQ, "g", "N_B1", "O_B1", "UNKNOWN", conditional="NOT_EQ")
    report = soundness_gate.build_gate_report([root])
    assert report.conditional_violations == ()
    assert report.passed is True
    payload = report.as_dict()
    assert payload["conditional"]["pairs"] == 2
    assert payload["conditional"]["passed"] is True
    text = soundness_gate.format_gate_report(report)
    assert "Eq: EQUIVALENT=1" in text
    assert "Neq: NOT_EQ=1" in text
    assert text.rstrip().endswith("GATE: PASS")
    assert soundness_gate.main([str(root)]) == soundness_gate.EXIT_PASS
