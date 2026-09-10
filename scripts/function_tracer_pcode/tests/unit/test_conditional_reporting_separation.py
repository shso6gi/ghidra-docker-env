# -*- coding: utf-8 -*-
"""Issue #20 PR-A: the conditional column is aggregated apart from the rest.

Every assertion here holds while the conditional lane is inactive, which is the
point: adding the column must not move a single unconditional count, line, or
gate verdict, and a conditional result must be gated against ground truth in
both directions once it does appear.
"""
from __future__ import annotations

import json

import pytest

from scripts.function_tracer_pcode.authority.contracts import Outcome
from scripts.function_tracer_pcode.reporting import benchmark_validation_gate as gate
from scripts.function_tracer_pcode.reporting.pair_outcomes import iter_pair_outcomes
from scripts.function_tracer_pcode.reporting.result_summary import (
    STATUS_EQ,
    STATUS_NOT_EQ,
    STATUS_UNKNOWN,
    ValidationLogRecord,
    aggregate_validation_records,
    classify_result_payload,
    format_benchmark_validation_lines,
    format_function_results_summary,
)

from scripts.function_tracer_pcode.tests.unit.test_benchmark_validation_gate import (
    EQ,
    NEQ,
    _manifest,
    write_pair_status,
)


def _record(pair_label: str, status: str, conditional=None) -> ValidationLogRecord:
    return ValidationLogRecord(
        path=f"/logs/{pair_label}.log",
        function_name="f",
        pair_label=pair_label,
        status=status,
        conditional_status=conditional,
    )


def _write_pair_status_with_conditional(root, sample, function, left, right, outcome, conditional):
    path = write_pair_status(root, sample, function, left, right, outcome)
    payload = json.loads(path.read_text(encoding="utf-8"))
    payload["conditional_outcome"] = conditional
    path.write_text(json.dumps(payload), encoding="utf-8")
    return path


# --- aggregation ------------------------------------------------------------


def test_conditional_results_are_counted_in_their_own_column():
    aggregate = aggregate_validation_records((
        _record("B1_B2", STATUS_UNKNOWN, "EQUIVALENT"),
        _record("B1_B3", STATUS_UNKNOWN, "EQUIVALENT"),
        _record("B1_B4", STATUS_UNKNOWN, "UNKNOWN"),
        _record("B1_B5", STATUS_UNKNOWN),
        _record("B2_B3", STATUS_EQ),
    ))
    # The unconditional column counts every pair exactly once and knows
    # nothing about the conditional proofs.
    assert aggregate.count(STATUS_UNKNOWN) == 4
    assert aggregate.count(STATUS_EQ) == 1
    assert aggregate.total_pairs == 5
    assert sum(aggregate.counts.values()) == aggregate.total_pairs
    assert aggregate.conditional_counts == {"EQUIVALENT": 2, "UNKNOWN": 1}
    assert aggregate.conditional_count("EQUIVALENT") == 2
    assert aggregate.total_conditional_pairs == 3
    assert aggregate.conditional_pairs_by_status["EQUIVALENT"] == ("B1_B2", "B1_B3")
    payload = aggregate.to_dict()
    assert payload["counts"][STATUS_UNKNOWN] == 4
    assert payload["conditional_counts"] == {"EQUIVALENT": 2, "UNKNOWN": 1}


def test_a_conditional_result_cannot_move_the_unconditional_counts():
    without = aggregate_validation_records((
        _record("B1_B2", STATUS_UNKNOWN), _record("B2_B3", STATUS_UNKNOWN),
    ))
    with_conditional = aggregate_validation_records((
        _record("B1_B2", STATUS_UNKNOWN, "EQUIVALENT"),
        _record("B2_B3", STATUS_UNKNOWN, "NOT_EQ"),
    ))
    assert with_conditional.counts == without.counts
    assert with_conditional.pairs_by_status == without.pairs_by_status
    assert without.conditional_counts == {}
    assert with_conditional.conditional_counts == {"EQUIVALENT": 1, "NOT_EQ": 1}


def test_summary_text_is_unchanged_without_a_conditional_lane():
    records = (_record("B1_B2", STATUS_UNKNOWN), _record("B2_B3", STATUS_EQ))
    text = format_function_results_summary(
        "f", aggregate_validation_records(records), include_unknown_reason_summary=False,
    )
    assert "Conditional" not in text

    conditional = (
        _record("B1_B2", STATUS_UNKNOWN, "EQUIVALENT"), _record("B2_B3", STATUS_EQ),
    )
    conditional_text = format_function_results_summary(
        "f", aggregate_validation_records(conditional), include_unknown_reason_summary=False,
    )
    assert "Conditional (assumption-dependent), reported separately: EQUIVALENT=1" in (
        conditional_text
    )
    # Only the added line differs; every unconditional line is byte-identical.
    added = [line for line in conditional_text.splitlines() if line not in text.splitlines()]
    assert added == [
        "  Conditional (assumption-dependent), reported separately: EQUIVALENT=1"
    ]


def test_the_payload_classifier_ignores_the_conditional_column():
    payload = {"is_equivalent": None, "conditional_outcome": "EQUIVALENT"}
    assert classify_result_payload(payload) == STATUS_UNKNOWN
    payload = {"is_equivalent": False, "conditional_outcome": "EQUIVALENT"}
    assert classify_result_payload(payload) == STATUS_NOT_EQ


# --- pair status ------------------------------------------------------------


def test_pair_outcomes_read_the_conditional_column_when_present(tmp_path):
    root = tmp_path / "results"
    write_pair_status(root, EQ, "f", "B1", "B2", "UNKNOWN")
    _write_pair_status_with_conditional(root, EQ, "f", "B1", "B3", "UNKNOWN", "EQUIVALENT")
    by_pair = {record.pair_id: record for record in iter_pair_outcomes(root)}
    assert by_pair["B1_B2"].outcome == "UNKNOWN"
    assert by_pair["B1_B2"].conditional_outcome is None
    assert by_pair["B1_B3"].outcome == "UNKNOWN"
    assert by_pair["B1_B3"].conditional_outcome == "EQUIVALENT"


# --- benchmark gate ---------------------------------------------------------


def test_gate_is_unchanged_when_no_pair_carries_a_conditional_outcome(tmp_path):
    root = tmp_path / "results"
    write_pair_status(root, EQ, "f", "B1", "B2", "EQUIVALENT")
    write_pair_status(root, NEQ, "confirmed", "N_B1", "O_B1", "NOT_EQ")
    manifest = gate.FunctionDiffManifest.load(_manifest(tmp_path))
    report = gate.build_gate_report([root], manifest)
    assert report.status == gate.GATE_STATUS_PASS
    assert report.conditional_classified == ()
    section = report.health_section()
    assert section["conditional"]["pairs"] == 0
    assert "conditional_soundness_violations" not in "\n".join(
        format_benchmark_validation_lines(section)
    )

    # A failing run without a conditional lane keeps its verdict line too.
    write_pair_status(root, EQ, "f", "B1", "B4", "NOT_EQ")
    failing = gate.build_gate_report([root], manifest)
    assert failing.status == gate.GATE_STATUS_FAIL
    assert "GATE: FAIL (1 hard violations, 0 suspicious)" in gate.format_gate_report(failing)
    assert "conditional" not in gate.format_gate_report(failing)


@pytest.mark.parametrize("sample,function,left,right,unconditional,conditional,kind", [
    # A Neq function with a reviewed counterexample judged conditionally EQ.
    (NEQ, "confirmed", "N_B1", "O_B1", "UNKNOWN", "EQUIVALENT",
     gate.KIND_NEQ_CONFIRMED_NOT_EQ_EQUIVALENT),
    # An Eq sample judged conditionally NOT_EQ.
    (EQ, "f", "B1", "B2", "UNKNOWN", "NOT_EQ", gate.KIND_EQ_NOT_EQ),
    # A Neq pair the manifest cannot classify, judged conditionally EQ.
    ("fam/missing/Neq/newV-oldV", "f", "N_B1", "O_B1", "UNKNOWN", "EQUIVALENT",
     gate.KIND_NEQ_EQUIVALENT_UNMAPPED),
])
def test_gate_fails_on_a_conditional_ground_truth_violation_in_both_directions(
    tmp_path, sample, function, left, right, unconditional, conditional, kind,
):
    root = tmp_path / "results"
    _write_pair_status_with_conditional(
        root, sample, function, left, right, unconditional, conditional,
    )
    manifest = gate.FunctionDiffManifest.load(_manifest(tmp_path))
    report = gate.build_gate_report([root], manifest)
    # The unconditional lane saw nothing but UNKNOWN and has no violation.
    assert report.hard_violations == ()
    assert [item.kind for item in report.conditional_hard_violations] == [kind]
    assert report.status == gate.GATE_STATUS_FAIL
    assert report.exit_code == gate.EXIT_VIOLATION
    section = report.health_section()
    assert section["hard_violations"][kind] == 0
    assert section["conditional"]["hard_violations"][kind] == 1
    assert section["conditional"]["pairs"] == 1
    lines = "\n".join(format_benchmark_validation_lines(section))
    assert "conditional_soundness_violations" in lines
    payload = report.as_dict()
    assert payload["rows"] == []
    assert [row["kind"] for row in payload["conditional_rows"]] == [kind]
    text = gate.format_gate_report(report)
    assert kind in text
    assert "1 conditional hard violations" in text


def test_a_sound_conditional_result_is_reported_without_failing_the_gate(tmp_path):
    root = tmp_path / "results"
    _write_pair_status_with_conditional(root, NEQ, "identical", "N_B1", "O_B1", "UNKNOWN", "EQUIVALENT")
    _write_pair_status_with_conditional(root, NEQ, "confirmed", "N_B1", "O_B1", "UNKNOWN", "NOT_EQ")
    manifest = gate.FunctionDiffManifest.load(_manifest(tmp_path))
    report = gate.build_gate_report([root], manifest)
    assert report.status == gate.GATE_STATUS_PASS
    assert report.conditional_hard_violations == ()
    section = report.health_section()
    assert section["conditional"]["benign"][gate.KIND_BENIGN_EQ_NO_IMPACT] == 1
    assert section["conditional"]["outcomes_by_label"] == {
        "Neq": {"EQUIVALENT": 1, "NOT_EQ": 1},
    }
    assert section["outcomes_by_label"] == {"Neq": {"UNKNOWN": 2}}


def test_conditional_outcome_values_are_the_unchanged_five(tmp_path):
    """No new Outcome value is introduced for the conditional column."""
    assert {member.value for member in Outcome} == {
        "EQUIVALENT", "NOT_EQ", "UNKNOWN", "TIMEOUT", "ERROR",
    }
