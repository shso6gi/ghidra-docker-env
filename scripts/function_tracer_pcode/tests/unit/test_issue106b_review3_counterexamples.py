# -*- coding: utf-8 -*-
"""Issue #106 PR-106-B review 3: present or convertible is not complete, valid and consistent.

Each scenario writes run trees the way the runners write them, runs the margin
tool's command line with a complete profile (the flags the reviewed head
``a6cf3b20`` already had), and reads the verdict.  Every scenario holds one
normal, fully measured profile pair that fits the margin -- alone it is a pass
-- plus the defect under test:

* a journal whose trip line is lost (written as a partial final line, garbled,
  beyond the read limit, or with a payload of the wrong type): the reader
  reported the loss, but the margin read the journal as "no trip";
* a non-finite number: in the command line (``nan`` / ``inf`` / a negative
  value) or in the measured trip (a JSON ``NaN``), which compared as neither
  over nor under the margin;
* facts that disagree: the manifest's analysis deadline against the budget the
  trips recorded, the manifest's process timeout against the supervisor's;
* a ``canonical_outcome`` that is not one of the five outcomes, read as a
  resolved pair.

None of these is evidence that the margin holds.  The expected statuses and
reasons are literal strings, never computed with the code under test.
"""
from __future__ import annotations

import json
from pathlib import Path

import pytest

from scripts.function_tracer_pcode.reporting import deadline_margin_summary as margin
from scripts.function_tracer_pcode.tests.unit.test_issue106b_review1_regressions import (
    _resolved_unknown,
    _row,
    _sidecar,
    _trip,
    _write_pair,
)

COMMIT = "c" * 40
KEY_2 = "REVE/sample/Eq/new/f/f_B3_B4"
#: the margin under evaluation: the normal pair needs 25.5 s (20 + 1 + 1.5 + 1 + lead 2)
MARGIN = 50.0


def _tree(tmp_path: Path, name: str = "profile", *, deadline="100", process="240") -> Path:
    root = tmp_path / name / "eq"
    root.mkdir(parents=True)
    (root / "run_manifest.txt").write_text(
        f"analysis_timeout={deadline}\npair_process_timeout_seconds={process}\n"
        f"pair_stack_dump_lead=2s\nparallel_jobs=4\ngit_commit={COMMIT}\ngit_dirty=0\n",
        encoding="utf-8")
    return root


def _cut_rows(origin_at=20.0, overrun=1.0, emit=1.5, budget=100.0):
    trip_at = origin_at + budget + overrun
    trip = _trip(2, trip_at, origin_at=origin_at)
    trip["payload"]["budget_seconds"] = budget
    return [
        _row(1, "note", 0.0, payload={"note": "pair_journal_opened"}),
        trip,
        _row(3, "stage_start", trip_at, "result_emit"),
        _row(4, "stage_end", trip_at + emit, "result_emit", emit),
    ], trip_at + emit


def _normal(root: Path) -> None:
    rows, last_at = _cut_rows()
    _write_pair(root, "f_B1_B2", _resolved_unknown(), journal=rows, sidecar=_sidecar(last_at + 1.0))


def _journal_path(root: Path, stem: str) -> Path:
    return root / "REVE" / "sample" / "Eq" / "new" / "f" / f"{stem}.stage.jsonl"


def _slow_pair_with_journal_text(root: Path, text: str) -> None:
    """A pair that needed 120 s after the deadline (more than the margin), whose journal
    is ``text``."""

    _write_pair(root, "f_B3_B4", _resolved_unknown(), journal=[], sidecar=_sidecar(220.0))
    _journal_path(root, "f_B3_B4").write_text(text, encoding="utf-8")


def _lines(rows) -> str:
    return "".join(json.dumps(row) + "\n" for row in rows)


def _verdict(tmp_path, profile, *, margin_seconds=str(MARGIN), deadline="100", process="240",
             extra=()):
    out = tmp_path / "verdict.json"
    argv = [str(root) for root in profile] + [
        "--margin", margin_seconds, "--profile-deadline", deadline,
        "--pair-process-timeout", process, "--machinery-commit", COMMIT,
        "--json", str(out), *extra,
    ]
    assert margin.main(argv) == 0
    return json.loads(out.read_text(encoding="utf-8"))["verdict"]


def test_the_normal_pair_alone_holds(tmp_path):
    profile = _tree(tmp_path)
    _normal(profile)
    verdict = _verdict(tmp_path, [profile])

    assert verdict["status"] == "holds", verdict
    assert verdict["required_margin_seconds"] == 25.5


def test_a_start_refused_trip_keeps_its_negative_overrun(tmp_path):
    """Control: the deadline refused to start a sub-operation 0.3 s early; that is valid."""

    profile = _tree(tmp_path)
    rows, last_at = _cut_rows(overrun=-0.3)
    _write_pair(profile, "f_B1_B2", _resolved_unknown(), journal=rows, sidecar=_sidecar(last_at + 1.0))
    verdict = _verdict(tmp_path, [profile])

    assert verdict["status"] == "holds", verdict
    assert verdict["terms"]["overrun"]["max"] == -0.3


# --------------------------------------------------------------------------
# 1. an incomplete journal is not "no trip"
# --------------------------------------------------------------------------


def _trip_lost_as(kind: str) -> str:
    rows, _ = _cut_rows(origin_at=20.0, overrun=60.0, emit=30.0)
    if kind == "partial_final_line":
        return _lines(rows[:1]) + json.dumps(rows[1])                     # no newline: cut off
    if kind == "malformed_line":
        return _lines(rows[:1]) + '{"schema": "pair-stage-journal-v1", "event": "no\n' + _lines(rows[2:])
    if kind == "payload_not_an_object":
        broken = dict(rows[1], payload="deadline_tripped")
        return _lines([rows[0], broken, *rows[2:]])
    raise AssertionError(kind)


@pytest.mark.parametrize("kind, reason", [
    ("partial_final_line", "partial_final_line"),
    ("malformed_line", "malformed_lines=1"),
    ("payload_not_an_object", "field_errors=1"),
])
def test_a_journal_that_lost_its_trip_is_not_a_pass(tmp_path, kind, reason):
    profile = _tree(tmp_path)
    _normal(profile)
    _slow_pair_with_journal_text(profile, _trip_lost_as(kind))
    verdict = _verdict(tmp_path, [profile])

    assert verdict["status"] == "undetermined", verdict
    assert verdict["undetermined"] == [
        f"pool P: pair {KEY_2}: cannot tell whether the deadline cut it "
        f"(journal incomplete: {reason})"
    ]


def test_a_journal_truncated_before_its_trip_is_not_a_pass(tmp_path):
    profile = _tree(tmp_path)
    _normal(profile)
    rows, _ = _cut_rows(origin_at=20.0, overrun=60.0, emit=30.0)
    filler = json.dumps(dict(_row(0, "note", 1.0, payload={"note": "x" * 1000}), seq=None)) + "\n"
    padding = filler * (9 * 1024 * 1024 // len(filler))                    # past the read limit
    _slow_pair_with_journal_text(profile, _lines(rows[:1]) + padding + _lines(rows[1:]))
    verdict = _verdict(tmp_path, [profile])

    assert verdict["status"] == "undetermined", verdict
    assert verdict["undetermined"] == [
        f"pool P: pair {KEY_2}: cannot tell whether the deadline cut it "
        "(journal incomplete: truncated, partial_final_line)"
    ]


# --------------------------------------------------------------------------
# 2. a number that is not finite (or out of range) is not evidence
# --------------------------------------------------------------------------


@pytest.mark.parametrize("option", ["--margin", "--profile-deadline", "--pair-process-timeout"])
@pytest.mark.parametrize("value", ["nan", "inf", "-5", "0"])
def test_a_profile_number_that_is_not_a_positive_finite_number_is_refused(tmp_path, option, value):
    profile = _tree(tmp_path)
    _normal(profile)
    flags = {"--margin": str(MARGIN), "--profile-deadline": "100", "--pair-process-timeout": "240"}
    flags[option] = value
    argv = [str(profile), "--machinery-commit", COMMIT, "--json", str(tmp_path / "v.json")]
    for name, text in flags.items():
        argv += [name, text]

    with pytest.raises(SystemExit) as refused:
        margin.main(argv)
    assert refused.value.code == 2                      # argparse refuses the value
    assert not (tmp_path / "v.json").exists()


@pytest.mark.parametrize("field, value, reason", [
    ("elapsed_seconds", float("nan"), "deadline_tripped elapsed_seconds is not a finite number"),
    ("elapsed_seconds", float("inf"), "deadline_tripped elapsed_seconds is not a finite number"),
    ("budget_seconds", float("nan"), "deadline_tripped budget_seconds is not a finite number"),
    ("budget_seconds", -100.0, "deadline_tripped budget_seconds is not positive"),
])
def test_a_trip_with_a_non_finite_or_impossible_number_is_not_measured(tmp_path, field, value, reason):
    profile = _tree(tmp_path)
    _normal(profile)
    rows, last_at = _cut_rows(origin_at=20.0, overrun=60.0, emit=30.0)
    rows[1]["payload"][field] = value                                    # JSON NaN / Infinity
    _write_pair(profile, "f_B3_B4", _resolved_unknown(), journal=rows, sidecar=_sidecar(last_at + 1.0))
    verdict = _verdict(tmp_path, [profile])

    assert verdict["status"] == "undetermined", verdict
    assert f"pool P: pair {KEY_2}: pre unobserved ({reason})" in verdict["undetermined"]
    assert verdict["violations"] == []


def test_a_journal_row_without_a_finite_time_after_the_trip_is_not_measured(tmp_path):
    profile = _tree(tmp_path)
    _normal(profile)
    rows, last_at = _cut_rows(origin_at=20.0, overrun=1.0, emit=30.0)
    rows[3]["t_monotonic"] = float("nan")                                 # the last event's time
    _write_pair(profile, "f_B3_B4", _resolved_unknown(), journal=rows, sidecar=_sidecar(last_at + 1.0))
    verdict = _verdict(tmp_path, [profile])

    assert verdict["status"] == "undetermined", verdict
    assert verdict["undetermined"] == [
        f"pool P: pair {KEY_2}: cannot tell whether the deadline cut it "
        "(journal incomplete: field_errors=1)"
    ]


def test_an_overrun_below_the_start_refusal_reserve_is_inconsistent(tmp_path):
    """The deadline refuses to start a sub-operation at most 1.5 s early; 30 s early
    contradicts the deadline's own rule."""

    profile = _tree(tmp_path)
    _normal(profile)
    rows, last_at = _cut_rows(overrun=-30.0)
    _write_pair(profile, "f_B3_B4", _resolved_unknown(), journal=rows, sidecar=_sidecar(last_at + 1.0))
    verdict = _verdict(tmp_path, [profile])

    assert verdict["status"] == "undetermined", verdict
    assert verdict["undetermined"] == [
        f"pool P: pair {KEY_2}: overrun -30s is earlier than the deadline under evaluation may "
        "refuse a start (1.5s before it)"
    ]


# --------------------------------------------------------------------------
# 3. facts recorded twice must agree
# --------------------------------------------------------------------------


def test_a_manifest_deadline_the_trips_contradict_is_not_accepted(tmp_path):
    """The manifest claims 120 s (>= the profile's 100 s, so P), the trip shows 50 s."""

    profile = _tree(tmp_path, deadline="120")
    rows, last_at = _cut_rows(budget=120.0)
    _write_pair(profile, "f_B1_B2", _resolved_unknown(), journal=rows, sidecar=_sidecar(last_at + 1.0))
    short, short_last = _cut_rows(budget=50.0)
    _write_pair(profile, "f_B3_B4", _resolved_unknown(), journal=short,
                sidecar=_sidecar(short_last + 1.0))
    verdict = _verdict(tmp_path, [profile])

    assert verdict["status"] == "undetermined", verdict
    assert (f"pool P: run {profile}: analysis deadline disagrees between sources "
            "(run_manifest analysis_timeout=120, deadline_tripped budget_seconds=50,120)"
            ) in verdict["undetermined"]


def test_a_manifest_process_timeout_the_supervisor_contradicts_is_not_accepted(tmp_path):
    profile = _tree(tmp_path)
    rows, last_at = _cut_rows()
    sidecar = _sidecar(last_at + 1.0)
    sidecar["timeout_seconds"] = 600.0
    sidecar["deadline_monotonic"] = sidecar["deadline_monotonic"] + 360.0
    sidecar["cancel_linearized_offset_seconds"] -= 360.0
    _write_pair(profile, "f_B1_B2", _resolved_unknown(), journal=rows, sidecar=sidecar)
    verdict = _verdict(tmp_path, [profile])

    assert verdict["status"] == "undetermined", verdict
    assert (f"pool P: run {profile}: process timeout disagrees between sources "
            "(run_manifest pair_process_timeout_seconds=240, stack-dump sidecar timeout_seconds=600)"
            ) in verdict["undetermined"]


# --------------------------------------------------------------------------
# 4. an outcome outside the five-value contract is not a resolved pair
# --------------------------------------------------------------------------


@pytest.mark.parametrize("outcome", ["MAYBE", "equivalent", "PASS"])
def test_an_unknown_canonical_outcome_is_not_a_resolved_pair(tmp_path, outcome):
    profile = _tree(tmp_path)
    _normal(profile)
    _write_pair(profile, "f_B3_B4", {"canonical_outcome": outcome},
                journal=[_row(1, "note", 0.0, payload={"note": "pair_journal_opened"})],
                sidecar=_sidecar(30.0))
    verdict = _verdict(tmp_path, [profile])

    assert verdict["status"] == "undetermined", verdict
    assert verdict["undetermined"] == [f"pool P: pair {KEY_2}: termination evidence invalid"]
