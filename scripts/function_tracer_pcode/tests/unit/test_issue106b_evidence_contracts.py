# -*- coding: utf-8 -*-
"""Issue #106 PR-106-B review 3: the evidence contracts of the margin, from files to the verdict.

The margin's verdict may only rest on evidence that is complete, valid and
consistent.  Each contract has one owner:

* completeness of a journal: `core.stage_journal_reader.JournalRead.incomplete_reasons`
  (diagnostic readers stay tolerant; the margin does not read "no trip" out of
  an incomplete journal);
* validity of numbers: a recorded number is a value only when it is finite and
  in range (`deadline_margin_summary` observes; the records refuse non-finite
  values; the profile's numbers share `core.deadline.parse_budget_seconds`);
* consistency of facts recorded twice: `deadline_margin_summary.observe_run`
  reconciles the manifest with the trips and the supervisor's sidecar;
* termination: the five-value `authority.contracts.Outcome`.

Every case writes the files a runner writes and reads the verdict the command
line prints.  Expectations are literal.
"""
from __future__ import annotations

import dataclasses
import json
from pathlib import Path

import pytest

from scripts.function_tracer_pcode.core import stage_journal_reader as reader
from scripts.function_tracer_pcode.reporting import deadline_margin_acceptance as acceptance
from scripts.function_tracer_pcode.reporting import deadline_margin_summary as margin
from scripts.function_tracer_pcode.tests.unit.test_issue106b_margin_acceptance import (
    COMMIT,
    KEY,
    KEY_2,
    _cut,
    _finished,
    _scenario,
    _tree,
    _verdict,
)
from scripts.function_tracer_pcode.tests.unit.test_issue106b_review1_regressions import (
    _resolved_unknown,
    _row,
    _sidecar,
    _trip,
    _write_pair,
)


def _journal(root: Path, stem: str) -> Path:
    return root / "REVE" / "sample" / "Eq" / "new" / "f" / f"{stem}.stage.jsonl"


def _lines(rows) -> str:
    return "".join(json.dumps(row) + "\n" for row in rows)


def _cut_rows():
    trip_at = 121.0
    return [
        _row(1, "note", 0.0, payload={"note": "pair_journal_opened"}),
        _trip(2, trip_at, origin_at=20.0),
        _row(3, "stage_start", trip_at, "result_emit"),
        _row(4, "stage_end", trip_at + 1.5, "result_emit", 1.5),
    ]


# --------------------------------------------------------------------------
# the reader reports every loss; diagnostic readers stay tolerant
# --------------------------------------------------------------------------

_LOSS_FIELDS = {"truncated", "partial_final_line", "malformed_lines", "field_errors"}
_STRUCTURE_FIELDS = {"path", "rows", "segments", "seq_rollbacks", "opened_notes",
                     "unavailable_reason"}


def test_every_journal_read_field_is_classified_as_loss_or_structure():
    """A new field on `JournalRead` must be classified here: a loss field that
    `incomplete_reasons` does not report would let a lost trip read as "no trip"."""

    names = {item.name for item in dataclasses.fields(reader.JournalRead)}
    assert names == _LOSS_FIELDS | _STRUCTURE_FIELDS
    for name in sorted(_LOSS_FIELDS):
        value = True if name in ("truncated", "partial_final_line") else 2
        read = reader.JournalRead(path="x", **{name: value})
        assert read.incomplete_reasons, name
    assert reader.JournalRead(path="x").incomplete_reasons == ()


@pytest.mark.parametrize("text, reasons", [
    (_lines(_cut_rows()), ()),
    (_lines(_cut_rows())[:-1], ("partial_final_line",)),
    ("{garbled\n" + _lines(_cut_rows()), ("malformed_lines=1",)),
    (_lines([dict(_cut_rows()[1], t_monotonic=float("nan"))]), ("field_errors=1",)),
    (_lines([dict(_cut_rows()[1], payload=["deadline_tripped"])]), ("field_errors=1",)),
    (_lines([dict(_cut_rows()[1], seq="2", pid=7.5)]), ("field_errors=2",)),
])
def test_the_reader_reports_what_it_lost(tmp_path, text, reasons):
    path = tmp_path / "j.stage.jsonl"
    path.write_text(text, encoding="utf-8")
    read = reader.read_stage_journal(path, max_bytes=reader.SUMMARY_READ_LIMIT_BYTES)

    assert read.incomplete_reasons == reasons
    assert read.state()["field_errors"] == (int(reasons[0].split("=")[1])
                                            if reasons and reasons[0].startswith("field") else 0)


def test_a_non_finite_time_is_not_a_time(tmp_path):
    path = tmp_path / "j.stage.jsonl"
    path.write_text(_lines([dict(_cut_rows()[1], t_monotonic=float("inf"))]), encoding="utf-8")
    (row,) = reader.read_stage_journal(path).rows

    assert row.t_monotonic is None


def test_diagnostic_readers_still_use_a_journal_cut_off_by_a_kill(tmp_path):
    """The supervisor and the hotspot summary keep reading a killed child's journal;
    only the margin refuses to conclude "no trip" from it."""

    path = tmp_path / "j.stage.jsonl"
    path.write_text(_lines(_cut_rows()[:3]) + json.dumps(_cut_rows()[3]), encoding="utf-8")
    read = reader.read_stage_journal(path, max_bytes=reader.SUMMARY_READ_LIMIT_BYTES)
    segment, reason = reader.select_current_segment(read)

    assert reason is None and len(segment.rows) == 3
    assert read.incomplete_reasons == ("partial_final_line",)


# --------------------------------------------------------------------------
# an incomplete journal is "cannot tell", in every pool
# --------------------------------------------------------------------------


@pytest.mark.parametrize("pool", ["P", "L", "F"])
@pytest.mark.parametrize("text, reason", [
    (_lines(_cut_rows()[:1]) + json.dumps(_cut_rows()[1]), "partial_final_line"),
    (_lines(_cut_rows()[:1]) + "{garbled\n", "malformed_lines=1"),
    (_lines(_cut_rows()[:1] + [dict(_cut_rows()[1], payload="x")]), "field_errors=1"),
])
def test_an_incomplete_journal_is_undetermined_in_every_pool(tmp_path, pool, text, reason):
    root, pools = _scenario(tmp_path, pool)
    if pool != "P":
        _cut(root)
    _write_pair(root, "f_B3_B4", _resolved_unknown(), journal=[], sidecar=_sidecar(30.0))
    _journal(root, "f_B3_B4").write_text(text, encoding="utf-8")
    verdict = _verdict(tmp_path, **pools)

    assert verdict["status"] == "undetermined", verdict
    assert verdict["undetermined"] == [
        f"pool {pool}: pair {KEY_2}: cannot tell whether the deadline cut it "
        f"(journal incomplete: {reason})"
    ]


def test_a_complete_journal_without_a_trip_is_a_pair_that_finished(tmp_path):
    profile = _tree(tmp_path, "profile")
    _cut(profile)
    _finished(profile, "f_B3_B4", {"canonical_outcome": "EQUIVALENT"})
    verdict = _verdict(tmp_path, [profile])

    assert verdict["status"] == "holds", verdict


# --------------------------------------------------------------------------
# a number is a value only when it is finite and in range
# --------------------------------------------------------------------------


@pytest.mark.parametrize("key, value, interval, reason", [
    ("deadline_monotonic", float("nan"), "pre", "sidecar deadline_monotonic is not a finite number"),
    ("timeout_seconds", float("inf"), "pre", "sidecar timeout_seconds is not a finite number"),
    ("timeout_seconds", -240.0, "pre", "sidecar timeout_seconds is not positive"),
    ("cancel_linearized_offset_seconds", float("nan"), "tail",
     "sidecar cancel_linearized_offset_seconds is not a finite number"),
    ("lead_seconds", float("nan"), "lead", "sidecar lead_seconds is not a finite number"),
])
def test_a_sidecar_number_that_is_not_finite_or_in_range_is_unobserved(
    tmp_path, key, value, interval, reason,
):
    profile = _tree(tmp_path, "profile")
    _cut(profile)
    rows = _cut_rows()
    sidecar = _sidecar(123.5)
    sidecar[key] = value                                                  # JSON NaN / Infinity
    _write_pair(profile, "f_B3_B4", _resolved_unknown(), journal=rows, sidecar=sidecar)
    verdict = _verdict(tmp_path, [profile])

    assert verdict["status"] == "undetermined", verdict
    assert f"pool P: pair {KEY_2}: {interval} unobserved ({reason})" in verdict["undetermined"]
    assert verdict["violations"] == []


@pytest.mark.parametrize("overrun, expected", [(-1.5, "holds"), (-1.51, "undetermined")])
def test_the_negative_overrun_boundary_is_the_deadlines_start_refusal_reserve(
    tmp_path, overrun, expected,
):
    profile = _tree(tmp_path, "profile")
    _cut(profile, overrun=overrun)
    verdict = _verdict(tmp_path, [profile])

    assert verdict["status"] == expected, verdict


def test_an_analysis_that_started_before_the_process_origin_is_inconsistent(tmp_path):
    profile = _tree(tmp_path, "profile")
    _cut(profile)
    _cut(profile, "f_B3_B4", origin_at=-5.0)                              # pre would be -5 s
    verdict = _verdict(tmp_path, [profile])

    assert verdict["status"] == "undetermined", verdict
    assert (f"pool P: pair {KEY_2}: pre unobserved (the analysis started 5s before the "
            "process deadline's origin)") in verdict["undetermined"]


def test_a_child_exit_before_the_last_journal_event_is_inconsistent(tmp_path):
    profile = _tree(tmp_path, "profile")
    _cut(profile)
    _cut(profile, "f_B3_B4", tail=-2.0)
    verdict = _verdict(tmp_path, [profile])

    assert verdict["status"] == "undetermined", verdict
    assert (f"pool P: pair {KEY_2}: tail unobserved (the child exit was observed 2s before the "
            "last journal event)") in verdict["undetermined"]


def test_the_records_refuse_non_finite_numbers():
    with pytest.raises(ValueError):
        acceptance.MarginProfile(name="p", deadline_seconds=100.0, margin_seconds=float("nan"),
                                 pair_process_timeout_seconds=240.0)
    with pytest.raises(ValueError):
        acceptance.MarginProfile(name="p", deadline_seconds=-1.0, margin_seconds=10.0,
                                 pair_process_timeout_seconds=240.0)
    with pytest.raises(ValueError):
        margin.PairObservation(key="k", outcome="UNKNOWN", termination="resolved",
                               timeout_kind=None, cut=True, values={"pre": float("inf")})
    with pytest.raises(ValueError):
        margin.PairObservation(key="k", outcome="UNKNOWN", termination="resolved",
                               timeout_kind=None, cut=None)                 # no reason


# --------------------------------------------------------------------------
# facts recorded twice must agree (never overwritten by one source)
# --------------------------------------------------------------------------


def _manifest(root: Path, **fields) -> None:
    text = (root / "run_manifest.txt").read_text(encoding="utf-8")
    for key, value in fields.items():
        text += f"{key}={value}\n"
    (root / "run_manifest.txt").write_text(text, encoding="utf-8")


@pytest.mark.parametrize("pool", ["P", "L", "F"])
def test_a_lead_the_supervisor_contradicts_is_undetermined_in_every_pool(tmp_path, pool):
    root, pools = _scenario(tmp_path, pool)
    if pool != "P":
        _cut(root)
    _manifest(root, pair_stack_dump_lead="5s")
    verdict = _verdict(tmp_path, **pools)

    assert verdict["status"] == "undetermined", verdict
    assert verdict["undetermined"] == [
        f"pool {pool}: run {root}: stack-dump lead disagrees between sources "
        "(run_manifest pair_stack_dump_lead=5, stack-dump sidecar lead_seconds=2)"
    ]


def test_a_run_recorded_as_off_that_tripped_is_undetermined(tmp_path):
    profile = _tree(tmp_path, "profile")
    _cut(profile)
    other = _tree(tmp_path, "other", deadline="0")
    _cut(other)
    verdict = _verdict(tmp_path, [profile], pre=[other])

    assert verdict["status"] == "undetermined", verdict
    assert verdict["undetermined"] == [
        f"pool F: run {other}: analysis deadline disagrees between sources (run_manifest "
        "analysis_timeout=0 (off), deadline_tripped budget_seconds=100)",
        f"pool F: run {other}: ran without the analysis deadline",
    ]


@pytest.mark.parametrize("text", ["nan", "inf", "-100", "100m"])
def test_a_manifest_deadline_that_is_not_a_number_of_seconds_is_undetermined(tmp_path, text):
    profile = _tree(tmp_path, "profile")
    _cut(profile)
    manifest = (profile / "run_manifest.txt").read_text(encoding="utf-8")
    (profile / "run_manifest.txt").write_text(
        manifest.replace("analysis_timeout=100", f"analysis_timeout={text}"), encoding="utf-8")
    verdict = _verdict(tmp_path, [profile])

    assert verdict["status"] == "undetermined", verdict
    assert verdict["undetermined"] == [
        f"pool P: run {profile}: run_manifest analysis_timeout={text!r} is not a valid number "
        "of seconds"
    ]


def test_trips_that_disagree_without_a_manifest_value_are_undetermined(tmp_path):
    profile = _tree(tmp_path, "profile")
    _cut(profile)
    manifest = (profile / "run_manifest.txt").read_text(encoding="utf-8")
    (profile / "run_manifest.txt").write_text(
        manifest.replace("analysis_timeout=100\n", ""), encoding="utf-8")
    rows = _cut_rows()
    rows[1]["payload"]["budget_seconds"] = 101.0
    rows[1]["payload"]["elapsed_seconds"] = 101.0
    _write_pair(profile, "f_B3_B4", _resolved_unknown(), journal=rows, sidecar=_sidecar(123.5))
    verdict = _verdict(tmp_path, [profile])

    assert verdict["status"] == "undetermined", verdict
    assert verdict["undetermined"] == [
        f"pool P: run {profile}: analysis deadline disagrees between sources "
        "(deadline_tripped budget_seconds=100,101)"
    ]


# --------------------------------------------------------------------------
# termination: only the five outcomes are terminations
# --------------------------------------------------------------------------


@pytest.mark.parametrize("outcome", ["EQUIVALENT", "NOT_EQ", "UNKNOWN", "ERROR"])
def test_the_four_resolved_outcomes_are_resolved(tmp_path, outcome):
    profile = _tree(tmp_path, "profile")
    _cut(profile)
    _finished(profile, "f_B3_B4", {"canonical_outcome": outcome})
    verdict = _verdict(tmp_path, [profile])

    assert verdict["status"] == "holds", verdict


@pytest.mark.parametrize("pool, expected", [
    ("P", "undetermined"), ("L", "undetermined"), ("F", "holds"),
])
def test_an_outcome_outside_the_contract_is_invalid_termination(tmp_path, pool, expected):
    root, pools = _scenario(tmp_path, pool)
    if pool != "P":
        _cut(root)
    _finished(root, "f_B3_B4", {"canonical_outcome": "Timeout"})          # not the enum's spelling
    verdict = _verdict(tmp_path, **pools)

    assert verdict["status"] == expected, verdict
    if expected == "undetermined":
        assert verdict["undetermined"] == [
            f"pool {pool}: pair {KEY_2}: termination evidence invalid"
        ]


def test_the_termination_vocabulary_is_the_authority_outcome():
    from scripts.function_tracer_pcode.authority.contracts import Outcome

    assert {margin.termination_of(item.value, None) for item in Outcome} == {
        "resolved", "timeout_unclassified",
    }
    assert margin.termination_of("MISSING", None) == "termination_invalid"
    assert margin.termination_of("INVALID", None) == "termination_invalid"


def test_the_start_refusal_bound_follows_every_time_unit():
    """The bound comes from the deadline's own rounding rule: every unit has a length,
    and a start is refused at most the margin plus the coarsest unit early."""

    from scripts.function_tracer_pcode.core import deadline

    assert set(deadline.UNIT_SECONDS) == set(deadline.TimeUnit)
    assert deadline.earliest_start_refusal_seconds() == 1.5
    assert deadline.earliest_start_refusal_seconds(0.25) == 1.25
    # the rounding rule itself: a seconds API with 0.999 s left before the margin is not started
    assert deadline.bounded_timeout(10.0, 100.999, deadline.TimeUnit.SECONDS, now=100.0) is None
    assert deadline.bounded_timeout(10.0, 101.0, deadline.TimeUnit.SECONDS, now=100.0) == 1


@pytest.mark.parametrize("where, value, interval, reason", [
    ("elapsed_seconds", -5.0, "pre", "deadline_tripped elapsed_seconds is negative"),
    ("lead_seconds", -1.0, "lead", "sidecar lead_seconds is negative"),
])
def test_a_negative_elapsed_or_lead_is_unobserved(tmp_path, where, value, interval, reason):
    profile = _tree(tmp_path, "profile")
    _cut(profile)
    rows = _cut_rows()
    sidecar = _sidecar(123.5)
    if where == "elapsed_seconds":
        rows[1]["payload"]["elapsed_seconds"] = value
    else:
        sidecar[where] = value
    _write_pair(profile, "f_B3_B4", _resolved_unknown(), journal=rows, sidecar=sidecar)
    verdict = _verdict(tmp_path, [profile])

    assert verdict["status"] == "undetermined", verdict
    assert f"pool P: pair {KEY_2}: {interval} unobserved ({reason})" in verdict["undetermined"]


def test_a_trip_without_a_time_is_not_measured(tmp_path):
    """``null`` is not a field error (the field may be absent), but a trip needs its time."""

    profile = _tree(tmp_path, "profile")
    _cut(profile)
    rows = _cut_rows()
    rows[1]["t_monotonic"] = None
    _write_pair(profile, "f_B3_B4", _resolved_unknown(), journal=rows, sidecar=_sidecar(123.5))
    verdict = _verdict(tmp_path, [profile])

    assert verdict["status"] == "undetermined", verdict
    assert (f"pool P: pair {KEY_2}: pre unobserved (deadline_tripped has no finite t_monotonic)"
            in verdict["undetermined"])


def test_a_row_without_a_time_after_the_trip_leaves_the_end_unknown(tmp_path):
    profile = _tree(tmp_path, "profile")
    _cut(profile)
    rows = _cut_rows()
    rows[3]["t_monotonic"] = None
    _write_pair(profile, "f_B3_B4", _resolved_unknown(), journal=rows, sidecar=_sidecar(123.5))
    verdict = _verdict(tmp_path, [profile])

    assert verdict["status"] == "undetermined", verdict
    assert verdict["undetermined"] == [
        f"pool P: pair {KEY_2}: post_trip unobserved (1 journal row(s) have no time)",
        f"pool P: pair {KEY_2}: tail unobserved (1 journal row(s) have no time)",
    ]


def test_the_start_refusal_bound_is_not_applied_to_another_machinery(tmp_path):
    """Pool F holds runs of other code (only ``pre`` is used); its trips follow that code's rule."""

    profile = _tree(tmp_path, "profile")
    _cut(profile)
    other = _tree(tmp_path, "other", commit="d" * 40, dirty="1")
    _cut(other, overrun=-20.0)
    verdict = _verdict(tmp_path, [profile], pre=[other])

    assert verdict["status"] == "holds", verdict


def test_a_sum_that_overflows_is_not_a_requirement():
    def run(pool_pairs):
        facts = margin.RunFacts(
            root="r", deadline_seconds=100.0, deadline_off=False, deadline_source="m",
            pair_process_timeout_seconds=240.0, stack_dump_lead_seconds=2.0, parallel_jobs=1,
            git_commit=COMMIT, git_dirty=False, samples=frozenset({"REVE/sample/Eq/new"}))
        return margin.RunObservation(facts=facts, pairs=tuple(pool_pairs))

    huge = margin.PairObservation(
        key=KEY, outcome="UNKNOWN", termination="resolved", timeout_kind=None, cut=True,
        values={"pre": 1e308, "overrun": 1e308, "post_trip": 1.0, "tail": 1.0},
        lead_seconds=2.0, needed=None, budget_seconds=100.0, process_timeout_seconds=240.0)
    profile = acceptance.MarginProfile(
        name="p", deadline_seconds=100.0, margin_seconds=140.0, pair_process_timeout_seconds=240.0,
        machinery_commits=frozenset({COMMIT}))
    verdict = acceptance.evaluate_margin(profile, {"P": [run([huge])]})

    assert verdict.status == "undetermined"
    assert verdict.required_margin_seconds is None
    assert "required margin inf is not a finite number" in verdict.undetermined
