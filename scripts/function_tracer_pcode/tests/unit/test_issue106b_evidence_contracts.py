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
    _deadline_log,
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

_LOSS_FIELDS = {"truncated", "partial_final_line", "malformed_lines", "field_errors", "seq_gaps"}
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
    (_lines([dict(_cut_rows()[1], seq=1, t_monotonic=float("nan"))]), ("field_errors=1",)),
    (_lines([dict(_cut_rows()[1], seq=1, payload=["deadline_tripped"])]), ("field_errors=1",)),
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


_INCOMPLETE = [
    (_lines(_cut_rows()[:1]) + json.dumps(_cut_rows()[1]), "partial_final_line"),
    (_lines(_cut_rows()[:1]) + "{garbled\n", "malformed_lines=1"),
    (_lines(_cut_rows()[:1] + [dict(_cut_rows()[1], payload="x")]),
     "field_errors in 1 row(s): payload"),
]


@pytest.mark.parametrize("pool", ["P", "L", "F"])
@pytest.mark.parametrize("text, reason", _INCOMPLETE)
def test_an_incomplete_journal_without_a_result_is_undetermined_in_every_pool(
    tmp_path, pool, text, reason,
):
    """No result JSON (the child printed none) and a journal with a loss: nothing says
    whether the deadline cut the pair."""

    root, pools = _scenario(tmp_path, pool)
    if pool != "P":
        _cut(root)
    _write_pair(root, "f_B3_B4", _resolved_unknown(), journal=[], sidecar=_sidecar(30.0), log="")
    _journal(root, "f_B3_B4").write_text(text, encoding="utf-8")
    verdict = _verdict(tmp_path, **pools)

    assert verdict["status"] == "undetermined", verdict
    assert verdict["undetermined"] == [
        f"pool {pool}: pair {KEY_2}: cannot tell whether the deadline cut it "
        f"(journal incomplete: {reason}; no result records analysis_deadline)"
    ]


@pytest.mark.parametrize("pool", ["P", "L", "F"])
@pytest.mark.parametrize("text, reason", _INCOMPLETE)
def test_a_cut_pair_with_an_incomplete_journal_is_not_measured_in_every_pool(
    tmp_path, pool, text, reason,
):
    """The result says the deadline cut the pair; no interval is taken from a journal with a loss."""

    root, pools = _scenario(tmp_path, pool)
    if pool != "P":
        _cut(root)
    _write_pair(root, "f_B3_B4", _resolved_unknown(), journal=[], sidecar=_sidecar(30.0),
                log=_deadline_log(True))
    _journal(root, "f_B3_B4").write_text(text, encoding="utf-8")
    verdict = _verdict(tmp_path, **pools)

    intervals = {"P": ["pre", "overrun", "post_trip", "tail"],
                 "L": ["pre", "overrun"], "F": ["pre"]}[pool]
    assert verdict["status"] == "undetermined", verdict
    assert verdict["undetermined"] == [
        f"pool {pool}: pair {KEY_2}: {name} unobserved (journal incomplete: {reason})"
        for name in intervals
    ]


@pytest.mark.parametrize("text, reason", _INCOMPLETE)
def test_a_result_that_did_not_trip_needs_nothing_from_the_journal(tmp_path, text, reason):
    """The deadline's own final record says it never tripped: the pair was not cut, whatever
    the journal lost (no interval is read from it)."""

    profile = _tree(tmp_path, "profile")
    _cut(profile)
    _write_pair(profile, "f_B3_B4", _resolved_unknown(), journal=[], sidecar=_sidecar(30.0),
                log=_deadline_log(False))
    _journal(profile, "f_B3_B4").write_text(text, encoding="utf-8")
    verdict = _verdict(tmp_path, [profile])

    assert verdict["status"] == "holds", verdict


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
    _write_pair(profile, "f_B3_B4", _resolved_unknown(), journal=rows, sidecar=_sidecar(123.5),
                log=_deadline_log(True, budget=101.0))
    verdict = _verdict(tmp_path, [profile])

    assert verdict["status"] == "undetermined", verdict
    assert verdict["undetermined"] == [
        f"pool P: run {profile}: analysis deadline disagrees between sources "
        "(deadline_tripped budget_seconds=100,101, result analysis_deadline budget_seconds=100,101)"
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


@pytest.mark.parametrize("index", [1, 3])
def test_a_row_without_a_time_is_a_journal_loss(tmp_path, index):
    """``t_monotonic`` is a required field: a row without it (the trip, or a row after it)
    is a loss of the journal, so no interval is read from it."""

    profile = _tree(tmp_path, "profile")
    _cut(profile)
    rows = _cut_rows()
    rows[index]["t_monotonic"] = None
    _write_pair(profile, "f_B3_B4", _resolved_unknown(), journal=rows, sidecar=_sidecar(123.5))
    verdict = _verdict(tmp_path, [profile])

    assert verdict["status"] == "undetermined", verdict
    assert verdict["undetermined"] == [
        f"pool P: pair {KEY_2}: {name} unobserved "
        "(journal incomplete: field_errors in 1 row(s): t_monotonic)"
        for name in ("pre", "overrun", "post_trip", "tail")
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


# --------------------------------------------------------------------------
# review 4: the row contract and the end of the journal (`core.stage_journal_reader`)
# --------------------------------------------------------------------------


def _written_journal(path: Path) -> list:
    """A journal the production writer wrote and sealed, as rows."""

    from scripts.function_tracer_pcode.core import stage_journal

    journal = stage_journal.StageJournal(path)
    journal.append("note", payload={"note": "pair_journal_opened"})
    journal.append("stage_start", stage="check")
    journal.append("note", payload={"note": "deadline_tripped", "stage": "solver",
                                    "budget_seconds": 100.0, "elapsed_seconds": 101.0})
    journal.append("stage_end", stage="check", seconds=1.0)
    journal.append("stage_end", stage="result_emit")                    # seconds: null
    assert journal.seal() == 6
    return [json.loads(line) for line in path.read_text(encoding="utf-8").splitlines()]


def _segment_after(tmp_path: Path, change):
    path = tmp_path / "j.stage.jsonl"
    rows = _written_journal(path)
    rows = change(rows) or rows
    path.write_text(_lines(rows), encoding="utf-8")
    try:
        read = reader.read_stage_journal(path, max_bytes=reader.SUMMARY_READ_LIMIT_BYTES)
    except Exception as exc:                                    # the reader never raises (contract)
        pytest.fail(f"the journal reader raised {type(exc).__name__}: {exc}")
    (segment,) = read.segments
    return segment


def _set(index, **fields):
    def change(rows):
        rows[index].update(fields)
    return change


def _set_payload(index, **fields):
    def change(rows):
        rows[index]["payload"].update(fields)
    return change


def test_the_sealed_journal_is_complete_to_its_end(tmp_path):
    segment = _segment_after(tmp_path, lambda rows: None)

    assert segment.losses == () and segment.end_attested is True
    assert reader.end_attestation_problem(segment) is None
    assert [row.seq for row in segment.rows] == [1, 2, 3, 4, 5, 6]


@pytest.mark.parametrize("change, losses", [
    (_set(1, stage=None), ("field_errors in 1 row(s): stage",)),             # stage_start needs it
    (_set(3, seconds=-1.0), ("field_errors in 1 row(s): seconds",)),
    (_set(3, seconds="1"), ("field_errors in 1 row(s): seconds",)),
    (_set(1, event="stage_begin"), ("field_errors in 1 row(s): event",)),
    (_set(0, payload={"journal_path": "x"}), ("field_errors in 1 row(s): payload.note",)),
    (_set(1, payload=None), ("field_errors in 1 row(s): payload",)),
    (_set(1, t_epoch=10 ** 400), ("field_errors in 1 row(s): t_epoch",)),
    (_set(1, pid=None), ("field_errors in 1 row(s): pid",)),
    (_set(1, seq=True), ("seq_gaps=1", "field_errors in 1 row(s): seq")),
    (_set_payload(5, last_seq="5"), ("field_errors in 1 row(s): payload.last_seq",)),
    (_set_payload(5, write_failures=-1), ("field_errors in 1 row(s): payload.write_failures",)),
    (lambda rows: rows[1:], ("first seq is 2, not 1",)),                    # the head was lost
    (lambda rows: rows[:2] + rows[3:], ("seq_gaps=1",)),                    # a row was lost
])
def test_a_row_outside_the_contract_is_a_loss_of_its_execution(tmp_path, change, losses):
    segment = _segment_after(tmp_path, change)

    assert segment.losses == losses
    assert segment.end_attested is False


@pytest.mark.parametrize("change", [
    _set(0, stage=None),                                                    # a note: may be null
    _set(4, seconds=None),                                                  # seconds: may be null
    _set_payload(2, extra=[1, 2]),                                          # payload: open object
])
def test_a_nullable_or_open_field_is_not_a_loss(tmp_path, change):
    segment = _segment_after(tmp_path, change)

    assert segment.losses == () and segment.end_attested is True


@pytest.mark.parametrize("change, problem", [
    (lambda rows: rows[:-1], "no journal_end row (the end is not attested)"),
    (_set_payload(5, last_seq=4), "journal_end last_seq=4 does not precede its own seq 6"),
    (_set_payload(5, write_failures=2), "journal_end reports 2 write failure(s)"),
    (lambda rows: rows + [dict(rows[4], seq=7)], "journal_end is not the last row of its execution"),
])
def test_an_end_the_seal_does_not_account_for_is_not_attested(tmp_path, change, problem):
    segment = _segment_after(tmp_path, change)

    assert segment.losses == ()
    assert segment.end_attested is False
    assert reader.end_attestation_problem(segment) == problem


def test_a_write_the_writer_could_not_make_leaves_a_gap_and_is_counted_in_the_seal(tmp_path):
    from scripts.function_tracer_pcode.core import stage_journal

    class _FailingOnce:
        def __init__(self, inner):
            self.inner, self.calls = inner, 0

        def write(self, text):
            self.calls += 1
            if self.calls == 2:
                raise OSError(28, "No space left on device")
            return self.inner.write(text)

        def flush(self):
            self.inner.flush()

        def close(self):
            self.inner.close()

    path = tmp_path / "j.stage.jsonl"
    journal = stage_journal.StageJournal(path)
    journal._handle = _FailingOnce(journal._handle)
    for _ in range(3):
        journal.append("note", payload={"note": "x"})
    journal.seal()
    read = reader.read_stage_journal(path)
    (segment,) = read.segments

    assert [row.seq for row in segment.rows] == [1, 3, 4]
    assert segment.rows[-1].payload == {"last_seq": 3, "write_failures": 1}
    assert segment.losses == ("seq_gaps=1",)
    assert read.incomplete_reasons == ("seq_gaps=1",)
    assert reader.select_verified_segment(read) == (None, "journal incomplete: seq_gaps=1")
    # the diagnostic readers keep reading it
    assert reader.select_current_segment(read) == (segment, None)


def test_rows_after_a_seal_are_not_written_and_not_counted(tmp_path):
    from scripts.function_tracer_pcode.core import stage_journal

    path = tmp_path / "j.stage.jsonl"
    journal = stage_journal.StageJournal(path)
    journal.append("note", payload={"note": "x"})
    journal.seal()
    assert journal.append("note", payload={"note": "late"}) is None
    assert journal.seal() is None
    (segment,) = reader.read_stage_journal(path).segments

    assert journal.write_failures == 0
    assert segment.end_attested is True and len(segment.rows) == 2


# --------------------------------------------------------------------------
# review 4: the two sources of "the deadline cut it" must agree
# --------------------------------------------------------------------------


def test_a_journal_trip_the_result_denies_is_undetermined(tmp_path):
    profile = _tree(tmp_path, "profile")
    _cut(profile)
    _write_pair(profile, "f_B3_B4", _resolved_unknown(), journal=_cut_rows(),
                sidecar=_sidecar(123.5), log=_deadline_log(False))
    verdict = _verdict(tmp_path, [profile])

    assert verdict["status"] == "undetermined", verdict
    assert verdict["undetermined"] == [
        f"pool P: pair {KEY_2}: cannot tell whether the deadline cut it (the journal records "
        "deadline_tripped but the result's analysis_deadline does not)"
    ]


def test_a_result_trip_the_attested_journal_denies_is_undetermined(tmp_path):
    profile = _tree(tmp_path, "profile")
    _cut(profile)
    rows = [row for row in _cut_rows() if row["payload"].get("note") != "deadline_tripped"]
    for seq, row in enumerate(rows, start=1):
        row["seq"] = seq
    _write_pair(profile, "f_B3_B4", _resolved_unknown(), journal=rows, sidecar=_sidecar(123.5),
                log=_deadline_log(True))
    verdict = _verdict(tmp_path, [profile])

    assert verdict["status"] == "undetermined", verdict
    assert verdict["undetermined"] == [
        f"pool P: pair {KEY_2}: cannot tell whether the deadline cut it (the result's "
        "analysis_deadline records a trip the attested journal does not)"
    ]


def test_a_result_trip_with_an_unattested_journal_without_it_is_a_cut_pair_unmeasured(tmp_path):
    profile = _tree(tmp_path, "profile")
    _cut(profile)
    rows = [_row(1, "note", 0.0, payload={"note": "pair_journal_opened"})]
    _write_pair(profile, "f_B3_B4", _resolved_unknown(), journal=rows, sidecar=_sidecar(123.5),
                log=_deadline_log(True), sealed=False)
    verdict = _verdict(tmp_path, [profile])

    assert verdict["status"] == "undetermined", verdict
    assert verdict["undetermined"] == [
        f"pool P: pair {KEY_2}: {name} unobserved (the journal has no deadline_tripped row "
        "(no journal_end row (the end is not attested)))"
        for name in ("pre", "overrun", "post_trip", "tail")
    ]


def test_a_journal_with_two_trips_is_not_read(tmp_path):
    profile = _tree(tmp_path, "profile")
    _cut(profile)
    rows = _cut_rows()
    rows.insert(2, dict(rows[1]))
    for seq, row in enumerate(rows, start=1):
        row["seq"] = seq
    _write_pair(profile, "f_B3_B4", _resolved_unknown(), journal=rows, sidecar=_sidecar(123.5))
    verdict = _verdict(tmp_path, [profile])

    assert verdict["status"] == "undetermined", verdict
    assert verdict["undetermined"] == [
        f"pool P: pair {KEY_2}: {name} unobserved (journal records deadline_tripped 2 times "
        "(the deadline writes it once))"
        for name in ("pre", "overrun", "post_trip", "tail")
    ]


@pytest.mark.parametrize("record, reason", [
    ("[]", "result analysis_deadline is not an object"),
    ('{"tripped": "yes", "budget_seconds": 100.0, "trip_stage": "solver"}',
     "result analysis_deadline tripped is not a boolean"),
    ('{"tripped": true, "budget_seconds": 100.0, "trip_stage": null}',
     "result analysis_deadline trip_stage does not match tripped"),
    ('{"tripped": false, "budget_seconds": 100.0, "trip_stage": "solver"}',
     "result analysis_deadline trip_stage does not match tripped"),
    ('{"tripped": true, "budget_seconds": NaN, "trip_stage": "solver"}',
     "result analysis_deadline budget_seconds is not a finite number"),
    ('{"tripped": true, "trip_stage": "solver"}', "result analysis_deadline budget_seconds is missing"),
])
def test_a_result_record_outside_its_contract_is_not_evidence_of_the_cut(tmp_path, record, reason):
    profile = _tree(tmp_path, "profile")
    _cut(profile)
    log = ("=== EQUIVALENCE_RESULT_JSON_BEGIN ===\n"
           '{"diagnostics": {"analysis_deadline": ' + record + "}}\n"
           "=== EQUIVALENCE_RESULT_JSON_END ===\n")
    _write_pair(profile, "f_B3_B4", _resolved_unknown(), journal=_cut_rows(),
                sidecar=_sidecar(123.5), log=log)
    verdict = _verdict(tmp_path, [profile])

    assert verdict["status"] == "undetermined", verdict
    assert verdict["undetermined"] == [
        f"pool P: pair {KEY_2}: cannot tell whether the deadline cut it ({reason})"
    ]


def test_a_needed_that_overflows_is_undetermined_not_a_crash(tmp_path):
    """Every interval is a finite double, but the time charged (exit - origin) is not."""

    profile = _tree(tmp_path, "profile")
    _cut(profile)
    sidecar = _sidecar(123.5)
    sidecar.update(deadline_monotonic=0.0, timeout_seconds=1e308,
                   cancel_linearized_offset_seconds=1e308)
    _write_pair(profile, "f_B3_B4", _resolved_unknown(), journal=_cut_rows(), sidecar=sidecar)
    (pair,) = [p for p in margin.observe_run(profile).pairs if p.key == KEY_2]
    verdict = _verdict(tmp_path, [profile])

    assert pair.missing == {
        "needed": "needed is not a finite number (the recorded values it is derived from are "
                  "out of range)"}
    assert (f"pool P: pair {KEY_2}: needed unobserved (needed is not a finite number (the "
            "recorded values it is derived from are out of range))") in verdict["undetermined"]
    assert verdict["status"] == "undetermined", verdict


@pytest.mark.parametrize("text", ["²", "1" * 5000, "-4", "4.0"])
def test_a_manifest_count_that_is_not_a_count_is_unknown_not_a_crash(tmp_path, text):
    profile = _tree(tmp_path, "profile")
    _cut(profile)
    manifest = (profile / "run_manifest.txt").read_text(encoding="utf-8")
    (profile / "run_manifest.txt").write_text(
        manifest.replace("parallel_jobs=4", f"parallel_jobs={text}"), encoding="utf-8")
    try:
        facts = margin.observe_run(profile).facts
    except Exception as exc:                        # an external record never raises (contract)
        pytest.fail(f"the margin command line raised {type(exc).__name__}: {exc}")

    assert facts.parallel_jobs is None
    assert _verdict(tmp_path, [profile])["status"] == "holds"


@pytest.mark.parametrize("stage", [None, "", 7])
def test_a_trip_note_without_its_stage_is_not_measured(tmp_path, stage):
    """The deadline writes the stage it tripped in; a note without it is not the deadline's note."""

    profile = _tree(tmp_path, "profile")
    _cut(profile)
    rows = _cut_rows()
    rows[1]["payload"]["stage"] = stage
    _write_pair(profile, "f_B3_B4", _resolved_unknown(), journal=rows, sidecar=_sidecar(123.5))
    verdict = _verdict(tmp_path, [profile])

    assert verdict["status"] == "undetermined", verdict
    assert verdict["undetermined"] == [
        f"pool P: pair {KEY_2}: {name} unobserved (deadline_tripped stage is missing)"
        for name in ("pre", "overrun", "post_trip", "tail")
    ]


@pytest.mark.parametrize("sealed, expected", [(True, "holds"), (False, "undetermined")])
def test_a_profile_run_whose_child_does_not_seal_is_not_a_profile_run(tmp_path, sealed, expected):
    """``post_trip`` / ``tail`` need an attested end, so pool P takes only runs whose child seals
    its journals (a run-level fact, fixed before any interval is read).  The same run is still a
    load run: its ``pre`` / ``overrun`` need no end."""

    profile = _tree(tmp_path, "profile")
    _cut(profile)
    old = _tree(tmp_path, "old")
    rows = _cut_rows()
    _write_pair(old, "f_B1_B2", _resolved_unknown(), journal=rows, sidecar=_sidecar(123.5),
                sealed=sealed)
    as_profile = _verdict(tmp_path, [profile, old])
    as_load = _verdict(tmp_path, [profile], load=[old])

    assert as_profile["status"] == expected, as_profile
    if not sealed:
        assert as_profile["undetermined"][0] == (
            f"pool P: run {old}: its child does not seal the journals (sealing_writer=False), "
            "so post_trip / tail cannot be attested")
    assert as_load["status"] == "holds", as_load
