# -*- coding: utf-8 -*-
"""Issue #106 PR-106-B review 4: a row that was readable is not a measurement that is complete.

Every scenario runs a real pair child (`_margin_journal_child`: the production
journal, its seal at exit, a real `core.deadline` trip and the result's own
``analysis_deadline`` record) with a failure injected into the real
`StageJournal`'s file, or corrupts what the child wrote, writes the runner's
files around it (pair status, the supervisor's sidecar, the run manifest), and
reads the verdict the margin's command line prints.

The child's pair needs more than the margin (the supervisor observes its exit
150 s after its last write), so the control is ``violated``.  The reviewer's
counter-examples turned that pair into "finished before the deadline" and the
verdict into ``holds``:

1. one failed write of the trip row (``write_failures=1``, seq 1, 3, 4, ...);
2. a trip row whose ``payload`` is missing or ``null``;
3. numbers outside a double (``10**400``) and finite numbers whose derived
   values overflow, which made the command line raise.

Only the command-line flags and the file layout the reviewed head already had
are used here, so the same file runs on that head (where the cases fail for the
reasons above).  Expected statuses and reasons are literal.
"""
from __future__ import annotations

import json
import os
import subprocess
import sys
import time
from pathlib import Path

import pytest

from scripts.function_tracer_pcode.reporting import deadline_margin_summary as margin

REPO = Path(__file__).resolve().parents[4]
COMMIT = "c" * 40
FOLDER = Path("REVE") / "sample" / "Eq" / "new" / "f"
KEY_FIT = "REVE/sample/Eq/new/f/f_B1_B2"
KEY = "REVE/sample/Eq/new/f/f_B3_B4"
PROCESS = 240.0
MARGIN = 140.0
#: the supervisor observes the child's exit this long after the child's last write
SLOW_EXIT = 150.0
PRE = 20.0
P_INTERVALS = ("pre", "overrun", "post_trip", "tail")

_RESOLVED = {"canonical_outcome": "UNKNOWN", "supervisor_status": "RESOLVED",
             "classification_valid": True}
_KILLED = {"canonical_outcome": "TIMEOUT", "supervisor_status": "TIMEOUT",
           "supervisor_authority_kind": "DurableTimeoutFinalizationBundle",
           "authority_kind": "DurableTimeoutFinalizationBundle",
           "child_exit_disposition": "EXITED_143_AFTER_SIGTERM", "child_returncode": 143,
           "child_returncode_observation_kind": "LIVE_PROCESS_WAIT",
           "classification_valid": True, "error_kind": None}


# --------------------------------------------------------------------------
# the run tree around a real child
# --------------------------------------------------------------------------


def _tree(tmp_path: Path, name: str = "profile") -> Path:
    root = tmp_path / name / "eq"
    (root / FOLDER / ".runtime-metrics").mkdir(parents=True)
    (root / "run_manifest.txt").write_text(
        f"analysis_timeout=100\npair_process_timeout_seconds={PROCESS:g}\n"
        f"pair_stack_dump_lead=2s\nparallel_jobs=4\ngit_commit={COMMIT}\ngit_dirty=0\n",
        encoding="utf-8")
    return root


def _paths(root: Path, stem: str):
    folder = root / FOLDER
    return (folder / f"{stem}.stage.jsonl", folder / f"{stem}.log",
            folder / f"{stem}.pair-status.json",
            folder / ".runtime-metrics" / f"{stem}.stack-dump.status.json")


def _run_child(root: Path, stem: str, inject: str = "none", exit_mode: str = "normal") -> dict:
    """Run one real child into ``stem``'s journal (appending, like a relaunch would)."""

    journal, log, _, _ = _paths(root, stem)
    dump = journal.with_suffix(".dump")
    child = subprocess.run(
        [sys.executable, "-B", "-m", "scripts.function_tracer_pcode.tests.unit._margin_journal_child",
         str(journal), str(dump), inject, exit_mode],
        cwd=REPO, env={**os.environ, "PYTHONPATH": str(REPO)},
        capture_output=True, text=True, timeout=120,
    )
    exited_at = time.monotonic()
    facts = json.loads(child.stderr.splitlines()[0])
    assert child.returncode == (0 if exit_mode == "normal" else -9), child.stderr
    log.write_text(child.stdout, encoding="utf-8")
    return {**facts, "exited_at": exited_at, "exit_mode": exit_mode}


def _supervisor_files(root: Path, stem: str, child: dict, **sidecar_overrides) -> None:
    """The pair status and the supervisor's sidecar for ``child`` (process deadline origin
    ``PRE`` s before the analysis started; exit observed ``SLOW_EXIT`` s after the child ended)."""

    _, _, status, sidecar = _paths(root, stem)
    deadline = child["analysis_start"] - PRE + PROCESS
    body = dict(_RESOLVED if child["exit_mode"] == "normal" else _KILLED)
    body["pair_execution_target"] = {
        "sample_identity": "REVE/sample/Eq/new", "function_name": "f",
        "left_binary_id": stem.split("_")[1], "right_binary_id": stem.split("_")[2],
    }
    status.write_text(json.dumps(body), encoding="utf-8")
    record = {
        "schema": "pair-stack-dump-status-v1", "deadline_monotonic": deadline,
        "timeout_seconds": PROCESS, "lead_seconds": 2.0, "signal_sent": False,
        "cancel_linearized_offset_seconds": child["exited_at"] + SLOW_EXIT - deadline,
        "deadline_finalization_offset_seconds": None, "child_timeout_evidence": None,
        "child_pid": child["pid"], "child_start_token": child["start_token"],
    }
    record.update(sidecar_overrides)
    text = json.dumps(record)
    for key, value in sidecar_overrides.items():
        if isinstance(value, str) and value.startswith("raw:"):          # a JSON number as text
            text = text.replace(json.dumps(value), value[4:])
    sidecar.write_text(text, encoding="utf-8")


def _fitting_pair(root: Path) -> None:
    """A real pair that fits the margin (the supervisor saw it exit right away)."""

    child = _run_child(root, "f_B1_B2")
    _supervisor_files(root, "f_B1_B2", dict(child, exited_at=child["exited_at"] - SLOW_EXIT))


def _verdict(tmp_path: Path, profile, *, pre=()) -> dict:
    out = tmp_path / "verdict.json"
    argv = [str(root) for root in profile]
    for root in pre:
        argv += ["--pre-root", str(root)]
    argv += ["--margin", f"{MARGIN:g}", "--profile-deadline", "100",
             "--pair-process-timeout", f"{PROCESS:g}", "--machinery-commit", COMMIT,
             "--json", str(out)]
    try:
        code = margin.main(argv)
    except Exception as exc:                                          # the reviewer's symptom 3
        pytest.fail(f"the margin command line raised {type(exc).__name__}: {exc}")
    assert code == 0
    return json.loads(out.read_text(encoding="utf-8"))["verdict"]


def _rows(root: Path, stem: str):
    journal, _, _, _ = _paths(root, stem)
    return [json.loads(line) for line in journal.read_text(encoding="utf-8").splitlines()]


def _event_seqs(root: Path, stem: str):
    """The seq of every row but the seal (the precondition: which rows the writer kept)."""

    return [row["seq"] for row in _rows(root, stem) if row["event"] != "journal_end"]


def _rewrite(root: Path, stem: str, rows) -> None:
    journal, _, _, _ = _paths(root, stem)
    journal.write_text("".join(json.dumps(row) + "\n" for row in rows), encoding="utf-8")


def _unobserved(reason: str, names=P_INTERVALS, key=KEY, pool="P"):
    return [f"pool {pool}: pair {key}: {name} unobserved ({reason})" for name in names]


def _over(verdict) -> bool:
    return (verdict["violations"][0] == "1 profile pair(s) needed more than the margin"
            and verdict["violations"][1].startswith("required ")
            and verdict["violations"][1].endswith(f"exceeds the margin {MARGIN:g}s"))


# --------------------------------------------------------------------------
# the control: a complete measurement of the slow pair is a violation
# --------------------------------------------------------------------------


def test_the_slow_pair_measured_completely_is_a_violation(tmp_path):
    profile = _tree(tmp_path)
    _fitting_pair(profile)
    _supervisor_files(profile, "f_B3_B4", _run_child(profile, "f_B3_B4"))
    verdict = _verdict(tmp_path, [profile])

    assert verdict["status"] == "violated", verdict
    assert _over(verdict) and verdict["undetermined"] == []


def test_the_fitting_pair_alone_holds(tmp_path):
    profile = _tree(tmp_path)
    _fitting_pair(profile)
    verdict = _verdict(tmp_path, [profile])

    assert verdict["status"] == "holds", verdict


# --------------------------------------------------------------------------
# 1. a write the real writer could not make
# --------------------------------------------------------------------------


def test_a_trip_row_the_writer_failed_to_write_is_not_a_pair_that_finished(tmp_path):
    """The reviewer's counter-example 1: write_failures=1, seq 1, 2, 3, 5, ...  The result
    says the deadline cut the pair; no interval is read from the journal with the gap."""

    profile = _tree(tmp_path)
    _fitting_pair(profile)
    _supervisor_files(profile, "f_B3_B4", _run_child(profile, "f_B3_B4", inject="trip"))
    verdict = _verdict(tmp_path, [profile])

    assert _event_seqs(profile, "f_B3_B4") == [1, 2, 3, 5, 6, 7]                # 4 = the trip
    assert verdict["status"] == "undetermined", verdict
    assert verdict["violations"] == []
    assert verdict["undetermined"] == _unobserved("journal incomplete: seq_gaps=1")


def test_writes_that_failed_after_the_last_row_leave_the_end_unattested(tmp_path):
    """Every write after the trip failed (the seal too): no gap shows it, so the end of
    the journal is not attested and the intervals that need the end are unobserved."""

    profile = _tree(tmp_path)
    _fitting_pair(profile)
    _supervisor_files(profile, "f_B3_B4", _run_child(profile, "f_B3_B4", inject="after_trip"))
    verdict = _verdict(tmp_path, [profile])

    assert _event_seqs(profile, "f_B3_B4") == [1, 2, 3, 4]
    assert verdict["status"] == "undetermined", verdict
    assert verdict["undetermined"] == _unobserved(
        "no journal_end row (the end is not attested)", names=("post_trip", "tail"))


def test_a_killed_child_whose_trip_row_was_lost_is_not_a_pair_that_finished(tmp_path):
    """No result, no seal, a gap: nothing says the deadline did not cut it (pool F)."""

    profile = _tree(tmp_path)
    _fitting_pair(profile)
    other = _tree(tmp_path, "other")
    _fitting_pair(other)
    _supervisor_files(other, "f_B3_B4", _run_child(other, "f_B3_B4", "trip", "killed"))
    verdict = _verdict(tmp_path, [profile], pre=[other])

    assert verdict["status"] == "undetermined", verdict
    assert verdict["undetermined"] == [
        f"pool F: pair {KEY}: cannot tell whether the deadline cut it (journal incomplete: "
        "seq_gaps=1; no result records analysis_deadline)"
    ]


def test_a_killed_childs_written_trip_still_counts(tmp_path):
    """The control of the case above: the trip row was written, so the pair was cut and its
    ``pre`` (the only interval pool F uses) is measured; the missing seal does not matter."""

    profile = _tree(tmp_path)
    _fitting_pair(profile)
    other = _tree(tmp_path, "other")
    _fitting_pair(other)
    _supervisor_files(other, "f_B3_B4", _run_child(other, "f_B3_B4", "none", "killed"))
    verdict = _verdict(tmp_path, [profile], pre=[other])

    assert verdict["status"] == "holds", verdict
    assert verdict["terms"]["pre"]["n"] == 3


# --------------------------------------------------------------------------
# 2. a required field that is missing or null
# --------------------------------------------------------------------------


@pytest.mark.parametrize("corrupt", ["missing", "null"])
def test_a_trip_row_without_its_payload_is_a_journal_loss(tmp_path, corrupt):
    profile = _tree(tmp_path)
    _fitting_pair(profile)
    _supervisor_files(profile, "f_B3_B4", _run_child(profile, "f_B3_B4"))
    rows = _rows(profile, "f_B3_B4")
    trip = next(row for row in rows if row["payload"].get("note") == "deadline_tripped")
    if corrupt == "missing":
        del trip["payload"]
    else:
        trip["payload"] = None
    _rewrite(profile, "f_B3_B4", rows)
    verdict = _verdict(tmp_path, [profile])

    assert verdict["status"] == "undetermined", verdict
    assert verdict["undetermined"] == _unobserved(
        "journal incomplete: field_errors in 1 row(s): payload")


@pytest.mark.parametrize("field", ["seq", "t_monotonic", "pid", "event"])
def test_a_trip_row_without_a_required_field_is_a_journal_loss(tmp_path, field):
    profile = _tree(tmp_path)
    _fitting_pair(profile)
    _supervisor_files(profile, "f_B3_B4", _run_child(profile, "f_B3_B4"))
    rows = _rows(profile, "f_B3_B4")
    trip = next(row for row in rows if row["payload"].get("note") == "deadline_tripped")
    trip[field] = None
    _rewrite(profile, "f_B3_B4", rows)
    verdict = _verdict(tmp_path, [profile])

    # a null event is not a row at all (it cannot be interpreted): a malformed line and its gap;
    # a null seq leaves its number missing as well
    reason = {"event": "seq_gaps=1, malformed_lines=1",
              "seq": "seq_gaps=1, field_errors in 1 row(s): seq"}.get(
                  field, f"field_errors in 1 row(s): {field}")
    assert verdict["status"] == "undetermined", verdict
    assert verdict["undetermined"] == _unobserved(f"journal incomplete: {reason}")


# --------------------------------------------------------------------------
# multiple executions: a legitimate restart of seq vs a loss in the selected one
# --------------------------------------------------------------------------


def test_a_loss_in_an_earlier_execution_does_not_hide_the_current_one(tmp_path):
    profile = _tree(tmp_path)
    _fitting_pair(profile)
    _run_child(profile, "f_B3_B4", inject="trip")                         # the earlier execution
    current = _run_child(profile, "f_B3_B4")                              # a relaunch, seq from 1
    _supervisor_files(profile, "f_B3_B4", current)
    verdict = _verdict(tmp_path, [profile])

    assert _event_seqs(profile, "f_B3_B4") == [1, 2, 3, 5, 6, 7, 1, 2, 3, 4, 5, 6, 7]
    assert verdict["status"] == "violated", verdict
    assert _over(verdict) and verdict["undetermined"] == []


def test_a_loss_in_the_current_execution_is_not_hidden_by_the_earlier_one(tmp_path):
    profile = _tree(tmp_path)
    _fitting_pair(profile)
    _run_child(profile, "f_B3_B4")
    current = _run_child(profile, "f_B3_B4", inject="trip")
    _supervisor_files(profile, "f_B3_B4", current)
    verdict = _verdict(tmp_path, [profile])

    assert verdict["status"] == "undetermined", verdict
    assert verdict["undetermined"] == _unobserved("journal incomplete: seq_gaps=1")


# --------------------------------------------------------------------------
# 3. numbers outside a double, and derived values that overflow
# --------------------------------------------------------------------------


_HUGE = "1" + "0" * 400                                                   # a JSON integer 10**400


@pytest.mark.parametrize("key, names, reason, status", [
    # the tail (150 s) is still measured: that alone is a violation
    ("timeout_seconds", ("pre",), "sidecar timeout_seconds is outside the range of a double",
     "violated"),
    ("deadline_monotonic", ("pre", "tail"),
     "sidecar deadline_monotonic is outside the range of a double", "undetermined"),
    ("cancel_linearized_offset_seconds", ("tail",),
     "sidecar cancel_linearized_offset_seconds is outside the range of a double", "undetermined"),
])
def test_a_sidecar_number_outside_a_double_is_unobserved(tmp_path, key, names, reason, status):
    profile = _tree(tmp_path)
    _fitting_pair(profile)
    _supervisor_files(profile, "f_B3_B4", _run_child(profile, "f_B3_B4"), **{key: "raw:" + _HUGE})
    verdict = _verdict(tmp_path, [profile])

    assert verdict["status"] == status, verdict
    assert [line for line in verdict["undetermined"] if line.startswith("pool")] == \
        _unobserved(reason, names=names)


def test_a_trip_budget_outside_a_double_is_unobserved(tmp_path):
    profile = _tree(tmp_path)
    _fitting_pair(profile)
    _supervisor_files(profile, "f_B3_B4", _run_child(profile, "f_B3_B4"))
    journal, _, _, _ = _paths(profile, "f_B3_B4")
    journal.write_text(journal.read_text(encoding="utf-8").replace(
        '"budget_seconds": 100.0', f'"budget_seconds": {_HUGE}'), encoding="utf-8")
    verdict = _verdict(tmp_path, [profile])

    assert verdict["status"] == "undetermined", verdict
    assert verdict["undetermined"] == _unobserved(
        "deadline_tripped budget_seconds is outside the range of a double")


def test_finite_records_whose_sum_overflows_are_unobserved(tmp_path):
    """``deadline_monotonic`` and the exit offset are each finite; the exit they add up to
    is not a double.  ``timeout_seconds`` is finite; the origin it subtracts to is not."""

    profile = _tree(tmp_path)
    _fitting_pair(profile)
    _supervisor_files(profile, "f_B3_B4", _run_child(profile, "f_B3_B4"),
                      deadline_monotonic=1e308, cancel_linearized_offset_seconds=1e308)
    other = _tree(tmp_path, "other")
    _fitting_pair(other)
    _supervisor_files(other, "f_B3_B4", _run_child(other, "f_B3_B4"),
                      deadline_monotonic=-1e308, timeout_seconds=1e308)
    verdict = _verdict(tmp_path, [profile], pre=[other])

    assert verdict["status"] == "undetermined", verdict
    exit_overflow = ("the child exit (deadline_monotonic + cancel_linearized_offset_seconds) is "
                     "not a finite number (the recorded values it is derived from are out of range)")
    origin_overflow = ("the process deadline's origin (deadline_monotonic - timeout_seconds) is "
                       "not a finite number (the recorded values it is derived from are out of range)")
    assert _unobserved(exit_overflow, names=("tail",)) == [
        line for line in verdict["undetermined"] if line.startswith(f"pool P: pair {KEY}: tail")]
    assert _unobserved(origin_overflow, names=("pre",), pool="F") == [
        line for line in verdict["undetermined"] if line.startswith(f"pool F: pair {KEY}: pre")]


def test_a_result_record_outside_a_double_is_not_evidence_of_the_cut(tmp_path):
    profile = _tree(tmp_path)
    _fitting_pair(profile)
    _supervisor_files(profile, "f_B3_B4", _run_child(profile, "f_B3_B4"))
    _, log, _, _ = _paths(profile, "f_B3_B4")
    log.write_text(log.read_text(encoding="utf-8").replace(
        '"budget_seconds": 100.0', f'"budget_seconds": {_HUGE}'), encoding="utf-8")
    verdict = _verdict(tmp_path, [profile])

    assert verdict["status"] == "undetermined", verdict
    assert verdict["undetermined"] == [
        f"pool P: pair {KEY}: cannot tell whether the deadline cut it "
        "(result analysis_deadline budget_seconds is outside the range of a double)"
    ]
