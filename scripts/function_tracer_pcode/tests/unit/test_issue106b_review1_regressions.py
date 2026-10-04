# -*- coding: utf-8 -*-
"""Issue #106 PR-106-B review 1: regressions found in review, through the production entry points.

* A ``TIMEOUT`` the checker resolved itself (a solver terminal timeout: the
  supervisor RESOLVED the pair, exit 3) is not a process TIMEOUT.  The margin
  summary must read the same termination evidence ``timeout_kind`` reads, not
  the bare ``canonical_outcome``.
* The post-trip parts are the intersection of each stage's interval with the
  window after the trip, attributed once: a trip inside a stage that began
  before the trip (the conditional lane after the authority is final), nested
  or repeated stages, and any order of stages give parts that are each >= 0 and
  add up to the post-trip interval.
* A value the runner policy accepts is exactly a value the CLI accepts, with the
  same seconds: ``0.<400 zeros>1`` is positive as a decimal but ``0.0`` as the
  float the CLI parses, so it is refused before any pair starts.

The trees are written the way the runners write them (pair status, stage
journal, the supervisor's stack-dump status sidecar, the runtime receipt), and
the expectations are literal: none is computed with the code under test.
"""
from __future__ import annotations

import json
import math
from pathlib import Path

import pytest

from scripts.function_tracer_pcode.reporting import deadline_margin_summary as margin
from scripts.function_tracer_pcode.reporting.runner_timeout_policy import (
    TimeoutPolicyError,
    resolve_runner_timeout_policy,
)
from scripts.function_tracer_pcode.tests.unit.test_issue124c_timeout_kind import (
    _pair_status as _process_timeout_status,
    _resolved_status as _resolved_timeout_status,
    _sidecar_evidence as _child_timeout_sidecar,
)

T0 = 1000.0          # monotonic origin of the supervisor's deadline (barrier release)
EPOCH = 1_700_000_000.0
PROCESS = 240.0
BUDGET = 100.0
LEAD = 2.0


def _row(seq, event, at, stage=None, seconds=None, payload=None):
    return {
        "schema": "pair-stage-journal-v1", "seq": seq, "event": event, "stage": stage,
        "seconds": seconds, "t_monotonic": T0 + at, "t_epoch": EPOCH + at,
        "pid": 7, "payload": payload or {},
    }


def _trip(seq, at, origin_at, stage="solver"):
    return _row(seq, "note", at, payload={
        "note": "deadline_tripped", "stage": stage, "budget_seconds": BUDGET,
        "elapsed_seconds": at - origin_at,
    })


def _sidecar(exit_at, *, signal_sent=False, evidence=None):
    """The supervisor's status sidecar: deadline = T0 + PROCESS; the child exit
    was observed at ``exit_at`` (relative to T0)."""

    return {
        "schema": "pair-stack-dump-status-v1",
        "deadline_monotonic": T0 + PROCESS,
        "timeout_seconds": PROCESS,
        "lead_seconds": LEAD,
        "signal_sent": signal_sent,
        "cancel_linearized_offset_seconds": None if signal_sent else exit_at - PROCESS,
        "deadline_finalization_offset_seconds": None,
        "child_timeout_evidence": evidence,
    }


def _journal_end(rows):
    """The row `StageJournal.seal()` writes when the child exits normally."""

    last = rows[-1]
    time = last.get("t_monotonic")
    at = time - T0 if isinstance(time, float) and math.isfinite(time) else 0.0
    return _row(last["seq"] + 1, "journal_end", at,
                payload={"last_seq": last["seq"], "write_failures": 0})


def _deadline_log(tripped=None, budget=BUDGET, stage="solver") -> str:
    """The result JSON a child that finished prints.  ``tripped`` ``None`` = a run without the
    deadline (no ``analysis_deadline``); otherwise the deadline's own final record
    (`core.deadline.Deadline.diagnostic`, attached at the end of the deadline's scope)."""

    diagnostics = {}
    if tripped is not None:
        diagnostics["analysis_deadline"] = {
            "budget_seconds": budget, "elapsed_seconds": 1.0, "stage_reads": {},
            "tripped": tripped, "trip_stage": stage if tripped else None,
        }
    return ("=== EQUIVALENCE_RESULT_JSON_BEGIN ===\n"
            + json.dumps({"diagnostics": diagnostics}) + "\n=== EQUIVALENCE_RESULT_JSON_END ===\n")


def _result_log(root: Path, journal) -> str:
    """The result a finished child prints for this journal: the run's deadline (the CLI's
    ``--analysis-timeout``, as the manifest records it) and whether the journal tripped."""

    manifest = root / "run_manifest.txt"
    fields = dict(line.split("=", 1) for line in manifest.read_text(encoding="utf-8").splitlines()
                  if "=" in line) if manifest.is_file() else {}
    deadline = fields.get("analysis_timeout", str(BUDGET)).rstrip("s")
    if deadline in ("0", "0.0"):
        return _deadline_log(None)
    trips = [row for row in journal or ()
             if isinstance(row.get("payload"), dict)
             and row["payload"].get("note") == "deadline_tripped"]
    return _deadline_log(bool(trips), budget=float(deadline))


def _write_pair(root: Path, stem: str, status: dict, journal=None, sidecar=None,
                runtime=None, log=None, sealed=None):
    """Write one pair the way the runner and the child do.

    A child that exits normally seals its journal (`journal_end`) and prints its
    result JSON with the deadline's record; a child the supervisor killed
    (``supervisor_status`` TIMEOUT) does neither.
    """

    killed = status.get("supervisor_status") == "TIMEOUT"
    if sealed is None:
        sealed = not killed
    if log is None:
        log = "no result json here\n" if killed else _result_log(root, journal)
    folder = root / "REVE" / "sample" / "Eq" / "new" / "f"
    (folder / ".runtime-metrics").mkdir(parents=True, exist_ok=True)
    status = dict(status)
    status.setdefault("pair_execution_target", {
        "sample_identity": "REVE/sample/Eq/new", "function_name": "f",
        "left_binary_id": stem.split("_")[1], "right_binary_id": stem.split("_")[2],
    })
    (folder / f"{stem}.pair-status.json").write_text(json.dumps(status), encoding="utf-8")
    (folder / f"{stem}.log").write_text(log, encoding="utf-8")
    if journal is not None:
        rows = list(journal) + ([_journal_end(journal)] if sealed and journal else [])
        (folder / f"{stem}.stage.jsonl").write_text(
            "".join(json.dumps(row) + "\n" for row in rows), encoding="utf-8")
    if sidecar is not None:
        (folder / ".runtime-metrics" / f"{stem}.stack-dump.status.json").write_text(
            json.dumps(sidecar), encoding="utf-8")
    if runtime is not None:
        (folder / ".runtime-metrics" / f"{stem}.runtime.json").write_text(
            json.dumps(runtime), encoding="utf-8")


def _root(tmp_path: Path) -> Path:
    root = tmp_path / "eq"
    root.mkdir(parents=True)
    (root / "run_manifest.txt").write_text(
        "analysis_timeout=100\npair_stack_dump_lead=2s\n", encoding="utf-8")
    return root


def _terminations(root):
    return {pair.key: pair.termination for pair in margin.observe_run(root).pairs}


def _runtime(exit_at):
    # GNU time's view (supervisor start 3 s before the barrier, 1 s of supervisor work after)
    return {"elapsed_seconds": exit_at + 4.0, "finished_at_epoch": EPOCH + exit_at + 1.0}


# --------------------------------------------------------------------------
# 3. a TIMEOUT is classified from the termination evidence
# --------------------------------------------------------------------------


def test_a_solver_timeout_resolved_by_the_checker_is_not_a_process_timeout(tmp_path):
    root = _root(tmp_path)
    _write_pair(root, "f_B1_B2", _resolved_timeout_status(),
                sidecar=_child_timeout_sidecar())
    _write_pair(root, "f_B3_B4", _process_timeout_status())

    terminations = _terminations(root)

    assert terminations == {
        "REVE/sample/Eq/new/f/f_B1_B2": "solver_timeout",
        "REVE/sample/Eq/new/f/f_B3_B4": "process_timeout",
    }


def test_a_timeout_without_evidence_is_unclassified_not_a_process_timeout(tmp_path):
    root = _root(tmp_path)
    _write_pair(root, "f_B1_B2", _resolved_timeout_status())  # rc 3 alone proves nothing

    assert _terminations(root) == {"REVE/sample/Eq/new/f/f_B1_B2": "timeout_unclassified"}


# --------------------------------------------------------------------------
# 4. the post-trip parts are intervals intersected with the window after the trip
# --------------------------------------------------------------------------


def _resolved_unknown():
    return {"canonical_outcome": "UNKNOWN", "supervisor_status": "RESOLVED",
            "classification_valid": True}


def _pair_parts(tmp_path, journal, exit_at):
    root = _root(tmp_path)
    _write_pair(root, "f_B1_B2", _resolved_unknown(), journal=journal,
                sidecar=_sidecar(exit_at), runtime=_runtime(exit_at))
    pairs = [pair for pair in margin.observe_run(root).pairs if pair.cut]
    assert len(pairs) == 1, pairs
    assert pairs[0].missing == {}, pairs[0]
    return {**pairs[0].values, "needed": pairs[0].needed,
            "post_trip_parts": pairs[0].post_trip_parts}


def test_a_trip_inside_the_conditional_lane_counts_only_what_followed_the_trip(tmp_path):
    """The reviewer's counter-example: the authority is final, the conditional
    lane runs, the deadline trips inside it.  Before the fix, the whole
    post-trip window was ``unwind`` and the stages were added on top
    (post_trip 4 s, other -4.5 s)."""

    journal = [
        _row(1, "note", 0.0, payload={"note": "pair_journal_opened"}),
        _row(2, "stage_start", 100.0, "authority_finalize"),
        _row(3, "stage_end", 103.0, "authority_finalize", 3.0),
        _row(4, "stage_start", 103.0, "conditional_lane"),
        _trip(5, 120.5, origin_at=20.0, stage="conditional_lane"),
        _row(6, "stage_end", 121.5, "conditional_lane", 18.5),
        _row(7, "stage_start", 122.0, "result_emit"),
        _row(8, "stage_end", 124.5, "result_emit", 2.5),
    ]
    pair = _pair_parts(tmp_path, journal, exit_at=126.0)
    parts = pair["post_trip_parts"]

    assert pair["post_trip"] == pytest.approx(4.0)
    assert parts["conditional_lane"] == pytest.approx(1.0)       # 120.5 -> 121.5 only
    assert parts["authority_finalize"] == pytest.approx(0.0)     # ended before the trip
    assert parts["result_emit"] == pytest.approx(2.5)
    assert parts["other"] == pytest.approx(0.5)                  # 121.5 -> 122.0
    assert all(value >= 0 for value in parts.values()), parts
    assert sum(parts.values()) == pytest.approx(pair["post_trip"])


def test_nested_and_repeated_stages_are_attributed_once(tmp_path):
    journal = [
        _row(1, "note", 0.0, payload={"note": "pair_journal_opened"}),
        _trip(2, 120.0, origin_at=20.0),
        _row(3, "stage_start", 120.5, "authority_finalize"),
        _row(4, "stage_start", 121.0, "result_emit"),           # nested inside finalize
        _row(5, "stage_end", 122.0, "result_emit", 1.0),
        _row(6, "stage_end", 123.0, "authority_finalize", 2.5),
        _row(7, "stage_start", 123.0, "close_programs"),
        _row(8, "stage_end", 123.25, "close_programs", 0.25),
        _row(9, "stage_start", 123.25, "close_programs"),
        _row(10, "stage_end", 123.5, "close_programs", 0.25),
    ]
    pair = _pair_parts(tmp_path, journal, exit_at=125.0)
    parts = pair["post_trip_parts"]

    assert pair["post_trip"] == pytest.approx(3.5)
    assert parts["result_emit"] == pytest.approx(1.0)
    assert parts["authority_finalize"] == pytest.approx(1.5)     # 2.5 minus the nested 1.0
    assert parts["close_programs"] == pytest.approx(0.5)
    assert parts["other"] == pytest.approx(0.5)                  # 120.0 -> 120.5
    assert sum(parts.values()) == pytest.approx(pair["post_trip"])


def test_a_stage_left_open_by_the_end_of_the_journal_runs_to_its_end(tmp_path):
    journal = [
        _row(1, "note", 0.0, payload={"note": "pair_journal_opened"}),
        _trip(2, 120.0, origin_at=20.0),
        _row(3, "stage_start", 120.0, "authority_finalize"),
        _row(4, "stage_start", 121.0, "result_emit"),
        _row(5, "note", 122.0, payload={"note": "late"}),          # no stage_end follows
    ]
    pair = _pair_parts(tmp_path, journal, exit_at=123.0)
    parts = pair["post_trip_parts"]

    assert parts["authority_finalize"] == pytest.approx(1.0)
    assert parts["result_emit"] == pytest.approx(1.0)
    assert sum(parts.values()) == pytest.approx(pair["post_trip"])


# --------------------------------------------------------------------------
# 1. the intervals are on the supervisor's clock, for Eq and Neq alike
# --------------------------------------------------------------------------


def test_the_intervals_use_the_supervisors_deadline_not_gnu_time(tmp_path):
    """``needed`` is what counts against PAIR_PROCESS_TIMEOUT: the child exit
    the supervisor observed, measured from the supervisor's deadline origin."""

    journal = [
        _row(1, "note", 0.0, payload={"note": "pair_journal_opened"}),
        _trip(2, 120.0, origin_at=20.0),
        _row(3, "stage_start", 121.0, "result_emit"),
        _row(4, "stage_end", 122.0, "result_emit", 1.0),
    ]
    pair = _pair_parts(tmp_path, journal, exit_at=124.0)

    assert pair["pre"] == pytest.approx(20.0)
    assert pair["overrun"] == pytest.approx(0.0)
    assert pair["post_trip"] == pytest.approx(2.0)
    assert pair["tail"] == pytest.approx(2.0)
    assert pair["needed"] == pytest.approx(24.0)                 # 124 - 100, not GNU time's 28


def test_a_pair_without_a_runtime_receipt_is_still_measured(tmp_path):
    """The Neq runner writes no runtime receipt (#160); the sidecar is enough."""

    root = _root(tmp_path)
    journal = [
        _row(1, "note", 0.0, payload={"note": "pair_journal_opened"}),
        _trip(2, 120.0, origin_at=20.0),
    ]
    _write_pair(root, "f_B1_B2", _resolved_unknown(), journal=journal,
                sidecar=_sidecar(121.0))
    (pair,) = margin.observe_run(root).pairs

    assert pair.needed == pytest.approx(21.0)


def test_a_child_still_running_in_the_lead_window_is_a_margin_failure(tmp_path):
    root = _root(tmp_path)
    journal = [
        _row(1, "note", 0.0, payload={"note": "pair_journal_opened"}),
        _trip(2, 120.0, origin_at=20.0),
    ]
    _write_pair(root, "f_B1_B2", _resolved_unknown(), journal=journal,
                sidecar=_sidecar(239.0, signal_sent=True))
    (pair,) = margin.observe_run(root).pairs

    assert pair.entered_lead_window is True
    assert pair.missing == {"tail": "the child exit was not observed before the stack-dump send"}


# --------------------------------------------------------------------------
# 5. the policy accepts exactly what the CLI accepts
# --------------------------------------------------------------------------


_TINY = "0." + "0" * 400 + "1"
_HUGE = "1" + "0" * 400


@pytest.mark.parametrize("raw", [_TINY, _TINY + "s", _HUGE])
def test_a_value_the_cli_would_read_as_zero_or_infinity_is_refused(raw):
    with pytest.raises(TimeoutPolicyError):
        resolve_runner_timeout_policy(
            analysis_timeout=raw, margin="1", pair_process_timeout="1" + "0" * 500,
        )


@pytest.mark.parametrize(
    "raw", ["1", "0.001", "480", "120.5", "0.1", "1e-300".replace("1e-300", "0." + "0" * 299 + "1")],
)
def test_every_accepted_value_reaches_the_cli_as_the_same_seconds(raw):
    from scripts.function_tracer_pcode.cli.args import build_parser

    resolved = resolve_runner_timeout_policy(
        analysis_timeout=raw, margin="1", pair_process_timeout="100000",
    )
    flag, text = resolved.cli_args()
    parsed = build_parser().parse_args(["--equiv", "a", "b", "-f", "x", flag, text])

    assert parsed.analysis_timeout == float(raw)
    assert parsed.analysis_timeout > 0


def test_a_process_timeout_or_margin_that_is_not_a_finite_float_is_refused():
    for settings in (
        {"analysis_timeout": "0", "margin": "1", "pair_process_timeout": _HUGE},
        {"analysis_timeout": "10", "margin": _TINY, "pair_process_timeout": "600"},
        {"analysis_timeout": "10", "margin": _HUGE, "pair_process_timeout": "600"},
    ):
        with pytest.raises(TimeoutPolicyError):
            resolve_runner_timeout_policy(**settings)


# --------------------------------------------------------------------------
# same root as 3: the targeted acceptance read "TIMEOUT" as "process killed",
# and took any stack dump in the pair's directory as this pair's snapshot
# --------------------------------------------------------------------------


def _deadline_unknown_log():
    payload = {
        "function1_name": "f", "function2_name": "f", "is_equivalent": None,
        "unknown_reasons": [{"reason_id": "analysis_budget_exceeded",
                             "decision_effect": "blocks_decision",
                             "count_kind": "reason_record", "aggregation_unit": "result"}],
        "diagnostics": {"failures": {
            "pair_stop_state": "PAIR_TERMINAL_DEADLINE",
            "analysis_limitation": {"site": "solver", "evidence_refs": ["stage=solver"]},
        }},
    }
    return ("Result: UNKNOWN\n=== EQUIVALENCE_RESULT_JSON_BEGIN ===\n" + json.dumps(payload)
            + "\n=== EQUIVALENCE_RESULT_JSON_END ===\n")


def _acceptance(tmp_path, before_status, before_sidecar=None, sibling_dump=False, own_dump=True):
    from scripts.function_tracer_pcode.reporting import deadline_acceptance

    before = tmp_path / "before" / "eq"
    after = tmp_path / "after" / "eq"
    for root in (before, after):
        root.mkdir(parents=True)
    _write_pair(before, "f_B1_B2", before_status, sidecar=before_sidecar)
    _write_pair(after, "f_B1_B2", _resolved_unknown(), log=_deadline_unknown_log())
    metrics = after / "REVE" / "sample" / "Eq" / "new" / "f" / ".runtime-metrics"
    if own_dump:
        (metrics / "f_B1_B2.stack-dump.txt").write_text("=== deadline_tripped site=solver\n")
    if sibling_dump:
        (metrics / "f_B3_B4.stack-dump.txt").write_text("=== deadline_tripped site=solver\n")
    rows = deadline_acceptance.observe_runs(
        before, after, {"REVE/sample/Eq/new|f|B1|B2": "A"},
    )
    return deadline_acceptance.classify_target(rows[0])


def test_a_process_timeout_before_is_an_improvement(tmp_path):
    row = _acceptance(tmp_path, _process_timeout_status())

    assert row.before_timeout_kind == "process_wall_clock"
    assert row.improvement is True


def test_a_solver_timeout_before_is_not_an_improvement_from_a_process_timeout(tmp_path):
    row = _acceptance(tmp_path, _resolved_timeout_status(), before_sidecar=_child_timeout_sidecar())

    assert row.before_timeout_kind == "child_solver_timeout"
    assert row.improvement is False


def test_only_the_pairs_own_stack_dump_counts_as_its_snapshot(tmp_path):
    row = _acceptance(tmp_path, _process_timeout_status(), own_dump=False, sibling_dump=True)

    assert row.stack_snapshot is False
