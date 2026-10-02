# -*- coding: utf-8 -*-
"""Issue #106 PR-106-B review 2: the margin verdict, pool by pool, from the run trees.

Every case writes run trees the way the runners write them (run manifest, pair
status, stage journal, the supervisor's stack-dump status sidecar), runs the
margin tool's command line with a complete profile, and reads the verdict it
printed.  The expectations are literal statuses and reasons; none is computed
with the code under test.

Per pool (P = the profile's runs, L = the load pool, F = the fixed-cost pool)
the matrix covers a normal measurement, an unclassified TIMEOUT, a missing
interval, and a pool given without a deadline-cut pair.  The cases after it
pin the confirmed process/solver TIMEOUT distinction, the per-pool interval
requirement and the run eligibility rules, all of which are fixed before any
number is aggregated.
"""
from __future__ import annotations

import json
from pathlib import Path

import pytest

from scripts.function_tracer_pcode.reporting import deadline_margin_summary as margin
from scripts.function_tracer_pcode.tests.unit.test_issue106b_review1_regressions import (
    _child_timeout_sidecar,
    _process_timeout_status,
    _resolved_timeout_status,
    _resolved_unknown,
    _row,
    _sidecar,
    _trip,
    _write_pair,
)

COMMIT = "c" * 40
OTHER_COMMIT = "d" * 40
KEY = "REVE/sample/Eq/new/f/f_B1_B2"
KEY_2 = "REVE/sample/Eq/new/f/f_B3_B4"


def _tree(tmp_path: Path, name: str, *, deadline="100", process="240", commit=COMMIT,
          dirty="0") -> Path:
    root = tmp_path / name / "eq"
    root.mkdir(parents=True)
    (root / "run_manifest.txt").write_text(
        f"analysis_timeout={deadline}\npair_process_timeout_seconds={process}\n"
        f"parallel_jobs=4\ngit_commit={commit}\ngit_dirty={dirty}\n", encoding="utf-8")
    return root


def _cut(root: Path, stem: str = "f_B1_B2", *, origin_at=20.0, overrun=1.0, emit=1.5,
         tail=1.0, sidecar=True, status=None) -> None:
    """A pair the deadline cut: pre ``origin_at``, overrun, post_trip ``emit``, tail."""

    trip_at = origin_at + 100.0 + overrun
    rows = [
        _row(1, "note", 0.0, payload={"note": "pair_journal_opened"}),
        _trip(2, trip_at, origin_at=origin_at),
        _row(3, "stage_start", trip_at, "result_emit"),
        _row(4, "stage_end", trip_at + emit, "result_emit", emit),
    ]
    _write_pair(root, stem, status or _resolved_unknown(), journal=rows,
                sidecar=_sidecar(trip_at + emit + tail) if sidecar else None)


def _finished(root: Path, stem: str, status) -> None:
    """A pair that ended without the deadline cutting it (journal without a trip)."""

    _write_pair(root, stem, status,
                journal=[_row(1, "note", 0.0, payload={"note": "pair_journal_opened"})],
                sidecar=_sidecar(30.0))


def _verdict(tmp_path, profile, load=(), pre=(), margin_seconds=140.0, deadline=100.0,
             extra=()):
    out = tmp_path / "verdict.json"
    argv = [str(root) for root in profile]
    for root in load:
        argv += ["--load-root", str(root)]
    for root in pre:
        argv += ["--pre-root", str(root)]
    argv += ["--margin", str(margin_seconds), "--profile-deadline", str(deadline),
             "--pair-process-timeout", "240", "--machinery-commit", COMMIT,
             "--json", str(out), *extra]
    assert margin.main(argv) == 0
    return json.loads(out.read_text(encoding="utf-8"))["verdict"]


def _scenario(tmp_path, pool):
    """A complete profile run, plus an extra run in ``pool`` (returned for the defect)."""

    profile = _tree(tmp_path, "profile")
    _cut(profile)
    if pool == "P":
        return profile, {"profile": [profile]}
    other = _tree(tmp_path, "other")
    return other, {"profile": [profile], ("load" if pool == "L" else "pre"): [other]}


# --------------------------------------------------------------------------
# the matrix: pool x {normal, unclassified, missing, empty}
# --------------------------------------------------------------------------


@pytest.mark.parametrize("pool", ["P", "L", "F"])
def test_normal_measurement_holds(tmp_path, pool):
    root, pools = _scenario(tmp_path, pool)
    if pool != "P":
        _cut(root, origin_at=30.0, overrun=4.0)
    verdict = _verdict(tmp_path, **pools)

    assert verdict["status"] == "holds", verdict
    assert verdict["violations"] == [] and verdict["undetermined"] == []
    # P: 20 + 1 + 1.5 + 1 + lead 2; an L run adds pre 30 and overrun 4; F adds pre 30 only
    assert verdict["required_margin_seconds"] == {"P": 25.5, "L": 38.5, "F": 35.5}[pool]


@pytest.mark.parametrize("pool, expected", [
    ("P", "undetermined"), ("L", "undetermined"),
    # F is another code's run used for pre only: how its pairs ended is not evidence
    # about this deadline machinery
    ("F", "holds"),
])
def test_unclassified_timeout(tmp_path, pool, expected):
    root, pools = _scenario(tmp_path, pool)
    if pool != "P":
        _cut(root)
    _finished(root, "f_B3_B4", _resolved_timeout_status())     # rc 3 alone: not established
    verdict = _verdict(tmp_path, **pools)

    assert verdict["status"] == expected, verdict
    if expected == "undetermined":
        assert verdict["undetermined"] == [
            f"pool {pool}: pair {KEY_2}: timeout_unclassified (timeout_kind not established)"
        ]


@pytest.mark.parametrize("pool, missing", [
    ("P", ["pre", "tail", "lead"]), ("L", ["pre"]), ("F", ["pre"]),
])
def test_missing_interval(tmp_path, pool, missing):
    root, pools = _scenario(tmp_path, pool)
    _cut(root, "f_B3_B4", sidecar=False)                         # cut, but no sidecar
    verdict = _verdict(tmp_path, **pools)

    assert verdict["status"] == "undetermined", verdict
    expected = {
        "pre": f"pool {pool}: pair {KEY_2}: pre unobserved (no stack-dump status sidecar)",
        "tail": f"pool {pool}: pair {KEY_2}: tail unobserved (no stack-dump status sidecar)",
        "lead": f"pool {pool}: pair {KEY_2}: lead unobserved (no stack-dump status sidecar)",
    }
    assert verdict["undetermined"] == [expected[name] for name in missing]


@pytest.mark.parametrize("pool", ["P", "L", "F"])
def test_pool_without_a_cut_pair(tmp_path, pool):
    if pool == "P":
        profile = _tree(tmp_path, "profile")
        _finished(profile, "f_B1_B2", {"canonical_outcome": "EQUIVALENT"})
        verdict = _verdict(tmp_path, [profile])
        assert verdict["status"] == "undetermined", verdict
        assert verdict["undetermined"] == [
            "pool P: no deadline-cut pair (nothing measured)",
            "term pre: no sample", "term overrun: no sample", "term post_trip: no sample",
            "term tail: no sample", "term lead: no sample",
        ]
        assert verdict["required_margin_seconds"] is None
        return
    root, pools = _scenario(tmp_path, pool)
    _finished(root, "f_B1_B2", {"canonical_outcome": "EQUIVALENT"})
    verdict = _verdict(tmp_path, **pools)

    assert verdict["status"] == "undetermined", verdict
    assert verdict["undetermined"] == [f"pool {pool}: no deadline-cut pair (nothing measured)"]


@pytest.mark.parametrize("pool", ["P", "L", "F"])
def test_pair_without_a_journal(tmp_path, pool):
    root, pools = _scenario(tmp_path, pool)
    if pool != "P":
        _cut(root)
    _write_pair(root, "f_B3_B4", _resolved_unknown(), sidecar=_sidecar(30.0))
    verdict = _verdict(tmp_path, **pools)

    assert verdict["status"] == "undetermined", verdict
    assert verdict["undetermined"] == [
        f"pool {pool}: pair {KEY_2}: cannot tell whether the deadline cut it (journal: journal_not_regular_file)"
    ]


# --------------------------------------------------------------------------
# termination evidence: process TIMEOUT, solver TIMEOUT, the lead window
# --------------------------------------------------------------------------


@pytest.mark.parametrize("pool, expected", [("P", "violated"), ("L", "violated"), ("F", "holds")])
def test_process_timeout(tmp_path, pool, expected):
    root, pools = _scenario(tmp_path, pool)
    if pool != "P":
        _cut(root)
    _finished(root, "f_B3_B4", _process_timeout_status())
    verdict = _verdict(tmp_path, **pools)

    assert verdict["status"] == expected, verdict
    if expected == "violated":
        assert verdict["violations"] == [
            f"pool {pool}: pair {KEY_2}: process TIMEOUT in a run with the deadline"
        ]


@pytest.mark.parametrize("pool, expected", [
    ("P", "undetermined"), ("L", "undetermined"), ("F", "holds"),
])
def test_a_pair_status_without_a_canonical_outcome(tmp_path, pool, expected):
    root, pools = _scenario(tmp_path, pool)
    if pool != "P":
        _cut(root)
    _finished(root, "f_B3_B4", {"canonical_outcome": "EQUIVALENT"})
    (root / "REVE/sample/Eq/new/f/f_B3_B4.pair-status.json").write_text("{", encoding="utf-8")
    verdict = _verdict(tmp_path, **pools)

    assert verdict["status"] == expected, verdict
    if expected == "undetermined":
        assert verdict["undetermined"] == [
            f"pool {pool}: pair {KEY_2}: termination evidence invalid"
        ]


def test_a_confirmed_solver_timeout_is_not_a_margin_event(tmp_path):
    profile = _tree(tmp_path, "profile")
    _cut(profile)
    _write_pair(profile, "f_B3_B4", _resolved_timeout_status(),
                journal=[_row(1, "note", 0.0, payload={"note": "pair_journal_opened"})],
                sidecar=_child_timeout_sidecar())
    verdict = _verdict(tmp_path, [profile])

    assert verdict["status"] == "holds", verdict


def test_a_child_in_the_lead_window_is_a_violation(tmp_path):
    profile = _tree(tmp_path, "profile")
    _cut(profile)
    rows = [_row(1, "note", 0.0, payload={"note": "pair_journal_opened"}),
            _trip(2, 121.0, origin_at=20.0)]
    _write_pair(profile, "f_B3_B4", _resolved_unknown(), journal=rows,
                sidecar=_sidecar(239.0, signal_sent=True))
    verdict = _verdict(tmp_path, [profile])

    assert verdict["status"] == "violated", verdict
    assert verdict["violations"] == [
        f"pool P: pair {KEY_2}: still running when the stack-dump send started"
    ]
    assert verdict["undetermined"] == [
        f"pool P: pair {KEY_2}: tail unobserved "
        "(the child exit was not observed before the stack-dump send)"
    ]


def test_a_margin_below_the_requirement_is_a_violation(tmp_path):
    profile = _tree(tmp_path, "profile")
    _cut(profile)                                            # needs 23.5 + lead 2
    verdict = _verdict(tmp_path, [profile], margin_seconds=25.0)

    assert verdict["status"] == "violated", verdict
    assert verdict["pairs_over_margin"] == [KEY]
    assert verdict["violations"] == [
        "1 profile pair(s) needed more than the margin",
        "required 25.5s exceeds the margin 25s",
    ]


def test_an_interval_the_pool_does_not_use_may_be_missing(tmp_path):
    """L and F do not use ``tail``: a load / fixed-cost pair without the child exit is fine."""

    profile = _tree(tmp_path, "profile")
    _cut(profile)
    load = _tree(tmp_path, "load")
    rows = [_row(1, "note", 0.0, payload={"note": "pair_journal_opened"}),
            _trip(2, 121.0, origin_at=20.0)]
    sidecar = _sidecar(122.0)
    sidecar["cancel_linearized_offset_seconds"] = None       # child exit not recorded
    _write_pair(load, "f_B1_B2", _resolved_unknown(), journal=rows, sidecar=sidecar)
    verdict = _verdict(tmp_path, [profile], load=[load])

    assert verdict["status"] == "holds", verdict


# --------------------------------------------------------------------------
# eligibility: fixed before aggregation; an ineligible run is never dropped silently
# --------------------------------------------------------------------------


def test_a_profile_run_with_a_longer_deadline_is_eligible(tmp_path):
    profile = _tree(tmp_path, "profile", deadline="120")
    _cut(profile)
    verdict = _verdict(tmp_path, [profile], margin_seconds=120.0)

    assert verdict["status"] == "holds", verdict


@pytest.mark.parametrize("pool, tree, reason", [
    ("P", {"deadline": "90"}, "deadline 90s is shorter than the profile's 100s"),
    ("P", {"process": "600"}, "process timeout 600.0 is not the profile's 240s"),
    ("P", {"commit": OTHER_COMMIT},
     f"commit {OTHER_COMMIT} does not have the deadline machinery under evaluation"),
    ("L", {"commit": OTHER_COMMIT},
     f"commit {OTHER_COMMIT} does not have the deadline machinery under evaluation"),
    ("L", {"dirty": "1"},
     "the tree was not clean (git_dirty=True), so its deadline machinery is not the listed "
     "commit's"),
    ("F", {"deadline": "0"}, "ran without the analysis deadline"),
])
def test_an_ineligible_run_makes_the_verdict_undetermined(tmp_path, pool, tree, reason):
    profile = _tree(tmp_path, "profile", **(tree if pool == "P" else {}))
    _cut(profile)
    pools = {"profile": [profile]}
    if pool != "P":
        other = _tree(tmp_path, "other", **tree)
        _cut(other)
        pools["load" if pool == "L" else "pre"] = [other]
    verdict = _verdict(tmp_path, **pools)

    assert verdict["status"] == "undetermined", verdict
    root = profile if pool == "P" else other
    assert f"pool {pool}: run {root}: {reason}" in verdict["undetermined"]


def test_a_fixed_cost_run_of_another_commit_is_eligible(tmp_path):
    profile = _tree(tmp_path, "profile")
    _cut(profile)
    other = _tree(tmp_path, "other", commit=OTHER_COMMIT, dirty="1")
    _cut(other, origin_at=60.0)
    verdict = _verdict(tmp_path, [profile], pre=[other])

    assert verdict["status"] == "holds", verdict
    assert verdict["required_margin_seconds"] == 65.5        # pre 60 + 1 + 1.5 + 1 + 2


def test_a_profile_run_outside_the_population_is_undetermined(tmp_path):
    profile = _tree(tmp_path, "profile")
    _cut(profile)
    population = tmp_path / "subset.json"
    population.write_text(json.dumps({"eq": {"sources": ["REVE/other/Eq/new"]},
                                      "neq": {"sources": []}}), encoding="utf-8")
    verdict = _verdict(tmp_path, [profile], extra=["--population-manifest", str(population)])

    assert verdict["status"] == "undetermined", verdict
    assert verdict["undetermined"] == [
        f"pool P: run {profile}: 1 sample(s) outside the profile, e.g. REVE/sample/Eq/new"
    ]


def test_without_the_profile_facts_the_verdict_is_undetermined(tmp_path):
    profile = _tree(tmp_path, "profile")
    _cut(profile)
    out = tmp_path / "v.json"
    assert margin.main([str(profile), "--margin", "140", "--json", str(out)]) == 0
    payload = json.loads(out.read_text(encoding="utf-8"))

    assert payload["margin_holds"] is False
    assert payload["verdict"]["status"] == "undetermined"
    assert payload["verdict"]["undetermined"] == [
        f"pool P: run {profile}: the deadline machinery commits are not given",
        f"pool P: run {profile}: the profile deadline / process timeout are not given",
    ]
