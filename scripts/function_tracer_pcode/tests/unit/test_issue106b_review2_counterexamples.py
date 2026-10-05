# -*- coding: utf-8 -*-
"""Issue #106 PR-106-B review 2: a margin verdict needs complete evidence.

The counter-examples go through the margin tool's command line with only the
flags the reviewed head already had (profile roots, ``--load-root``,
``--pre-root``, ``--margin``), so on that head they fail on the verdict itself
(``margin_holds`` was true), not on a missing option.  Each scenario has one
normal, fully measured profile pair that fits the margin -- the reviewed head
passed as soon as such a pair existed -- plus the defect under test:

* a TIMEOUT whose kind the termination evidence does not establish;
* a pair of the load pool or of the fixed-cost pool that cannot be measured;
* a load pool or fixed-cost pool that was given but holds no deadline-cut pair.

None of these is evidence that the margin holds, so the verdict is not a pass,
and the output names why.  The expected reasons are literal strings.
"""
from __future__ import annotations

import json
from pathlib import Path

import pytest

from scripts.function_tracer_pcode.reporting import deadline_margin_summary as margin
from scripts.function_tracer_pcode.tests.unit.test_issue106b_review1_regressions import (
    _resolved_timeout_status,
    _resolved_unknown,
    _row,
    _sidecar,
    _trip,
    _write_pair,
)


def _root(tmp_path: Path, name: str, deadline: str = "100") -> Path:
    root = tmp_path / name / "eq"
    root.mkdir(parents=True)
    (root / "run_manifest.txt").write_text(
        f"analysis_timeout={deadline}\npair_stack_dump_lead=2s\n", encoding="utf-8")
    return root


def _cut_journal(origin_at=20.0, overrun=1.0, emit=1.0):
    trip_at = origin_at + 100.0 + overrun
    return [
        _row(1, "note", 0.0, payload={"note": "pair_journal_opened"}),
        _trip(2, trip_at, origin_at=origin_at),
        _row(3, "stage_start", trip_at + 0.5, "result_emit"),
        _row(4, "stage_end", trip_at + 0.5 + emit, "result_emit", emit),
    ], trip_at + 0.5 + emit


def _normal_pair(root: Path, stem: str = "f_B1_B2") -> None:
    rows, last_at = _cut_journal()
    _write_pair(root, stem, _resolved_unknown(), journal=rows, sidecar=_sidecar(last_at + 1.0))


def _verdict(tmp_path, profile, load=(), pre=(), margin_seconds=200.0):
    out = tmp_path / "verdict.json"
    argv = [str(root) for root in profile]
    for root in load:
        argv += ["--load-root", str(root)]
    for root in pre:
        argv += ["--pre-root", str(root)]
    argv += ["--margin", str(margin_seconds), "--json", str(out)]
    assert margin.main(argv) == 0
    return json.loads(out.read_text(encoding="utf-8"))


def _reasons(payload) -> str:
    return json.dumps(payload.get("verdict", {}), sort_keys=True)


def test_the_complete_scenario_alone_is_the_control(tmp_path):
    """The normal profile pair on its own: the numbers fit (control for the rest)."""

    profile = _root(tmp_path, "profile")
    _normal_pair(profile)
    payload = _verdict(tmp_path, [profile])

    assert payload["required_margin_seconds"] is not None
    assert payload["required_margin_seconds"] < 200.0


def test_an_unclassified_timeout_in_the_profile_is_not_a_pass(tmp_path):
    profile = _root(tmp_path, "profile")
    _normal_pair(profile)
    _write_pair(profile, "f_B3_B4", _resolved_timeout_status())   # rc 3 alone: unclassified
    payload = _verdict(tmp_path, [profile])

    assert payload["margin_holds"] is False
    assert "timeout_unclassified" in _reasons(payload)


@pytest.mark.parametrize("pool", ["load", "pre"])
def test_an_unmeasurable_pair_in_a_pool_is_not_a_pass(tmp_path, pool):
    profile = _root(tmp_path, "profile")
    _normal_pair(profile)
    other = _root(tmp_path, "other")
    rows, _ = _cut_journal()
    _write_pair(other, "f_B1_B2", _resolved_unknown(), journal=rows)   # cut, but no sidecar
    payload = _verdict(tmp_path, [profile], **{pool: [other]})

    assert payload["margin_holds"] is False
    assert "sidecar" in _reasons(payload)


@pytest.mark.parametrize("pool", ["load", "pre"])
def test_a_pool_given_without_any_cut_pair_is_not_a_pass(tmp_path, pool):
    profile = _root(tmp_path, "profile")
    _normal_pair(profile)
    other = _root(tmp_path, "other")
    _write_pair(other, "f_B1_B2", {"canonical_outcome": "EQUIVALENT"},
                journal=[_row(1, "note", 0.0, payload={"note": "pair_journal_opened"})],
                sidecar=_sidecar(10.0))
    payload = _verdict(tmp_path, [profile], **{pool: [other]})

    assert payload["margin_holds"] is False
    assert "no deadline-cut pair" in _reasons(payload)


@pytest.mark.parametrize("pool", ["profile", "load", "pre"])
def test_a_pair_whose_journal_is_missing_is_not_silently_dropped(tmp_path, pool):
    """A TIMEOUT without a journal used to vanish from the measurement.  (Without a journal
    and without a result: a result's own record of the deadline would settle "not cut".)"""

    profile = _root(tmp_path, "profile")
    _normal_pair(profile)
    other = profile if pool == "profile" else _root(tmp_path, "other")
    if pool != "profile":
        _normal_pair(other, "f_B5_B6")
    _write_pair(other, "f_B3_B4", _resolved_timeout_status(), log="")
    kwargs = {} if pool == "profile" else {pool: [other]}
    payload = _verdict(tmp_path, [profile], **kwargs)

    assert payload["margin_holds"] is False
    assert "REVE/sample/Eq/new/f/f_B3_B4" in _reasons(payload)
