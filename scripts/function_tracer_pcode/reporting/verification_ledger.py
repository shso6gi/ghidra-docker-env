# -*- coding: utf-8 -*-
"""Machine-readable ledger of verification runs (Issue #123).

Usage::

    python3 -m scripts.function_tracer_pcode.reporting.verification_ledger \
        record --run-dir logs/EqBench/subset_x --requested-scope subset \
        [--before logs/EqBench/subset_w] [--issue 123] [--pr 151] [--note TEXT]
    python3 -m scripts.function_tracer_pcode.reporting.verification_ledger list

Every verification run used to leave a hand-written ``NOTES.md`` saying which
commit it was made on, what it was compared against and how far it actually
got.  This records the same facts mechanically, one JSON line per run in
``logs/EqBench/verification_ledger.jsonl`` (git-ignored).

**The ledger is a measurement aid, never an authority.**  It only reads
artifacts other tools already produced -- pair statuses, the runner manifests,
the publication manifests, the gates -- and nothing here can change a pair's
outcome, a receipt, or a runner's exit status.  ``eqbench_run_subset.sh``
records into it *after* the pairs are judged and after the soundness and
transition artifacts exist, and a failure to record is reported as a
diagnostic instead of failing the run.

Three distinctions the schema exists to keep apart:

``requested_scope`` vs ``completed_scope``
    "a run exists" and "the range that was asked for was actually verified"
    are different facts.  ``requested_scope`` is what the run was asked to
    cover (``subset`` / ``focused`` / ``full_eq`` / ``full_neq``);
    ``completed_scope`` is ``complete`` / ``partial`` / ``unknown``, derived
    from each result tree's own ``matrix-publication-manifest.json``.  There is
    deliberately no single ``full_evaluation`` boolean to collapse them into.

``coverage``
    The counted evidence behind ``completed_scope``: how many pairs the
    manifest expected, how many have a status on disk, how many are missing,
    how many the run only reused from an earlier run, and how many carry no
    readable result payload (``pairs_incomparable``).  A pair nobody looked at
    is never counted as one that was checked.

``code_matches_head`` / ``stale_code``
    Computed by ``list`` against the *current* HEAD, never stored -- a stored
    answer would silently rot as HEAD moves.  ``yes`` needs a recorded commit
    that equals the current HEAD, a run that was not dirty, and a working tree
    whose git state can be read right now; anything else is ``no`` or
    ``unknown`` and gets a ``stale_code`` mark.  ``stale_code`` means "this is
    not evidence about the code at HEAD", **not** "this run was invalid": a
    past run stays a perfectly good record of the commit it was made on.

The three axes of EPIC #130 (correctness / transition / gate) are recorded as
three separate groups of counters, exactly as ``outcome_transition --axes``
computes them.  They are never folded into one ``PASS``.
"""

from __future__ import annotations

import argparse
import json
import socket
import sys
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Dict, List, Mapping, Optional, Sequence, Tuple

from scripts.function_tracer_pcode.reporting import outcome_transition
from scripts.function_tracer_pcode.reporting.execution_identity import (
    GIT_DIRTY_NO,
    GIT_DIRTY_UNKNOWN,
    GIT_DIRTY_YES,
    GIT_STATE_UNAVAILABLE,
    git_state,
)
from scripts.function_tracer_pcode.reporting.pair_outcomes import (
    OUTCOME_ORDER,
    load_pair_outcomes,
)

LEDGER_SCHEMA = "verification-ledger-v1"
DEFAULT_LEDGER = Path("logs/EqBench/verification_ledger.jsonl")

SCOPE_SUBSET = "subset"
SCOPE_FOCUSED = "focused"
SCOPE_FULL_EQ = "full_eq"
SCOPE_FULL_NEQ = "full_neq"
REQUESTED_SCOPES = (SCOPE_SUBSET, SCOPE_FOCUSED, SCOPE_FULL_EQ, SCOPE_FULL_NEQ)
FULL_SCOPES = (SCOPE_FULL_EQ, SCOPE_FULL_NEQ)

LAYOUT_SUBSET = "subset_halves"
LAYOUT_MATRIX = "matrix_root"
LAYOUT_UNRECOGNISED = "unrecognised"

HEAD_MATCH_YES = "yes"
HEAD_MATCH_NO = "no"
HEAD_MATCH_UNKNOWN = "unknown"

SUBSET_MANIFEST_FILE = "subset_manifest.txt"
RUN_MANIFEST_FILE = "run_manifest.txt"
SOUNDNESS_GATE_FILE = "soundness_gate.json"
BENCHMARK_GATE_FILE = "benchmark_validation_gate.json"
UNSET = "unknown"
# Several sources carried a value and they were not the same.  Kept distinct
# from UNSET: "they differ" and "nobody recorded one" are different facts, and
# where the difference is legitimate (an Eq half and a Neq half really do run
# under different analysis configs) the per-tree values are kept as well.
MISMATCH = "differs"

# What the runners write into their own artifacts for a whole-benchmark run.
# This is the only thing a full verdict may be built on: it is written by the
# runner into the sealed publication manifest and the run manifest, and it is
# cross-checked against the filters below.
RUN_SCOPE_BY_FULL_SCOPE = {
    SCOPE_FULL_EQ: "FULL_EQBENCH",
    SCOPE_FULL_NEQ: "FULL_NEQ",
}
PUBLICATION_MANIFEST_FILE = "matrix-publication-manifest.json"
# A run that filtered its samples or pairs did not cover the benchmark, whatever
# its declared scope says.
NARROWING_FILTER_KEYS = ("sample_filter", "pair_filter")
NARROWING_LIMIT_KEY = "max_samples"
# Recorded per tree as well as folded, because these legitimately differ
# between the halves of one subset run.
PER_TREE_PROVENANCE_KEYS = (
    "analysis_config_digest", "analysis_source_digest_start",
    "analysis_source_digest_end", "run_scope", "run_kind",
    "start_time_utc", "end_time_utc",
)
# Settings that describe what a comparison was actually run under.  Recorded so
# two rows can be told apart without reopening the run directory.
SETTING_KEYS = (
    "parallel_jobs", "pair_process_timeout", "equiv_timeout", "decompile_timeout",
    "pairwise_timeout", "pairwise_timeout_hard", "pair_process_kill_after",
    "build_policy", "resource_admission",
)


def _utc_now() -> str:
    return datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")


def read_key_value_manifest(path: Path) -> Dict[str, str]:
    """A runner ``key=value`` manifest; missing file gives an empty mapping.

    Values may contain ``=`` (filters, paths), so only the first one splits.
    A later line wins, which is how the subset runner appends its own
    ``ledger_*`` outcome after the manifest is first written.
    """
    try:
        text = path.read_text(encoding="utf-8", errors="replace")
    except OSError:
        return {}
    fields: Dict[str, str] = {}
    for line in text.splitlines():
        if "=" in line:
            key, value = line.split("=", 1)
            fields[key.strip()] = value.strip()
    return fields


class RunLayout:
    """Where a run directory keeps its result trees.

    A subset run has an ``eq`` / ``neq`` half under it and a
    ``subset_manifest.txt``; a full or focused matrix run *is* the result tree
    and has a ``run_manifest.txt`` at its top.  A directory that matches
    neither is still recorded -- with ``unrecognised`` and whatever pair
    statuses can be found -- rather than crashing or being silently dropped.
    """

    def __init__(self, run_dir: Path):
        self.run_dir = Path(run_dir)
        self.subset_manifest = read_key_value_manifest(self.run_dir / SUBSET_MANIFEST_FILE)
        if self.subset_manifest:
            self.kind = LAYOUT_SUBSET
            scope = self.subset_manifest.get("scope", "all")
            expected = ("eq", "neq") if scope == "all" else (scope,)
        elif (self.run_dir / RUN_MANIFEST_FILE).is_file():
            self.kind = LAYOUT_MATRIX
            expected = (".",)
        else:
            self.kind = LAYOUT_UNRECOGNISED
            expected = (".",)
        # The halves the run said it would produce, kept apart from the ones
        # that are actually on disk.  Listing only what exists would make the
        # absence of a half disappear from every count that follows it, and a
        # run missing half its results would then read as complete.
        self.expected_tree_names = expected
        self.tree_names = tuple(
            name for name in expected if self._tree_path(name).is_dir()
        )
        self.trees = tuple(self._tree_path(name) for name in self.tree_names)
        self.missing_tree_names = tuple(
            name for name in expected if name not in self.tree_names
        )

    def _tree_path(self, name: str) -> Path:
        return self.run_dir if name == "." else self.run_dir / name

    def run_manifests(self) -> Tuple[Tuple[str, Dict[str, str]], ...]:
        return tuple(
            (name, read_key_value_manifest(tree / RUN_MANIFEST_FILE))
            for name, tree in zip(self.tree_names, self.trees)
        )


def _agreed_field(sources: Sequence[Mapping[str, str]], key: str) -> str:
    """One value shared by every source, ``mismatch`` when they disagree.

    Never invents a value: a key no source carries stays ``unknown``, which is
    what an older run without provenance produces.
    """
    values = {source[key] for source in sources if source.get(key)}
    if not values:
        return UNSET
    if len(values) > 1:
        return MISMATCH
    return values.pop()


def _per_tree_fields(layout: RunLayout, keys: Sequence[str]) -> Dict[str, Dict[str, str]]:
    """``tree -> {key: value}`` straight from each tree's own run manifest.

    Kept alongside the folded value so that a legitimate per-tree difference --
    an Eq half and a Neq half genuinely run under different analysis configs --
    is still readable instead of collapsing into the single word ``differs``.
    """
    return {
        name: {key: fields.get(key, UNSET) for key in keys}
        for name, fields in layout.run_manifests()
    }


def collect_provenance(layout: RunLayout) -> Dict[str, Any]:
    """The run's own record of the code it ran, read from its manifests.

    The subset manifest is preferred because it covers the whole run; the
    halves' ``run_manifest.txt`` fill in for a matrix run and for keys the
    subset manifest does not carry.  Nothing is derived from file timestamps
    or from the current checkout: a run that recorded no provenance stays
    ``unknown`` here and can never be matched to HEAD later.
    """
    half_manifests = [fields for _name, fields in layout.run_manifests() if fields]
    sources: List[Mapping[str, str]] = []
    if layout.subset_manifest:
        sources.append(layout.subset_manifest)
    sources.extend(half_manifests)
    provenance = {
        "source": (
            "subset_manifest" if layout.subset_manifest
            else ("run_manifest" if half_manifests else "absent")
        ),
        "commit": _agreed_field(sources, "git_commit"),
        "dirty": _agreed_field(sources, "git_dirty"),
        "dirty_files_digest": _agreed_field(sources, "git_dirty_files_digest"),
        "manifest_sha256": _agreed_field(sources, "manifest_sha256"),
        "analysis_source_digest_start": _agreed_field(
            half_manifests, "analysis_source_digest_start"),
        "analysis_source_digest_end": _agreed_field(
            half_manifests, "analysis_source_digest_end"),
        "analysis_config_digest": _agreed_field(half_manifests, "analysis_config_digest"),
        "runner_script_sha256": _agreed_field(half_manifests, "runner_script_sha256"),
        "trees": _per_tree_fields(layout, PER_TREE_PROVENANCE_KEYS),
    }
    return provenance


def collect_timing(layout: RunLayout) -> Dict[str, Any]:
    """The run's own wall clock, with the halves' clocks kept separately.

    A subset run starts, runs the Eq half, runs the Neq half and then stops, so
    its own start/end are *supposed* to differ from either half's.  Folding all
    three together turned every healthy run into ``differs``, which said
    nothing.  The whole-run clock therefore comes from ``subset_manifest.txt``
    alone; a matrix run has no such file and keeps using its run manifest.
    """
    half_manifests = [fields for _name, fields in layout.run_manifests() if fields]
    whole_run: List[Mapping[str, str]] = (
        [layout.subset_manifest] if layout.subset_manifest else half_manifests
    )
    elapsed = layout.subset_manifest.get("elapsed_seconds")
    return {
        "source": "subset_manifest" if layout.subset_manifest else "run_manifest",
        "start_time_utc": _agreed_field(whole_run, "start_time_utc"),
        "end_time_utc": _agreed_field(whole_run, "end_time_utc"),
        "hostname": _agreed_field(whole_run, "hostname"),
        "elapsed_seconds": int(elapsed) if (elapsed or "").isdigit() else None,
        "trees": {
            name: {
                "start_time_utc": fields.get("start_time_utc", UNSET),
                "end_time_utc": fields.get("end_time_utc", UNSET),
                "elapsed_seconds": layout.subset_manifest.get(
                    f"{name}_elapsed_seconds", UNSET),
            }
            for name, fields in layout.run_manifests()
        },
    }


def collect_settings(layout: RunLayout) -> Dict[str, str]:
    half_manifests = [fields for _name, fields in layout.run_manifests() if fields]
    sources: List[Mapping[str, str]] = []
    if layout.subset_manifest:
        sources.append(layout.subset_manifest)
    sources.extend(half_manifests)
    return {key: _agreed_field(sources, key) for key in SETTING_KEYS}


def collect_coverage(layout: RunLayout) -> Tuple[Dict[str, Any], str, str]:
    """``(coverage, completed_scope, detail)`` from each tree's own manifest.

    ``completed_scope`` is fail-closed: a tree whose publication manifest is
    absent or unreadable makes the whole run ``unknown``, and a tree with a
    missing, unexpected or merely reused pair makes it ``partial``.  Only a run
    in which every tree expected some pairs and executed all of them is
    ``complete``.
    """
    parts = []
    per_tree: Dict[str, Any] = {}
    pairs_incomparable = 0
    for name, tree in zip(layout.tree_names, layout.trees):
        part = outcome_transition.tree_completeness(tree)
        parts.append(part)
        per_tree[name] = part.as_dict()
        try:
            outcomes = load_pair_outcomes(tree)
        except (OSError, ValueError):
            outcomes = {}
        pairs_incomparable += sum(
            1 for record in outcomes.values()
            if outcome_transition.final_reason_set(record) is None
        )
    status, detail = outcome_transition.combine_completeness(parts)
    if status == outcome_transition.COMPLETENESS_COMPLETE and not any(
        part.pairs_expected for part in parts
    ):
        # Nothing was expected, so nothing was verified.  "0 of 0 pairs" is not
        # a complete verification of anything.
        status, detail = outcome_transition.COMPLETENESS_UNKNOWN, "no expected pairs"
    if layout.missing_tree_names:
        # A half the run said it would produce is not on disk at all.  Its
        # publication manifest is gone with it, so the size of the gap is not
        # knowable -- the counts below cover only the halves that exist, and
        # calling that ``complete`` or even ``partial`` would overstate them.
        missing = ", ".join(layout.missing_tree_names)
        status = outcome_transition.COMPLETENESS_UNKNOWN
        detail = "; ".join(filter(None, (
            f"expected result tree(s) missing: {missing}", detail,
        )))
    coverage = {
        "pairs_expected": sum(part.pairs_expected for part in parts),
        "pairs_with_status": sum(part.pairs_with_status for part in parts),
        "pairs_missing": sum(len(part.pairs_missing) for part in parts),
        "pairs_unexpected": sum(len(part.pairs_unexpected) for part in parts),
        "pairs_verified_skipped": sum(part.pairs_verified_skipped for part in parts),
        "pairs_incomparable": pairs_incomparable,
        "trees_expected": list(layout.expected_tree_names),
        "trees_missing": list(layout.missing_tree_names),
        "trees": per_tree,
    }
    return coverage, status, detail


def collect_counts(layout: RunLayout) -> Dict[str, int]:
    counts: Dict[str, int] = {name: 0 for name in OUTCOME_ORDER}
    for tree in layout.trees:
        try:
            outcomes = load_pair_outcomes(tree)
        except (OSError, ValueError):
            continue
        for record in outcomes.values():
            counts[record.outcome] = counts.get(record.outcome, 0) + 1
    return {name: value for name, value in counts.items() if value}


def collect_axes(
    layout: RunLayout, before_layout: Optional["RunLayout"],
) -> Tuple[Dict[str, Any], Dict[str, Any], Dict[str, Any]]:
    """The three axes as three separate groups of counters.

    Axis A (correctness) and axis C (gate) are properties of this run alone.
    Axis B (transition) needs a before run; without one it is recorded as not
    evaluated rather than as "nothing changed".
    """
    correctness: Dict[str, Any] = {name: 0 for name in outcome_transition.CORRECTNESS_ORDER}
    gate: Dict[str, Any] = {name: 0 for name in outcome_transition.GATE_ORDER}
    by_label: Dict[str, Any] = {}
    decided: Dict[str, Any] = {}
    for tree in layout.trees:
        try:
            outcomes = load_pair_outcomes(tree)
        except (OSError, ValueError):
            continue
        manifest, ground_truth = outcome_transition.load_ground_truth(tree)
        summary = outcome_transition.summarize_run_axes(
            outcomes, manifest=manifest, ground_truth=ground_truth,
        )
        for name in outcome_transition.CORRECTNESS_ORDER:
            correctness[name] += summary["correctness"][name]
        for name in outcome_transition.GATE_ORDER:
            gate[name] += summary["gate"][name]
        for label, values in summary["correctness"]["by_label"].items():
            row = by_label.setdefault(label, {name: 0 for name in outcome_transition.CORRECTNESS_ORDER})
            for name, value in values.items():
                row[name] += value
        for label, outcomes_table in summary["correctness"]["decided"].items():
            row = decided.setdefault(label, {})
            for name, values in outcomes_table.items():
                cell = row.setdefault(name, {key: 0 for key in outcome_transition.CORRECTNESS_ORDER})
                for key, value in values.items():
                    cell[key] += value
    correctness["by_label"] = by_label
    correctness["decided"] = decided

    transition: Dict[str, Any] = {"evaluated": False, "reason": "no before run"}
    if before_layout is not None:
        transition = _collect_transition(layout, before_layout)
    return correctness, transition, gate


def _collect_transition(layout: RunLayout, before_layout: RunLayout) -> Dict[str, Any]:
    """Axis B plus the reason-set comparison, tree by tree.

    Trees are paired by name so an ``eq`` half is never compared against a
    ``neq`` one.  A tree the before run does not have is recorded as not
    compared instead of being counted as unchanged.
    """
    totals: Dict[str, Any] = {
        "evaluated": True,
        "before_run": str(before_layout.run_dir),
        "pairs": 0,
        "changed": 0,
        "trees_not_compared": [],
        "reason_sets": {
            "pairs": 0, "comparable": 0, "incomparable": 0,
            "outcome_mismatch": 0, "reason_set_mismatch": 0,
            "incomparable_sides_agree": True,
        },
    }
    for name in outcome_transition.TRANSITION_ORDER:
        totals[name] = 0
    notes = {name: 0 for name in outcome_transition.TRANSITION_NOTE_ORDER}
    before_trees = dict(zip(before_layout.tree_names, before_layout.trees))
    for name, tree in zip(layout.tree_names, layout.trees):
        before_tree = before_trees.get(name)
        if before_tree is None or not Path(before_tree).is_dir():
            totals["trees_not_compared"].append(name)
            continue
        try:
            report, sections = outcome_transition.build_report_sections(
                Path(before_tree), Path(tree), axes=True, reason_sets=True,
            )
        except (OSError, ValueError) as exc:
            totals["trees_not_compared"].append(f"{name}: {exc}")
            continue
        axes = sections["axes"]
        reason_sets = sections["reason_sets"]
        totals["pairs"] += len(report.rows)
        totals["changed"] += len(report.changed_rows)
        for key, value in axes.transition_counts().items():
            totals[key] += value
        for key, value in axes.transition_notes().items():
            notes[key] += value
        counts = reason_sets.counts()
        for key in ("pairs", "comparable", "incomparable", "outcome_mismatch", "reason_set_mismatch"):
            totals["reason_sets"][key] += counts[key]
        totals["reason_sets"]["incomparable_sides_agree"] = (
            totals["reason_sets"]["incomparable_sides_agree"]
            and reason_sets.incomparable_sides_agree
        )
    totals["notes"] = notes
    return totals


def collect_scope_evidence(layout: RunLayout) -> Dict[str, Any]:
    """What the run's own artifacts say about the scope it actually executed.

    ``requested_scope`` is what somebody asked for; it is not evidence.  This
    reads what the runner wrote into the artifacts instead:

    * ``run_scope`` from the sealed ``matrix-publication-manifest.json`` (and
      from its ``analysis_config``, whose digest is ``analysis_config_digest``),
      cross-checked against ``run_manifest.txt``;
    * the filters the run was given -- a run with a ``sample_filter`` or a
      ``pair_filter``, or a ``max_samples`` limit, covered part of the benchmark
      whatever its declared scope says.

    Anything missing or disagreeing leaves ``unknown`` / ``differs``, which can
    never support a full verdict.
    """
    trees: Dict[str, Any] = {}
    for name, tree in zip(layout.tree_names, layout.trees):
        run_manifest = read_key_value_manifest(tree / RUN_MANIFEST_FILE)
        publication = _read_json(tree / PUBLICATION_MANIFEST_FILE) or {}
        config = publication.get("analysis_config")
        config = config if isinstance(config, Mapping) else {}
        declared = _agreed_field(
            [
                source for source in (
                    run_manifest,
                    {"run_scope": publication.get("run_scope")}
                    if isinstance(publication.get("run_scope"), str) else {},
                    {"run_scope": config.get("run_scope")}
                    if isinstance(config.get("run_scope"), str) else {},
                ) if source
            ],
            "run_scope",
        )
        trees[name] = {
            "declared_run_scope": declared,
            "narrowed": _run_was_narrowed(run_manifest, config),
            "has_publication_manifest": bool(publication),
        }
    return {
        "trees": trees,
        "declared_run_scope": _agreed_field(
            [{"run_scope": row["declared_run_scope"]} for row in trees.values()],
            "run_scope",
        ) if trees else UNSET,
    }


def _run_was_narrowed(
    run_manifest: Mapping[str, str], config: Mapping[str, Any],
) -> Optional[bool]:
    """``True`` when a filter or a sample limit narrowed the run, else ``False``.

    ``None`` when neither source recorded the filters at all: not knowing
    whether a run was narrowed must not read as "it was not".
    """
    seen = False
    for source in (run_manifest, config):
        if not source:
            continue
        for key in NARROWING_FILTER_KEYS:
            if key in source:
                seen = True
                if str(source[key] or ""):
                    return True
        if NARROWING_LIMIT_KEY in source:
            seen = True
            try:
                if int(source[NARROWING_LIMIT_KEY]) > 0:
                    return True
            except (TypeError, ValueError):
                return None
    return False if seen else None


def full_scope_evidence(row: Mapping[str, Any]) -> Tuple[Optional[str], str]:
    """``(full scope this row really covers, reason)`` -- artifacts only.

    A row supports a full verdict only when every one of these holds, so that
    no self-declared field can manufacture one:

    * the run is a single matrix tree (a subset run's ``eq``/``neq`` halves are
      by construction not a whole-benchmark run, whatever scope was requested);
    * the scope the runner recorded in its artifacts is the full scope, and it
      agrees across the publication manifest and the run manifest;
    * that recorded scope matches what was requested;
    * no sample or pair filter narrowed the run;
    * the run is complete, by the publication manifest's own pair census.

    Whether it is evidence about the code at *HEAD* is a separate question,
    answered by ``head_match``.
    """
    requested = row.get("requested_scope")
    if requested not in FULL_SCOPES:
        return None, "not a full scope request"
    if row.get("run_layout") != LAYOUT_MATRIX:
        return None, (
            f"run layout is {row.get('run_layout')}, not a single whole-benchmark "
            "matrix tree"
        )
    evidence = row.get("scope_evidence") or {}
    declared = evidence.get("declared_run_scope", UNSET)
    expected = RUN_SCOPE_BY_FULL_SCOPE[requested]
    if declared != expected:
        return None, f"the run recorded run_scope={declared}, not {expected}"
    narrowed = {
        name: tree.get("narrowed") for name, tree in (evidence.get("trees") or {}).items()
    }
    if any(value is not False for value in narrowed.values()) or not narrowed:
        return None, "the run was narrowed by a filter, or its filters are unknown"
    if row.get("completed_scope") != outcome_transition.COMPLETENESS_COMPLETE:
        return None, f"completed_scope is {row.get('completed_scope')}"
    return requested, ""


def _read_json(path: Path) -> Optional[Mapping[str, Any]]:
    try:
        payload = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, ValueError):
        return None
    return payload if isinstance(payload, Mapping) else None


def collect_gate_reports(layout: RunLayout) -> Dict[str, Any]:
    """The gates' own persisted verdicts, read back rather than recomputed.

    The soundness gate is a per-run artifact written next to the results; the
    benchmark gate is per tree.  A gate whose artifact is absent is recorded
    as ``unknown`` -- never as ``PASS``.
    """
    soundness = _read_json(layout.run_dir / SOUNDNESS_GATE_FILE)
    benchmark: Dict[str, Any] = {}
    for name, tree in zip(layout.tree_names, layout.trees):
        payload = _read_json(tree / BENCHMARK_GATE_FILE)
        if payload is None:
            benchmark[name] = {"gate": UNSET}
            continue
        benchmark[name] = {
            "gate": payload.get("gate", UNSET),
            "pairs": payload.get("pairs"),
            "hard_violations": sum((payload.get("hard_violations") or {}).values()),
            "suspicious": sum((payload.get("suspicious") or {}).values()),
        }
    if soundness is None or not isinstance(soundness.get("passed"), bool):
        # No readable soundness artifact: the gate is unknown, never a PASS.
        soundness_status, soundness_violations = UNSET, None
    else:
        soundness_status = "PASS" if soundness["passed"] else "VIOLATION"
        soundness_violations = soundness.get("violations")
    return {
        "soundness": {
            "status": soundness_status,
            "violations": soundness_violations,
            "recorded_exit_status": layout.subset_manifest.get(
                "soundness_gate_status", UNSET),
        },
        "benchmark": benchmark,
    }


def _reference(given: Optional[str], recorded: Optional[str]) -> Optional[str]:
    """An issue / PR reference, with the runner's literal ``none`` normalised.

    ``eqbench_run_subset.sh`` writes ``issue=none`` when nothing was named, and
    a row carrying the string ``"none"`` would read like a reference.
    """
    for value in (given, recorded):
        if value and value != "none":
            return value
    return None


def build_row(
    run_dir: Path,
    *,
    requested_scope: str,
    before: Optional[Path] = None,
    issue: Optional[str] = None,
    pr: Optional[str] = None,
    note: Optional[str] = None,
) -> Dict[str, Any]:
    """One ledger row for one verification run.

    ``requested_scope`` is taken from the caller and never guessed from the
    directory: only the person who started the run knows what it was meant to
    cover.  Everything else is read from the run's own artifacts.
    """
    if requested_scope not in REQUESTED_SCOPES:
        raise ValueError(
            f"requested scope must be one of {', '.join(REQUESTED_SCOPES)}: {requested_scope}"
        )
    run_dir = Path(run_dir)
    if not run_dir.is_dir():
        raise ValueError(f"not a run directory: {run_dir}")
    layout = RunLayout(run_dir)
    before_layout = None
    before_run = layout.subset_manifest.get("before_run") or None
    if before is not None:
        before_run = str(before)
    if before_run and before_run not in ("none", ""):
        candidate = Path(before_run)
        before_layout = RunLayout(candidate) if candidate.is_dir() else None
    coverage, completed_scope, completed_detail = collect_coverage(layout)
    correctness, transition, gate_axis_counts = collect_axes(layout, before_layout)
    before_commit = layout.subset_manifest.get("before_commit", UNSET)
    if before_layout is not None:
        recorded = collect_provenance(before_layout)["commit"]
        if recorded != UNSET:
            before_commit = recorded
    return {
        "schema": LEDGER_SCHEMA,
        "recorded_at_utc": _utc_now(),
        "recorded_on_host": socket.gethostname(),
        "run_dir": str(run_dir),
        "run_layout": layout.kind,
        "trees": list(layout.tree_names),
        "issue": _reference(issue, layout.subset_manifest.get("issue")),
        "pr": _reference(pr, layout.subset_manifest.get("pr")),
        "note": note or None,
        "requested_scope": requested_scope,
        "completed_scope": completed_scope,
        "completed_scope_detail": completed_detail,
        # What the run's own artifacts say about the scope it executed.  A full
        # verdict is built from this, never from ``requested_scope`` alone.
        "scope_evidence": collect_scope_evidence(layout),
        "coverage": coverage,
        "provenance": collect_provenance(layout),
        "before": {
            "run": before_run or None,
            "commit": before_commit,
            "resolved": before_layout is not None,
        },
        "timing": collect_timing(layout),
        "settings": collect_settings(layout),
        "counts": collect_counts(layout),
        "correctness": correctness,
        "transition": transition,
        "gate": {**collect_gate_reports(layout), "axis": gate_axis_counts},
        "run_exit_status": layout.subset_manifest.get("exit_status", UNSET),
        # Issue #123 / v3 §9.3: filled in by hand when an indicator moved and
        # a rerun did not settle whether it was the code or run-to-run noise.
        "unresolved_variance": [],
    }


def append_row(ledger_path: Path, row: Mapping[str, Any]) -> None:
    ledger_path = Path(ledger_path)
    ledger_path.parent.mkdir(parents=True, exist_ok=True)
    with ledger_path.open("a", encoding="utf-8") as stream:
        stream.write(json.dumps(row, sort_keys=True) + "\n")


def read_rows(ledger_path: Path) -> Tuple[Dict[str, Any], ...]:
    """Every ledger row; an unparsable line is skipped, not fatal.

    A ledger is append-only diagnostics, so one corrupt line must not hide the
    rest of the history.  Skipped lines are reported by ``list``.
    """
    try:
        text = Path(ledger_path).read_text(encoding="utf-8", errors="replace")
    except OSError:
        return ()
    rows = []
    for line in text.splitlines():
        if not line.strip():
            continue
        try:
            payload = json.loads(line)
        except ValueError:
            rows.append({"schema": "unparsable", "raw": line[:200]})
            continue
        rows.append(payload if isinstance(payload, dict) else {"schema": "unparsable"})
    return tuple(rows)


def head_match(row: Mapping[str, Any], head: Mapping[str, Any]) -> Tuple[str, str]:
    """``(code_matches_head, reason)`` for one row against the current HEAD.

    Computed here rather than stored, because HEAD moves and a stored answer
    would quietly become wrong.  Only a clean run recorded at exactly the
    current commit, in a checkout whose git state can be read right now, is
    ``yes``; anything else fails to ``no`` or ``unknown`` so that a row can
    never be misread as evidence about the code at HEAD.
    """
    provenance = row.get("provenance") or {}
    commit = provenance.get("commit", UNSET)
    dirty = provenance.get("dirty", UNSET)
    head_commit = head.get("commit", GIT_STATE_UNAVAILABLE)
    if head_commit == GIT_STATE_UNAVAILABLE:
        return HEAD_MATCH_UNKNOWN, "the current HEAD cannot be read"
    if commit in (UNSET, GIT_STATE_UNAVAILABLE, MISMATCH, "", None):
        return HEAD_MATCH_UNKNOWN, f"the run recorded no usable commit ({commit})"
    if commit != head_commit:
        return HEAD_MATCH_NO, "the run was made on a different commit"
    if dirty == GIT_DIRTY_YES:
        return HEAD_MATCH_NO, "the run was made on a dirty tree, so it is not HEAD's code"
    if dirty != GIT_DIRTY_NO:
        return HEAD_MATCH_UNKNOWN, f"the run did not record whether it was dirty ({dirty})"
    if head.get("dirty") == GIT_DIRTY_YES:
        return HEAD_MATCH_NO, "the working tree has uncommitted changes under the source roots"
    if head.get("dirty") != GIT_DIRTY_NO:
        return HEAD_MATCH_UNKNOWN, "the current working tree state cannot be read"
    return HEAD_MATCH_YES, ""


def _coverage_cell(row: Mapping[str, Any]) -> str:
    coverage = row.get("coverage") or {}
    expected = coverage.get("pairs_expected", 0)
    seen = coverage.get("pairs_with_status", 0)
    parts = [f"{seen}/{expected}"]
    for key, label in (
        ("pairs_missing", "missing"),
        ("pairs_unexpected", "unexpected"),
        ("pairs_verified_skipped", "reused"),
        ("pairs_incomparable", "no-payload"),
    ):
        value = coverage.get(key, 0)
        if value:
            parts.append(f"{value} {label}")
    # A result tree that is not there at all cannot be counted above, so it is
    # named instead of vanishing from the numbers.
    absent = coverage.get("trees_missing") or []
    if absent:
        parts.append(f"MISSING TREE(S): {', '.join(absent)}")
    return " ".join(parts)


def _digest_cell(row: Mapping[str, Any], key: str) -> str:
    """One provenance digest, keeping the per-tree values when they differ.

    ``differs`` alone would hide that an Eq half and a Neq half legitimately
    run under different analysis configs, so the individual values follow it.
    """
    provenance = row.get("provenance") or {}
    value = provenance.get(key, UNSET)
    # "mismatch" is what rows written before this field was renamed carry.
    if value not in (MISMATCH, "mismatch"):
        return _short(value)
    per_tree = provenance.get("trees") or {}
    detail = " ".join(
        f"{name}={_short((fields or {}).get(key, UNSET))}"
        for name, fields in sorted(per_tree.items())
    )
    return f"{MISMATCH} ({detail})" if detail else MISMATCH


def _short(value: Any) -> str:
    text = str(value)
    return text if len(text) <= 16 else text[:12]


def format_row_lines(row: Mapping[str, Any], head: Mapping[str, Any]) -> List[str]:
    if row.get("schema") != LEDGER_SCHEMA:
        return [f"  (unreadable ledger line: {row.get('raw', '')!r})"]
    match, reason = head_match(row, head)
    stale = "" if match == HEAD_MATCH_YES else "  [stale_code]"
    provenance = row.get("provenance") or {}
    transition = row.get("transition") or {}
    correctness = row.get("correctness") or {}
    gate = row.get("gate") or {}
    reason_sets = transition.get("reason_sets") or {}
    timing = row.get("timing") or {}
    scope_evidence, scope_reason = full_scope_evidence(row)
    lines = [
        f"  {row.get('recorded_at_utc', '?')}  {row.get('run_dir', '?')}{stale}",
        f"      requested_scope={row.get('requested_scope')}  "
        f"completed_scope={row.get('completed_scope')}"
        + (f" ({row.get('completed_scope_detail')})" if row.get("completed_scope_detail") else ""),
        f"      coverage={_coverage_cell(row)}",
        f"      layout={row.get('run_layout')} "
        f"declared_run_scope={(row.get('scope_evidence') or {}).get('declared_run_scope', UNSET)} "
        + (
            f"whole_benchmark_evidence={scope_evidence}"
            if scope_evidence is not None
            else f"whole_benchmark_evidence=no ({scope_reason})"
        ),
        f"      commit={_short(provenance.get('commit', UNSET))} "
        f"dirty={provenance.get('dirty', UNSET)} "
        f"code_matches_head={match}" + (f" ({reason})" if reason else ""),
        f"      manifest_sha256={_digest_cell(row, 'manifest_sha256')} "
        f"analysis_config_digest={_digest_cell(row, 'analysis_config_digest')}",
        f"      timing={timing.get('start_time_utc', UNSET)} -> "
        f"{timing.get('end_time_utc', UNSET)} "
        f"host={timing.get('hostname', UNSET)} "
        f"(source: {timing.get('source', UNSET)})",
        f"      issue={row.get('issue')} pr={row.get('pr')} "
        f"before={(row.get('before') or {}).get('run')}",
        "      A correctness: " + " ".join(
            f"{name}={correctness.get(name, 0)}"
            for name in outcome_transition.CORRECTNESS_ORDER
        ),
    ]
    if transition.get("evaluated"):
        notes = transition.get("notes") or {}
        lines.append(
            "      B transition: " + " ".join(
                f"{name}={transition.get(name, 0)}"
                for name in outcome_transition.TRANSITION_ORDER
            )
            + f" changed={transition.get('changed', 0)}"
            + f" decided_but_unconfirmed={notes.get('decided_but_unconfirmed', 0)}"
        )
        lines.append(
            "        reason sets: "
            f"comparable={reason_sets.get('comparable', 0)} "
            f"mismatch={reason_sets.get('reason_set_mismatch', 0)} "
            f"outcome_mismatch={reason_sets.get('outcome_mismatch', 0)} "
            f"incomparable={reason_sets.get('incomparable', 0)}"
        )
    else:
        lines.append(
            f"      B transition: not evaluated ({transition.get('reason', 'no before run')})"
        )
    lines.append(
        "      C gate: soundness=" + str((gate.get("soundness") or {}).get("status", UNSET))
        + " benchmark=" + " ".join(
            f"{name}:{(value or {}).get('gate', UNSET)}"
            for name, value in sorted((gate.get("benchmark") or {}).items())
        )
        + " axis=" + " ".join(
            f"{name}={(gate.get('axis') or {}).get(name, 0)}"
            for name in outcome_transition.GATE_ORDER
        )
    )
    if row.get("note"):
        lines.append(f"      note: {row['note']}")
    return lines


def format_listing(
    rows: Sequence[Mapping[str, Any]],
    head: Mapping[str, Any],
    *,
    ledger_path: Path,
    limit: Optional[int] = None,
) -> str:
    """The ledger, read so that a subset can never be mistaken for a full run.

    The listing names the last run recorded for each full scope, then every run
    recorded after it, and ends with an explicit verdict on whether the current
    HEAD has a complete evaluation behind it.  "there are rows" is never
    printed as "verified".
    """
    dirty = head.get("dirty", GIT_DIRTY_UNKNOWN)
    dirty_text = {
        GIT_DIRTY_NO: "clean", GIT_DIRTY_YES: "dirty", GIT_DIRTY_UNKNOWN: "unknown",
    }.get(dirty, dirty)
    real_rows = [row for row in rows if row.get("schema") == LEDGER_SCHEMA]
    unparsable = len(rows) - len(real_rows)
    lines = [
        f"Verification ledger: {ledger_path} ({len(real_rows)} rows"
        + (f", {unparsable} unreadable" if unparsable else "") + ")",
        f"Current HEAD: {head.get('commit', GIT_STATE_UNAVAILABLE)} "
        f"(source roots: {dirty_text})",
        "",
    ]

    last_full_index: Optional[int] = None
    lines.append("Last run recorded *requesting* each full scope (a request is not evidence):")
    for scope in FULL_SCOPES:
        indexes = [i for i, row in enumerate(real_rows) if row.get("requested_scope") == scope]
        if not indexes:
            lines.append(f"  {scope}: (none recorded)")
            continue
        index = indexes[-1]
        last_full_index = index if last_full_index is None else max(last_full_index, index)
        row = real_rows[index]
        match, _reason = head_match(row, head)
        evidence, evidence_reason = full_scope_evidence(row)
        lines.append(
            f"  {scope}: {row.get('run_dir')} "
            f"completed_scope={row.get('completed_scope')} "
            f"coverage={_coverage_cell(row)} code_matches_head={match}"
            + ("" if match == HEAD_MATCH_YES else "  [stale_code]")
        )
        # "requested" is not "did": say so on the same line as the request.
        lines.append(
            "      whole-benchmark evidence: "
            + ("yes" if evidence is not None else f"NO -- {evidence_reason}")
        )
    lines.append("")

    if last_full_index is None:
        lines.append("Runs recorded (no full-scope run to count from):")
        shown = real_rows
    else:
        lines.append("Runs recorded after the last full-scope run:")
        shown = real_rows[last_full_index + 1:]
    if limit is not None:
        shown = shown[-limit:]
    if not shown:
        lines.append("  (none)")
    for row in shown:
        lines.extend(format_row_lines(row, head))
    lines.append("")
    lines.extend(_format_verdict(real_rows, head))
    return "\n".join(lines) + "\n"


def _format_verdict(
    rows: Sequence[Mapping[str, Any]], head: Mapping[str, Any],
) -> List[str]:
    """The one question the ledger exists to answer, answered explicitly.

    ``YES`` needs two independent things: the run's own artifacts must show it
    really executed that full scope (``full_scope_evidence``), and it must be
    evidence about the code at HEAD (``head_match``).  A request for
    ``--requested-scope full_eq`` on a subset run satisfies neither.
    """
    covered = {}
    for row in rows:
        scope, _reason = full_scope_evidence(row)
        if scope is not None and head_match(row, head)[0] == HEAD_MATCH_YES:
            covered[scope] = row
    lines = ["Has everything been evaluated at the current HEAD?"]
    for scope in FULL_SCOPES:
        if scope in covered:
            lines.append(f"  {scope}: YES ({covered[scope].get('run_dir')})")
        else:
            lines.append(f"  {scope}: NO")
    missing = [scope for scope in FULL_SCOPES if scope not in covered]
    if missing:
        lines.append(
            "  FULL_EQBENCH / FULL_NEQ have not been completely evaluated at this "
            "commit: " + ", ".join(missing) + "."
        )
        lines.append(
            "  Subset verification is not full verification -- a subset row says "
            "nothing about the pairs outside the subset."
        )
        for scope in missing:
            for row in rows:
                if row.get("requested_scope") != scope:
                    continue
                evidence, reason = full_scope_evidence(row)
                if evidence is None:
                    lines.append(
                        f"    {row.get('run_dir')} requested {scope} but is not "
                        f"whole-benchmark evidence: {reason}"
                    )
                elif head_match(row, head)[0] != HEAD_MATCH_YES:
                    lines.append(
                        f"    {row.get('run_dir')} is a complete {scope} run, but "
                        f"{head_match(row, head)[1]}"
                    )
    return lines


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument(
        "--ledger", type=Path, default=DEFAULT_LEDGER,
        help=f"ledger file (default: {DEFAULT_LEDGER})",
    )
    parser.add_argument(
        "--repo-root", type=Path, default=Path("."),
        help="repository whose HEAD a row is compared against",
    )
    commands = parser.add_subparsers(dest="command", required=True)

    record = commands.add_parser("record", help="append one run to the ledger")
    record.add_argument("--run-dir", required=True, type=Path, help="the run directory")
    record.add_argument(
        "--requested-scope", required=True, choices=REQUESTED_SCOPES,
        help="what the run was asked to cover (never guessed from the results)",
    )
    record.add_argument(
        "--before", type=Path, default=None,
        help="run this one is compared against (default: the run's own before_run)",
    )
    record.add_argument("--issue", default=None)
    record.add_argument("--pr", default=None)
    record.add_argument("--note", default=None)
    record.add_argument(
        "--print-row", action="store_true", help="also print the row as JSON",
    )

    listing = commands.add_parser("list", help="show the ledger")
    listing.add_argument(
        "--limit", type=int, default=None, help="show only the last N runs",
    )
    return parser


def main(argv: Optional[Sequence[str]] = None) -> int:
    args = build_parser().parse_args(argv)
    if args.command == "record":
        try:
            row = build_row(
                args.run_dir, requested_scope=args.requested_scope,
                before=args.before, issue=args.issue, pr=args.pr, note=args.note,
            )
            append_row(args.ledger, row)
        except (OSError, ValueError) as exc:
            print(f"error: cannot record {args.run_dir}: {exc}", file=sys.stderr)
            return 1
        if args.print_row:
            print(json.dumps(row, indent=1, sort_keys=True))
        print(
            f"recorded {row['run_dir']} -> {args.ledger} "
            f"(requested_scope={row['requested_scope']} "
            f"completed_scope={row['completed_scope']} "
            f"coverage={_coverage_cell(row)})"
        )
        return 0
    rows = read_rows(args.ledger)
    sys.stdout.write(format_listing(
        rows, git_state(args.repo_root), ledger_path=args.ledger, limit=args.limit,
    ))
    return 0


if __name__ == "__main__":
    sys.exit(main())
