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

# Publication fields that say whether the benchmark *target* survived the run.
# Each was read out of the runners (Eq `eqbench_run_all_32jobs.sh`, Neq
# `neqbench_run_all_32jobs.sh`) rather than assumed:
#
#   function_census_failure_count -- the actual function set diverged from the
#       frozen expectation.  Eq records it and *keeps going* (:1096-1099), so
#       `total_functions`, `total_pair_jobs` and the census are all rebuilt from
#       the reduced set and stay self-consistent; Neq drops the sample outright
#       (:671-676).  Either way part of the benchmark was not evaluated.
#   compile_failure_count -- a sample (Eq :1241) or a variant (Neq :685/:695)
#       did not build, and its pairs were never run.
#   missing_binary_count -- an axis binary is absent (Eq :1232-1239, Neq via
#       `record_missing_variant_axes`), so pairs over it cannot be formed.
#   run_pair_failures -- a pair job exited non-zero, i.e. failed canonical
#       classification or a run-health check (`pair_scheduler.sh:200-202`, and
#       the runner's own message at Eq :1484).  A TIMEOUT or ERROR *outcome*
#       does not bump it: the fixed subset carries 5 such pairs with
#       run_pair_failures=0.  So a non-zero value means a pair nobody could
#       evaluate, not a pair that was evaluated and came out badly.
#
# The benchmark gate is deliberately absent from this list: it lives in
# `VALIDATION_BENCHMARK_GATE_FAILURES` / `benchmark_gate_failures`, which is not
# a publication manifest field at all.  Coverage ("did we run everything?") and
# the gate ("is what we got sound?") stay separate axes.
SCOPE_HEALTH_COUNTERS = (
    ("function_census_failure_count", "function_census_failures"),
    ("compile_failure_count", "compile_failure_samples"),
    ("missing_binary_count", "missing_binary_axes"),
    ("run_pair_failures", None),
)
# Accounting that must close for a run that covered the whole benchmark.  Each
# identity was checked against the one real full run and against healthy runs of
# both runners before being adopted.
SCOPE_HEALTH_ACCOUNTING_KEYS = (
    "target_sources", "completed_samples", "skipped_samples",
    "expected_binary_count", "compiled_binary_count",
    "total_functions", "expected_pairs_per_function", "total_pair_jobs",
    "total_scheduled_pair_jobs", "total_skipped_pair_jobs", "dry_run",
)
SCOPE_HEALTH_OK = "ok"
SCOPE_HEALTH_FAILED = "failed"
SCOPE_HEALTH_UNKNOWN = "unknown"
EXECUTION_RECEIPT_FILE = "validation-execution-receipt.json"
PAIR_STATUS_PUBLIC_KEY_FILE = "pair-status-verification-key.json"
BINDING_OK = "ok"
BINDING_FAILED = "failed"
# `run_manifest.txt` keys that must repeat what the signed artifacts say.  These
# are the three the publication itself is built from, so a manifest left over
# from a different execution cannot agree with them by accident.
RUN_MANIFEST_BINDING_KEYS = (
    ("analysis_config_digest", "analysis_config_digest"),
    ("analysis_source_digest_start", "analysis_source_digest_start"),
    ("analysis_source_digest_end", "analysis_source_digest_end"),
)
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
    """Whether each result tree is a formally published whole-benchmark run.

    ``requested_scope`` is what somebody asked for; it is not evidence.  What
    counts is whether the tree carries a ``matrix-publication-manifest.json``
    that satisfies the repository's own publication artifact contract --
    checked by calling the owning validator,
    ``execution_receipt.validate_matrix_publication_manifest``, rather than by
    re-implementing a few of its field checks here.  That validator already
    binds the whole artifact together: the exact field set, the schema tag, the
    ``run_scope`` and its agreement with ``analysis_config.run_scope``, the
    ``analysis_config_digest`` over that config, the ``artifact_digest`` over
    the body, and the typed analysis config itself.

    Nothing is inferred from a source that is absent.  A missing manifest, a
    missing ``run_scope`` in ``run_manifest.txt``, a disagreement between the
    two, or filters that cannot be read from the validated config are each a
    recorded *failure reason* -- never a field quietly dropped from the
    comparison.
    """
    trees: Dict[str, Any] = {}
    for name, tree in zip(layout.tree_names, layout.trees):
        trees[name] = _tree_scope_evidence(tree)
    scopes = {row["whole_benchmark_scope"] for row in trees.values()}
    return {
        "trees": trees,
        # One agreed scope only when every tree established the same one.
        "whole_benchmark_scope": (
            scopes.pop() if len(scopes) == 1 and None not in scopes else None
        ),
        "declared_run_scope": _agreed_field(
            [{"run_scope": row["declared_run_scope"]} for row in trees.values()],
            "run_scope",
        ) if trees else UNSET,
    }


def _tree_scope_evidence(tree: Path) -> Dict[str, Any]:
    """One tree's scope evidence: the validated scope, or why there is none."""
    run_manifest = read_key_value_manifest(tree / RUN_MANIFEST_FILE)
    run_manifest_scope = run_manifest.get("run_scope") or UNSET
    publication, failure = _formally_published_manifest(tree)
    row: Dict[str, Any] = {
        "whole_benchmark_scope": None,
        "failure_reason": failure,
        "formal_publication": "valid" if publication is not None else failure,
        "run_manifest_run_scope": run_manifest_scope,
        "publication_run_scope": UNSET,
        "analysis_config_run_scope": UNSET,
        "declared_run_scope": run_manifest_scope,
        "narrowed": None,
    }
    if publication is None:
        return row
    config = publication["analysis_config"]
    # The validator guarantees these exist, are strings, and agree with each
    # other; they are read back so the row records what was actually checked.
    row["publication_run_scope"] = publication["run_scope"]
    row["analysis_config_run_scope"] = config["run_scope"]
    row["narrowed"] = _config_narrowed(config)
    row["narrowing_agrees_with_run_manifest"] = _run_manifest_filters_agree(
        run_manifest, config)
    row["pairs_declared"], row["pairs_in_census"] = _declared_and_published_extent(
        publication)
    row["scope_health"] = scope_health(publication)
    row["execution_binding"] = execution_binding(tree, publication)
    # The three sources are compared directly rather than through
    # _agreed_field(), which ignores a source whose value is empty.  Here an
    # absent value must be a reason to say no, not one fewer source to agree.
    sources = (run_manifest_scope, publication["run_scope"], config["run_scope"])
    declared = sources[0] if len(set(sources)) == 1 else MISMATCH
    row["declared_run_scope"] = declared
    if run_manifest_scope == UNSET:
        row["failure_reason"] = f"{RUN_MANIFEST_FILE} records no run_scope"
        return row
    if declared == MISMATCH:
        row["failure_reason"] = (
            f"run_scope differs across sources: {RUN_MANIFEST_FILE}="
            f"{run_manifest_scope} {PUBLICATION_MANIFEST_FILE}="
            f"{publication['run_scope']} analysis_config={config['run_scope']}"
        )
        return row
    if row["narrowed"] is not False:
        row["failure_reason"] = (
            "the published analysis config narrowed the run "
            "(sample_filter / pair_filter / max_samples)"
        )
        return row
    if row["narrowing_agrees_with_run_manifest"] is not True:
        row["failure_reason"] = (
            f"the filters in {RUN_MANIFEST_FILE} are absent or disagree with the "
            f"published analysis config"
        )
        return row
    pairs_declared, census = row["pairs_declared"], row["pairs_in_census"]
    if pairs_declared is None or census is None:
        row["failure_reason"] = (
            "the published manifest does not state how many pairs a whole "
            "benchmark run covers"
        )
        return row
    if census != pairs_declared:
        # The scope and the filters can both look whole-benchmark while the
        # published pair census covers only a slice -- a rerun manifest, say,
        # which no typed config field models.  The manifest contradicts itself
        # in that case, and a contradiction is never evidence.
        row["failure_reason"] = (
            f"the published pair census covers {census} of the {pairs_declared} pairs "
            f"the manifest itself declares (total_functions x "
            f"expected_pairs_per_function)"
        )
        return row
    binding = row["execution_binding"]
    if binding["status"] != BINDING_OK:
        # Each artifact can be individually valid while belonging to a
        # different run than the one next to it.  Current provenance plus a
        # previous run's coverage is not evidence about either.
        row["failure_reason"] = (
            f"execution binding {binding['status']}: {binding['failure_reason']}"
        )
        return row
    health = row["scope_health"]
    if health["status"] != SCOPE_HEALTH_OK:
        # The artifact is well-formed and internally consistent, but its own
        # failure counters or accounting say the benchmark target shrank while
        # the run was going.  A run that lost part of its target did not verify
        # the whole benchmark, however complete the remainder looks.
        row["failure_reason"] = f"scope health {health['status']}: {health['failure_reason']}"
        return row
    row["failure_reason"] = None
    row["whole_benchmark_scope"] = declared
    return row


def _formally_published_manifest(
    tree: Path,
) -> Tuple[Optional[Mapping[str, Any]], Optional[str]]:
    """``(manifest, None)`` when the tree's publication artifact is valid.

    Validity is decided by the artifact's owner
    (``execution_receipt.validate_matrix_publication_manifest``), so the ledger
    reads only artifacts that authority already considers well-formed instead
    of minting a second, weaker contract of its own.  The ledger stays a
    measurement aid: it never signs, repairs, or relaxes anything.
    """
    from scripts.function_tracer_pcode.reporting.execution_receipt import (
        validate_matrix_publication_manifest,
    )

    path = tree / PUBLICATION_MANIFEST_FILE
    if not path.is_file():
        return None, f"no {PUBLICATION_MANIFEST_FILE}"
    try:
        payload = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, ValueError) as exc:
        return None, f"unreadable {PUBLICATION_MANIFEST_FILE}: {exc}"
    try:
        validate_matrix_publication_manifest(payload)
    except ValueError as exc:
        return None, f"{PUBLICATION_MANIFEST_FILE} fails the publication contract: {exc}"
    except TypeError as exc:
        # A malformed artifact can make the validator's own set/hash work
        # raise (an unhashable census entry, say).  That is bad data, not a
        # bug in this module, so it is reported like any other rejection --
        # and nothing broader is caught, so real defects still surface.
        return None, f"{PUBLICATION_MANIFEST_FILE} is malformed: {exc}"
    return payload, None


def _run_manifest_filters_agree(
    run_manifest: Mapping[str, str], config: Mapping[str, Any],
) -> Optional[bool]:
    """Whether ``run_manifest.txt``'s own filters match the published config.

    The publication manifest is built *from* the run manifest, so the two
    should say the same thing; if they do not, one of them is not describing
    this run and neither can be trusted.  A filter the run manifest does not
    record keeps the answer ``None`` -- the source is not dropped from the
    comparison just because it is silent.
    """
    for key in NARROWING_FILTER_KEYS:
        if key not in run_manifest or not isinstance(config.get(key), str):
            return None
        if run_manifest[key] != config[key]:
            return False
    if NARROWING_LIMIT_KEY not in run_manifest or type(config.get(NARROWING_LIMIT_KEY)) is not int:
        return None
    try:
        if int(run_manifest[NARROWING_LIMIT_KEY]) != config[NARROWING_LIMIT_KEY]:
            return False
    except ValueError:
        return None
    return True


def execution_binding(
    tree: Path, publication: Mapping[str, Any],
) -> Dict[str, Any]:
    """Whether this tree's three artifacts describe one and the same execution.

    A result directory can be reused across runs, and the artifacts in it are
    written at different moments: the run manifest early, the publication and
    the signed receipt at the end.  A run that is interrupted after rewriting
    `run_manifest.txt` but before republishing therefore leaves one execution's
    publication and receipt beside another execution's manifest -- and every
    other check here would pass, because each artifact is individually valid.
    Current provenance would then be read off the new manifest while the
    coverage came from the old run.

    So the receipt is validated by its owner
    (``execution_receipt.validate_execution_receipt``, against the tree's own
    ``pair-status-verification-key.json``), bound to the publication by the
    shared predicate ``matrix_execution_binding_mismatch``, and the run manifest
    is required to repeat the same analysis-config and source-tree digests.
    Anything missing, unreadable or disagreeing fails closed with a reason.

    ``exit_status`` is deliberately not consulted: the runners fold benchmark
    gate failures into their exit code, and coverage must not be lost because
    the gate found something.  The receipt is used here only to prove which
    execution these artifacts came from.
    """
    from scripts.function_tracer_pcode.reporting.execution_receipt import (
        matrix_execution_binding_mismatch,
        validate_execution_receipt,
    )

    row: Dict[str, Any] = {
        "status": BINDING_FAILED, "failure_reason": None,
        "receipt": UNSET, "run_manifest": UNSET,
    }
    receipt_path = tree / EXECUTION_RECEIPT_FILE
    key_path = tree / PAIR_STATUS_PUBLIC_KEY_FILE
    if not receipt_path.is_file():
        row["failure_reason"] = f"no {EXECUTION_RECEIPT_FILE}"
        return row
    if not key_path.is_file():
        row["failure_reason"] = f"no {PAIR_STATUS_PUBLIC_KEY_FILE} to verify the receipt"
        return row
    try:
        receipt = validate_execution_receipt(
            json.loads(receipt_path.read_text(encoding="utf-8")),
            public_key_path=key_path,
        )
    except (OSError, ValueError) as exc:
        row["failure_reason"] = f"{EXECUTION_RECEIPT_FILE} is not a valid receipt: {exc}"
        return row
    row["receipt"] = "valid"
    mismatch = matrix_execution_binding_mismatch(
        tree / PUBLICATION_MANIFEST_FILE, publication, receipt,
    )
    if mismatch is not None:
        row["failure_reason"] = mismatch
        return row
    run_manifest = read_key_value_manifest(tree / RUN_MANIFEST_FILE)
    for manifest_key, publication_key in RUN_MANIFEST_BINDING_KEYS:
        recorded = run_manifest.get(manifest_key)
        if not recorded:
            row["failure_reason"] = f"{RUN_MANIFEST_FILE} records no {manifest_key}"
            return row
        if recorded != publication[publication_key]:
            row["failure_reason"] = (
                f"{RUN_MANIFEST_FILE} {manifest_key} ({recorded}) differs from the "
                f"published {publication_key} ({publication[publication_key]}): the "
                "manifest and the signed artifacts are from different executions"
            )
            return row
    row["run_manifest"] = "bound"
    row["status"] = BINDING_OK
    return row


def scope_health(publication: Mapping[str, Any]) -> Dict[str, Any]:
    """Whether the benchmark target survived the run, from the manifest itself.

    "Well-formed artifact" and "evaluated the whole benchmark without losing
    part of the target" are different claims.  The formal validator settles the
    first; this settles the second, using the failure counters and the
    accounting the same validated manifest already carries.

    The failure that motivates it: an Eq function-census failure records the
    divergence and lets the run continue, so ``total_functions``, the pair count
    and the census are all rebuilt from the *reduced* function set.  Every
    self-consistency check then passes -- 99 functions x 120 pairs, all statuses
    present, ``complete`` -- while a hundredth function was never evaluated.

    ``unknown`` (not ``ok``) whenever a field needed to answer is missing or not
    an integer: an unanswerable question is never an affirmative answer.
    """
    numbers: Dict[str, Any] = {}
    for key in SCOPE_HEALTH_ACCOUNTING_KEYS:
        value = publication.get(key)
        if type(value) is not int:
            return {
                "status": SCOPE_HEALTH_UNKNOWN,
                "failure_reason": f"the published manifest has no usable {key}",
                "failures": {}, "accounting": numbers,
            }
        numbers[key] = value
    failures: Dict[str, int] = {}
    for counter, _listing in SCOPE_HEALTH_COUNTERS:
        value = publication.get(counter)
        if type(value) is not int:
            return {
                "status": SCOPE_HEALTH_UNKNOWN,
                "failure_reason": f"the published manifest has no usable {counter}",
                "failures": failures, "accounting": numbers,
            }
        failures[counter] = value

    def failed(reason: str) -> Dict[str, Any]:
        return {
            "status": SCOPE_HEALTH_FAILED, "failure_reason": reason,
            "failures": failures, "accounting": numbers,
        }

    if numbers["dry_run"]:
        return failed("the run was a dry run, so no pair was evaluated")
    for counter, listing in SCOPE_HEALTH_COUNTERS:
        if not failures[counter]:
            continue
        detail = ""
        rows = publication.get(listing) if listing else None
        if isinstance(rows, list) and rows:
            shown = ", ".join(str(row) for row in rows[:3])
            detail = f" ({shown}{', ...' if len(rows) > 3 else ''})"
        return failed(
            f"{counter}={failures[counter]}{detail}: part of the benchmark target "
            "was not evaluated"
        )
    if numbers["completed_samples"] + numbers["skipped_samples"] != numbers["target_sources"]:
        return failed(
            f"{numbers['completed_samples']} completed + "
            f"{numbers['skipped_samples']} skipped samples do not account for the "
            f"{numbers['target_sources']} the run targeted"
        )
    if not numbers["expected_binary_count"] or (
        numbers["compiled_binary_count"] != numbers["expected_binary_count"]
    ):
        return failed(
            f"{numbers['compiled_binary_count']} of "
            f"{numbers['expected_binary_count']} expected binaries were built"
        )
    if (
        numbers["total_scheduled_pair_jobs"] + numbers["total_skipped_pair_jobs"]
        != numbers["total_pair_jobs"]
    ):
        return failed(
            f"{numbers['total_scheduled_pair_jobs']} scheduled + "
            f"{numbers['total_skipped_pair_jobs']} reused pair jobs do not account "
            f"for the {numbers['total_pair_jobs']} the run expected"
        )
    return {
        "status": SCOPE_HEALTH_OK, "failure_reason": None,
        "failures": failures, "accounting": numbers,
    }


def _declared_and_published_extent(
    publication: Mapping[str, Any],
) -> Tuple[Optional[int], Optional[int]]:
    """``(pairs a whole run covers, pairs the census actually lists)``.

    Both numbers come from the already-validated manifest: the extent it
    declares (``total_functions`` x ``expected_pairs_per_function``) and the
    census it published.  Either being unreadable yields ``None``, which is
    never read as agreement.
    """
    functions = publication.get("total_functions")
    per_function = publication.get("expected_pairs_per_function")
    jobs = publication.get("total_pair_jobs")
    census = publication.get("expected_pair_status_paths")
    if any(type(value) is not int for value in (functions, per_function, jobs)):
        return None, None
    if not isinstance(census, list) or len(census) != jobs:
        return None, None
    return functions * per_function, len(census)


def _config_narrowed(config: Mapping[str, Any]) -> Optional[bool]:
    """Whether the *validated* analysis config shows a narrowed run.

    Only the formal config is consulted: it has passed
    ``validate_analysis_config``, so the filter fields are known to be present
    and correctly typed.  ``None`` means the question could not be answered,
    which is never read as "not narrowed".
    """
    for key in NARROWING_FILTER_KEYS:
        value = config.get(key)
        if not isinstance(value, str):
            return None
        if value:
            return True
    limit = config.get(NARROWING_LIMIT_KEY)
    if type(limit) is not int:
        return None
    return limit > 0


def full_scope_evidence(row: Mapping[str, Any]) -> Tuple[Optional[str], str]:
    """``(full scope this row really covers, reason)`` -- artifacts only.

    A row supports a full verdict only when every one of these holds, so that
    no request and no self-declared field can manufacture one:

    * the run is a single whole-benchmark matrix tree -- a subset run's
      ``eq``/``neq`` halves are by construction not one, whatever was
      requested;
    * that tree's ``matrix-publication-manifest.json`` satisfies the
      repository's publication artifact contract in full, as judged by the
      validator that owns it (which also binds ``run_scope``,
      ``analysis_config``, ``analysis_config_digest`` and ``artifact_digest``
      together);
    * ``run_manifest.txt`` records a ``run_scope`` and it agrees with the
      published one;
    * the validated analysis config shows no ``sample_filter`` /
      ``pair_filter`` / ``max_samples`` narrowing;
    * the recorded scope matches the requested full scope;
    * the run is complete by the publication manifest's own pair census.

    Anything absent, malformed, disagreeing or simply uncheckable is a reason
    to say no.  Whether the row is evidence about the code at *HEAD* is a
    separate question, answered by ``head_match``.
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
    trees = evidence.get("trees") or {}
    if not trees:
        return None, "the run has no result tree to read a published scope from"
    for name, tree in sorted(trees.items()):
        reason = tree.get("failure_reason")
        if reason or not tree.get("whole_benchmark_scope"):
            return None, reason or "no formally published whole-benchmark scope"
    scope = evidence.get("whole_benchmark_scope")
    expected = RUN_SCOPE_BY_FULL_SCOPE[requested]
    if scope != expected:
        return None, f"the published run_scope is {scope or UNSET}, not {expected}"
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


def _run_exit_status(layout: RunLayout) -> Dict[str, Any]:
    """The run's own exit status, as a diagnostic only.

    A subset run records it directly; a matrix run does not, so it is read back
    from the signed execution receipt it already writes.  **It is deliberately
    not a scope condition**: the runners exit non-zero when
    ``VALIDATION_BENCHMARK_GATE_FAILURES`` is non-zero too (Eq :1431, Neq :818),
    so a run that executed every pair and then failed the benchmark gate would
    lose its coverage fact along with its gate verdict.  Coverage is decided by
    ``scope_health``; the gate is the separate C axis.  Reading the receipt here
    does not make it an authority for anything -- nothing is verified or
    re-signed, only reported.
    """
    recorded = layout.subset_manifest.get("exit_status")
    if recorded not in (None, ""):
        return {"status": recorded, "source": SUBSET_MANIFEST_FILE}
    statuses = {}
    for name, tree in zip(layout.tree_names, layout.trees):
        receipt = _read_json(tree / EXECUTION_RECEIPT_FILE) or {}
        value = receipt.get("exit_status")
        statuses[name] = str(value) if type(value) is int else UNSET
    if not statuses:
        return {"status": UNSET, "source": "absent"}
    distinct = set(statuses.values())
    return {
        "status": distinct.pop() if len(distinct) == 1 else MISMATCH,
        "source": EXECUTION_RECEIPT_FILE,
        "trees": statuses,
        "note": "diagnostic only; a non-zero status also covers benchmark gate failures",
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
        "run_exit_status": _run_exit_status(layout),
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


def _scope_health_cell(row: Mapping[str, Any]) -> str:
    """``ok`` / ``failed(counter=n)`` / ``unknown`` per tree, for the listing.

    The counter that decided a ``failed`` is named inline so a ``full_eq: NO``
    can be traced to the number behind it without reopening the run directory.
    """
    trees = ((row.get("scope_evidence") or {}).get("trees") or {})
    cells = []
    for name, tree in sorted(trees.items()):
        health = (tree or {}).get("scope_health") or {}
        status = health.get("status", UNSET)
        if status == SCOPE_HEALTH_FAILED:
            offending = [
                f"{counter}={value}"
                for counter, value in sorted((health.get("failures") or {}).items())
                if value
            ]
            status = f"failed({', '.join(offending)})" if offending else "failed"
        cells.append(status if len(trees) == 1 else f"{name}:{status}")
    return " ".join(cells) if cells else UNSET


def _binding_cell(row: Mapping[str, Any]) -> str:
    """``ok`` / ``failed`` per tree; the reason follows on its own line."""
    trees = ((row.get("scope_evidence") or {}).get("trees") or {})
    cells = []
    for name, tree in sorted(trees.items()):
        status = ((tree or {}).get("execution_binding") or {}).get("status", UNSET)
        cells.append(status if len(trees) == 1 else f"{name}:{status}")
    return " ".join(cells) if cells else UNSET


def _binding_reasons(row: Mapping[str, Any]) -> List[str]:
    """One line per tree whose artifacts do not agree on their execution."""
    trees = ((row.get("scope_evidence") or {}).get("trees") or {})
    lines = []
    for name, tree in sorted(trees.items()):
        binding = (tree or {}).get("execution_binding") or {}
        if binding.get("status") in (None, BINDING_OK):
            continue
        if binding.get("failure_reason"):
            lines.append(f"        execution binding ({name}): {binding['failure_reason']}")
    return lines


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
        f"scope_health={_scope_health_cell(row)} "
        f"execution_binding={_binding_cell(row)} "
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
    lines.extend(_binding_reasons(row))
    if row.get("note"):
        lines.append(f"      note: {row['note']}")
    return lines


def _supporting_indexes(
    rows: Sequence[Mapping[str, Any]], head: Mapping[str, Any],
) -> Dict[str, int]:
    """``scope -> index`` of the latest row that actually supports a full verdict.

    Computed once and used by both the verdict and the detail listing, so the
    row a ``YES`` rests on can never be a different row from the one printed.
    """
    supporting: Dict[str, int] = {}
    for index, row in enumerate(rows):
        scope, _reason = full_scope_evidence(row)
        if scope is not None and head_match(row, head)[0] == HEAD_MATCH_YES:
            supporting[scope] = index
    return supporting


def _requesting_indexes(rows: Sequence[Mapping[str, Any]]) -> Dict[str, int]:
    """``scope -> index`` of the latest row that merely *requested* each scope."""
    requesting: Dict[str, int] = {}
    for index, row in enumerate(rows):
        if row.get("requested_scope") in FULL_SCOPES:
            requesting[row["requested_scope"]] = index
    return requesting


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

    requesting = _requesting_indexes(real_rows)
    supporting = _supporting_indexes(real_rows, head)
    # Both the latest request for a scope and the latest row that actually
    # supports it are kept: they are often the same row, and when they are not,
    # a reader needs to see both -- the one that was asked for, and the one the
    # verdict is built on.
    latest_full: Dict[str, int] = dict(requesting)
    lines.append("Last run recorded *requesting* each full scope (a request is not evidence):")
    for scope in FULL_SCOPES:
        if scope not in requesting:
            lines.append(f"  {scope}: (none recorded)")
            continue
        index = requesting[scope]
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

    for scope, index in supporting.items():
        latest_full[f"{scope}:evidence"] = index
    if not latest_full:
        lines.append("Runs recorded (no full-scope run to count from):")
        indexes = list(range(len(real_rows)))
    else:
        # Every scope's latest candidate is shown in full, not just the most
        # recent one: `full_eq` and `full_neq` are answered separately, so the
        # digests and timing behind *each* answer have to be readable.  The
        # runs recorded after the newest of them follow, and an index appears
        # once however many of those sets it belongs to.
        lines.append(
            "The latest run requesting each full scope, and every run recorded "
            "after the newest of them:"
        )
        indexes = sorted(
            set(latest_full.values()) | set(range(max(latest_full.values()), len(real_rows)))
        )
    if limit is not None:
        # The latest candidate for each full scope is always kept: --limit
        # trims the trailing verification runs, never the evidence the verdict
        # above is built from.
        keep = set(latest_full.values())
        trailing = [index for index in indexes if index not in keep]
        indexes = sorted(keep | set(trailing[-limit:]))
    if not indexes:
        lines.append("  (none)")
    for index in indexes:
        lines.extend(format_row_lines(real_rows[index], head))
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
    supporting = _supporting_indexes(rows, head)
    covered = {scope: rows[index] for scope, index in supporting.items()}
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
            # Only the most recent request for each scope is explained: older
            # ones say nothing new and would bury the verdict.
            requesting = [row for row in rows if row.get("requested_scope") == scope]
            if not requesting:
                continue
            row = requesting[-1]
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
