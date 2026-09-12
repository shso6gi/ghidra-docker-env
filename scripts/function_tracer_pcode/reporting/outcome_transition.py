# -*- coding: utf-8 -*-
"""Function x pair outcome transition table between two result trees.

Usage::

    python3 -m scripts.function_tracer_pcode.reporting.outcome_transition \
        --before logs/EqBench/subset_before --after logs/EqBench/subset_after \
        [--json transition.json] [--changed-only] [--fail-on-change] \
        [--axes] [--reason-sets] [--manifest] [--runtime-metrics]

The table counts how many pairs moved from each outcome in ``--before`` to
each outcome in ``--after``; pairs present in only one tree are reported as
``MISSING`` on the other side. It says nothing about which side is correct.

Issue #20: an assumption-dependent (conditional) result is reported in its own
matrix, never mixed into the unconditional one, and ``NONE`` marks a pair with
no conditional decision on that side.  ``--fail-on-change`` keeps its
unconditional meaning exactly; ``--fail-on-conditional-change`` is the separate
switch for the conditional matrix.  A run in which no pair carries a
conditional decision prints and serializes exactly what it did before.

Issue #123 / PR-123-B adds four opt-in sections.  They are opt-in so that the
default invocation prints and serializes exactly what it did before, and none
of them can move ``--fail-on-change``:

``--axes``
    The three independent axes of EPIC #130, never folded into one verdict:
    **correctness** (does a benchmark ground truth confirm this decision?),
    **transition** (what did this pair do between the two runs?) and **gate**
    (what does ``benchmark_validation_gate`` say?).  A decision nothing can
    confirm is ``unconfirmed`` and is counted as ``decided_but_unconfirmed``,
    never as an improvement -- most ``Neq`` ``NOT_EQ`` results are in that
    bucket, because their reviewed ground truth is ``UNKNOWN``.
``--reason-sets``
    The final UNKNOWN reason-id set of every pair, compared between the runs.
    A pair whose result payload cannot be read on either side is
    ``incomparable`` and is counted on its own -- never as a match.
``--manifest``
    Completeness against each side's own ``matrix-publication-manifest.json``
    (``expected_pair_status_paths`` minus what is actually on disk).  Missing
    or unreadable manifest, missing pairs, or pairs the run only reused from an
    earlier run (``verified_skipped_pair_status_paths``) all keep the tree from
    being called ``complete``.
``--runtime-metrics``
    Wall-clock deltas from ``.runtime-metrics/<pair>.runtime.json``.  Purely
    informational: it never changes an exit code, it reports how much of each
    tree it could actually see, and a pair without a receipt is never read as
    zero seconds.
"""

from __future__ import annotations

import argparse
import json
import statistics
import sys
from collections import Counter
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Dict, List, Mapping, Optional, Sequence, Tuple

from scripts.function_tracer_pcode.reporting.pair_outcomes import (
    LABEL_EQ,
    LABEL_NEQ,
    OUTCOME_MISSING,
    OUTCOME_ORDER,
    PAIR_STATUS_SUFFIX,
    PairKey,
    PairOutcome,
    benchmark_label,
    load_pair_outcomes,
)

# The conditional axis of a pair that has no conditional decision on one side.
CONDITIONAL_NONE = "NONE"
CONDITIONAL_OUTCOME_ORDER = OUTCOME_ORDER + (CONDITIONAL_NONE,)


@dataclass(frozen=True)
class TransitionRow:
    sample_identity: str
    function_name: str
    pair_id: str
    before: str
    after: str
    conditional_before: str = CONDITIONAL_NONE
    conditional_after: str = CONDITIONAL_NONE

    @property
    def changed(self) -> bool:
        return self.before != self.after

    @property
    def has_conditional(self) -> bool:
        """True when at least one side actually carries a conditional result."""
        return any(
            value not in (CONDITIONAL_NONE, OUTCOME_MISSING)
            for value in (self.conditional_before, self.conditional_after)
        )

    @property
    def conditional_changed(self) -> bool:
        return self.conditional_before != self.conditional_after

    def as_dict(self) -> Dict[str, object]:
        return {
            "sample_identity": self.sample_identity,
            "function_name": self.function_name,
            "pair_id": self.pair_id,
            "before": self.before,
            "after": self.after,
            "changed": self.changed,
        }

    def as_conditional_dict(self) -> Dict[str, object]:
        return {
            "sample_identity": self.sample_identity,
            "function_name": self.function_name,
            "pair_id": self.pair_id,
            "before": self.conditional_before,
            "after": self.conditional_after,
            "changed": self.conditional_changed,
        }


@dataclass(frozen=True)
class TransitionReport:
    rows: Tuple[TransitionRow, ...]

    @property
    def matrix(self) -> Counter:
        return Counter((row.before, row.after) for row in self.rows)

    @property
    def changed_rows(self) -> Tuple[TransitionRow, ...]:
        return tuple(row for row in self.rows if row.changed)

    @property
    def outcomes(self) -> Tuple[str, ...]:
        seen = {row.before for row in self.rows} | {row.after for row in self.rows}
        ordered = [name for name in OUTCOME_ORDER if name in seen]
        ordered.extend(sorted(seen - set(OUTCOME_ORDER)))
        return tuple(ordered)

    @property
    def conditional_rows(self) -> Tuple[TransitionRow, ...]:
        """Rows where either side carries an assumption-dependent result."""
        return tuple(row for row in self.rows if row.has_conditional)

    @property
    def conditional_matrix(self) -> Counter:
        return Counter(
            (row.conditional_before, row.conditional_after)
            for row in self.conditional_rows
        )

    @property
    def conditional_changed_rows(self) -> Tuple[TransitionRow, ...]:
        return tuple(row for row in self.conditional_rows if row.conditional_changed)

    @property
    def conditional_outcomes(self) -> Tuple[str, ...]:
        seen = {row.conditional_before for row in self.conditional_rows}
        seen |= {row.conditional_after for row in self.conditional_rows}
        ordered = [name for name in CONDITIONAL_OUTCOME_ORDER if name in seen]
        ordered.extend(sorted(seen - set(CONDITIONAL_OUTCOME_ORDER)))
        return tuple(ordered)

    def as_dict(self) -> Dict[str, object]:
        payload: Dict[str, object] = {
            "pairs": len(self.rows),
            "changed": len(self.changed_rows),
            "outcomes": list(self.outcomes),
            "matrix": [
                {"before": before, "after": after, "count": count}
                for (before, after), count in sorted(self.matrix.items())
            ],
            "rows": [row.as_dict() for row in self.rows],
        }
        # The conditional section appears only when a run produced one, so a
        # transition report without the lane is byte-identical to before.
        if self.conditional_rows:
            payload["conditional"] = self.as_conditional_dict()
        return payload

    def as_conditional_dict(self) -> Dict[str, object]:
        return {
            "pairs": len(self.conditional_rows),
            "changed": len(self.conditional_changed_rows),
            "outcomes": list(self.conditional_outcomes),
            "matrix": [
                {"before": before, "after": after, "count": count}
                for (before, after), count in sorted(self.conditional_matrix.items())
            ],
            "rows": [row.as_conditional_dict() for row in self.conditional_rows],
        }


def _conditional_axis(record: Optional[PairOutcome]) -> str:
    if record is None:
        return OUTCOME_MISSING
    return record.conditional_outcome or CONDITIONAL_NONE


def build_transition(
    before: Dict[PairKey, PairOutcome],
    after: Dict[PairKey, PairOutcome],
) -> TransitionReport:
    rows: List[TransitionRow] = []
    for key in sorted(set(before) | set(after)):
        sample_identity, function_name, left_id, right_id = key
        rows.append(
            TransitionRow(
                sample_identity=sample_identity,
                function_name=function_name,
                pair_id=f"{left_id}_{right_id}",
                before=before[key].outcome if key in before else OUTCOME_MISSING,
                after=after[key].outcome if key in after else OUTCOME_MISSING,
                conditional_before=_conditional_axis(before.get(key)),
                conditional_after=_conditional_axis(after.get(key)),
            )
        )
    return TransitionReport(rows=tuple(rows))


def format_transition(report: TransitionReport, changed_only: bool = False) -> str:
    outcomes = report.outcomes
    matrix = report.matrix
    width = max([len("before \\ after")] + [len(name) for name in outcomes])
    lines = [
        f"Pairs compared: {len(report.rows)} (changed: {len(report.changed_rows)})",
        "",
        "Outcome transition matrix (rows: before, columns: after):",
    ]
    header = "before \\ after".ljust(width) + "".join(name.rjust(width + 2) for name in outcomes)
    lines.append(header)
    for before in outcomes:
        cells = "".join(str(matrix.get((before, after), 0)).rjust(width + 2) for after in outcomes)
        lines.append(before.ljust(width) + cells)
    lines.append("")
    rows = report.changed_rows if changed_only else report.rows
    lines.append("Changed pairs:" if changed_only else "Pairs:")
    if not rows:
        lines.append("  (none)")
    for row in rows:
        marker = "*" if row.changed else " "
        lines.append(
            f"  {marker} {row.sample_identity} {row.function_name} {row.pair_id}: "
            f"{row.before} -> {row.after}"
        )
    lines.extend(_format_conditional_transition(report, changed_only=changed_only))
    return "\n".join(lines) + "\n"


def _format_conditional_transition(
    report: TransitionReport, *, changed_only: bool = False,
) -> List[str]:
    """Render the assumption-dependent matrix, and only when a run has one."""
    conditional_rows = report.conditional_rows
    if not conditional_rows:
        return []
    outcomes = report.conditional_outcomes
    matrix = report.conditional_matrix
    width = max([len("before \\ after")] + [len(name) for name in outcomes])
    lines = [
        "",
        "Conditional (assumption-dependent) results, reported separately:",
        f"Pairs with a conditional result: {len(conditional_rows)} "
        f"(changed: {len(report.conditional_changed_rows)})",
        "",
        "Conditional transition matrix (rows: before, columns: after):",
        "before \\ after".ljust(width) + "".join(
            name.rjust(width + 2) for name in outcomes
        ),
    ]
    for before in outcomes:
        lines.append(before.ljust(width) + "".join(
            str(matrix.get((before, after), 0)).rjust(width + 2) for after in outcomes
        ))
    lines.append("")
    rows = report.conditional_changed_rows if changed_only else conditional_rows
    lines.append("Changed conditional pairs:" if changed_only else "Conditional pairs:")
    if not rows:
        lines.append("  (none)")
    for row in rows:
        marker = "*" if row.conditional_changed else " "
        lines.append(
            f"  {marker} {row.sample_identity} {row.function_name} {row.pair_id}: "
            f"{row.conditional_before} -> {row.conditional_after}"
        )
    return lines

# --------------------------------------------------------------------------
# Issue #123 / PR-123-B: the three independent axes of EPIC #130.
#
# A pair carries three separate facts and they are deliberately never folded
# into one verdict:
#
#   A. correctness -- did a benchmark ground truth confirm this decision?
#   B. transition  -- what did this pair do between the two runs?
#   C. gate        -- what does ``benchmark_validation_gate`` say about it?
#
# "the outcome changed", "the outcome is right" and "the gate passed" are three
# different claims.  A gate PASS is the absence of a detected violation, not
# evidence that a decision is correct, and a ``Neq`` ``NOT_EQ`` whose reviewed
# ground truth is ``UNKNOWN`` stays ``unconfirmed`` on axis A no matter how
# many gates it passes.
# --------------------------------------------------------------------------

CORRECTNESS_CONSISTENT = "confirmed_consistent"
CORRECTNESS_CONTRADICTED = "confirmed_contradicted"
CORRECTNESS_UNCONFIRMED = "unconfirmed"
CORRECTNESS_NOT_APPLICABLE = "not_applicable"
CORRECTNESS_ORDER = (
    CORRECTNESS_CONSISTENT,
    CORRECTNESS_CONTRADICTED,
    CORRECTNESS_UNCONFIRMED,
    CORRECTNESS_NOT_APPLICABLE,
)

GATE_VIOLATION = "violation"
GATE_SUSPICIOUS = "suspicious"
GATE_OK = "ok"
GATE_NOT_APPLICABLE = "not_applicable"
GATE_ORDER = (GATE_VIOLATION, GATE_SUSPICIOUS, GATE_OK, GATE_NOT_APPLICABLE)

TRANSITION_IMPROVEMENT = "capability_improvement"
TRANSITION_CLASSIFICATION_CHANGE = "classification_change"
TRANSITION_REGRESSION = "regression"
TRANSITION_OTHER = "other"
TRANSITION_ORDER = (
    TRANSITION_IMPROVEMENT,
    TRANSITION_CLASSIFICATION_CHANGE,
    TRANSITION_REGRESSION,
    TRANSITION_OTHER,
)
# Named breakdown of what lands in ``other`` (and of the reason-set part of
# ``classification_change``), so nothing disappears into a catch-all bucket.
TRANSITION_NOTE_UNCHANGED = "unchanged"
TRANSITION_NOTE_DECIDED_BUT_UNCONFIRMED = "decided_but_unconfirmed"
TRANSITION_NOTE_REASON_SET_CHANGED = "reason_set_changed"
TRANSITION_NOTE_MISSING = "missing_on_one_side"
TRANSITION_NOTE_ORDER = (
    TRANSITION_NOTE_UNCHANGED,
    TRANSITION_NOTE_DECIDED_BUT_UNCONFIRMED,
    TRANSITION_NOTE_REASON_SET_CHANGED,
    TRANSITION_NOTE_MISSING,
)

OUTCOME_EQ = "EQUIVALENT"
OUTCOME_NOT_EQ = "NOT_EQ"
DECISIVE_OUTCOMES = frozenset({OUTCOME_EQ, OUTCOME_NOT_EQ})

GROUND_TRUTH_FILE = "function_diff_manifest.json"
GROUND_TRUTH_ABSENT = "absent"
# EPIC #130's fourth category.  It needs per-pair wall clock on both sides, so
# it is reported by --runtime-metrics and never by the transition axis: a run
# without runtime receipts must not silently report "no performance change".
TRANSITION_PERFORMANCE_NOTE = (
    "performance_improvement (EPIC #130) is not an outcome transition; it needs "
    "per-pair wall clock and is reported by --runtime-metrics only"
)


def load_ground_truth(root: Path) -> Tuple[Optional[Any], str]:
    """A tree's own ``function_diff_manifest.json``, or ``(None, reason)``.

    The manifest the runner already wrote next to the results is the only
    ground truth read here; nothing is inferred from a source diff, and a tree
    without one simply leaves every ``Neq`` decision ``unconfirmed``.
    """
    from scripts.function_tracer_pcode.reporting.benchmark_validation_gate import (
        FunctionDiffManifest,
    )

    path = Path(root) / GROUND_TRUTH_FILE
    if not path.is_file():
        return None, GROUND_TRUTH_ABSENT
    try:
        return FunctionDiffManifest.load(path), str(path)
    except (OSError, ValueError) as exc:
        return None, f"unreadable: {exc}"


def correctness_axis(record: Optional[PairOutcome], manifest: Optional[Any]) -> str:
    """Axis A: what a benchmark ground truth says about this pair's decision.

    ``Eq`` samples compile one single source on both sides, so the label itself
    is the ground truth.  ``Neq`` samples need the reviewed annotation in the
    function diff manifest; ``source_relation``/``source_impact`` are *not*
    used as a substitute for it, because "the source changed" does not mean
    "the semantics changed".  Anything else stays ``unconfirmed``.
    """
    if record is None:
        return CORRECTNESS_NOT_APPLICABLE
    outcome = record.outcome
    if outcome not in DECISIVE_OUTCOMES:
        # UNKNOWN / TIMEOUT / ERROR / INVALID decide nothing, so there is
        # nothing for a ground truth to confirm or contradict.
        return CORRECTNESS_NOT_APPLICABLE
    label = record.label
    if label == LABEL_EQ:
        return CORRECTNESS_CONSISTENT if outcome == OUTCOME_EQ else CORRECTNESS_CONTRADICTED
    if label != LABEL_NEQ or manifest is None:
        return CORRECTNESS_UNCONFIRMED
    fact, _reason = manifest.lookup(record.sample_identity, record.function_name)
    if fact is None:
        return CORRECTNESS_UNCONFIRMED
    truth = fact.semantic_ground_truth
    if truth == "CONFIRMED_NOT_EQ":
        return CORRECTNESS_CONSISTENT if outcome == OUTCOME_NOT_EQ else CORRECTNESS_CONTRADICTED
    if truth == "CONFIRMED_EQ":
        return CORRECTNESS_CONSISTENT if outcome == OUTCOME_EQ else CORRECTNESS_CONTRADICTED
    return CORRECTNESS_UNCONFIRMED


def gate_axis(record: Optional[PairOutcome], manifest: Optional[Any]) -> str:
    """Axis C: ``benchmark_validation_gate``'s own verdict for this pair.

    The gate keeps its own classification; this only groups its kinds.  It is
    read as a separate fact from axis A on purpose -- ``ok`` here means "the
    gate found nothing to complain about", never "the decision is correct".
    """
    from scripts.function_tracer_pcode.reporting import benchmark_validation_gate as gate

    if record is None:
        return GATE_NOT_APPLICABLE
    kind = gate.classify(record, manifest).kind
    if kind in gate.HARD_VIOLATION_KINDS:
        return GATE_VIOLATION
    if kind in gate.SUSPICIOUS_KINDS:
        return GATE_SUSPICIOUS
    if kind in gate.BENIGN_KINDS:
        return GATE_OK
    return GATE_NOT_APPLICABLE


def classify_transition(
    before_outcome: str,
    after_outcome: str,
    before_correctness: str,
    after_correctness: str,
    *,
    reason_set_changed: Optional[bool] = None,
) -> Tuple[str, Tuple[str, ...]]:
    """Axis B: EPIC #130's outcome transition category, plus named notes.

    A new decision counts as ``capability_improvement`` only when axis A
    confirms it.  A decision nothing can confirm is ``other`` with the note
    ``decided_but_unconfirmed``: the pair is not evidence of an improvement,
    and rolling it into one would manufacture progress out of unverified
    verdicts.  A decision a ground truth contradicts is a ``regression`` even
    when the pair previously decided nothing.
    """
    if OUTCOME_MISSING in (before_outcome, after_outcome):
        return TRANSITION_OTHER, (TRANSITION_NOTE_MISSING,)
    before_decisive = before_outcome in DECISIVE_OUTCOMES
    after_decisive = after_outcome in DECISIVE_OUTCOMES
    # A decision the ground truth contradicts is never anything but a
    # regression, whichever direction the pair moved in.
    if after_correctness == CORRECTNESS_CONTRADICTED and before_correctness != CORRECTNESS_CONTRADICTED:
        return TRANSITION_REGRESSION, ()
    if before_decisive and not after_decisive:
        return TRANSITION_REGRESSION, ()
    if after_decisive and not before_decisive:
        if after_correctness == CORRECTNESS_CONSISTENT:
            return TRANSITION_IMPROVEMENT, ()
        return TRANSITION_OTHER, (TRANSITION_NOTE_DECIDED_BUT_UNCONFIRMED,)
    if before_decisive and after_decisive:
        if before_outcome == after_outcome:
            return TRANSITION_OTHER, (TRANSITION_NOTE_UNCHANGED,)
        # EQUIVALENT <-> NOT_EQ: only a ground truth can say which way this is.
        if after_correctness == CORRECTNESS_CONSISTENT:
            return TRANSITION_IMPROVEMENT, ()
        if before_correctness == CORRECTNESS_CONSISTENT:
            return TRANSITION_REGRESSION, ()
        return TRANSITION_OTHER, (TRANSITION_NOTE_DECIDED_BUT_UNCONFIRMED,)
    # Neither side decided anything.
    if before_outcome != after_outcome:
        return TRANSITION_CLASSIFICATION_CHANGE, ()
    if reason_set_changed:
        return TRANSITION_CLASSIFICATION_CHANGE, (TRANSITION_NOTE_REASON_SET_CHANGED,)
    return TRANSITION_OTHER, (TRANSITION_NOTE_UNCHANGED,)


@dataclass(frozen=True)
class AxisRow:
    key: PairKey
    label: str
    before_outcome: str
    after_outcome: str
    before_correctness: str
    after_correctness: str
    before_gate: str
    after_gate: str
    transition: str
    notes: Tuple[str, ...]

    @property
    def pair_id(self) -> str:
        return f"{self.key[2]}_{self.key[3]}"

    def as_dict(self) -> Dict[str, Any]:
        return {
            "sample_identity": self.key[0],
            "function_name": self.key[1],
            "pair_id": self.pair_id,
            "label": self.label,
            "before": self.before_outcome,
            "after": self.after_outcome,
            "correctness_before": self.before_correctness,
            "correctness_after": self.after_correctness,
            "gate_before": self.before_gate,
            "gate_after": self.after_gate,
            "transition": self.transition,
            "notes": list(self.notes),
        }


@dataclass(frozen=True)
class AxisReport:
    """The three axes, each summarised on its own.

    ``reason_sets_compared`` records whether axis B could see a reason-set
    change at all; without ``--reason-sets`` an UNKNOWN -> UNKNOWN pair whose
    reasons changed is invisible here, and the report says so rather than
    letting a zero be read as "no reason changed".
    """

    rows: Tuple[AxisRow, ...]
    before_ground_truth: str
    after_ground_truth: str
    reason_sets_compared: bool

    def correctness_counts(self, side: str = "after") -> Dict[str, int]:
        values = Counter(getattr(row, f"{side}_correctness") for row in self.rows)
        return {name: values.get(name, 0) for name in CORRECTNESS_ORDER}

    def correctness_by_label(self, side: str = "after") -> Dict[str, Dict[str, int]]:
        table: Dict[str, Counter] = {}
        for row in self.rows:
            table.setdefault(row.label, Counter())[getattr(row, f"{side}_correctness")] += 1
        return {
            label: {name: counts.get(name, 0) for name in CORRECTNESS_ORDER}
            for label, counts in sorted(table.items())
        }

    def decided_outcome_correctness(self, side: str = "after") -> Dict[str, Dict[str, Dict[str, int]]]:
        """``label -> decisive outcome -> correctness counts``.

        This is the table that shows how many ``Neq`` ``NOT_EQ`` verdicts no
        ground truth can confirm.
        """
        table: Dict[str, Dict[str, Counter]] = {}
        for row in self.rows:
            outcome = getattr(row, f"{side}_outcome")
            if outcome not in DECISIVE_OUTCOMES:
                continue
            row_table = table.setdefault(row.label, {})
            row_table.setdefault(outcome, Counter())[getattr(row, f"{side}_correctness")] += 1
        return {
            label: {
                outcome: {name: counts.get(name, 0) for name in CORRECTNESS_ORDER}
                for outcome, counts in sorted(outcomes.items())
            }
            for label, outcomes in sorted(table.items())
        }

    def gate_counts(self, side: str = "after") -> Dict[str, int]:
        values = Counter(getattr(row, f"{side}_gate") for row in self.rows)
        return {name: values.get(name, 0) for name in GATE_ORDER}

    def transition_counts(self) -> Dict[str, int]:
        values = Counter(row.transition for row in self.rows)
        return {name: values.get(name, 0) for name in TRANSITION_ORDER}

    def transition_notes(self) -> Dict[str, int]:
        values: Counter = Counter()
        for row in self.rows:
            values.update(row.notes)
        return {name: values.get(name, 0) for name in TRANSITION_NOTE_ORDER}

    def rows_of_interest(self) -> Tuple[AxisRow, ...]:
        """Rows a reader has to look at: anything but an unchanged pair."""
        return tuple(
            row for row in self.rows
            if row.transition != TRANSITION_OTHER
            or row.notes != (TRANSITION_NOTE_UNCHANGED,)
        )

    def as_dict(self) -> Dict[str, Any]:
        return {
            "pairs": len(self.rows),
            "ground_truth": {
                "before": self.before_ground_truth,
                "after": self.after_ground_truth,
            },
            "reason_sets_compared": self.reason_sets_compared,
            "correctness": {
                "after": self.correctness_counts("after"),
                "before": self.correctness_counts("before"),
                "after_by_label": self.correctness_by_label("after"),
                "after_decided": self.decided_outcome_correctness("after"),
            },
            "transition": {
                **self.transition_counts(),
                "notes": self.transition_notes(),
                "performance_note": TRANSITION_PERFORMANCE_NOTE,
            },
            "gate": {
                "after": self.gate_counts("after"),
                "before": self.gate_counts("before"),
            },
            "rows": [row.as_dict() for row in self.rows_of_interest()],
        }


def build_axes(
    before: Mapping[PairKey, PairOutcome],
    after: Mapping[PairKey, PairOutcome],
    *,
    before_manifest: Optional[Any] = None,
    after_manifest: Optional[Any] = None,
    before_ground_truth: str = GROUND_TRUTH_ABSENT,
    after_ground_truth: str = GROUND_TRUTH_ABSENT,
    reason_sets: Optional["ReasonSetReport"] = None,
) -> AxisReport:
    changed_reasons = {} if reason_sets is None else {
        row.key: row.reason_set_mismatch for row in reason_sets.rows
    }
    rows: List[AxisRow] = []
    for key in sorted(set(before) | set(after)):
        before_record, after_record = before.get(key), after.get(key)
        before_outcome = before_record.outcome if before_record else OUTCOME_MISSING
        after_outcome = after_record.outcome if after_record else OUTCOME_MISSING
        before_correctness = correctness_axis(before_record, before_manifest)
        after_correctness = correctness_axis(after_record, after_manifest)
        transition, notes = classify_transition(
            before_outcome, after_outcome, before_correctness, after_correctness,
            reason_set_changed=changed_reasons.get(key),
        )
        rows.append(AxisRow(
            key=key,
            label=benchmark_label(key[0]),
            before_outcome=before_outcome,
            after_outcome=after_outcome,
            before_correctness=before_correctness,
            after_correctness=after_correctness,
            before_gate=gate_axis(before_record, before_manifest),
            after_gate=gate_axis(after_record, after_manifest),
            transition=transition,
            notes=notes,
        ))
    return AxisReport(
        rows=tuple(rows),
        before_ground_truth=before_ground_truth,
        after_ground_truth=after_ground_truth,
        reason_sets_compared=reason_sets is not None,
    )


def summarize_run_axes(
    outcomes: Mapping[PairKey, PairOutcome],
    *,
    manifest: Optional[Any] = None,
    ground_truth: str = GROUND_TRUTH_ABSENT,
) -> Dict[str, Any]:
    """Axes A and C for a single run (axis B needs two runs and is absent)."""
    report = build_axes(
        {}, outcomes, after_manifest=manifest, after_ground_truth=ground_truth,
    )
    return {
        "pairs": len(report.rows),
        "ground_truth": ground_truth,
        "correctness": {
            **report.correctness_counts("after"),
            "by_label": report.correctness_by_label("after"),
            "decided": report.decided_outcome_correctness("after"),
        },
        "gate": report.gate_counts("after"),
    }

# --------------------------------------------------------------------------
# Issue #123 / PR-123-B: the reason-set comparison, mechanised.
#
# This replaces the ``compare_reason_sets.py`` that used to be copied into
# every run directory by hand.  Only three things are compared -- the pair
# identity, the canonical outcome, and the final UNKNOWN reason-id set -- and
# nothing that is unique per run (payload preimage digests, cause ids,
# semantic target digests) is looked at.
#
# A pair whose result payload cannot be read on either side is *incomparable*
# and is counted on its own.  Counting it as a match would turn "we could not
# look" into "we looked and they agree".
# --------------------------------------------------------------------------

REASON_SET_COMPARABLE = "comparable"
REASON_SET_INCOMPARABLE = "incomparable"
REASON_DETAIL_MISSING = "missing_on_one_side"
REASON_DETAIL_NO_PAYLOAD_BEFORE = "no_result_payload_before"
REASON_DETAIL_NO_PAYLOAD_AFTER = "no_result_payload_after"
REASON_DETAIL_NO_PAYLOAD_BOTH = "no_result_payload_both"


def _log_path_for(record: PairOutcome) -> Path:
    """The pair log next to a ``*.pair-status.json`` (same stem, ``.log``)."""
    status = Path(record.status_path)
    return status.with_name(status.name[: -len(PAIR_STATUS_SUFFIX)] + ".log")


def _reason_ids(reasons: Any) -> Tuple[str, ...]:
    """The reason-id set of one result payload, order-insensitive."""
    found = set()
    for entry in reasons or ():
        value = entry.get("reason_id") if isinstance(entry, Mapping) else getattr(entry, "reason_id", None)
        value = getattr(value, "value", value)
        if value:
            found.add(str(value))
    return tuple(sorted(found))


def final_reason_set(record: Optional[PairOutcome]) -> Optional[Tuple[str, ...]]:
    """The last result payload's reason-id set, or ``None`` when unreadable.

    ``None`` means "this pair produced no readable result payload" (a
    wall-clock kill before the result was emitted, a truncated log, ...).  It
    is never the same thing as an empty reason set.
    """
    from scripts.function_tracer_pcode.reporting.unknown_reason_summary import (
        extract_result_payloads_from_text,
    )

    if record is None:
        return None
    log_path = _log_path_for(record)
    try:
        text = log_path.read_text(errors="replace")
    except OSError:
        return None
    try:
        payloads = extract_result_payloads_from_text(text)
    except ValueError:
        return None
    if not payloads:
        return None
    return _reason_ids(payloads[-1].get("unknown_reasons"))


@dataclass(frozen=True)
class ReasonSetRow:
    key: PairKey
    verdict: str
    detail: str
    before_outcome: str
    after_outcome: str
    before_reasons: Optional[Tuple[str, ...]]
    after_reasons: Optional[Tuple[str, ...]]

    @property
    def outcome_mismatch(self) -> bool:
        """Both sides have a status and their canonical outcomes differ."""
        return (
            OUTCOME_MISSING not in (self.before_outcome, self.after_outcome)
            and self.before_outcome != self.after_outcome
        )

    @property
    def reason_set_mismatch(self) -> bool:
        """Only a comparable pair can mismatch; an unreadable one cannot."""
        return self.verdict == REASON_SET_COMPARABLE and self.before_reasons != self.after_reasons

    def as_dict(self) -> Dict[str, Any]:
        return {
            "sample_identity": self.key[0],
            "function_name": self.key[1],
            "pair_id": f"{self.key[2]}_{self.key[3]}",
            "verdict": self.verdict,
            "detail": self.detail,
            "before_outcome": self.before_outcome,
            "after_outcome": self.after_outcome,
            "before_reasons": None if self.before_reasons is None else list(self.before_reasons),
            "after_reasons": None if self.after_reasons is None else list(self.after_reasons),
            "outcome_mismatch": self.outcome_mismatch,
            "reason_set_mismatch": self.reason_set_mismatch,
        }


@dataclass(frozen=True)
class ReasonSetReport:
    rows: Tuple[ReasonSetRow, ...]

    @property
    def comparable(self) -> Tuple[ReasonSetRow, ...]:
        return tuple(row for row in self.rows if row.verdict == REASON_SET_COMPARABLE)

    @property
    def incomparable(self) -> Tuple[ReasonSetRow, ...]:
        return tuple(row for row in self.rows if row.verdict == REASON_SET_INCOMPARABLE)

    @property
    def outcome_mismatches(self) -> Tuple[ReasonSetRow, ...]:
        return tuple(row for row in self.rows if row.outcome_mismatch)

    @property
    def reason_set_mismatches(self) -> Tuple[ReasonSetRow, ...]:
        return tuple(row for row in self.rows if row.reason_set_mismatch)

    @property
    def incomparable_sides_agree(self) -> bool:
        """Whether exactly the same pairs were unreadable on both sides.

        A run that loses a *different* set of payloads is a change worth
        seeing even when every comparable pair matched.
        """
        before = {row.key for row in self.rows if row.before_reasons is None and row.before_outcome != OUTCOME_MISSING}
        after = {row.key for row in self.rows if row.after_reasons is None and row.after_outcome != OUTCOME_MISSING}
        return before == after

    def counts(self) -> Dict[str, int]:
        return {
            "pairs": len(self.rows),
            "comparable": len(self.comparable),
            "incomparable": len(self.incomparable),
            "outcome_mismatch": len(self.outcome_mismatches),
            "reason_set_mismatch": len(self.reason_set_mismatches),
        }

    def as_dict(self) -> Dict[str, Any]:
        return {
            **self.counts(),
            "incomparable_sides_agree": self.incomparable_sides_agree,
            "rows": [
                row.as_dict() for row in self.rows
                if row.verdict == REASON_SET_INCOMPARABLE
                or row.outcome_mismatch
                or row.reason_set_mismatch
            ],
        }


def build_reason_sets(
    before: Mapping[PairKey, PairOutcome],
    after: Mapping[PairKey, PairOutcome],
) -> ReasonSetReport:
    rows: List[ReasonSetRow] = []
    for key in sorted(set(before) | set(after)):
        before_record, after_record = before.get(key), after.get(key)
        before_reasons = final_reason_set(before_record)
        after_reasons = final_reason_set(after_record)
        if before_record is None or after_record is None:
            verdict, detail = REASON_SET_INCOMPARABLE, REASON_DETAIL_MISSING
        elif before_reasons is None and after_reasons is None:
            verdict, detail = REASON_SET_INCOMPARABLE, REASON_DETAIL_NO_PAYLOAD_BOTH
        elif before_reasons is None:
            verdict, detail = REASON_SET_INCOMPARABLE, REASON_DETAIL_NO_PAYLOAD_BEFORE
        elif after_reasons is None:
            verdict, detail = REASON_SET_INCOMPARABLE, REASON_DETAIL_NO_PAYLOAD_AFTER
        else:
            verdict, detail = REASON_SET_COMPARABLE, ""
        rows.append(ReasonSetRow(
            key=key,
            verdict=verdict,
            detail=detail,
            before_outcome=before_record.outcome if before_record else OUTCOME_MISSING,
            after_outcome=after_record.outcome if after_record else OUTCOME_MISSING,
            before_reasons=before_reasons,
            after_reasons=after_reasons,
        ))
    return ReasonSetReport(rows=tuple(rows))


# --------------------------------------------------------------------------
# Issue #123 / PR-123-B: completeness against a tree's own publication
# manifest, and the informational runtime-metrics section.
# --------------------------------------------------------------------------

COMPLETENESS_COMPLETE = "complete"
COMPLETENESS_PARTIAL = "partial"
COMPLETENESS_UNKNOWN = "unknown"
PUBLICATION_MANIFEST_FILE = "matrix-publication-manifest.json"
RUNTIME_METRICS_DIR = ".runtime-metrics"
RUNTIME_METRICS_SUFFIX = ".runtime.json"


@dataclass(frozen=True)
class TreeCompleteness:
    """What a result tree's own publication manifest says it should hold.

    ``status`` is ``complete`` only when the manifest could be read *and*
    every pair it expects is on disk *and* the run actually executed all of
    them.  A manifest that is missing or unreadable gives ``unknown``, never
    ``complete``: "we could not check" must not read as "we checked".
    """

    root: str
    status: str
    detail: str
    pairs_expected: int
    pairs_with_status: int
    pairs_missing: Tuple[str, ...]
    pairs_unexpected: Tuple[str, ...]
    pairs_verified_skipped: int

    def as_dict(self) -> Dict[str, Any]:
        return {
            "root": self.root,
            "status": self.status,
            "detail": self.detail,
            "pairs_expected": self.pairs_expected,
            "pairs_with_status": self.pairs_with_status,
            "pairs_missing": len(self.pairs_missing),
            "pairs_unexpected": len(self.pairs_unexpected),
            "pairs_verified_skipped": self.pairs_verified_skipped,
            "missing_paths": list(self.pairs_missing[:20]),
            "unexpected_paths": list(self.pairs_unexpected[:20]),
        }


def _observed_status_paths(root: Path) -> Tuple[str, ...]:
    return tuple(sorted(
        path.relative_to(root).as_posix()
        for path in root.rglob(f"*{PAIR_STATUS_SUFFIX}")
    ))


def _census(payload: Mapping[str, Any], key: str) -> set:
    """One census list of the publication manifest, or ``ValueError``.

    Only the two fields completeness actually consumes are checked, against
    the current schema tag.  Re-running the whole signed-artifact validation
    (``execution_receipt``) is deliberately not done here: that artifact has
    its own owner and its own checks, and an older manifest whose census lists
    are perfectly readable should still be able to say what it expected rather
    than being downgraded to "unknown" over an unrelated field.
    """
    rows = payload.get(key)
    if not isinstance(rows, list) or any(not isinstance(row, str) or not row for row in rows):
        raise ValueError(f"{key} is not a list of paths")
    if len(rows) != len(set(rows)):
        raise ValueError(f"{key} repeats a path")
    return set(rows)


def tree_completeness(root: Path) -> TreeCompleteness:
    from scripts.function_tracer_pcode.reporting.execution_receipt import (
        MATRIX_PUBLICATION_SCHEMA,
    )

    root = Path(root)
    observed = set(_observed_status_paths(root))
    manifest_path = root / PUBLICATION_MANIFEST_FILE
    if not manifest_path.is_file():
        return TreeCompleteness(
            root=str(root), status=COMPLETENESS_UNKNOWN,
            detail=f"no {PUBLICATION_MANIFEST_FILE}",
            pairs_expected=0, pairs_with_status=len(observed),
            pairs_missing=(), pairs_unexpected=(), pairs_verified_skipped=0,
        )
    try:
        payload = json.loads(manifest_path.read_text(encoding="utf-8"))
        if not isinstance(payload, Mapping):
            raise ValueError("not an object")
        if payload.get("schema") != MATRIX_PUBLICATION_SCHEMA:
            raise ValueError(f"schema is not {MATRIX_PUBLICATION_SCHEMA}")
        expected = _census(payload, "expected_pair_status_paths")
        skipped = _census(payload, "verified_skipped_pair_status_paths")
    except (OSError, ValueError) as exc:
        return TreeCompleteness(
            root=str(root), status=COMPLETENESS_UNKNOWN,
            detail=f"unreadable {PUBLICATION_MANIFEST_FILE}: {exc}",
            pairs_expected=0, pairs_with_status=len(observed),
            pairs_missing=(), pairs_unexpected=(), pairs_verified_skipped=0,
        )
    # A verified-skipped pair was reused from an earlier run, not executed by
    # this one, so it is not evidence about the code this run was made for.
    missing = tuple(sorted(expected - observed))
    unexpected = tuple(sorted(observed - expected))
    if missing or unexpected:
        status = COMPLETENESS_PARTIAL
        detail = f"{len(missing)} expected pair(s) missing, {len(unexpected)} unexpected"
    elif skipped:
        status = COMPLETENESS_PARTIAL
        detail = f"{len(skipped)} pair(s) reused from an earlier run, not executed here"
    else:
        status, detail = COMPLETENESS_COMPLETE, ""
    return TreeCompleteness(
        root=str(root), status=status, detail=detail,
        pairs_expected=len(expected), pairs_with_status=len(observed),
        pairs_missing=missing, pairs_unexpected=unexpected,
        pairs_verified_skipped=len(skipped),
    )


def combine_completeness(parts: Sequence[TreeCompleteness]) -> Tuple[str, str]:
    """Fold per-tree completeness fail-closed: any doubt wins over ``complete``."""
    if not parts:
        return COMPLETENESS_UNKNOWN, "no result tree"
    if any(part.status == COMPLETENESS_UNKNOWN for part in parts):
        reasons = "; ".join(
            f"{part.root}: {part.detail}" for part in parts
            if part.status == COMPLETENESS_UNKNOWN
        )
        return COMPLETENESS_UNKNOWN, reasons
    if any(part.status == COMPLETENESS_PARTIAL for part in parts):
        reasons = "; ".join(
            f"{part.root}: {part.detail}" for part in parts
            if part.status == COMPLETENESS_PARTIAL
        )
        return COMPLETENESS_PARTIAL, reasons
    return COMPLETENESS_COMPLETE, ""


def _runtime_identity(root: Path, path: Path) -> Optional[PairKey]:
    """``(sample, function, left, right)`` of a ``.runtime.json``, from its path.

    The path layout is the contract (``<sample>/<function>/.runtime-metrics/
    <function>_<left>_<right>.runtime.json``); the receipt's own identity
    fields are then required to agree, and a receipt that disagrees is dropped
    rather than guessed at.
    """
    from scripts.function_tracer_pcode.reporting.pair_outcomes import (
        identity_from_status_path,
    )

    relative = path.relative_to(root)
    if len(relative.parts) < 4 or relative.parts[-2] != RUNTIME_METRICS_DIR:
        return None
    status_like = root.joinpath(
        *relative.parts[:-2],
        relative.name[: -len(RUNTIME_METRICS_SUFFIX)] + PAIR_STATUS_SUFFIX,
    )
    try:
        return identity_from_status_path(root, status_like)
    except ValueError:
        return None


def load_runtime_metrics(root: Path) -> Tuple[Dict[PairKey, float], int]:
    """``(elapsed seconds per pair, number of unusable receipts)``."""
    root = Path(root)
    elapsed: Dict[PairKey, float] = {}
    unusable = 0
    for path in sorted(root.rglob(f"*{RUNTIME_METRICS_SUFFIX}")):
        key = _runtime_identity(root, path)
        try:
            payload = json.loads(path.read_text(encoding="utf-8"))
        except (OSError, ValueError):
            payload = None
        if key is None or not isinstance(payload, Mapping):
            unusable += 1
            continue
        identity_matches = (
            payload.get("function_name") == key[1]
            and payload.get("left_binary_id") == key[2]
            and payload.get("right_binary_id") == key[3]
        )
        seconds = payload.get("elapsed_seconds")
        if not identity_matches or not isinstance(seconds, (int, float)):
            unusable += 1
            continue
        elapsed[key] = float(seconds)
    return elapsed, unusable

@dataclass(frozen=True)
class RuntimeMetricsReport:
    """Wall-clock deltas, and how much of each run they actually cover.

    Informational only.  The report always states its own coverage, because a
    pair without a receipt must not be read as zero seconds and a partially
    instrumented run must not be read as a complete measurement.  It never
    contributes to an exit code.
    """

    pairs: int
    before_seen: int
    after_seen: int
    before_unusable: int
    after_unusable: int
    deltas: Tuple[Tuple[PairKey, float, float], ...]

    @property
    def complete(self) -> bool:
        return (
            self.pairs > 0
            and len(self.deltas) == self.pairs
            and not (self.before_unusable or self.after_unusable)
        )

    @property
    def faster(self) -> int:
        return sum(1 for _key, before, after in self.deltas if after < before)

    @property
    def slower(self) -> int:
        return sum(1 for _key, before, after in self.deltas if after > before)

    def median_delta(self) -> Optional[float]:
        if not self.deltas:
            return None
        return statistics.median(after - before for _key, before, after in self.deltas)

    def as_dict(self) -> Dict[str, Any]:
        return {
            "pairs": self.pairs,
            "pairs_with_both_receipts": len(self.deltas),
            "before_receipts": self.before_seen,
            "after_receipts": self.after_seen,
            "before_unusable_receipts": self.before_unusable,
            "after_unusable_receipts": self.after_unusable,
            "coverage_complete": self.complete,
            "faster": self.faster,
            "slower": self.slower,
            "median_delta_seconds": self.median_delta(),
            "informational_only": True,
        }


def build_runtime_metrics(
    before_root: Path,
    after_root: Path,
    keys: Sequence[PairKey],
) -> RuntimeMetricsReport:
    before_elapsed, before_unusable = load_runtime_metrics(before_root)
    after_elapsed, after_unusable = load_runtime_metrics(after_root)
    deltas = tuple(
        (key, before_elapsed[key], after_elapsed[key])
        for key in keys
        if key in before_elapsed and key in after_elapsed
    )
    return RuntimeMetricsReport(
        pairs=len(keys),
        before_seen=len(before_elapsed),
        after_seen=len(after_elapsed),
        before_unusable=before_unusable,
        after_unusable=after_unusable,
        deltas=deltas,
    )


# --------------------------------------------------------------------------
# Rendering of the opt-in sections.
# --------------------------------------------------------------------------


def format_axes(report: AxisReport) -> List[str]:
    lines = [
        "",
        "Three independent axes (EPIC #130) -- A correctness, B transition, C gate.",
        "They are separate facts: a gate PASS is not a correctness confirmation,",
        "and an outcome change is not by itself an improvement.",
        f"Ground truth: after={report.after_ground_truth} before={report.before_ground_truth}",
        "",
        "A. correctness of the after run (only decisive outcomes can be confirmed):",
    ]
    for name, count in report.correctness_counts("after").items():
        lines.append(f"  {name}: {count}")
    lines.append("  by label and decisive outcome:")
    decided = report.decided_outcome_correctness("after")
    if not decided:
        lines.append("    (no decisive outcome)")
    for label, outcomes in decided.items():
        for outcome, counts in outcomes.items():
            detail = " ".join(f"{name}={value}" for name, value in counts.items())
            lines.append(f"    {label} {outcome}: {detail}")
    lines.extend([
        "",
        "B. outcome transition of every pair:",
    ])
    for name, count in report.transition_counts().items():
        lines.append(f"  {name}: {count}")
    for name, count in report.transition_notes().items():
        lines.append(f"    {name}: {count}")
    if not report.reason_sets_compared:
        lines.append(
            "    (reason sets were not compared: --reason-sets is off, so an "
            "UNKNOWN -> UNKNOWN reason change is not visible here)"
        )
    lines.append(f"  note: {TRANSITION_PERFORMANCE_NOTE}")
    lines.extend(["", "C. benchmark validation gate of the after run:"])
    for name, count in report.gate_counts("after").items():
        lines.append(f"  {name}: {count}")
    rows = report.rows_of_interest()
    lines.append("")
    lines.append(f"Pairs that are not an unchanged pair ({len(rows)}):")
    if not rows:
        lines.append("  (none)")
    for row in rows:
        notes = f" [{' '.join(row.notes)}]" if row.notes else ""
        lines.append(
            f"  {row.key[0]} {row.key[1]} {row.pair_id}: "
            f"{row.before_outcome} -> {row.after_outcome} "
            f"transition={row.transition} correctness={row.after_correctness} "
            f"gate={row.after_gate}{notes}"
        )
    return lines


def format_reason_sets(report: ReasonSetReport) -> List[str]:
    counts = report.counts()
    lines = [
        "",
        "Final UNKNOWN reason sets (pair identity, canonical outcome, reason ids only):",
        f"  pairs: {counts['pairs']}",
        f"  comparable: {counts['comparable']}",
        f"  outcome mismatch: {counts['outcome_mismatch']}",
        f"  reason-set mismatch: {counts['reason_set_mismatch']} "
        f"(of {counts['comparable']} comparable)",
        f"  incomparable: {counts['incomparable']} "
        "(no readable result payload, or present on one side only)",
        f"  the same pairs are unreadable on both sides: {report.incomparable_sides_agree}",
    ]
    for title, rows in (
        ("Outcome mismatches", report.outcome_mismatches),
        ("Reason-set mismatches", report.reason_set_mismatches),
        ("Incomparable pairs", report.incomparable),
    ):
        lines.append(f"{title} ({len(rows)}):")
        if not rows:
            lines.append("  (none)")
        for row in rows:
            detail = f" [{row.detail}]" if row.detail else ""
            lines.append(
                f"  {row.key[0]} {row.key[1]} {row.key[2]}_{row.key[3]}: "
                f"{row.before_outcome} -> {row.after_outcome}{detail}"
            )
            if row in report.reason_set_mismatches:
                lines.append(f"      before={list(row.before_reasons or ())}")
                lines.append(f"      after ={list(row.after_reasons or ())}")
    return lines


def format_completeness(
    before: TreeCompleteness, after: TreeCompleteness,
) -> List[str]:
    lines = [
        "",
        "Completeness against each tree's own matrix-publication-manifest.json:",
    ]
    for side, part in (("before", before), ("after", after)):
        detail = f" -- {part.detail}" if part.detail else ""
        lines.append(
            f"  {side}: {part.status} "
            f"({part.pairs_with_status}/{part.pairs_expected} expected pairs on disk, "
            f"{len(part.pairs_missing)} missing, {len(part.pairs_unexpected)} unexpected, "
            f"{part.pairs_verified_skipped} reused from an earlier run){detail}"
        )
        for path in part.pairs_missing[:20]:
            lines.append(f"      missing: {path}")
        for path in part.pairs_unexpected[:20]:
            lines.append(f"      unexpected: {path}")
    return lines


def format_runtime_metrics(report: RuntimeMetricsReport) -> List[str]:
    median = report.median_delta()
    lines = [
        "",
        "Runtime metrics (informational only -- never part of an exit code):",
        f"  pairs: {report.pairs}; with a usable receipt on both sides: {len(report.deltas)}",
        f"  receipts read: before {report.before_seen}, after {report.after_seen} "
        f"(unusable: before {report.before_unusable}, after {report.after_unusable})",
        f"  coverage complete: {report.complete}",
        f"  faster: {report.faster}  slower: {report.slower}  "
        f"median delta: {'n/a' if median is None else f'{median:+.2f}s'}",
        "  a pair without a receipt is not counted as zero seconds, and wall clock "
        "varies between runs, so a delta alone is not evidence of a code effect.",
    ]
    return lines

def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--before", required=True, type=Path, help="result tree of the earlier run")
    parser.add_argument("--after", required=True, type=Path, help="result tree of the later run")
    parser.add_argument("--json", type=Path, default=None, help="write the report as JSON to this path")
    parser.add_argument("--changed-only", action="store_true", help="list only pairs whose outcome changed")
    parser.add_argument(
        "--fail-on-change",
        action="store_true",
        help=(
            "exit 2 when any pair changed its unconditional outcome or is missing "
            "on one side; a conditional-only change never trips this switch"
        ),
    )
    parser.add_argument(
        "--fail-on-conditional-change",
        action="store_true",
        help=(
            "exit 3 when any pair changed its conditional (assumption-dependent) "
            "outcome; separate from --fail-on-change on purpose"
        ),
    )
    parser.add_argument(
        "--axes", action="store_true",
        help=(
            "add the three independent axes of EPIC #130 (correctness / transition / "
            "gate); the ground truth is each tree's own function_diff_manifest.json"
        ),
    )
    parser.add_argument(
        "--ground-truth-manifest", type=Path, default=None,
        help=(
            "function diff manifest to use for --axes on both sides instead of the "
            "one inside each tree"
        ),
    )
    parser.add_argument(
        "--reason-sets", action="store_true",
        help=(
            "compare the final UNKNOWN reason-id set of every pair; a pair with no "
            "readable result payload is reported as incomparable, never as a match"
        ),
    )
    parser.add_argument(
        "--manifest", action="store_true",
        help=(
            "check each tree against its own matrix-publication-manifest.json; a "
            "missing manifest, a missing pair or a pair reused from an earlier run "
            "keeps the tree from being called complete"
        ),
    )
    parser.add_argument(
        "--runtime-metrics", action="store_true",
        help=(
            "add the wall-clock delta from .runtime-metrics/<pair>.runtime.json; "
            "informational only, and it never changes the exit code"
        ),
    )
    return parser


def build_report_sections(
    before_root: Path,
    after_root: Path,
    *,
    axes: bool = False,
    reason_sets: bool = False,
    manifest: bool = False,
    runtime_metrics: bool = False,
    ground_truth_manifest: Optional[Path] = None,
) -> Tuple[TransitionReport, Dict[str, Any]]:
    """The transition report plus whichever opt-in sections were asked for.

    The sections are returned separately so that the default report -- text and
    JSON -- stays exactly what it was before they existed.
    """
    before = load_pair_outcomes(before_root)
    after = load_pair_outcomes(after_root)
    report = build_transition(before, after)
    sections: Dict[str, Any] = {}
    reason_set_report = None
    if reason_sets:
        reason_set_report = build_reason_sets(before, after)
        sections["reason_sets"] = reason_set_report
    if axes:
        if ground_truth_manifest is not None:
            from scripts.function_tracer_pcode.reporting.benchmark_validation_gate import (
                FunctionDiffManifest,
            )
            shared = FunctionDiffManifest.load(ground_truth_manifest)
            before_truth = after_truth = (shared, str(ground_truth_manifest))
        else:
            before_truth = load_ground_truth(before_root)
            after_truth = load_ground_truth(after_root)
        sections["axes"] = build_axes(
            before, after,
            before_manifest=before_truth[0], after_manifest=after_truth[0],
            before_ground_truth=before_truth[1], after_ground_truth=after_truth[1],
            reason_sets=reason_set_report,
        )
    if manifest:
        sections["completeness"] = (
            tree_completeness(before_root), tree_completeness(after_root),
        )
    if runtime_metrics:
        sections["runtime_metrics"] = build_runtime_metrics(
            before_root, after_root, sorted(set(before) | set(after)),
        )
    return report, sections


def format_sections(sections: Mapping[str, Any]) -> str:
    lines: List[str] = []
    if "axes" in sections:
        lines.extend(format_axes(sections["axes"]))
    if "reason_sets" in sections:
        lines.extend(format_reason_sets(sections["reason_sets"]))
    if "completeness" in sections:
        lines.extend(format_completeness(*sections["completeness"]))
    if "runtime_metrics" in sections:
        lines.extend(format_runtime_metrics(sections["runtime_metrics"]))
    return "\n".join(lines) + "\n" if lines else ""


def sections_as_dict(sections: Mapping[str, Any]) -> Dict[str, Any]:
    payload: Dict[str, Any] = {}
    if "axes" in sections:
        payload["axes"] = sections["axes"].as_dict()
    if "reason_sets" in sections:
        payload["reason_sets"] = sections["reason_sets"].as_dict()
    if "completeness" in sections:
        before, after = sections["completeness"]
        status, detail = combine_completeness((before, after))
        payload["completeness"] = {
            "before": before.as_dict(), "after": after.as_dict(),
            "combined_status": status, "combined_detail": detail,
        }
    if "runtime_metrics" in sections:
        payload["runtime_metrics"] = sections["runtime_metrics"].as_dict()
    return payload


def main(argv: Optional[Sequence[str]] = None) -> int:
    args = build_parser().parse_args(argv)
    for path in (args.before, args.after):
        if not path.is_dir():
            print(f"error: not a directory: {path}", file=sys.stderr)
            return 1
    try:
        report, sections = build_report_sections(
            args.before, args.after,
            axes=args.axes, reason_sets=args.reason_sets,
            manifest=args.manifest, runtime_metrics=args.runtime_metrics,
            ground_truth_manifest=args.ground_truth_manifest,
        )
    except (OSError, ValueError) as exc:
        print(f"error: {exc}", file=sys.stderr)
        return 1
    if args.json is not None:
        payload = {**report.as_dict(), **sections_as_dict(sections)}
        args.json.write_text(json.dumps(payload, indent=1) + "\n", encoding="utf-8")
    sys.stdout.write(format_transition(report, changed_only=args.changed_only))
    sys.stdout.write(format_sections(sections))
    # The opt-in sections are reports, not gates: only the two switches that
    # existed before decide the exit code, and they keep their exact meaning.
    if args.fail_on_change and report.changed_rows:
        return 2
    if args.fail_on_conditional_change and report.conditional_changed_rows:
        return 3
    return 0


if __name__ == "__main__":
    sys.exit(main())
