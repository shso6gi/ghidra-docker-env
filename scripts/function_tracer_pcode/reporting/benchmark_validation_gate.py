# -*- coding: utf-8 -*-
"""Benchmark validation gate for EqBench / NeqBench runner output (Issue #104).

Usage::

    python3 -m scripts.function_tracer_pcode.reporting.benchmark_validation_gate \
        logs/EqBench/all_neq_same_isa_closure_current \
        --manifest logs/EqBench/all_neq_same_isa_closure_current/function_diff_manifest.json \
        [--json gate.json] [--health-summary-json ... --health-summary-text ...] \
        [--fail-on-suspicious]

This is an *evaluation* gate, not a semantic authority: it never changes a
pair's outcome and the checker never sees its inputs.  It joins the canonical
pair outcomes of a result tree with the source-derived function diff manifest
(``scripts/eqbench/function_diff_manifest.py``) and classifies every pair:

hard violations (gate FAIL, runner exit 1)
    * ``eq_not_eq`` -- a pair of an ``Eq`` sample judged ``NOT_EQ``;
    * ``neq_confirmed_not_eq_equivalent`` -- a ``Neq`` function whose
      reviewed ground truth is ``CONFIRMED_NOT_EQ`` judged ``EQUIVALENT``;
    * ``neq_confirmed_eq_not_eq`` -- a ``Neq`` function whose reviewed
      ground truth is ``CONFIRMED_EQ`` judged ``NOT_EQ`` (a false NOT_EQ is
      a correctness failure too);
    * ``neq_equivalent_unmapped`` -- a ``Neq`` pair judged ``EQUIVALENT``
      whose function the manifest cannot classify (missing sample/function or
      parse failure).  The gate cannot vouch for it, so it fails closed.

suspicious (counted, gate PASS unless ``--fail-on-suspicious``)
    * ``suspicious_eq_on_source_changed_function`` -- ``EQUIVALENT`` on a
      ``Neq`` function whose source impact is not ``NO_KNOWN_SOURCE_IMPACT``
      while its ground truth is still ``UNKNOWN``;
    * ``suspicious_not_eq_on_source_identical_function`` -- ``NOT_EQ`` on a
      ``Neq`` function with ``NO_KNOWN_SOURCE_IMPACT`` (a possible false
      NOT_EQ; not a violation because the binaries may still differ).

benign
    * ``benign_eq_no_known_source_impact`` -- ``EQUIVALENT`` on a ``Neq``
      function the source change cannot reach;
    * ``benign_eq_confirmed`` -- ``EQUIVALENT`` on a function annotated
      ``CONFIRMED_EQ``.

UNKNOWN / TIMEOUT / ERROR / INVALID never count against the gate.  Exit 0 on
PASS, 1 on FAIL, 2 when the trees contain no pair status (an empty tree is not
a pass) or the manifest cannot be read.
"""

from __future__ import annotations

import argparse
import json
import sys
from collections import Counter
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Dict, List, Mapping, Optional, Sequence, Tuple

from scripts.function_tracer_pcode.reporting.pair_outcomes import (
    LABEL_EQ,
    LABEL_NEQ,
    PairOutcome,
    iter_pair_outcomes,
)
from scripts.function_tracer_pcode.reporting.result_summary import (
    BENCHMARK_VALIDATION_KEY,
    format_benchmark_validation_lines,
    format_run_health_summary,
)

EXIT_PASS = 0
EXIT_VIOLATION = 1
EXIT_EMPTY = 2

MANIFEST_SCHEMA = "eqbench-function-diff-manifest-v1"
HEALTH_KEY = BENCHMARK_VALIDATION_KEY
GATE_STATUS_PASS = "PASS"
GATE_STATUS_FAIL = "FAIL"
GATE_STATUS_EMPTY = "EMPTY"

OUTCOME_EQ = "EQUIVALENT"
OUTCOME_NOT_EQ = "NOT_EQ"

IMPACT_NONE = "NO_KNOWN_SOURCE_IMPACT"
TRUTH_EQ = "CONFIRMED_EQ"
TRUTH_NOT_EQ = "CONFIRMED_NOT_EQ"
TRUTH_UNKNOWN = "UNKNOWN"

# Classification kinds, in the order they are reported.
KIND_EQ_NOT_EQ = "eq_not_eq"
KIND_NEQ_CONFIRMED_NOT_EQ_EQUIVALENT = "neq_confirmed_not_eq_equivalent"
KIND_NEQ_CONFIRMED_EQ_NOT_EQ = "neq_confirmed_eq_not_eq"
KIND_NEQ_EQUIVALENT_UNMAPPED = "neq_equivalent_unmapped"
KIND_SUSPICIOUS_EQ = "suspicious_eq_on_source_changed_function"
KIND_SUSPICIOUS_NOT_EQ = "suspicious_not_eq_on_source_identical_function"
KIND_BENIGN_EQ_NO_IMPACT = "benign_eq_no_known_source_impact"
KIND_BENIGN_EQ_CONFIRMED = "benign_eq_confirmed"
KIND_NOT_APPLICABLE = "not_applicable"

HARD_VIOLATION_KINDS = (
    KIND_EQ_NOT_EQ,
    KIND_NEQ_CONFIRMED_NOT_EQ_EQUIVALENT,
    KIND_NEQ_CONFIRMED_EQ_NOT_EQ,
    KIND_NEQ_EQUIVALENT_UNMAPPED,
)
SUSPICIOUS_KINDS = (KIND_SUSPICIOUS_EQ, KIND_SUSPICIOUS_NOT_EQ)
BENIGN_KINDS = (KIND_BENIGN_EQ_NO_IMPACT, KIND_BENIGN_EQ_CONFIRMED)
REPORTED_KINDS = HARD_VIOLATION_KINDS + SUSPICIOUS_KINDS + BENIGN_KINDS


@dataclass(frozen=True)
class FunctionFact:
    """What the manifest knows about one (sample, function)."""

    source_relation: str
    source_impact: str
    semantic_ground_truth: str
    ground_truth_evidence: Optional[str]


@dataclass(frozen=True)
class FunctionDiffManifest:
    samples: Mapping[str, Mapping[str, Any]]

    @classmethod
    def load(cls, path: Path) -> "FunctionDiffManifest":
        payload = json.loads(Path(path).read_text(encoding="utf-8"))
        if not isinstance(payload, dict) or payload.get("schema") != MANIFEST_SCHEMA:
            raise ValueError(f"unexpected function diff manifest schema in {path}")
        samples = payload.get("samples")
        if not isinstance(samples, dict):
            raise ValueError(f"function diff manifest has no samples: {path}")
        return cls(samples=samples)

    def lookup(self, sample_identity: str, function_name: str) -> Tuple[Optional[FunctionFact], str]:
        """Return (fact, reason) where ``fact`` is None when the manifest cannot classify."""
        record = self.samples.get(sample_identity)
        if not isinstance(record, dict):
            return None, "sample_not_in_manifest"
        if record.get("parse_status") != "ok":
            return None, "sample_parse_failed"
        functions = record.get("functions")
        entry = functions.get(function_name) if isinstance(functions, dict) else None
        if not isinstance(entry, dict):
            return None, "function_not_in_manifest"
        return (
            FunctionFact(
                source_relation=str(entry.get("source_relation")),
                source_impact=str(entry.get("source_impact")),
                semantic_ground_truth=str(entry.get("semantic_ground_truth", TRUTH_UNKNOWN)),
                ground_truth_evidence=entry.get("ground_truth_evidence"),
            ),
            "ok",
        )


@dataclass(frozen=True)
class Classified:
    record: PairOutcome
    kind: str
    detail: str

    def as_dict(self) -> Dict[str, Any]:
        return {
            "kind": self.kind,
            "sample_identity": self.record.sample_identity,
            "function_name": self.record.function_name,
            "pair_id": self.record.pair_id,
            "label": self.record.label,
            "outcome": self.record.outcome,
            "detail": self.detail,
            "status_path": self.record.status_path,
        }


def classify_conditional(
    record: PairOutcome, manifest: Optional[FunctionDiffManifest],
) -> Classified:
    """Classify the assumption-dependent column with the same ground truth.

    Issue #20 gates the conditional lane in both directions -- an ``Eq`` sample
    judged conditionally ``NOT_EQ`` and a ``Neq`` sample judged conditionally
    ``EQUIVALENT`` are both violations -- but the counts stay in their own
    section so the unconditional gate cannot be moved by a conditional proof.
    """
    conditional = record.conditional_outcome
    if not conditional:
        return Classified(record, KIND_NOT_APPLICABLE, "")
    return classify(_as_conditional_record(record), manifest)


def _as_conditional_record(record: PairOutcome) -> PairOutcome:
    """View one pair through its conditional outcome, keeping its identity."""
    return PairOutcome(
        record.sample_identity,
        record.function_name,
        record.left_binary_id,
        record.right_binary_id,
        str(record.conditional_outcome),
        record.status_path,
        conditional_outcome=record.conditional_outcome,
    )


def classify(record: PairOutcome, manifest: Optional[FunctionDiffManifest]) -> Classified:
    label = record.label
    outcome = record.outcome
    if label == LABEL_EQ:
        if outcome == OUTCOME_NOT_EQ:
            return Classified(record, KIND_EQ_NOT_EQ, "Eq sample: single source on both sides")
        return Classified(record, KIND_NOT_APPLICABLE, "")
    if label != LABEL_NEQ or outcome not in (OUTCOME_EQ, OUTCOME_NOT_EQ):
        return Classified(record, KIND_NOT_APPLICABLE, "")

    fact, reason = (None, "no_manifest") if manifest is None else manifest.lookup(
        record.sample_identity, record.function_name
    )
    if fact is None:
        if outcome == OUTCOME_EQ:
            return Classified(record, KIND_NEQ_EQUIVALENT_UNMAPPED, reason)
        return Classified(record, KIND_NOT_APPLICABLE, reason)

    impact = f"source_relation={fact.source_relation} source_impact={fact.source_impact}"
    if outcome == OUTCOME_EQ:
        if fact.semantic_ground_truth == TRUTH_NOT_EQ:
            return Classified(
                record, KIND_NEQ_CONFIRMED_NOT_EQ_EQUIVALENT,
                f"{impact} ground_truth=CONFIRMED_NOT_EQ ({fact.ground_truth_evidence})",
            )
        if fact.semantic_ground_truth == TRUTH_EQ:
            return Classified(
                record, KIND_BENIGN_EQ_CONFIRMED,
                f"{impact} ground_truth=CONFIRMED_EQ ({fact.ground_truth_evidence})",
            )
        if fact.source_impact == IMPACT_NONE:
            return Classified(record, KIND_BENIGN_EQ_NO_IMPACT, impact)
        return Classified(record, KIND_SUSPICIOUS_EQ, f"{impact} ground_truth=UNKNOWN")
    # NOT_EQ on a Neq pair
    if fact.semantic_ground_truth == TRUTH_EQ:
        return Classified(
            record, KIND_NEQ_CONFIRMED_EQ_NOT_EQ,
            f"{impact} ground_truth=CONFIRMED_EQ ({fact.ground_truth_evidence})",
        )
    if fact.source_impact == IMPACT_NONE and fact.semantic_ground_truth != TRUTH_NOT_EQ:
        return Classified(record, KIND_SUSPICIOUS_NOT_EQ, f"{impact} ground_truth={fact.semantic_ground_truth}")
    return Classified(record, KIND_NOT_APPLICABLE, impact)


@dataclass(frozen=True)
class GateReport:
    classified: Tuple[Classified, ...]
    manifest_path: Optional[str]
    fail_on_suspicious: bool = False
    # Issue #20: rows whose assumption-dependent outcome is classified against
    # the same ground truth.  Empty until the conditional lane is activated.
    conditional_classified: Tuple[Classified, ...] = ()

    @property
    def pairs(self) -> int:
        return len(self.classified)

    @property
    def counts(self) -> Counter:
        return Counter(item.kind for item in self.classified)

    @property
    def hard_violations(self) -> Tuple[Classified, ...]:
        return tuple(item for item in self.classified if item.kind in HARD_VIOLATION_KINDS)

    @property
    def suspicious(self) -> Tuple[Classified, ...]:
        return tuple(item for item in self.classified if item.kind in SUSPICIOUS_KINDS)

    @property
    def conditional_pairs(self) -> int:
        return len(self.conditional_classified)

    @property
    def conditional_counts(self) -> Counter:
        return Counter(item.kind for item in self.conditional_classified)

    @property
    def conditional_hard_violations(self) -> Tuple[Classified, ...]:
        return tuple(
            item for item in self.conditional_classified
            if item.kind in HARD_VIOLATION_KINDS
        )

    @property
    def conditional_suspicious(self) -> Tuple[Classified, ...]:
        return tuple(
            item for item in self.conditional_classified if item.kind in SUSPICIOUS_KINDS
        )

    @property
    def status(self) -> str:
        if not self.classified:
            return GATE_STATUS_EMPTY
        if self.hard_violations or self.conditional_hard_violations:
            return GATE_STATUS_FAIL
        if self.fail_on_suspicious and (self.suspicious or self.conditional_suspicious):
            return GATE_STATUS_FAIL
        return GATE_STATUS_PASS

    @property
    def exit_code(self) -> int:
        if self.status == GATE_STATUS_EMPTY:
            return EXIT_EMPTY
        return EXIT_VIOLATION if self.status == GATE_STATUS_FAIL else EXIT_PASS

    def label_outcome_counts(self) -> Dict[str, Dict[str, int]]:
        table: Dict[str, Dict[str, int]] = {}
        for item in self.classified:
            row = table.setdefault(item.record.label, {})
            row[item.record.outcome] = row.get(item.record.outcome, 0) + 1
        return {label: dict(sorted(row.items())) for label, row in sorted(table.items())}

    def health_section(self) -> Dict[str, Any]:
        """The compact block merged into ``run_health_summary.json``."""
        counts = self.counts
        return {
            "gate": self.status,
            "pairs": self.pairs,
            "manifest": self.manifest_path,
            "fail_on_suspicious": self.fail_on_suspicious,
            "hard_violations": {kind: counts.get(kind, 0) for kind in HARD_VIOLATION_KINDS},
            "suspicious": {kind: counts.get(kind, 0) for kind in SUSPICIOUS_KINDS},
            "benign": {kind: counts.get(kind, 0) for kind in BENIGN_KINDS},
            "outcomes_by_label": self.label_outcome_counts(),
            "conditional": self.conditional_section(),
        }

    def conditional_section(self) -> Dict[str, Any]:
        """The assumption-dependent counts, kept out of the columns above."""
        counts = self.conditional_counts
        return {
            "pairs": self.conditional_pairs,
            "hard_violations": {
                kind: counts.get(kind, 0) for kind in HARD_VIOLATION_KINDS
            },
            "suspicious": {kind: counts.get(kind, 0) for kind in SUSPICIOUS_KINDS},
            "benign": {kind: counts.get(kind, 0) for kind in BENIGN_KINDS},
            "outcomes_by_label": self.conditional_label_outcome_counts(),
        }

    def conditional_label_outcome_counts(self) -> Dict[str, Dict[str, int]]:
        table: Dict[str, Dict[str, int]] = {}
        for item in self.conditional_classified:
            row = table.setdefault(item.record.label, {})
            outcome = str(item.record.conditional_outcome)
            row[outcome] = row.get(outcome, 0) + 1
        return {label: dict(sorted(row.items())) for label, row in sorted(table.items())}

    def as_dict(self) -> Dict[str, Any]:
        return {
            **self.health_section(),
            "rows": [
                item.as_dict()
                for item in self.classified
                if item.kind in HARD_VIOLATION_KINDS + SUSPICIOUS_KINDS
            ],
            "conditional_rows": [
                item.as_dict()
                for item in self.conditional_classified
                if item.kind in HARD_VIOLATION_KINDS + SUSPICIOUS_KINDS
            ],
        }


def build_gate_report(
    roots: Sequence[Path],
    manifest: Optional[FunctionDiffManifest],
    *,
    manifest_path: Optional[str] = None,
    fail_on_suspicious: bool = False,
) -> GateReport:
    classified: List[Classified] = []
    conditional: List[Classified] = []
    for root in roots:
        for record in iter_pair_outcomes(root):
            classified.append(classify(record, manifest))
            if record.conditional_outcome:
                conditional.append(classify_conditional(record, manifest))
    return GateReport(
        classified=tuple(classified), manifest_path=manifest_path, fail_on_suspicious=fail_on_suspicious,
        conditional_classified=tuple(conditional),
    )


def format_gate_report(report: GateReport) -> str:
    lines = [f"Pairs checked: {report.pairs}", "", "Outcomes by benchmark label:"]
    for label, row in report.label_outcome_counts().items():
        lines.append(f"  {label}: " + " ".join(f"{outcome}={count}" for outcome, count in row.items()))
    lines.append("")
    lines.append("Benchmark validation:")
    lines.extend(format_benchmark_validation_lines(report.health_section()))
    lines.append("")
    for title, rows in (
        ("Hard violations", report.hard_violations),
        ("Suspicious", report.suspicious),
        ("Conditional hard violations", report.conditional_hard_violations),
        ("Conditional suspicious", report.conditional_suspicious),
    ):
        if rows:
            lines.append(f"{title} ({len(rows)}):")
            for item in rows:
                lines.append(
                    f"  {item.kind}: {item.record.sample_identity} {item.record.function_name} "
                    f"{item.record.pair_id} -> {item.record.outcome} [{item.detail}]"
                )
            lines.append("")
    status = report.status
    if status == GATE_STATUS_EMPTY:
        lines.append("GATE: EMPTY (no pair status found)")
    elif status == GATE_STATUS_FAIL:
        # The conditional clause is appended only when the run produced one, so
        # a run without a conditional lane prints exactly what it printed before.
        conditional = (
            f", {len(report.conditional_hard_violations)} conditional hard violations"
            if report.conditional_classified
            else ""
        )
        lines.append(
            f"GATE: FAIL ({len(report.hard_violations)} hard violations, "
            f"{len(report.suspicious)} suspicious{conditional})"
        )
    else:
        lines.append(f"GATE: PASS ({len(report.suspicious)} suspicious)")
    return "\n".join(lines) + "\n"


def merge_into_health_summary(
    report: GateReport, *, json_path: Optional[Path], text_path: Optional[Path],
) -> None:
    """Record the gate in ``run_health_summary.json`` / ``.txt`` (creating them if absent)."""
    health: Dict[str, Any] = {}
    if json_path is not None and json_path.is_file():
        try:
            loaded = json.loads(json_path.read_text(encoding="utf-8"))
        except ValueError:
            loaded = {}
        if isinstance(loaded, dict):
            health = loaded
    health[HEALTH_KEY] = report.health_section()
    if json_path is not None:
        json_path.parent.mkdir(parents=True, exist_ok=True)
        json_path.write_text(json.dumps(health, indent=1, sort_keys=True) + "\n", encoding="utf-8")
    if text_path is not None:
        text_path.parent.mkdir(parents=True, exist_ok=True)
        text_path.write_text(format_run_health_summary(health) + "\n", encoding="utf-8")


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("roots", nargs="+", type=Path, help="result trees to check")
    parser.add_argument("--manifest", type=Path, default=None,
                        help="function diff manifest JSON (scripts/eqbench/function_diff_manifest.py); "
                             "without it every Neq EQUIVALENT is unmapped and fails the gate")
    parser.add_argument("--json", type=Path, default=None, help="write the full report as JSON")
    parser.add_argument("--health-summary-json", type=Path, default=None,
                        help="run_health_summary.json to merge the gate section into")
    parser.add_argument("--health-summary-text", type=Path, default=None,
                        help="run_health_summary.txt to rewrite from the merged JSON")
    parser.add_argument("--fail-on-suspicious", action="store_true",
                        help="also fail the gate on suspicious rows (default: count only)")
    return parser


def main(argv: Optional[Sequence[str]] = None) -> int:
    args = build_parser().parse_args(argv)
    for root in args.roots:
        if not root.is_dir():
            print(f"error: not a directory: {root}", file=sys.stderr)
            return EXIT_EMPTY
    manifest = None
    if args.manifest is not None:
        try:
            manifest = FunctionDiffManifest.load(args.manifest)
        except (OSError, ValueError) as exc:
            print(f"error: cannot read function diff manifest: {exc}", file=sys.stderr)
            return EXIT_EMPTY
    report = build_gate_report(
        args.roots, manifest,
        manifest_path=None if args.manifest is None else str(args.manifest),
        fail_on_suspicious=args.fail_on_suspicious,
    )
    if args.json is not None:
        args.json.parent.mkdir(parents=True, exist_ok=True)
        args.json.write_text(json.dumps(report.as_dict(), indent=1) + "\n", encoding="utf-8")
    if args.health_summary_json is not None or args.health_summary_text is not None:
        merge_into_health_summary(
            report, json_path=args.health_summary_json, text_path=args.health_summary_text,
        )
    sys.stdout.write(format_gate_report(report))
    return report.exit_code


if __name__ == "__main__":
    sys.exit(main())
