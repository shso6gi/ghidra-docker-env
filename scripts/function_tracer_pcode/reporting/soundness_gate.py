# -*- coding: utf-8 -*-
"""Soundness gate over benchmark labels.

Usage::

    python3 -m scripts.function_tracer_pcode.reporting.soundness_gate \
        logs/EqBench/subset_current/eq logs/EqBench/subset_current/neq [--json gate.json]

The gate uses only the dataset label encoded in each sample path: a pair from
an ``Eq`` sample must never be judged ``NOT_EQ`` and a pair from a ``Neq``
sample must never be judged ``EQUIVALENT``. Any such pair is a soundness
violation and the command exits 1. UNKNOWN/TIMEOUT/ERROR are not violations.
Exit 2 means the trees contained no pair status at all (an empty tree is not
a pass).
"""

from __future__ import annotations

import argparse
import json
import sys
from collections import Counter
from dataclasses import dataclass
from pathlib import Path
from typing import Dict, List, Optional, Sequence, Tuple

from scripts.function_tracer_pcode.reporting.pair_outcomes import (
    LABEL_EQ,
    LABEL_NEQ,
    LABEL_UNLABELLED,
    OUTCOME_ORDER,
    PairOutcome,
    iter_pair_outcomes,
)

EXIT_PASS = 0
EXIT_VIOLATION = 1
EXIT_EMPTY = 2

FORBIDDEN_OUTCOME = {LABEL_EQ: "NOT_EQ", LABEL_NEQ: "EQUIVALENT"}


def is_violation(record: PairOutcome) -> bool:
    return FORBIDDEN_OUTCOME.get(record.label) == record.outcome


@dataclass(frozen=True)
class GateReport:
    records: Tuple[PairOutcome, ...]

    @property
    def violations(self) -> Tuple[PairOutcome, ...]:
        return tuple(record for record in self.records if is_violation(record))

    @property
    def counts(self) -> Counter:
        return Counter((record.label, record.outcome) for record in self.records)

    @property
    def passed(self) -> bool:
        return bool(self.records) and not self.violations

    def as_dict(self) -> Dict[str, object]:
        return {
            "pairs": len(self.records),
            "violations": len(self.violations),
            "passed": self.passed,
            "counts": [
                {"label": label, "outcome": outcome, "count": count}
                for (label, outcome), count in sorted(self.counts.items())
            ],
            "violation_rows": [
                {
                    "sample_identity": record.sample_identity,
                    "function_name": record.function_name,
                    "pair_id": record.pair_id,
                    "label": record.label,
                    "outcome": record.outcome,
                    "status_path": record.status_path,
                }
                for record in self.violations
            ],
        }


def build_gate_report(roots: Sequence[Path]) -> GateReport:
    records: List[PairOutcome] = []
    for root in roots:
        records.extend(iter_pair_outcomes(root))
    return GateReport(records=tuple(records))


def format_gate_report(report: GateReport) -> str:
    counts = report.counts
    labels = [label for label in (LABEL_EQ, LABEL_NEQ, LABEL_UNLABELLED) if any(k[0] == label for k in counts)]
    outcomes = [name for name in OUTCOME_ORDER if any(k[1] == name for k in counts)]
    outcomes.extend(sorted({k[1] for k in counts} - set(OUTCOME_ORDER)))
    lines = [f"Pairs checked: {len(report.records)}", "", "Outcomes by benchmark label:"]
    width = max([len("label")] + [len(name) for name in outcomes] + [len(name) for name in labels])
    lines.append("label".ljust(width) + "".join(name.rjust(width + 2) for name in outcomes))
    for label in labels:
        lines.append(
            label.ljust(width)
            + "".join(str(counts.get((label, outcome), 0)).rjust(width + 2) for outcome in outcomes)
        )
    lines.append("")
    violations = report.violations
    if not report.records:
        lines.append("GATE: EMPTY (no pair status found)")
    elif violations:
        lines.append(f"Soundness violations ({len(violations)}):")
        for record in violations:
            lines.append(
                f"  {record.label} sample judged {record.outcome}: "
                f"{record.sample_identity} {record.function_name} {record.pair_id}"
            )
        lines.append("")
        lines.append(f"GATE: FAIL ({len(violations)} violations)")
    else:
        lines.append("GATE: PASS")
    return "\n".join(lines) + "\n"


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("roots", nargs="+", type=Path, help="result trees to check")
    parser.add_argument("--json", type=Path, default=None, help="write the report as JSON to this path")
    return parser


def main(argv: Optional[Sequence[str]] = None) -> int:
    args = build_parser().parse_args(argv)
    for root in args.roots:
        if not root.is_dir():
            print(f"error: not a directory: {root}", file=sys.stderr)
            return EXIT_EMPTY
    report = build_gate_report(args.roots)
    if args.json is not None:
        args.json.write_text(json.dumps(report.as_dict(), indent=1) + "\n", encoding="utf-8")
    sys.stdout.write(format_gate_report(report))
    if not report.records:
        return EXIT_EMPTY
    if report.violations:
        return EXIT_VIOLATION
    return EXIT_PASS


if __name__ == "__main__":
    sys.exit(main())
