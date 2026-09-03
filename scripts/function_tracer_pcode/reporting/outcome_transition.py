# -*- coding: utf-8 -*-
"""Function x pair outcome transition table between two result trees.

Usage::

    python3 -m scripts.function_tracer_pcode.reporting.outcome_transition \
        --before logs/EqBench/subset_before --after logs/EqBench/subset_after \
        [--json transition.json] [--changed-only] [--fail-on-change]

The table counts how many pairs moved from each outcome in ``--before`` to
each outcome in ``--after``; pairs present in only one tree are reported as
``MISSING`` on the other side. It says nothing about which side is correct.
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
    OUTCOME_MISSING,
    OUTCOME_ORDER,
    PairKey,
    PairOutcome,
    load_pair_outcomes,
)


@dataclass(frozen=True)
class TransitionRow:
    sample_identity: str
    function_name: str
    pair_id: str
    before: str
    after: str

    @property
    def changed(self) -> bool:
        return self.before != self.after

    def as_dict(self) -> Dict[str, object]:
        return {
            "sample_identity": self.sample_identity,
            "function_name": self.function_name,
            "pair_id": self.pair_id,
            "before": self.before,
            "after": self.after,
            "changed": self.changed,
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

    def as_dict(self) -> Dict[str, object]:
        return {
            "pairs": len(self.rows),
            "changed": len(self.changed_rows),
            "outcomes": list(self.outcomes),
            "matrix": [
                {"before": before, "after": after, "count": count}
                for (before, after), count in sorted(self.matrix.items())
            ],
            "rows": [row.as_dict() for row in self.rows],
        }


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
    return "\n".join(lines) + "\n"


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--before", required=True, type=Path, help="result tree of the earlier run")
    parser.add_argument("--after", required=True, type=Path, help="result tree of the later run")
    parser.add_argument("--json", type=Path, default=None, help="write the report as JSON to this path")
    parser.add_argument("--changed-only", action="store_true", help="list only pairs whose outcome changed")
    parser.add_argument(
        "--fail-on-change",
        action="store_true",
        help="exit 2 when any pair changed outcome or is missing on one side",
    )
    return parser


def main(argv: Optional[Sequence[str]] = None) -> int:
    args = build_parser().parse_args(argv)
    for path in (args.before, args.after):
        if not path.is_dir():
            print(f"error: not a directory: {path}", file=sys.stderr)
            return 1
    report = build_transition(load_pair_outcomes(args.before), load_pair_outcomes(args.after))
    if args.json is not None:
        args.json.write_text(json.dumps(report.as_dict(), indent=1) + "\n", encoding="utf-8")
    sys.stdout.write(format_transition(report, changed_only=args.changed_only))
    if args.fail_on_change and report.changed_rows:
        return 2
    return 0


if __name__ == "__main__":
    sys.exit(main())
