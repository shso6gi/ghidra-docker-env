# -*- coding: utf-8 -*-
"""Build compact run-health summaries from validation artifacts.

The fast path consumes ``overall_summary.txt`` so routine triage does not need
to reread every large pair log.
"""

from __future__ import annotations

import argparse
import json
import re
from pathlib import Path
from typing import Any, Dict, Mapping, Optional, Sequence

from scripts.function_tracer_pcode.reporting.result_summary import (
    STATUS_EQ,
    STATUS_ERROR,
    STATUS_INCOMPLETE,
    STATUS_NOT_EQ,
    STATUS_TIMEOUT,
    STATUS_UNKNOWN,
    format_run_health_summary,
)


_TOTALS_RE = re.compile(
    r"TOTAL=\s*(?P<TOTAL>\d+),\s*"
    r"EQ=\s*(?P<EQ>\d+),\s*"
    r"NOT_EQ=\s*(?P<NOT_EQ>\d+),\s*"
    r"ERROR=\s*(?P<ERROR>\d+),\s*"
    r"UNKNOWN=\s*(?P<UNKNOWN>\d+),\s*"
    r"TIMEOUT=\s*(?P<TIMEOUT>\d+),\s*"
    r"INCOMPLETE=\s*(?P<INCOMPLETE>\d+)"
)
_FUNCTION_LINE_RE = re.compile(r"^\s{2}(?P<function>[A-Za-z0-9_:$.-]+)\s+: (?P<totals>.*)$")
_COUNT_LINE_RE = re.compile(r"^\s+- (?P<key>.+): (?P<count>-?\d+)$")


def parse_overall_summary_health(path: Path) -> Dict[str, Any]:
    text = Path(path).read_text(errors="replace")
    lines = text.splitlines()
    functions: Dict[str, Dict[str, int]] = {}
    final_counts = {
        STATUS_EQ: 0,
        STATUS_NOT_EQ: 0,
        STATUS_ERROR: 0,
        STATUS_UNKNOWN: 0,
        STATUS_TIMEOUT: 0,
        STATUS_INCOMPLETE: 0,
    }
    total_results = 0
    unknown_results = 0
    unknown_units = 0
    sections: Dict[str, Dict[str, int]] = {
        "unknown_by_reason": {},
        "proof_backlog_by_reason": {},
        "proof_backlog_by_proof_kind": {},
        "operational_unknown_by_reason": {},
    }
    active_section: Optional[str] = None
    section_titles = {
        "UNKNOWN by reason:": "unknown_by_reason",
        "Proof backlog by reason:": "proof_backlog_by_reason",
        "Proof backlog by proof_kind:": "proof_backlog_by_proof_kind",
        "Operational UNKNOWN by reason:": "operational_unknown_by_reason",
    }

    for line in lines:
        stripped = line.strip()
        if stripped.startswith("Unknown results:"):
            unknown_results = _trailing_int(stripped)
            active_section = None
            continue
        if stripped.startswith("Unknown units  :"):
            unknown_units = _trailing_int(stripped)
            active_section = None
            continue
        if stripped in section_titles:
            active_section = section_titles[stripped]
            continue
        if stripped.endswith(":") and not stripped.startswith("- "):
            active_section = None

        match = _FUNCTION_LINE_RE.match(line)
        if match and "Overall totals" not in line:
            totals = _parse_totals(match.group("totals"))
            if totals is not None:
                functions[match.group("function")] = totals
            active_section = None
            continue
        if "Overall totals" in line:
            totals = _parse_totals(line)
            if totals is not None:
                total_results = totals["total"]
                final_counts = {
                    STATUS_EQ: totals[STATUS_EQ],
                    STATUS_NOT_EQ: totals[STATUS_NOT_EQ],
                    STATUS_ERROR: totals[STATUS_ERROR],
                    STATUS_UNKNOWN: totals[STATUS_UNKNOWN],
                    STATUS_TIMEOUT: totals[STATUS_TIMEOUT],
                    STATUS_INCOMPLETE: totals[STATUS_INCOMPLETE],
                }
            active_section = None
            continue
        if active_section:
            count_match = _COUNT_LINE_RE.match(line)
            if count_match:
                sections[active_section][count_match.group("key")] = int(
                    count_match.group("count")
                )

    return {
        "source": "overall_summary_txt",
        "source_path": str(path),
        "total_results": total_results,
        "final_result_counts": final_counts,
        "unknown_results": unknown_results,
        "unknown_units": unknown_units,
        "functions": functions,
        **sections,
    }


def _parse_totals(text: str) -> Optional[Dict[str, int]]:
    match = _TOTALS_RE.search(text)
    if not match:
        return None
    return {
        "total": int(match.group("TOTAL")),
        STATUS_EQ: int(match.group("EQ")),
        STATUS_NOT_EQ: int(match.group("NOT_EQ")),
        STATUS_ERROR: int(match.group("ERROR")),
        STATUS_UNKNOWN: int(match.group("UNKNOWN")),
        STATUS_TIMEOUT: int(match.group("TIMEOUT")),
        STATUS_INCOMPLETE: int(match.group("INCOMPLETE")),
    }


def _trailing_int(text: str) -> int:
    match = re.search(r"(-?\d+)\s*$", text)
    return int(match.group(1)) if match else 0


def write_health_outputs(
    health: Mapping[str, Any],
    *,
    output_json: Optional[Path] = None,
    output_text: Optional[Path] = None,
    print_text: bool = False,
) -> None:
    if output_json is not None:
        output_json.parent.mkdir(parents=True, exist_ok=True)
        output_json.write_text(json.dumps(dict(health), indent=2, sort_keys=True) + "\n")
    rendered = format_run_health_summary(health)
    if output_text is not None:
        output_text.parent.mkdir(parents=True, exist_ok=True)
        output_text.write_text(rendered.rstrip() + "\n")
    if print_text:
        print(rendered)


def main(argv: Optional[Sequence[str]] = None) -> int:
    parser = argparse.ArgumentParser(description="Generate compact run-health summaries.")
    parser.add_argument("--overall-summary", required=True)
    parser.add_argument("--output-json")
    parser.add_argument("--output-text")
    parser.add_argument("--print-text", action="store_true")
    args = parser.parse_args(argv)

    health = parse_overall_summary_health(Path(args.overall_summary))
    write_health_outputs(
        health,
        output_json=Path(args.output_json) if args.output_json else None,
        output_text=Path(args.output_text) if args.output_text else None,
        print_text=args.print_text,
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
