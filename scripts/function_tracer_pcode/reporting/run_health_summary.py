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
    FAILURE_EVIDENCE_KEY,
    FAILURE_INTERNAL_BY_SITE_KEY,
    FAILURE_INTERNAL_BY_SITE_TITLE,
    FAILURE_INTERNAL_SURFACE,
    FAILURE_SWALLOWED_BY_TYPE_KEY,
    FAILURE_SWALLOWED_BY_TYPE_TITLE,
    FAILURE_SWALLOWED_OBSERVED_TOTAL_KEY,
    FAILURE_SWALLOWED_SURFACE,
    FAILURE_SWALLOWED_TOTAL_KEY,
    STATUS_EQ,
    STATUS_ERROR,
    STATUS_INCOMPLETE,
    STATUS_NOT_EQ,
    STATUS_TIMEOUT,
    STATUS_UNKNOWN,
    TIMEOUT_DIAGNOSTICS_KEY,
    format_run_health_summary,
    timeout_diagnostics_from_health,
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
# Issue #128: the two aggregation families and how much of the diagnostic source
# was observable.  A run whose diagnostic evidence is incomplete must not read
# back as a fully observed zero.
_FINAL_REASON_SOURCES_RE = re.compile(r"^\s+Final reason sources:\s*(?P<value>.*?)\s*$")
_DIAGNOSTIC_SOURCES_RE = re.compile(
    r"^\s+Diagnostic sources\s*:\s*(?P<value>.*?)"
    r"\s*\(observed (?P<observed>\d+) / missing (?P<missing>\d+)\)\s*$"
)
_CAUSAL_EVIDENCE_RE = re.compile(r"^\s+Causal evidence\s*:\s*(?P<value>.*?)\s*$")
_CAUSAL_BLOCK_RE = re.compile(
    r"(?P<name>[a-z_]+) observed (?P<observed>\d+) / missing (?P<missing>\d+)"
)
# Issue #125 PR-125-B: typed failure 診断の evidence と握り潰し合計。
# evidence は surface ごと（握り潰し台帳 / 内部エラー）。observed / missing /
# malformed を分けて往復させ、「読めなかった」を「0 件」と読ませない。
_FAILURE_EVIDENCE_RE = re.compile(
    r"^\s+(?P<label>Swallowed|Internal) exception evidence\s*:\s*"
    r"(?P<state>complete|partial|unknown)\s*"
    r"\(observed (?P<observed>\d+) / missing (?P<missing>\d+)"
    r" / malformed (?P<malformed>\d+)\)\s*$"
)
# 正確な合計（evidence complete）と、観測できた下限（incomplete）を別の形で書く。
_SWALLOWED_TOTAL_RE = re.compile(
    r"^\s+Swallowed exceptions total\s*:\s*"
    r"(?:(?P<exact>\d+)|unknown \(observed (?P<observed>\d+)\))\s*$"
)
_FAILURE_EVIDENCE_SURFACES = {
    "Swallowed": FAILURE_SWALLOWED_SURFACE,
    "Internal": FAILURE_INTERNAL_SURFACE,
}


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
        FAILURE_SWALLOWED_BY_TYPE_KEY: {},
        FAILURE_INTERNAL_BY_SITE_KEY: {},
    }
    failure_evidence: Dict[str, Dict[str, Any]] = {}
    swallowed_exact_total: Optional[int] = None
    swallowed_observed_total: Optional[int] = None
    active_section: Optional[str] = None
    # Issue #128: `(unknown)` = 証拠が無い、`(none)` = 実際に 0 件。どちらも
    # 空の section になるので、marker を見た section だけ別に記録する。
    evidence_missing_sections: list = []
    final_reason_sources: list = []
    diagnostic_sources: list = []
    diagnostic_evidence: Dict[str, int] = {}
    causal_evidence_counts: Dict[str, Dict[str, int]] = {}
    section_titles = {
        "UNKNOWN by reason:": "unknown_by_reason",
        "Proof backlog by reason:": "proof_backlog_by_reason",
        "Proof backlog by proof_kind:": "proof_backlog_by_proof_kind",
        "Operational UNKNOWN by reason:": "operational_unknown_by_reason",
        # Issue #125 PR-125-B。登録しないと直後の `- key: count` 行が
        # 前の section の続きとして読まれてしまう。
        f"{FAILURE_SWALLOWED_BY_TYPE_TITLE}:": FAILURE_SWALLOWED_BY_TYPE_KEY,
        f"{FAILURE_INTERNAL_BY_SITE_TITLE}:": FAILURE_INTERNAL_BY_SITE_KEY,
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
        source_match = _FINAL_REASON_SOURCES_RE.match(line)
        if source_match:
            final_reason_sources = _split_sources(source_match.group("value"))
            active_section = None
            continue
        diagnostic_match = _DIAGNOSTIC_SOURCES_RE.match(line)
        if diagnostic_match:
            diagnostic_sources = _split_sources(diagnostic_match.group("value"))
            diagnostic_evidence = {
                "observed": int(diagnostic_match.group("observed")),
                "missing": int(diagnostic_match.group("missing")),
            }
            active_section = None
            continue
        failure_evidence_match = _FAILURE_EVIDENCE_RE.match(line)
        if failure_evidence_match:
            surface = _FAILURE_EVIDENCE_SURFACES[failure_evidence_match.group("label")]
            failure_evidence[surface] = {
                "state": failure_evidence_match.group("state"),
                "observed": int(failure_evidence_match.group("observed")),
                "missing": int(failure_evidence_match.group("missing")),
                "malformed": int(failure_evidence_match.group("malformed")),
            }
            active_section = None
            continue
        swallowed_total_match = _SWALLOWED_TOTAL_RE.match(line)
        if swallowed_total_match:
            exact = swallowed_total_match.group("exact")
            observed = swallowed_total_match.group("observed")
            # `unknown (observed N)` は下限であって合計ではない。exact は None。
            swallowed_exact_total = None if exact is None else int(exact)
            swallowed_observed_total = int(exact if exact is not None else observed)
            active_section = None
            continue
        causal_match = _CAUSAL_EVIDENCE_RE.match(line)
        if causal_match:
            causal_evidence_counts = {
                block.group("name"): {
                    "observed": int(block.group("observed")),
                    "missing": int(block.group("missing")),
                }
                for block in _CAUSAL_BLOCK_RE.finditer(causal_match.group("value"))
            }
            active_section = None
            continue
        if active_section and stripped in ("(unknown)", "(none)"):
            if stripped == "(unknown)" and active_section not in evidence_missing_sections:
                evidence_missing_sections.append(active_section)
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
        "evidence_missing_sections": evidence_missing_sections,
        "final_reason_sources": final_reason_sources,
        "diagnostic_sources": diagnostic_sources,
        "diagnostic_evidence": diagnostic_evidence,
        "causal_evidence_counts": causal_evidence_counts,
        FAILURE_EVIDENCE_KEY: failure_evidence,
        # 行が無い（PR-125-B 以前の summary）ときも、evidence が incomplete な
        # ときも exact total は `None`。**0 に変換しない**。下限は別 key に持つ。
        FAILURE_SWALLOWED_TOTAL_KEY: swallowed_exact_total,
        FAILURE_SWALLOWED_OBSERVED_TOTAL_KEY: swallowed_observed_total,
        **sections,
    }


def _split_sources(text: str) -> list:
    return [item for item in (part.strip() for part in text.split(",")) if item and item != "(none)"]


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


def merge_timeout_diagnostics(
    health: Dict[str, Any], report_path: Optional[Path],
) -> Dict[str, Any]:
    """Issue #124 PR-124-C: TIMEOUT 診断の節を health に足す。

    `timeout_hotspot_summary` が書いた report JSON（または既に merge 済みの
    health JSON）から節だけを取る。path を渡さない / 読めない場合は **key を
    足さない**: 節が無いことを「TIMEOUT 0 件」と読ませないため。
    """

    if report_path is None:
        return health
    try:
        payload = json.loads(Path(report_path).read_text(encoding="utf-8"))
    except (OSError, ValueError):
        return health
    if not isinstance(payload, dict):
        return health
    section = timeout_diagnostics_from_health(payload)
    if section is None:
        # report JSON そのものは節を平らに持っている（`pairs` / `timeout_kind`）。
        section = payload if "timeout_kind" in payload and "pairs" in payload else None
    if section is None:
        return health
    health[TIMEOUT_DIAGNOSTICS_KEY] = dict(section)
    return health


def main(argv: Optional[Sequence[str]] = None) -> int:
    parser = argparse.ArgumentParser(description="Generate compact run-health summaries.")
    parser.add_argument("--overall-summary", required=True)
    parser.add_argument("--output-json")
    parser.add_argument("--output-text")
    parser.add_argument("--print-text", action="store_true")
    parser.add_argument(
        "--timeout-hotspots-json",
        help="timeout_hotspot_summary の report JSON を timeout_diagnostics 節として取り込む",
    )
    args = parser.parse_args(argv)

    health = parse_overall_summary_health(Path(args.overall_summary))
    health = merge_timeout_diagnostics(
        health,
        Path(args.timeout_hotspots_json) if args.timeout_hotspots_json else None,
    )
    write_health_outputs(
        health,
        output_json=Path(args.output_json) if args.output_json else None,
        output_text=Path(args.output_text) if args.output_text else None,
        print_text=args.print_text,
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
