# -*- coding: utf-8 -*-
"""Build a Phase 0B UNKNOWN reason correspondence diagnostics gate.

This gate makes the parser diagnostics required by the plan an explicit
artifact.  It compares the primary validation UNKNOWN unit tuples with typed
reason records and proof actions, then classifies every mismatch as one of the
allowed correspondence categories.
"""

from __future__ import annotations

import argparse
import json
from collections import Counter
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Dict, Mapping, Optional, Sequence

from .result_summary import STATUS_TIMEOUT, STATUS_UNKNOWN, aggregate_validation_logs
from .unknown_reason_summary import diagnose_unknown_reason_correspondence, summarize_validation_unknowns


MANIFEST_VERSION = 1
EXPECTED_BASELINE_ID = "observed-v0@0a53352"
EXPECTED_GIT_HEAD = "0a53352cf3c9528abfb654906ed7b963474bedc5"
EXPECTED_CATEGORIES = ("function_call", "loop")
ALLOWED_CORRESPONDENCE_CLASSIFICATIONS = frozenset(
    {
        "aggregation_difference",
        "detail_missing",
        "parser_bug",
        "proof_action_expansion",
        "raw_log_missing",
    }
)
BLOCKING_CORRESPONDENCE_CLASSIFICATIONS = frozenset(
    {
        "parser_bug",
        "raw_log_missing",
    }
)


def build_phase0b_unknown_reason_correspondence_gate(
    *,
    baseline_raw_dir: Path,
    output_dir: Path,
    categories: Sequence[str] = EXPECTED_CATEGORIES,
) -> Path:
    raw_dir = Path(baseline_raw_dir)
    output = Path(output_dir)
    output.mkdir(parents=True, exist_ok=True)

    raw_manifest = _read_json(raw_dir / "artifact_manifest.json")
    category_reports: Dict[str, Any] = {}
    checks = []
    checks.extend(_baseline_identity_checks(raw_manifest))

    combined_counts: Counter[str] = Counter()
    combined_blocking_counts: Counter[str] = Counter()
    for category in tuple(str(item) for item in categories):
        report = _build_category_report(raw_dir / "logs" / category)
        category_reports[category] = report
        combined_counts.update(report["classification_counts"])
        combined_blocking_counts.update(report["blocking_classification_counts"])
        checks.extend(_category_checks(category, report))

    checks.append(
        _ok("correspondence_blocking_classifications_absent")
        if not combined_blocking_counts
        else _failed(
            "correspondence_blocking_classifications_absent",
            blocking_classification_counts=dict(sorted(combined_blocking_counts.items())),
        )
    )

    summary = _summary(checks)
    manifest = {
        "manifest_version": MANIFEST_VERSION,
        "manifest_kind": "phase0b_unknown_reason_correspondence_gate",
        "artifact_role": "derived_observed_baseline_unknown_reason_correspondence_diagnostics",
        "created_at": datetime.now(timezone.utc).isoformat(),
        "baseline_id": raw_manifest.get("baseline_id"),
        "baseline_git_head": raw_manifest.get("git_head"),
        "baseline_raw_artifact_ref": {
            "path": str(raw_dir / "artifact_manifest.json"),
        },
        "diagnostic_model": {
            "required_classification_enum": sorted(ALLOWED_CORRESPONDENCE_CLASSIFICATIONS),
            "blocking_classifications": sorted(BLOCKING_CORRESPONDENCE_CLASSIFICATIONS),
            "non_blocking_classifications": sorted(
                ALLOWED_CORRESPONDENCE_CLASSIFICATIONS - BLOCKING_CORRESPONDENCE_CLASSIFICATIONS
            ),
            "comparison": "validation_unknown_unit_vs_reason_record_vs_proof_action",
        },
        "categories": category_reports,
        "combined_classification_counts": dict(sorted(combined_counts.items())),
        "combined_blocking_classification_counts": dict(sorted(combined_blocking_counts.items())),
        "phase0b_unknown_reason_correspondence_ready": summary["failed"] == 0,
        "summary": summary,
        "checks": checks,
    }
    path = output / "phase0b_unknown_reason_correspondence_gate.json"
    _write_json(path, manifest)
    return path


def validate_phase0b_unknown_reason_correspondence_gate(manifest: Mapping[str, Any]) -> None:
    if manifest.get("phase0b_unknown_reason_correspondence_ready") is True:
        return
    summary = manifest.get("summary")
    if not isinstance(summary, Mapping):
        raise ValueError("Phase 0B UNKNOWN reason correspondence gate is not ready and summary is missing")
    failed = summary.get("failed_kinds") or ()
    if not failed:
        raise ValueError("Phase 0B UNKNOWN reason correspondence gate is not ready without failed gate kinds")
    raise ValueError(f"Phase 0B UNKNOWN reason correspondence gate failed: {', '.join(map(str, failed))}")


def main(argv: Optional[Sequence[str]] = None) -> int:
    parser = argparse.ArgumentParser(description="Build a Phase 0B UNKNOWN reason correspondence gate.")
    parser.add_argument("--baseline-raw-dir", required=True)
    parser.add_argument("--output-dir", required=True)
    parser.add_argument("--category", action="append", default=None)
    parser.add_argument("--require-ready", action="store_true")
    args = parser.parse_args(argv)

    path = build_phase0b_unknown_reason_correspondence_gate(
        baseline_raw_dir=Path(args.baseline_raw_dir),
        output_dir=Path(args.output_dir),
        categories=tuple(args.category or EXPECTED_CATEGORIES),
    )
    print(path)
    if args.require_ready:
        validate_phase0b_unknown_reason_correspondence_gate(_read_json(path))
    return 0


def _build_category_report(log_root: Path) -> Dict[str, Any]:
    root = Path(log_root)
    log_paths = sorted(root.glob("*/*.log"))
    aggregate = aggregate_validation_logs(log_paths)
    payloads = [payload for record in aggregate.records for payload in record.payloads]
    summary = summarize_validation_unknowns(payloads)
    diagnostics = [item.to_dict() for item in diagnose_unknown_reason_correspondence(summary)]

    missing_payload_entries = [
        {
            "classification": "raw_log_missing",
            "log_path": record.path,
            "function": record.function_name,
            "binary_pair": record.pair_label,
            "status": record.status,
            "detail": "UNKNOWN/TIMEOUT log has no typed equivalence result JSON payload",
        }
        for record in aggregate.records
        if record.status in {STATUS_UNKNOWN, STATUS_TIMEOUT} and not record.payloads
    ]
    classifications = [
        str(item.get("classification"))
        for item in diagnostics
        if isinstance(item, Mapping)
    ] + [str(item["classification"]) for item in missing_payload_entries]
    classification_counts = Counter(classifications)
    blocking_counts = Counter(
        classification
        for classification in classifications
        if classification in BLOCKING_CORRESPONDENCE_CLASSIFICATIONS
    )
    unexpected = sorted(set(classifications) - ALLOWED_CORRESPONDENCE_CLASSIFICATIONS)

    return {
        "log_root": str(root),
        "pair_log_count": len(log_paths),
        "unknown_or_timeout_log_count": sum(
            1 for record in aggregate.records if record.status in {STATUS_UNKNOWN, STATUS_TIMEOUT}
        ),
        "typed_payload_count": len(payloads),
        "typed_unknown_result_count": summary.unknown_results,
        "typed_validation_unknown_units": summary.unknown_units,
        "classification_counts": dict(sorted(classification_counts.items())),
        "blocking_classification_counts": dict(sorted(blocking_counts.items())),
        "unexpected_classifications": unexpected,
        "correspondence_diagnostics": diagnostics,
        "missing_payload_entries": missing_payload_entries[:50],
        "missing_payload_entry_count": len(missing_payload_entries),
    }


def _baseline_identity_checks(raw_manifest: Mapping[str, Any]) -> Sequence[Dict[str, Any]]:
    raw_baseline_id = raw_manifest.get("baseline_id")
    raw_git_head = raw_manifest.get("git_head")
    return [
        _ok("baseline_id_expected", baseline_id=raw_baseline_id)
        if raw_baseline_id == EXPECTED_BASELINE_ID
        else _failed("baseline_id_expected", expected=EXPECTED_BASELINE_ID, actual=raw_baseline_id),
        _ok("baseline_git_head_expected", baseline_git_head=raw_git_head)
        if raw_git_head == EXPECTED_GIT_HEAD
        else _failed("baseline_git_head_expected", expected=EXPECTED_GIT_HEAD, actual=raw_git_head),
    ]


def _category_checks(category: str, report: Mapping[str, Any]) -> Sequence[Dict[str, Any]]:
    unexpected = report.get("unexpected_classifications") or ()
    blocking = report.get("blocking_classification_counts") or {}
    return [
        _ok("category_logs_present", category=category, count=report.get("pair_log_count"))
        if int(report.get("pair_log_count") or 0) > 0
        else _failed("category_logs_present", category=category, count=report.get("pair_log_count")),
        _ok("correspondence_classifications_known", category=category)
        if not unexpected
        else _failed("correspondence_classifications_known", category=category, unexpected=unexpected),
        _ok("category_blocking_correspondence_absent", category=category)
        if not blocking
        else _failed(
            "category_blocking_correspondence_absent",
            category=category,
            blocking_classification_counts=dict(blocking),
        ),
    ]


def _summary(checks: Sequence[Mapping[str, Any]]) -> Dict[str, Any]:
    failed_kinds = sorted({str(check.get("kind")) for check in checks if check.get("status") == "failed"})
    return {
        "total": len(checks),
        "passed": sum(1 for check in checks if check.get("status") == "ok"),
        "failed": sum(1 for check in checks if check.get("status") == "failed"),
        "failed_kinds": failed_kinds,
    }


def _ok(kind: str, **details: Any) -> Dict[str, Any]:
    result = {"kind": kind, "status": "ok"}
    result.update(details)
    return result


def _failed(kind: str, **details: Any) -> Dict[str, Any]:
    result = {"kind": kind, "status": "failed"}
    result.update(details)
    return result


def _read_json(path: Path) -> Dict[str, Any]:
    with path.open("r", encoding="utf-8") as handle:
        payload = json.load(handle)
    if not isinstance(payload, dict):
        raise ValueError(f"expected JSON object in {path}")
    return payload


def _write_json(path: Path, payload: Any) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")


if __name__ == "__main__":
    raise SystemExit(main())
