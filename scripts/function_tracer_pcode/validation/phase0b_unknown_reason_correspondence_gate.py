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
from typing import Any, Dict, Iterable, Mapping, Optional, Sequence

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
EXPECTED_CATEGORY_CLASSIFICATION_COUNTS: Mapping[str, Mapping[str, int]] = {
    "function_call": {
        "aggregation_difference": 3,
        "proof_action_expansion": 11,
    },
    "loop": {
        "aggregation_difference": 2,
        "proof_action_expansion": 13,
    },
}
EXPECTED_COMBINED_CLASSIFICATION_COUNTS: Mapping[str, int] = {
    "aggregation_difference": 5,
    "proof_action_expansion": 24,
}


def build_phase0b_unknown_reason_correspondence_gate(
    *,
    baseline_raw_dir: Path,
    output_dir: Path,
    current_log_roots: Optional[Mapping[str, Path]] = None,
    categories: Sequence[str] = EXPECTED_CATEGORIES,
    expected_category_classification_counts: Optional[Mapping[str, Mapping[str, int]]] = None,
    expected_combined_classification_counts: Optional[Mapping[str, int]] = None,
) -> Path:
    raw_dir = Path(baseline_raw_dir)
    output = Path(output_dir)
    output.mkdir(parents=True, exist_ok=True)

    raw_manifest = _read_json(raw_dir / "artifact_manifest.json")
    category_names = tuple(str(category) for category in categories)
    current_roots = _normalize_current_roots(
        raw_dir=raw_dir,
        categories=category_names,
        current_log_roots=current_log_roots,
    )
    category_reports: Dict[str, Any] = {}
    checks = []
    checks.extend(_baseline_identity_checks(raw_manifest))
    expected_category_counts = {
        str(category): {str(key): int(value) for key, value in counts.items()}
        for category, counts in (
            expected_category_classification_counts or EXPECTED_CATEGORY_CLASSIFICATION_COUNTS
        ).items()
    }
    expected_combined_counts = _expected_combined_counts_for_categories(
        category_names,
        expected_category_counts,
        expected_combined_classification_counts,
    )

    combined_counts: Counter[str] = Counter()
    combined_blocking_counts: Counter[str] = Counter()
    for category in category_names:
        report = _build_category_report(current_roots[category])
        category_reports[category] = report
        combined_counts.update(report["classification_counts"])
        combined_blocking_counts.update(report["blocking_classification_counts"])
        checks.extend(_category_checks(category, report, expected_category_counts.get(category, {})))

    checks.append(
        _ok("correspondence_blocking_classifications_absent")
        if not combined_blocking_counts
        else _failed(
            "correspondence_blocking_classifications_absent",
            blocking_classification_counts=dict(sorted(combined_blocking_counts.items())),
        )
    )
    checks.append(
        _ok("combined_classification_counts_expected", counts=dict(sorted(combined_counts.items())))
        if dict(sorted(combined_counts.items())) == dict(sorted(expected_combined_counts.items()))
        else _failed(
            "combined_classification_counts_expected",
            expected=dict(sorted(expected_combined_counts.items())),
            actual=dict(sorted(combined_counts.items())),
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
        "baseline_log_roots": {
            category: str(raw_dir / "logs" / category)
            for category in category_names
        },
        "current_log_roots": {
            category: str(path)
            for category, path in sorted(current_roots.items())
        },
        "diagnostic_model": {
            "required_classification_enum": sorted(ALLOWED_CORRESPONDENCE_CLASSIFICATIONS),
            "blocking_classifications": sorted(BLOCKING_CORRESPONDENCE_CLASSIFICATIONS),
            "non_blocking_classifications": sorted(
                ALLOWED_CORRESPONDENCE_CLASSIFICATIONS - BLOCKING_CORRESPONDENCE_CLASSIFICATIONS
            ),
            "comparison": "validation_unknown_unit_vs_reason_record_vs_proof_action",
        },
        "expected": {
            "category_classification_counts": expected_category_counts,
            "combined_classification_counts": expected_combined_counts,
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
    failures = _phase0b_unknown_reason_correspondence_failures(manifest)
    if not failures:
        return
    raise ValueError(f"Phase 0B UNKNOWN reason correspondence gate failed: {', '.join(map(str, failures))}")


def _phase0b_unknown_reason_correspondence_failures(manifest: Mapping[str, Any]) -> Sequence[str]:
    failures = []
    if not isinstance(manifest, Mapping):
        return ("manifest_not_mapping",)
    if manifest.get("manifest_version") != MANIFEST_VERSION:
        failures.append("manifest_version_mismatch")
    if manifest.get("manifest_kind") != "phase0b_unknown_reason_correspondence_gate":
        failures.append("manifest_kind_mismatch")
    if manifest.get("artifact_role") != "derived_observed_baseline_unknown_reason_correspondence_diagnostics":
        failures.append("artifact_role_mismatch")
    if manifest.get("baseline_id") != EXPECTED_BASELINE_ID:
        failures.append("baseline_id_expected")
    if manifest.get("baseline_git_head") != EXPECTED_GIT_HEAD:
        failures.append("baseline_git_head_expected")
    summary = manifest.get("summary")
    if not isinstance(summary, Mapping):
        failures.append("summary_missing")
        summary = {}
    checks = manifest.get("checks")
    if not _is_non_string_sequence(checks):
        failures.append("checks_missing")
        checks = ()
    expected_summary = _summary(tuple(check for check in checks if isinstance(check, Mapping)))
    for key in ("total", "passed", "failed", "failed_kinds"):
        if summary.get(key) != expected_summary.get(key):
            failures.append(f"summary_{key}_mismatch")
    categories = manifest.get("categories")
    expected = manifest.get("expected")
    if not isinstance(categories, Mapping):
        failures.append("categories_missing")
        categories = {}
    if not isinstance(expected, Mapping):
        failures.append("expected_missing")
        expected = {}
    combined_counts = Counter()
    blocking_counts = Counter()
    for category, report in categories.items():
        if not isinstance(report, Mapping):
            failures.append("category_report_not_mapping")
            continue
        combined_counts.update(
            {str(key): int(value) for key, value in (report.get("classification_counts") or {}).items()}
        )
        blocking_counts.update(
            {str(key): int(value) for key, value in (report.get("blocking_classification_counts") or {}).items()}
        )
        unexpected = set(str(item) for item in (report.get("unexpected_classifications") or ()))
        if unexpected:
            failures.append("correspondence_classifications_known")
        if not set(report.get("classification_counts") or {}).issubset(ALLOWED_CORRESPONDENCE_CLASSIFICATIONS):
            failures.append("correspondence_classifications_known")
    expected_combined = {
        str(key): int(value)
        for key, value in ((expected.get("combined_classification_counts") if isinstance(expected, Mapping) else {}) or {}).items()
    }
    actual_combined = {str(key): int(value) for key, value in combined_counts.items()}
    if dict(sorted(actual_combined.items())) != dict(sorted(expected_combined.items())):
        failures.append("combined_classification_counts_expected")
    actual_manifest_combined = {
        str(key): int(value)
        for key, value in (manifest.get("combined_classification_counts") or {}).items()
    }
    if dict(sorted(actual_manifest_combined.items())) != dict(sorted(actual_combined.items())):
        failures.append("combined_classification_counts_consistency")
    actual_manifest_blocking = {
        str(key): int(value)
        for key, value in (manifest.get("combined_blocking_classification_counts") or {}).items()
    }
    if dict(sorted(actual_manifest_blocking.items())) != dict(sorted(blocking_counts.items())):
        failures.append("combined_blocking_classification_counts_consistency")
    if blocking_counts:
        failures.append("correspondence_blocking_classifications_absent")
    if manifest.get("phase0b_unknown_reason_correspondence_ready") is not (expected_summary.get("failed") == 0):
        failures.append("phase0b_ready_consistency")
    materialized = _materialize_phase0b_gate_from_manifest(manifest)
    if materialized is None:
        failures.append("materialized_context_missing")
    else:
        for key in (
            "baseline_id",
            "baseline_git_head",
            "baseline_log_roots",
            "current_log_roots",
            "diagnostic_model",
            "expected",
            "categories",
            "combined_classification_counts",
            "combined_blocking_classification_counts",
        ):
            if not _strict_json_equal(manifest.get(key), materialized.get(key)):
                failures.append(f"materialized_{key}")
        if not _strict_json_equal(list(checks), materialized.get("checks")):
            failures.append("materialized_checks")
        if tuple(expected_summary.get("failed_kinds") or ()) != tuple(
            _summary(materialized["checks"]).get("failed_kinds") or ()
        ):
            failures.append("materialized_failed_kinds")
    return tuple(sorted(set(failures + list(expected_summary.get("failed_kinds") or ()))))


def main(argv: Optional[Sequence[str]] = None) -> int:
    parser = argparse.ArgumentParser(description="Build a Phase 0B UNKNOWN reason correspondence gate.")
    parser.add_argument("--baseline-raw-dir", required=True)
    parser.add_argument("--output-dir", required=True)
    parser.add_argument("--category", action="append", default=None)
    parser.add_argument(
        "--current-log-root",
        action="append",
        default=None,
        metavar="CATEGORY=PATH",
        help="current validation log root for a category; may be repeated",
    )
    parser.add_argument("--require-ready", action="store_true")
    args = parser.parse_args(argv)

    path = build_phase0b_unknown_reason_correspondence_gate(
        baseline_raw_dir=Path(args.baseline_raw_dir),
        output_dir=Path(args.output_dir),
        current_log_roots=_parse_current_log_roots(args.current_log_root or ()),
        categories=tuple(args.category or EXPECTED_CATEGORIES),
    )
    print(path)
    if args.require_ready:
        validate_phase0b_unknown_reason_correspondence_gate(_read_json(path))
    return 0


def _materialize_phase0b_gate_from_manifest(manifest: Mapping[str, Any]) -> Optional[Dict[str, Any]]:
    baseline_ref = manifest.get("baseline_raw_artifact_ref")
    current_log_roots = manifest.get("current_log_roots")
    expected = manifest.get("expected")
    baseline_log_roots = manifest.get("baseline_log_roots")
    if (
        not isinstance(baseline_ref, Mapping)
        or not isinstance(current_log_roots, Mapping)
        or not isinstance(expected, Mapping)
    ):
        return None
    raw_manifest_path = baseline_ref.get("path")
    if not isinstance(raw_manifest_path, str) or not raw_manifest_path:
        return None
    raw_manifest_file = Path(raw_manifest_path)
    if raw_manifest_file.name != "artifact_manifest.json" or not raw_manifest_file.is_file():
        return None
    raw_dir = raw_manifest_file.parent
    raw_manifest = _read_json(raw_manifest_file)
    if isinstance(baseline_log_roots, Mapping) and baseline_log_roots:
        categories = tuple(str(category) for category in baseline_log_roots)
    else:
        categories = tuple(str(category) for category in current_log_roots)
    if not categories:
        return None
    current_roots = {
        str(category): Path(str(path))
        for category, path in current_log_roots.items()
    }
    expected_category_counts = {
        str(category): {str(key): int(value) for key, value in (counts or {}).items()}
        for category, counts in (expected.get("category_classification_counts") or {}).items()
    }
    expected_combined_counts = {
        str(key): int(value)
        for key, value in (expected.get("combined_classification_counts") or {}).items()
    }

    checks = list(_baseline_identity_checks(raw_manifest))
    category_reports: Dict[str, Any] = {}
    combined_counts: Counter[str] = Counter()
    combined_blocking_counts: Counter[str] = Counter()
    for category in categories:
        if category not in current_roots:
            return None
        report = _build_category_report(current_roots[category])
        category_reports[category] = report
        combined_counts.update(report["classification_counts"])
        combined_blocking_counts.update(report["blocking_classification_counts"])
        checks.extend(_category_checks(category, report, expected_category_counts.get(category, {})))

    checks.append(
        _ok("correspondence_blocking_classifications_absent")
        if not combined_blocking_counts
        else _failed(
            "correspondence_blocking_classifications_absent",
            blocking_classification_counts=dict(sorted(combined_blocking_counts.items())),
        )
    )
    checks.append(
        _ok("combined_classification_counts_expected", counts=dict(sorted(combined_counts.items())))
        if dict(sorted(combined_counts.items())) == dict(sorted(expected_combined_counts.items()))
        else _failed(
            "combined_classification_counts_expected",
            expected=dict(sorted(expected_combined_counts.items())),
            actual=dict(sorted(combined_counts.items())),
        )
    )
    return {
        "baseline_id": raw_manifest.get("baseline_id"),
        "baseline_git_head": raw_manifest.get("git_head"),
        "baseline_log_roots": {
            category: str(raw_dir / "logs" / category)
            for category in categories
        },
        "current_log_roots": {
            category: str(path)
            for category, path in sorted(current_roots.items())
        },
        "diagnostic_model": {
            "required_classification_enum": sorted(ALLOWED_CORRESPONDENCE_CLASSIFICATIONS),
            "blocking_classifications": sorted(BLOCKING_CORRESPONDENCE_CLASSIFICATIONS),
            "non_blocking_classifications": sorted(
                ALLOWED_CORRESPONDENCE_CLASSIFICATIONS - BLOCKING_CORRESPONDENCE_CLASSIFICATIONS
            ),
            "comparison": "validation_unknown_unit_vs_reason_record_vs_proof_action",
        },
        "expected": {
            "category_classification_counts": expected_category_counts,
            "combined_classification_counts": expected_combined_counts,
        },
        "categories": category_reports,
        "combined_classification_counts": dict(sorted(combined_counts.items())),
        "combined_blocking_classification_counts": dict(sorted(combined_blocking_counts.items())),
        "checks": checks,
    }


def _normalize_current_roots(
    *,
    raw_dir: Path,
    categories: Sequence[str],
    current_log_roots: Optional[Mapping[str, Path]],
) -> Dict[str, Path]:
    current = {str(category): Path(path) for category, path in (current_log_roots or {}).items()}
    expected_categories = set(categories)
    unknown_categories = sorted(set(current) - expected_categories)
    if unknown_categories:
        raise ValueError(
            "unknown --current-log-root category: "
            f"{', '.join(unknown_categories)}; expected one of {', '.join(sorted(expected_categories))}"
        )
    return {
        category: current.get(category, raw_dir / "logs" / category)
        for category in categories
    }


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


def _category_checks(
    category: str,
    report: Mapping[str, Any],
    expected_classification_counts: Mapping[str, int],
) -> Sequence[Dict[str, Any]]:
    unexpected = report.get("unexpected_classifications") or ()
    blocking = report.get("blocking_classification_counts") or {}
    actual_counts = {
        str(key): int(value)
        for key, value in (report.get("classification_counts") or {}).items()
    }
    expected_counts = {
        str(key): int(value)
        for key, value in expected_classification_counts.items()
    }
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
        _ok("category_classification_counts_expected", category=category, counts=actual_counts)
        if actual_counts == expected_counts
        else _failed(
            "category_classification_counts_expected",
            category=category,
            expected=expected_counts,
            actual=actual_counts,
        ),
    ]


def _parse_current_log_roots(values: Iterable[str]) -> Dict[str, Path]:
    parsed: Dict[str, Path] = {}
    for value in values:
        if "=" not in value:
            raise ValueError(f"--current-log-root must be CATEGORY=PATH, got {value!r}")
        category, raw_path = value.split("=", 1)
        category = category.strip()
        if not category:
            raise ValueError(f"--current-log-root category is empty in {value!r}")
        parsed[category] = Path(raw_path)
    return parsed


def _expected_combined_counts_for_categories(
    categories: Sequence[str],
    expected_category_counts: Mapping[str, Mapping[str, int]],
    explicit_expected_combined_counts: Optional[Mapping[str, int]],
) -> Dict[str, int]:
    if explicit_expected_combined_counts is not None:
        return {
            str(key): int(value)
            for key, value in explicit_expected_combined_counts.items()
        }
    combined: Counter[str] = Counter()
    for category in categories:
        combined.update(
            {
                str(key): int(value)
                for key, value in (expected_category_counts.get(str(category)) or {}).items()
            }
        )
    return dict(sorted(combined.items()))


def _summary(checks: Sequence[Mapping[str, Any]]) -> Dict[str, Any]:
    failed_kinds = sorted({str(check.get("kind")) for check in checks if check.get("status") == "failed"})
    return {
        "total": len(checks),
        "passed": sum(1 for check in checks if check.get("status") == "ok"),
        "failed": sum(1 for check in checks if check.get("status") == "failed"),
        "failed_kinds": failed_kinds,
    }


def _strict_json_equal(left: Any, right: Any) -> bool:
    return json.dumps(left, sort_keys=True, separators=(",", ":"), default=str) == json.dumps(
        right,
        sort_keys=True,
        separators=(",", ":"),
        default=str,
    )


def _is_non_string_sequence(value: Any) -> bool:
    return isinstance(value, Sequence) and not isinstance(value, (str, bytes, bytearray))


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
