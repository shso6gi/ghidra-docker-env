# -*- coding: utf-8 -*-
"""Build a Phase 0C canonical reproduction gate.

This gate compares a frozen observed baseline against supplied current log
roots using the shared canonical comparison model.  By default the current roots
are the frozen raw logs themselves, which makes this a parser/order invariant
self-check.  Callers can pass regenerated log roots to validate runner
reproduction without running Ghidra inside this gate.
"""

from __future__ import annotations

import argparse
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Dict, Iterable, Mapping, Optional, Sequence

from .result_summary import (
    ValidationBaselineComparison,
    aggregate_validation_logs,
    canonical_validation_surface_hash,
    compare_validation_baseline_records,
)


MANIFEST_VERSION = 1
EXPECTED_BASELINE_ID = "observed-v0@0a53352"
EXPECTED_GIT_HEAD = "0a53352cf3c9528abfb654906ed7b963474bedc5"
DEFAULT_CATEGORIES = ("function_call", "loop")


def build_phase0c_canonical_reproduction_gate(
    *,
    baseline_raw_dir: Path,
    output_dir: Path,
    current_log_roots: Optional[Mapping[str, Path]] = None,
    categories: Sequence[str] = DEFAULT_CATEGORIES,
) -> Path:
    raw_dir = Path(baseline_raw_dir)
    output = Path(output_dir)
    output.mkdir(parents=True, exist_ok=True)

    raw_manifest = _read_json(raw_dir / "artifact_manifest.json")
    category_names = _normalize_categories(categories)
    current_roots = _normalize_current_roots(
        raw_dir=raw_dir,
        categories=category_names,
        current_log_roots=current_log_roots,
    )

    checks = []
    checks.extend(_baseline_identity_checks(raw_manifest))

    category_comparisons: Dict[str, Any] = {}
    combined_before = []
    combined_after = []
    for category in category_names:
        before_root = raw_dir / "logs" / category
        current_root = current_roots[category]
        before_records = aggregate_validation_logs(_log_paths(before_root)).records
        after_records = aggregate_validation_logs(_log_paths(current_root)).records
        combined_before.extend(before_records)
        combined_after.extend(after_records)
        comparison = compare_validation_baseline_records(before_records, after_records)
        surface_hashes = _surface_hashes(before_records, after_records)
        category_comparisons[category] = {
            **_comparison_to_dict(comparison),
            "canonical_surface_hashes": surface_hashes,
            "canonical_surface_hash_match": surface_hashes["baseline"] == surface_hashes["current"],
        }
        checks.extend(_comparison_checks(f"category:{category}", comparison))
        checks.append(_surface_hash_check(f"category:{category}", surface_hashes))

    combined_comparison = compare_validation_baseline_records(combined_before, combined_after)
    checks.extend(_comparison_checks("combined", combined_comparison))
    combined_surface_hashes = _surface_hashes(combined_before, combined_after)
    checks.append(_surface_hash_check("combined", combined_surface_hashes))

    summary = _summary(checks)
    manifest = {
        "manifest_version": MANIFEST_VERSION,
        "manifest_kind": "phase0c_canonical_reproduction_gate",
        "artifact_role": "derived_observed_baseline_canonical_reproduction_gate",
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
        "categories": list(category_names),
        "current_log_roots": {
            category: str(path)
            for category, path in sorted(current_roots.items())
        },
        "comparison_mode": "exact_canonical_match",
        "locked_count_kinds": [
            "final_result",
            "validation_unknown_unit",
            "reason_record",
            "proof_action",
        ],
        "locked_tuple_surfaces": [
            "timeout_class_multiset",
            "pair_final_result",
            "pair_result",
        ],
        "category_comparisons": category_comparisons,
        "combined_comparison": {
            **_comparison_to_dict(combined_comparison),
            "canonical_surface_hashes": combined_surface_hashes,
            "canonical_surface_hash_match": (
                combined_surface_hashes["baseline"] == combined_surface_hashes["current"]
            ),
        },
        "phase0c_canonical_reproduction_ready": summary["failed"] == 0,
        "summary": summary,
        "checks": checks,
    }
    path = output / "phase0c_canonical_reproduction_gate.json"
    _write_json(path, manifest)
    return path


def validate_phase0c_canonical_reproduction_gate(manifest: Mapping[str, Any]) -> None:
    failures = []
    checks = manifest.get("checks")
    if not isinstance(checks, (list, tuple)):
        failures.append("checks_missing")
        checks = ()
    expected_summary = _summary(tuple(check for check in checks if isinstance(check, Mapping)))
    summary = manifest.get("summary")
    if not isinstance(summary, Mapping):
        failures.append("summary_missing")
        summary = {}
    for key in ("total", "passed", "failed"):
        value = summary.get(key)
        if isinstance(value, bool):
            failures.append(f"summary_{key}_count")
        elif value != expected_summary.get(key):
            failures.append(f"summary_{key}_mismatch")
    if tuple(summary.get("failed_kinds") or ()) != tuple(expected_summary.get("failed_kinds") or ()):
        failures.append("summary_failed_kinds_mismatch")
    if manifest.get("phase0c_canonical_reproduction_ready") is not (expected_summary.get("failed") == 0):
        failures.append("phase0c_ready_consistency")

    materialized = _materialize_phase0c_gate_from_manifest(manifest)
    if materialized is None:
        failures.append("materialized_context_missing")
    else:
        for key in ("baseline_id", "baseline_git_head", "baseline_log_roots", "categories", "current_log_roots"):
            if not _strict_json_equal(manifest.get(key), materialized.get(key)):
                failures.append(f"materialized_{key}")
        if not _strict_json_equal(manifest.get("category_comparisons"), materialized.get("category_comparisons")):
            failures.append("materialized_category_comparisons")
        if not _strict_json_equal(manifest.get("combined_comparison"), materialized.get("combined_comparison")):
            failures.append("materialized_combined_comparison")
        if not _strict_json_equal(list(checks), materialized.get("checks")):
            failures.append("materialized_checks")
        if tuple(expected_summary.get("failed_kinds") or ()) != tuple(
            _summary(materialized["checks"]).get("failed_kinds") or ()
        ):
            failures.append("materialized_failed_kinds")

    failed = tuple(expected_summary.get("failed_kinds") or ())
    if failures or failed:
        all_failures = tuple(dict.fromkeys([*failures, *failed]))
        raise ValueError(f"Phase 0C canonical reproduction gate failed: {', '.join(map(str, all_failures))}")


def main(argv: Optional[Sequence[str]] = None) -> int:
    parser = argparse.ArgumentParser(description="Build a Phase 0C canonical reproduction gate.")
    parser.add_argument("--baseline-raw-dir", required=True)
    parser.add_argument("--output-dir", required=True)
    parser.add_argument(
        "--current-log-root",
        action="append",
        default=None,
        metavar="CATEGORY=PATH",
        help="current validation log root for a category; may be repeated",
    )
    parser.add_argument("--require-ready", action="store_true")
    args = parser.parse_args(argv)

    path = build_phase0c_canonical_reproduction_gate(
        baseline_raw_dir=Path(args.baseline_raw_dir),
        output_dir=Path(args.output_dir),
        current_log_roots=_parse_current_log_roots(args.current_log_root or ()),
    )
    print(path)
    if args.require_ready:
        validate_phase0c_canonical_reproduction_gate(_read_json(path))
    return 0


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


def _normalize_categories(categories: Sequence[str]) -> Sequence[str]:
    normalized = tuple(str(category).strip() for category in categories)
    if not normalized:
        raise ValueError("Phase 0C canonical reproduction requires the full category set")
    if any(not category for category in normalized):
        raise ValueError("category must not be empty")
    duplicates = sorted({category for category in normalized if normalized.count(category) > 1})
    if duplicates:
        raise ValueError(f"duplicate category value: {', '.join(duplicates)}")
    expected = set(DEFAULT_CATEGORIES)
    unknown_categories = sorted(set(normalized) - expected)
    if unknown_categories:
        raise ValueError(
            "unknown category value: "
            f"{', '.join(unknown_categories)}; expected one of {', '.join(sorted(expected))}"
        )
    if set(normalized) != expected:
        raise ValueError(
            "Phase 0C canonical reproduction requires the full category set: "
            f"{', '.join(DEFAULT_CATEGORIES)}"
        )
    return normalized


def _materialize_phase0c_gate_from_manifest(manifest: Mapping[str, Any]) -> Optional[Dict[str, Any]]:
    baseline_ref = manifest.get("baseline_raw_artifact_ref")
    current_log_roots = manifest.get("current_log_roots")
    baseline_log_roots = manifest.get("baseline_log_roots")
    if (
        not isinstance(baseline_ref, Mapping)
        or not isinstance(current_log_roots, Mapping)
        or not isinstance(baseline_log_roots, Mapping)
        or not baseline_log_roots
    ):
        return None
    raw_manifest_path = baseline_ref.get("path")
    if not isinstance(raw_manifest_path, str) or not raw_manifest_path:
        return None
    raw_manifest_file = Path(raw_manifest_path)
    if raw_manifest_file.name != "artifact_manifest.json":
        return None
    raw_dir = raw_manifest_file.parent
    if not raw_manifest_file.is_file():
        return None
    try:
        categories = _normalize_categories(tuple(str(category) for category in baseline_log_roots))
    except ValueError:
        return None
    raw_manifest = _read_json(raw_manifest_file)
    current_roots = {
        str(category): Path(str(path))
        for category, path in current_log_roots.items()
    }
    if set(current_roots) != set(categories):
        return None

    checks = list(_baseline_identity_checks(raw_manifest))
    category_comparisons: Dict[str, Any] = {}
    combined_before = []
    combined_after = []
    for category in categories:
        before_root = raw_dir / "logs" / category
        current_root = current_roots[category]
        before_records = aggregate_validation_logs(_log_paths(before_root)).records
        after_records = aggregate_validation_logs(_log_paths(current_root)).records
        combined_before.extend(before_records)
        combined_after.extend(after_records)
        comparison = compare_validation_baseline_records(before_records, after_records)
        surface_hashes = _surface_hashes(before_records, after_records)
        category_comparisons[category] = {
            **_comparison_to_dict(comparison),
            "canonical_surface_hashes": surface_hashes,
            "canonical_surface_hash_match": surface_hashes["baseline"] == surface_hashes["current"],
        }
        checks.extend(_comparison_checks(f"category:{category}", comparison))
        checks.append(_surface_hash_check(f"category:{category}", surface_hashes))

    combined_comparison = compare_validation_baseline_records(combined_before, combined_after)
    checks.extend(_comparison_checks("combined", combined_comparison))
    combined_surface_hashes = _surface_hashes(combined_before, combined_after)
    checks.append(_surface_hash_check("combined", combined_surface_hashes))
    return {
        "baseline_id": raw_manifest.get("baseline_id"),
        "baseline_git_head": raw_manifest.get("git_head"),
        "baseline_log_roots": {
            category: str(raw_dir / "logs" / category)
            for category in categories
        },
        "categories": list(categories),
        "current_log_roots": {
            category: str(path)
            for category, path in sorted(current_roots.items())
        },
        "category_comparisons": category_comparisons,
        "combined_comparison": {
            **_comparison_to_dict(combined_comparison),
            "canonical_surface_hashes": combined_surface_hashes,
            "canonical_surface_hash_match": (
                combined_surface_hashes["baseline"] == combined_surface_hashes["current"]
            ),
        },
        "checks": checks,
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


def _comparison_checks(scope: str, comparison: ValidationBaselineComparison) -> Sequence[Dict[str, Any]]:
    details = _comparison_to_dict(comparison)
    return [
        _ok("canonical_reproduction_total_results", scope=scope)
        if comparison.before_total_results == comparison.after_total_results
        else _failed("canonical_reproduction_total_results", scope=scope, comparison=details),
        _ok("canonical_reproduction_final_result_counts", scope=scope)
        if not comparison.final_result_counts_delta
        else _failed("canonical_reproduction_final_result_counts", scope=scope, comparison=details),
        _ok("canonical_reproduction_unknown_final_results", scope=scope)
        if comparison.unknown_final_results_delta == 0
        else _failed("canonical_reproduction_unknown_final_results", scope=scope, comparison=details),
        _ok("canonical_reproduction_timeout_final_results", scope=scope)
        if comparison.timeout_final_results_delta == 0
        else _failed("canonical_reproduction_timeout_final_results", scope=scope, comparison=details),
        _ok("canonical_reproduction_timeout_class_multiset", scope=scope)
        if not comparison.timeout_class_multiset_delta
        else _failed("canonical_reproduction_timeout_class_multiset", scope=scope, comparison=details),
        _ok("canonical_reproduction_validation_unknown_unit_multiset", scope=scope)
        if not comparison.validation_unknown_unit_multiset_delta
        else _failed("canonical_reproduction_validation_unknown_unit_multiset", scope=scope, comparison=details),
        _ok("canonical_reproduction_reason_record_multiset", scope=scope)
        if not comparison.reason_record_multiset_delta
        else _failed("canonical_reproduction_reason_record_multiset", scope=scope, comparison=details),
        _ok("canonical_reproduction_proof_action_multiset", scope=scope)
        if not comparison.proof_action_multiset_delta
        else _failed("canonical_reproduction_proof_action_multiset", scope=scope, comparison=details),
        _ok("canonical_reproduction_pair_final_result_multiset", scope=scope)
        if not comparison.pair_final_result_multiset_delta
        else _failed("canonical_reproduction_pair_final_result_multiset", scope=scope, comparison=details),
        _ok("canonical_reproduction_pair_result_multiset", scope=scope)
        if not comparison.pair_result_multiset_delta
        else _failed("canonical_reproduction_pair_result_multiset", scope=scope, comparison=details),
        _ok("canonical_reproduction_pair_identities", scope=scope)
        if not comparison.missing_pair_identities and not comparison.added_pair_identities
        else _failed("canonical_reproduction_pair_identities", scope=scope, comparison=details),
    ]


def _comparison_to_dict(comparison: ValidationBaselineComparison) -> Dict[str, Any]:
    return {
        "before_total_results": comparison.before_total_results,
        "after_total_results": comparison.after_total_results,
        "final_result_counts_delta": dict(comparison.final_result_counts_delta),
        "unknown_final_results_delta": comparison.unknown_final_results_delta,
        "timeout_final_results_delta": comparison.timeout_final_results_delta,
        "timeout_class_multiset_delta": dict(comparison.timeout_class_multiset_delta),
        "validation_unknown_unit_multiset_delta": _tuple_count_items(
            comparison.validation_unknown_unit_multiset_delta
        ),
        "reason_record_multiset_delta": _tuple_count_items(comparison.reason_record_multiset_delta),
        "proof_action_multiset_delta": _tuple_count_items(comparison.proof_action_multiset_delta),
        "pair_final_result_multiset_delta": _tuple_count_items(comparison.pair_final_result_multiset_delta),
        "pair_result_multiset_delta": _tuple_count_items(comparison.pair_result_multiset_delta),
        "missing_pair_identities": [list(item) for item in comparison.missing_pair_identities],
        "added_pair_identities": [list(item) for item in comparison.added_pair_identities],
    }


def _surface_hashes(before_records: Sequence[Any], after_records: Sequence[Any]) -> Dict[str, str]:
    return {
        "baseline": canonical_validation_surface_hash(before_records),
        "current": canonical_validation_surface_hash(after_records),
    }


def _surface_hash_check(scope: str, surface_hashes: Mapping[str, str]) -> Dict[str, Any]:
    return (
        _ok("canonical_reproduction_surface_hash", scope=scope, surface_hash=surface_hashes["current"])
        if surface_hashes["baseline"] == surface_hashes["current"]
        else _failed(
            "canonical_reproduction_surface_hash",
            scope=scope,
            baseline_hash=surface_hashes["baseline"],
            current_hash=surface_hashes["current"],
        )
    )


def _tuple_count_items(counts: Mapping[Any, int]) -> Sequence[Dict[str, Any]]:
    return [
        {"key": list(key) if isinstance(key, tuple) else key, "delta": int(value)}
        for key, value in sorted(counts.items(), key=lambda item: str(item[0]))
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


def _log_paths(root: Path) -> Sequence[Path]:
    if not root.is_dir():
        return ()
    return tuple(sorted(root.glob("*/*.log"), key=lambda path: str(path)))


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
