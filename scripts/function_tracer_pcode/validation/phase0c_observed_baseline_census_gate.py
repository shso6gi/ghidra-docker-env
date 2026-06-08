# -*- coding: utf-8 -*-
"""Build a Phase 0C observed-baseline census gate.

This gate validates the frozen raw observed baseline without running Ghidra.
It fixes the count model used by later semantic phases:

* final_result: pair final status counts
* validation_unknown_unit: primary UNKNOWN census unit
* reason_record: typed reason detail records
* proof_action: proof backlog/recovery action records
"""

from __future__ import annotations

import argparse
import json
from collections import Counter
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Dict, Mapping, Optional, Sequence, Tuple

from ..equivalence.unknown_reason import UNKNOWN_TUPLE_MISSING, UnknownCountKind
from .result_summary import STATUS_ORDER, aggregate_validation_logs
from .unknown_reason_summary import diagnose_unknown_reason_correspondence, summarize_validation_unknowns


MANIFEST_VERSION = 1
EXPECTED_BASELINE_ID = "observed-v0@0a53352"
EXPECTED_GIT_HEAD = "0a53352cf3c9528abfb654906ed7b963474bedc5"
PRIMARY_CENSUS_COUNT_KIND = UnknownCountKind.VALIDATION_UNKNOWN_UNIT.value
GLOBAL_REASON_TUPLE_WIDTH = 7
ALLOWED_CORRESPONDENCE_CLASSIFICATIONS = frozenset(
    {
        "aggregation_difference",
        "detail_missing",
        "parser_bug",
        "proof_action_expansion",
        "raw_log_missing",
    }
)

EXPECTED_FINAL_RESULT_COUNTS: Mapping[str, Mapping[str, int]] = {
    "function_call": {
        "EQ": 1555,
        "NOT_EQ": 71,
        "ERROR": 0,
        "UNKNOWN": 655,
        "TIMEOUT": 119,
        "INCOMPLETE": 0,
    },
    "loop": {
        "EQ": 62,
        "NOT_EQ": 1,
        "ERROR": 0,
        "UNKNOWN": 537,
        "TIMEOUT": 0,
        "INCOMPLETE": 0,
    },
}
EXPECTED_VALIDATION_UNKNOWN_UNITS = {
    "function_call": 2491,
    "loop": 1297,
}
EXPECTED_CATEGORY_PAIR_LOG_COUNTS = {
    "function_call": 2400,
    "loop": 600,
}
EXPECTED_COMBINED_PAIR_LOG_COUNT = 3000
EXPECTED_COMBINED_FINAL_RESULT_COUNTS = {
    "EQ": 1617,
    "NOT_EQ": 72,
    "ERROR": 0,
    "UNKNOWN": 1192,
    "TIMEOUT": 119,
    "INCOMPLETE": 0,
}
EXPECTED_COMBINED_VALIDATION_UNKNOWN_UNITS = 3788
EXPECTED_COMBINED_UNKNOWN_BY_REASON = {
    "equivalence_blocking_unsafety": 132,
    "method_b_closure_blocked": 443,
    "readonly_identity_missing": 143,
    "return_coverage_gap": 316,
    "return_coverage_inconclusive": 1,
    "return_width_bridge_missing": 504,
    "sat_unsafety": 194,
    "solver_proven_rewrite_no_change": 282,
    "solver_proven_rewrite_proof_failed": 76,
    "solver_unknown_timeout": 131,
    "unresolved_expression": 1566,
}


def build_phase0c_observed_baseline_census_gate(
    *,
    baseline_raw_dir: Path,
    output_dir: Path,
    expected_final_result_counts: Optional[Mapping[str, Mapping[str, int]]] = None,
    expected_validation_unknown_units: Optional[Mapping[str, int]] = None,
    expected_category_pair_log_counts: Optional[Mapping[str, int]] = None,
    expected_combined_pair_log_count: int = EXPECTED_COMBINED_PAIR_LOG_COUNT,
    expected_combined_final_result_counts: Optional[Mapping[str, int]] = None,
    expected_combined_validation_unknown_units: int = EXPECTED_COMBINED_VALIDATION_UNKNOWN_UNITS,
    expected_combined_unknown_by_reason: Optional[Mapping[str, int]] = None,
) -> Path:
    raw_dir = Path(baseline_raw_dir)
    output = Path(output_dir)
    output.mkdir(parents=True, exist_ok=True)

    raw_manifest = _read_json(raw_dir / "artifact_manifest.json")
    expected_counts = {
        category: dict(counts)
        for category, counts in (expected_final_result_counts or EXPECTED_FINAL_RESULT_COUNTS).items()
    }
    expected_unknown_units = dict(expected_validation_unknown_units or EXPECTED_VALIDATION_UNKNOWN_UNITS)
    expected_pair_log_counts = dict(expected_category_pair_log_counts or EXPECTED_CATEGORY_PAIR_LOG_COUNTS)
    expected_combined_counts = dict(
        expected_combined_final_result_counts or EXPECTED_COMBINED_FINAL_RESULT_COUNTS
    )
    expected_combined_reasons = dict(
        expected_combined_unknown_by_reason or EXPECTED_COMBINED_UNKNOWN_BY_REASON
    )

    category_summaries: Dict[str, Any] = {}
    checks = []
    checks.extend(_baseline_identity_checks(raw_manifest))

    combined_final_counts: Counter[str] = Counter()
    combined_pair_log_count = 0
    combined_unknown_units = 0
    combined_unknown_by_reason: Counter[str] = Counter()

    for category in sorted(expected_counts):
        summary = _summarize_category(raw_dir / "logs" / category)
        category_summaries[category] = summary
        combined_pair_log_count += int(summary["pair_log_count"])
        combined_final_counts.update(summary["final_result_counts"])
        combined_unknown_units += int(summary["validation_unknown_units"])
        combined_unknown_by_reason.update(summary["unknown_by_reason"])

        checks.append(
            _ok("category_pair_log_count_expected", category=category, count=summary["pair_log_count"])
            if int(summary["pair_log_count"]) == int(expected_pair_log_counts.get(category, -1))
            else _failed(
                "category_pair_log_count_expected",
                category=category,
                expected=expected_pair_log_counts.get(category),
                actual=summary["pair_log_count"],
            )
        )
        checks.append(
            _ok("category_pair_identities_unique", category=category, count=summary["pair_identity_count"])
            if not summary["duplicate_pair_identities"]
            else _failed(
                "category_pair_identities_unique",
                category=category,
                duplicate_pair_identities=summary["duplicate_pair_identities"],
            )
        )
        checks.append(
            _ok("category_no_error_or_incomplete_results", category=category)
            if summary["final_result_counts"].get("ERROR", 0) == 0
            and summary["final_result_counts"].get("INCOMPLETE", 0) == 0
            else _failed(
                "category_no_error_or_incomplete_results",
                category=category,
                counts=summary["final_result_counts"],
            )
        )
        checks.append(
            _ok("category_final_result_counts_expected", category=category, counts=summary["final_result_counts"])
            if summary["final_result_counts"] == _normalize_status_counts(expected_counts[category])
            else _failed(
                "category_final_result_counts_expected",
                category=category,
                expected=_normalize_status_counts(expected_counts[category]),
                actual=summary["final_result_counts"],
            )
        )
        checks.append(
            _ok(
                "category_validation_unknown_units_expected",
                category=category,
                count=summary["validation_unknown_units"],
            )
            if int(summary["validation_unknown_units"]) == int(expected_unknown_units.get(category, -1))
            else _failed(
                "category_validation_unknown_units_expected",
                category=category,
                expected=expected_unknown_units.get(category),
                actual=summary["validation_unknown_units"],
            )
        )
        checks.extend(_count_kind_schema_checks(category, summary))
        checks.extend(_correspondence_classification_checks(category, summary))

    combined_final_result_counts = _normalize_status_counts(combined_final_counts)
    combined_unknown_by_reason_dict = dict(sorted(combined_unknown_by_reason.items()))
    checks.extend(
        [
            _ok("combined_final_result_counts_expected", counts=combined_final_result_counts)
            if combined_final_result_counts == _normalize_status_counts(expected_combined_counts)
            else _failed(
                "combined_final_result_counts_expected",
                expected=_normalize_status_counts(expected_combined_counts),
                actual=combined_final_result_counts,
            ),
            _ok("combined_pair_log_count_expected", count=combined_pair_log_count)
            if combined_pair_log_count == expected_combined_pair_log_count
            else _failed(
                "combined_pair_log_count_expected",
                expected=expected_combined_pair_log_count,
                actual=combined_pair_log_count,
            ),
            _ok("combined_validation_unknown_units_expected", count=combined_unknown_units)
            if combined_unknown_units == expected_combined_validation_unknown_units
            else _failed(
                "combined_validation_unknown_units_expected",
                expected=expected_combined_validation_unknown_units,
                actual=combined_unknown_units,
            ),
            _ok("combined_unknown_by_reason_expected", counts=combined_unknown_by_reason_dict)
            if combined_unknown_by_reason_dict == expected_combined_reasons
            else _failed(
                "combined_unknown_by_reason_expected",
                expected=expected_combined_reasons,
                actual=combined_unknown_by_reason_dict,
            ),
            _ok("primary_census_count_kind", count_kind=PRIMARY_CENSUS_COUNT_KIND),
        ]
    )

    summary = _summary(checks)
    manifest = {
        "manifest_version": MANIFEST_VERSION,
        "manifest_kind": "phase0c_observed_baseline_census_gate",
        "artifact_role": "derived_observed_baseline_census_gate",
        "created_at": datetime.now(timezone.utc).isoformat(),
        "baseline_id": raw_manifest.get("baseline_id"),
        "baseline_git_head": raw_manifest.get("git_head"),
        "baseline_raw_artifact_ref": {
            "path": str(raw_dir / "artifact_manifest.json"),
        },
        "count_model": {
            "primary_census_count_kind": PRIMARY_CENSUS_COUNT_KIND,
            "count_kinds": [
                UnknownCountKind.FINAL_RESULT.value,
                UnknownCountKind.VALIDATION_UNKNOWN_UNIT.value,
                UnknownCountKind.REASON_RECORD.value,
                UnknownCountKind.PROOF_ACTION.value,
            ],
            "global_reason_tuple_key": [
                "count_kind",
                "reason_id",
                "decision_effect",
                "reason_scope",
                "recovery_proof_kind",
                "proof_stage",
                "action_status",
            ],
            "optional_field_missing_sentinel": UNKNOWN_TUPLE_MISSING,
        },
        "expected": {
            "category_final_result_counts": expected_counts,
            "category_pair_log_counts": expected_pair_log_counts,
            "category_validation_unknown_units": expected_unknown_units,
            "combined_final_result_counts": _normalize_status_counts(expected_combined_counts),
            "combined_pair_log_count": expected_combined_pair_log_count,
            "combined_validation_unknown_units": expected_combined_validation_unknown_units,
            "combined_unknown_by_reason": expected_combined_reasons,
        },
        "observed": {
            "categories": category_summaries,
            "combined_final_result_counts": combined_final_result_counts,
            "combined_pair_log_count": combined_pair_log_count,
            "combined_validation_unknown_units": combined_unknown_units,
            "combined_unknown_by_reason": combined_unknown_by_reason_dict,
        },
        "phase0c_observed_baseline_census_ready": summary["failed"] == 0,
        "summary": summary,
        "checks": checks,
    }
    path = output / "phase0c_observed_baseline_census_gate.json"
    _write_json(path, manifest)
    return path


def validate_phase0c_observed_baseline_census_gate(manifest: Mapping[str, Any]) -> None:
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
    if manifest.get("phase0c_observed_baseline_census_ready") is not (expected_summary.get("failed") == 0):
        failures.append("phase0c_ready_consistency")

    materialized = _materialize_phase0c_census_from_manifest(manifest)
    if materialized is None:
        failures.append("materialized_context_missing")
    else:
        for key in ("baseline_id", "baseline_git_head", "count_model", "expected", "observed"):
            if not _strict_json_equal(manifest.get(key), materialized.get(key)):
                failures.append(f"materialized_{key}")
        if not _strict_json_equal(list(checks), materialized.get("checks")):
            failures.append("materialized_checks")
        if tuple(expected_summary.get("failed_kinds") or ()) != tuple(
            _summary(materialized["checks"]).get("failed_kinds") or ()
        ):
            failures.append("materialized_failed_kinds")

    failed = tuple(expected_summary.get("failed_kinds") or ())
    if failures or failed:
        all_failures = tuple(dict.fromkeys([*failures, *failed]))
        raise ValueError(f"Phase 0C observed baseline census gate failed: {', '.join(map(str, all_failures))}")


def main(argv: Optional[Sequence[str]] = None) -> int:
    parser = argparse.ArgumentParser(description="Build a Phase 0C observed-baseline census gate.")
    parser.add_argument("--baseline-raw-dir", required=True)
    parser.add_argument("--output-dir", required=True)
    parser.add_argument("--require-ready", action="store_true")
    args = parser.parse_args(argv)

    path = build_phase0c_observed_baseline_census_gate(
        baseline_raw_dir=Path(args.baseline_raw_dir),
        output_dir=Path(args.output_dir),
    )
    print(path)
    if args.require_ready:
        validate_phase0c_observed_baseline_census_gate(_read_json(path))
    return 0


def _materialize_phase0c_census_from_manifest(manifest: Mapping[str, Any]) -> Optional[Dict[str, Any]]:
    baseline_ref = manifest.get("baseline_raw_artifact_ref")
    expected = manifest.get("expected")
    if not isinstance(baseline_ref, Mapping) or not isinstance(expected, Mapping):
        return None
    raw_manifest_path = baseline_ref.get("path")
    if not isinstance(raw_manifest_path, str) or not raw_manifest_path:
        return None
    raw_manifest_file = Path(raw_manifest_path)
    if raw_manifest_file.name != "artifact_manifest.json" or not raw_manifest_file.is_file():
        return None
    raw_dir = raw_manifest_file.parent
    raw_manifest = _read_json(raw_manifest_file)
    expected_counts = {
        str(category): {str(status): int(count) for status, count in (counts or {}).items()}
        for category, counts in (expected.get("category_final_result_counts") or {}).items()
    }
    expected_unknown_units = {
        str(category): int(count)
        for category, count in (expected.get("category_validation_unknown_units") or {}).items()
    }
    expected_pair_log_counts = {
        str(category): int(count)
        for category, count in (expected.get("category_pair_log_counts") or {}).items()
    }
    if not expected_counts or not expected_unknown_units or not expected_pair_log_counts:
        return None
    expected_combined_pair_log_count = expected.get("combined_pair_log_count")
    expected_combined_validation_unknown_units = expected.get("combined_validation_unknown_units")
    if isinstance(expected_combined_pair_log_count, bool) or isinstance(
        expected_combined_validation_unknown_units,
        bool,
    ):
        return None
    try:
        expected_combined_pair_log_count = int(expected_combined_pair_log_count)
        expected_combined_validation_unknown_units = int(expected_combined_validation_unknown_units)
    except (TypeError, ValueError):
        return None
    expected_combined_counts = {
        str(status): int(count)
        for status, count in (expected.get("combined_final_result_counts") or {}).items()
    }
    expected_combined_reasons = {
        str(reason): int(count)
        for reason, count in (expected.get("combined_unknown_by_reason") or {}).items()
    }

    checks = list(_baseline_identity_checks(raw_manifest))
    category_summaries: Dict[str, Any] = {}
    combined_final_counts: Counter[str] = Counter()
    combined_pair_log_count = 0
    combined_unknown_units = 0
    combined_unknown_by_reason: Counter[str] = Counter()

    for category in sorted(expected_counts):
        category_summary = _summarize_category(raw_dir / "logs" / category)
        category_summaries[category] = category_summary
        combined_pair_log_count += int(category_summary["pair_log_count"])
        combined_final_counts.update(category_summary["final_result_counts"])
        combined_unknown_units += int(category_summary["validation_unknown_units"])
        combined_unknown_by_reason.update(category_summary["unknown_by_reason"])

        checks.append(
            _ok("category_pair_log_count_expected", category=category, count=category_summary["pair_log_count"])
            if int(category_summary["pair_log_count"]) == int(expected_pair_log_counts.get(category, -1))
            else _failed(
                "category_pair_log_count_expected",
                category=category,
                expected=expected_pair_log_counts.get(category),
                actual=category_summary["pair_log_count"],
            )
        )
        checks.append(
            _ok("category_pair_identities_unique", category=category, count=category_summary["pair_identity_count"])
            if not category_summary["duplicate_pair_identities"]
            else _failed(
                "category_pair_identities_unique",
                category=category,
                duplicate_pair_identities=category_summary["duplicate_pair_identities"],
            )
        )
        checks.append(
            _ok("category_no_error_or_incomplete_results", category=category)
            if category_summary["final_result_counts"].get("ERROR", 0) == 0
            and category_summary["final_result_counts"].get("INCOMPLETE", 0) == 0
            else _failed(
                "category_no_error_or_incomplete_results",
                category=category,
                counts=category_summary["final_result_counts"],
            )
        )
        checks.append(
            _ok("category_final_result_counts_expected", category=category, counts=category_summary["final_result_counts"])
            if category_summary["final_result_counts"] == _normalize_status_counts(expected_counts[category])
            else _failed(
                "category_final_result_counts_expected",
                category=category,
                expected=_normalize_status_counts(expected_counts[category]),
                actual=category_summary["final_result_counts"],
            )
        )
        checks.append(
            _ok(
                "category_validation_unknown_units_expected",
                category=category,
                count=category_summary["validation_unknown_units"],
            )
            if int(category_summary["validation_unknown_units"]) == int(expected_unknown_units.get(category, -1))
            else _failed(
                "category_validation_unknown_units_expected",
                category=category,
                expected=expected_unknown_units.get(category),
                actual=category_summary["validation_unknown_units"],
            )
        )
        checks.extend(_count_kind_schema_checks(category, category_summary))
        checks.extend(_correspondence_classification_checks(category, category_summary))

    combined_final_result_counts = _normalize_status_counts(combined_final_counts)
    combined_unknown_by_reason_dict = dict(sorted(combined_unknown_by_reason.items()))
    checks.extend(
        [
            _ok("combined_final_result_counts_expected", counts=combined_final_result_counts)
            if combined_final_result_counts == _normalize_status_counts(expected_combined_counts)
            else _failed(
                "combined_final_result_counts_expected",
                expected=_normalize_status_counts(expected_combined_counts),
                actual=combined_final_result_counts,
            ),
            _ok("combined_pair_log_count_expected", count=combined_pair_log_count)
            if combined_pair_log_count == expected_combined_pair_log_count
            else _failed(
                "combined_pair_log_count_expected",
                expected=expected_combined_pair_log_count,
                actual=combined_pair_log_count,
            ),
            _ok("combined_validation_unknown_units_expected", count=combined_unknown_units)
            if combined_unknown_units == expected_combined_validation_unknown_units
            else _failed(
                "combined_validation_unknown_units_expected",
                expected=expected_combined_validation_unknown_units,
                actual=combined_unknown_units,
            ),
            _ok("combined_unknown_by_reason_expected", counts=combined_unknown_by_reason_dict)
            if combined_unknown_by_reason_dict == expected_combined_reasons
            else _failed(
                "combined_unknown_by_reason_expected",
                expected=expected_combined_reasons,
                actual=combined_unknown_by_reason_dict,
            ),
            _ok("primary_census_count_kind", count_kind=PRIMARY_CENSUS_COUNT_KIND),
        ]
    )
    return {
        "baseline_id": raw_manifest.get("baseline_id"),
        "baseline_git_head": raw_manifest.get("git_head"),
        "count_model": {
            "primary_census_count_kind": PRIMARY_CENSUS_COUNT_KIND,
            "count_kinds": [
                UnknownCountKind.FINAL_RESULT.value,
                UnknownCountKind.VALIDATION_UNKNOWN_UNIT.value,
                UnknownCountKind.REASON_RECORD.value,
                UnknownCountKind.PROOF_ACTION.value,
            ],
            "global_reason_tuple_key": [
                "count_kind",
                "reason_id",
                "decision_effect",
                "reason_scope",
                "recovery_proof_kind",
                "proof_stage",
                "action_status",
            ],
            "optional_field_missing_sentinel": UNKNOWN_TUPLE_MISSING,
        },
        "expected": {
            "category_final_result_counts": expected_counts,
            "category_pair_log_counts": expected_pair_log_counts,
            "category_validation_unknown_units": expected_unknown_units,
            "combined_final_result_counts": _normalize_status_counts(expected_combined_counts),
            "combined_pair_log_count": expected_combined_pair_log_count,
            "combined_validation_unknown_units": expected_combined_validation_unknown_units,
            "combined_unknown_by_reason": expected_combined_reasons,
        },
        "observed": {
            "categories": category_summaries,
            "combined_final_result_counts": combined_final_result_counts,
            "combined_pair_log_count": combined_pair_log_count,
            "combined_validation_unknown_units": combined_unknown_units,
            "combined_unknown_by_reason": combined_unknown_by_reason_dict,
        },
        "checks": checks,
    }


def _summarize_category(log_root: Path) -> Dict[str, Any]:
    root = Path(log_root)
    log_paths = sorted(root.glob("*/*.log"))
    aggregate = aggregate_validation_logs(log_paths)
    pair_identity_counts = Counter(_pair_identity(record) for record in aggregate.records)
    duplicate_pair_identities = [
        {"function": key[0], "binary_pair": key[1], "count": count}
        for key, count in sorted(pair_identity_counts.items())
        if count > 1
    ]
    payloads = [payload for record in aggregate.records for payload in record.payloads]
    unknown_summary = summarize_validation_unknowns(payloads)
    overall_unknown_by_reason = _parse_overall_unknown_by_reason(root / "overall_summary.txt")
    correspondence = tuple(diagnostic.to_dict() for diagnostic in diagnose_unknown_reason_correspondence(unknown_summary))
    return {
        "log_root": str(log_root),
        "pair_log_count": len(log_paths),
        "pair_identity_count": len(pair_identity_counts),
        "duplicate_pair_identities": duplicate_pair_identities[:20],
        "final_result_counts": _normalize_status_counts(aggregate.counts),
        "validation_unknown_units": sum(overall_unknown_by_reason.values()),
        "unknown_results": unknown_summary.unknown_results,
        "unknown_by_reason": overall_unknown_by_reason,
        "typed_payload_validation_unknown_units": unknown_summary.unknown_units,
        "typed_payload_unknown_by_reason": dict(sorted(unknown_summary.unknown_by_reason.items())),
        "overall_vs_typed_payload_unknown_by_reason_delta": _diff_counts(
            unknown_summary.unknown_by_reason,
            overall_unknown_by_reason,
        ),
        "count_kind_tuple_counts": {
            UnknownCountKind.VALIDATION_UNKNOWN_UNIT.value: len(unknown_summary.validation_unknown_unit_multiset),
            UnknownCountKind.REASON_RECORD.value: len(unknown_summary.reason_record_multiset),
            UnknownCountKind.PROOF_ACTION.value: len(unknown_summary.proof_action_multiset),
        },
        "count_kind_tuple_schema": {
            UnknownCountKind.VALIDATION_UNKNOWN_UNIT.value: _tuple_schema(
                unknown_summary.validation_unknown_unit_multiset,
                UnknownCountKind.VALIDATION_UNKNOWN_UNIT.value,
            ),
            UnknownCountKind.REASON_RECORD.value: _tuple_schema(
                unknown_summary.reason_record_multiset,
                UnknownCountKind.REASON_RECORD.value,
            ),
            UnknownCountKind.PROOF_ACTION.value: _tuple_schema(
                unknown_summary.proof_action_multiset,
                UnknownCountKind.PROOF_ACTION.value,
            ),
        },
        "reason_record_correspondence": list(correspondence),
        "reason_record_correspondence_classification_counts": dict(
            sorted(Counter(item["classification"] for item in correspondence).items())
        ),
    }


def _pair_identity(record: Any) -> Tuple[str, str]:
    if "↔" in record.pair_label:
        left, right = (part.strip() for part in record.pair_label.split("↔", 1))
        binary_pair = "_".join(sorted((left, right)))
    else:
        binary_pair = record.pair_label
    return (record.function_name, binary_pair)


def _parse_overall_unknown_by_reason(path: Path) -> Dict[str, int]:
    if not path.is_file():
        return {}
    counts: Dict[str, int] = {}
    in_block = False
    for line in path.read_text(encoding="utf-8", errors="replace").splitlines():
        stripped = line.strip()
        if stripped == "UNKNOWN by reason:":
            in_block = True
            continue
        if not in_block:
            continue
        if not stripped:
            break
        if not stripped.startswith("- "):
            break
        label, sep, raw_count = stripped[2:].partition(":")
        if not sep:
            break
        try:
            counts[label.strip()] = int(raw_count.strip())
        except ValueError:
            break
    return dict(sorted(counts.items()))


def _tuple_schema(multiset: Mapping[Tuple[Any, ...], int], expected_count_kind: str) -> Dict[str, Any]:
    invalid = []
    for key in multiset:
        if len(key) != GLOBAL_REASON_TUPLE_WIDTH or str(key[0]) != expected_count_kind:
            invalid.append(list(key))
            continue
        if any(part is None or str(part) == "" for part in key):
            invalid.append(list(key))
    return {
        "expected_count_kind": expected_count_kind,
        "tuple_width": GLOBAL_REASON_TUPLE_WIDTH,
        "tuple_count": len(multiset),
        "invalid_tuple_count": len(invalid),
        "invalid_tuples": invalid[:20],
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


def _count_kind_schema_checks(category: str, summary: Mapping[str, Any]) -> Sequence[Dict[str, Any]]:
    checks = []
    schemas = summary.get("count_kind_tuple_schema") or {}
    for count_kind in (
        UnknownCountKind.VALIDATION_UNKNOWN_UNIT.value,
        UnknownCountKind.REASON_RECORD.value,
        UnknownCountKind.PROOF_ACTION.value,
    ):
        schema = schemas.get(count_kind) if isinstance(schemas, Mapping) else None
        invalid_count = schema.get("invalid_tuple_count") if isinstance(schema, Mapping) else None
        checks.append(
            _ok("count_kind_tuple_schema_valid", category=category, count_kind=count_kind)
            if invalid_count == 0
            else _failed(
                "count_kind_tuple_schema_valid",
                category=category,
                count_kind=count_kind,
                invalid_tuple_count=invalid_count,
                schema=schema,
            )
        )
    return checks


def _correspondence_classification_checks(category: str, summary: Mapping[str, Any]) -> Sequence[Dict[str, Any]]:
    counts = summary.get("reason_record_correspondence_classification_counts") or {}
    actual = set(counts) if isinstance(counts, Mapping) else set()
    unexpected = sorted(actual - ALLOWED_CORRESPONDENCE_CLASSIFICATIONS)
    return [
        _ok("reason_record_correspondence_classified", category=category, counts=dict(counts))
        if not unexpected
        else _failed("reason_record_correspondence_classified", category=category, unexpected=unexpected),
    ]


def _normalize_status_counts(counts: Mapping[str, int]) -> Dict[str, int]:
    return {status: int(counts.get(status, 0) or 0) for status in STATUS_ORDER}


def _diff_counts(before: Mapping[str, int], after: Mapping[str, int]) -> Dict[str, int]:
    keys = set(before) | set(after)
    return {
        key: int(after.get(key, 0) or 0) - int(before.get(key, 0) or 0)
        for key in sorted(keys)
        if int(after.get(key, 0) or 0) - int(before.get(key, 0) or 0) != 0
    }


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
