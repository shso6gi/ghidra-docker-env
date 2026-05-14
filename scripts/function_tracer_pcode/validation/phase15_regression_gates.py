# -*- coding: utf-8 -*-
"""Build Phase 1.5 pre-semantic-fix regression gates.

Phase 1.5 is intentionally a gating artifact, not a semantic fix.  It freezes
the concrete Phase 1 manifests against a canonical validation artifact so later
semantic changes can be judged against explicit movement rules.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Dict, Iterable, Mapping, Optional, Sequence, Tuple

from ..equivalence.unknown_reason import coerce_unknown_reason_records
from .phase1_concrete_manifests import (
    validate_negative_manifest,
    validate_phase1_readiness,
    validate_positive_manifest,
    validate_representative_manifest,
    validate_synthetic_manifest,
)
from .result_summary import (
    STATUS_EQ,
    STATUS_UNKNOWN,
    ValidationBaselineComparison,
    ValidationLogRecord,
    aggregate_validation_logs,
    compare_validation_baseline_records,
)


MANIFEST_VERSION = 1
MISSING_SENTINEL = "<missing>"


def build_phase15_regression_gates(
    *,
    baseline_raw_dir: Path,
    phase1_dir: Path,
    output_dir: Path,
    current_log_roots: Optional[Mapping[str, Path]] = None,
    stage: str = "pre_semantic_fix",
) -> Path:
    """Write a Phase 1.5 gate manifest and return its path."""

    raw_dir = Path(baseline_raw_dir).resolve()
    phase1 = Path(phase1_dir).resolve()
    output = Path(output_dir)
    output.mkdir(parents=True, exist_ok=True)

    baseline_manifest = _read_json(raw_dir / "artifact_manifest.json")
    phase1_bundle = _load_phase1_bundle(phase1)
    current_roots = _normalize_current_roots(
        raw_dir=raw_dir,
        current_log_roots=current_log_roots,
    )

    checks = []
    baseline_comparisons = {}
    current_records_by_category = {}

    checks.extend(_phase1_manifest_checks(phase1_bundle))

    for category, current_root in sorted(current_roots.items()):
        before_root = raw_dir / "logs" / category
        before_records = aggregate_validation_logs(_log_paths(before_root)).records
        current_records = aggregate_validation_logs(_log_paths(current_root)).records
        current_records_by_category[category] = current_records
        comparison = compare_validation_baseline_records(before_records, current_records)
        baseline_comparisons[category] = _comparison_to_dict(comparison)
        checks.extend(_baseline_comparison_checks(category, comparison))

    current_records_by_key = _records_by_key(current_records_by_category)
    checks.extend(_object_evidence_checks(phase1_bundle["positive"]))
    checks.extend(_positive_pair_checks(phase1_bundle["positive"], current_records_by_key))
    checks.extend(_negative_guard_checks(phase1_bundle["negative"], current_records_by_key))
    checks.extend(
        _representative_record_tuple_checks(
            phase1_bundle["representative"],
            current_records_by_key,
        )
    )

    summary = _gate_summary(checks)
    manifest = {
        "manifest_version": MANIFEST_VERSION,
        "manifest_kind": "phase1_5_pre_semantic_fix_regression_gates",
        "stage": stage,
        "baseline_id": baseline_manifest.get("baseline_id"),
        "baseline_git_head": baseline_manifest.get("git_head"),
        "created_at": datetime.now(timezone.utc).isoformat(),
        "phase1_manifest_refs": _phase1_manifest_refs(phase1, phase1_bundle["index"]),
        "current_log_roots": {
            category: str(path)
            for category, path in sorted(current_roots.items())
        },
        "gate_summary": summary,
        "phase1_5_ready": summary["failed"] == 0,
        "checks": checks,
        "baseline_comparisons": baseline_comparisons,
    }
    path = output / "phase1_5_regression_gates.json"
    _write_json(path, manifest)
    return path


def validate_phase15_regression_gates(manifest: Mapping[str, Any]) -> None:
    if manifest.get("phase1_5_ready") is True:
        return
    summary = manifest.get("gate_summary")
    if not isinstance(summary, Mapping):
        raise ValueError("Phase 1.5 readiness is false and gate summary is missing")
    failed = summary.get("failed_kinds") or ()
    if not failed:
        raise ValueError("Phase 1.5 readiness is false without failed gate kinds")
    raise ValueError(f"Phase 1.5 regression gates failed: {', '.join(map(str, failed))}")


def main(argv: Optional[Sequence[str]] = None) -> int:
    parser = argparse.ArgumentParser(description="Build Phase 1.5 regression gate manifest.")
    parser.add_argument("--baseline-raw-dir", required=True)
    parser.add_argument("--phase1-dir", required=True)
    parser.add_argument("--output-dir", required=True)
    parser.add_argument(
        "--current-log-root",
        action="append",
        default=None,
        metavar="CATEGORY=PATH",
        help="current validation log root for a category; may be repeated",
    )
    parser.add_argument(
        "--require-ready",
        action="store_true",
        help="exit non-zero if any Phase 1.5 gate fails",
    )
    args = parser.parse_args(argv)

    path = build_phase15_regression_gates(
        baseline_raw_dir=Path(args.baseline_raw_dir),
        phase1_dir=Path(args.phase1_dir),
        output_dir=Path(args.output_dir),
        current_log_roots=_parse_current_log_roots(args.current_log_root or ()),
    )
    print(path)
    if args.require_ready:
        validate_phase15_regression_gates(_read_json(path))
    return 0


def _phase1_manifest_checks(bundle: Mapping[str, Mapping[str, Any]]) -> Sequence[Dict[str, Any]]:
    checks = []
    try:
        validate_phase1_readiness(bundle["index"])
    except ValueError as exc:
        checks.append(_failed("phase1_readiness_required", error=str(exc)))
    else:
        checks.append(_ok("phase1_readiness_required"))

    validators = (
        ("positive_manifest_schema", validate_positive_manifest, bundle["positive"]),
        ("negative_manifest_schema", validate_negative_manifest, bundle["negative"]),
        ("representative_manifest_schema", validate_representative_manifest, bundle["representative"]),
        ("synthetic_manifest_schema", validate_synthetic_manifest, bundle["synthetic"]),
    )
    for kind, validator, manifest in validators:
        try:
            if kind == "positive_manifest_schema":
                validator(manifest, require_object_evidence=True)
            else:
                validator(manifest)
        except ValueError as exc:
            checks.append(_failed(kind, error=str(exc)))
        else:
            checks.append(_ok(kind))
    return checks


def _baseline_comparison_checks(
    category: str,
    comparison: ValidationBaselineComparison,
) -> Sequence[Dict[str, Any]]:
    details = _comparison_to_dict(comparison)
    checks = [
        _ok("baseline_exact_match", category=category)
        if not comparison.has_differences()
        else _failed("baseline_exact_match_regression", category=category, comparison=details)
    ]
    conservative_decision_changed = any(
        (
            bool(comparison.final_result_counts_delta),
            comparison.unknown_final_results_delta != 0,
            comparison.timeout_final_results_delta != 0,
            bool(comparison.pair_result_multiset_delta),
        )
    )
    checks.append(
        _failed("conservative_decision_regression", category=category, comparison=details)
        if conservative_decision_changed
        else _ok("conservative_decision_regression", category=category)
    )
    checks.append(
        _failed(
            "proof_action_multiset_regression",
            category=category,
            proof_action_multiset_delta=_tuple_count_items(comparison.proof_action_multiset_delta),
        )
        if comparison.proof_action_multiset_delta
        else _ok("proof_action_multiset_regression", category=category)
    )
    return checks


def _object_evidence_checks(positive_manifest: Mapping[str, Any]) -> Sequence[Dict[str, Any]]:
    checks = []
    for entry in _entries(positive_manifest):
        entry_id = str(entry.get("id") or MISSING_SENTINEL)
        ref = entry.get("object_evidence_ref")
        summary = entry.get("object_evidence_summary")
        if (
            entry.get("object_evidence_status") == "verified"
            and isinstance(ref, Mapping)
            and bool(ref.get("sha256"))
            and isinstance(summary, Mapping)
            and isinstance(summary.get("object_facts"), Mapping)
        ):
            checks.append(_ok("object_derived_evidence_emission_regression", entry_id=entry_id))
        else:
            checks.append(
                _failed(
                    "object_derived_evidence_emission_regression",
                    entry_id=entry_id,
                    object_evidence_status=entry.get("object_evidence_status"),
                )
            )
    return checks


def _positive_pair_checks(
    positive_manifest: Mapping[str, Any],
    current_records_by_key: Mapping[Tuple[str, str, str], ValidationLogRecord],
) -> Sequence[Dict[str, Any]]:
    checks = []
    for entry in _entries(positive_manifest):
        entry_id = str(entry.get("id") or MISSING_SENTINEL)
        record = current_records_by_key.get(_entry_key(entry))
        if record is None:
            checks.append(_failed("positive_concrete_pair_regression", entry_id=entry_id, error="missing current log"))
            continue
        if record.status != STATUS_EQ:
            checks.append(
                _failed(
                    "positive_concrete_pair_regression",
                    entry_id=entry_id,
                    current_result=record.status,
                    expected_result=STATUS_EQ,
                )
            )
            continue
        checks.append(_ok("positive_concrete_pair_regression", entry_id=entry_id))
    return checks


def _negative_guard_checks(
    negative_manifest: Mapping[str, Any],
    current_records_by_key: Mapping[Tuple[str, str, str], ValidationLogRecord],
) -> Sequence[Dict[str, Any]]:
    checks = []
    for entry in _entries(negative_manifest):
        entry_id = str(entry.get("id") or MISSING_SENTINEL)
        if entry.get("category") == "synthetic_negative":
            if entry.get("current_result") == "NOT_EQ" and entry.get("must_not_be_equivalent") is True:
                checks.append(_ok("false_eq_guard_regression", entry_id=entry_id, synthetic=True))
            else:
                checks.append(_failed("false_eq_guard_regression", entry_id=entry_id, synthetic=True))
            continue
        record = current_records_by_key.get(_entry_key(entry))
        if record is None:
            checks.append(_failed("false_eq_guard_regression", entry_id=entry_id, error="missing current log"))
            continue
        reason_ids = set(_record_reason_ids(record))
        required_reason_ids = set(str(reason) for reason in (entry.get("required_reason_ids") or ()))
        if record.status == STATUS_EQ:
            checks.append(
                _failed(
                    "false_eq_guard_regression",
                    entry_id=entry_id,
                    current_result=record.status,
                    required_reason_ids=sorted(required_reason_ids),
                )
            )
            continue
        if entry.get("expected_result") == STATUS_UNKNOWN and not required_reason_ids.issubset(reason_ids):
            checks.append(
                _failed(
                    "false_eq_guard_regression",
                    entry_id=entry_id,
                    current_result=record.status,
                    missing_required_reason_ids=sorted(required_reason_ids - reason_ids),
                )
            )
            continue
        checks.append(_ok("false_eq_guard_regression", entry_id=entry_id))
    return checks


def _representative_record_tuple_checks(
    representative_manifest: Mapping[str, Any],
    current_records_by_key: Mapping[Tuple[str, str, str], ValidationLogRecord],
) -> Sequence[Dict[str, Any]]:
    checks = []
    for entry in _entries(representative_manifest):
        entry_id = str(entry.get("id") or MISSING_SENTINEL)
        record = current_records_by_key.get(_entry_key(entry))
        if record is None:
            checks.append(
                _failed("representative_record_tuple_regression", entry_id=entry_id, error="missing current log")
            )
            continue
        expected_records = _normalized_entry_reason_records(entry)
        current_records = _record_reason_records(record)
        if record.status != entry.get("current_result") or current_records != expected_records:
            checks.append(
                _failed(
                    "representative_record_tuple_regression",
                    entry_id=entry_id,
                    expected_result=entry.get("current_result"),
                    current_result=record.status,
                    expected_reason_records=expected_records,
                    current_reason_records=current_records,
                )
            )
            continue
        checks.append(_ok("representative_record_tuple_regression", entry_id=entry_id))
    return checks


def _load_phase1_bundle(phase1_dir: Path) -> Dict[str, Mapping[str, Any]]:
    index = _read_json(phase1_dir / "phase1_manifest_index.json")
    paths = index.get("manifests") or {}
    return {
        "index": index,
        "positive": _read_json(phase1_dir / str(paths.get("positive") or "positive_manifest.json")),
        "negative": _read_json(phase1_dir / str(paths.get("negative") or "negative_manifest.json")),
        "representative": _read_json(phase1_dir / str(paths.get("representative") or "representative_manifest.json")),
        "synthetic": _read_json(phase1_dir / str(paths.get("synthetic") or "synthetic_manifest.json")),
    }


def _phase1_manifest_refs(phase1_dir: Path, index: Mapping[str, Any]) -> Dict[str, Dict[str, str]]:
    paths = {"index": "phase1_manifest_index.json"}
    paths.update({str(key): str(value) for key, value in (index.get("manifests") or {}).items()})
    refs = {}
    for name, rel_path in sorted(paths.items()):
        path = phase1_dir / rel_path
        refs[name] = {"path": rel_path, "sha256": _sha256_file(path) if path.is_file() else MISSING_SENTINEL}
    return refs


def _normalize_current_roots(
    *,
    raw_dir: Path,
    current_log_roots: Optional[Mapping[str, Path]],
) -> Dict[str, Path]:
    if current_log_roots:
        return {str(category): Path(path) for category, path in current_log_roots.items()}
    log_root = raw_dir / "logs"
    return {
        path.name: path
        for path in sorted(log_root.iterdir())
        if path.is_dir()
    }


def _parse_current_log_roots(values: Iterable[str]) -> Dict[str, Path]:
    result = {}
    for value in values:
        if "=" not in value:
            raise ValueError(f"--current-log-root must be CATEGORY=PATH, got {value!r}")
        category, raw_path = value.split("=", 1)
        result[category] = Path(raw_path)
    return result


def _records_by_key(
    records_by_category: Mapping[str, Sequence[ValidationLogRecord]],
) -> Dict[Tuple[str, str, str], ValidationLogRecord]:
    result = {}
    for category, records in records_by_category.items():
        for record in records:
            result[(category, record.function_name, _canonical_binary_pair(_record_pair_label(record)))] = record
    return result


def _record_pair_label(record: ValidationLogRecord) -> str:
    if "↔" not in record.pair_label:
        return record.pair_label
    left, right = record.pair_label.split("↔", 1)
    return f"{left.strip()}_{right.strip()}"


def _entry_key(entry: Mapping[str, Any]) -> Tuple[str, str, str]:
    return (
        str(entry.get("category") or MISSING_SENTINEL),
        str(entry.get("function") or MISSING_SENTINEL),
        _canonical_binary_pair(str(entry.get("binary_pair") or MISSING_SENTINEL)),
    )


def _record_reason_ids(record: ValidationLogRecord) -> Tuple[str, ...]:
    return tuple(reason["reason_id"] for reason in _record_reason_records(record))


def _record_reason_records(record: ValidationLogRecord) -> Sequence[Dict[str, str]]:
    payload = record.payloads[-1] if record.payloads else {}
    records = coerce_unknown_reason_records(payload.get("unknown_reasons") or ())
    return tuple(sorted((_reason_record_dict(record) for record in records), key=_reason_record_sort_key))


def _normalized_entry_reason_records(entry: Mapping[str, Any]) -> Sequence[Dict[str, str]]:
    records = []
    for raw_record in entry.get("observed_reason_records") or ():
        if isinstance(raw_record, Mapping):
            records.append(
                {
                    "reason_id": str(raw_record.get("reason_id") or MISSING_SENTINEL),
                    "decision_effect": str(raw_record.get("decision_effect") or MISSING_SENTINEL),
                    "reason_scope": str(raw_record.get("reason_scope") or MISSING_SENTINEL),
                    "recovery_proof_kind": str(raw_record.get("recovery_proof_kind") or MISSING_SENTINEL),
                    "proof_stage": str(raw_record.get("proof_stage") or MISSING_SENTINEL),
                    "action_status": str(raw_record.get("action_status") or MISSING_SENTINEL),
                }
            )
    return tuple(sorted(records, key=_reason_record_sort_key))


def _reason_record_dict(record: Any) -> Dict[str, str]:
    return {
        "reason_id": str(record.reason_id),
        "decision_effect": str(record.decision_effect),
        "reason_scope": str(record.reason_scope),
        "recovery_proof_kind": str(record.recovery_proof_kind),
        "proof_stage": str(record.proof_stage) if record.proof_stage is not None else MISSING_SENTINEL,
        "action_status": str(record.action_status) if record.action_status is not None else MISSING_SENTINEL,
    }


def _reason_record_sort_key(record: Mapping[str, str]) -> Tuple[str, ...]:
    return (
        str(record.get("reason_id")),
        str(record.get("decision_effect")),
        str(record.get("reason_scope")),
        str(record.get("recovery_proof_kind")),
        str(record.get("proof_stage")),
        str(record.get("action_status")),
    )


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
        "pair_result_multiset_delta": _tuple_count_items(comparison.pair_result_multiset_delta),
        "missing_pair_identities": [list(item) for item in comparison.missing_pair_identities],
        "added_pair_identities": [list(item) for item in comparison.added_pair_identities],
    }


def _tuple_count_items(counts: Mapping[Any, int]) -> Sequence[Dict[str, Any]]:
    return [
        {"key": list(key) if isinstance(key, tuple) else key, "delta": int(value)}
        for key, value in sorted(counts.items(), key=lambda item: str(item[0]))
    ]


def _gate_summary(checks: Sequence[Mapping[str, Any]]) -> Dict[str, Any]:
    failed_kinds = sorted(
        {
            str(check.get("kind"))
            for check in checks
            if check.get("status") != "ok"
        }
    )
    return {
        "baseline_comparison_mode": "exact_match",
        "total": len(checks),
        "passed": sum(1 for check in checks if check.get("status") == "ok"),
        "failed": sum(1 for check in checks if check.get("status") != "ok"),
        "failed_kinds": failed_kinds,
        "locked_gates": [
            "conservative_decision_regression",
            "object_derived_evidence_emission_regression",
            "false_eq_guard_regression",
            "proof_action_multiset_regression",
            "positive_concrete_pair_regression",
            "representative_record_tuple_regression",
        ],
    }


def _entries(manifest: Mapping[str, Any]) -> Sequence[Mapping[str, Any]]:
    entries = manifest.get("entries") or ()
    if not isinstance(entries, Sequence):
        raise ValueError("manifest entries must be a sequence")
    return entries


def _log_paths(root: Path) -> Sequence[Path]:
    if not root.is_dir():
        return ()
    return tuple(sorted(root.glob("*/*.log"), key=lambda path: str(path)))


def _canonical_binary_pair(pair: str) -> str:
    if "_" not in pair:
        return pair
    left, right = pair.split("_", 1)
    return "_".join(sorted((left, right), key=_binary_sort_key))


def _binary_sort_key(binary_id: str) -> Tuple[str, int, str]:
    text = str(binary_id)
    if len(text) > 1 and text[0].isalpha() and text[1:].isdigit():
        return text[0], int(text[1:]), text
    return text, -1, text


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
        return json.load(handle)


def _write_json(path: Path, payload: Mapping[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def _sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


if __name__ == "__main__":
    raise SystemExit(main())
