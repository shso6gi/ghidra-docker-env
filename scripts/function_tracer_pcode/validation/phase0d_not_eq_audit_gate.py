# -*- coding: utf-8 -*-
"""Build a Phase 0D NOT_EQ audit acceptance gate.

This gate intentionally does not bless any observed NOT_EQ as ground truth.
It freezes the current audit posture: observed same-source NOT_EQ results are
enumerated, linked to draft oracle entries, and remain unresolved until replay
and domain evidence upgrades individual entries.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from collections import Counter
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Dict, Mapping, Optional, Sequence

from .not_eq_audit_manifest import (
    CLASSIFICATIONS,
    validate_not_eq_audit_manifest,
    validate_oracle_manifest,
)


MANIFEST_VERSION = 1
EXPECTED_BASELINE_ID = "observed-v0@0a53352"
EXPECTED_GIT_HEAD = "0a53352cf3c9528abfb654906ed7b963474bedc5"
EXPECTED_ENTRY_COUNT = 72
EXPECTED_CLASSIFICATION_COUNTS = {
    "unresolved": 72,
}
EXPECTED_ORACLE_REVIEW_STATUS_COUNTS = {
    "draft": 3,
}
REQUIRED_AUDIT_ENTRY_FIELDS = (
    "function",
    "category",
    "binary_pair",
    "left_binary_id",
    "right_binary_id",
    "side_or_role",
    "current_result",
    "expected_equivalent",
    "oracle_manifest_ref",
    "classification",
    "counterexample_model_ref",
    "sat_unsafety_status",
    "coverage_status",
    "coverage_status_source",
    "coverage_gap_status",
    "call_memory_effect_status",
    "target_proof_lane",
    "oracle_decision_status",
    "replay_harness",
    "input_width_policy",
    "return_compare_width",
    "memory_initial_state",
    "ub_exclusion_rule",
    "audit_source",
)
EXPECTED_TARGET_PROOF_LANE_COUNTS = {
    "not_eq_counterexample_replay": 72,
}
EXPECTED_REPLAY_STATUS_COUNTS = {
    "missing": 72,
}
EXPECTED_COVERAGE_STATUS_SOURCE_COUNTS = {
    "/pairwise_stats": 54,
    "<missing>": 18,
}
EXPECTED_AUDIT_CATEGORY_COUNTS = {
    "function_call": 71,
    "loop": 1,
}
EXPECTED_ORACLE_SCOPE_COUNTS = {
    "function_category": 3,
}
EXPECTED_ORACLE_EXPECTED_EQUIVALENT_COUNTS = {
    "true": 3,
}


def build_phase0d_not_eq_audit_gate(
    *,
    baseline_raw_dir: Path,
    audit_manifest: Path,
    oracle_manifest: Path,
    output_dir: Path,
    expected_entry_count: int = EXPECTED_ENTRY_COUNT,
    expected_classification_counts: Optional[Mapping[str, int]] = None,
    expected_oracle_review_status_counts: Optional[Mapping[str, int]] = None,
    expected_target_proof_lane_counts: Optional[Mapping[str, int]] = None,
    expected_replay_status_counts: Optional[Mapping[str, int]] = None,
    expected_coverage_status_source_counts: Optional[Mapping[str, int]] = None,
    expected_audit_category_counts: Optional[Mapping[str, int]] = None,
    expected_oracle_scope_counts: Optional[Mapping[str, int]] = None,
    expected_oracle_expected_equivalent_counts: Optional[Mapping[str, int]] = None,
) -> Path:
    raw_dir = Path(baseline_raw_dir)
    output = Path(output_dir)
    output.mkdir(parents=True, exist_ok=True)

    raw_manifest = _read_json(raw_dir / "artifact_manifest.json")
    audit = _read_json(Path(audit_manifest))
    oracle = _read_json(Path(oracle_manifest))

    checks = []
    checks.extend(_schema_checks(audit, oracle))
    checks.extend(_baseline_identity_checks(raw_manifest, audit, oracle))
    checks.extend(
        _count_checks(
            audit=audit,
            oracle=oracle,
            expected_entry_count=expected_entry_count,
            expected_classification_counts=dict(expected_classification_counts or EXPECTED_CLASSIFICATION_COUNTS),
            expected_oracle_review_status_counts=dict(
                expected_oracle_review_status_counts or EXPECTED_ORACLE_REVIEW_STATUS_COUNTS
            ),
        )
    )
    checks.extend(_oracle_scope_checks(audit, oracle))
    checks.extend(_audit_source_log_checks(audit, raw_dir))
    audit_posture = _audit_acceptance_posture(audit)
    checks.extend(
        _audit_acceptance_posture_checks(
            audit_posture,
            expected_target_proof_lane_counts=dict(
                expected_target_proof_lane_counts or EXPECTED_TARGET_PROOF_LANE_COUNTS
            ),
            expected_replay_status_counts=dict(expected_replay_status_counts or EXPECTED_REPLAY_STATUS_COUNTS),
            expected_coverage_status_source_counts=dict(
                expected_coverage_status_source_counts or EXPECTED_COVERAGE_STATUS_SOURCE_COUNTS
            ),
        )
    )
    concrete_identity_report = _audit_concrete_identity_report(audit)
    checks.extend(
        _audit_concrete_identity_checks(
            concrete_identity_report,
            expected_audit_category_counts=dict(expected_audit_category_counts or EXPECTED_AUDIT_CATEGORY_COUNTS),
        )
    )
    oracle_posture = _oracle_posture(oracle)
    checks.extend(
        _oracle_posture_checks(
            oracle_posture,
            expected_oracle_scope_counts=dict(expected_oracle_scope_counts or EXPECTED_ORACLE_SCOPE_COUNTS),
            expected_oracle_expected_equivalent_counts=dict(
                expected_oracle_expected_equivalent_counts or EXPECTED_ORACLE_EXPECTED_EQUIVALENT_COUNTS
            ),
        )
    )

    summary = _summary(checks)
    manifest = {
        "manifest_version": MANIFEST_VERSION,
        "manifest_kind": "phase0d_not_eq_audit_gate",
        "artifact_role": "derived_audit_phase0d_gate",
        "created_at": datetime.now(timezone.utc).isoformat(),
        "baseline_id": raw_manifest.get("baseline_id"),
        "baseline_git_head": raw_manifest.get("git_head"),
        "baseline_raw_artifact_ref": {
            "path": str(raw_dir / "artifact_manifest.json"),
        },
        "audit_manifest_ref": {
            "path": str(Path(audit_manifest)),
            "sha256": _sha256_file(Path(audit_manifest)),
            "entry_count": len(audit.get("entries") or ()),
        },
        "oracle_manifest_ref": {
            "path": str(Path(oracle_manifest)),
            "sha256": _sha256_file(Path(oracle_manifest)),
            "entry_count": len(oracle.get("entries") or ()),
        },
        "expected_entry_count": expected_entry_count,
        "expected_classification_counts": dict(expected_classification_counts or EXPECTED_CLASSIFICATION_COUNTS),
        "expected_oracle_review_status_counts": dict(
            expected_oracle_review_status_counts or EXPECTED_ORACLE_REVIEW_STATUS_COUNTS
        ),
        "expected_target_proof_lane_counts": dict(
            expected_target_proof_lane_counts or EXPECTED_TARGET_PROOF_LANE_COUNTS
        ),
        "expected_replay_status_counts": dict(expected_replay_status_counts or EXPECTED_REPLAY_STATUS_COUNTS),
        "expected_coverage_status_source_counts": dict(
            expected_coverage_status_source_counts or EXPECTED_COVERAGE_STATUS_SOURCE_COUNTS
        ),
        "expected_audit_category_counts": dict(expected_audit_category_counts or EXPECTED_AUDIT_CATEGORY_COUNTS),
        "expected_oracle_scope_counts": dict(expected_oracle_scope_counts or EXPECTED_ORACLE_SCOPE_COUNTS),
        "expected_oracle_expected_equivalent_counts": dict(
            expected_oracle_expected_equivalent_counts or EXPECTED_ORACLE_EXPECTED_EQUIVALENT_COUNTS
        ),
        "classification_counts": _classification_counts(audit),
        "oracle_review_status_counts": _oracle_review_status_counts(oracle),
        "audit_acceptance_posture": audit_posture,
        "audit_concrete_identities": concrete_identity_report,
        "oracle_posture": oracle_posture,
        "phase0d_not_eq_audit_ready": summary["failed"] == 0,
        "summary": summary,
        "checks": checks,
    }
    path = output / "phase0d_not_eq_audit_gate.json"
    _write_json(path, manifest)
    return path


def validate_phase0d_not_eq_audit_gate(manifest: Mapping[str, Any]) -> None:
    summary = manifest.get("summary")
    failures = []
    if not isinstance(summary, Mapping):
        failures.append("summary_missing")
    else:
        failures.extend(str(kind) for kind in (summary.get("failed_kinds") or ()))
    checks = manifest.get("checks")
    if isinstance(checks, list):
        failures.extend(
            str(check.get("kind"))
            for check in checks
            if isinstance(check, Mapping) and check.get("status") == "failed"
        )
    else:
        failures.append("checks_missing")
    if manifest.get("phase0d_not_eq_audit_ready") is not True:
        failures.append("phase0d_not_eq_audit_not_ready")
    materialized = _materialize_phase0d_gate_from_manifest(manifest)
    if materialized is None:
        failures.append("materialized_context_missing")
    else:
        for key in (
            "baseline_id",
            "baseline_git_head",
            "baseline_raw_artifact_ref",
            "audit_manifest_ref",
            "oracle_manifest_ref",
            "expected_entry_count",
            "expected_classification_counts",
            "expected_oracle_review_status_counts",
            "expected_target_proof_lane_counts",
            "expected_replay_status_counts",
            "expected_coverage_status_source_counts",
            "expected_audit_category_counts",
            "expected_oracle_scope_counts",
            "expected_oracle_expected_equivalent_counts",
            "classification_counts",
            "oracle_review_status_counts",
            "audit_acceptance_posture",
            "audit_concrete_identities",
            "oracle_posture",
            "phase0d_not_eq_audit_ready",
            "summary",
            "checks",
        ):
            if not _strict_json_equal(manifest.get(key), materialized.get(key)):
                failures.append(f"materialized_{key}")
    failures = list(dict.fromkeys(failures))
    if not failures:
        return
    if manifest.get("phase0d_not_eq_audit_ready") is False and failures == ["phase0d_not_eq_audit_not_ready"]:
        raise ValueError("Phase 0D NOT_EQ audit gate is not ready without failed gate kinds")
    raise ValueError(f"Phase 0D NOT_EQ audit gate failed: {', '.join(map(str, failures))}")


def _materialize_phase0d_gate_from_manifest(manifest: Mapping[str, Any]) -> Optional[Dict[str, Any]]:
    baseline_ref = manifest.get("baseline_raw_artifact_ref")
    audit_ref = manifest.get("audit_manifest_ref")
    oracle_ref = manifest.get("oracle_manifest_ref")
    if not isinstance(baseline_ref, Mapping) or not isinstance(audit_ref, Mapping) or not isinstance(oracle_ref, Mapping):
        return None
    baseline_manifest_path = baseline_ref.get("path")
    audit_path = audit_ref.get("path")
    oracle_path = oracle_ref.get("path")
    if not isinstance(baseline_manifest_path, str) or not isinstance(audit_path, str) or not isinstance(oracle_path, str):
        return None
    raw_manifest_path = Path(baseline_manifest_path)
    audit_manifest_path = Path(audit_path)
    oracle_manifest_path = Path(oracle_path)
    if not raw_manifest_path.is_file() or not audit_manifest_path.is_file() or not oracle_manifest_path.is_file():
        return None

    raw_dir = raw_manifest_path.parent
    raw_manifest = _read_json(raw_manifest_path)
    audit = _read_json(audit_manifest_path)
    oracle = _read_json(oracle_manifest_path)
    expected_entry_count = manifest.get("expected_entry_count")
    if not isinstance(expected_entry_count, int):
        return None
    expected_classification_counts = dict(
        manifest.get("expected_classification_counts") or EXPECTED_CLASSIFICATION_COUNTS
    )
    expected_oracle_review_status_counts = dict(
        manifest.get("expected_oracle_review_status_counts") or EXPECTED_ORACLE_REVIEW_STATUS_COUNTS
    )
    expected_target_proof_lane_counts = dict(
        manifest.get("expected_target_proof_lane_counts") or EXPECTED_TARGET_PROOF_LANE_COUNTS
    )
    expected_replay_status_counts = dict(
        manifest.get("expected_replay_status_counts") or EXPECTED_REPLAY_STATUS_COUNTS
    )
    expected_coverage_status_source_counts = dict(
        manifest.get("expected_coverage_status_source_counts") or EXPECTED_COVERAGE_STATUS_SOURCE_COUNTS
    )
    expected_audit_category_counts = dict(
        manifest.get("expected_audit_category_counts") or EXPECTED_AUDIT_CATEGORY_COUNTS
    )
    expected_oracle_scope_counts = dict(
        manifest.get("expected_oracle_scope_counts") or EXPECTED_ORACLE_SCOPE_COUNTS
    )
    expected_oracle_expected_equivalent_counts = dict(
        manifest.get("expected_oracle_expected_equivalent_counts")
        or EXPECTED_ORACLE_EXPECTED_EQUIVALENT_COUNTS
    )

    checks = []
    checks.extend(_schema_checks(audit, oracle))
    checks.extend(_baseline_identity_checks(raw_manifest, audit, oracle))
    checks.extend(
        _count_checks(
            audit=audit,
            oracle=oracle,
            expected_entry_count=expected_entry_count,
            expected_classification_counts=expected_classification_counts,
            expected_oracle_review_status_counts=expected_oracle_review_status_counts,
        )
    )
    checks.extend(_oracle_scope_checks(audit, oracle))
    checks.extend(_audit_source_log_checks(audit, raw_dir))
    audit_posture = _audit_acceptance_posture(audit)
    checks.extend(
        _audit_acceptance_posture_checks(
            audit_posture,
            expected_target_proof_lane_counts=expected_target_proof_lane_counts,
            expected_replay_status_counts=expected_replay_status_counts,
            expected_coverage_status_source_counts=expected_coverage_status_source_counts,
        )
    )
    concrete_identity_report = _audit_concrete_identity_report(audit)
    checks.extend(
        _audit_concrete_identity_checks(
            concrete_identity_report,
            expected_audit_category_counts=expected_audit_category_counts,
        )
    )
    oracle_posture = _oracle_posture(oracle)
    checks.extend(
        _oracle_posture_checks(
            oracle_posture,
            expected_oracle_scope_counts=expected_oracle_scope_counts,
            expected_oracle_expected_equivalent_counts=expected_oracle_expected_equivalent_counts,
        )
    )
    summary = _summary(checks)
    return {
        "baseline_id": raw_manifest.get("baseline_id"),
        "baseline_git_head": raw_manifest.get("git_head"),
        "baseline_raw_artifact_ref": {"path": str(raw_manifest_path)},
        "audit_manifest_ref": {
            "path": str(audit_manifest_path),
            "sha256": _sha256_file(audit_manifest_path),
            "entry_count": len(audit.get("entries") or ()),
        },
        "oracle_manifest_ref": {
            "path": str(oracle_manifest_path),
            "sha256": _sha256_file(oracle_manifest_path),
            "entry_count": len(oracle.get("entries") or ()),
        },
        "expected_entry_count": expected_entry_count,
        "expected_classification_counts": expected_classification_counts,
        "expected_oracle_review_status_counts": expected_oracle_review_status_counts,
        "expected_target_proof_lane_counts": expected_target_proof_lane_counts,
        "expected_replay_status_counts": expected_replay_status_counts,
        "expected_coverage_status_source_counts": expected_coverage_status_source_counts,
        "expected_audit_category_counts": expected_audit_category_counts,
        "expected_oracle_scope_counts": expected_oracle_scope_counts,
        "expected_oracle_expected_equivalent_counts": expected_oracle_expected_equivalent_counts,
        "classification_counts": _classification_counts(audit),
        "oracle_review_status_counts": _oracle_review_status_counts(oracle),
        "audit_acceptance_posture": audit_posture,
        "audit_concrete_identities": concrete_identity_report,
        "oracle_posture": oracle_posture,
        "phase0d_not_eq_audit_ready": summary["failed"] == 0,
        "summary": summary,
        "checks": checks,
    }


def _strict_json_equal(left: Any, right: Any) -> bool:
    return json.dumps(left, sort_keys=True, separators=(",", ":")) == json.dumps(
        right,
        sort_keys=True,
        separators=(",", ":"),
    )


def main(argv: Optional[Sequence[str]] = None) -> int:
    parser = argparse.ArgumentParser(description="Build a Phase 0D NOT_EQ audit gate.")
    parser.add_argument("--baseline-raw-dir", required=True)
    parser.add_argument("--audit-manifest", required=True)
    parser.add_argument("--oracle-manifest", required=True)
    parser.add_argument("--output-dir", required=True)
    parser.add_argument("--expected-entry-count", type=int, default=EXPECTED_ENTRY_COUNT)
    parser.add_argument("--require-ready", action="store_true")
    args = parser.parse_args(argv)

    path = build_phase0d_not_eq_audit_gate(
        baseline_raw_dir=Path(args.baseline_raw_dir),
        audit_manifest=Path(args.audit_manifest),
        oracle_manifest=Path(args.oracle_manifest),
        output_dir=Path(args.output_dir),
        expected_entry_count=args.expected_entry_count,
    )
    print(path)
    if args.require_ready:
        validate_phase0d_not_eq_audit_gate(_read_json(path))
    return 0


def _schema_checks(audit: Mapping[str, Any], oracle: Mapping[str, Any]) -> Sequence[Dict[str, Any]]:
    checks = []
    try:
        validate_oracle_manifest(oracle)
        validate_not_eq_audit_manifest(audit, oracle_manifest=oracle)
    except ValueError as exc:
        checks.append(_failed("not_eq_audit_oracle_schema", error=str(exc)))
    else:
        checks.append(_ok("not_eq_audit_oracle_schema"))
    return checks


def _baseline_identity_checks(
    raw_manifest: Mapping[str, Any],
    audit: Mapping[str, Any],
    oracle: Mapping[str, Any],
) -> Sequence[Dict[str, Any]]:
    raw_baseline_id = raw_manifest.get("baseline_id")
    raw_git_head = raw_manifest.get("git_head")
    checks = [
        _ok("baseline_id_expected", baseline_id=raw_baseline_id)
        if raw_baseline_id == EXPECTED_BASELINE_ID
        else _failed("baseline_id_expected", expected=EXPECTED_BASELINE_ID, actual=raw_baseline_id),
        _ok("baseline_git_head_expected", baseline_git_head=raw_git_head)
        if raw_git_head == EXPECTED_GIT_HEAD
        else _failed("baseline_git_head_expected", expected=EXPECTED_GIT_HEAD, actual=raw_git_head),
    ]
    for kind, payload in (("audit", audit), ("oracle", oracle)):
        checks.append(
            _ok(f"{kind}_baseline_id_matches_raw")
            if payload.get("baseline_id") == raw_baseline_id
            else _failed(f"{kind}_baseline_id_matches_raw", expected=raw_baseline_id, actual=payload.get("baseline_id"))
        )
        checks.append(
            _ok(f"{kind}_baseline_git_head_matches_raw")
            if payload.get("baseline_git_head") == raw_git_head
            else _failed(
                f"{kind}_baseline_git_head_matches_raw",
                expected=raw_git_head,
                actual=payload.get("baseline_git_head"),
            )
        )
    dirty_state = raw_manifest.get("dirty_state")
    checks.append(
        _ok("dirty_snapshot_hash_present")
        if isinstance(dirty_state, Mapping)
        and (
            dirty_state.get("is_dirty") is not True
            or bool(dirty_state.get("dirty_snapshot_hash"))
        )
        else _failed("dirty_snapshot_hash_present")
    )
    return checks


def _count_checks(
    *,
    audit: Mapping[str, Any],
    oracle: Mapping[str, Any],
    expected_entry_count: int,
    expected_classification_counts: Mapping[str, int],
    expected_oracle_review_status_counts: Mapping[str, int],
) -> Sequence[Dict[str, Any]]:
    actual_entry_count = len(audit.get("entries") or ())
    actual_classification_counts = _classification_counts(audit)
    actual_oracle_review_status_counts = _oracle_review_status_counts(oracle)
    checks = [
        _ok("not_eq_audit_entry_count_expected", count=actual_entry_count)
        if actual_entry_count == expected_entry_count
        else _failed("not_eq_audit_entry_count_expected", expected=expected_entry_count, actual=actual_entry_count),
        _ok("not_eq_audit_classification_counts_expected", counts=actual_classification_counts)
        if actual_classification_counts == dict(expected_classification_counts)
        else _failed(
            "not_eq_audit_classification_counts_expected",
            expected=dict(expected_classification_counts),
            actual=actual_classification_counts,
        ),
        _ok("not_eq_audit_no_accepted_ground_truth", count=actual_classification_counts.get("ground_truth_not_eq", 0))
        if actual_classification_counts.get("ground_truth_not_eq", 0) == 0
        else _failed("not_eq_audit_no_accepted_ground_truth", actual=actual_classification_counts.get("ground_truth_not_eq")),
        _ok("not_eq_audit_classification_enum_expected")
        if tuple(audit.get("classification_enum") or ()) == tuple(sorted(CLASSIFICATIONS))
        else _failed("not_eq_audit_classification_enum_expected"),
        _ok("oracle_review_status_counts_expected", counts=actual_oracle_review_status_counts)
        if actual_oracle_review_status_counts == dict(expected_oracle_review_status_counts)
        else _failed(
            "oracle_review_status_counts_expected",
            expected=dict(expected_oracle_review_status_counts),
            actual=actual_oracle_review_status_counts,
        ),
    ]
    return checks


def _oracle_scope_checks(audit: Mapping[str, Any], oracle: Mapping[str, Any]) -> Sequence[Dict[str, Any]]:
    oracle_keys = {str(entry.get("entry_key")) for entry in oracle.get("entries") or () if isinstance(entry, Mapping)}
    audit_keys = {
        str((entry.get("oracle_manifest_ref") or {}).get("entry_key"))
        for entry in audit.get("entries") or ()
        if isinstance(entry, Mapping) and isinstance(entry.get("oracle_manifest_ref"), Mapping)
    }
    missing = sorted(audit_keys - oracle_keys)
    unused = sorted(oracle_keys - audit_keys)
    return [
        _ok("audit_oracle_refs_all_resolved", count=len(audit_keys))
        if not missing
        else _failed("audit_oracle_refs_all_resolved", missing=missing),
        _ok("oracle_entries_all_used_by_audit", count=len(oracle_keys))
        if not unused
        else _failed("oracle_entries_all_used_by_audit", unused=unused),
    ]


def _audit_source_log_checks(audit: Mapping[str, Any], raw_dir: Path) -> Sequence[Dict[str, Any]]:
    missing = []
    mismatched = []
    checked_count = 0
    for index, entry in enumerate(audit.get("entries") or ()):
        if not isinstance(entry, Mapping):
            continue
        source = entry.get("audit_source")
        if not isinstance(source, Mapping):
            missing.append(_audit_entry_identity(index, entry))
            continue
        rel_path = source.get("log_path")
        expected_hash = source.get("log_sha256")
        if not rel_path or not expected_hash:
            missing.append(_audit_entry_identity(index, entry))
            continue
        path = raw_dir / str(rel_path)
        if not path.is_file():
            missing.append({**_audit_entry_identity(index, entry), "path": str(rel_path)})
            continue
        checked_count += 1
        actual_hash = _sha256_file(path)
        if actual_hash != expected_hash:
            mismatched.append(
                {
                    **_audit_entry_identity(index, entry),
                    "path": str(rel_path),
                    "expected": expected_hash,
                    "actual": actual_hash,
                }
            )
    return [
        _ok("not_eq_audit_source_logs_present", count=checked_count)
        if not missing
        else _failed("not_eq_audit_source_logs_present", missing=missing),
        _ok("not_eq_audit_source_log_hashes_match", count=checked_count)
        if not mismatched
        else _failed("not_eq_audit_source_log_hashes_match", mismatched=mismatched[:20]),
    ]


def _classification_counts(audit: Mapping[str, Any]) -> Dict[str, int]:
    return dict(sorted(Counter(str(entry.get("classification") or "") for entry in audit.get("entries") or ()).items()))


def _oracle_review_status_counts(oracle: Mapping[str, Any]) -> Dict[str, int]:
    return dict(sorted(Counter(str(entry.get("oracle_review_status") or "") for entry in oracle.get("entries") or ()).items()))


def _audit_acceptance_posture(audit: Mapping[str, Any]) -> Dict[str, Any]:
    entries = tuple(entry for entry in audit.get("entries") or () if isinstance(entry, Mapping))
    missing_required_fields = []
    ground_truth_conflicts_without_override = []
    ground_truth_entries_without_accepted_oracle = []
    target_proof_lane_counts: Counter[str] = Counter()
    replay_status_counts: Counter[str] = Counter()
    coverage_status_source_counts: Counter[str] = Counter()
    for index, entry in enumerate(entries):
        missing = [field for field in REQUIRED_AUDIT_ENTRY_FIELDS if field not in entry]
        if missing:
            missing_required_fields.append(
                {
                    "index": index,
                    "function": entry.get("function"),
                    "binary_pair": entry.get("binary_pair"),
                    "missing_fields": missing,
                }
            )
        target_proof_lane_counts[str(entry.get("target_proof_lane") or "")] += 1
        replay = entry.get("counterexample_model_ref")
        replay_status_counts[
            str(replay.get("replay_status") if isinstance(replay, Mapping) else "<missing>")
        ] += 1
        coverage_status_source_counts[str(entry.get("coverage_status_source") or "<missing>")] += 1
        if entry.get("classification") != "ground_truth_not_eq":
            continue
        oracle_ref = entry.get("oracle_manifest_ref")
        if not isinstance(oracle_ref, Mapping) or oracle_ref.get("oracle_review_status") != "accepted":
            ground_truth_entries_without_accepted_oracle.append(_audit_entry_identity(index, entry))
        if _has_expected_equivalent_conflict(entry) and not _has_accepted_not_eq_override(entry):
            ground_truth_conflicts_without_override.append(_audit_entry_identity(index, entry))
    return {
        "required_entry_fields": list(REQUIRED_AUDIT_ENTRY_FIELDS),
        "missing_required_field_entries": missing_required_fields,
        "missing_required_field_entry_count": len(missing_required_fields),
        "ground_truth_conflicts_without_override": ground_truth_conflicts_without_override,
        "ground_truth_conflict_without_override_count": len(ground_truth_conflicts_without_override),
        "ground_truth_entries_without_accepted_oracle": ground_truth_entries_without_accepted_oracle,
        "ground_truth_without_accepted_oracle_count": len(ground_truth_entries_without_accepted_oracle),
        "target_proof_lane_counts": dict(sorted(target_proof_lane_counts.items())),
        "replay_status_counts": dict(sorted(replay_status_counts.items())),
        "coverage_status_source_counts": dict(sorted(coverage_status_source_counts.items())),
    }


def _audit_acceptance_posture_checks(
    posture: Mapping[str, Any],
    *,
    expected_target_proof_lane_counts: Mapping[str, int],
    expected_replay_status_counts: Mapping[str, int],
    expected_coverage_status_source_counts: Mapping[str, int],
) -> Sequence[Dict[str, Any]]:
    target_counts = posture.get("target_proof_lane_counts") or {}
    replay_counts = posture.get("replay_status_counts") or {}
    coverage_sources = posture.get("coverage_status_source_counts") or {}
    return [
        _ok("not_eq_audit_required_fields_present")
        if int(posture.get("missing_required_field_entry_count") or 0) == 0
        else _failed(
            "not_eq_audit_required_fields_present",
            missing_entries=posture.get("missing_required_field_entries"),
        ),
        _ok("not_eq_ground_truth_conflicts_have_override")
        if int(posture.get("ground_truth_conflict_without_override_count") or 0) == 0
        else _failed(
            "not_eq_ground_truth_conflicts_have_override",
            conflicts=posture.get("ground_truth_conflicts_without_override"),
        ),
        _ok("not_eq_ground_truth_requires_accepted_oracle")
        if int(posture.get("ground_truth_without_accepted_oracle_count") or 0) == 0
        else _failed(
            "not_eq_ground_truth_requires_accepted_oracle",
            entries=posture.get("ground_truth_entries_without_accepted_oracle"),
        ),
        _ok("not_eq_audit_target_proof_lane_counts_expected", counts=dict(target_counts))
        if dict(target_counts) == dict(expected_target_proof_lane_counts)
        else _failed(
            "not_eq_audit_target_proof_lane_counts_expected",
            expected=dict(expected_target_proof_lane_counts),
            actual=dict(target_counts),
        ),
        _ok("not_eq_audit_replay_status_counts_expected", counts=dict(replay_counts))
        if dict(replay_counts) == dict(expected_replay_status_counts)
        else _failed(
            "not_eq_audit_replay_status_counts_expected",
            expected=dict(expected_replay_status_counts),
            actual=dict(replay_counts),
        ),
        _ok("not_eq_audit_coverage_status_source_counts_expected", counts=dict(coverage_sources))
        if dict(coverage_sources) == dict(expected_coverage_status_source_counts)
        else _failed(
            "not_eq_audit_coverage_status_source_counts_expected",
            expected=dict(expected_coverage_status_source_counts),
            actual=dict(coverage_sources),
        ),
    ]


def _audit_entry_identity(index: int, entry: Mapping[str, Any]) -> Dict[str, Any]:
    return {
        "index": index,
        "function": entry.get("function"),
        "category": entry.get("category"),
        "binary_pair": entry.get("binary_pair"),
        "classification": entry.get("classification"),
    }


def _audit_concrete_identity_report(audit: Mapping[str, Any]) -> Dict[str, Any]:
    entries = []
    identity_counts: Counter[tuple[str, str, str]] = Counter()
    category_counts: Counter[str] = Counter()
    missing = []
    pair_mismatches = []
    for index, entry in enumerate(audit.get("entries") or ()):
        if not isinstance(entry, Mapping):
            continue
        identity = {
            "index": index,
            "category": entry.get("category"),
            "function": entry.get("function"),
            "binary_pair": entry.get("binary_pair"),
            "left_binary_id": entry.get("left_binary_id"),
            "right_binary_id": entry.get("right_binary_id"),
        }
        entries.append(identity)
        required_missing = [
            field
            for field in ("category", "function", "binary_pair", "left_binary_id", "right_binary_id")
            if not entry.get(field)
        ]
        if required_missing:
            missing.append({**identity, "missing_fields": required_missing})
            continue
        key = (str(entry["category"]), str(entry["function"]), str(entry["binary_pair"]))
        identity_counts[key] += 1
        category_counts[str(entry["category"])] += 1
        expected_pair = _canonical_binary_pair_from_sides(entry["left_binary_id"], entry["right_binary_id"])
        if str(entry["binary_pair"]) != expected_pair:
            pair_mismatches.append({**identity, "expected_binary_pair": expected_pair})
    duplicates = [
        {
            "category": key[0],
            "function": key[1],
            "binary_pair": key[2],
            "count": count,
        }
        for key, count in sorted(identity_counts.items())
        if count > 1
    ]
    return {
        "entry_count": len(entries),
        "unique_concrete_identity_count": len(identity_counts),
        "category_counts": dict(sorted(category_counts.items())),
        "duplicate_concrete_identities": duplicates,
        "missing_concrete_identity_fields": missing,
        "binary_pair_side_mismatches": pair_mismatches,
        "entries": entries,
    }


def _audit_concrete_identity_checks(
    report: Mapping[str, Any],
    *,
    expected_audit_category_counts: Mapping[str, int],
) -> Sequence[Dict[str, Any]]:
    duplicates = list(report.get("duplicate_concrete_identities") or ())
    missing = list(report.get("missing_concrete_identity_fields") or ())
    pair_mismatches = list(report.get("binary_pair_side_mismatches") or ())
    category_counts = dict(report.get("category_counts") or {})
    return [
        _ok("not_eq_audit_concrete_identities_unique", count=report.get("unique_concrete_identity_count"))
        if not duplicates
        else _failed("not_eq_audit_concrete_identities_unique", duplicates=duplicates),
        _ok("not_eq_audit_concrete_identity_fields_present", count=report.get("entry_count"))
        if not missing
        else _failed("not_eq_audit_concrete_identity_fields_present", missing=missing),
        _ok("not_eq_audit_binary_pair_matches_sides", count=report.get("entry_count"))
        if not pair_mismatches
        else _failed("not_eq_audit_binary_pair_matches_sides", mismatches=pair_mismatches),
        _ok("not_eq_audit_category_counts_expected", counts=category_counts)
        if category_counts == dict(expected_audit_category_counts)
        else _failed(
            "not_eq_audit_category_counts_expected",
            expected=dict(expected_audit_category_counts),
            actual=category_counts,
        ),
    ]


def _oracle_posture(oracle: Mapping[str, Any]) -> Dict[str, Any]:
    scope_counts: Counter[str] = Counter()
    expected_equivalent_counts: Counter[str] = Counter()
    scope_target_mismatches = []
    pair_scoped_entries = []
    for index, entry in enumerate(oracle.get("entries") or ()):
        if not isinstance(entry, Mapping):
            continue
        scope = str(entry.get("oracle_scope") or "")
        scope_counts[scope] += 1
        expected_equivalent_counts["true" if entry.get("expected_equivalent") is True else "false"] += 1
        target = entry.get("scope_target")
        if not isinstance(target, Mapping) or target.get("category") != entry.get("category") or target.get("function") != entry.get("function"):
            scope_target_mismatches.append(
                {
                    "index": index,
                    "entry_key": entry.get("entry_key"),
                    "category": entry.get("category"),
                    "function": entry.get("function"),
                    "scope_target": target,
                }
            )
        if scope == "pair":
            pair_scoped_entries.append(
                {
                    "index": index,
                    "entry_key": entry.get("entry_key"),
                    "scope_target": target,
                }
            )
    return {
        "scope_counts": dict(sorted(scope_counts.items())),
        "expected_equivalent_counts": dict(sorted(expected_equivalent_counts.items())),
        "scope_target_mismatches": scope_target_mismatches,
        "scope_target_mismatch_count": len(scope_target_mismatches),
        "pair_scoped_entries": pair_scoped_entries,
        "pair_scoped_entry_count": len(pair_scoped_entries),
    }


def _oracle_posture_checks(
    posture: Mapping[str, Any],
    *,
    expected_oracle_scope_counts: Mapping[str, int],
    expected_oracle_expected_equivalent_counts: Mapping[str, int],
) -> Sequence[Dict[str, Any]]:
    scope_counts = dict(posture.get("scope_counts") or {})
    expected_counts = dict(posture.get("expected_equivalent_counts") or {})
    return [
        _ok("oracle_scope_counts_expected", counts=scope_counts)
        if scope_counts == dict(expected_oracle_scope_counts)
        else _failed("oracle_scope_counts_expected", expected=dict(expected_oracle_scope_counts), actual=scope_counts),
        _ok("oracle_expected_equivalent_counts_expected", counts=expected_counts)
        if expected_counts == dict(expected_oracle_expected_equivalent_counts)
        else _failed(
            "oracle_expected_equivalent_counts_expected",
            expected=dict(expected_oracle_expected_equivalent_counts),
            actual=expected_counts,
        ),
        _ok("oracle_scope_targets_match_entries")
        if int(posture.get("scope_target_mismatch_count") or 0) == 0
        else _failed("oracle_scope_targets_match_entries", mismatches=posture.get("scope_target_mismatches")),
        _ok("oracle_pair_scope_absent_until_exception_review")
        if int(posture.get("pair_scoped_entry_count") or 0) == 0
        else _failed("oracle_pair_scope_absent_until_exception_review", pair_scoped_entries=posture.get("pair_scoped_entries")),
    ]


def _canonical_binary_pair_from_sides(left: Any, right: Any) -> str:
    return "_".join(sorted((str(left), str(right)), key=_binary_sort_key))


def _binary_sort_key(binary_id: str) -> tuple[int, str]:
    text = str(binary_id)
    if len(text) > 1 and text[0].upper() == "B" and text[1:].isdigit():
        return (0, f"{int(text[1:]):04d}")
    if len(text) > 1 and text[0].upper() == "S" and text[1:].isdigit():
        return (1, f"{int(text[1:]):04d}")
    return (2, text)


def _has_expected_equivalent_conflict(entry: Mapping[str, Any]) -> bool:
    if entry.get("expected_equivalent") is True:
        return True
    oracle_ref = entry.get("oracle_manifest_ref")
    return isinstance(oracle_ref, Mapping) and oracle_ref.get("expected_equivalent") is True


def _has_accepted_not_eq_override(entry: Mapping[str, Any]) -> bool:
    for field_name in ("oracle_exception", "eq_goal_exclusion"):
        value = entry.get(field_name)
        if not isinstance(value, Mapping):
            continue
        if value.get("status") == "accepted":
            return True
        if value.get("review_status") == "accepted":
            return True
        if value.get("oracle_review_status") == "accepted":
            return True
    return False


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


def _sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def _write_json(path: Path, payload: Any) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")


if __name__ == "__main__":
    raise SystemExit(main())
