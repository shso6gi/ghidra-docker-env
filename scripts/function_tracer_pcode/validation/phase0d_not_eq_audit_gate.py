# -*- coding: utf-8 -*-
"""Build a Phase 0D NOT_EQ audit acceptance gate.

This gate intentionally does not bless any observed NOT_EQ as ground truth.
It freezes the current audit posture: observed same-source NOT_EQ results are
enumerated, linked to draft oracle entries, and remain unresolved until replay
and domain evidence upgrades individual entries.
"""

from __future__ import annotations

import argparse
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


def build_phase0d_not_eq_audit_gate(
    *,
    baseline_raw_dir: Path,
    audit_manifest: Path,
    oracle_manifest: Path,
    output_dir: Path,
    expected_entry_count: int = EXPECTED_ENTRY_COUNT,
    expected_classification_counts: Optional[Mapping[str, int]] = None,
    expected_oracle_review_status_counts: Optional[Mapping[str, int]] = None,
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
            "entry_count": len(audit.get("entries") or ()),
        },
        "oracle_manifest_ref": {
            "path": str(Path(oracle_manifest)),
            "entry_count": len(oracle.get("entries") or ()),
        },
        "expected_entry_count": expected_entry_count,
        "expected_classification_counts": dict(expected_classification_counts or EXPECTED_CLASSIFICATION_COUNTS),
        "expected_oracle_review_status_counts": dict(
            expected_oracle_review_status_counts or EXPECTED_ORACLE_REVIEW_STATUS_COUNTS
        ),
        "classification_counts": _classification_counts(audit),
        "oracle_review_status_counts": _oracle_review_status_counts(oracle),
        "phase0d_not_eq_audit_ready": summary["failed"] == 0,
        "summary": summary,
        "checks": checks,
    }
    path = output / "phase0d_not_eq_audit_gate.json"
    _write_json(path, manifest)
    return path


def validate_phase0d_not_eq_audit_gate(manifest: Mapping[str, Any]) -> None:
    if manifest.get("phase0d_not_eq_audit_ready") is True:
        return
    summary = manifest.get("summary")
    if not isinstance(summary, Mapping):
        raise ValueError("Phase 0D NOT_EQ audit gate is not ready and summary is missing")
    failed = summary.get("failed_kinds") or ()
    if not failed:
        raise ValueError("Phase 0D NOT_EQ audit gate is not ready without failed gate kinds")
    raise ValueError(f"Phase 0D NOT_EQ audit gate failed: {', '.join(map(str, failed))}")


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


def _classification_counts(audit: Mapping[str, Any]) -> Dict[str, int]:
    return dict(sorted(Counter(str(entry.get("classification") or "") for entry in audit.get("entries") or ()).items()))


def _oracle_review_status_counts(oracle: Mapping[str, Any]) -> Dict[str, int]:
    return dict(sorted(Counter(str(entry.get("oracle_review_status") or "") for entry in oracle.get("entries") or ()).items()))


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
