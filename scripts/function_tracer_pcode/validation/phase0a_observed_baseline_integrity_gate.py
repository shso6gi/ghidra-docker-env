# -*- coding: utf-8 -*-
"""Build a Phase 0A observed-baseline raw artifact integrity gate.

This gate validates the frozen observed baseline as an immutable artifact.  It
does not run Ghidra or solvers; it verifies that the raw evidence present on the
machine still matches the hash index captured at baseline freeze time.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Dict, Mapping, Optional, Sequence


MANIFEST_VERSION = 1
EXPECTED_BASELINE_ID = "observed-v0@0a53352"
EXPECTED_GIT_HEAD = "0a53352cf3c9528abfb654906ed7b963474bedc5"
EXPECTED_RAW_EVIDENCE_GIT_POLICY = "external_not_committed"
EXPECTED_RAW_EVIDENCE_ROOT = "logs"
EXPECTED_HASH_INDEX_PATH = "file_hashes.json"
EXPECTED_RECOVERED_MANIFESTS = {
    "function_call": "function_call_20_manifest.json",
    "loop": "loop_5_manifest.json",
}
HASH_SAMPLE_LIMIT = 20


def build_phase0a_observed_baseline_integrity_gate(
    *,
    baseline_raw_dir: Path,
    output_dir: Path,
    validate_file_content_hashes: bool = True,
) -> Path:
    raw_dir = Path(baseline_raw_dir)
    output = Path(output_dir)
    output.mkdir(parents=True, exist_ok=True)

    raw_manifest_path = raw_dir / "artifact_manifest.json"
    hash_index_path = raw_dir / EXPECTED_HASH_INDEX_PATH
    raw_manifest = _read_json(raw_manifest_path)
    hash_index = _read_json(hash_index_path)

    checks = []
    checks.extend(_baseline_identity_checks(raw_manifest))
    checks.extend(_dirty_state_checks(raw_manifest))
    checks.extend(_artifact_storage_checks(raw_manifest, raw_dir))
    checks.extend(_hash_index_checks(raw_manifest, hash_index))
    checks.extend(_recovered_manifest_checks(raw_manifest, raw_dir))
    checks.extend(_source_path_checks(raw_manifest, hash_index))
    if validate_file_content_hashes:
        checks.extend(_file_content_hash_checks(raw_dir, hash_index))
    else:
        checks.append(_ok("file_content_hashes_validated", skipped=True, reason="disabled by CLI"))

    summary = _summary(checks)
    manifest = {
        "manifest_version": MANIFEST_VERSION,
        "manifest_kind": "phase0a_observed_baseline_integrity_gate",
        "artifact_role": "derived_observed_baseline_integrity_gate",
        "created_at": datetime.now(timezone.utc).isoformat(),
        "baseline_id": raw_manifest.get("baseline_id"),
        "baseline_git_head": raw_manifest.get("git_head"),
        "baseline_raw_artifact_ref": {
            "path": str(raw_manifest_path),
            "hash_index_path": str(hash_index_path),
        },
        "raw_evidence": {
            "indexed_file_count": len(hash_index),
            "validate_file_content_hashes": validate_file_content_hashes,
        },
        "phase0a_observed_baseline_integrity_ready": summary["failed"] == 0,
        "summary": summary,
        "checks": checks,
    }
    path = output / "phase0a_observed_baseline_integrity_gate.json"
    _write_json(path, manifest)
    return path


def validate_phase0a_observed_baseline_integrity_gate(manifest: Mapping[str, Any]) -> None:
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
    if manifest.get("phase0a_observed_baseline_integrity_ready") is not (expected_summary.get("failed") == 0):
        failures.append("phase0a_ready_consistency")

    materialized = _materialize_phase0a_gate_from_manifest(manifest)
    if materialized is None:
        failures.append("materialized_context_missing")
    else:
        for key in ("baseline_id", "baseline_git_head", "baseline_raw_artifact_ref", "raw_evidence"):
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
        raise ValueError(f"Phase 0A observed baseline integrity gate failed: {', '.join(map(str, all_failures))}")


def main(argv: Optional[Sequence[str]] = None) -> int:
    parser = argparse.ArgumentParser(description="Build a Phase 0A observed-baseline integrity gate.")
    parser.add_argument("--baseline-raw-dir", required=True)
    parser.add_argument("--output-dir", required=True)
    parser.add_argument(
        "--skip-file-content-hashes",
        action="store_true",
        help="validate metadata only; by default every indexed raw evidence file is hashed",
    )
    parser.add_argument("--require-ready", action="store_true")
    args = parser.parse_args(argv)

    path = build_phase0a_observed_baseline_integrity_gate(
        baseline_raw_dir=Path(args.baseline_raw_dir),
        output_dir=Path(args.output_dir),
        validate_file_content_hashes=not args.skip_file_content_hashes,
    )
    print(path)
    if args.require_ready:
        validate_phase0a_observed_baseline_integrity_gate(_read_json(path))
    return 0


def _materialize_phase0a_gate_from_manifest(manifest: Mapping[str, Any]) -> Optional[Dict[str, Any]]:
    baseline_ref = manifest.get("baseline_raw_artifact_ref")
    raw_evidence = manifest.get("raw_evidence")
    if not isinstance(baseline_ref, Mapping) or not isinstance(raw_evidence, Mapping):
        return None
    raw_manifest_path = baseline_ref.get("path")
    hash_index_path = baseline_ref.get("hash_index_path")
    if not isinstance(raw_manifest_path, str) or not isinstance(hash_index_path, str):
        return None
    raw_manifest_file = Path(raw_manifest_path)
    hash_index_file = Path(hash_index_path)
    if raw_manifest_file.name != "artifact_manifest.json" or hash_index_file.name != EXPECTED_HASH_INDEX_PATH:
        return None
    if not raw_manifest_file.is_file() or not hash_index_file.is_file():
        return None
    raw_dir = raw_manifest_file.parent
    raw_manifest = _read_json(raw_manifest_file)
    hash_index = _read_json(hash_index_file)
    validate_file_content_hashes = raw_evidence.get("validate_file_content_hashes") is not False

    checks = []
    checks.extend(_baseline_identity_checks(raw_manifest))
    checks.extend(_dirty_state_checks(raw_manifest))
    checks.extend(_artifact_storage_checks(raw_manifest, raw_dir))
    checks.extend(_hash_index_checks(raw_manifest, hash_index))
    checks.extend(_recovered_manifest_checks(raw_manifest, raw_dir))
    checks.extend(_source_path_checks(raw_manifest, hash_index))
    if validate_file_content_hashes:
        checks.extend(_file_content_hash_checks(raw_dir, hash_index))
    else:
        checks.append(_ok("file_content_hashes_validated", skipped=True, reason="disabled by CLI"))
    return {
        "baseline_id": raw_manifest.get("baseline_id"),
        "baseline_git_head": raw_manifest.get("git_head"),
        "baseline_raw_artifact_ref": {
            "path": str(raw_manifest_file),
            "hash_index_path": str(hash_index_file),
        },
        "raw_evidence": {
            "indexed_file_count": len(hash_index),
            "validate_file_content_hashes": validate_file_content_hashes,
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


def _dirty_state_checks(raw_manifest: Mapping[str, Any]) -> Sequence[Dict[str, Any]]:
    dirty_state = raw_manifest.get("dirty_state")
    is_dirty = isinstance(dirty_state, Mapping) and dirty_state.get("is_dirty") is True
    dirty_snapshot_hash = dirty_state.get("dirty_snapshot_hash") if isinstance(dirty_state, Mapping) else None
    return [
        _ok("dirty_state_present")
        if isinstance(dirty_state, Mapping)
        else _failed("dirty_state_present"),
        _ok("dirty_snapshot_hash_present", dirty_snapshot_hash=dirty_snapshot_hash)
        if not is_dirty or _is_sha256(dirty_snapshot_hash)
        else _failed("dirty_snapshot_hash_present", dirty_snapshot_hash=dirty_snapshot_hash),
    ]


def _artifact_storage_checks(raw_manifest: Mapping[str, Any], raw_dir: Path) -> Sequence[Dict[str, Any]]:
    storage = raw_manifest.get("artifact_storage")
    if not isinstance(storage, Mapping):
        return [_failed("artifact_storage_present")]
    tracked_paths = storage.get("tracked_metadata_paths") or ()
    checks = [
        _ok("artifact_storage_present"),
        _ok("raw_evidence_git_policy_expected")
        if storage.get("raw_evidence_git_policy") == EXPECTED_RAW_EVIDENCE_GIT_POLICY
        else _failed(
            "raw_evidence_git_policy_expected",
            expected=EXPECTED_RAW_EVIDENCE_GIT_POLICY,
            actual=storage.get("raw_evidence_git_policy"),
        ),
        _ok("raw_evidence_root_expected")
        if storage.get("raw_evidence_root") == EXPECTED_RAW_EVIDENCE_ROOT
        else _failed("raw_evidence_root_expected", expected=EXPECTED_RAW_EVIDENCE_ROOT, actual=storage.get("raw_evidence_root")),
        _ok("raw_evidence_hash_index_expected")
        if storage.get("raw_evidence_hash_index_path") == EXPECTED_HASH_INDEX_PATH
        else _failed(
            "raw_evidence_hash_index_expected",
            expected=EXPECTED_HASH_INDEX_PATH,
            actual=storage.get("raw_evidence_hash_index_path"),
        ),
        _ok("raw_evidence_complete_in_freeze_dir")
        if storage.get("raw_evidence_complete_in_freeze_dir") is True
        else _failed("raw_evidence_complete_in_freeze_dir", actual=storage.get("raw_evidence_complete_in_freeze_dir")),
    ]
    for rel_path in tracked_paths:
        path = raw_dir / str(rel_path)
        checks.append(
            _ok("tracked_metadata_present", path=str(rel_path))
            if path.is_file()
            else _failed("tracked_metadata_present", path=str(rel_path))
        )
    return checks


def _hash_index_checks(raw_manifest: Mapping[str, Any], hash_index: Mapping[str, Any]) -> Sequence[Dict[str, Any]]:
    embedded = raw_manifest.get("file_content_hashes")
    if not isinstance(embedded, Mapping):
        return [_failed("file_content_hashes_embedded")]
    normalized_hash_index = {str(key): str(value) for key, value in hash_index.items()}
    normalized_embedded = {str(key): str(value) for key, value in embedded.items()}
    invalid_hashes = sorted(
        key
        for key, value in normalized_hash_index.items()
        if not key.startswith(f"{EXPECTED_RAW_EVIDENCE_ROOT}/") or not _is_sha256(value)
    )
    checks = [
        _ok("file_hash_index_non_empty", count=len(normalized_hash_index))
        if normalized_hash_index
        else _failed("file_hash_index_non_empty"),
        _ok("file_hash_index_matches_manifest", count=len(normalized_hash_index))
        if normalized_hash_index == normalized_embedded
        else _failed(
            "file_hash_index_matches_manifest",
            file_hashes_count=len(normalized_hash_index),
            manifest_hashes_count=len(normalized_embedded),
            missing_in_index=sorted(set(normalized_embedded) - set(normalized_hash_index))[:HASH_SAMPLE_LIMIT],
            extra_in_index=sorted(set(normalized_hash_index) - set(normalized_embedded))[:HASH_SAMPLE_LIMIT],
        ),
        _ok("file_hash_index_entries_valid")
        if not invalid_hashes
        else _failed("file_hash_index_entries_valid", invalid_paths=invalid_hashes[:HASH_SAMPLE_LIMIT]),
    ]
    return checks


def _recovered_manifest_checks(raw_manifest: Mapping[str, Any], raw_dir: Path) -> Sequence[Dict[str, Any]]:
    recovered = raw_manifest.get("recovered_manifests")
    if not isinstance(recovered, Mapping):
        return [_failed("recovered_manifests_present")]
    checks = [_ok("recovered_manifests_present")]
    for category, expected_path in EXPECTED_RECOVERED_MANIFESTS.items():
        actual_path = recovered.get(category)
        path = raw_dir / str(actual_path or "")
        checks.append(
            _ok("recovered_manifest_path_expected", category=category, path=actual_path)
            if actual_path == expected_path
            else _failed("recovered_manifest_path_expected", category=category, expected=expected_path, actual=actual_path)
        )
        checks.append(
            _ok("recovered_manifest_file_present", category=category, path=actual_path)
            if path.is_file()
            else _failed("recovered_manifest_file_present", category=category, path=actual_path)
        )
    return checks


def _source_path_checks(raw_manifest: Mapping[str, Any], hash_index: Mapping[str, Any]) -> Sequence[Dict[str, Any]]:
    entries = raw_manifest.get("source_paths")
    if not isinstance(entries, Sequence) or isinstance(entries, (str, bytes)):
        return [_failed("source_paths_present")]
    checks = [_ok("source_paths_present", count=len(entries))]
    hash_keys = tuple(str(key) for key in hash_index)
    for entry in entries:
        if not isinstance(entry, Mapping):
            checks.append(_failed("source_path_entry_schema"))
            continue
        category = str(entry.get("category") or "")
        raw_copy_path = str(entry.get("raw_copy_path") or "")
        expected_prefix = f"{raw_copy_path.rstrip('/')}/"
        indexed_count = sum(1 for key in hash_keys if key.startswith(expected_prefix))
        checks.append(
            _ok("source_path_raw_copy_indexed", category=category, raw_copy_path=raw_copy_path, indexed_file_count=indexed_count)
            if indexed_count > 0
            else _failed("source_path_raw_copy_indexed", category=category, raw_copy_path=raw_copy_path)
        )
        checks.append(
            _ok("source_path_file_count_matches_index", category=category, file_count=entry.get("file_count"))
            if int(entry.get("file_count") or -1) == indexed_count
            else _failed(
                "source_path_file_count_matches_index",
                category=category,
                expected=entry.get("file_count"),
                actual=indexed_count,
            )
        )
    return checks


def _file_content_hash_checks(raw_dir: Path, hash_index: Mapping[str, Any]) -> Sequence[Dict[str, Any]]:
    missing = []
    mismatched = []
    checked = 0
    for rel_path, expected_hash in sorted((str(key), str(value)) for key, value in hash_index.items()):
        path = raw_dir / rel_path
        if not path.is_file():
            missing.append(rel_path)
            continue
        checked += 1
        actual_hash = _sha256_file(path)
        if actual_hash != expected_hash:
            mismatched.append({"path": rel_path, "expected": expected_hash, "actual": actual_hash})
    return [
        _ok("file_content_hashes_validated", checked=checked)
        if not missing and not mismatched
        else _failed(
            "file_content_hashes_validated",
            checked=checked,
            missing_count=len(missing),
            mismatch_count=len(mismatched),
            missing=missing[:HASH_SAMPLE_LIMIT],
            mismatched=mismatched[:HASH_SAMPLE_LIMIT],
        )
    ]


def _is_sha256(value: Any) -> bool:
    text = str(value or "")
    return len(text) == 64 and all(char in "0123456789abcdef" for char in text)


def _sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


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
