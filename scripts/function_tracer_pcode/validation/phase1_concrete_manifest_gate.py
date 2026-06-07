# -*- coding: utf-8 -*-
"""Validate frozen Phase 1 concrete manifests without regenerating them."""

from __future__ import annotations

import argparse
import hashlib
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Dict, Mapping, Optional, Sequence

from .phase1_concrete_manifests import (
    NEGATIVE_MINIMUM_CASES,
    validate_negative_manifest,
    validate_phase1_readiness,
    validate_positive_manifest,
    validate_representative_manifest,
    validate_synthetic_manifest,
)


MANIFEST_VERSION = 1
EXPECTED_BASELINE_ID = "observed-v0@0a53352"
EXPECTED_GIT_HEAD = "0a53352cf3c9528abfb654906ed7b963474bedc5"
EXPECTED_MANIFESTS = {
    "positive": ("positive_manifest.json", "positive_concrete_pairs"),
    "negative": ("negative_manifest.json", "negative_concrete_pairs"),
    "representative": ("representative_manifest.json", "representative_concrete_pairs"),
    "synthetic": ("synthetic_manifest.json", "synthetic_positive_manifest"),
}


def build_phase1_concrete_manifest_gate(
    *,
    phase1_dir: Path,
    baseline_raw_dir: Path,
    output_dir: Path,
) -> Path:
    phase1_root = Path(phase1_dir)
    raw_dir = Path(baseline_raw_dir)
    output = Path(output_dir)
    output.mkdir(parents=True, exist_ok=True)

    index_path = phase1_root / "phase1_manifest_index.json"
    index = _read_json(index_path)
    manifests = {
        name: _read_json(phase1_root / expected_path)
        for name, (expected_path, _expected_kind) in EXPECTED_MANIFESTS.items()
    }

    checks = []
    checks.extend(_index_checks(index))
    checks.extend(_manifest_identity_checks(index, manifests))
    checks.extend(_validator_checks(index, manifests))
    checks.extend(_source_artifact_checks(manifests, raw_dir))
    checks.extend(_object_evidence_ref_checks(manifests["positive"], phase1_root))
    checks.extend(_synthetic_artifact_ref_checks(manifests["synthetic"], phase1_root))
    checks.extend(_minimum_negative_case_checks(manifests["negative"]))

    manifest_hashes = {
        "index": _sha256_file(index_path),
        **{
            name: _sha256_file(phase1_root / expected_path)
            for name, (expected_path, _expected_kind) in EXPECTED_MANIFESTS.items()
        },
    }
    summary = _summary(checks)
    gate = {
        "manifest_version": MANIFEST_VERSION,
        "manifest_kind": "phase1_concrete_manifest_gate",
        "artifact_role": "derived_phase1_concrete_manifest_gate",
        "created_at": datetime.now(timezone.utc).isoformat(),
        "baseline_id": index.get("baseline_id"),
        "baseline_git_head": index.get("baseline_git_head"),
        "phase1_manifest_ref": {
            "phase1_dir": str(phase1_root),
            "index_path": str(index_path),
            "manifest_hashes": manifest_hashes,
        },
        "counts": dict(index.get("counts") or {}),
        "phase1_concrete_manifest_ready": summary["failed"] == 0,
        "summary": summary,
        "checks": checks,
    }
    path = output / "phase1_concrete_manifest_gate.json"
    _write_json(path, gate)
    return path


def validate_phase1_concrete_manifest_gate(manifest: Mapping[str, Any]) -> None:
    if manifest.get("phase1_concrete_manifest_ready") is True:
        return
    summary = manifest.get("summary")
    if not isinstance(summary, Mapping):
        raise ValueError("Phase 1 concrete manifest gate is not ready and summary is missing")
    failed = summary.get("failed_kinds") or ()
    if not failed:
        raise ValueError("Phase 1 concrete manifest gate is not ready without failed gate kinds")
    raise ValueError(f"Phase 1 concrete manifest gate failed: {', '.join(map(str, failed))}")


def main(argv: Optional[Sequence[str]] = None) -> int:
    parser = argparse.ArgumentParser(description="Validate frozen Phase 1 concrete manifests.")
    parser.add_argument("--phase1-dir", required=True)
    parser.add_argument("--baseline-raw-dir", required=True)
    parser.add_argument("--output-dir", required=True)
    parser.add_argument("--require-ready", action="store_true")
    args = parser.parse_args(argv)

    path = build_phase1_concrete_manifest_gate(
        phase1_dir=Path(args.phase1_dir),
        baseline_raw_dir=Path(args.baseline_raw_dir),
        output_dir=Path(args.output_dir),
    )
    print(path)
    if args.require_ready:
        validate_phase1_concrete_manifest_gate(_read_json(path))
    return 0


def _index_checks(index: Mapping[str, Any]) -> Sequence[Dict[str, Any]]:
    checks = [
        _ok("phase1_manifest_index_kind")
        if index.get("manifest_kind") == "phase1_concrete_manifest_index"
        else _failed("phase1_manifest_index_kind", actual=index.get("manifest_kind")),
        _ok("baseline_id_expected", baseline_id=index.get("baseline_id"))
        if index.get("baseline_id") == EXPECTED_BASELINE_ID
        else _failed("baseline_id_expected", expected=EXPECTED_BASELINE_ID, actual=index.get("baseline_id")),
        _ok("baseline_git_head_expected", baseline_git_head=index.get("baseline_git_head"))
        if index.get("baseline_git_head") == EXPECTED_GIT_HEAD
        else _failed("baseline_git_head_expected", expected=EXPECTED_GIT_HEAD, actual=index.get("baseline_git_head")),
        _ok("phase1_ready")
        if index.get("phase1_ready") is True
        else _failed("phase1_ready", actual=index.get("phase1_ready")),
    ]
    manifest_paths = index.get("manifests")
    if not isinstance(manifest_paths, Mapping):
        checks.append(_failed("phase1_manifest_paths_present"))
        return checks
    checks.append(_ok("phase1_manifest_paths_present"))
    for name, (expected_path, _expected_kind) in EXPECTED_MANIFESTS.items():
        actual = manifest_paths.get(name)
        checks.append(
            _ok("phase1_manifest_path_expected", manifest=name, path=actual)
            if actual == expected_path
            else _failed("phase1_manifest_path_expected", manifest=name, expected=expected_path, actual=actual)
        )
    return checks


def _manifest_identity_checks(
    index: Mapping[str, Any],
    manifests: Mapping[str, Mapping[str, Any]],
) -> Sequence[Dict[str, Any]]:
    checks = []
    for name, manifest in manifests.items():
        _expected_path, expected_kind = EXPECTED_MANIFESTS[name]
        checks.extend(
            [
                _ok("phase1_manifest_kind", manifest=name)
                if manifest.get("manifest_kind") == expected_kind
                else _failed("phase1_manifest_kind", manifest=name, expected=expected_kind, actual=manifest.get("manifest_kind")),
                _ok("phase1_manifest_baseline_id", manifest=name)
                if manifest.get("baseline_id") == index.get("baseline_id")
                else _failed("phase1_manifest_baseline_id", manifest=name, expected=index.get("baseline_id"), actual=manifest.get("baseline_id")),
                _ok("phase1_manifest_baseline_git_head", manifest=name)
                if manifest.get("baseline_git_head") == index.get("baseline_git_head")
                else _failed(
                    "phase1_manifest_baseline_git_head",
                    manifest=name,
                    expected=index.get("baseline_git_head"),
                    actual=manifest.get("baseline_git_head"),
                ),
            ]
        )
    counts = index.get("counts") or {}
    actual_counts = {
        "positive": len(manifests["positive"].get("entries") or ()),
        "negative": len(manifests["negative"].get("entries") or ()),
        "representative": len(manifests["representative"].get("entries") or ()),
        "synthetic": len(manifests["synthetic"].get("entries") or ()),
        "synthetic_negative": len(manifests["synthetic"].get("synthetic_negative_entries") or ()),
        "planned_negative_synthetic": manifests["synthetic"].get("planned_negative_synthetic_count"),
    }
    for name, actual in actual_counts.items():
        expected = counts.get(name)
        checks.append(
            _ok("phase1_manifest_count_expected", count_name=name, count=actual)
            if actual == expected
            else _failed("phase1_manifest_count_expected", count_name=name, expected=expected, actual=actual)
        )
    return checks


def _validator_checks(
    index: Mapping[str, Any],
    manifests: Mapping[str, Mapping[str, Any]],
) -> Sequence[Dict[str, Any]]:
    checks = []
    validators = (
        ("phase1_readiness_validator", lambda: validate_phase1_readiness(index)),
        (
            "positive_manifest_validator",
            lambda: validate_positive_manifest(manifests["positive"], require_object_evidence=True),
        ),
        ("negative_manifest_validator", lambda: validate_negative_manifest(manifests["negative"])),
        ("representative_manifest_validator", lambda: validate_representative_manifest(manifests["representative"])),
        ("synthetic_manifest_validator", lambda: validate_synthetic_manifest(manifests["synthetic"])),
    )
    for name, validator in validators:
        try:
            validator()
        except ValueError as exc:
            checks.append(_failed(name, error=str(exc)))
        else:
            checks.append(_ok(name))
    return checks


def _source_artifact_checks(
    manifests: Mapping[str, Mapping[str, Any]],
    raw_dir: Path,
) -> Sequence[Dict[str, Any]]:
    checks = []
    for manifest_name in ("positive", "negative", "representative"):
        for entry in manifests[manifest_name].get("entries") or ():
            if entry.get("category") == "synthetic_negative":
                checks.append(
                    _ok(
                        "phase1_source_artifact_not_required",
                        manifest=manifest_name,
                        entry_id=entry.get("id"),
                        category=entry.get("category"),
                    )
                )
                continue
            source = entry.get("source_artifact")
            if not isinstance(source, Mapping):
                checks.append(_failed("phase1_source_artifact_present", manifest=manifest_name, entry_id=entry.get("id")))
                continue
            rel_path = source.get("log_path")
            expected_hash = source.get("log_sha256")
            path = raw_dir / str(rel_path)
            if not path.is_file():
                checks.append(_failed("phase1_source_log_present", manifest=manifest_name, entry_id=entry.get("id"), path=rel_path))
                continue
            actual_hash = _sha256_file(path)
            checks.append(
                _ok("phase1_source_log_hash", manifest=manifest_name, entry_id=entry.get("id"), path=rel_path)
                if actual_hash == expected_hash
                else _failed(
                    "phase1_source_log_hash",
                    manifest=manifest_name,
                    entry_id=entry.get("id"),
                    path=rel_path,
                    expected=expected_hash,
                    actual=actual_hash,
                )
            )
    return checks


def _object_evidence_ref_checks(positive: Mapping[str, Any], phase1_root: Path) -> Sequence[Dict[str, Any]]:
    checks = []
    for entry in positive.get("entries") or ():
        ref = entry.get("object_evidence_ref")
        if not isinstance(ref, Mapping):
            checks.append(_failed("positive_object_evidence_ref_present", entry_id=entry.get("id")))
            continue
        checks.extend(_referenced_hash_checks(ref, phase1_root, "positive_object_evidence_ref", entry.get("id")))
    return checks


def _synthetic_artifact_ref_checks(synthetic: Mapping[str, Any], phase1_root: Path) -> Sequence[Dict[str, Any]]:
    ref = synthetic.get("synthetic_negative_artifact_ref")
    if not isinstance(ref, Mapping):
        return [_failed("synthetic_negative_artifact_ref_present")]
    return _referenced_hash_checks(ref, phase1_root, "synthetic_negative_artifact_ref", "synthetic")


def _referenced_hash_checks(
    ref: Mapping[str, Any],
    base_dir: Path,
    kind: str,
    entry_id: Any,
) -> Sequence[Dict[str, Any]]:
    rel_path = ref.get("path")
    expected_hash = ref.get("sha256")
    path = base_dir / str(rel_path)
    if not path.is_file():
        return [_failed(f"{kind}_present", entry_id=entry_id, path=rel_path)]
    actual_hash = _sha256_file(path)
    if actual_hash != expected_hash:
        return [
            _failed(
                f"{kind}_hash",
                entry_id=entry_id,
                path=rel_path,
                expected=expected_hash,
                actual=actual_hash,
            )
        ]
    return [_ok(f"{kind}_hash", entry_id=entry_id, path=rel_path)]


def _minimum_negative_case_checks(negative: Mapping[str, Any]) -> Sequence[Dict[str, Any]]:
    coverage = negative.get("minimum_case_coverage")
    if not isinstance(coverage, Mapping):
        return [_failed("negative_minimum_case_coverage_present")]
    expected_cases = list(NEGATIVE_MINIMUM_CASES)
    missing = list(coverage.get("missing_cases") or ())
    covered = sorted(coverage.get("covered_cases") or ())
    checks = [
        _ok("negative_minimum_cases_expected")
        if list(coverage.get("minimum_cases") or ()) == expected_cases
        else _failed("negative_minimum_cases_expected", expected=expected_cases, actual=coverage.get("minimum_cases")),
        _ok("negative_minimum_cases_complete", covered_count=len(covered))
        if not missing
        else _failed("negative_minimum_cases_complete", missing_cases=missing),
    ]
    return checks


def _summary(checks: Sequence[Mapping[str, Any]]) -> Dict[str, Any]:
    failed = [check for check in checks if check.get("status") != "ok"]
    return {
        "total": len(checks),
        "passed": len(checks) - len(failed),
        "failed": len(failed),
        "failed_kinds": sorted({str(check.get("kind")) for check in failed}),
    }


def _ok(kind: str, **details: Any) -> Dict[str, Any]:
    return {"kind": kind, "status": "ok", **details}


def _failed(kind: str, **details: Any) -> Dict[str, Any]:
    return {"kind": kind, "status": "failed", **details}


def _sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def _read_json(path: Path) -> Dict[str, Any]:
    with path.open("r", encoding="utf-8") as handle:
        data = json.load(handle)
    if not isinstance(data, dict):
        raise ValueError(f"expected JSON object: {path}")
    return data


def _write_json(path: Path, payload: Mapping[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")


if __name__ == "__main__":
    raise SystemExit(main())
