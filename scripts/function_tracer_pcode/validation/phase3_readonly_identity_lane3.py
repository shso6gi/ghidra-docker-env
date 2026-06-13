# -*- coding: utf-8 -*-
"""Freeze Phase 3 lane 3 representatives for readonly identity proof work."""

from __future__ import annotations

import argparse
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Dict, Mapping, Optional, Sequence, Tuple

from .result_summary import (
    STATUS_EQ,
    STATUS_TIMEOUT,
    STATUS_UNKNOWN,
    classify_result_payload,
)
from .unknown_reason_summary import (
    _extract_final_unknown_reasons,
    _global_reason_tuple_from_action,
    _global_reason_tuple_from_record,
)
from .phase3_return_width_bridge_lane2 import (
    _canonical_json,
    _canonical_movements,
    _canonical_targets,
    _binary_direction_matches,
    _entry_details,
    _entry_key,
    _entry_map,
    _failed,
    _file_ref,
    _identity_set_check,
    _identity_to_dict,
    _jsonable,
    _normalize_nested_tuple,
    _ok,
    _parse_roots,
    _read_json,
    _records_by_key,
    _sha256_file,
    _structured_node_is_specific,
    _structured_root_is_specific,
    _text_identity_is_specific,
    _write_json,
)
from ..equivalence.unknown_reason import (
    UNKNOWN_TUPLE_MISSING,
    UnknownCountKind,
    build_proof_obligation_id,
    coerce_unknown_recovery_actions,
)


MANIFEST_VERSION = 1
TARGET_REASON_IDS = ("readonly_identity_missing",)
MISSING_SENTINEL = UNKNOWN_TUPLE_MISSING
READONLY_PROOF_KIND = "storage_backed_identity_propagation"
READONLY_PROOF_STAGE = "readonly_operand_identity"
READONLY_EVIDENCE_KIND = "object_storage_identity"
READONLY_REQUIRED_EVIDENCE = (
    "object_storage_identity",
    "count_identity",
    "guard_implication",
    "finite_witness",
)
READONLY_REASON_TUPLE = (
    UnknownCountKind.REASON_RECORD.value,
    "readonly_identity_missing",
    "blocks_equivalence",
    "expression",
    READONLY_PROOF_KIND,
    READONLY_PROOF_STAGE,
    MISSING_SENTINEL,
)
READONLY_ACTION_TUPLE = (
    UnknownCountKind.PROOF_ACTION.value,
    "readonly_identity_missing",
    "blocks_equivalence",
    "expression",
    READONLY_PROOF_KIND,
    READONLY_PROOF_STAGE,
    "planned",
)
COMPLETED_PROOF_BLOCKER_FIELDS = (
    "sat_unsafety_reasons",
    "coverage_gap_reasons",
    "unsupported_effect_reasons",
    "active_unsafety_reasons",
    "active_coverage_gaps",
    "active_coverage_gap_reasons",
    "active_unsupported_effects",
    "unsupported_call_effect_reasons",
    "unsupported_memory_effect_reasons",
)
LOOP_BINARY_NAMES = {
    "B10": "loop_method_b_test-mips64-clang-O1",
    "B13": "loop_method_b_test-mips64-gcc-O0",
}


def _expected_reason_record(movement_id: str) -> Dict[str, Any]:
    return {
        "id": movement_id,
        "count_kind": UnknownCountKind.REASON_RECORD.value,
        "tuple": list(READONLY_REASON_TUPLE),
        "aggregation_unit": "pair",
        "stage": "S_PAIRWISE",
        "pair_or_case": MISSING_SENTINEL,
        "expected_evidence_refs": ["object_storage_identity"],
        "required_object_target_kind": "readonly_identity",
    }


def _expected_proof_action(movement_id: str) -> Dict[str, Any]:
    return {
        "id": movement_id,
        "count_kind": UnknownCountKind.PROOF_ACTION.value,
        "tuple": list(READONLY_ACTION_TUPLE),
        "aggregation_unit": "pair",
        "stage": "S_PAIRWISE",
        "pair_or_case": MISSING_SENTINEL,
        "expected_evidence_refs": ["object_storage_identity"],
        "required_evidence": list(READONLY_REQUIRED_EVIDENCE),
        "required_object_target_kind": "readonly_identity",
        "require_proof_obligation_id": True,
    }


DEFAULT_REPRESENTATIVES: Tuple[Mapping[str, Any], ...] = (
    {
        "id": "representative-readonly-identity-even-index-step2-count-mismatch",
        "category": "loop",
        "function": "lmb_sum_even_index_step2",
        "binary_pair": "B10_B13",
        "expected_observed_binary1_name": LOOP_BINARY_NAMES["B10"],
        "expected_observed_binary2_name": LOOP_BINARY_NAMES["B13"],
        "required_reason_ids": ["readonly_identity_missing"],
        "role": "readonly count identity mismatch requiring storage-backed identity propagation proof",
        "expected_movements": [
            _expected_reason_record("readonly-identity-reason-record"),
            _expected_proof_action("readonly-identity-storage-backed-proof"),
        ],
    },
)


def build_phase3_readonly_identity_lane3_manifest(
    *,
    baseline_raw_dir: Path,
    output_dir: Path,
    current_log_roots: Mapping[str, Path],
    baseline_log_roots: Mapping[str, Path],
    representatives: Sequence[Mapping[str, Any]] = DEFAULT_REPRESENTATIVES,
) -> Path:
    raw_dir = Path(baseline_raw_dir)
    output = Path(output_dir)
    output.mkdir(parents=True, exist_ok=True)
    baseline_manifest = _read_json(raw_dir / "artifact_manifest.json")
    target_keys = tuple(_entry_key(entry) for entry in representatives)
    current_records = _records_by_key(current_log_roots, target_keys=target_keys)
    baseline_records = _records_by_key(baseline_log_roots, target_keys=target_keys)
    entries = [
        _materialize_entry(raw_entry, current_records, baseline_records)
        for raw_entry in representatives
    ]
    readiness = _readiness(entries)
    manifest = {
        "manifest_version": MANIFEST_VERSION,
        "manifest_kind": "phase3_readonly_identity_lane3_representatives",
        "artifact_role": "derived_audit_proof_backlog_gate",
        "baseline_id": baseline_manifest.get("baseline_id") or MISSING_SENTINEL,
        "baseline_git_head": baseline_manifest.get("git_head") or MISSING_SENTINEL,
        "created_at": datetime.now(timezone.utc).isoformat(),
        "target_reason_ids": list(TARGET_REASON_IDS),
        "baseline_raw_artifact_ref": _file_ref(raw_dir / "artifact_manifest.json"),
        "current_log_roots": {
            category: str(path) for category, path in sorted(current_log_roots.items())
        },
        "baseline_log_roots": {
            category: str(path) for category, path in sorted(baseline_log_roots.items())
        },
        "selection_policy": {
            "representative_count": len(entries),
            "criteria": [
                "concrete loop function x binary_pair ids",
                "baseline/current UNKNOWN result",
                "current readonly_identity_missing record preserves final UNKNOWN",
                "current proof action carries raw object_target_key and proof_obligation_id",
                "readonly target is object-derived and excludes diagnostic reason prose",
                "no semantic recovery is accepted before storage-backed identity proof completes",
            ],
        },
        "implementation_manifest": _implementation_manifest(entries),
        "readiness": readiness,
        "phase3_lane3_ready": readiness["ready"],
        "entries": entries,
    }
    path = output / "readonly_identity_lane3_representatives.json"
    _write_json(path, manifest)
    return path


def validate_phase3_readonly_identity_lane3_manifest(manifest: Mapping[str, Any]) -> None:
    readiness = manifest.get("readiness")
    failures = []
    if isinstance(readiness, Mapping):
        failures.extend(str(kind) for kind in readiness.get("failure_kinds") or ())
    else:
        failures.append("readiness_missing")
    if manifest.get("phase3_lane3_ready") is not True:
        failures.append("phase3_lane3_not_ready")
    if manifest.get("phase3_lane3_ready") is False and not failures:
        raise ValueError("Phase 3 lane 3 readiness is false without failure details")
    if failures:
        raise ValueError(f"Phase 3 lane 3 representative manifest is not ready: {', '.join(failures)}")


def build_phase3_readonly_identity_lane3_post_fix_gate(
    *,
    baseline_raw_dir: Path,
    output_dir: Path,
    current_log_roots: Mapping[str, Path],
    baseline_log_roots: Mapping[str, Path],
    phase3_manifest_path: Optional[Path] = None,
    phase3_manifest_sha256: Optional[str] = None,
) -> Path:
    raw_dir = Path(baseline_raw_dir)
    output = Path(output_dir)
    output.mkdir(parents=True, exist_ok=True)
    baseline_manifest = _read_json(raw_dir / "artifact_manifest.json")
    phase3_manifest, phase3_ref = _load_phase3_manifest(
        raw_dir=raw_dir,
        explicit_path=phase3_manifest_path,
    )
    frozen_entries = tuple(phase3_manifest.get("entries") or ())
    target_keys = tuple(_entry_key(entry) for entry in frozen_entries if isinstance(entry, Mapping))
    current_records = _records_by_key(current_log_roots, target_keys=target_keys)
    manifest_checks = _phase3_pre_fix_manifest_checks(
        phase3_manifest=phase3_manifest,
        phase3_manifest_ref=phase3_ref,
        expected_phase3_manifest_sha256=phase3_manifest_sha256,
        frozen_entries=frozen_entries,
    )
    entries = [
        _materialize_post_fix_entry(raw_entry, current_records)
        for raw_entry in frozen_entries
        if isinstance(raw_entry, Mapping)
    ]
    post_fix_gate = _post_fix_regression_gate(
        entries=entries,
        manifest_checks=manifest_checks,
    )
    manifest = {
        "manifest_version": MANIFEST_VERSION,
        "manifest_kind": "phase3_readonly_identity_lane3_post_fix_gate",
        "artifact_role": "derived_audit_post_fix_gate",
        "baseline_id": baseline_manifest.get("baseline_id") or MISSING_SENTINEL,
        "baseline_git_head": baseline_manifest.get("git_head") or MISSING_SENTINEL,
        "created_at": datetime.now(timezone.utc).isoformat(),
        "target_reason_ids": list(TARGET_REASON_IDS),
        "baseline_raw_artifact_ref": _file_ref(raw_dir / "artifact_manifest.json"),
        "phase3_pre_fix_manifest_ref": phase3_ref,
        "current_log_roots": {
            category: str(path) for category, path in sorted(current_log_roots.items())
        },
        "baseline_log_roots": {
            category: str(path) for category, path in sorted(baseline_log_roots.items())
        },
        "post_fix_policy": {
            "unknown_with_pending_proof": "accepted_pending_proof",
            "eq_requires_completed_storage_backed_identity_proof": True,
            "proof_id_source": "pre_fix_manifest_unknown_recovery_actions",
            "reject_eq_with_pending_readonly_identity_reason": True,
            "reject_eq_with_any_readonly_identity_proof_action": True,
        },
        "post_fix_regression_gate": post_fix_gate,
        "phase3_lane3_post_fix_ready": post_fix_gate["ready"],
        "entries": entries,
    }
    path = output / "readonly_identity_lane3_post_fix_gate.json"
    _write_json(path, manifest)
    return path


def validate_phase3_readonly_identity_lane3_post_fix_gate(manifest: Mapping[str, Any]) -> None:
    gate = manifest.get("post_fix_regression_gate")
    failures = []
    if isinstance(gate, Mapping):
        summary = gate.get("summary")
        if isinstance(summary, Mapping):
            failures.extend(str(kind) for kind in summary.get("failed_kinds") or ())
        else:
            failures.append("post_fix_summary_missing")
    else:
        failures.append("post_fix_regression_gate_missing")
    if manifest.get("phase3_lane3_post_fix_ready") is not True:
        failures.append("phase3_lane3_post_fix_not_ready")
    if manifest.get("phase3_lane3_post_fix_ready") is False and not failures:
        raise ValueError("Phase 3 lane 3 post-fix gate is false without failure details")
    if failures:
        raise ValueError(f"Phase 3 lane 3 post-fix gate is not ready: {', '.join(failures)}")


def main(argv: Optional[Sequence[str]] = None) -> int:
    parser = argparse.ArgumentParser(
        description="Build Phase 3 lane 3 readonly identity representative gate.",
    )
    parser.add_argument("--gate-stage", choices=("pre-fix", "post-fix"), default="pre-fix")
    parser.add_argument("--baseline-raw-dir", required=True)
    parser.add_argument("--output-dir", required=True)
    parser.add_argument("--current-log-root", action="append", default=[], metavar="CATEGORY=PATH")
    parser.add_argument("--baseline-log-root", action="append", default=[], metavar="CATEGORY=PATH")
    parser.add_argument("--phase3-manifest", default=None)
    parser.add_argument("--phase3-manifest-sha256", default=None)
    parser.add_argument("--require-ready", action="store_true")
    args = parser.parse_args(argv)
    if args.gate_stage == "post-fix" and not args.phase3_manifest_sha256:
        parser.error("--phase3-manifest-sha256 is required when --gate-stage=post-fix")
    current_roots = _parse_roots(args.current_log_root)
    baseline_roots = _parse_roots(args.baseline_log_root)
    if args.gate_stage == "post-fix":
        path = build_phase3_readonly_identity_lane3_post_fix_gate(
            baseline_raw_dir=Path(args.baseline_raw_dir),
            output_dir=Path(args.output_dir),
            current_log_roots=current_roots,
            baseline_log_roots=baseline_roots,
            phase3_manifest_path=Path(args.phase3_manifest) if args.phase3_manifest else None,
            phase3_manifest_sha256=args.phase3_manifest_sha256,
        )
    else:
        path = build_phase3_readonly_identity_lane3_manifest(
            baseline_raw_dir=Path(args.baseline_raw_dir),
            output_dir=Path(args.output_dir),
            current_log_roots=current_roots,
            baseline_log_roots=baseline_roots,
        )
    if args.require_ready:
        if args.gate_stage == "post-fix":
            validate_phase3_readonly_identity_lane3_post_fix_gate(_read_json(path))
        else:
            validate_phase3_readonly_identity_lane3_manifest(_read_json(path))
    print(path)
    return 0


def _implementation_manifest(entries: Sequence[Mapping[str, Any]]) -> Dict[str, Any]:
    return {
        "lane_id": "phase3_readonly_identity_lane3",
        "lane_reason_ids": list(TARGET_REASON_IDS),
        "proof_completion_gate": {
            "eq_allowed_without_completed_proof": False,
            "pending_proof_keeps_final_result": STATUS_UNKNOWN,
            "completion_required_for_recovery": [READONLY_PROOF_STAGE],
            "required_recovery_actions": [READONLY_PROOF_STAGE],
        },
        "expected_movement_entries": [
            {
                "id": entry.get("id"),
                "category": entry.get("category"),
                "function": entry.get("function"),
                "binary_pair": entry.get("binary_pair"),
                "expected_movements": entry.get("expected_movements") or (),
                "expected_readonly_identity_targets": _canonical_targets(
                    _current_targets(entry)
                ),
                "required_completion_actions": _canonical_actions(
                    _current_readonly_actions(entry)
                ),
            }
            for entry in entries
        ],
    }


def _readiness(entries: Sequence[Mapping[str, Any]]) -> Dict[str, Any]:
    checks: list[Dict[str, Any]] = []
    checks.append(_identity_set_check("phase3_lane3_entries_exact_set", DEFAULT_REPRESENTATIVES, entries))
    for entry in entries:
        checks.extend(_entry_readiness_checks(entry))
    failed = [check for check in checks if check.get("status") == "failed"]
    return {
        "ready": not failed,
        "summary": {
            "total": len(checks),
            "passed": sum(1 for check in checks if check.get("status") == "ok"),
            "failed": len(failed),
            "failed_kinds": sorted({str(check.get("kind")) for check in failed}),
        },
        "failure_kinds": sorted({str(check.get("kind")) for check in failed}),
        "checks": checks,
    }


def _entry_readiness_checks(entry: Mapping[str, Any]) -> Sequence[Dict[str, Any]]:
    checks: list[Dict[str, Any]] = []
    details = _entry_details(entry)
    baseline = entry.get("baseline_observation") if isinstance(entry.get("baseline_observation"), Mapping) else {}
    current = entry.get("current_observation") if isinstance(entry.get("current_observation"), Mapping) else {}
    checks.append(
        _ok("readonly_identity_baseline_unknown", **details)
        if baseline.get("final_result") == STATUS_UNKNOWN
        else _failed(
            "readonly_identity_baseline_unknown",
            current_result=baseline.get("final_result", MISSING_SENTINEL),
            **details,
        )
    )
    checks.append(
        _ok("readonly_identity_current_unknown", **details)
        if current.get("final_result") == STATUS_UNKNOWN
        else _failed(
            "readonly_identity_current_unknown",
            current_result=current.get("final_result", MISSING_SENTINEL),
            **details,
        )
    )
    checks.append(
        _ok("readonly_identity_binary_direction", **details)
        if _binary_direction_matches(entry, current)
        else _failed(
            "readonly_identity_binary_direction",
            observed_binary1_name=current.get("observed_binary1_name", MISSING_SENTINEL),
            observed_binary2_name=current.get("observed_binary2_name", MISSING_SENTINEL),
            **details,
        )
    )
    current_targets = _current_targets(entry)
    checks.append(
        _ok("readonly_identity_current_targets_present", count=len(current_targets), **details)
        if current_targets
        else _failed("readonly_identity_current_targets_present", count=0, **details)
    )
    checks.append(
        _ok(
            "readonly_identity_current_actions_complete",
            count=len(_current_readonly_actions(entry)),
            target_count=len(current_targets),
            **details,
        )
        if current_targets and not _missing_readonly_actions(entry)
        else _failed(
            "readonly_identity_current_actions_complete",
            missing=_missing_readonly_actions(entry),
            **details,
        )
    )
    checks.append(
        _ok("readonly_identity_expected_movements_match_definition", **details)
        if _canonical_movements(entry.get("expected_movements"))
        == _canonical_movements(_expected_entry_for(entry).get("expected_movements"))
        else _failed(
            "readonly_identity_expected_movements_match_definition",
            expected=_canonical_movements(_expected_entry_for(entry).get("expected_movements")),
            actual=_canonical_movements(entry.get("expected_movements")),
            **details,
        )
    )
    return checks


def _phase3_pre_fix_manifest_checks(
    *,
    phase3_manifest: Mapping[str, Any],
    phase3_manifest_ref: Mapping[str, Any],
    expected_phase3_manifest_sha256: Optional[str],
    frozen_entries: Sequence[Any],
) -> Sequence[Dict[str, Any]]:
    checks: list[Dict[str, Any]] = []
    checks.append(
        _ok("phase3_pre_fix_manifest_available", phase3_manifest_ref=dict(phase3_manifest_ref))
        if phase3_manifest_ref.get("sha256") != "__missing__"
        else _failed("phase3_pre_fix_manifest_available", phase3_manifest_ref=dict(phase3_manifest_ref))
    )
    if expected_phase3_manifest_sha256 is None:
        checks.append(
            _failed(
                "phase3_pre_fix_manifest_sha256_required",
                actual_sha256=phase3_manifest_ref.get("sha256") or MISSING_SENTINEL,
            )
        )
    else:
        actual_sha256 = phase3_manifest_ref.get("sha256")
        checks.append(
            _ok("phase3_pre_fix_manifest_sha256", sha256=actual_sha256)
            if actual_sha256 == expected_phase3_manifest_sha256
            else _failed(
                "phase3_pre_fix_manifest_sha256",
                expected_sha256=expected_phase3_manifest_sha256,
                actual_sha256=actual_sha256 or MISSING_SENTINEL,
            )
        )
    checks.append(
        _ok("phase3_pre_fix_manifest_kind")
        if phase3_manifest.get("manifest_kind") == "phase3_readonly_identity_lane3_representatives"
        else _failed(
            "phase3_pre_fix_manifest_kind",
            manifest_kind=phase3_manifest.get("manifest_kind", MISSING_SENTINEL),
        )
    )
    try:
        validate_phase3_readonly_identity_lane3_manifest(phase3_manifest)
    except ValueError as exc:
        checks.append(_failed("phase3_pre_fix_manifest_ready", error=str(exc)))
    else:
        checks.append(_ok("phase3_pre_fix_manifest_ready"))
    checks.append(
        _ok("phase3_pre_fix_entries_non_empty", count=len(frozen_entries))
        if frozen_entries
        else _failed("phase3_pre_fix_entries_non_empty", count=0)
    )
    checks.append(_identity_set_check("phase3_pre_fix_entries_exact_set", DEFAULT_REPRESENTATIVES, frozen_entries))
    implementation = phase3_manifest.get("implementation_manifest")
    implementation_entries = ()
    if isinstance(implementation, Mapping):
        checks.append(_ok("phase3_pre_fix_implementation_manifest_available"))
        implementation_entries = implementation.get("expected_movement_entries") or ()
    else:
        checks.append(_failed("phase3_pre_fix_implementation_manifest_available"))
    checks.append(
        _identity_set_check(
            "phase3_pre_fix_implementation_entries_consistent",
            implementation_entries,
            frozen_entries,
        )
    )
    checks.extend(
        _pre_fix_entry_content_checks(
            frozen_entries=frozen_entries,
            implementation_entries=implementation_entries,
        )
    )
    return checks


def _pre_fix_entry_content_checks(
    *,
    frozen_entries: Sequence[Any],
    implementation_entries: Any,
) -> Sequence[Dict[str, Any]]:
    checks: list[Dict[str, Any]] = []
    expected_map = _entry_map(DEFAULT_REPRESENTATIVES)
    actual_map = _entry_map(frozen_entries)
    implementation_map = _entry_map(implementation_entries)
    for identity, expected_entry in sorted(expected_map.items()):
        actual = actual_map.get(identity)
        implementation = implementation_map.get(identity)
        details = {"entry": _identity_to_dict(identity)}
        expected_movements = _canonical_movements(expected_entry.get("expected_movements"))
        actual_movements = _canonical_movements(actual.get("expected_movements") if isinstance(actual, Mapping) else None)
        impl_movements = _canonical_movements(implementation.get("expected_movements") if isinstance(implementation, Mapping) else None)
        checks.append(
            _ok("phase3_pre_fix_entry_expected_movements_match_definition", **details)
            if actual_movements == expected_movements
            else _failed(
                "phase3_pre_fix_entry_expected_movements_match_definition",
                expected=expected_movements,
                actual=actual_movements,
                **details,
            )
        )
        checks.append(
            _ok("phase3_pre_fix_implementation_expected_movements_match_definition", **details)
            if impl_movements == expected_movements
            else _failed(
                "phase3_pre_fix_implementation_expected_movements_match_definition",
                expected=expected_movements,
                actual=impl_movements,
                **details,
            )
        )
        actual_targets = _canonical_targets(_current_targets(actual)) if isinstance(actual, Mapping) else ()
        impl_targets = _canonical_targets(
            implementation.get("expected_readonly_identity_targets")
            if isinstance(implementation, Mapping)
            else None
        )
        checks.append(
            _ok("phase3_pre_fix_entry_targets_match_implementation", **details)
            if actual_targets and actual_targets == impl_targets
            else _failed(
                "phase3_pre_fix_entry_targets_match_implementation",
                expected=impl_targets,
                actual=actual_targets,
                **details,
            )
        )
        actual_actions = _canonical_actions(_current_readonly_actions(actual)) if isinstance(actual, Mapping) else ()
        impl_actions = _canonical_actions(
            implementation.get("required_completion_actions")
            if isinstance(implementation, Mapping)
            else None
        )
        checks.append(
            _ok("phase3_pre_fix_entry_actions_match_implementation", **details)
            if actual_actions and actual_actions == impl_actions
            else _failed(
                "phase3_pre_fix_entry_actions_match_implementation",
                expected=impl_actions,
                actual=actual_actions,
                **details,
            )
        )
    return checks


def _post_fix_regression_gate(
    *,
    entries: Sequence[Mapping[str, Any]],
    manifest_checks: Sequence[Mapping[str, Any]],
) -> Dict[str, Any]:
    checks: list[Dict[str, Any]] = [dict(check) for check in manifest_checks]
    for entry in entries:
        checks.append(
            _ok(
                "readonly_identity_post_fix_expected_movement",
                entry_id=entry.get("id"),
                function=entry.get("function"),
                binary_pair=entry.get("binary_pair"),
                post_fix_status=entry.get("post_fix_status"),
            )
            if entry.get("post_fix_status") in {"pending_proof", "completed_recovery"}
            else _failed(
                "readonly_identity_post_fix_expected_movement",
                entry_id=entry.get("id"),
                function=entry.get("function"),
                binary_pair=entry.get("binary_pair"),
                failures=entry.get("post_fix_failures") or (),
                current_result=(entry.get("current_observation") or {}).get("final_result"),
            )
        )
    failed = [check for check in checks if check.get("status") == "failed"]
    return {
        "gate_kind": "phase3_readonly_identity_lane3_post_fix_regression",
        "baseline_mode": "pending_proof_or_completed_proof_against_pre_fix_manifest",
        "ready": not failed,
        "summary": {
            "total": len(checks),
            "passed": sum(1 for check in checks if check.get("status") == "ok"),
            "failed": len(failed),
            "failed_kinds": sorted({str(check.get("kind")) for check in failed}),
            "locked_gates": [
                "phase3_pre_fix_manifest_sha256",
                "readonly_identity_object_target_key",
                "readonly_identity_proof_obligation_id",
                "storage_backed_identity_proof_required_before_eq",
                "no_pending_proof_gate_on_eq",
                "no_unresolved_readonly_identity_proof_action_on_eq",
            ],
        },
        "checks": checks,
    }


def _materialize_entry(
    raw_entry: Mapping[str, Any],
    current_records: Mapping[Tuple[str, str, str], Mapping[str, Any]],
    baseline_records: Mapping[Tuple[str, str, str], Mapping[str, Any]],
) -> Dict[str, Any]:
    entry = dict(raw_entry)
    key = _entry_key(raw_entry)
    entry["baseline_observation"] = _observation(raw_entry, baseline_records.get(key))
    entry["current_observation"] = _observation(raw_entry, current_records.get(key))
    entry["target_object_keys"] = _canonical_targets(_current_targets(entry))
    entry["required_completion_actions"] = _canonical_actions(_current_readonly_actions(entry))
    return entry


def _materialize_post_fix_entry(
    frozen_entry: Mapping[str, Any],
    current_records: Mapping[Tuple[str, str, str], Mapping[str, Any]],
) -> Dict[str, Any]:
    entry = dict(frozen_entry)
    key = _entry_key(frozen_entry)
    entry["current_observation"] = _observation(frozen_entry, current_records.get(key))
    status, failures = _post_fix_status(entry)
    entry["post_fix_status"] = status
    entry["post_fix_failures"] = failures
    entry["pending_proof_obligations"] = (
        _pending_proof_obligations(entry) if status == "pending_proof" else []
    )
    return entry


def _post_fix_status(entry: Mapping[str, Any]) -> Tuple[str, Sequence[Dict[str, Any]]]:
    failures: list[Dict[str, Any]] = []
    current = entry.get("current_observation") if isinstance(entry.get("current_observation"), Mapping) else {}
    result = current.get("final_result")
    details = _entry_details(entry)
    if result == STATUS_TIMEOUT:
        failures.append(_failed("readonly_identity_timeout_regression", **details))
        return "failed", failures
    if result == STATUS_EQ:
        failures.extend(_completed_recovery_failures(entry, current))
        if failures:
            return "failed", failures
        return "completed_recovery", ()
    if result != STATUS_UNKNOWN:
        failures.append(
            _failed(
                "readonly_identity_unexpected_final_result",
                current_result=result or MISSING_SENTINEL,
                **details,
            )
        )
        return "failed", failures
    frozen_targets = _canonical_targets(entry.get("target_object_keys"))
    current_targets = _canonical_targets(_current_targets(entry))
    if not frozen_targets or current_targets != frozen_targets:
        failures.append(
            _failed(
                "readonly_identity_target_set_changed",
                expected=frozen_targets,
                actual=current_targets,
                **details,
            )
        )
    frozen_actions = _canonical_actions(entry.get("required_completion_actions"))
    current_actions = _canonical_actions(_current_readonly_actions(entry))
    if not frozen_actions or current_actions != frozen_actions:
        failures.append(
            _failed(
                "readonly_identity_required_actions_changed",
                expected=frozen_actions,
                actual=current_actions,
                **details,
            )
        )
    missing = _missing_readonly_actions(entry)
    if missing:
        failures.append(_failed("readonly_identity_current_actions_complete", missing=missing, **details))
    if failures:
        return "failed", failures
    return "pending_proof", ()


def _observation(
    entry: Mapping[str, Any],
    record: Optional[Mapping[str, Any]],
) -> Dict[str, Any]:
    if record is None:
        return {
            "log_status": "missing",
            "final_result": "MISSING",
            "observed_reason_ids": [],
            "reason_records": [],
            "proof_actions": [],
            "reason_record_tuples": [],
            "proof_action_tuples": [],
        }
    payload = record.get("payload") if isinstance(record.get("payload"), Mapping) else {}
    reasons = _extract_final_unknown_reasons(payload)
    raw_actions = payload.get("unknown_recovery_actions")
    if not isinstance(raw_actions, Sequence) or isinstance(raw_actions, (str, bytes)):
        raw_actions = ()
    actions = coerce_unknown_recovery_actions(raw_actions)
    return {
        "log_status": "present",
        "log_path": record.get("relative_log_path") or MISSING_SENTINEL,
        "log_sha256": record.get("log_sha256") or MISSING_SENTINEL,
        "final_result": classify_result_payload(payload),
        "observed_function1_name": payload.get("function1_name") or MISSING_SENTINEL,
        "observed_function2_name": payload.get("function2_name") or MISSING_SENTINEL,
        "observed_binary1_name": payload.get("binary1_name") or MISSING_SENTINEL,
        "observed_binary2_name": payload.get("binary2_name") or MISSING_SENTINEL,
        "observed_left_binary_id": record.get("observed_left_binary_id") or MISSING_SENTINEL,
        "observed_right_binary_id": record.get("observed_right_binary_id") or MISSING_SENTINEL,
        "observed_reason_ids": sorted({reason.reason_id for reason in reasons}),
        "decision_gated_by_pending_proof": bool(payload.get("decision_gated_by_pending_proof")),
        "completed_recovery_proof_evidence": _completed_recovery_proof_summaries(payload),
        "reason_record_tuples": [
            list(_global_reason_tuple_from_record(reason, UnknownCountKind.REASON_RECORD.value))
            for reason in reasons
        ],
        "proof_action_tuples": [
            list(_global_reason_tuple_from_action(action))
            for action in actions
        ],
        "reason_records": [_reason_to_dict(reason) for reason in reasons],
        "proof_actions": [
            _action_to_dict(action, raw_actions[index] if index < len(raw_actions) else None)
            for index, action in enumerate(actions)
        ],
    }


def _reason_to_dict(reason: Any) -> Dict[str, Any]:
    return {
        "count_kind": reason.count_kind,
        "reason_id": reason.reason_id,
        "decision_effect": reason.decision_effect,
        "reason_scope": reason.reason_scope,
        "aggregation_unit": reason.aggregation_unit,
        "stage": reason.stage,
        "pair_or_case": reason.pair_or_case,
        "recovery_proof_kind": reason.recovery_proof_kind,
        "proof_stage": reason.proof_stage,
        "evidence_kind": reason.evidence_kind,
        "object_target_key": _jsonable(reason.object_target_key),
        "proof_obligation_id": _jsonable(reason.proof_obligation_id),
        "action_status": reason.action_status,
        "tuple": list(_global_reason_tuple_from_record(reason, UnknownCountKind.REASON_RECORD.value)),
    }


def _action_to_dict(action: Any, raw_action: Any) -> Dict[str, Any]:
    raw_has_proof_id = (
        isinstance(raw_action, Mapping)
        and "proof_obligation_id" in raw_action
        and raw_action.get("proof_obligation_id") is not None
    )
    raw_has_target = (
        isinstance(raw_action, Mapping)
        and "object_target_key" in raw_action
        and raw_action.get("object_target_key") is not None
    )
    return {
        "count_kind": action.count_kind,
        "reason_id": action.reason_id,
        "decision_effect": action.decision_effect,
        "reason_scope": action.reason_scope,
        "aggregation_unit": action.aggregation_unit,
        "stage": action.stage,
        "pair_or_case": action.pair_or_case,
        "proof_kind": action.proof_kind,
        "proof_stage": action.proof_stage,
        "status": action.status,
        "required_evidence": list(action.required_evidence or ()),
        "evidence_kind": action.evidence_kind,
        "object_target_key": _jsonable(action.object_target_key),
        "proof_obligation_id": _jsonable(action.proof_obligation_id),
        "raw_object_target_key_present": raw_has_target,
        "raw_proof_obligation_id_present": raw_has_proof_id,
        "tuple": list(_global_reason_tuple_from_action(action)),
    }


def _current_targets(entry: Any) -> Sequence[Any]:
    if not isinstance(entry, Mapping):
        return ()
    current = entry.get("current_observation")
    if not isinstance(current, Mapping):
        return ()
    targets = []
    for record in current.get("reason_records") or ():
        if not isinstance(record, Mapping):
            continue
        if record.get("reason_id") != "readonly_identity_missing":
            continue
        target = record.get("object_target_key")
        if _object_target_key_is_specific_readonly_identity(target):
            targets.append(target)
    return tuple(targets)


def _current_readonly_actions(entry: Any) -> Sequence[Mapping[str, Any]]:
    if not isinstance(entry, Mapping):
        return ()
    current = entry.get("current_observation")
    if not isinstance(current, Mapping):
        return ()
    actions = []
    for action in current.get("proof_actions") or ():
        if not isinstance(action, Mapping):
            continue
        if action.get("reason_id") != "readonly_identity_missing":
            continue
        if action.get("proof_kind") != READONLY_PROOF_KIND:
            continue
        if action.get("proof_stage") != READONLY_PROOF_STAGE:
            continue
        if not _object_target_key_is_specific_readonly_identity(action.get("object_target_key")):
            continue
        if action.get("proof_obligation_id") is None:
            continue
        if action.get("raw_proof_obligation_id_present") is not True:
            continue
        if action.get("raw_object_target_key_present") is not True:
            continue
        if not _proof_action_has_expected_id(action):
            continue
        if not _proof_action_matches_lane_definition(action):
            continue
        actions.append(action)
    return tuple(actions)


def _missing_readonly_actions(entry: Mapping[str, Any]) -> Sequence[Dict[str, Any]]:
    current_targets = _canonical_targets(_current_targets(entry))
    actions = _current_readonly_actions(entry)
    action_keys = {
        (
            _canonical_json(action.get("object_target_key")),
            action.get("proof_kind"),
            action.get("proof_stage"),
        )
        for action in actions
    }
    missing = []
    for target in current_targets:
        target_json = _canonical_json(target)
        key = (target_json, READONLY_PROOF_KIND, READONLY_PROOF_STAGE)
        if key not in action_keys:
            missing.append(
                {
                    "object_target_key": target,
                    "proof_kind": READONLY_PROOF_KIND,
                    "proof_stage": READONLY_PROOF_STAGE,
                }
            )
    return missing


def _completed_recovery_failures(
    entry: Mapping[str, Any],
    current: Mapping[str, Any],
) -> Sequence[Dict[str, Any]]:
    failures: list[Dict[str, Any]] = []
    details = _entry_details(entry)
    if current.get("decision_gated_by_pending_proof") is True:
        failures.append(_failed("readonly_identity_decision_gated_by_pending_proof", **details))
    active_reasons = [
        reason_id
        for reason_id in current.get("observed_reason_ids") or ()
        if _text_identity_is_specific(reason_id)
    ]
    if active_reasons:
        failures.append(
            _failed(
                "readonly_identity_active_reason_not_cleared",
                active_reason_ids=active_reasons,
                **details,
            )
        )
    pending_actions = [
        action
        for action in current.get("proof_actions") or ()
        if isinstance(action, Mapping)
    ]
    if pending_actions:
        failures.append(_failed("readonly_identity_pending_proof_action_still_active", **details))
    required_actions = _canonical_actions(entry.get("required_completion_actions"))
    if not required_actions:
        failures.append(_failed("readonly_identity_frozen_proof_actions_missing", **details))
        return failures
    completed = tuple(current.get("completed_recovery_proof_evidence") or ())
    if not completed:
        failures.append(_failed("readonly_identity_completed_proof_required", **details))
        return failures
    for action in required_actions:
        if not any(_completed_evidence_matches_action(evidence, action) for evidence in completed):
            failures.append(
                _failed(
                    "readonly_identity_completed_proof_required",
                    proof_stage=action.get("proof_stage") or MISSING_SENTINEL,
                    evidence_kind=action.get("evidence_kind") or MISSING_SENTINEL,
                    proof_kind=action.get("proof_kind") or MISSING_SENTINEL,
                    **details,
                )
            )
    return failures


def _pending_proof_obligations(entry: Mapping[str, Any]) -> Sequence[Dict[str, Any]]:
    current = entry.get("current_observation") if isinstance(entry.get("current_observation"), Mapping) else {}
    completed = tuple(current.get("completed_recovery_proof_evidence") or ())
    obligations = []
    for action in _canonical_actions(entry.get("required_completion_actions")):
        has_completed_evidence = any(
            _completed_evidence_matches_action(evidence, action)
            for evidence in completed
        )
        obligations.append(
            {
                "reason_id": action.get("reason_id") or MISSING_SENTINEL,
                "proof_kind": action.get("proof_kind") or MISSING_SENTINEL,
                "proof_stage": action.get("proof_stage") or MISSING_SENTINEL,
                "evidence_kind": action.get("evidence_kind") or MISSING_SENTINEL,
                "required_evidence": list(action.get("required_evidence") or ()),
                "proof_obligation_id": _jsonable(action.get("proof_obligation_id")),
                "completed_evidence_present": has_completed_evidence,
                "status": "completed_evidence_present" if has_completed_evidence else "pending_evidence",
            }
        )
    return obligations


def _completed_evidence_matches_action(
    evidence_summary: Mapping[str, Any],
    action: Mapping[str, Any],
) -> bool:
    if not isinstance(evidence_summary, Mapping):
        return False
    evidence = evidence_summary.get("evidence")
    if not isinstance(evidence, Mapping):
        evidence = evidence_summary
    if evidence_summary.get("object_derived") is not True and evidence.get("object_derived") is not True:
        return False
    if str(evidence_summary.get("status") or evidence.get("status") or "") not in {
        "complete",
        "completed",
        "proven",
    }:
        return False
    object_target_key = _normalize_nested_tuple(
        evidence_summary.get("object_target_key") or evidence.get("object_target_key")
    )
    if not _object_target_key_is_specific_readonly_identity(object_target_key):
        return False
    if (
        str(evidence_summary.get("reason_id") or evidence.get("reason_id") or MISSING_SENTINEL)
        != str(action.get("reason_id") or MISSING_SENTINEL)
        or str(evidence_summary.get("proof_stage") or evidence.get("proof_stage") or MISSING_SENTINEL)
        != str(action.get("proof_stage") or MISSING_SENTINEL)
        or str(evidence_summary.get("proof_kind") or evidence.get("proof_kind") or MISSING_SENTINEL)
        != str(action.get("proof_kind") or MISSING_SENTINEL)
        or str(evidence_summary.get("evidence_kind") or evidence.get("evidence_kind") or MISSING_SENTINEL)
        != str(action.get("evidence_kind") or MISSING_SENTINEL)
    ):
        return False
    if _completed_evidence_has_active_blocker(evidence):
        return False
    if not _completed_evidence_has_required_proof_content(evidence_summary, evidence, action, object_target_key):
        return False
    expected_id = _expected_proof_obligation_id(action, object_target_key=object_target_key)
    provided_id = _normalize_nested_tuple(
        evidence_summary.get("proof_obligation_id") or evidence.get("proof_obligation_id")
    )
    return (
        provided_id == expected_id
        and object_target_key == _normalize_nested_tuple(action.get("object_target_key"))
        and expected_id == _normalize_nested_tuple(action.get("proof_obligation_id"))
    )


def _completed_evidence_has_required_proof_content(
    evidence_summary: Mapping[str, Any],
    evidence: Mapping[str, Any],
    action: Mapping[str, Any],
    object_target_key: Any,
) -> bool:
    actual_required = tuple(
        str(item)
        for item in (
            evidence_summary.get("required_evidence")
            or evidence.get("required_evidence")
            or ()
        )
    )
    if actual_required != READONLY_REQUIRED_EVIDENCE:
        return False
    content = _completed_proof_content(evidence_summary, evidence)
    if not isinstance(content, Mapping):
        return False
    if _nested_completed_proof_has_active_blocker(content):
        return False
    return _storage_backed_identity_proof_content_is_specific(content, object_target_key)


def _completed_proof_content(evidence_summary: Mapping[str, Any], evidence: Mapping[str, Any]) -> Any:
    for container in (evidence_summary, evidence):
        for field_name in ("proof_content", "proof", "proof_evidence"):
            content = container.get(field_name)
            if isinstance(content, Mapping):
                if READONLY_PROOF_KIND in content and isinstance(content[READONLY_PROOF_KIND], Mapping):
                    return content[READONLY_PROOF_KIND]
                return content
    return None


def _storage_backed_identity_proof_content_is_specific(content: Mapping[str, Any], object_target_key: Any) -> bool:
    target = _normalize_nested_tuple(object_target_key)
    left = _readonly_side(target, "left")
    right = _readonly_side(target, "right")
    if not (
        content.get("object_derived") is True
        and _normalize_nested_tuple(content.get("object_target_key")) == target
        and _normalize_nested_tuple(content.get("left_side")) == left
        and _normalize_nested_tuple(content.get("right_side")) == right
        and content.get("object_storage_identity") == "matched"
        and content.get("count_identity") == "matched"
        and content.get("guard_implication") in {"proven", "vacuous"}
        and content.get("finite_witness") == "checked"
    ):
        return False
    storage_relation = _readonly_storage_relation_from_target(target)
    if storage_relation is None:
        return False
    if storage_relation[0] == "same_register_base_projection":
        if _normalize_nested_tuple(content.get("storage_relation")) != storage_relation:
            return False
        return _readonly_projection_extension_proof_content_is_specific(
            content.get("parameter_extension"),
            storage_relation,
        )
    return True


def _readonly_storage_relation_from_target(object_target_key: Any) -> Any:
    target = _normalize_nested_tuple(object_target_key)
    if not isinstance(target, tuple) or len(target) != 5:
        return None
    relation = _normalize_nested_tuple(target[4])
    if not isinstance(relation, tuple) or len(relation) != 3:
        return None
    storage = _normalize_nested_tuple(relation[2])
    if not isinstance(storage, tuple) or len(storage) != 2 or storage[0] != "count_storage_relation":
        return None
    storage_relation = _normalize_nested_tuple(storage[1])
    return storage_relation if isinstance(storage_relation, tuple) else None


def _readonly_projection_extension_proof_content_is_specific(extension: Any, storage_relation: Any) -> bool:
    if not isinstance(extension, Mapping):
        return False
    if extension.get("object_derived") is not True or extension.get("status") != "proven":
        return False
    if extension.get("relation") != "same_register_base_projection_semantic_extension":
        return False
    if _normalize_nested_tuple(extension.get("projection_relation")) != storage_relation:
        return False
    if extension.get("wide_side") not in {"left", "right"} or extension.get("narrow_side") not in {"left", "right"}:
        return False
    if extension.get("wide_side") == extension.get("narrow_side"):
        return False
    if extension.get("signedness") not in {"signed", "unsigned"}:
        return False
    if extension.get("extension") not in {"sign_extend", "zero_extend"}:
        return False
    if (extension.get("signedness") == "signed") != (extension.get("extension") == "sign_extend"):
        return False
    try:
        narrow_bits = int(extension.get("narrow_bits"))
        wide_bits = int(extension.get("wide_bits"))
        parameter_index = int(extension.get("parameter_index"))
    except (TypeError, ValueError):
        return False
    if parameter_index < 0 or narrow_bits <= 0 or wide_bits <= narrow_bits:
        return False
    relation_spans = {
        item[0]: item
        for item in storage_relation
        if isinstance(item, tuple) and len(item) == 3 and item[0] in {"left_bits", "right_bits"}
    }
    left_span = relation_spans.get("left_bits")
    right_span = relation_spans.get("right_bits")
    if left_span is None or right_span is None:
        return False
    try:
        left_size = int(left_span[2])
        right_size = int(right_span[2])
    except (TypeError, ValueError):
        return False
    expected_wide_side = "left" if left_size > right_size else "right"
    expected_narrow_side = "right" if expected_wide_side == "left" else "left"
    return (
        extension.get("wide_side") == expected_wide_side
        and extension.get("narrow_side") == expected_narrow_side
        and max(left_size, right_size) == wide_bits
        and min(left_size, right_size) == narrow_bits
        and extension.get("proof_source")
        in {"param_semantic_hint", "declared_parameter_narrow_type_on_wide_storage"}
    )


def _completed_evidence_has_active_blocker(evidence: Mapping[str, Any]) -> bool:
    for field_name in COMPLETED_PROOF_BLOCKER_FIELDS:
        if evidence.get(field_name):
            return True
    return False


def _nested_completed_proof_has_active_blocker(value: Any) -> bool:
    if isinstance(value, Mapping):
        for field_name in COMPLETED_PROOF_BLOCKER_FIELDS:
            if value.get(field_name):
                return True
        return any(_nested_completed_proof_has_active_blocker(item) for item in value.values())
    if isinstance(value, Sequence) and not isinstance(value, (str, bytes)):
        return any(_nested_completed_proof_has_active_blocker(item) for item in value)
    return False


def _completed_recovery_proof_summaries(payload: Mapping[str, Any]) -> Sequence[Dict[str, Any]]:
    raw_items = payload.get("completed_recovery_proof_evidence") or ()
    if not isinstance(raw_items, Sequence) or isinstance(raw_items, (str, bytes)):
        return ()
    summaries = []
    for raw_item in raw_items:
        if not isinstance(raw_item, Mapping):
            continue
        wrapper = raw_item
        evidence = raw_item.get("evidence")
        if not isinstance(evidence, Mapping):
            evidence = raw_item
        summaries.append(
            {
                "status": evidence.get("status") or wrapper.get("status") or MISSING_SENTINEL,
                "reason_id": evidence.get("reason_id") or wrapper.get("reason_id") or MISSING_SENTINEL,
                "proof_kind": evidence.get("proof_kind") or wrapper.get("proof_kind") or MISSING_SENTINEL,
                "proof_stage": evidence.get("proof_stage") or wrapper.get("proof_stage") or MISSING_SENTINEL,
                "evidence_kind": evidence.get("evidence_kind") or wrapper.get("evidence_kind") or MISSING_SENTINEL,
                "required_evidence": list(evidence.get("required_evidence") or wrapper.get("required_evidence") or ()),
                "object_derived": bool(evidence.get("object_derived") or wrapper.get("object_derived")),
                "object_target_key": _jsonable(
                    evidence.get("object_target_key") or wrapper.get("object_target_key")
                ),
                "proof_obligation_id": _jsonable(
                    evidence.get("proof_obligation_id") or wrapper.get("proof_obligation_id")
                ),
                "evidence": _jsonable(evidence),
            }
        )
    return tuple(summaries)


def _object_target_key_is_specific_readonly_identity(value: Any) -> bool:
    target = _normalize_nested_tuple(value)
    if not isinstance(target, tuple) or len(target) != 5 or target[0] != "readonly_identity":
        return False
    pair = target[1]
    if not (
        isinstance(pair, tuple)
        and len(pair) == 2
        and pair[0] == "pair"
        and _text_identity_is_specific(pair[1])
    ):
        return False
    if _nested_contains_diagnostic_reason(target):
        return False
    sides_are_specific = _readonly_side_is_specific(target[2], "left") and _readonly_side_is_specific(target[3], "right")
    return sides_are_specific and _readonly_identity_relation_is_specific(target[4])


def _readonly_identity_relation_is_specific(value: Any) -> bool:
    relation = _normalize_nested_tuple(value)
    if not isinstance(relation, tuple) or len(relation) != 3 or relation[0] != "readonly_identity_relation":
        return False
    shared = relation[1]
    storage = relation[2]
    return (
        isinstance(shared, tuple)
        and len(shared) == 2
        and shared[0] == "shared_count_identities"
        and isinstance(shared[1], tuple)
        and all(_readonly_component_key_is_specific(item) for item in shared[1])
        and isinstance(storage, tuple)
        and len(storage) == 2
        and storage[0] == "count_storage_relation"
        and _readonly_storage_relation_is_specific(storage[1])
    )


def _readonly_storage_relation_is_specific(value: Any) -> bool:
    relation = _normalize_nested_tuple(value)
    if not isinstance(relation, tuple) or not relation or not _text_identity_is_specific(relation[0]):
        return False
    kind = relation[0]
    if kind == "same_storage_identity":
        return len(relation) == 2 and _readonly_component_key_is_specific(relation[1])
    if kind in {"missing_storage_identity", "different_storage_identity", "different_register_base"}:
        return (
            len(relation) == 3
            and all(item is None or _readonly_component_key_is_specific(item) for item in relation[1:])
        )
    if kind == "same_register_base_projection":
        return (
            len(relation) == 5
            and _tag_payload_specific(relation[1], "base")
            and _readonly_bit_span_is_specific(relation[2], "left_bits")
            and _readonly_bit_span_is_specific(relation[3], "right_bits")
            and isinstance(relation[4], tuple)
            and len(relation[4]) == 2
            and relation[4][0] == "projection"
            and _text_identity_is_specific(relation[4][1])
        )
    return False


def _readonly_bit_span_is_specific(value: Any, tag: str) -> bool:
    span = _normalize_nested_tuple(value)
    return (
        isinstance(span, tuple)
        and len(span) == 3
        and span[0] == tag
        and _nonnegative_int_like(span[1])
        and _positive_int_like(span[2])
    )


def _readonly_side_is_specific(value: Any, expected_side: str) -> bool:
    side = _normalize_nested_tuple(value)
    if not isinstance(side, tuple) or len(side) != 7:
        return False
    if side[0] != "readonly_identity_side" or side[1] != expected_side:
        return False
    function_ref = side[2]
    return (
        _analysis_entry_key_is_specific(function_ref)
        and _readonly_return_case_member_is_specific(side[3])
        and _readonly_reduction_ref_is_specific(side[4])
        and _guards_key_is_specific(side[5], allow_empty=True)
        and _readonly_value_entry_is_specific(side[6])
    )


def _analysis_entry_key_is_specific(value: Any) -> bool:
    normalized = _normalize_nested_tuple(value)
    if not isinstance(normalized, tuple) or not normalized:
        return False
    if normalized[0] == "function_ref":
        return len(normalized) == 2 and _function_ref_payload_is_specific(normalized[1])
    if normalized[0] == "entry_point":
        return len(normalized) == 2 and _text_identity_is_specific(normalized[1])
    return False


def _function_ref_payload_is_specific(value: Any) -> bool:
    normalized = _normalize_nested_tuple(value)
    if not isinstance(normalized, tuple) or len(normalized) < 3:
        return False
    kind, binary_id, entry_offset = normalized[:3]
    if kind not in {"function", "code_address"}:
        return False
    return _text_identity_is_specific(binary_id) and _nonnegative_int_like(entry_offset)


def _readonly_return_case_member_is_specific(value: Any) -> bool:
    member = _normalize_nested_tuple(value)
    if not isinstance(member, tuple) or len(member) != 7 or member[0] != "readonly_return_case_partition_member":
        return False
    case_index, source_indices = member[1], member[2]
    return_case, comparison_surface, value_entry, guards = member[3], member[4], member[5], member[6]
    if not (_nonnegative_int_like(case_index) and _source_indices_are_specific(source_indices)):
        return False
    if not _return_case_key_is_specific(return_case, case_index):
        return False
    if not _comparison_surface_is_specific(comparison_surface):
        return False
    return _readonly_value_entry_is_specific(value_entry) and _guards_key_is_specific(guards, allow_empty=True)


def _return_case_key_is_specific(value: Any, case_index: Any) -> bool:
    case = _normalize_nested_tuple(value)
    if not isinstance(case, tuple) or len(case) != 6 or case[0] != "return_case":
        return False
    return (
        case[1] == case_index
        and _text_identity_is_specific(case[2])
        and _pcode_op_ref_is_specific(case[3])
        and _text_identity_is_specific(case[4])
        and _nonnegative_int_like(case[5])
    )


def _comparison_surface_is_specific(value: Any) -> bool:
    surface = _normalize_nested_tuple(value)
    if not isinstance(surface, tuple) or len(surface) != 4 or surface[0] != "comparison_surface":
        return False
    kind = surface[1]
    width = surface[2]
    return kind == "return_value" and _nonnegative_int_like(width)


def _readonly_reduction_ref_is_specific(value: Any) -> bool:
    ref = _normalize_nested_tuple(value)
    if not isinstance(ref, tuple) or len(ref) not in {11, 12} or ref[0] != "readonly_reduction_ref":
        return False
    required = (
        _text_identity_is_specific(ref[1])
        and _tag_payload_specific(ref[2], "semantic_key")
        and _tag_payload_specific(ref[3], "pointer_base_identity")
        and _count_identities_are_specific(ref[4])
        and _tag_payload_specific(ref[5], "term_contract")
        and _tag_nonnegative_int(ref[6], "result_size")
        and _tag_nonnegative_int(ref[7], "stride")
        and _tag_nonnegative_int(ref[8], "element_size")
        and _tag_int_like(ref[9], "start_offset")
        and _tag_int_like(ref[10], "constant_bias")
    )
    if not required:
        return False
    if len(ref) == 11:
        return True
    witnesses = ref[11]
    return _semantic_witnesses_are_specific(witnesses)


def _semantic_witnesses_are_specific(value: Any) -> bool:
    normalized = _normalize_nested_tuple(value)
    if (
        not isinstance(normalized, tuple)
        or len(normalized) != 2
        or normalized[0] != "semantic_witnesses"
        or not isinstance(normalized[1], tuple)
        or not normalized[1]
    ):
        return False
    return all(_readonly_reduction_witness_is_specific(witness) for witness in normalized[1])


def _readonly_reduction_witness_is_specific(value: Any) -> bool:
    witness = _normalize_nested_tuple(value)
    if (
        not isinstance(witness, tuple)
        or len(witness) != 4
        or witness[0] != "readonly_reduction_witness"
        or not _text_identity_is_specific(witness[1])
        or not _nonnegative_int_like(witness[2])
        or not isinstance(witness[3], tuple)
    ):
        return False
    terms = witness[3]
    exact_count = int(witness[2])
    if exact_count > 0 and not terms:
        return False
    return all(_readonly_reduction_term_is_specific(term) for term in terms)


def _readonly_reduction_term_is_specific(value: Any) -> bool:
    term = _normalize_nested_tuple(value)
    return (
        isinstance(term, tuple)
        and len(term) == 3
        and term[0] == "readonly_reduction_term"
        and _int_like(term[1])
        and _positive_int_like(term[2])
    )


def _count_identities_are_specific(value: Any) -> bool:
    normalized = _normalize_nested_tuple(value)
    if not isinstance(normalized, tuple) or len(normalized) != 2 or normalized[0] != "count_identities":
        return False
    identities = normalized[1]
    return isinstance(identities, tuple) and bool(identities) and all(_object_leaf_is_specific(item) for item in identities)


def _readonly_value_entry_is_specific(value: Any) -> bool:
    normalized = _normalize_nested_tuple(value)
    if not isinstance(normalized, tuple) or len(normalized) != 2:
        return False
    if normalized[0] == "value":
        return _readonly_value_object_is_specific(normalized[1])
    return False


def _readonly_value_object_is_specific(value: Any) -> bool:
    normalized = _normalize_nested_tuple(value)
    if not isinstance(normalized, tuple) or not normalized:
        return False
    if normalized[0] == "readonly_value":
        return len(normalized) == 2 and _readonly_reduction_ref_is_specific(normalized[1])
    if normalized[0] == "expression":
        return _structured_root_is_specific(normalized, {"expression"})
    return False


def _guards_key_is_specific(value: Any, *, allow_empty: bool) -> bool:
    normalized = _normalize_nested_tuple(value)
    if not isinstance(normalized, tuple) or len(normalized) != 2 or normalized[0] != "guards":
        return False
    guards = normalized[1]
    if not isinstance(guards, tuple):
        return False
    if not guards:
        return bool(allow_empty)
    return all(_return_guard_is_specific(guard) for guard in guards)


def _return_guard_is_specific(value: Any) -> bool:
    guard = _normalize_nested_tuple(value)
    return (
        isinstance(guard, tuple)
        and len(guard) == 4
        and guard[0] == "return_guard"
        and isinstance(guard[1], bool)
        and _structured_root_is_specific(guard[2], {"condition"})
        and _structured_root_is_specific(guard[3], {"expression"})
    )


def _source_indices_are_specific(value: Any) -> bool:
    normalized = _normalize_nested_tuple(value)
    return isinstance(normalized, tuple) and bool(normalized) and all(_nonnegative_int_like(item) for item in normalized)


def _tag_payload_specific(value: Any, tag: str) -> bool:
    normalized = _normalize_nested_tuple(value)
    if not (isinstance(normalized, tuple) and len(normalized) == 2 and normalized[0] == tag):
        return False
    payload = normalized[1]
    if tag == "semantic_key":
        return _readonly_semantic_key_is_specific(payload)
    if tag == "pointer_base_identity":
        return _readonly_pointer_base_identity_is_specific(payload)
    if tag == "term_contract":
        return _readonly_term_contract_is_specific(payload)
    return isinstance(payload, tuple) and _object_leaf_is_specific(payload)


def _readonly_semantic_key_is_specific(value: Any) -> bool:
    normalized = _normalize_nested_tuple(value)
    if not _readonly_structured_tuple_has_root(
        normalized,
        {"readonly_reduction_proof_semantic", "readonly_sum"},
    ):
        return False
    if normalized[0] == "readonly_reduction_proof_semantic":
        return (
            len(normalized) >= 7
            and _text_identity_is_specific(normalized[1])
            and _readonly_component_key_is_specific(normalized[2])
            and _readonly_component_key_is_specific(normalized[3])
            and _nonnegative_int_like(normalized[4])
            and _readonly_projection_key_is_specific(normalized[5])
            and _readonly_term_contract_is_specific(normalized[6])
        )
    if normalized[0] == "readonly_sum":
        return (
            len(normalized) >= 4
            and all(_readonly_component_key_is_specific(item) for item in normalized[1:])
        )
    return False


def _readonly_pointer_base_identity_is_specific(value: Any) -> bool:
    return _readonly_component_key_is_specific(value)


def _readonly_term_contract_is_specific(value: Any) -> bool:
    normalized = _normalize_nested_tuple(value)
    if not _readonly_structured_tuple_has_root(
        normalized,
        {"readonly_reduction_term_sequence_contract", "affine_readonly_sum"},
    ):
        return False
    if normalized[0] == "readonly_reduction_term_sequence_contract":
        return (
            len(normalized) >= 14
            and _text_identity_is_specific(normalized[1])
            and _readonly_component_key_is_specific(normalized[2])
            and _readonly_component_key_is_specific(normalized[3])
            and _readonly_component_key_is_specific(normalized[4])
            and all(_int_like(item) for item in normalized[5:10])
            and isinstance(normalized[10], bool)
            and isinstance(normalized[11], tuple)
            and _readonly_projection_key_is_specific(normalized[12])
            and _readonly_side_effect_profile_is_specific(normalized[13])
        )
    if normalized[0] == "affine_readonly_sum":
        return (
            len(normalized) >= 4
            and all(_readonly_component_key_is_specific(item) for item in normalized[1:])
        )
    return False


def _readonly_structured_tuple_has_root(value: Any, roots: set[str]) -> bool:
    return (
        isinstance(value, tuple)
        and len(value) >= 2
        and value[0] in roots
        and not _nested_contains_missing(value)
        and not _nested_contains_diagnostic_reason(value)
    )


def _readonly_component_key_is_specific(value: Any) -> bool:
    normalized = _normalize_nested_tuple(value)
    if isinstance(normalized, tuple):
        if not normalized or not _text_identity_is_specific(normalized[0]):
            return False
        if _nested_contains_missing(normalized) or _nested_contains_diagnostic_reason(normalized):
            return False
        root = normalized[0]
        if root in {"parameter", "loop_limit_parameter"}:
            return len(normalized) == 2 and _nonnegative_int_like(normalized[1])
        if root == "parameter_storage":
            return len(normalized) == 2 and _readonly_component_key_is_specific(normalized[1])
        if root == "register_storage":
            return len(normalized) == 6 and all(_int_like(item) for item in normalized[1:])
        if root in {"binary", "kind"}:
            return len(normalized) == 2 and _text_identity_is_specific(normalized[1])
        if root in {"base", "count", "storage"}:
            return len(normalized) == 2 and _readonly_component_key_is_specific(normalized[1])
        if root in {"stride", "element_size", "result_size"}:
            return len(normalized) == 2 and _nonnegative_int_like(normalized[1])
        if root in {"start_offset", "constant_bias"}:
            return len(normalized) == 2 and _int_like(normalized[1])
        if root in {"expression", "condition"}:
            return _structured_root_is_specific(normalized, {root})
        if root in {"const", "literal", "parameter", "variable", "binary", "unary", "memory", "call", "intrinsic", "phi"}:
            return _structured_node_is_specific(normalized)
    return False


def _readonly_projection_key_is_specific(value: Any) -> bool:
    normalized = _normalize_nested_tuple(value)
    return (
        isinstance(normalized, tuple)
        and bool(normalized)
        and all(_int_like(item) for item in normalized)
    )


def _readonly_side_effect_profile_is_specific(value: Any) -> bool:
    normalized = _normalize_nested_tuple(value)
    if not isinstance(normalized, tuple) or len(normalized) < 2:
        return False
    return (
        normalized[0] == "loop_side_effect_profile"
        and _text_identity_is_specific(normalized[1])
        and not _nested_contains_missing(normalized)
        and not _nested_contains_diagnostic_reason(normalized)
    )


def _tag_nonnegative_int(value: Any, tag: str) -> bool:
    normalized = _normalize_nested_tuple(value)
    return (
        isinstance(normalized, tuple)
        and len(normalized) == 2
        and normalized[0] == tag
        and _nonnegative_int_like(normalized[1])
    )


def _tag_int_like(value: Any, tag: str) -> bool:
    normalized = _normalize_nested_tuple(value)
    return (
        isinstance(normalized, tuple)
        and len(normalized) == 2
        and normalized[0] == tag
        and _int_like(normalized[1])
    )


def _object_leaf_is_specific(value: Any) -> bool:
    normalized = _normalize_nested_tuple(value)
    if normalized is None or normalized == "" or normalized == MISSING_SENTINEL:
        return False
    if isinstance(normalized, str):
        return _text_identity_is_specific(normalized)
    if isinstance(normalized, bool):
        return True
    if isinstance(normalized, int):
        return True
    if isinstance(normalized, tuple):
        return (
            bool(normalized)
            and not _nested_contains_missing(normalized)
            and not _nested_contains_diagnostic_reason(normalized)
        )
    return False


def _pcode_op_ref_is_specific(value: Any) -> bool:
    ref = _normalize_nested_tuple(value)
    if not isinstance(ref, tuple) or len(ref) != 8 or ref[0] != "pcode_op":
        return False
    return (
        _text_identity_is_specific(ref[1])
        and _address_ref_is_specific(ref[2], "function_entry")
        and _address_ref_is_specific(ref[3], "seq_target")
        and _nonnegative_int_like(ref[4])
        and _nonnegative_int_like(ref[5])
        and _opcode_is_specific(ref[6])
        and _nonnegative_int_like(ref[7])
    )


def _opcode_is_specific(value: Any) -> bool:
    if isinstance(value, bool) or value is None:
        return False
    if isinstance(value, int):
        return value >= 0
    return _text_identity_is_specific(value)


def _address_ref_is_specific(value: Any, expected_tag: str) -> bool:
    ref = _normalize_nested_tuple(value)
    return (
        isinstance(ref, tuple)
        and len(ref) == 3
        and ref[0] == expected_tag
        and _text_identity_is_specific(ref[1])
        and _nonnegative_int_like(ref[2])
    )


def _nested_contains_missing(value: Any) -> bool:
    normalized = _normalize_nested_tuple(value)
    if normalized is None or normalized == "" or normalized == MISSING_SENTINEL:
        return True
    if isinstance(normalized, tuple):
        return any(_nested_contains_missing(item) for item in normalized)
    return False


def _nested_contains_diagnostic_reason(value: Any) -> bool:
    normalized = _normalize_nested_tuple(value)
    if isinstance(normalized, tuple):
        if normalized[:1] == ("reason",):
            return True
        return any(_nested_contains_diagnostic_reason(item) for item in normalized)
    return False


def _nonnegative_int_like(value: Any) -> bool:
    if isinstance(value, bool) or value is None:
        return False
    try:
        return int(value) >= 0
    except (TypeError, ValueError):
        return False


def _int_like(value: Any) -> bool:
    if isinstance(value, bool) or value is None:
        return False
    try:
        int(value)
    except (TypeError, ValueError):
        return False
    return True


def _positive_int_like(value: Any) -> bool:
    if isinstance(value, bool) or value is None:
        return False
    try:
        return int(value) > 0
    except (TypeError, ValueError):
        return False


def _proof_action_has_expected_id(action: Mapping[str, Any]) -> bool:
    target = _normalize_nested_tuple(action.get("object_target_key"))
    provided = _normalize_nested_tuple(action.get("proof_obligation_id"))
    return provided == _expected_proof_obligation_id(action, object_target_key=target)


def _expected_proof_obligation_id(action: Mapping[str, Any], *, object_target_key: Any) -> Tuple[Any, ...]:
    return build_proof_obligation_id(
        str(action.get("reason_id") or MISSING_SENTINEL),
        str(action.get("proof_stage") or MISSING_SENTINEL),
        str(action.get("proof_kind") or MISSING_SENTINEL),
        str(action.get("evidence_kind") or MISSING_SENTINEL),
        _normalize_nested_tuple(object_target_key),
    )


def _proof_action_matches_lane_definition(action: Mapping[str, Any]) -> bool:
    return (
        action.get("count_kind") == UnknownCountKind.PROOF_ACTION.value
        and action.get("decision_effect") == "blocks_equivalence"
        and action.get("reason_scope") == "expression"
        and action.get("aggregation_unit") == "pair"
        and action.get("stage") == "S_PAIRWISE"
        and action.get("status") == "planned"
        and action.get("evidence_kind") == READONLY_EVIDENCE_KIND
        and tuple(action.get("required_evidence") or ()) == READONLY_REQUIRED_EVIDENCE
        and tuple(action.get("tuple") or ()) == READONLY_ACTION_TUPLE
    )


def _canonical_actions(values: Any) -> Tuple[Dict[str, Any], ...]:
    if not isinstance(values, Sequence) or isinstance(values, (str, bytes)):
        return ()
    canonical = []
    for action in values:
        if not isinstance(action, Mapping):
            continue
        canonical.append(
            {
                "count_kind": action.get("count_kind") or MISSING_SENTINEL,
                "reason_id": action.get("reason_id") or MISSING_SENTINEL,
                "decision_effect": action.get("decision_effect") or MISSING_SENTINEL,
                "reason_scope": action.get("reason_scope") or MISSING_SENTINEL,
                "aggregation_unit": action.get("aggregation_unit") or MISSING_SENTINEL,
                "stage": action.get("stage") or MISSING_SENTINEL,
                "pair_or_case": action.get("pair_or_case") or MISSING_SENTINEL,
                "proof_kind": action.get("proof_kind") or MISSING_SENTINEL,
                "proof_stage": action.get("proof_stage") or MISSING_SENTINEL,
                "status": action.get("status") or MISSING_SENTINEL,
                "evidence_kind": action.get("evidence_kind") or MISSING_SENTINEL,
                "required_evidence": list(action.get("required_evidence") or ()),
                "object_target_key": _jsonable(action.get("object_target_key")),
                "proof_obligation_id": _jsonable(action.get("proof_obligation_id")),
                "tuple": list(action.get("tuple") or ()),
            }
        )
    return tuple(sorted(canonical, key=_canonical_json))


def _readonly_side(target: Any, side_label: str) -> Any:
    normalized = _normalize_nested_tuple(target)
    if not isinstance(normalized, tuple):
        return None
    for item in normalized:
        if (
            isinstance(item, tuple)
            and len(item) >= 2
            and item[0] == "readonly_identity_side"
            and item[1] == side_label
        ):
            return item
    return None


def _expected_entry_for(entry: Mapping[str, Any]) -> Mapping[str, Any]:
    return _entry_map(DEFAULT_REPRESENTATIVES).get(_entry_key(entry), {})


def _load_phase3_manifest(
    *,
    raw_dir: Path,
    explicit_path: Optional[Path],
) -> Tuple[Dict[str, Any], Dict[str, Any]]:
    candidates = []
    if explicit_path is not None:
        candidates.append(Path(explicit_path))
    else:
        candidates.append(
            raw_dir.parent
            / "audit"
            / "phase3_readonly_identity_lane3"
            / "readonly_identity_lane3_representatives.json"
        )
    for path in candidates:
        if path.is_file():
            return _read_json(path), _file_ref(path)
    fallback = candidates[0]
    return {}, {"path": str(fallback), "sha256": "__missing__"}


if __name__ == "__main__":
    raise SystemExit(main())
