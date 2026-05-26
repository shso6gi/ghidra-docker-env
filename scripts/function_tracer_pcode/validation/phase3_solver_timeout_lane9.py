# -*- coding: utf-8 -*-
"""Freeze Phase 3 lane 9 solver-timeout operational representatives."""

from __future__ import annotations

import argparse
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Dict, Mapping, Optional, Sequence, Tuple

from .result_summary import STATUS_EQ, STATUS_TIMEOUT, classify_result_payload
from .unknown_reason_summary import (
    _extract_final_unknown_reasons,
    _global_reason_tuple_from_action,
    _global_reason_tuple_from_record,
)
from .phase3_method_b_closure_lane4 import (
    _action_to_dict,
    _completed_recovery_proof_summaries,
    _observation as _base_observation,
    _reason_to_dict,
)
from .phase3_readonly_identity_lane3 import (
    _analysis_entry_key_is_specific,
    _completed_evidence_has_active_blocker,
    _nested_completed_proof_has_active_blocker,
    _nested_contains_diagnostic_reason,
)
from .phase3_return_width_bridge_lane2 import (
    _binary_direction_matches,
    _canonical_actions,
    _canonical_json,
    _canonical_movements,
    _canonical_targets,
    _display_path,
    _entry_details,
    _entry_key,
    _entry_map,
    _failed,
    _file_ref,
    _identity_set_check,
    _identity_to_dict,
    _jsonable,
    _nonnegative_int_like,
    _normalize_nested_tuple,
    _ok,
    _parse_roots,
    _read_json,
    _records_by_key,
    _sha256_file,
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
TARGET_REASON_IDS = ("solver_unknown_timeout",)
MISSING_SENTINEL = UNKNOWN_TUPLE_MISSING
SOLVER_TIMEOUT_PROOF_KIND = "solver_retry_or_normalization"
SOLVER_TIMEOUT_PROOF_STAGE = "solver_timeout_retry"
SOLVER_TIMEOUT_EVIDENCE_KIND = "query_hash"
SOLVER_TIMEOUT_REQUIRED_EVIDENCE = (
    "query_hash",
    "timeout_budget",
    "solver_options",
    "normalized_query",
)
NON_SPECIFIC_SOLVER_NAMES = frozenset(
    {
        "unknown_solver",
        "no_solver_result",
        "unknown",
        MISSING_SENTINEL,
    }
)
SOLVER_TIMEOUT_REASON_TUPLE = (
    UnknownCountKind.REASON_RECORD.value,
    "solver_unknown_timeout",
    "retryable",
    "query",
    SOLVER_TIMEOUT_PROOF_KIND,
    SOLVER_TIMEOUT_PROOF_STAGE,
    MISSING_SENTINEL,
)
SOLVER_TIMEOUT_ACTION_TUPLE = (
    UnknownCountKind.PROOF_ACTION.value,
    "solver_unknown_timeout",
    "retryable",
    "query",
    SOLVER_TIMEOUT_PROOF_KIND,
    SOLVER_TIMEOUT_PROOF_STAGE,
    "planned",
)
FUNCTION_CALL_BINARY_NAMES = {
    "B8": "function_call_test-arm64-gcc-O3",
    "B9": "function_call_test-mips64-clang-O0",
}


def _expected_reason_record(movement_id: str) -> Dict[str, Any]:
    return {
        "id": movement_id,
        "count_kind": UnknownCountKind.REASON_RECORD.value,
        "tuple": list(SOLVER_TIMEOUT_REASON_TUPLE),
        "aggregation_unit": "pair",
        "stage": "S_MONOLITHIC_FALLBACK",
        "pair_or_case": MISSING_SENTINEL,
        "expected_evidence_refs": ["monolithic_query_timeout"],
        "expected_evidence_kind": SOLVER_TIMEOUT_EVIDENCE_KIND,
        "required_evidence": list(SOLVER_TIMEOUT_REQUIRED_EVIDENCE),
        "required_object_target_kind": "solver_timeout",
        "require_proof_obligation_id": True,
    }


def _expected_proof_action(movement_id: str) -> Dict[str, Any]:
    return {
        "id": movement_id,
        "count_kind": UnknownCountKind.PROOF_ACTION.value,
        "tuple": list(SOLVER_TIMEOUT_ACTION_TUPLE),
        "aggregation_unit": "pair",
        "stage": "S_MONOLITHIC_FALLBACK",
        "pair_or_case": MISSING_SENTINEL,
        "expected_evidence_refs": ["monolithic_query_timeout"],
        "expected_evidence_kind": SOLVER_TIMEOUT_EVIDENCE_KIND,
        "required_evidence": list(SOLVER_TIMEOUT_REQUIRED_EVIDENCE),
        "required_object_target_kind": "solver_timeout",
        "require_proof_obligation_id": True,
    }


DEFAULT_REPRESENTATIVES: Tuple[Mapping[str, Any], ...] = (
    {
        "id": "representative-solver-timeout-long-branch-dispatch-arm64-mips64",
        "category": "function_call",
        "function": "fc_long_branch_dispatch",
        "binary_pair": "B8_B9",
        "expected_observed_binary1_name": FUNCTION_CALL_BINARY_NAMES["B8"],
        "expected_observed_binary2_name": FUNCTION_CALL_BINARY_NAMES["B9"],
        "required_reason_ids": ["solver_unknown_timeout"],
        "role": "monolithic solver timeout with query retry/normalization proof backlog",
        "expected_movements": [
            _expected_reason_record("solver-timeout-reason-record"),
            _expected_proof_action("solver-timeout-retry-proof"),
        ],
    },
)


def build_phase3_solver_timeout_lane9_manifest(
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
        "manifest_kind": "phase3_solver_timeout_lane9_representatives",
        "artifact_role": "derived_audit_operational_timeout_gate",
        "baseline_id": baseline_manifest.get("baseline_id") or MISSING_SENTINEL,
        "baseline_git_head": baseline_manifest.get("git_head") or MISSING_SENTINEL,
        "created_at": datetime.now(timezone.utc).isoformat(),
        "target_reason_ids": list(TARGET_REASON_IDS),
        "baseline_raw_artifact_ref": _file_ref(raw_dir / "artifact_manifest.json"),
        "current_log_roots": {
            category: _display_path(path) for category, path in sorted(current_log_roots.items())
        },
        "baseline_log_roots": {
            category: _display_path(path) for category, path in sorted(baseline_log_roots.items())
        },
        "selection_policy": {
            "representative_count": len(entries),
            "criteria": [
                "concrete function_call function x binary_pair id",
                "baseline/current TIMEOUT result",
                "current solver_unknown_timeout record carries query hash target",
                "current proof action carries raw object_target_key and proof_obligation_id",
                "solver timeout target includes query hash, timeout budget, solver options, and both function entries",
            ],
        },
        "implementation_manifest": _implementation_manifest(entries),
        "readiness": readiness,
        "phase3_lane9_ready": readiness["ready"],
        "entries": entries,
    }
    path = output / "solver_timeout_lane9_representatives.json"
    _write_json(path, manifest)
    return path


def validate_phase3_solver_timeout_lane9_manifest(manifest: Mapping[str, Any]) -> None:
    if manifest.get("phase3_lane9_ready") is True:
        return
    readiness = manifest.get("readiness")
    failures = []
    if isinstance(readiness, Mapping):
        failures.extend(str(kind) for kind in readiness.get("failure_kinds") or ())
    if not failures:
        raise ValueError("Phase 3 lane 9 readiness is false without failure details")
    raise ValueError(f"Phase 3 lane 9 representative manifest is not ready: {', '.join(failures)}")


def build_phase3_solver_timeout_lane9_post_fix_gate(
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
    phase3_manifest, phase3_ref = _load_phase3_manifest(raw_dir=raw_dir, explicit_path=phase3_manifest_path)
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
    post_fix_gate = _post_fix_regression_gate(entries=entries, manifest_checks=manifest_checks)
    manifest = {
        "manifest_version": MANIFEST_VERSION,
        "manifest_kind": "phase3_solver_timeout_lane9_post_fix_gate",
        "artifact_role": "derived_audit_post_fix_gate",
        "baseline_id": baseline_manifest.get("baseline_id") or MISSING_SENTINEL,
        "baseline_git_head": baseline_manifest.get("git_head") or MISSING_SENTINEL,
        "created_at": datetime.now(timezone.utc).isoformat(),
        "target_reason_ids": list(TARGET_REASON_IDS),
        "baseline_raw_artifact_ref": _file_ref(raw_dir / "artifact_manifest.json"),
        "phase3_pre_fix_manifest_ref": phase3_ref,
        "current_log_roots": {
            category: _display_path(path) for category, path in sorted(current_log_roots.items())
        },
        "baseline_log_roots": {
            category: _display_path(path) for category, path in sorted(baseline_log_roots.items())
        },
        "post_fix_policy": {
            "timeout_with_pending_retry": "accepted_pending_retry_only_when_final_result_remains_timeout",
            "eq_requires_completed_solver_retry_proof": True,
            "proof_id_source": "pre_fix_manifest_unknown_recovery_actions",
            "reject_eq_with_pending_solver_timeout_reason": True,
            "reject_eq_with_any_solver_timeout_proof_action": True,
            "reject_unknown_without_explicit_expected_movement": True,
        },
        "post_fix_regression_gate": post_fix_gate,
        "phase3_lane9_post_fix_ready": post_fix_gate["ready"],
        "entries": entries,
    }
    path = output / "solver_timeout_lane9_post_fix_gate.json"
    _write_json(path, manifest)
    return path


def validate_phase3_solver_timeout_lane9_post_fix_gate(manifest: Mapping[str, Any]) -> None:
    if manifest.get("phase3_lane9_post_fix_ready") is True:
        return
    gate = manifest.get("post_fix_regression_gate")
    failures = []
    if isinstance(gate, Mapping):
        summary = gate.get("summary")
        if isinstance(summary, Mapping):
            failures.extend(str(kind) for kind in summary.get("failed_kinds") or ())
    if not failures:
        raise ValueError("Phase 3 lane 9 post-fix gate is false without failure details")
    raise ValueError(f"Phase 3 lane 9 post-fix gate is not ready: {', '.join(failures)}")


def _implementation_manifest(entries: Sequence[Mapping[str, Any]]) -> Dict[str, Any]:
    return {
        "lane_id": "phase3_solver_timeout_lane9",
        "lane_reason_ids": list(TARGET_REASON_IDS),
        "proof_completion_gate": {
            "eq_allowed_without_completed_proof": False,
            "pending_proof_keeps_final_result": STATUS_TIMEOUT,
            "completion_required_for_recovery": [SOLVER_TIMEOUT_PROOF_STAGE],
            "required_recovery_actions": [SOLVER_TIMEOUT_PROOF_STAGE],
        },
        "expected_movement_entries": [
            {
                "id": entry.get("id"),
                "category": entry.get("category"),
                "function": entry.get("function"),
                "binary_pair": entry.get("binary_pair"),
                "expected_movements": entry.get("expected_movements") or (),
                "expected_solver_timeout_targets": _canonical_targets(_current_targets(entry)),
                "required_completion_actions": _canonical_actions(_current_timeout_actions(entry)),
            }
            for entry in entries
        ],
    }


def _readiness(entries: Sequence[Mapping[str, Any]]) -> Dict[str, Any]:
    checks: list[Dict[str, Any]] = []
    checks.append(_identity_set_check("phase3_lane9_entries_exact_set", DEFAULT_REPRESENTATIVES, entries))
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
        _ok("solver_timeout_baseline_timeout", **details)
        if baseline.get("final_result") == STATUS_TIMEOUT
        else _failed(
            "solver_timeout_baseline_timeout",
            current_result=baseline.get("final_result", MISSING_SENTINEL),
            **details,
        )
    )
    checks.append(
        _ok("solver_timeout_current_timeout", **details)
        if current.get("final_result") == STATUS_TIMEOUT
        else _failed(
            "solver_timeout_current_timeout",
            current_result=current.get("final_result", MISSING_SENTINEL),
            **details,
        )
    )
    checks.append(
        _ok("solver_timeout_binary_direction", **details)
        if _binary_direction_matches(entry, current)
        else _failed(
            "solver_timeout_binary_direction",
            observed_binary1_name=current.get("observed_binary1_name", MISSING_SENTINEL),
            observed_binary2_name=current.get("observed_binary2_name", MISSING_SENTINEL),
            **details,
        )
    )
    current_targets = _current_targets(entry)
    checks.append(
        _ok("solver_timeout_current_targets_present", count=len(current_targets), **details)
        if current_targets
        else _failed("solver_timeout_current_targets_present", count=0, **details)
    )
    checks.append(
        _ok(
            "solver_timeout_current_actions_complete",
            count=len(_current_timeout_actions(entry)),
            target_count=len(current_targets),
            **details,
        )
        if current_targets and not _missing_timeout_actions(entry)
        else _failed(
            "solver_timeout_current_actions_complete",
            missing=_missing_timeout_actions(entry),
            **details,
        )
    )
    checks.append(
        _ok("solver_timeout_expected_movements_match_definition", **details)
        if _canonical_movements(entry.get("expected_movements"))
        == _canonical_movements(_expected_entry_for(entry).get("expected_movements"))
        else _failed(
            "solver_timeout_expected_movements_match_definition",
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
        if phase3_manifest.get("manifest_kind") == "phase3_solver_timeout_lane9_representatives"
        else _failed(
            "phase3_pre_fix_manifest_kind",
            manifest_kind=phase3_manifest.get("manifest_kind", MISSING_SENTINEL),
        )
    )
    checks.append(
        _ok("phase3_pre_fix_manifest_ready")
        if phase3_manifest.get("phase3_lane9_ready") is True
        else _failed(
            "phase3_pre_fix_manifest_ready",
            phase3_lane9_ready=phase3_manifest.get("phase3_lane9_ready", MISSING_SENTINEL),
        )
    )
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
            implementation.get("expected_solver_timeout_targets")
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
        actual_actions = _canonical_actions(_current_timeout_actions(actual)) if isinstance(actual, Mapping) else ()
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
                "solver_timeout_post_fix_expected_movement",
                entry_id=entry.get("id"),
                function=entry.get("function"),
                binary_pair=entry.get("binary_pair"),
                post_fix_status=entry.get("post_fix_status"),
            )
            if entry.get("post_fix_status") in {"pending_retry", "completed_recovery"}
            else _failed(
                "solver_timeout_post_fix_expected_movement",
                entry_id=entry.get("id"),
                function=entry.get("function"),
                binary_pair=entry.get("binary_pair"),
                failures=entry.get("post_fix_failures") or (),
                current_result=(entry.get("current_observation") or {}).get("final_result"),
            )
        )
    failed = [check for check in checks if check.get("status") == "failed"]
    return {
        "gate_kind": "phase3_solver_timeout_lane9_post_fix_regression",
        "baseline_mode": "timeout_pending_retry_or_completed_proof_against_pre_fix_manifest",
        "ready": not failed,
        "summary": {
            "total": len(checks),
            "passed": sum(1 for check in checks if check.get("status") == "ok"),
            "failed": len(failed),
            "failed_kinds": sorted({str(check.get("kind")) for check in failed}),
            "locked_gates": [
                "phase3_pre_fix_manifest_sha256",
                "solver_timeout_object_target_key",
                "solver_timeout_proof_obligation_id",
                "solver_timeout_completed_proof_required_before_eq",
                "no_pending_solver_timeout_action_on_eq",
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
    entry["required_completion_actions"] = _canonical_actions(_current_timeout_actions(entry))
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
    return entry


def _post_fix_status(entry: Mapping[str, Any]) -> Tuple[str, Sequence[Dict[str, Any]]]:
    failures: list[Dict[str, Any]] = []
    current = entry.get("current_observation") if isinstance(entry.get("current_observation"), Mapping) else {}
    result = current.get("final_result")
    details = _entry_details(entry)
    if result == STATUS_EQ:
        failures.extend(_completed_recovery_failures(entry, current))
        if failures:
            return "failed", failures
        return "completed_recovery", ()
    if result != STATUS_TIMEOUT:
        failures.append(
            _failed(
                "solver_timeout_pending_retry_requires_timeout_final_result",
                current_result=result or MISSING_SENTINEL,
                expected_result=STATUS_TIMEOUT,
                **details,
            )
        )
        return "failed", failures
    frozen_targets = _canonical_targets(entry.get("target_object_keys"))
    current_targets = _canonical_targets(_current_targets(entry))
    if not frozen_targets or current_targets != frozen_targets:
        failures.append(
            _failed(
                "solver_timeout_target_set_changed",
                expected=frozen_targets,
                actual=current_targets,
                **details,
            )
        )
    frozen_actions = _canonical_actions(entry.get("required_completion_actions"))
    current_actions = _canonical_actions(_current_timeout_actions(entry))
    if not frozen_actions or current_actions != frozen_actions:
        failures.append(
            _failed(
                "solver_timeout_required_actions_changed",
                expected=frozen_actions,
                actual=current_actions,
                **details,
            )
        )
    missing = _missing_timeout_actions(entry)
    if missing:
        failures.append(_failed("solver_timeout_current_actions_complete", missing=missing, **details))
    if failures:
        return "failed", failures
    return "pending_retry", ()


def _observation(entry: Mapping[str, Any], record: Optional[Mapping[str, Any]]) -> Dict[str, Any]:
    observation = _base_observation(entry, record)
    if record is None:
        return observation
    payload = record.get("payload") if isinstance(record.get("payload"), Mapping) else {}
    reasons = _extract_final_unknown_reasons(payload)
    raw_actions = payload.get("unknown_recovery_actions")
    if not isinstance(raw_actions, Sequence) or isinstance(raw_actions, (str, bytes)):
        raw_actions = ()
    actions = coerce_unknown_recovery_actions(raw_actions)
    observation.update(
        {
            "final_result": classify_result_payload(payload),
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
    )
    return observation


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
        if record.get("reason_id") != "solver_unknown_timeout":
            continue
        target = record.get("object_target_key")
        if _object_target_key_is_specific_solver_timeout(target):
            targets.append(target)
    return tuple(targets)


def _current_timeout_actions(entry: Any) -> Sequence[Mapping[str, Any]]:
    if not isinstance(entry, Mapping):
        return ()
    current = entry.get("current_observation")
    if not isinstance(current, Mapping):
        return ()
    actions = []
    for action in current.get("proof_actions") or ():
        if not isinstance(action, Mapping):
            continue
        if action.get("reason_id") != "solver_unknown_timeout":
            continue
        if not _solver_timeout_action_matches_lane_definition(action):
            continue
        if not _object_target_key_is_specific_solver_timeout(action.get("object_target_key")):
            continue
        if action.get("proof_obligation_id") is None:
            continue
        if action.get("raw_proof_obligation_id_present") is not True:
            continue
        if action.get("raw_object_target_key_present") is not True:
            continue
        if not _proof_action_has_expected_id(action):
            continue
        actions.append(action)
    return tuple(actions)


def _missing_timeout_actions(entry: Mapping[str, Any]) -> Sequence[Dict[str, Any]]:
    current_targets = _canonical_targets(_current_targets(entry))
    actions = _current_timeout_actions(entry)
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
        key = (_canonical_json(target), SOLVER_TIMEOUT_PROOF_KIND, SOLVER_TIMEOUT_PROOF_STAGE)
        if key not in action_keys:
            missing.append(
                {
                    "object_target_key": target,
                    "proof_kind": SOLVER_TIMEOUT_PROOF_KIND,
                    "proof_stage": SOLVER_TIMEOUT_PROOF_STAGE,
                }
            )
    return missing


def _completed_recovery_failures(
    entry: Mapping[str, Any],
    current: Mapping[str, Any],
) -> Sequence[Dict[str, Any]]:
    failures: list[Dict[str, Any]] = []
    details = _entry_details(entry)
    active_reasons = [
        reason_id
        for reason_id in current.get("observed_reason_ids") or ()
        if _text_identity_is_specific(reason_id)
    ]
    if active_reasons:
        failures.append(_failed("solver_timeout_active_reason_not_cleared", active_reason_ids=active_reasons, **details))
    pending_actions = [action for action in current.get("proof_actions") or () if isinstance(action, Mapping)]
    if pending_actions:
        failures.append(_failed("solver_timeout_pending_proof_action_still_active", **details))
    required_actions = _canonical_actions(entry.get("required_completion_actions"))
    if not required_actions:
        failures.append(_failed("solver_timeout_frozen_proof_actions_missing", **details))
        return failures
    completed = tuple(current.get("completed_recovery_proof_evidence") or ())
    if not completed:
        failures.append(_failed("solver_timeout_completed_proof_required", **details))
        return failures
    for action in required_actions:
        if not any(_completed_evidence_matches_action(evidence, action) for evidence in completed):
            failures.append(
                _failed(
                    "solver_timeout_completed_proof_required",
                    proof_stage=action.get("proof_stage") or MISSING_SENTINEL,
                    evidence_kind=action.get("evidence_kind") or MISSING_SENTINEL,
                    proof_kind=action.get("proof_kind") or MISSING_SENTINEL,
                    **details,
                )
            )
    return failures


def _completed_evidence_matches_action(evidence_summary: Mapping[str, Any], action: Mapping[str, Any]) -> bool:
    if not isinstance(evidence_summary, Mapping):
        return False
    evidence = evidence_summary.get("evidence")
    if not isinstance(evidence, Mapping):
        evidence = evidence_summary
    if evidence_summary.get("object_derived") is not True and evidence.get("object_derived") is not True:
        return False
    if str(evidence_summary.get("status") or evidence.get("status") or "") not in {"complete", "completed", "proven"}:
        return False
    object_target_key = _normalize_nested_tuple(evidence_summary.get("object_target_key") or evidence.get("object_target_key"))
    if not _object_target_key_is_specific_solver_timeout(object_target_key):
        return False
    if (
        str(evidence_summary.get("reason_id") or evidence.get("reason_id") or MISSING_SENTINEL) != str(action.get("reason_id") or MISSING_SENTINEL)
        or str(evidence_summary.get("proof_stage") or evidence.get("proof_stage") or MISSING_SENTINEL) != str(action.get("proof_stage") or MISSING_SENTINEL)
        or str(evidence_summary.get("proof_kind") or evidence.get("proof_kind") or MISSING_SENTINEL) != str(action.get("proof_kind") or MISSING_SENTINEL)
        or str(evidence_summary.get("evidence_kind") or evidence.get("evidence_kind") or MISSING_SENTINEL) != str(action.get("evidence_kind") or MISSING_SENTINEL)
    ):
        return False
    if _completed_evidence_has_active_blocker(evidence):
        return False
    if not _completed_evidence_has_required_proof_content(evidence_summary, evidence, action, object_target_key):
        return False
    expected_id = _expected_proof_obligation_id(action, object_target_key=object_target_key)
    provided_id = _normalize_nested_tuple(evidence_summary.get("proof_obligation_id") or evidence.get("proof_obligation_id"))
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
    actual_required = tuple(str(item) for item in (evidence_summary.get("required_evidence") or evidence.get("required_evidence") or ()))
    if actual_required != SOLVER_TIMEOUT_REQUIRED_EVIDENCE:
        return False
    content = _completed_proof_content(evidence_summary, evidence)
    if not isinstance(content, Mapping):
        return False
    if _nested_completed_proof_has_active_blocker(content):
        return False
    if content.get("object_derived") is not True or _normalize_nested_tuple(content.get("object_target_key")) != _normalize_nested_tuple(object_target_key):
        return False
    return (
        _proof_status_value_is_complete(content.get("query_hash"))
        and _proof_status_value_is_complete(content.get("timeout_budget"))
        and _proof_status_value_is_complete(content.get("solver_options"))
        and _proof_status_value_is_complete(content.get("normalized_query"))
    )


def _completed_proof_content(evidence_summary: Mapping[str, Any], evidence: Mapping[str, Any]) -> Any:
    for container in (evidence_summary, evidence):
        for field_name in ("proof_content", "proof", "proof_evidence"):
            content = container.get(field_name)
            if isinstance(content, Mapping):
                proof_kind = evidence_summary.get("proof_kind") or evidence.get("proof_kind")
                if proof_kind in content and isinstance(content[proof_kind], Mapping):
                    return content[proof_kind]
                return content
    return None


def _proof_status_value_is_complete(value: Any) -> bool:
    return str(value or "") in {"complete", "completed", "covered", "matched", "proven", "checked"}


def _object_target_key_is_specific_solver_timeout(value: Any) -> bool:
    target = _normalize_nested_tuple(value)
    if not isinstance(target, tuple) or len(target) != 8 or target[0] != "solver_timeout":
        return False
    pair, stage, query_hash, timeout_budget, solver_options, left, right = target[1:]
    if not (
        isinstance(pair, tuple)
        and len(pair) == 2
        and pair[0] == "pair"
        and _text_identity_is_specific(pair[1])
    ):
        return False
    if not (isinstance(stage, tuple) and len(stage) == 2 and stage[0] == "stage" and _text_identity_is_specific(stage[1])):
        return False
    if not _query_hash_key_is_specific(query_hash):
        return False
    if not _timeout_budget_key_is_specific(timeout_budget):
        return False
    if not _solver_options_key_is_specific(solver_options, timeout_budget[1]):
        return False
    if _nested_contains_diagnostic_reason(target) or _solver_timeout_target_contains_disallowed_missing(target):
        return False
    return _solver_timeout_side_is_specific(left, "left") and _solver_timeout_side_is_specific(right, "right")


def _query_hash_key_is_specific(value: Any) -> bool:
    return (
        isinstance(value, tuple)
        and len(value) == 2
        and value[0] == "query_hash"
        and isinstance(value[1], str)
        and len(value[1]) == 64
        and all(ch in "0123456789abcdef" for ch in value[1])
    )


def _timeout_budget_key_is_specific(value: Any) -> bool:
    return isinstance(value, tuple) and len(value) == 2 and value[0] == "timeout_budget_seconds" and _nonnegative_int_like(value[1])


def _solver_options_key_is_specific(value: Any, timeout_seconds: Any) -> bool:
    if not isinstance(value, tuple) or len(value) < 3 or value[0] != "solver_options":
        return False
    solver_info = value[1]
    timeout = value[2]
    solver_specific = False
    if isinstance(solver_info, tuple) and len(solver_info) == 2 and solver_info[0] == "solver":
        solver_specific = _solver_identity_is_specific(solver_info[1])
    elif isinstance(solver_info, tuple) and len(solver_info) == 2 and solver_info[0] == "solvers":
        solvers = solver_info[1]
        solver_specific = (
            isinstance(solvers, tuple)
            and bool(solvers)
            and all(_solver_identity_is_specific(solver_name) for solver_name in solvers)
        )
    return (
        solver_specific
        and isinstance(timeout, tuple)
        and len(timeout) == 2
        and timeout[0] == "timeout_seconds"
        and timeout[1] == timeout_seconds
    )


def _solver_identity_is_specific(value: Any) -> bool:
    return _text_identity_is_specific(value) and str(value).strip().lower() not in NON_SPECIFIC_SOLVER_NAMES


def _solver_timeout_side_is_specific(value: Any, side_label: str) -> bool:
    side = _normalize_nested_tuple(value)
    return (
        isinstance(side, tuple)
        and len(side) == 6
        and side[0] == "solver_timeout_side"
        and side[1] == side_label
        and _analysis_entry_key_is_specific(side[2])
        and _return_storage_key_is_specific(side[3])
        and _return_partition_key_is_specific(side[4])
        and _guard_disjunction_key_is_specific(side[5])
    )


def _return_storage_key_is_specific(value: Any) -> bool:
    return (
        isinstance(value, tuple)
        and len(value) == 5
        and value[0] == "return_storage"
        and _text_identity_is_specific(value[1])
        and _nonnegative_int_like(value[2])
        and value[3] in {True, False, None}
        and _text_identity_is_specific(value[4])
    )


def _return_partition_key_is_specific(value: Any) -> bool:
    return (
        isinstance(value, tuple)
        and len(value) == 2
        and value[0] == "return_partition"
        and isinstance(value[1], tuple)
        and bool(value[1])
        and all(_return_case_key_is_specific(item) for item in value[1])
    )


def _return_case_key_is_specific(value: Any) -> bool:
    case = _normalize_nested_tuple(value)
    return (
        isinstance(case, tuple)
        and len(case) >= 8
        and case[0] == "return_case"
        and _nonnegative_int_like(case[1])
        and _text_identity_is_specific(case[2])
        and _text_identity_is_specific(case[4])
        and _nonnegative_int_like(case[5])
        and _structured_expression_key_is_specific(case[6])
        and isinstance(case[7], tuple)
    )


def _guard_disjunction_key_is_specific(value: Any) -> bool:
    guard = _normalize_nested_tuple(value)
    return (
        isinstance(guard, tuple)
        and len(guard) == 2
        and guard[0] == "guard_disjunction"
        and isinstance(guard[1], tuple)
        and bool(guard[1])
        and all(
            isinstance(item, tuple)
            and len(item) == 2
            and _nonnegative_int_like(item[0])
            and isinstance(item[1], tuple)
            for item in guard[1]
        )
    )


def _structured_expression_key_is_specific(value: Any) -> bool:
    expr = _normalize_nested_tuple(value)
    if not isinstance(expr, tuple) or not expr:
        return False
    root = expr[0]
    if root in {"const", "parameter", "binary", "unary", "runtime_ref", "expression"}:
        return len(expr) >= 2 and not _nested_contains_missing(expr)
    return False


def _solver_timeout_action_matches_lane_definition(action: Mapping[str, Any]) -> bool:
    return (
        action.get("count_kind") == UnknownCountKind.PROOF_ACTION.value
        and action.get("reason_id") == "solver_unknown_timeout"
        and action.get("decision_effect") == "retryable"
        and action.get("reason_scope") == "query"
        and action.get("proof_kind") == SOLVER_TIMEOUT_PROOF_KIND
        and action.get("proof_stage") == SOLVER_TIMEOUT_PROOF_STAGE
        and action.get("status") == "planned"
        and action.get("stage") == "S_MONOLITHIC_FALLBACK"
        and action.get("evidence_kind") == SOLVER_TIMEOUT_EVIDENCE_KIND
        and tuple(action.get("required_evidence") or ()) == SOLVER_TIMEOUT_REQUIRED_EVIDENCE
    )


def _proof_action_has_expected_id(action: Mapping[str, Any]) -> bool:
    return _normalize_nested_tuple(action.get("proof_obligation_id")) == _expected_proof_obligation_id(action)


def _expected_proof_obligation_id(
    action: Mapping[str, Any],
    *,
    object_target_key: Any = None,
) -> Tuple[Any, ...]:
    return build_proof_obligation_id(
        "solver_unknown_timeout",
        SOLVER_TIMEOUT_PROOF_STAGE,
        SOLVER_TIMEOUT_PROOF_KIND,
        SOLVER_TIMEOUT_EVIDENCE_KIND,
        _normalize_nested_tuple(object_target_key if object_target_key is not None else action.get("object_target_key")),
    )


def _nested_contains_missing(value: Any) -> bool:
    if value in {None, "", MISSING_SENTINEL}:
        return True
    if isinstance(value, (tuple, list)):
        return any(_nested_contains_missing(item) for item in value)
    if isinstance(value, Mapping):
        return any(_nested_contains_missing(key) or _nested_contains_missing(item) for key, item in value.items())
    return False


def _solver_timeout_target_contains_disallowed_missing(value: Any) -> bool:
    return _nested_contains_disallowed_missing(value, path=())


def _nested_contains_disallowed_missing(value: Any, *, path: Tuple[int, ...]) -> bool:
    if value in {"", MISSING_SENTINEL}:
        return True
    if value is None:
        return not _solver_timeout_none_allowed_at_path(path)
    if isinstance(value, tuple):
        return any(
            _nested_contains_disallowed_missing(item, path=path + (index,))
            for index, item in enumerate(value)
        )
    if isinstance(value, list):
        return any(
            _nested_contains_disallowed_missing(item, path=path + (index,))
            for index, item in enumerate(value)
        )
    if isinstance(value, Mapping):
        return any(
            _nested_contains_disallowed_missing(key, path=path + (-1,))
            or _nested_contains_disallowed_missing(item, path=path + (-2,))
            for key, item in value.items()
        )
    return False


def _solver_timeout_none_allowed_at_path(path: Tuple[int, ...]) -> bool:
    # side return_storage use_sign_extension is optional for return-value surfaces.
    return path in {
        (6, 3, 3),
        (7, 3, 3),
    }


def _expected_entry_for(entry: Mapping[str, Any]) -> Mapping[str, Any]:
    identity = _entry_key(entry)
    for expected in DEFAULT_REPRESENTATIVES:
        if _entry_key(expected) == identity:
            return expected
    return {}


def _load_phase3_manifest(
    *,
    raw_dir: Path,
    explicit_path: Optional[Path],
) -> Tuple[Mapping[str, Any], Mapping[str, Any]]:
    path = explicit_path or (
        raw_dir.parent
        / "audit"
        / "phase3_solver_timeout_lane9"
        / "solver_timeout_lane9_representatives.json"
    )
    if not path.is_file():
        return {}, {"path": _display_path(path), "sha256": "__missing__"}
    return _read_json(path), {"path": _display_path(path), "sha256": _sha256_file(path)}


def main(argv: Optional[Sequence[str]] = None) -> int:
    parser = argparse.ArgumentParser(description="Build Phase 3 lane 9 solver-timeout representative gate.")
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
        path = build_phase3_solver_timeout_lane9_post_fix_gate(
            baseline_raw_dir=Path(args.baseline_raw_dir),
            output_dir=Path(args.output_dir),
            current_log_roots=current_roots,
            baseline_log_roots=baseline_roots,
            phase3_manifest_path=Path(args.phase3_manifest) if args.phase3_manifest else None,
            phase3_manifest_sha256=args.phase3_manifest_sha256,
        )
    else:
        path = build_phase3_solver_timeout_lane9_manifest(
            baseline_raw_dir=Path(args.baseline_raw_dir),
            output_dir=Path(args.output_dir),
            current_log_roots=current_roots,
            baseline_log_roots=baseline_roots,
        )
    if args.require_ready:
        if args.gate_stage == "post-fix":
            validate_phase3_solver_timeout_lane9_post_fix_gate(_read_json(path))
        else:
            validate_phase3_solver_timeout_lane9_manifest(_read_json(path))
    print(path)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
