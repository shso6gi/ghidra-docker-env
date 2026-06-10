# -*- coding: utf-8 -*-
"""Freeze Phase 3 lane 6 representatives for unresolved-expression work."""

from __future__ import annotations

import argparse
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Dict, Mapping, Optional, Sequence, Tuple

from .result_summary import STATUS_TIMEOUT, STATUS_UNKNOWN, classify_result_payload
from .unknown_reason_summary import _extract_final_unknown_reasons, _global_reason_tuple_from_record
from .phase3_return_width_bridge_lane2 import (
    _canonical_json,
    _canonical_movements,
    _canonical_targets,
    _call_callee_key_is_specific,
    _entry_details,
    _entry_key,
    _failed,
    _display_path,
    _file_ref,
    _identity_set_check,
    _jsonable,
    _nested_contains_missing,
    _nested_contains_missing_sentinel,
    _nested_has_specific_leaf,
    _nonnegative_int_like,
    _normalize_nested_tuple,
    _ok,
    _parse_roots,
    _read_json,
    _records_by_key,
    _sha256_file,
    _text_identity_is_specific,
    _typed_atom_key_is_specific,
    _write_json,
)
from .phase3_readonly_identity_lane3 import (
    _analysis_entry_key_is_specific,
    _nested_contains_diagnostic_reason,
)
from ..equivalence.unknown_reason import (
    UNKNOWN_TUPLE_MISSING,
    UnknownCountKind,
    build_unknown_recovery_actions,
)


MANIFEST_VERSION = 1
TARGET_REASON_IDS = ("unresolved_expression",)
MISSING_SENTINEL = UNKNOWN_TUPLE_MISSING
UNRESOLVED_EVIDENCE_KIND = "unresolved_expression_safety"
UNRESOLVED_PROOF_KIND = "solver_retry_or_normalization"
UNRESOLVED_GENERIC_PROOF_STAGES = (
    "typed_expression_lowering",
    "type_normalization",
)
UNRESOLVED_PHI_CIRCULAR_PROOF_STAGES = (
    "phi_circular_guard_condition_lowering",
    "recursive_summary_guard_equivalence",
)
UNRESOLVED_PROOF_STAGES = UNRESOLVED_GENERIC_PROOF_STAGES + UNRESOLVED_PHI_CIRCULAR_PROOF_STAGES
UNRESOLVED_REASON_TUPLE = (
    UnknownCountKind.REASON_RECORD.value,
    "unresolved_expression",
    "blocks_decision",
    "expression",
    "none",
    MISSING_SENTINEL,
    MISSING_SENTINEL,
)
FUNCTION_CALL_BINARY_NAMES = {
    "B11": "function_call_test-mips64-clang-O2",
    "B12": "function_call_test-mips64-clang-O3",
}


def _expected_reason_record(movement_id: str) -> Dict[str, Any]:
    return {
        "id": movement_id,
        "count_kind": UnknownCountKind.REASON_RECORD.value,
        "tuple": list(UNRESOLVED_REASON_TUPLE),
        "aggregation_unit": "pair",
        "stage": "S_PAIRWISE",
        "pair_or_case": MISSING_SENTINEL,
        "expected_evidence_refs": ["pairwise_unresolved_case_labels"],
        "expected_evidence_kind": UNRESOLVED_EVIDENCE_KIND,
        "required_object_target_kind": "unresolved_expression",
        "require_proof_obligation_id": False,
    }


DEFAULT_REPRESENTATIVES: Tuple[Mapping[str, Any], ...] = (
    {
        "id": "representative-unresolved-expression-is-even-recursive-summary-current-transition",
        "category": "function_call",
        "function": "fc_is_even",
        "binary_pair": "B11_B12",
        "expected_observed_binary1_name": FUNCTION_CALL_BINARY_NAMES["B11"],
        "expected_observed_binary2_name": FUNCTION_CALL_BINARY_NAMES["B12"],
        "required_reason_ids": ["unresolved_expression"],
        "role": "recursive-summary guard unresolved-expression current-transition diagnostic",
        "expected_movements": [
            _expected_reason_record("unresolved-expression-reason-record"),
        ],
    },
)


def build_phase3_unresolved_expression_lane6_manifest(
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
        "manifest_kind": "phase3_unresolved_expression_lane6_representatives",
        "artifact_role": "derived_audit_object_evidence_gate",
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
                "Phase 3 lane order target reason unresolved_expression",
                "current reason records preserve conservative UNKNOWN",
                "object_target_key is derived from return cases, guards, and expression provenance",
            ],
        },
        "phase3_lane6_ready": readiness["ready"],
        "readiness": readiness,
        "entries": entries,
        "implementation_manifest": _implementation_manifest(entries),
    }
    path = output / "unresolved_expression_lane6_representatives.json"
    _write_json(path, manifest)
    return path


def validate_phase3_unresolved_expression_lane6_manifest(manifest: Mapping[str, Any]) -> None:
    readiness = manifest.get("readiness")
    failures = []
    if isinstance(readiness, Mapping):
        failures.extend(readiness.get("failed_checks") or ())
        failures.extend(
            _failed(str(kind))
            for kind in (readiness.get("failed_kinds") or ())
            if kind not in {check.get("kind") for check in failures if isinstance(check, Mapping)}
        )
    else:
        failures.append(_failed("unresolved_expression_readiness_missing"))
    if manifest.get("manifest_kind") != "phase3_unresolved_expression_lane6_representatives":
        failures.append(_failed("unresolved_expression_manifest_kind"))
    if not manifest.get("phase3_lane6_ready"):
        failures.append(_failed("unresolved_expression_manifest_not_ready"))
    if failures:
        raise ValueError(f"Phase 3 lane 6 manifest is not ready: {failures!r}")


def build_phase3_unresolved_expression_lane6_post_fix_gate(
    *,
    baseline_raw_dir: Path,
    output_dir: Path,
    current_log_roots: Mapping[str, Path],
    baseline_log_roots: Mapping[str, Path],
    phase3_manifest_path: Path,
    phase3_manifest_sha256: Optional[str],
) -> Path:
    raw_dir = Path(baseline_raw_dir)
    output = Path(output_dir)
    output.mkdir(parents=True, exist_ok=True)
    baseline_manifest = _read_json(raw_dir / "artifact_manifest.json")
    phase3_manifest_path = Path(phase3_manifest_path)
    phase3_manifest = _read_json(phase3_manifest_path)
    phase3_sha = _sha256_file(phase3_manifest_path)
    target_keys = tuple(_entry_key(entry) for entry in phase3_manifest.get("entries") or ())
    current_records = _records_by_key(current_log_roots, target_keys=target_keys)
    all_current_records = _records_by_key(current_log_roots)
    extra_current_observations = _extra_current_unresolved_expression_observations_from_records(
        all_current_records,
        manifest_keys=target_keys,
    )
    entries = [
        _materialize_post_fix_entry(entry, current_records)
        for entry in phase3_manifest.get("entries") or ()
    ]
    checks = _post_fix_checks(
        baseline_manifest=baseline_manifest,
        phase3_manifest=phase3_manifest,
        phase3_manifest_path=phase3_manifest_path,
        actual_phase3_sha256=phase3_sha,
        expected_phase3_sha256=phase3_manifest_sha256,
        entries=entries,
    )
    manifest = {
        "manifest_version": MANIFEST_VERSION,
        "manifest_kind": "phase3_unresolved_expression_lane6_post_fix_gate",
        "artifact_role": "derived_audit_post_fix_gate",
        "baseline_id": baseline_manifest.get("baseline_id") or MISSING_SENTINEL,
        "baseline_git_head": baseline_manifest.get("git_head") or MISSING_SENTINEL,
        "created_at": datetime.now(timezone.utc).isoformat(),
        "target_reason_ids": list(TARGET_REASON_IDS),
        "baseline_raw_artifact_ref": _file_ref(raw_dir / "artifact_manifest.json"),
        "phase3_manifest_ref": _file_ref(phase3_manifest_path),
        "phase3_manifest_sha256": phase3_sha,
        "expected_phase3_manifest_sha256": phase3_manifest_sha256 or MISSING_SENTINEL,
        "current_log_roots": {
            category: _display_path(path) for category, path in sorted(current_log_roots.items())
        },
        "baseline_log_roots": {
            category: _display_path(path) for category, path in sorted(baseline_log_roots.items())
        },
        "phase3_lane6_post_fix_ready": not any(check.get("status") == "failed" for check in checks),
        "post_fix_summary": {
            "failed_kinds": [
                check.get("kind")
                for check in checks
                if isinstance(check, Mapping) and check.get("status") == "failed"
            ],
            "extra_current_unresolved_expression_count": len(extra_current_observations),
            "entry_statuses": [
                {
                    "id": entry.get("id"),
                    "function": entry.get("function"),
                    "binary_pair": entry.get("binary_pair"),
                    "post_fix_status": entry.get("post_fix_status"),
                    "post_fix_failures": entry.get("post_fix_failures") or [],
                }
                for entry in entries
            ],
        },
        "checks": checks,
        "entries": entries,
        "extra_current_unresolved_expression_observations": extra_current_observations,
    }
    path = output / "unresolved_expression_lane6_post_fix_gate.json"
    _write_json(path, manifest)
    return path


def validate_phase3_unresolved_expression_lane6_post_fix_gate(manifest: Mapping[str, Any]) -> None:
    checks = manifest.get("checks")
    failures = []
    if isinstance(checks, list):
        failures.extend(
            check
            for check in checks
            if isinstance(check, Mapping) and check.get("status") == "failed"
        )
    else:
        failures.append(_failed("unresolved_expression_post_fix_checks_missing"))
    if manifest.get("manifest_kind") != "phase3_unresolved_expression_lane6_post_fix_gate":
        failures.append(_failed("unresolved_expression_post_fix_manifest_kind"))
    if not manifest.get("phase3_lane6_post_fix_ready"):
        failures.append(_failed("unresolved_expression_post_fix_not_ready"))
    if failures:
        raise ValueError(f"Phase 3 lane 6 post-fix gate is not ready: {failures!r}")


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
    entry["required_completion_actions"] = (
        _required_completion_actions(entry) if status == "pending_proof" else []
    )
    entry["pending_proof_obligations"] = (
        _pending_proof_obligations(entry) if status == "pending_proof" else []
    )
    return entry


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
            "reason_record_tuples": [],
        }
    payload = record.get("payload") if isinstance(record.get("payload"), Mapping) else {}
    reasons = _extract_final_unknown_reasons(payload)
    reason_records = [_reason_to_dict(reason) for reason in reasons]
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
        "reason_record_tuples": [
            list(_global_reason_tuple_from_record(reason, UnknownCountKind.REASON_RECORD.value))
            for reason in reasons
        ],
        "reason_records": reason_records,
        "proof_actions": [
            action.to_dict()
            for action in build_unknown_recovery_actions(reasons)
        ],
    }


def _extra_current_unresolved_expression_observations_from_records(
    records: Mapping[Tuple[str, str, str], Mapping[str, Any]],
    *,
    manifest_keys: Sequence[Tuple[str, str, str]],
) -> Sequence[Dict[str, Any]]:
    manifest_key_set = set(manifest_keys or ())
    observations: list[Dict[str, Any]] = []
    for key, record in sorted(records.items(), key=lambda item: item[0]):
        if key in manifest_key_set:
            continue
        category, function, binary_pair = key
        observation = _observation(
            {
                "category": category,
                "function": function,
                "binary_pair": binary_pair,
            },
            record,
        )
        unresolved_records = [
            reason
            for reason in observation.get("reason_records") or ()
            if isinstance(reason, Mapping) and reason.get("reason_id") == "unresolved_expression"
        ]
        if observation.get("final_result") != STATUS_UNKNOWN or not unresolved_records:
            continue
        observations.append(
            {
                "category": category,
                "function": function,
                "binary_pair": binary_pair,
                "log_path": observation.get("log_path") or MISSING_SENTINEL,
                "final_result": observation.get("final_result") or MISSING_SENTINEL,
                "unresolved_expression_reason_record_count": len(unresolved_records),
                "observed_reason_ids": list(observation.get("observed_reason_ids") or ()),
            }
        )
    return tuple(observations)


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
        "evidence_refs": list(reason.evidence_refs or ()),
        "object_target_key": _jsonable(reason.object_target_key),
        "proof_obligation_id": _jsonable(reason.proof_obligation_id),
        "action_status": reason.action_status,
        "tuple": list(_global_reason_tuple_from_record(reason, UnknownCountKind.REASON_RECORD.value)),
    }


def _readiness(entries: Sequence[Mapping[str, Any]]) -> Dict[str, Any]:
    checks = []
    for entry in entries:
        checks.extend(_entry_readiness(entry))
    return {
        "ready": not any(check.get("status") == "failed" for check in checks),
        "failed_kinds": [
            check.get("kind")
            for check in checks
            if isinstance(check, Mapping) and check.get("status") == "failed"
        ],
        "failed_checks": [
            check
            for check in checks
            if isinstance(check, Mapping) and check.get("status") == "failed"
        ],
        "checks": checks,
        "covered_target_reason_ids": sorted(TARGET_REASON_IDS),
    }


def _entry_readiness(entry: Mapping[str, Any]) -> Sequence[Dict[str, Any]]:
    checks = []
    current = entry.get("current_observation") if isinstance(entry.get("current_observation"), Mapping) else {}
    baseline = entry.get("baseline_observation") if isinstance(entry.get("baseline_observation"), Mapping) else {}
    details = _entry_details(entry)
    if baseline.get("final_result") == STATUS_UNKNOWN:
        checks.append(_ok("unresolved_expression_baseline_unknown", **details))
    else:
        checks.append(_failed("unresolved_expression_baseline_unknown", baseline_result=baseline.get("final_result") or MISSING_SENTINEL, **details))
    if current.get("final_result") == STATUS_UNKNOWN:
        checks.append(_ok("unresolved_expression_current_unknown", **details))
    else:
        checks.append(_failed("unresolved_expression_current_unknown", current_result=current.get("final_result") or MISSING_SENTINEL, **details))
    if _binary_direction_matches(entry, current):
        checks.append(_ok("unresolved_expression_binary_direction", **details))
    else:
        checks.append(
            _failed(
                "unresolved_expression_binary_direction",
                observed_binary1=current.get("observed_binary1_name") or MISSING_SENTINEL,
                observed_binary2=current.get("observed_binary2_name") or MISSING_SENTINEL,
                **details,
            )
        )
    targets = _current_targets(entry)
    checks.append(
        _ok("unresolved_expression_current_targets_present", count=len(targets), **details)
        if targets
        else _failed("unresolved_expression_current_targets_present", count=0, **details)
    )
    if _expected_movements_match_definition(entry):
        checks.append(_ok("unresolved_expression_expected_movements_match_definition", **details))
    else:
        checks.append(
            _failed(
                "unresolved_expression_expected_movements_match_definition",
                expected=_canonical_movements(DEFAULT_REPRESENTATIVES[0]["expected_movements"]),
                actual=_canonical_movements(entry.get("expected_movements")),
                **details,
            )
        )
    return checks


def _post_fix_status(entry: Mapping[str, Any]) -> Tuple[str, Sequence[Dict[str, Any]]]:
    failures: list[Dict[str, Any]] = []
    current = entry.get("current_observation") if isinstance(entry.get("current_observation"), Mapping) else {}
    result = current.get("final_result")
    details = _entry_details(entry)
    if result == STATUS_TIMEOUT:
        failures.append(_failed("unresolved_expression_timeout_regression", **details))
        return "failed", failures
    if result != STATUS_UNKNOWN:
        failures.append(
            _failed(
                "unresolved_expression_unexpected_final_result",
                current_result=result or MISSING_SENTINEL,
                **details,
            )
        )
        return "failed", failures
    frozen_targets = _canonical_targets(entry.get("target_object_keys"))
    current_targets = _canonical_targets(_current_targets(entry))
    if (
        _unresolved_expression_targets_cleared_under_other_unknown(
            entry,
            frozen_targets=frozen_targets,
            current_targets=current_targets,
        )
    ):
        return "resolved_under_other_conservative_unknown", ()
    if not frozen_targets or current_targets != frozen_targets:
        failures.append(
            _failed(
                "unresolved_expression_target_set_changed",
                expected=frozen_targets,
                actual=current_targets,
                **details,
            )
        )
    if failures:
        return "failed", failures
    if _unresolved_expression_proof_actions_complete(entry, current_targets):
        return "pending_proof", ()
    return "pending_object_evidence", ()


def _post_fix_checks(
    *,
    baseline_manifest: Mapping[str, Any],
    phase3_manifest: Mapping[str, Any],
    phase3_manifest_path: Path,
    actual_phase3_sha256: str,
    expected_phase3_sha256: Optional[str],
    entries: Sequence[Mapping[str, Any]],
) -> Sequence[Dict[str, Any]]:
    checks: list[Dict[str, Any]] = []
    if baseline_manifest.get("baseline_id") == "observed-v0@0a53352":
        checks.append(_ok("baseline_id"))
    else:
        checks.append(_failed("baseline_id", actual=baseline_manifest.get("baseline_id")))
    if expected_phase3_sha256 and actual_phase3_sha256 == expected_phase3_sha256:
        checks.append(_ok("phase3_pre_fix_manifest_sha256"))
    else:
        checks.append(
            _failed(
                "phase3_pre_fix_manifest_sha256",
                expected=expected_phase3_sha256 or MISSING_SENTINEL,
                actual=actual_phase3_sha256,
                path=str(phase3_manifest_path),
            )
        )
    if phase3_manifest.get("manifest_kind") == "phase3_unresolved_expression_lane6_representatives":
        checks.append(_ok("phase3_pre_fix_manifest_kind"))
    else:
        checks.append(_failed("phase3_pre_fix_manifest_kind"))
    try:
        validate_phase3_unresolved_expression_lane6_manifest(phase3_manifest)
    except ValueError as exc:
        checks.append(_failed("phase3_pre_fix_manifest_ready", error=str(exc)))
    else:
        checks.append(_ok("phase3_pre_fix_manifest_ready"))
    checks.append(_identity_set_check("phase3_pre_fix_entries", phase3_manifest.get("entries"), DEFAULT_REPRESENTATIVES))
    implementation = phase3_manifest.get("implementation_manifest")
    if isinstance(implementation, Mapping):
        checks.append(_ok("phase3_pre_fix_implementation_manifest_present"))
        expected_targets = _canonical_targets(implementation.get("expected_unresolved_expression_targets"))
        actual_targets = _canonical_targets(
            [
                target
                for entry in phase3_manifest.get("entries") or ()
                for target in (entry.get("target_object_keys") or ())
            ]
        )
        checks.append(
            _ok("phase3_pre_fix_implementation_targets_consistent")
            if expected_targets and expected_targets == actual_targets
            else _failed("phase3_pre_fix_implementation_targets_consistent", expected=expected_targets, actual=actual_targets)
        )
        expected_movements = _canonical_movements(implementation.get("expected_movement_entries"))
        actual_movements = _canonical_movements(
            [
                movement
                for entry in phase3_manifest.get("entries") or ()
                for movement in (entry.get("expected_movements") or ())
            ]
        )
        checks.append(
            _ok("phase3_pre_fix_implementation_movements_consistent")
            if expected_movements and expected_movements == actual_movements
            else _failed("phase3_pre_fix_implementation_movements_consistent", expected=expected_movements, actual=actual_movements)
        )
    else:
        checks.append(_failed("phase3_pre_fix_implementation_manifest_present"))
    for entry in entries:
        for failure in entry.get("post_fix_failures") or ():
            checks.append(failure)
        if entry.get("post_fix_status") in {"pending_object_evidence", "pending_proof"}:
            checks.append(
                _ok(
                    "unresolved_expression_post_fix_expected_movement",
                    post_fix_status=entry.get("post_fix_status"),
                    **_entry_details(entry),
                )
            )
        elif entry.get("post_fix_status") == "resolved_under_other_conservative_unknown":
            checks.append(
                _ok(
                    "unresolved_expression_post_fix_expected_movement",
                    post_fix_status=entry.get("post_fix_status"),
                    **_entry_details(entry),
                )
            )
        else:
            checks.append(
                _failed(
                    "unresolved_expression_post_fix_expected_movement",
                    post_fix_status=entry.get("post_fix_status") or MISSING_SENTINEL,
                    **_entry_details(entry),
                )
            )
    return checks


def _unresolved_expression_targets_cleared_under_other_unknown(
    entry: Mapping[str, Any],
    *,
    frozen_targets: Sequence[Any],
    current_targets: Sequence[Any],
) -> bool:
    if not frozen_targets or current_targets:
        return False
    current = entry.get("current_observation") if isinstance(entry.get("current_observation"), Mapping) else {}
    observed_reason_ids = tuple(current.get("observed_reason_ids") or ())
    if not observed_reason_ids or "unresolved_expression" in observed_reason_ids:
        return False
    reason_records = tuple(record for record in current.get("reason_records") or () if isinstance(record, Mapping))
    if not reason_records:
        return False
    for record in reason_records:
        if record.get("reason_id") == "unresolved_expression":
            return False
    for action in current.get("proof_actions") or ():
        if isinstance(action, Mapping) and action.get("reason_id") == "unresolved_expression":
            return False
    return True


def _implementation_manifest(entries: Sequence[Mapping[str, Any]]) -> Dict[str, Any]:
    return {
        "lane_id": "phase3_unresolved_expression_lane6",
        "target_reason_id": "unresolved_expression",
        "baseline_mode": "pending_object_evidence_against_pre_fix_manifest",
        "expected_movement_entries": _canonical_movements(
            [
                movement
                for entry in entries
                for movement in (entry.get("expected_movements") or ())
            ]
        ),
        "expected_unresolved_expression_targets": _canonical_targets(
            [
                target
                for entry in entries
                for target in (entry.get("target_object_keys") or ())
            ]
        ),
    }


def _unresolved_expression_proof_actions_complete(
    entry: Mapping[str, Any],
    current_targets: Sequence[Any],
) -> bool:
    target_keys = {_canonical_json(target) for target in current_targets}
    if not target_keys:
        return False
    stages_by_target: Dict[str, set[str]] = {target_key: set() for target_key in target_keys}
    current = entry.get("current_observation") if isinstance(entry.get("current_observation"), Mapping) else {}
    for action in current.get("proof_actions") or ():
        if not isinstance(action, Mapping):
            continue
        if action.get("reason_id") != "unresolved_expression":
            continue
        if action.get("proof_kind") != UNRESOLVED_PROOF_KIND:
            continue
        stage = action.get("proof_stage")
        if stage not in UNRESOLVED_PROOF_STAGES:
            continue
        if action.get("status") not in {"planned", "pending_proof"}:
            continue
        if not action.get("required_evidence"):
            continue
        proof_obligation_id = action.get("proof_obligation_id")
        if proof_obligation_id is None or _nested_contains_missing_sentinel(proof_obligation_id):
            continue
        target = action.get("object_target_key")
        if not _object_target_key_is_specific_unresolved_expression(target):
            continue
        target_key = _canonical_json(target)
        if target_key not in stages_by_target:
            continue
        stages_by_target[target_key].add(str(stage))
    return all(
        stages == set(_required_unresolved_proof_stages_for_target(target))
        for target in current_targets
        for target_key, stages in ((_canonical_json(target), stages_by_target[_canonical_json(target)]),)
    )


def _required_unresolved_proof_stages_for_target(target: Any) -> Tuple[str, ...]:
    if _target_contains_originated_phi_circular(target):
        return UNRESOLVED_PHI_CIRCULAR_PROOF_STAGES
    return UNRESOLVED_GENERIC_PROOF_STAGES


def _target_contains_originated_phi_circular(value: Any) -> bool:
    normalized = _normalize_nested_tuple(value)
    if isinstance(normalized, tuple):
        if (
            len(normalized) >= 6
            and normalized[0] == "opaque_unknown"
            and normalized[1] == "phi_circular"
            and normalized[4] == "multiequal_pcode_op"
            and normalized[5] is not None
        ):
            return True
        return any(_target_contains_originated_phi_circular(item) for item in normalized)
    if isinstance(normalized, dict):
        return any(
            _target_contains_originated_phi_circular(key)
            or _target_contains_originated_phi_circular(item)
            for key, item in normalized.items()
        )
    return False


def _pending_proof_obligations(entry: Mapping[str, Any]) -> Sequence[Dict[str, Any]]:
    target_keys = {_canonical_json(target) for target in _canonical_targets(entry.get("target_object_keys"))}
    obligations = []
    for action in _current_unresolved_expression_actions(entry):
        target_key = _canonical_json(action.get("object_target_key"))
        if target_key not in target_keys:
            continue
        obligations.append(
            {
                "reason_id": action.get("reason_id") or MISSING_SENTINEL,
                "proof_kind": action.get("proof_kind") or MISSING_SENTINEL,
                "proof_stage": action.get("proof_stage") or MISSING_SENTINEL,
                "evidence_kind": action.get("evidence_kind") or MISSING_SENTINEL,
                "required_evidence": list(action.get("required_evidence") or ()),
                "proof_obligation_id": _jsonable(action.get("proof_obligation_id")),
                "completed_evidence_present": False,
                "status": "pending_evidence",
            }
        )
    return tuple(sorted(obligations, key=_canonical_json))


def _required_completion_actions(entry: Mapping[str, Any]) -> Sequence[Dict[str, Any]]:
    actions = []
    for action in _current_unresolved_expression_actions(entry):
        actions.append(
            {
                "count_kind": action.get("count_kind") or UnknownCountKind.PROOF_ACTION.value,
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
            }
        )
    return tuple(sorted(actions, key=_canonical_json))


def _current_unresolved_expression_actions(entry: Mapping[str, Any]) -> Sequence[Mapping[str, Any]]:
    current = entry.get("current_observation") if isinstance(entry.get("current_observation"), Mapping) else {}
    actions = []
    for action in current.get("proof_actions") or ():
        if not isinstance(action, Mapping):
            continue
        if action.get("reason_id") != "unresolved_expression":
            continue
        if action.get("proof_kind") != UNRESOLVED_PROOF_KIND:
            continue
        if action.get("proof_stage") not in UNRESOLVED_PROOF_STAGES:
            continue
        if action.get("status") not in {"planned", "pending_proof"}:
            continue
        if not action.get("required_evidence"):
            continue
        proof_obligation_id = action.get("proof_obligation_id")
        if proof_obligation_id is None or _nested_contains_missing_sentinel(proof_obligation_id):
            continue
        target = action.get("object_target_key")
        if not _object_target_key_is_specific_unresolved_expression(target):
            continue
        actions.append(action)
    return tuple(actions)


def _current_targets(entry: Any) -> Sequence[Any]:
    current = entry.get("current_observation") if isinstance(entry, Mapping) else None
    if not isinstance(current, Mapping):
        return ()
    targets = []
    for record in current.get("reason_records") or ():
        if not isinstance(record, Mapping) or record.get("reason_id") != "unresolved_expression":
            continue
        if record.get("evidence_kind") != UNRESOLVED_EVIDENCE_KIND:
            continue
        target = record.get("object_target_key")
        if _object_target_key_is_specific_unresolved_expression(target):
            targets.append(target)
    return tuple(targets)


def _expected_movements_match_definition(entry: Mapping[str, Any]) -> bool:
    return _canonical_movements(entry.get("expected_movements")) == _canonical_movements(
        DEFAULT_REPRESENTATIVES[0]["expected_movements"]
    )


def _object_target_key_is_specific_unresolved_expression(value: Any) -> bool:
    target = _normalize_nested_tuple(value)
    if not isinstance(target, tuple) or len(target) != 4 or target[0] != "unresolved_expression":
        return False
    if _nested_contains_diagnostic_reason(target):
        return False
    pair = target[1]
    if not (
        isinstance(pair, tuple)
        and len(pair) == 2
        and pair[0] == "pair"
        and _text_identity_is_specific(pair[1])
    ):
        return False
    left_ok = _unresolved_expression_side_is_specific(target[2], "left")
    right_ok = _unresolved_expression_side_is_specific(target[3], "right")
    return left_ok and right_ok and (
        _side_has_unresolved_locations(target[2])
        or _side_has_unresolved_locations(target[3])
    )


def _unresolved_expression_side_is_specific(value: Any, expected_side: str) -> bool:
    side = _normalize_nested_tuple(value)
    if not isinstance(side, tuple) or len(side) != 6:
        return False
    if side[0] != "unresolved_expression_side" or side[1] != expected_side:
        return False
    return_storage = side[3]
    width = _return_storage_width(return_storage)
    return (
        _analysis_entry_key_is_specific(side[2])
        and _return_storage_is_specific(return_storage)
        and _unresolved_return_case_partition_member_is_specific(side[4], width)
        and _unresolved_locations_are_specific(side[5])
    )


def _side_has_unresolved_locations(value: Any) -> bool:
    side = _normalize_nested_tuple(value)
    return (
        isinstance(side, tuple)
        and len(side) == 6
        and isinstance(side[5], tuple)
        and len(side[5]) == 2
        and isinstance(side[5][1], tuple)
        and bool(side[5][1])
    )


def _return_storage_width(value: Any) -> int:
    storage = _normalize_nested_tuple(value)
    if isinstance(storage, tuple) and len(storage) >= 3 and _nonnegative_int_like(storage[2]):
        width = int(storage[2])
        if width > 0:
            return width
    return -1


def _return_storage_is_specific(value: Any) -> bool:
    storage = _normalize_nested_tuple(value)
    return (
        isinstance(storage, tuple)
        and len(storage) >= 5
        and storage[0] == "return_storage"
        and storage[1] == "return_value"
        and _return_storage_width(storage) > 0
        and _text_identity_is_specific(storage[4])
    )


def _unresolved_return_case_partition_member_is_specific(value: Any, expected_return_size: int) -> bool:
    member = _normalize_nested_tuple(value)
    if not isinstance(member, tuple) or len(member) < 6 or member[0] != "return_case_partition_member":
        return False
    member_index = member[1]
    source_indices = member[2]
    return_case = member[3]
    comparison_surface = member[4]
    value_evidence = member[5]
    return (
        _nonnegative_int_like(member_index)
        and _source_indices_are_specific(source_indices)
        and _unresolved_return_case_key_is_specific(return_case, expected_member_index=member_index)
        and _comparison_surface_key_is_specific(comparison_surface, expected_return_size)
        and _return_value_evidence_is_specific(value_evidence)
    )


def _source_indices_are_specific(value: Any) -> bool:
    return isinstance(value, tuple) and bool(value) and all(_nonnegative_int_like(item) for item in value)


def _unresolved_return_case_key_is_specific(value: Any, *, expected_member_index: Any) -> bool:
    return_case = _normalize_nested_tuple(value)
    if not isinstance(return_case, tuple) or len(return_case) < 8 or return_case[0] != "return_case":
        return False
    case_index = return_case[1]
    address = return_case[2]
    pcode_ref = return_case[3]
    pcode_identity = return_case[4]
    return_ordinal = return_case[5]
    return_value = return_case[6]
    guards = return_case[7]
    return (
        _nonnegative_int_like(case_index)
        and int(case_index) == int(expected_member_index)
        and _text_identity_is_specific(address)
        and _pcode_ref_is_specific(pcode_ref)
        and _text_identity_is_specific(pcode_identity)
        and _nonnegative_int_like(return_ordinal)
        and _expression_provenance_is_specific(return_value)
        and _return_guards_are_specific(guards)
    )


def _pcode_ref_is_specific(value: Any) -> bool:
    ref = _normalize_nested_tuple(value)
    if not isinstance(ref, tuple) or len(ref) != 8 or ref[0] != "pcode_op":
        return False
    return (
        _text_identity_is_specific(ref[1])
        and _pcode_address_ref_is_specific(ref[2], "function_entry")
        and _pcode_address_ref_is_specific(ref[3], "seq_target")
        and _nonnegative_int_like(ref[4])
        and _nonnegative_int_like(ref[5])
        and _text_identity_is_specific(str(ref[6]))
        and _nonnegative_int_like(ref[7])
    )


def _pcode_address_ref_is_specific(value: Any, expected_kind: str) -> bool:
    address = _normalize_nested_tuple(value)
    return (
        isinstance(address, tuple)
        and len(address) == 3
        and address[0] == expected_kind
        and _text_identity_is_specific(address[1])
        and _nonnegative_int_like(address[2])
    )


def _comparison_surface_key_is_specific(value: Any, expected_return_size: int) -> bool:
    surface = _normalize_nested_tuple(value)
    return (
        isinstance(surface, tuple)
        and len(surface) == 4
        and surface[0] == "comparison_surface"
        and surface[1] == "return_value"
        and _nonnegative_int_like(surface[2])
        and int(surface[2]) == int(expected_return_size)
    )


def _return_value_evidence_is_specific(value: Any) -> bool:
    evidence = _normalize_nested_tuple(value)
    return isinstance(evidence, tuple) and len(evidence) == 2 and evidence[0] == "value" and _expression_provenance_is_specific(evidence[1])


def _return_guards_are_specific(value: Any) -> bool:
    guards = _normalize_nested_tuple(value)
    return isinstance(guards, tuple) and bool(guards) and all(_return_guard_like_key_is_specific(guard) for guard in guards)


def _unresolved_locations_are_specific(value: Any) -> bool:
    locations = _normalize_nested_tuple(value)
    return (
        isinstance(locations, tuple)
        and len(locations) == 2
        and locations[0] == "unresolved_locations"
        and isinstance(locations[1], tuple)
        and all(_unresolved_location_is_specific(item) for item in locations[1])
    )


def _unresolved_location_is_specific(value: Any) -> bool:
    location = _normalize_nested_tuple(value)
    if not isinstance(location, tuple) or len(location) < 3:
        return False
    if location[0] != "unresolved_location":
        return False
    if location[1] == "return_value":
        return (
            len(location) in {4, 5}
            and _unresolved_location_classification_is_specific(location[2], "return_value")
            and _expression_provenance_is_specific(location[3])
            and (
                len(location) == 4
                or _typed_lowering_evidence_is_specific(location[4], "return_value")
            )
        )
    if location[1] == "guard_condition":
        return (
            len(location) in {6, 7}
            and _nonnegative_int_like(location[2])
            and isinstance(location[3], bool)
            and _unresolved_location_classification_is_specific(location[4], "guard_condition")
            and _return_guard_like_key_is_specific(location[5])
            and (
                len(location) == 6
                or _typed_lowering_evidence_is_specific(location[6], "guard_condition")
            )
        )
    return False


def _typed_lowering_evidence_is_specific(value: Any, expected_scope: str) -> bool:
    evidence = _normalize_nested_tuple(value)
    if not isinstance(evidence, tuple) or len(evidence) != 7:
        return False
    if evidence[0] != "typed_lowering_evidence":
        return False
    scope = evidence[1]
    expression_kind = evidence[2]
    expression_bits = evidence[3]
    typed_expression_key = evidence[4]
    unsupported = evidence[5]
    lowering_status = evidence[6]
    return (
        isinstance(scope, tuple)
        and len(scope) == 2
        and scope == ("location_scope", expected_scope)
        and isinstance(expression_kind, tuple)
        and len(expression_kind) == 2
        and expression_kind[0] == "expression_kind"
        and _text_identity_is_specific(expression_kind[1])
        and isinstance(expression_bits, tuple)
        and len(expression_bits) == 2
        and expression_bits[0] == "expression_bits"
        and _nonnegative_int_like(expression_bits[1])
        and isinstance(typed_expression_key, tuple)
        and len(typed_expression_key) == 2
        and typed_expression_key[0] == "typed_expression_key"
        and _expression_provenance_is_specific(typed_expression_key[1])
        and isinstance(unsupported, tuple)
        and len(unsupported) == 2
        and unsupported[0] == "contains_unsupported_smt_ops"
        and unsupported[1] in {True, False}
        and isinstance(lowering_status, tuple)
        and len(lowering_status) == 2
        and lowering_status[0] == "lowering_status"
        and lowering_status[1] in {
            "blocked_unknown_expression",
            "blocked_unsupported_smt_op",
            "blocked_nested_unresolved_expression",
        }
    )


def _unresolved_location_classification_is_specific(value: Any, expected_scope: str) -> bool:
    classification = _normalize_nested_tuple(value)
    if (
        not isinstance(classification, tuple)
        or len(classification) != 5
        or classification[0] != "unresolved_classification"
    ):
        return False
    if _nested_contains_diagnostic_reason(classification) or _nested_contains_missing_sentinel(classification):
        return False
    scope = classification[1]
    kinds = classification[2]
    unknown_refs = classification[3]
    unsupported_ops = classification[4]
    if (
        not isinstance(scope, tuple)
        or len(scope) != 2
        or scope[0] != "location_scope"
        or scope[1] != expected_scope
    ):
        return False
    if (
        not isinstance(kinds, tuple)
        or len(kinds) != 2
        or kinds[0] != "unresolved_kinds"
        or not isinstance(kinds[1], tuple)
        or not kinds[1]
        or not all(_text_identity_is_specific(kind) for kind in kinds[1])
    ):
        return False
    if not _unresolved_unknown_refs_are_specific(unknown_refs):
        return False
    if not _unsupported_smt_ops_are_specific(unsupported_ops):
        return False
    return bool(unknown_refs[1]) or bool(unsupported_ops[1])


def _unresolved_unknown_refs_are_specific(value: Any) -> bool:
    unknown_refs = _normalize_nested_tuple(value)
    if (
        not isinstance(unknown_refs, tuple)
        or len(unknown_refs) != 2
        or unknown_refs[0] != "unknown_refs"
        or not isinstance(unknown_refs[1], tuple)
    ):
        return False
    for ref in unknown_refs[1]:
        normalized = _normalize_nested_tuple(ref)
        if (
            not isinstance(normalized, tuple)
            or len(normalized) != 2
            or normalized[0] not in {"unknown_runtime_ref", "unknown_expression"}
            or not _nested_has_specific_leaf(normalized[1])
        ):
            return False
        if normalized[0] == "unknown_runtime_ref" and not _unknown_runtime_ref_is_specific(normalized[1]):
            return False
    return True


def _unknown_runtime_ref_is_specific(value: Any) -> bool:
    runtime_key = _normalize_nested_tuple(value)
    if not isinstance(runtime_key, tuple) or not runtime_key:
        return False
    if (
        len(runtime_key) >= 2
        and runtime_key[0] == "opaque_unknown"
        and runtime_key[1] == "phi_circular"
    ):
        if len(runtime_key) < 6:
            return False
        origin_kind = runtime_key[4]
        origin_ref = runtime_key[5]
        return (
            origin_kind == "multiequal_pcode_op"
            and _nested_has_specific_leaf(origin_ref)
            and not _nested_contains_missing_sentinel(origin_ref)
        )
    return True


def _unsupported_smt_ops_are_specific(value: Any) -> bool:
    unsupported_ops = _normalize_nested_tuple(value)
    if (
        not isinstance(unsupported_ops, tuple)
        or len(unsupported_ops) != 2
        or unsupported_ops[0] != "unsupported_ops"
        or not isinstance(unsupported_ops[1], tuple)
    ):
        return False
    for op in unsupported_ops[1]:
        normalized = _normalize_nested_tuple(op)
        if (
            not isinstance(normalized, tuple)
            or len(normalized) != 4
            or normalized[0] != "unsupported_smt_op"
            or not _text_identity_is_specific(normalized[1])
            or not _text_identity_is_specific(normalized[2])
        ):
            return False
        opcode = normalized[3]
        if opcode is not None and not _nonnegative_int_like(opcode):
            return False
    return True


def _return_guard_like_key_is_specific(value: Any) -> bool:
    guard = _normalize_nested_tuple(value)
    if not isinstance(guard, tuple) or len(guard) != 4 or guard[0] != "return_guard":
        return False
    return (
        isinstance(guard[1], bool)
        and _condition_structural_key_is_specific(guard[2])
        and _expression_provenance_is_specific(guard[3])
    )


def _expression_provenance_is_specific(value: Any) -> bool:
    node = _normalize_nested_tuple(value)
    if not isinstance(node, tuple) or len(node) < 2:
        return False
    if _nested_contains_diagnostic_reason(node):
        return False
    root = node[0]
    if root == "expression":
        return _expression_node_is_specific(node[1])
    if _nested_contains_missing(node):
        return False
    if root == "storage":
        return _nested_has_specific_leaf(node[1]) and not _nested_contains_missing(node[1])
    if root == "runtime_ref":
        return _nested_has_specific_leaf(node[1]) and not _nested_contains_missing(node[1])
    if root == "expression_digest":
        return len(node) >= 5 and _text_identity_is_specific(node[1]) and _nested_has_specific_leaf(node[4])
    return False


def _condition_structural_key_is_specific(value: Any) -> bool:
    condition = _normalize_nested_tuple(value)
    return (
        isinstance(condition, tuple)
        and len(condition) == 3
        and condition[0] == "condition"
        and _expression_node_is_specific(condition[1])
        and isinstance(condition[2], bool)
    )


def _expression_node_is_specific(value: Any) -> bool:
    node = _normalize_nested_tuple(value)
    if not isinstance(node, tuple) or len(node) < 2 or not _text_identity_is_specific(node[0]):
        return False
    if _nested_contains_diagnostic_reason(node):
        return False
    root = node[0]
    if root in {"const", "literal"}:
        return _const_or_literal_node_is_specific(node)
    if root in {"parameter", "variable"}:
        return _named_value_node_is_specific(node)
    if root == "unknown":
        return _unknown_expression_node_is_specific(node)
    if root == "binary":
        return _binary_expression_node_is_specific(node)
    if root == "unary":
        return _unary_expression_node_is_specific(node)
    if root == "phi":
        return _phi_expression_node_is_specific(node)
    if root == "intrinsic":
        return _intrinsic_expression_node_is_specific(node)
    if root == "memory":
        return _memory_expression_node_is_specific(node)
    if root == "call":
        return _call_expression_node_is_specific(node)
    return False


def _const_or_literal_node_is_specific(value: tuple) -> bool:
    return (
        len(value) == 3
        and _typed_atom_key_is_specific(value[1])
        and _positive_int_like(value[2])
    )


def _named_value_node_is_specific(value: tuple) -> bool:
    return (
        len(value) == 4
        and _text_identity_is_specific(value[1])
        and _typed_atom_key_is_specific(value[2])
        and _positive_int_like(value[3])
    )


def _unknown_expression_node_is_specific(value: tuple) -> bool:
    if len(value) < 4 or not _nonnegative_int_like(value[3]):
        return False
    name = value[1]
    metadata = value[4:]
    return _text_identity_is_specific(name) or any(
        _unknown_metadata_is_specific(item) for item in metadata
    )


def _unknown_metadata_is_specific(value: Any) -> bool:
    normalized = _normalize_nested_tuple(value)
    if not isinstance(normalized, tuple) or not normalized:
        return False
    if _nested_contains_diagnostic_reason(normalized) or _nested_contains_missing(normalized):
        return False
    root = normalized[0]
    if root == "runtime_ref":
        return len(normalized) == 2 and _nested_has_specific_leaf(normalized[1])
    if root == "stable_runtime_ref":
        return _nested_has_specific_leaf(normalized)
    if root in {"storage", "expression_digest"}:
        return _nested_has_specific_leaf(normalized)
    return False


def _binary_expression_node_is_specific(value: tuple) -> bool:
    return (
        len(value) == 5
        and _text_identity_is_specific(value[1])
        and _positive_int_like(value[2])
        and _expression_node_is_specific(value[3])
        and _expression_node_is_specific(value[4])
    )


def _unary_expression_node_is_specific(value: tuple) -> bool:
    return (
        len(value) == 4
        and _text_identity_is_specific(value[1])
        and _positive_int_like(value[2])
        and _expression_node_is_specific(value[3])
    )


def _phi_expression_node_is_specific(value: tuple) -> bool:
    if len(value) != 3 or not _positive_int_like(value[1]):
        return False
    branches = _normalize_nested_tuple(value[2])
    if not isinstance(branches, tuple) or not branches:
        return False
    for branch in branches:
        branch = _normalize_nested_tuple(branch)
        if not isinstance(branch, tuple) or len(branch) != 2:
            return False
        condition, branch_value = branch
        if not (
            _phi_condition_key_is_specific(condition)
            and _expression_node_is_specific(branch_value)
        ):
            return False
    return True


def _phi_condition_key_is_specific(value: Any) -> bool:
    condition = _normalize_nested_tuple(value)
    if condition == ("none",):
        return True
    return (
        isinstance(condition, tuple)
        and len(condition) == 3
        and condition[0] == "cond"
        and _expression_node_is_specific(condition[1])
        and isinstance(condition[2], bool)
    )


def _intrinsic_expression_node_is_specific(value: tuple) -> bool:
    opcode = value[2] if len(value) >= 3 else None
    args = _normalize_nested_tuple(value[4]) if len(value) >= 5 else None
    return (
        len(value) == 5
        and _text_identity_is_specific(value[1])
        and (opcode is None or _nonnegative_int_like(opcode))
        and _positive_int_like(value[3])
        and _expression_node_sequence_is_specific(args)
    )


def _memory_expression_node_is_specific(value: tuple) -> bool:
    read_order = value[3] if len(value) >= 4 else None
    return (
        len(value) >= 4
        and _positive_int_like(value[1])
        and _expression_node_is_specific(value[2])
        and isinstance(read_order, tuple)
        and len(read_order) == 2
        and read_order[0] == "read_order"
        and _nonnegative_int_like(read_order[1])
    )


def _call_expression_node_is_specific(value: tuple) -> bool:
    args = _normalize_nested_tuple(value[3]) if len(value) >= 4 else None
    return (
        len(value) == 4
        and _call_callee_key_is_specific(_normalize_nested_tuple(value[1]))
        and _positive_int_like(value[2])
        and _expression_node_sequence_is_specific(args)
    )


def _expression_node_sequence_is_specific(value: Any) -> bool:
    return isinstance(value, tuple) and all(_expression_node_is_specific(item) for item in value)


def _positive_int_like(value: Any) -> bool:
    if isinstance(value, bool) or value is None:
        return False
    try:
        return int(value) > 0
    except (TypeError, ValueError):
        return False


def _binary_direction_matches(entry: Mapping[str, Any], current: Mapping[str, Any]) -> bool:
    expected1 = entry.get("expected_observed_binary1_name")
    expected2 = entry.get("expected_observed_binary2_name")
    return (
        (not expected1 or current.get("observed_binary1_name") == expected1)
        and (not expected2 or current.get("observed_binary2_name") == expected2)
    )


def main(argv: Optional[Sequence[str]] = None) -> int:
    parser = argparse.ArgumentParser(description="Validate Phase 3 lane 6 unresolved_expression representatives.")
    parser.add_argument("--gate-stage", choices=("pre-fix", "post-fix"), default="pre-fix")
    parser.add_argument("--baseline-raw-dir", type=Path, required=True)
    parser.add_argument("--output-dir", type=Path, required=True)
    parser.add_argument("--current-log-root", action="append", default=[])
    parser.add_argument("--baseline-log-root", action="append", default=[])
    parser.add_argument("--phase3-manifest", type=Path)
    parser.add_argument("--phase3-manifest-sha256")
    parser.add_argument("--require-ready", action="store_true")
    args = parser.parse_args(argv)
    current_roots = _parse_roots(args.current_log_root)
    baseline_roots = _parse_roots(args.baseline_log_root)
    if args.gate_stage == "post-fix":
        if args.phase3_manifest is None:
            raise SystemExit("--phase3-manifest is required for post-fix")
        path = build_phase3_unresolved_expression_lane6_post_fix_gate(
            baseline_raw_dir=args.baseline_raw_dir,
            output_dir=args.output_dir,
            current_log_roots=current_roots,
            baseline_log_roots=baseline_roots,
            phase3_manifest_path=args.phase3_manifest,
            phase3_manifest_sha256=args.phase3_manifest_sha256,
        )
        if args.require_ready:
            validate_phase3_unresolved_expression_lane6_post_fix_gate(_read_json(path))
    else:
        path = build_phase3_unresolved_expression_lane6_manifest(
            baseline_raw_dir=args.baseline_raw_dir,
            output_dir=args.output_dir,
            current_log_roots=current_roots,
            baseline_log_roots=baseline_roots,
        )
        if args.require_ready:
            validate_phase3_unresolved_expression_lane6_manifest(_read_json(path))
    print(path)
    return 0


if __name__ == "__main__":  # pragma: no cover
    raise SystemExit(main())
