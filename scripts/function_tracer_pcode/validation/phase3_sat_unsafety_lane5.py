# -*- coding: utf-8 -*-
"""Freeze Phase 3 lane 5 representatives for SAT unsafety proof work."""

from __future__ import annotations

import argparse
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Dict, Mapping, Optional, Sequence, Tuple

from .result_summary import STATUS_NOT_EQ, STATUS_TIMEOUT, STATUS_UNKNOWN, classify_result_payload
from .unknown_reason_summary import _global_reason_tuple_from_action, _global_reason_tuple_from_record
from .phase2_equivalence_blocking_unsafety import _object_target_key_is_specific as _call_effect_target_is_specific
from .phase3_return_coverage_lane1 import _return_coverage_key_is_specific
from .phase3_return_width_bridge_lane2 import (
    _canonical_json,
    _canonical_movements,
    _canonical_targets,
    _entry_details,
    _entry_key,
    _entry_map,
    _failed,
    _file_ref,
    _find_tagged_entry,
    _identity_set_check,
    _identity_to_dict,
    _is_positive_int,
    _jsonable,
    _nonnegative_int_like,
    _normalize_nested_tuple,
    _ok,
    _parse_roots,
    _read_json,
    _records_by_key,
    _return_case_partition_member_is_specific,
    _sha256_file,
    _text_identity_is_specific,
    _write_json,
)
from .phase3_readonly_identity_lane3 import (
    _analysis_entry_key_is_specific,
    _completed_evidence_has_active_blocker,
    _completed_recovery_proof_summaries,
    _nested_completed_proof_has_active_blocker,
    _nested_contains_diagnostic_reason,
)
from ..equivalence.unknown_reason import (
    UNKNOWN_TUPLE_MISSING,
    UnknownCountKind,
    build_proof_obligation_id,
    build_unknown_recovery_actions,
    coerce_unknown_recovery_actions,
)


MANIFEST_VERSION = 1
TARGET_REASON_IDS = ("sat_unsafety",)
MISSING_SENTINEL = UNKNOWN_TUPLE_MISSING
SAT_PROOF_KIND = "sat_unsafety_resolution"
SAT_PROOF_STAGE = "sat_counterexample_safety"
SAT_EVIDENCE_KIND = "active_unsafety_summary"
SAT_REQUIRED_EVIDENCE = (
    "counterexample_replay",
    "active_unsafety_discharge",
    "coverage_effect_safety",
)
SAT_REASON_TUPLE = (
    UnknownCountKind.REASON_RECORD.value,
    "sat_unsafety",
    "blocks_disequivalence",
    "pair",
    SAT_PROOF_KIND,
    SAT_PROOF_STAGE,
    "pending_proof",
)
SAT_ACTION_TUPLE = (
    UnknownCountKind.PROOF_ACTION.value,
    "sat_unsafety",
    "blocks_disequivalence",
    "pair",
    SAT_PROOF_KIND,
    SAT_PROOF_STAGE,
    "pending_proof",
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
FUNCTION_CALL_BINARY_NAMES = {
    "B9": "function_call_test-mips64-clang-O0",
    "B10": "function_call_test-mips64-clang-O1",
}


def _expected_reason_record(movement_id: str) -> Dict[str, Any]:
    return {
        "id": movement_id,
        "count_kind": UnknownCountKind.REASON_RECORD.value,
        "tuple": list(SAT_REASON_TUPLE),
        "aggregation_unit": "pair",
        "stage": "S_PAIRWISE",
        "pair_or_case": MISSING_SENTINEL,
        "expected_evidence_refs": ["active_sat_unsafety"],
        "required_object_target_kind": "sat_unsafety",
        "require_proof_obligation_id": True,
    }


def _expected_proof_action(movement_id: str) -> Dict[str, Any]:
    return {
        "id": movement_id,
        "count_kind": UnknownCountKind.PROOF_ACTION.value,
        "tuple": list(SAT_ACTION_TUPLE),
        "aggregation_unit": "pair",
        "stage": "S_PAIRWISE",
        "pair_or_case": MISSING_SENTINEL,
        "expected_evidence_refs": [SAT_EVIDENCE_KIND],
        "required_evidence": list(SAT_REQUIRED_EVIDENCE),
        "required_object_target_kind": "sat_unsafety",
        "require_proof_obligation_id": True,
    }


DEFAULT_REPRESENTATIVES: Tuple[Mapping[str, Any], ...] = (
    {
        "id": "representative-sat-unsafety-is-even-guard",
        "category": "function_call",
        "function": "fc_is_even",
        "binary_pair": "B9_B10",
        "expected_observed_binary1_name": FUNCTION_CALL_BINARY_NAMES["B9"],
        "expected_observed_binary2_name": FUNCTION_CALL_BINARY_NAMES["B10"],
        "required_reason_ids": ["sat_unsafety"],
        "role": "SAT counterexample false-NOT_EQ guard with active coverage/effect unsafety",
        "expected_movements": [
            _expected_reason_record("sat-unsafety-reason-record"),
            _expected_proof_action("sat-unsafety-resolution-proof"),
        ],
    },
)


def build_phase3_sat_unsafety_lane5_manifest(
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
        "manifest_kind": "phase3_sat_unsafety_lane5_representatives",
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
                "Phase 1 negative-sat-unsafety-guard concrete pair",
                "current sat_unsafety record preserves conservative UNKNOWN",
                "object_target_key includes pair, return cases, and active unsafety targets",
            ],
        },
        "phase3_lane5_ready": readiness["ready"],
        "readiness": readiness,
        "entries": entries,
        "implementation_manifest": _implementation_manifest(entries),
    }
    path = output / "sat_unsafety_lane5_representatives.json"
    _write_json(path, manifest)
    return path


def validate_phase3_sat_unsafety_lane5_manifest(manifest: Mapping[str, Any]) -> None:
    failures = list((manifest.get("readiness") or {}).get("failed_checks") or ())
    if manifest.get("manifest_kind") != "phase3_sat_unsafety_lane5_representatives":
        failures.append(_failed("sat_unsafety_manifest_kind"))
    if not manifest.get("phase3_lane5_ready"):
        failures.append(_failed("sat_unsafety_manifest_not_ready"))
    if failures:
        raise ValueError(f"Phase 3 lane 5 manifest is not ready: {failures!r}")


def build_phase3_sat_unsafety_lane5_post_fix_gate(
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
        "manifest_kind": "phase3_sat_unsafety_lane5_post_fix_gate",
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
            category: str(path) for category, path in sorted(current_log_roots.items())
        },
        "baseline_log_roots": {
            category: str(path) for category, path in sorted(baseline_log_roots.items())
        },
        "phase3_lane5_post_fix_ready": not any(check.get("status") == "failed" for check in checks),
        "post_fix_summary": {
            "failed_kinds": [
                check.get("kind")
                for check in checks
                if isinstance(check, Mapping) and check.get("status") == "failed"
            ],
            "not_evaluated_kinds": [
                check.get("kind")
                for check in checks
                if isinstance(check, Mapping) and check.get("status") == "not_evaluated"
            ],
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
    }
    path = output / "sat_unsafety_lane5_post_fix_gate.json"
    _write_json(path, manifest)
    return path


def validate_phase3_sat_unsafety_lane5_post_fix_gate(manifest: Mapping[str, Any]) -> None:
    failures = [
        check
        for check in manifest.get("checks") or ()
        if isinstance(check, Mapping) and check.get("status") == "failed"
    ]
    if manifest.get("manifest_kind") != "phase3_sat_unsafety_lane5_post_fix_gate":
        failures.append(_failed("sat_unsafety_post_fix_manifest_kind"))
    if not manifest.get("phase3_lane5_post_fix_ready"):
        failures.append(_failed("sat_unsafety_post_fix_not_ready"))
    if failures:
        raise ValueError(f"Phase 3 lane 5 post-fix gate is not ready: {failures!r}")


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
    entry["required_completion_actions"] = _canonical_actions(_current_sat_actions(entry))
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
    from .unknown_reason_summary import _extract_final_unknown_reasons

    reasons = _extract_final_unknown_reasons(payload)
    raw_actions = payload.get("unknown_recovery_actions")
    if not isinstance(raw_actions, Sequence) or isinstance(raw_actions, (str, bytes)):
        raw_actions = ()
    actions_with_raw = _merged_recovery_actions(reasons, raw_actions)
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
            for action, _raw_action in actions_with_raw
        ],
        "reason_records": [_reason_to_dict(reason) for reason in reasons],
        "proof_actions": [
            _action_to_dict(action, raw_action)
            for action, raw_action in actions_with_raw
        ],
    }


def _merged_recovery_actions(
    reasons: Sequence[Any],
    raw_actions: Sequence[Any],
) -> Tuple[Tuple[Any, Any], ...]:
    merged: list[Tuple[Any, Any]] = []
    seen: set[Tuple[str, str, str, str, str, str]] = set()
    for raw_action, action in zip(raw_actions, coerce_unknown_recovery_actions(raw_actions)):
        key = _recovery_action_key(action)
        seen.add(key)
        merged.append((action, raw_action))
    for action in build_unknown_recovery_actions(reasons):
        key = _recovery_action_key(action)
        if key in seen:
            continue
        seen.add(key)
        merged.append((action, None))
    return tuple(merged)


def _recovery_action_key(action: Any) -> Tuple[str, str, str, str, str, str]:
    return (
        str(getattr(action, "reason_id", MISSING_SENTINEL)),
        str(getattr(action, "proof_kind", MISSING_SENTINEL)),
        str(getattr(action, "proof_stage", MISSING_SENTINEL)),
        str(getattr(action, "evidence_kind", MISSING_SENTINEL)),
        _canonical_json(_jsonable(getattr(action, "object_target_key", None))),
        _canonical_json(_jsonable(getattr(action, "proof_obligation_id", None))),
    )


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
        "evidence_refs": list(action.evidence_refs or ()),
        "evidence_kind": action.evidence_kind,
        "object_target_key": _jsonable(action.object_target_key),
        "proof_obligation_id": _jsonable(action.proof_obligation_id),
        "raw_object_target_key_present": raw_has_target,
        "raw_proof_obligation_id_present": raw_has_proof_id,
        "tuple": list(_global_reason_tuple_from_action(action)),
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
        checks.append(_ok("sat_unsafety_baseline_unknown", **details))
    else:
        checks.append(
            _failed(
                "sat_unsafety_baseline_unknown",
                baseline_result=baseline.get("final_result") or MISSING_SENTINEL,
                **details,
            )
        )
    if current.get("final_result") == STATUS_UNKNOWN:
        checks.append(_ok("sat_unsafety_current_unknown", **details))
    else:
        checks.append(
            _failed(
                "sat_unsafety_current_unknown",
                current_result=current.get("final_result") or MISSING_SENTINEL,
                **details,
            )
        )
    if _binary_direction_matches(entry, current):
        checks.append(_ok("sat_unsafety_binary_direction", **details))
    else:
        checks.append(
            _failed(
                "sat_unsafety_binary_direction",
                observed_binary1=current.get("observed_binary1_name") or MISSING_SENTINEL,
                observed_binary2=current.get("observed_binary2_name") or MISSING_SENTINEL,
                **details,
            )
        )
    targets = _current_targets(entry)
    checks.append(
        _ok("sat_unsafety_current_targets_present", count=len(targets), **details)
        if targets
        else _failed("sat_unsafety_current_targets_present", count=0, **details)
    )
    missing = _missing_sat_actions(entry)
    checks.append(
        _failed("sat_unsafety_current_actions_complete", missing=missing, **details)
        if missing
        else _ok("sat_unsafety_current_actions_complete", **details)
    )
    if _expected_movements_match_definition(entry):
        checks.append(_ok("sat_unsafety_expected_movements_match_definition", **details))
    else:
        checks.append(
            _failed(
                "sat_unsafety_expected_movements_match_definition",
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
        failures.append(_failed("sat_unsafety_timeout_regression", **details))
        return "failed", failures
    if result == STATUS_NOT_EQ:
        failures.extend(_completed_recovery_failures(entry, current))
        if failures:
            return "failed", failures
        return "completed_recovery", ()
    if result != STATUS_UNKNOWN:
        failures.append(
            _failed(
                "sat_unsafety_unexpected_final_result",
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
                "sat_unsafety_target_set_changed",
                expected=frozen_targets,
                actual=current_targets,
                **details,
            )
        )
    frozen_actions = _canonical_actions(entry.get("required_completion_actions"))
    current_actions = _canonical_actions(_current_sat_actions(entry))
    if not frozen_actions or current_actions != frozen_actions:
        failures.append(
            _failed(
                "sat_unsafety_required_actions_changed",
                expected=frozen_actions,
                actual=current_actions,
                **details,
            )
        )
    missing = _missing_sat_actions(entry)
    if missing:
        failures.append(_failed("sat_unsafety_current_actions_complete", missing=missing, **details))
    if failures:
        return "failed", failures
    return "pending_proof", ()


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
    if phase3_manifest.get("manifest_kind") == "phase3_sat_unsafety_lane5_representatives":
        checks.append(_ok("phase3_pre_fix_manifest_kind"))
    else:
        checks.append(_failed("phase3_pre_fix_manifest_kind"))
    if phase3_manifest.get("phase3_lane5_ready") is True:
        checks.append(_ok("phase3_pre_fix_manifest_ready"))
    else:
        checks.append(_failed("phase3_pre_fix_manifest_ready"))
    checks.append(_identity_set_check("phase3_pre_fix_entries", phase3_manifest.get("entries"), DEFAULT_REPRESENTATIVES))
    implementation = phase3_manifest.get("implementation_manifest")
    if isinstance(implementation, Mapping):
        checks.append(_ok("phase3_pre_fix_implementation_manifest_present"))
        expected_targets = _canonical_targets(implementation.get("expected_sat_unsafety_targets"))
        actual_targets = _canonical_targets(
            [
                target
                for entry in phase3_manifest.get("entries") or ()
                for target in (entry.get("target_object_keys") or ())
            ]
        )
        if expected_targets and expected_targets == actual_targets:
            checks.append(_ok("phase3_pre_fix_implementation_targets_consistent"))
        else:
            checks.append(
                _failed(
                    "phase3_pre_fix_implementation_targets_consistent",
                    expected=expected_targets,
                    actual=actual_targets,
                )
            )
        expected_actions = _canonical_actions(implementation.get("required_completion_actions"))
        actual_actions = _canonical_actions(
            action
            for entry in phase3_manifest.get("entries") or ()
            for action in (entry.get("required_completion_actions") or ())
        )
        if expected_actions and expected_actions == actual_actions:
            checks.append(_ok("phase3_pre_fix_implementation_actions_consistent"))
        else:
            checks.append(
                _failed(
                    "phase3_pre_fix_implementation_actions_consistent",
                    expected=expected_actions,
                    actual=actual_actions,
                )
            )
    else:
        checks.append(_failed("phase3_pre_fix_implementation_manifest_present"))
    for entry in entries:
        for failure in entry.get("post_fix_failures") or ():
            checks.append(failure)
        if entry.get("post_fix_status") in {"pending_proof", "completed_recovery"}:
            checks.append(
                _ok(
                    "sat_unsafety_post_fix_expected_movement",
                    post_fix_status=entry.get("post_fix_status"),
                    **_entry_details(entry),
                )
            )
        else:
            checks.append(
                _failed(
                    "sat_unsafety_post_fix_expected_movement",
                    post_fix_status=entry.get("post_fix_status") or MISSING_SENTINEL,
                    **_entry_details(entry),
                )
            )
    return checks


def _implementation_manifest(entries: Sequence[Mapping[str, Any]]) -> Dict[str, Any]:
    return {
        "lane_id": "phase3_sat_unsafety_lane5",
        "target_reason_id": "sat_unsafety",
        "baseline_mode": "pending_proof_or_completed_not_eq_against_pre_fix_manifest",
        "expected_movement_entries": _canonical_movements(
            movement
            for entry in entries
            for movement in (entry.get("expected_movements") or ())
        ),
        "expected_sat_unsafety_targets": _canonical_targets(
            [
                target
                for entry in entries
                for target in (entry.get("target_object_keys") or ())
            ]
        ),
        "required_completion_actions": _canonical_actions(
            action
            for entry in entries
            for action in (entry.get("required_completion_actions") or ())
        ),
    }


def _current_targets(entry: Any) -> Sequence[Any]:
    current = entry.get("current_observation") if isinstance(entry, Mapping) else None
    if not isinstance(current, Mapping):
        return ()
    targets = []
    for record in current.get("reason_records") or ():
        if not isinstance(record, Mapping) or record.get("reason_id") != "sat_unsafety":
            continue
        target = record.get("object_target_key")
        if _object_target_key_is_specific_sat_unsafety(target):
            targets.append(target)
    return tuple(targets)


def _current_sat_actions(entry: Any) -> Sequence[Mapping[str, Any]]:
    current = entry.get("current_observation") if isinstance(entry, Mapping) else None
    if not isinstance(current, Mapping):
        return ()
    actions = []
    for action in current.get("proof_actions") or ():
        if not isinstance(action, Mapping):
            continue
        if action.get("reason_id") != "sat_unsafety":
            continue
        if not _object_target_key_is_specific_sat_unsafety(action.get("object_target_key")):
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


def _missing_sat_actions(entry: Mapping[str, Any]) -> Sequence[Dict[str, Any]]:
    current_targets = _canonical_targets(_current_targets(entry))
    actions = _current_sat_actions(entry)
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
        key = (_canonical_json(target), SAT_PROOF_KIND, SAT_PROOF_STAGE)
        if key not in action_keys:
            missing.append(
                {
                    "object_target_key": target,
                    "proof_kind": SAT_PROOF_KIND,
                    "proof_stage": SAT_PROOF_STAGE,
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
        failures.append(_failed("sat_unsafety_decision_gated_by_pending_proof", **details))
    active_reasons = [
        reason_id
        for reason_id in current.get("observed_reason_ids") or ()
        if _text_identity_is_specific(reason_id)
    ]
    if active_reasons:
        failures.append(
            _failed(
                "sat_unsafety_active_reason_not_cleared",
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
        failures.append(_failed("sat_unsafety_pending_proof_action_still_active", **details))
    required_actions = _canonical_actions(entry.get("required_completion_actions"))
    if not required_actions:
        failures.append(_failed("sat_unsafety_frozen_proof_actions_missing", **details))
        return failures
    completed = tuple(current.get("completed_recovery_proof_evidence") or ())
    if not completed:
        failures.append(_failed("sat_unsafety_completed_proof_required", **details))
        return failures
    for action in required_actions:
        if not any(_completed_evidence_matches_action(evidence, action) for evidence in completed):
            failures.append(
                _failed(
                    "sat_unsafety_completed_proof_required",
                    proof_stage=action.get("proof_stage") or MISSING_SENTINEL,
                    evidence_kind=action.get("evidence_kind") or MISSING_SENTINEL,
                    proof_kind=action.get("proof_kind") or MISSING_SENTINEL,
                    **details,
                )
            )
    return failures


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
    if not _object_target_key_is_specific_sat_unsafety(object_target_key):
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


def _completed_evidence_has_required_proof_content(
    evidence_summary: Mapping[str, Any],
    evidence: Mapping[str, Any],
    action: Mapping[str, Any],
    object_target_key: Any,
) -> bool:
    if tuple(action.get("required_evidence") or ()) != SAT_REQUIRED_EVIDENCE:
        return False
    content = _completed_proof_content(evidence_summary, evidence)
    if not isinstance(content, Mapping):
        return False
    if _nested_completed_proof_has_active_blocker(content):
        return False
    if (
        content.get("object_derived") is not True
        or _normalize_nested_tuple(content.get("object_target_key")) != _normalize_nested_tuple(object_target_key)
    ):
        return False
    return all(
        _proof_status_value_is_complete(content.get(field))
        for field in SAT_REQUIRED_EVIDENCE
    )


def _completed_proof_content(evidence_summary: Mapping[str, Any], evidence: Mapping[str, Any]) -> Any:
    for container in (evidence_summary, evidence):
        for field_name in ("proof_content", "proof", "proof_evidence"):
            content = container.get(field_name)
            if isinstance(content, Mapping):
                return content
    return None


def _proof_status_value_is_complete(value: Any) -> bool:
    if isinstance(value, Mapping):
        if _nested_completed_proof_has_active_blocker(value):
            return False
        status = str(value.get("status") or "")
        return status in {"complete", "completed", "proven", "discharged", "replayed"} and any(
            key != "status" for key in value
        )
    return False


def _expected_movements_match_definition(entry: Mapping[str, Any]) -> bool:
    expected = _canonical_movements(DEFAULT_REPRESENTATIVES[0]["expected_movements"])
    actual = _canonical_movements(entry.get("expected_movements"))
    return expected == actual


def _canonical_actions(actions: Any) -> Tuple[Dict[str, Any], ...]:
    canonical = []
    for action in actions or ():
        if not isinstance(action, Mapping):
            continue
        canonical.append(
            {
                "count_kind": action.get("count_kind") or UnknownCountKind.PROOF_ACTION.value,
                "reason_id": action.get("reason_id"),
                "decision_effect": action.get("decision_effect"),
                "reason_scope": action.get("reason_scope"),
                "proof_kind": action.get("proof_kind"),
                "proof_stage": action.get("proof_stage"),
                "status": action.get("status"),
                "aggregation_unit": action.get("aggregation_unit"),
                "stage": action.get("stage"),
                "pair_or_case": action.get("pair_or_case"),
                "required_evidence": list(action.get("required_evidence") or ()),
                "evidence_kind": action.get("evidence_kind"),
                "object_target_key": _jsonable(action.get("object_target_key")),
                "proof_obligation_id": _jsonable(action.get("proof_obligation_id")),
            }
        )
    return tuple(sorted(canonical, key=_canonical_json))


def _proof_action_has_expected_id(action: Mapping[str, Any]) -> bool:
    target = _normalize_nested_tuple(action.get("object_target_key"))
    if not _object_target_key_is_specific_sat_unsafety(target):
        return False
    return _normalize_nested_tuple(action.get("proof_obligation_id")) == _expected_proof_obligation_id(
        action,
        object_target_key=target,
    )


def _expected_proof_obligation_id(
    action: Mapping[str, Any],
    *,
    object_target_key: Any,
) -> Tuple[Any, ...]:
    return build_proof_obligation_id(
        "sat_unsafety",
        action.get("proof_stage"),
        action.get("proof_kind"),
        action.get("evidence_kind"),
        object_target_key,
    )


def _proof_action_matches_lane_definition(action: Mapping[str, Any]) -> bool:
    return (
        action.get("count_kind") == UnknownCountKind.PROOF_ACTION.value
        and action.get("reason_id") == "sat_unsafety"
        and action.get("decision_effect") == "blocks_disequivalence"
        and action.get("reason_scope") == "pair"
        and action.get("aggregation_unit") == "pair"
        and action.get("stage") == "S_PAIRWISE"
        and action.get("proof_kind") == SAT_PROOF_KIND
        and action.get("proof_stage") == SAT_PROOF_STAGE
        and action.get("status") in {"planned", "pending_proof"}
        and tuple(action.get("required_evidence") or ()) == SAT_REQUIRED_EVIDENCE
        and action.get("evidence_kind") == SAT_EVIDENCE_KIND
    )


def _object_target_key_is_specific_sat_unsafety(value: Any) -> bool:
    target = _normalize_nested_tuple(value)
    if not isinstance(target, tuple) or len(target) != 5 or target[0] != "sat_unsafety":
        return False
    if _nested_contains_diagnostic_reason(target):
        return False
    pair = target[1]
    active = target[4]
    return (
        isinstance(pair, tuple)
        and len(pair) == 2
        and pair[0] == "pair"
        and _text_identity_is_specific(pair[1])
        and _sat_unsafety_side_is_specific(target[2], "left")
        and _sat_unsafety_side_is_specific(target[3], "right")
        and _active_unsafety_targets_are_specific(active)
    )


def _sat_unsafety_side_is_specific(value: Any, expected_side: str) -> bool:
    side = _normalize_nested_tuple(value)
    if not isinstance(side, tuple) or len(side) != 5:
        return False
    if side[0] != "sat_unsafety_side" or side[1] != expected_side:
        return False
    return_storage = side[3]
    width = _return_storage_width(return_storage)
    return (
        _analysis_entry_key_is_specific(side[2])
        and _return_storage_is_specific(return_storage)
        and _return_case_partition_member_is_specific(side[4], width)
    )


def _return_storage_width(value: Any) -> int:
    storage = _normalize_nested_tuple(value)
    if isinstance(storage, tuple) and len(storage) >= 3 and _is_positive_int(storage[2]):
        return int(storage[2])
    return -1


def _return_storage_is_specific(value: Any) -> bool:
    storage = _normalize_nested_tuple(value)
    return (
        isinstance(storage, tuple)
        and len(storage) >= 5
        and storage[0] == "return_storage"
        and storage[1] == "return_value"
        and _is_positive_int(storage[2])
        and _text_identity_is_specific(storage[4])
    )


def _active_unsafety_targets_are_specific(value: Any) -> bool:
    active = _normalize_nested_tuple(value)
    return (
        isinstance(active, tuple)
        and len(active) == 2
        and active[0] == "active_unsafety"
        and isinstance(active[1], tuple)
        and bool(active[1])
        and all(_active_unsafety_target_is_specific(item) for item in active[1])
    )


def _active_unsafety_target_is_specific(value: Any) -> bool:
    item = _normalize_nested_tuple(value)
    if not isinstance(item, tuple) or len(item) < 4:
        return False
    if item[0] == "coverage_unsafety":
        return (
            len(item) == 4
            and item[1] in {"function1", "function2"}
            and item[2] in {"return_coverage_gap", "return_coverage_inconclusive"}
            and isinstance(item[3], tuple)
            and _return_coverage_key_is_specific(item[3])
        )
    if item[0] == "call_effect_unsafety":
        return (
            len(item) == 4
            and item[1] in {"function1", "function2"}
            and _text_identity_is_specific(item[2])
            and isinstance(item[3], tuple)
            and _call_effect_subtarget_is_specific(item[3])
        )
    if item[0] == "analysis_unsafety":
        return _analysis_unsafety_target_is_specific(item)
    return False


def _call_effect_subtarget_is_specific(value: Any) -> bool:
    target = _normalize_nested_tuple(value)
    if not isinstance(target, tuple) or not target:
        return False
    if target[0] == "call_effect_blocker":
        return (
            len(target) == 8
            and target[1] in {"function1", "function2"}
            and _analysis_entry_key_is_specific(target[2])
            and _text_identity_is_specific(target[3])
            and _call_effect_collection_is_specific(target[5])
            and _call_effect_collection_is_specific(target[6])
            and _call_effect_collection_is_specific(target[7])
        )
    return _call_effect_target_is_specific(target)


def _call_effect_collection_is_specific(value: Any) -> bool:
    normalized = _normalize_nested_tuple(value)
    return isinstance(normalized, tuple) and all(_call_effect_target_is_specific(item) for item in normalized)


def _analysis_unsafety_target_is_specific(value: Tuple[Any, ...]) -> bool:
    if len(value) != 8:
        return False
    (
        _kind,
        side_label,
        reason_kind,
        analysis_key,
        return_storage,
        return_partition,
        guard_disjunction,
        deferred_keys,
    ) = value
    if side_label not in {"function1", "function2"}:
        return False
    if reason_kind not in {
        "unresolved_return_value",
        "symbolic_post_state_reads",
        "effect_sensitive_raw_memory_reads",
        "overlapping_unconditional_returns",
        "incomplete_control_flow",
        "indirect_control_flow_unresolved",
        "effect_summary_path_coverage_incomplete",
        "bounded_call_refinement_argument_alignment_failed",
        "bounded_call_refinement_deferred_target_unresolved",
        "bounded_call_refinement_return_summary_unusable",
        "effect_call_argument_evidence_incomplete",
    }:
        return False
    return (
        _analysis_entry_key_is_specific(analysis_key)
        and _return_storage_is_specific(return_storage)
        and _return_partition_is_specific(return_partition)
        and _guard_disjunction_is_specific(guard_disjunction)
        and isinstance(deferred_keys, tuple)
        and all(_call_effect_target_is_specific(key) for key in deferred_keys)
    )


def _return_partition_is_specific(value: Any) -> bool:
    partition = _normalize_nested_tuple(value)
    if not isinstance(partition, tuple) or len(partition) != 2 or partition[0] != "return_partition":
        return False
    cases = partition[1]
    return isinstance(cases, tuple) and bool(cases) and all(_return_case_is_specific(case) for case in cases)


def _return_case_is_specific(value: Any) -> bool:
    case = _normalize_nested_tuple(value)
    if not isinstance(case, tuple) or len(case) < 8 or case[0] != "return_case":
        return False
    return _nonnegative_int_like(case[1]) and _text_identity_is_specific(case[2]) and case[3] is not None


def _guard_disjunction_is_specific(value: Any) -> bool:
    guard = _normalize_nested_tuple(value)
    return (
        isinstance(guard, tuple)
        and len(guard) == 2
        and guard[0] == "guard_disjunction"
        and isinstance(guard[1], tuple)
    )


def _binary_direction_matches(entry: Mapping[str, Any], current: Mapping[str, Any]) -> bool:
    expected1 = entry.get("expected_observed_binary1_name")
    expected2 = entry.get("expected_observed_binary2_name")
    return (
        (not expected1 or current.get("observed_binary1_name") == expected1)
        and (not expected2 or current.get("observed_binary2_name") == expected2)
    )


def main(argv: Optional[Sequence[str]] = None) -> int:
    parser = argparse.ArgumentParser(description="Validate Phase 3 lane 5 sat_unsafety representatives.")
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
        path = build_phase3_sat_unsafety_lane5_post_fix_gate(
            baseline_raw_dir=args.baseline_raw_dir,
            output_dir=args.output_dir,
            current_log_roots=current_roots,
            baseline_log_roots=baseline_roots,
            phase3_manifest_path=args.phase3_manifest,
            phase3_manifest_sha256=args.phase3_manifest_sha256,
        )
        if args.require_ready:
            validate_phase3_sat_unsafety_lane5_post_fix_gate(_read_json(path))
    else:
        path = build_phase3_sat_unsafety_lane5_manifest(
            baseline_raw_dir=args.baseline_raw_dir,
            output_dir=args.output_dir,
            current_log_roots=current_roots,
            baseline_log_roots=baseline_roots,
        )
        if args.require_ready:
            validate_phase3_sat_unsafety_lane5_manifest(_read_json(path))
    print(path)
    return 0


if __name__ == "__main__":  # pragma: no cover
    raise SystemExit(main())
