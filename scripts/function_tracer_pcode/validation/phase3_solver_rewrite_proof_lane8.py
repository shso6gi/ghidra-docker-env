# -*- coding: utf-8 -*-
"""Freeze Phase 3 lane 8 representatives for solver rewrite proof recheck."""

from __future__ import annotations

import argparse
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Dict, Mapping, Optional, Sequence, Tuple

from .result_summary import STATUS_TIMEOUT, STATUS_UNKNOWN, classify_result_payload
from .unknown_reason_summary import _extract_final_unknown_reasons, _global_reason_tuple_from_action, _global_reason_tuple_from_record
from .phase3_return_width_bridge_lane2 import (
    _canonical_json,
    _canonical_movements,
    _canonical_targets,
    _entry_details,
    _entry_key,
    _failed,
    _display_path,
    _file_ref,
    _identity_set_check,
    _jsonable,
    _normalize_nested_tuple,
    _ok,
    _parse_roots,
    _read_json,
    _records_by_key,
    _sha256_file,
    _text_identity_is_specific,
    _write_json,
)
from .phase3_readonly_identity_lane3 import _nested_contains_diagnostic_reason
from .phase3_unresolved_expression_lane6 import _expression_provenance_is_specific
from .phase3_solver_rewrite_lane7 import (
    _action_to_dict,
    _binary_direction_matches,
    _reason_to_dict,
    _solver_rewrite_side_is_specific,
)
from .phase3_sat_unsafety_lane5 import (
    SAT_ACTION_TUPLE,
    SAT_EVIDENCE_KIND,
    SAT_PROOF_KIND,
    SAT_PROOF_STAGE,
    SAT_REASON_TUPLE,
    SAT_REQUIRED_EVIDENCE,
    _object_target_key_is_specific_sat_unsafety,
    _proof_action_has_expected_id as _sat_proof_action_has_expected_id,
    _proof_action_matches_lane_definition as _sat_proof_action_matches_lane_definition,
)
from ..equivalence.unknown_reason import (
    UNKNOWN_TUPLE_MISSING,
    UnknownCountKind,
    build_proof_obligation_id,
    coerce_unknown_recovery_actions,
)


MANIFEST_VERSION = 1
TARGET_REASON_IDS = ("solver_proven_rewrite_proof_failed",)
MISSING_SENTINEL = UNKNOWN_TUPLE_MISSING
SOLVER_PROOF_KIND = "solver_retry_or_normalization"
REWRITE_RECHECK_STAGE = "rewrite_proof_recheck"
SOLVER_RETRY_STAGE = "solver_retry"
REWRITE_RECHECK_EVIDENCE_KIND = "rewrite_before_expr"
SOLVER_RETRY_EVIDENCE_KIND = "normalized_query"
REWRITE_RECHECK_REQUIRED_EVIDENCE = (
    "rewrite_before_expr",
    "rewrite_after_expr",
    "proof_counterexample_or_solver_trace",
)
SOLVER_RETRY_REQUIRED_EVIDENCE = (
    "normalized_query",
    "solver_options",
    "query_hash",
)
SOLVER_REASON_TUPLE = (
    UnknownCountKind.REASON_RECORD.value,
    "solver_proven_rewrite_proof_failed",
    "retryable",
    "pair",
    SOLVER_PROOF_KIND,
    MISSING_SENTINEL,
    MISSING_SENTINEL,
)
REWRITE_RECHECK_ACTION_TUPLE = (
    UnknownCountKind.PROOF_ACTION.value,
    "solver_proven_rewrite_proof_failed",
    "retryable",
    "pair",
    SOLVER_PROOF_KIND,
    REWRITE_RECHECK_STAGE,
    "planned",
)
SOLVER_RETRY_ACTION_TUPLE = (
    UnknownCountKind.PROOF_ACTION.value,
    "solver_proven_rewrite_proof_failed",
    "retryable",
    "pair",
    SOLVER_PROOF_KIND,
    SOLVER_RETRY_STAGE,
    "planned",
)
FUNCTION_CALL_BINARY_NAMES = {
    "B8": "function_call_test-arm64-gcc-O3",
    "B10": "function_call_test-mips64-clang-O1",
}


def _expected_reason_record(movement_id: str) -> Dict[str, Any]:
    return {
        "id": movement_id,
        "count_kind": UnknownCountKind.REASON_RECORD.value,
        "tuple": list(SOLVER_REASON_TUPLE),
        "aggregation_unit": "pair",
        "stage": "S_PAIRWISE",
        "pair_or_case": MISSING_SENTINEL,
        "expected_evidence_refs": ["rewrite-proof-2"],
        "expected_evidence_kind": MISSING_SENTINEL,
        "required_object_target_kind": "solver_rewrite_proof",
        "require_proof_obligation_id": False,
    }


def _expected_proof_action(movement_id: str, proof_stage: str) -> Dict[str, Any]:
    if proof_stage == REWRITE_RECHECK_STAGE:
        action_tuple = REWRITE_RECHECK_ACTION_TUPLE
        evidence_kind = REWRITE_RECHECK_EVIDENCE_KIND
        required_evidence = REWRITE_RECHECK_REQUIRED_EVIDENCE
    elif proof_stage == SOLVER_RETRY_STAGE:
        action_tuple = SOLVER_RETRY_ACTION_TUPLE
        evidence_kind = SOLVER_RETRY_EVIDENCE_KIND
        required_evidence = SOLVER_RETRY_REQUIRED_EVIDENCE
    else:
        raise ValueError(f"unknown solver rewrite proof stage: {proof_stage}")
    return {
        "id": movement_id,
        "count_kind": UnknownCountKind.PROOF_ACTION.value,
        "tuple": list(action_tuple),
        "aggregation_unit": "pair",
        "stage": "S_PAIRWISE",
        "pair_or_case": MISSING_SENTINEL,
        "expected_evidence_refs": ["rewrite-proof-2"],
        "expected_evidence_kind": evidence_kind,
        "required_evidence": list(required_evidence),
        "required_object_target_kind": "solver_rewrite_proof",
        "require_proof_obligation_id": True,
    }


def _expected_sat_unsafety_reason_record(movement_id: str) -> Dict[str, Any]:
    return {
        "id": movement_id,
        "count_kind": UnknownCountKind.REASON_RECORD.value,
        "tuple": list(SAT_REASON_TUPLE),
        "aggregation_unit": "pair",
        "stage": "S_PAIRWISE",
        "pair_or_case": MISSING_SENTINEL,
        "expected_evidence_refs": ["active_sat_unsafety"],
        "expected_evidence_kind": SAT_EVIDENCE_KIND,
        "required_object_target_kind": "sat_unsafety",
        "require_proof_obligation_id": True,
    }


def _expected_sat_unsafety_proof_action(movement_id: str) -> Dict[str, Any]:
    return {
        "id": movement_id,
        "count_kind": UnknownCountKind.PROOF_ACTION.value,
        "tuple": list(SAT_ACTION_TUPLE),
        "aggregation_unit": "pair",
        "stage": "S_PAIRWISE",
        "pair_or_case": MISSING_SENTINEL,
        "expected_evidence_refs": [SAT_EVIDENCE_KIND],
        "expected_evidence_kind": SAT_EVIDENCE_KIND,
        "required_evidence": list(SAT_REQUIRED_EVIDENCE),
        "required_object_target_kind": "sat_unsafety",
        "require_proof_obligation_id": True,
    }


def _accepted_sat_unsafety_reclassification() -> Dict[str, Any]:
    return {
        "status": "retired_to_sat_unsafety",
        "from_reason_id": "solver_proven_rewrite_proof_failed",
        "to_reason_id": "sat_unsafety",
        "reason": (
            "current object-derived analysis exposes active SAT unsafety before "
            "the solver rewrite proof-failed lane is reached"
        ),
        "accepted_movements": [
            _expected_sat_unsafety_reason_record("solver-rewrite-proof-retired-to-sat-unsafety-reason-record"),
            _expected_sat_unsafety_proof_action("solver-rewrite-proof-retired-to-sat-unsafety-proof"),
        ],
    }


ACTIVE_SOLVER_REWRITE_PROOF_EXPECTED_MOVEMENTS: Tuple[Mapping[str, Any], ...] = (
    _expected_reason_record("solver-rewrite-proof-failed-reason-record"),
    _expected_proof_action("solver-rewrite-proof-recheck-action", REWRITE_RECHECK_STAGE),
    _expected_proof_action("solver-rewrite-normalized-query-retry-action", SOLVER_RETRY_STAGE),
)


DEFAULT_REPRESENTATIVES: Tuple[Mapping[str, Any], ...] = (
    {
        "id": "representative-solver-rewrite-proof-retired-to-sat-unsafety-recursive-sum-arm64-mips64",
        "category": "function_call",
        "function": "fc_recursive_sum",
        "binary_pair": "B8_B10",
        "expected_observed_binary1_name": FUNCTION_CALL_BINARY_NAMES["B8"],
        "expected_observed_binary2_name": FUNCTION_CALL_BINARY_NAMES["B10"],
        "required_reason_ids": ["sat_unsafety"],
        "retired_reason_ids": ["solver_proven_rewrite_proof_failed"],
        "role": (
            "baseline solver rewrite proof failure retired by the current "
            "object-derived sat_unsafety proof backlog"
        ),
        "expected_movements": list((_accepted_sat_unsafety_reclassification())["accepted_movements"]),
        "accepted_current_reclassification": _accepted_sat_unsafety_reclassification(),
    },
)


def build_phase3_solver_rewrite_proof_lane8_manifest(
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
        "manifest_kind": "phase3_solver_rewrite_proof_lane8_representatives",
        "artifact_role": "derived_audit_proof_backlog_gate",
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
                "Phase 3 lane order target reason solver_proven_rewrite_proof_failed",
                "current result preserves conservative UNKNOWN",
                "active solver rewrite proof records freeze rewrite recheck and normalized-query retry actions",
                "retired solver rewrite proof records freeze the accepted sat_unsafety replacement movement",
                "active object_target_key includes original and rewritten typed expression provenance",
                "retired movement object_target_key is the current object-derived sat_unsafety key",
            ],
        },
        "phase3_lane8_ready": readiness["ready"],
        "readiness": readiness,
        "entries": entries,
        "implementation_manifest": _implementation_manifest(entries),
    }
    path = output / "solver_rewrite_proof_lane8_representatives.json"
    _write_json(path, manifest)
    return path


def validate_phase3_solver_rewrite_proof_lane8_manifest(manifest: Mapping[str, Any]) -> None:
    failures = list((manifest.get("readiness") or {}).get("failed_checks") or ())
    if manifest.get("manifest_kind") != "phase3_solver_rewrite_proof_lane8_representatives":
        failures.append(_failed("solver_rewrite_proof_manifest_kind"))
    if not manifest.get("phase3_lane8_ready"):
        failures.append(_failed("solver_rewrite_proof_manifest_not_ready"))
    if failures:
        raise ValueError(f"Phase 3 lane 8 manifest is not ready: {failures!r}")


def build_phase3_solver_rewrite_proof_lane8_post_fix_gate(
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
        "manifest_kind": "phase3_solver_rewrite_proof_lane8_post_fix_gate",
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
        "phase3_lane8_post_fix_ready": not any(check.get("status") == "failed" for check in checks),
        "post_fix_summary": {
            "failed_kinds": [
                check.get("kind")
                for check in checks
                if isinstance(check, Mapping) and check.get("status") == "failed"
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
    path = output / "solver_rewrite_proof_lane8_post_fix_gate.json"
    _write_json(path, manifest)
    return path


def validate_phase3_solver_rewrite_proof_lane8_post_fix_gate(manifest: Mapping[str, Any]) -> None:
    failures = [
        check
        for check in manifest.get("checks") or ()
        if isinstance(check, Mapping) and check.get("status") == "failed"
    ]
    if manifest.get("manifest_kind") != "phase3_solver_rewrite_proof_lane8_post_fix_gate":
        failures.append(_failed("solver_rewrite_proof_post_fix_manifest_kind"))
    if not manifest.get("phase3_lane8_post_fix_ready"):
        failures.append(_failed("solver_rewrite_proof_post_fix_not_ready"))
    if failures:
        raise ValueError(f"Phase 3 lane 8 post-fix gate is not ready: {failures!r}")


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
    entry["required_completion_actions"] = _canonical_actions(_current_actions(entry))
    entry["accepted_current_reclassification_targets"] = _canonical_targets(
        _current_accepted_reclassification_targets(entry)
    )
    entry["accepted_current_reclassification_actions"] = _canonical_actions(
        _current_accepted_reclassification_actions(entry)
    )
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
    checks.append(
        _ok("solver_rewrite_proof_baseline_unknown", **details)
        if baseline.get("final_result") == STATUS_UNKNOWN
        else _failed("solver_rewrite_proof_baseline_unknown", baseline_result=baseline.get("final_result") or MISSING_SENTINEL, **details)
    )
    checks.append(
        _ok("solver_rewrite_proof_current_unknown", **details)
        if current.get("final_result") == STATUS_UNKNOWN
        else _failed("solver_rewrite_proof_current_unknown", current_result=current.get("final_result") or MISSING_SENTINEL, **details)
    )
    checks.append(
        _ok("solver_rewrite_proof_binary_direction", **details)
        if _binary_direction_matches(entry, current)
        else _failed(
            "solver_rewrite_proof_binary_direction",
            observed_binary1=current.get("observed_binary1_name") or MISSING_SENTINEL,
            observed_binary2=current.get("observed_binary2_name") or MISSING_SENTINEL,
            **details,
        )
    )
    accepted_reclassification_failures = _accepted_current_reclassification_failures(entry)
    if accepted_reclassification_failures is not None:
        checks.extend(accepted_reclassification_failures)
        return checks
    targets = _current_targets(entry)
    actions = _current_actions(entry)
    checks.append(
        _ok("solver_rewrite_proof_current_targets_present", count=len(targets), **details)
        if targets
        else _failed("solver_rewrite_proof_current_targets_present", count=0, **details)
    )
    missing_actions = _missing_actions(entry)
    checks.append(
        _ok("solver_rewrite_proof_current_actions_complete", count=len(actions), **details)
        if actions and not missing_actions
        else _failed("solver_rewrite_proof_current_actions_complete", missing=missing_actions, count=len(actions), **details)
    )
    checks.append(
        _ok("solver_rewrite_proof_expected_movements_match_definition", **details)
        if _expected_movements_match_definition(entry)
        else _failed(
            "solver_rewrite_proof_expected_movements_match_definition",
            expected=_canonical_movements(_expected_movements_for_entry(entry)),
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
        failures.append(_failed("solver_rewrite_proof_timeout_regression", **details))
        return "failed", failures
    if result != STATUS_UNKNOWN:
        failures.append(
            _failed("solver_rewrite_proof_unexpected_final_result", current_result=result or MISSING_SENTINEL, **details)
        )
        return "failed", failures
    accepted_reclassification_failures = _accepted_current_reclassification_failures(entry)
    if accepted_reclassification_failures is not None:
        failures.extend(
            check
            for check in accepted_reclassification_failures
            if isinstance(check, Mapping) and check.get("status") == "failed"
        )
        frozen_targets = _canonical_targets(entry.get("accepted_current_reclassification_targets"))
        current_targets = _canonical_targets(_current_accepted_reclassification_targets(entry))
        if not frozen_targets or current_targets != frozen_targets:
            failures.append(
                _failed(
                    "solver_rewrite_proof_accepted_reclassification_target_set_changed",
                    expected=frozen_targets,
                    actual=current_targets,
                    **details,
                )
            )
        frozen_actions = _canonical_actions(entry.get("accepted_current_reclassification_actions"))
        current_actions = _canonical_actions(_current_accepted_reclassification_actions(entry))
        if not frozen_actions or current_actions != frozen_actions:
            failures.append(
                _failed(
                    "solver_rewrite_proof_accepted_reclassification_actions_changed",
                    expected=frozen_actions,
                    actual=current_actions,
                    **details,
                )
            )
        if failures:
            return "failed", failures
        return "retired_to_sat_unsafety", ()
    frozen_targets = _canonical_targets(entry.get("target_object_keys"))
    current_targets = _canonical_targets(_current_targets(entry))
    if not frozen_targets or current_targets != frozen_targets:
        failures.append(
            _failed("solver_rewrite_proof_target_set_changed", expected=frozen_targets, actual=current_targets, **details)
        )
    frozen_actions = _canonical_actions(entry.get("required_completion_actions"))
    current_actions = _canonical_actions(_current_actions(entry))
    if not frozen_actions or current_actions != frozen_actions:
        failures.append(
            _failed("solver_rewrite_proof_required_actions_changed", expected=frozen_actions, actual=current_actions, **details)
        )
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
    checks.append(_ok("baseline_id") if baseline_manifest.get("baseline_id") == "observed-v0@0a53352" else _failed("baseline_id", actual=baseline_manifest.get("baseline_id")))
    checks.append(
        _ok("phase3_pre_fix_manifest_sha256")
        if expected_phase3_sha256 and actual_phase3_sha256 == expected_phase3_sha256
        else _failed(
            "phase3_pre_fix_manifest_sha256",
            expected=expected_phase3_sha256 or MISSING_SENTINEL,
            actual=actual_phase3_sha256,
            path=str(phase3_manifest_path),
        )
    )
    checks.append(
        _ok("phase3_pre_fix_manifest_kind")
        if phase3_manifest.get("manifest_kind") == "phase3_solver_rewrite_proof_lane8_representatives"
        else _failed("phase3_pre_fix_manifest_kind")
    )
    checks.append(
        _ok("phase3_pre_fix_manifest_ready")
        if phase3_manifest.get("phase3_lane8_ready") is True
        else _failed("phase3_pre_fix_manifest_ready")
    )
    checks.append(_identity_set_check("phase3_pre_fix_entries", phase3_manifest.get("entries"), DEFAULT_REPRESENTATIVES))
    implementation = phase3_manifest.get("implementation_manifest")
    if isinstance(implementation, Mapping):
        checks.append(_ok("phase3_pre_fix_implementation_manifest_present"))
        expected_reclassifications = _canonical_reclassifications(
            implementation.get("accepted_current_reclassifications")
        )
        expected_targets = _canonical_targets(implementation.get("expected_solver_rewrite_proof_targets"))
        actual_targets = _canonical_targets(
            [
                target
                for entry in phase3_manifest.get("entries") or ()
                for target in (entry.get("target_object_keys") or ())
            ]
        )
        checks.append(
            _ok("phase3_pre_fix_implementation_targets_consistent")
            if expected_targets == actual_targets and (expected_targets or expected_reclassifications)
            else _failed("phase3_pre_fix_implementation_targets_consistent", expected=expected_targets, actual=actual_targets)
        )
        expected_actions = _canonical_actions(implementation.get("required_completion_actions"))
        actual_actions = _canonical_actions(
            [
                action
                for entry in phase3_manifest.get("entries") or ()
                for action in (entry.get("required_completion_actions") or ())
            ]
        )
        checks.append(
            _ok("phase3_pre_fix_implementation_actions_consistent")
            if expected_actions == actual_actions and (expected_actions or expected_reclassifications)
            else _failed("phase3_pre_fix_implementation_actions_consistent", expected=expected_actions, actual=actual_actions)
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
        actual_reclassifications = _canonical_reclassifications(
            [
                entry.get("accepted_current_reclassification")
                for entry in phase3_manifest.get("entries") or ()
                if isinstance(entry, Mapping) and entry.get("accepted_current_reclassification")
            ]
        )
        checks.append(
            _ok("phase3_pre_fix_implementation_reclassifications_consistent")
            if expected_reclassifications == actual_reclassifications
            else _failed(
                "phase3_pre_fix_implementation_reclassifications_consistent",
                expected=expected_reclassifications,
                actual=actual_reclassifications,
            )
        )
        expected_reclassification_targets = _canonical_targets(
            implementation.get("accepted_sat_unsafety_targets")
        )
        actual_reclassification_targets = _canonical_targets(
            [
                target
                for entry in phase3_manifest.get("entries") or ()
                for target in (entry.get("accepted_current_reclassification_targets") or ())
            ]
        )
        checks.append(
            _ok("phase3_pre_fix_implementation_reclassification_targets_consistent")
            if expected_reclassification_targets == actual_reclassification_targets
            else _failed(
                "phase3_pre_fix_implementation_reclassification_targets_consistent",
                expected=expected_reclassification_targets,
                actual=actual_reclassification_targets,
            )
        )
        expected_reclassification_actions = _canonical_actions(
            implementation.get("accepted_sat_unsafety_actions")
        )
        actual_reclassification_actions = _canonical_actions(
            [
                action
                for entry in phase3_manifest.get("entries") or ()
                for action in (entry.get("accepted_current_reclassification_actions") or ())
            ]
        )
        checks.append(
            _ok("phase3_pre_fix_implementation_reclassification_actions_consistent")
            if expected_reclassification_actions == actual_reclassification_actions
            else _failed(
                "phase3_pre_fix_implementation_reclassification_actions_consistent",
                expected=expected_reclassification_actions,
                actual=actual_reclassification_actions,
            )
        )
    else:
        checks.append(_failed("phase3_pre_fix_implementation_manifest_present"))
    for entry in entries:
        for failure in entry.get("post_fix_failures") or ():
            checks.append(failure)
        checks.append(
            _ok("solver_rewrite_proof_post_fix_expected_movement", post_fix_status=entry.get("post_fix_status"), **_entry_details(entry))
            if entry.get("post_fix_status") in {"pending_proof", "retired_to_sat_unsafety"}
            else _failed("solver_rewrite_proof_post_fix_expected_movement", post_fix_status=entry.get("post_fix_status") or MISSING_SENTINEL, **_entry_details(entry))
        )
    return checks


def _implementation_manifest(entries: Sequence[Mapping[str, Any]]) -> Dict[str, Any]:
    return {
        "lane_id": "phase3_solver_rewrite_proof_lane8",
        "target_reason_id": "solver_proven_rewrite_proof_failed",
        "baseline_mode": "pending_proof_or_retired_to_sat_unsafety_against_pre_fix_manifest",
        "expected_movement_entries": _canonical_movements(
            [
                movement
                for entry in entries
                for movement in (entry.get("expected_movements") or ())
            ]
        ),
        "expected_solver_rewrite_proof_targets": _canonical_targets(
            [
                target
                for entry in entries
                for target in (entry.get("target_object_keys") or ())
            ]
        ),
        "required_completion_actions": _canonical_actions(
            [
                action
                for entry in entries
                for action in (entry.get("required_completion_actions") or ())
            ]
        ),
        "accepted_current_reclassifications": _canonical_reclassifications(
            [
                entry.get("accepted_current_reclassification")
                for entry in entries
                if entry.get("accepted_current_reclassification")
            ]
        ),
        "accepted_sat_unsafety_targets": _canonical_targets(
            [
                target
                for entry in entries
                for target in (entry.get("accepted_current_reclassification_targets") or ())
            ]
        ),
        "accepted_sat_unsafety_actions": _canonical_actions(
            [
                action
                for entry in entries
                for action in (entry.get("accepted_current_reclassification_actions") or ())
            ]
        ),
    }


def _current_targets(entry: Any) -> Sequence[Any]:
    current = entry.get("current_observation") if isinstance(entry, Mapping) else None
    if not isinstance(current, Mapping):
        return ()
    targets = []
    for record in current.get("reason_records") or ():
        if not isinstance(record, Mapping):
            continue
        if record.get("reason_id") != "solver_proven_rewrite_proof_failed":
            continue
        if tuple(record.get("tuple") or ()) != SOLVER_REASON_TUPLE:
            continue
        if not _object_target_key_is_specific_solver_rewrite_proof(record.get("object_target_key")):
            continue
        targets.append(record.get("object_target_key"))
    return tuple(targets)


def _current_actions(entry: Any) -> Sequence[Mapping[str, Any]]:
    current = entry.get("current_observation") if isinstance(entry, Mapping) else None
    if not isinstance(current, Mapping):
        return ()
    actions = []
    for action in current.get("proof_actions") or ():
        if not isinstance(action, Mapping):
            continue
        if action.get("reason_id") != "solver_proven_rewrite_proof_failed":
            continue
        if not _object_target_key_is_specific_solver_rewrite_proof(action.get("object_target_key")):
            continue
        if action.get("raw_proof_obligation_id_present") is not True:
            continue
        if action.get("raw_object_target_key_present") is not True:
            continue
        if not _action_matches_lane_definition(action):
            continue
        if not _action_has_expected_id(action):
            continue
        actions.append(action)
    return tuple(actions)


def _current_accepted_reclassification_targets(entry: Any) -> Sequence[Any]:
    if not _accepted_current_reclassification(entry):
        return ()
    current = entry.get("current_observation") if isinstance(entry, Mapping) else None
    if not isinstance(current, Mapping):
        return ()
    targets = []
    for record in current.get("reason_records") or ():
        if not isinstance(record, Mapping):
            continue
        if record.get("reason_id") != "sat_unsafety":
            continue
        if tuple(record.get("tuple") or ()) != SAT_REASON_TUPLE:
            continue
        if not _object_target_key_is_specific_sat_unsafety(record.get("object_target_key")):
            continue
        targets.append(record.get("object_target_key"))
    return tuple(targets)


def _current_accepted_reclassification_actions(entry: Any) -> Sequence[Mapping[str, Any]]:
    if not _accepted_current_reclassification(entry):
        return ()
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
        if action.get("raw_proof_obligation_id_present") is not True:
            continue
        if action.get("raw_object_target_key_present") is not True:
            continue
        if not _sat_proof_action_matches_lane_definition(action):
            continue
        if not _sat_proof_action_has_expected_id(action):
            continue
        actions.append(action)
    return tuple(actions)


def _accepted_current_reclassification(entry: Mapping[str, Any]) -> Optional[Mapping[str, Any]]:
    accepted = entry.get("accepted_current_reclassification")
    return accepted if isinstance(accepted, Mapping) else None


def _accepted_current_reclassification_failures(
    entry: Mapping[str, Any],
) -> Optional[Sequence[Dict[str, Any]]]:
    accepted = _accepted_current_reclassification(entry)
    if accepted is None:
        return None
    current = entry.get("current_observation") if isinstance(entry.get("current_observation"), Mapping) else {}
    baseline = entry.get("baseline_observation") if isinstance(entry.get("baseline_observation"), Mapping) else {}
    details = _entry_details(entry)
    failures: list[Dict[str, Any]] = []
    if _canonical_reclassifications([accepted]) != _canonical_reclassifications(
        [DEFAULT_REPRESENTATIVES[0].get("accepted_current_reclassification")]
    ):
        failures.append(
            _failed(
                "solver_rewrite_proof_accepted_reclassification_definition",
                expected=_canonical_reclassifications(
                    [DEFAULT_REPRESENTATIVES[0].get("accepted_current_reclassification")]
                ),
                actual=_canonical_reclassifications([accepted]),
                **details,
            )
        )
    if accepted.get("status") != "retired_to_sat_unsafety":
        failures.append(
            _failed(
                "solver_rewrite_proof_accepted_reclassification_status",
                expected="retired_to_sat_unsafety",
                actual=accepted.get("status") or MISSING_SENTINEL,
                **details,
            )
        )
    baseline_reasons = set(baseline.get("observed_reason_ids") or ())
    current_reasons = set(current.get("observed_reason_ids") or ())
    if "solver_proven_rewrite_proof_failed" not in baseline_reasons:
        failures.append(
            _failed(
                "solver_rewrite_proof_accepted_reclassification_baseline_reason",
                expected="solver_proven_rewrite_proof_failed",
                actual=sorted(baseline_reasons),
                **details,
            )
        )
    if "sat_unsafety" not in current_reasons:
        failures.append(
            _failed(
                "solver_rewrite_proof_accepted_reclassification_current_reason",
                expected="sat_unsafety",
                actual=sorted(current_reasons),
                **details,
            )
        )
    if "solver_proven_rewrite_proof_failed" in current_reasons:
        failures.append(
            _failed(
                "solver_rewrite_proof_accepted_reclassification_old_reason_still_active",
                actual=sorted(current_reasons),
                **details,
            )
        )
    targets = _current_accepted_reclassification_targets(entry)
    if targets:
        failures.append(
            _ok(
                "solver_rewrite_proof_accepted_reclassification_targets_present",
                count=len(targets),
                **details,
            )
        )
    else:
        failures.append(
            _failed(
                "solver_rewrite_proof_accepted_reclassification_targets_present",
                count=0,
                **details,
            )
        )
    actions = _current_accepted_reclassification_actions(entry)
    missing_actions = _missing_accepted_reclassification_actions(entry)
    if actions and not missing_actions:
        failures.append(
            _ok(
                "solver_rewrite_proof_accepted_reclassification_actions_complete",
                count=len(actions),
                **details,
            )
        )
    else:
        failures.append(
            _failed(
                "solver_rewrite_proof_accepted_reclassification_actions_complete",
                missing=missing_actions,
                count=len(actions),
                **details,
            )
        )
    failures.extend(_accepted_reclassification_tuple_failures(current, accepted, details))
    return tuple(failures)


def _missing_accepted_reclassification_actions(entry: Mapping[str, Any]) -> Sequence[Dict[str, Any]]:
    current_targets = _canonical_targets(_current_accepted_reclassification_targets(entry))
    action_keys = {
        (_canonical_json(action.get("object_target_key")), action.get("proof_kind"), action.get("proof_stage"))
        for action in _current_accepted_reclassification_actions(entry)
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


def _accepted_reclassification_tuple_failures(
    current: Mapping[str, Any],
    accepted: Mapping[str, Any],
    details: Mapping[str, Any],
) -> Sequence[Dict[str, Any]]:
    failures: list[Dict[str, Any]] = []
    movements = tuple(
        movement
        for movement in (accepted.get("accepted_movements") or ())
        if isinstance(movement, Mapping)
    )
    if not movements:
        return [_failed("solver_rewrite_proof_accepted_reclassification_movements_missing", **details)]
    reason_tuples = {tuple(item or ()) for item in current.get("reason_record_tuples") or ()}
    action_tuples = {tuple(item or ()) for item in current.get("proof_action_tuples") or ()}
    for movement in movements:
        expected_tuple = tuple(movement.get("tuple") or ())
        count_kind = movement.get("count_kind")
        if count_kind == UnknownCountKind.REASON_RECORD.value:
            present = expected_tuple in reason_tuples
        elif count_kind == UnknownCountKind.PROOF_ACTION.value:
            present = expected_tuple in action_tuples
        else:
            present = False
        if not present:
            failures.append(
                _failed(
                    "solver_rewrite_proof_accepted_reclassification_tuple_missing",
                    movement_id=movement.get("id") or MISSING_SENTINEL,
                    expected_tuple=list(expected_tuple),
                    **details,
                )
            )
    return tuple(failures)


def _missing_actions(entry: Mapping[str, Any]) -> Sequence[Dict[str, Any]]:
    current_targets = _canonical_targets(_current_targets(entry))
    action_keys = {
        (_canonical_json(action.get("object_target_key")), action.get("proof_kind"), action.get("proof_stage"))
        for action in _current_actions(entry)
    }
    missing = []
    for target in current_targets:
        for proof_stage in (REWRITE_RECHECK_STAGE, SOLVER_RETRY_STAGE):
            key = (_canonical_json(target), SOLVER_PROOF_KIND, proof_stage)
            if key not in action_keys:
                missing.append(
                    {
                        "object_target_key": target,
                        "proof_kind": SOLVER_PROOF_KIND,
                        "proof_stage": proof_stage,
                    }
                )
    return missing


def _canonical_actions(actions: Any) -> Tuple[Any, ...]:
    canonical = []
    for action in actions or ():
        if not isinstance(action, Mapping):
            continue
        canonical.append(
            {
                "tuple": list(action.get("tuple") or ()),
                "stage": action.get("stage"),
                "pair_or_case": action.get("pair_or_case"),
                "evidence_kind": action.get("evidence_kind"),
                "required_evidence": list(action.get("required_evidence") or ()),
                "object_target_key": _jsonable(action.get("object_target_key")),
                "proof_obligation_id": _jsonable(action.get("proof_obligation_id")),
            }
        )
    return tuple(sorted(canonical, key=_canonical_json))


def _canonical_reclassifications(values: Any) -> Tuple[Any, ...]:
    canonical = []
    for value in values or ():
        if not isinstance(value, Mapping):
            continue
        canonical.append(
            {
                "status": value.get("status"),
                "from_reason_id": value.get("from_reason_id"),
                "to_reason_id": value.get("to_reason_id"),
                "reason": value.get("reason"),
                "accepted_movements": _canonical_movements(value.get("accepted_movements")),
            }
        )
    return tuple(sorted(canonical, key=_canonical_json))


def _action_has_expected_id(action: Mapping[str, Any]) -> bool:
    expected = build_proof_obligation_id(
        action.get("reason_id"),
        action.get("proof_stage"),
        action.get("proof_kind"),
        action.get("evidence_kind"),
        action.get("object_target_key"),
    )
    return _normalize_nested_tuple(action.get("proof_obligation_id")) == _normalize_nested_tuple(expected)


def _action_matches_lane_definition(action: Mapping[str, Any]) -> bool:
    proof_stage = action.get("proof_stage")
    if proof_stage == REWRITE_RECHECK_STAGE:
        expected_tuple = REWRITE_RECHECK_ACTION_TUPLE
        evidence_kind = REWRITE_RECHECK_EVIDENCE_KIND
        required_evidence = REWRITE_RECHECK_REQUIRED_EVIDENCE
    elif proof_stage == SOLVER_RETRY_STAGE:
        expected_tuple = SOLVER_RETRY_ACTION_TUPLE
        evidence_kind = SOLVER_RETRY_EVIDENCE_KIND
        required_evidence = SOLVER_RETRY_REQUIRED_EVIDENCE
    else:
        return False
    return (
        tuple(action.get("tuple") or ()) == expected_tuple
        and action.get("status") == "planned"
        and action.get("stage") == "S_PAIRWISE"
        and action.get("proof_kind") == SOLVER_PROOF_KIND
        and action.get("evidence_kind") == evidence_kind
        and tuple(action.get("required_evidence") or ()) == required_evidence
    )


def _expected_movements_match_definition(entry: Mapping[str, Any]) -> bool:
    return _canonical_movements(entry.get("expected_movements")) == _canonical_movements(
        _expected_movements_for_entry(entry)
    )


def _expected_movements_for_entry(entry: Mapping[str, Any]) -> Sequence[Mapping[str, Any]]:
    if _accepted_current_reclassification(entry):
        return tuple((_accepted_sat_unsafety_reclassification())["accepted_movements"])
    return ACTIVE_SOLVER_REWRITE_PROOF_EXPECTED_MOVEMENTS


def _object_target_key_is_specific_solver_rewrite_proof(value: Any) -> bool:
    target = _normalize_nested_tuple(value)
    if not isinstance(target, tuple) or len(target) != 8 or target[0] != "solver_rewrite_proof":
        return False
    if _nested_contains_diagnostic_reason(target):
        return False
    pair = target[1]
    rewrite_side = target[2]
    rewrite_stage = target[3]
    return (
        isinstance(pair, tuple)
        and len(pair) == 2
        and pair[0] == "pair"
        and _text_identity_is_specific(pair[1])
        and isinstance(rewrite_side, tuple)
        and len(rewrite_side) == 2
        and rewrite_side[0] == "rewrite_side"
        and rewrite_side[1] in {"left", "right"}
        and isinstance(rewrite_stage, tuple)
        and len(rewrite_stage) == 2
        and rewrite_stage[0] == "rewrite_stage"
        and _text_identity_is_specific(rewrite_stage[1])
        and _solver_rewrite_side_is_specific(target[4], "left")
        and _solver_rewrite_side_is_specific(target[5], "right")
        and _rewrite_expression_key_is_specific(target[6], "original_expression")
        and _rewrite_expression_key_is_specific(target[7], "rewritten_expression")
    )


def _rewrite_expression_key_is_specific(value: Any, expected_tag: str) -> bool:
    expression = _normalize_nested_tuple(value)
    return (
        isinstance(expression, tuple)
        and len(expression) == 2
        and expression[0] == expected_tag
        and _expression_provenance_is_specific(expression[1])
    )


def main(argv: Optional[Sequence[str]] = None) -> int:
    parser = argparse.ArgumentParser(description="Validate Phase 3 lane 8 solver rewrite proof representatives.")
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
            raise SystemExit("--phase3-manifest is required for post-fix gate")
        path = build_phase3_solver_rewrite_proof_lane8_post_fix_gate(
            baseline_raw_dir=args.baseline_raw_dir,
            output_dir=args.output_dir,
            current_log_roots=current_roots,
            baseline_log_roots=baseline_roots,
            phase3_manifest_path=args.phase3_manifest,
            phase3_manifest_sha256=args.phase3_manifest_sha256,
        )
        if args.require_ready:
            validate_phase3_solver_rewrite_proof_lane8_post_fix_gate(_read_json(path))
    else:
        path = build_phase3_solver_rewrite_proof_lane8_manifest(
            baseline_raw_dir=args.baseline_raw_dir,
            output_dir=args.output_dir,
            current_log_roots=current_roots,
            baseline_log_roots=baseline_roots,
        )
        if args.require_ready:
            validate_phase3_solver_rewrite_proof_lane8_manifest(_read_json(path))
    print(path)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
