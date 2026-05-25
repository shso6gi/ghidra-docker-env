# -*- coding: utf-8 -*-
"""Freeze Phase 3 lane 7 representatives for solver rewrite normalization."""

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
from .phase3_readonly_identity_lane3 import (
    _analysis_entry_key_is_specific,
    _nested_contains_diagnostic_reason,
)
from .phase3_return_coverage_lane1 import (
    _object_target_key_is_specific as _return_coverage_object_target_key_is_specific,
)
from .phase3_unresolved_expression_lane6 import (
    _expression_provenance_is_specific,
    _return_guard_like_key_is_specific,
    _return_storage_is_specific,
    _return_storage_width,
    _unresolved_return_case_partition_member_is_specific,
)
from ..equivalence.unknown_reason import (
    UNKNOWN_TUPLE_MISSING,
    UnknownCountKind,
    build_proof_obligation_id,
    coerce_unknown_recovery_actions,
)


MANIFEST_VERSION = 1
TARGET_REASON_IDS = ("solver_proven_rewrite_no_change",)
MISSING_SENTINEL = UNKNOWN_TUPLE_MISSING
SOLVER_PROOF_KIND = "solver_retry_or_normalization"
SOLVER_PROOF_STAGE = "rewrite_candidate_generation"
SOLVER_EVIDENCE_KIND = "pre_normalized_query"
SOLVER_REQUIRED_EVIDENCE = (
    "pre_normalized_query",
    "rewrite_candidate",
    "typed_expression_key",
)
SOLVER_REASON_TUPLE = (
    UnknownCountKind.REASON_RECORD.value,
    "solver_proven_rewrite_no_change",
    "retryable",
    "pair",
    SOLVER_PROOF_KIND,
    SOLVER_PROOF_STAGE,
    MISSING_SENTINEL,
)
SOLVER_ACTION_TUPLE = (
    UnknownCountKind.PROOF_ACTION.value,
    "solver_proven_rewrite_no_change",
    "retryable",
    "pair",
    SOLVER_PROOF_KIND,
    SOLVER_PROOF_STAGE,
    "planned",
)
RETURN_COVERAGE_RECLASSIFIED_REASON_TUPLE = (
    UnknownCountKind.REASON_RECORD.value,
    "return_coverage_gap",
    "blocks_equivalence",
    "function",
    "return_coverage_completion",
    MISSING_SENTINEL,
    "pending_proof",
)
RETURN_COVERAGE_RECLASSIFIED_PARTITION_ACTION_TUPLE = (
    UnknownCountKind.PROOF_ACTION.value,
    "return_coverage_gap",
    "blocks_equivalence",
    "function",
    "return_coverage_completion",
    "return_partition_extraction",
    "pending_proof",
)
RETURN_COVERAGE_RECLASSIFIED_GUARD_ACTION_TUPLE = (
    UnknownCountKind.PROOF_ACTION.value,
    "return_coverage_gap",
    "blocks_equivalence",
    "function",
    "return_coverage_completion",
    "return_guard_coverage",
    "pending_proof",
)
LOOP_BINARY_NAMES = {
    "B12": "loop_method_b_test-mips64-clang-O3",
    "B16": "loop_method_b_test-mips64-gcc-O3",
}


def _expected_reason_record(movement_id: str) -> Dict[str, Any]:
    return {
        "id": movement_id,
        "count_kind": UnknownCountKind.REASON_RECORD.value,
        "tuple": list(SOLVER_REASON_TUPLE),
        "aggregation_unit": "pair",
        "stage": "S_PAIRWISE",
        "pair_or_case": MISSING_SENTINEL,
        "expected_evidence_refs": ["rewrite-no-change"],
        "expected_evidence_kind": SOLVER_EVIDENCE_KIND,
        "required_object_target_kind": "solver_rewrite_candidate",
        "require_proof_obligation_id": True,
    }


def _expected_proof_action(movement_id: str) -> Dict[str, Any]:
    return {
        "id": movement_id,
        "count_kind": UnknownCountKind.PROOF_ACTION.value,
        "tuple": list(SOLVER_ACTION_TUPLE),
        "aggregation_unit": "pair",
        "stage": "S_PAIRWISE",
        "pair_or_case": MISSING_SENTINEL,
        "expected_evidence_refs": ["rewrite-no-change"],
        "expected_evidence_kind": SOLVER_EVIDENCE_KIND,
        "required_evidence": list(SOLVER_REQUIRED_EVIDENCE),
        "required_object_target_kind": "solver_rewrite_candidate",
        "require_proof_obligation_id": True,
    }


def _accepted_return_coverage_reclassification() -> Sequence[Dict[str, Any]]:
    return (
        {
            "id": "solver-rewrite-retired-to-return-coverage-reason-record",
            "count_kind": UnknownCountKind.REASON_RECORD.value,
            "tuple": list(RETURN_COVERAGE_RECLASSIFIED_REASON_TUPLE),
            "aggregation_unit": "function",
            "stage": "S_PAIRWISE",
            "pair_or_case": MISSING_SENTINEL,
            "expected_evidence_refs": ["function1:return_coverage_gap"],
            "expected_evidence_kind": MISSING_SENTINEL,
            "required_object_target_kind": "return_coverage",
            "require_proof_obligation_id": False,
        },
        {
            "id": "solver-rewrite-retired-to-return-coverage-partition-action",
            "count_kind": UnknownCountKind.PROOF_ACTION.value,
            "tuple": list(RETURN_COVERAGE_RECLASSIFIED_PARTITION_ACTION_TUPLE),
            "aggregation_unit": "function",
            "stage": "S_PAIRWISE",
            "pair_or_case": MISSING_SENTINEL,
            "expected_evidence_refs": ["function1:return_coverage_gap"],
            "expected_evidence_kind": "missing_return_guard",
            "required_evidence": [
                "missing_return_guard",
                "tail_or_default_return_value",
                "return_storage",
            ],
            "required_object_target_kind": "return_coverage",
            "require_proof_obligation_id": True,
        },
        {
            "id": "solver-rewrite-retired-to-return-coverage-guard-action",
            "count_kind": UnknownCountKind.PROOF_ACTION.value,
            "tuple": list(RETURN_COVERAGE_RECLASSIFIED_GUARD_ACTION_TUPLE),
            "aggregation_unit": "function",
            "stage": "S_PAIRWISE",
            "pair_or_case": MISSING_SENTINEL,
            "expected_evidence_refs": ["function1:return_coverage_gap"],
            "expected_evidence_kind": "case_guard_disjunction",
            "required_evidence": [
                "case_guard_disjunction",
                "path_feasibility",
                "function_precondition",
            ],
            "required_object_target_kind": "return_coverage",
            "require_proof_obligation_id": True,
        },
    )


DEFAULT_REPRESENTATIVES: Tuple[Mapping[str, Any], ...] = (
    {
        "id": "representative-solver-rewrite-no-change-prefix-loop-mips64",
        "category": "loop",
        "function": "lmb_sum_prefix_loop",
        "binary_pair": "B12_B16",
        "expected_observed_binary1_name": LOOP_BINARY_NAMES["B12"],
        "expected_observed_binary2_name": LOOP_BINARY_NAMES["B16"],
        "required_reason_ids": ["solver_proven_rewrite_no_change"],
        "role": "solver rewrite no-change candidate generation backlog with object-derived return cases",
        "expected_movements": [
            _expected_reason_record("solver-rewrite-no-change-reason-record"),
            _expected_proof_action("solver-rewrite-candidate-generation-proof"),
        ],
        "accepted_post_fix_reclassification": {
            "status": "retired_to_return_coverage_gap",
            "reason": (
                "readonly proof guard SMT metadata normalization exposes the existing "
                "return coverage proof backlog before solver rewrite retry"
            ),
            "accepted_movements": list(_accepted_return_coverage_reclassification()),
        },
    },
)


def build_phase3_solver_rewrite_lane7_manifest(
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
        "manifest_kind": "phase3_solver_rewrite_lane7_representatives",
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
                "Phase 3 lane order target reason solver_proven_rewrite_no_change",
                "current reason record preserves conservative UNKNOWN",
                "object_target_key includes pair, function entries, return cases, guards, and typed expression provenance",
            ],
        },
        "phase3_lane7_ready": readiness["ready"],
        "readiness": readiness,
        "entries": entries,
        "implementation_manifest": _implementation_manifest(entries),
    }
    path = output / "solver_rewrite_lane7_representatives.json"
    _write_json(path, manifest)
    return path


def validate_phase3_solver_rewrite_lane7_manifest(manifest: Mapping[str, Any]) -> None:
    failures = list((manifest.get("readiness") or {}).get("failed_checks") or ())
    if manifest.get("manifest_kind") != "phase3_solver_rewrite_lane7_representatives":
        failures.append(_failed("solver_rewrite_manifest_kind"))
    if not manifest.get("phase3_lane7_ready"):
        failures.append(_failed("solver_rewrite_manifest_not_ready"))
    if failures:
        raise ValueError(f"Phase 3 lane 7 manifest is not ready: {failures!r}")


def build_phase3_solver_rewrite_lane7_post_fix_gate(
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
        "manifest_kind": "phase3_solver_rewrite_lane7_post_fix_gate",
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
        "phase3_lane7_post_fix_ready": not any(check.get("status") == "failed" for check in checks),
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
    path = output / "solver_rewrite_lane7_post_fix_gate.json"
    _write_json(path, manifest)
    return path


def validate_phase3_solver_rewrite_lane7_post_fix_gate(manifest: Mapping[str, Any]) -> None:
    failures = [
        check
        for check in manifest.get("checks") or ()
        if isinstance(check, Mapping) and check.get("status") == "failed"
    ]
    if manifest.get("manifest_kind") != "phase3_solver_rewrite_lane7_post_fix_gate":
        failures.append(_failed("solver_rewrite_post_fix_manifest_kind"))
    if not manifest.get("phase3_lane7_post_fix_ready"):
        failures.append(_failed("solver_rewrite_post_fix_not_ready"))
    if failures:
        raise ValueError(f"Phase 3 lane 7 post-fix gate is not ready: {failures!r}")


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
    checks.append(
        _ok("solver_rewrite_baseline_unknown", **details)
        if baseline.get("final_result") == STATUS_UNKNOWN
        else _failed("solver_rewrite_baseline_unknown", baseline_result=baseline.get("final_result") or MISSING_SENTINEL, **details)
    )
    checks.append(
        _ok("solver_rewrite_current_unknown", **details)
        if current.get("final_result") == STATUS_UNKNOWN
        else _failed("solver_rewrite_current_unknown", current_result=current.get("final_result") or MISSING_SENTINEL, **details)
    )
    checks.append(
        _ok("solver_rewrite_binary_direction", **details)
        if _binary_direction_matches(entry, current)
        else _failed(
            "solver_rewrite_binary_direction",
            observed_binary1=current.get("observed_binary1_name") or MISSING_SENTINEL,
            observed_binary2=current.get("observed_binary2_name") or MISSING_SENTINEL,
            **details,
        )
    )
    targets = _current_targets(entry)
    actions = _current_actions(entry)
    checks.append(
        _ok("solver_rewrite_current_targets_present", count=len(targets), **details)
        if targets
        else _failed("solver_rewrite_current_targets_present", count=0, **details)
    )
    missing_actions = _missing_actions(entry)
    checks.append(
        _ok("solver_rewrite_current_actions_complete", count=len(actions), **details)
        if actions and not missing_actions
        else _failed("solver_rewrite_current_actions_complete", missing=missing_actions, count=len(actions), **details)
    )
    checks.append(
        _ok("solver_rewrite_expected_movements_match_definition", **details)
        if _expected_movements_match_definition(entry)
        else _failed(
            "solver_rewrite_expected_movements_match_definition",
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
        failures.append(_failed("solver_rewrite_timeout_regression", **details))
        return "failed", failures
    if result != STATUS_UNKNOWN:
        failures.append(
            _failed("solver_rewrite_unexpected_final_result", current_result=result or MISSING_SENTINEL, **details)
        )
        return "failed", failures
    reclassification_failures = _accepted_reclassification_failures(entry)
    if reclassification_failures is not None:
        if not reclassification_failures:
            return "retired_to_return_coverage_gap", ()
        failures.extend(reclassification_failures)
        return "failed", failures
    frozen_targets = _canonical_targets(entry.get("target_object_keys"))
    current_targets = _canonical_targets(_current_targets(entry))
    if not frozen_targets or current_targets != frozen_targets:
        failures.append(
            _failed("solver_rewrite_target_set_changed", expected=frozen_targets, actual=current_targets, **details)
        )
    frozen_actions = _canonical_actions(entry.get("required_completion_actions"))
    current_actions = _canonical_actions(_current_actions(entry))
    if not frozen_actions or current_actions != frozen_actions:
        failures.append(
            _failed("solver_rewrite_required_actions_changed", expected=frozen_actions, actual=current_actions, **details)
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
        if phase3_manifest.get("manifest_kind") == "phase3_solver_rewrite_lane7_representatives"
        else _failed("phase3_pre_fix_manifest_kind")
    )
    checks.append(
        _ok("phase3_pre_fix_manifest_ready")
        if phase3_manifest.get("phase3_lane7_ready") is True
        else _failed("phase3_pre_fix_manifest_ready")
    )
    checks.append(_identity_set_check("phase3_pre_fix_entries", phase3_manifest.get("entries"), DEFAULT_REPRESENTATIVES))
    implementation = phase3_manifest.get("implementation_manifest")
    if isinstance(implementation, Mapping):
        checks.append(_ok("phase3_pre_fix_implementation_manifest_present"))
        expected_targets = _canonical_targets(implementation.get("expected_solver_rewrite_targets"))
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
            if expected_actions and expected_actions == actual_actions
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
        expected_reclassifications = _canonical_reclassifications(
            implementation.get("accepted_post_fix_reclassifications")
        )
        actual_reclassifications = _canonical_reclassifications(
            [
                entry.get("accepted_post_fix_reclassification")
                for entry in phase3_manifest.get("entries") or ()
                if isinstance(entry, Mapping) and entry.get("accepted_post_fix_reclassification")
            ]
        )
        checks.append(
            _ok("phase3_pre_fix_implementation_reclassifications_consistent")
            if expected_reclassifications and expected_reclassifications == actual_reclassifications
            else _failed(
                "phase3_pre_fix_implementation_reclassifications_consistent",
                expected=expected_reclassifications,
                actual=actual_reclassifications,
            )
        )
    else:
        checks.append(_failed("phase3_pre_fix_implementation_manifest_present"))
    for entry in entries:
        for failure in entry.get("post_fix_failures") or ():
            checks.append(failure)
        checks.append(
            _ok("solver_rewrite_post_fix_expected_movement", post_fix_status=entry.get("post_fix_status"), **_entry_details(entry))
            if entry.get("post_fix_status") in {"pending_proof", "retired_to_return_coverage_gap"}
            else _failed("solver_rewrite_post_fix_expected_movement", post_fix_status=entry.get("post_fix_status") or MISSING_SENTINEL, **_entry_details(entry))
        )
    return checks


def _implementation_manifest(entries: Sequence[Mapping[str, Any]]) -> Dict[str, Any]:
    return {
        "lane_id": "phase3_solver_rewrite_lane7",
        "target_reason_id": "solver_proven_rewrite_no_change",
        "baseline_mode": "pending_proof_against_pre_fix_manifest",
        "expected_movement_entries": _canonical_movements(
            [
                movement
                for entry in entries
                for movement in (entry.get("expected_movements") or ())
            ]
        ),
        "expected_solver_rewrite_targets": _canonical_targets(
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
        "accepted_post_fix_reclassifications": _canonical_reclassifications(
            [
                entry.get("accepted_post_fix_reclassification")
                for entry in entries
                if entry.get("accepted_post_fix_reclassification")
            ]
        ),
    }


def _accepted_reclassification_failures(entry: Mapping[str, Any]) -> Optional[Sequence[Dict[str, Any]]]:
    accepted = entry.get("accepted_post_fix_reclassification")
    if not isinstance(accepted, Mapping):
        return None
    current = entry.get("current_observation") if isinstance(entry.get("current_observation"), Mapping) else {}
    details = _entry_details(entry)
    failures: list[Dict[str, Any]] = []
    if accepted.get("status") != "retired_to_return_coverage_gap":
        failures.append(
            _failed(
                "solver_rewrite_accepted_reclassification_status",
                expected="retired_to_return_coverage_gap",
                actual=accepted.get("status") or MISSING_SENTINEL,
                **details,
            )
        )
    if _canonical_reclassifications([accepted]) != _canonical_reclassifications(
        [DEFAULT_REPRESENTATIVES[0].get("accepted_post_fix_reclassification")]
    ):
        failures.append(
            _failed(
                "solver_rewrite_accepted_reclassification_definition",
                expected=_canonical_reclassifications(
                    [DEFAULT_REPRESENTATIVES[0].get("accepted_post_fix_reclassification")]
                ),
                actual=_canonical_reclassifications([accepted]),
                **details,
            )
        )
    observed = set(current.get("observed_reason_ids") or ())
    if observed != {"return_coverage_gap"}:
        failures.append(
            _failed(
                "solver_rewrite_accepted_reclassification_reason_set",
                expected=["return_coverage_gap"],
                actual=sorted(observed),
                **details,
            )
        )
    expected_movements = accepted.get("accepted_movements") or ()
    failures.extend(_accepted_reclassification_tuple_failures(current, expected_movements, details))
    failures.extend(
        _accepted_reclassification_object_evidence_failures(current, expected_movements, details)
    )
    return tuple(failures)


def _accepted_reclassification_tuple_failures(
    current: Mapping[str, Any],
    expected_movements: Any,
    details: Mapping[str, Any],
) -> Sequence[Dict[str, Any]]:
    failures: list[Dict[str, Any]] = []
    movements = tuple(
        movement for movement in (expected_movements or ()) if isinstance(movement, Mapping)
    )
    if not movements:
        return [_failed("solver_rewrite_accepted_reclassification_movements_missing", **details)]
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
                    "solver_rewrite_accepted_reclassification_tuple_missing",
                    movement_id=movement.get("id") or MISSING_SENTINEL,
                    expected_tuple=list(expected_tuple),
                    **details,
                )
            )
    return tuple(failures)


def _accepted_reclassification_object_evidence_failures(
    current: Mapping[str, Any],
    expected_movements: Any,
    details: Mapping[str, Any],
) -> Sequence[Dict[str, Any]]:
    failures: list[Dict[str, Any]] = []
    records = [
        record
        for record in current.get("reason_records") or ()
        if isinstance(record, Mapping) and record.get("reason_id") == "return_coverage_gap"
    ]
    if not records:
        failures.append(_failed("solver_rewrite_accepted_reclassification_record_missing", **details))
    for record in records:
        expected_record = _accepted_reclassification_record_definition(record, expected_movements)
        if not expected_record:
            failures.append(
                _failed(
                    "solver_rewrite_accepted_reclassification_record_definition_missing",
                    expected_tuple=list(record.get("tuple") or ()),
                    **details,
                )
            )
        else:
            expected_refs = tuple(str(ref) for ref in expected_record.get("expected_evidence_refs") or ())
            actual_refs = tuple(str(ref) for ref in record.get("evidence_refs") or ())
            if actual_refs != expected_refs:
                failures.append(
                    _failed(
                        "solver_rewrite_accepted_reclassification_record_evidence_refs",
                        expected=list(expected_refs),
                        actual=list(actual_refs),
                        **details,
                    )
                )
        if not _return_coverage_object_target_key_is_specific(record.get("object_target_key")):
            failures.append(
                _failed(
                    "solver_rewrite_accepted_reclassification_record_target",
                    object_target_key=_jsonable(record.get("object_target_key")),
                    **details,
                )
            )
    actions = [
        action
        for action in current.get("proof_actions") or ()
        if isinstance(action, Mapping) and action.get("reason_id") == "return_coverage_gap"
    ]
    expected_stages = {"return_partition_extraction", "return_guard_coverage"}
    action_definitions = _accepted_reclassification_action_definitions(expected_movements)
    observed_stages = {action.get("proof_stage") for action in actions}
    if not expected_stages.issubset(observed_stages):
        failures.append(
            _failed(
                "solver_rewrite_accepted_reclassification_actions_missing",
                expected=sorted(expected_stages),
                actual=sorted(str(stage) for stage in observed_stages),
                **details,
            )
        )
    for action in actions:
        if action.get("proof_stage") not in expected_stages:
            continue
        expected_action = action_definitions.get(str(action.get("proof_stage")))
        if not expected_action:
            failures.append(
                _failed(
                    "solver_rewrite_accepted_reclassification_action_definition_missing",
                    proof_stage=action.get("proof_stage") or MISSING_SENTINEL,
                    **details,
                )
            )
            continue
        if tuple(action.get("tuple") or ()) != tuple(expected_action.get("tuple") or ()):
            failures.append(
                _failed(
                    "solver_rewrite_accepted_reclassification_action_tuple",
                    proof_stage=action.get("proof_stage") or MISSING_SENTINEL,
                    expected_tuple=list(expected_action.get("tuple") or ()),
                    actual_tuple=list(action.get("tuple") or ()),
                    **details,
                )
            )
        expected_evidence_kind = expected_action.get("expected_evidence_kind") or MISSING_SENTINEL
        if action.get("evidence_kind") != expected_evidence_kind:
            failures.append(
                _failed(
                    "solver_rewrite_accepted_reclassification_action_evidence_kind",
                    proof_stage=action.get("proof_stage") or MISSING_SENTINEL,
                    expected=expected_evidence_kind,
                    actual=action.get("evidence_kind") or MISSING_SENTINEL,
                    **details,
                )
            )
        expected_required = tuple(expected_action.get("required_evidence") or ())
        if tuple(action.get("required_evidence") or ()) != expected_required:
            failures.append(
                _failed(
                    "solver_rewrite_accepted_reclassification_action_required_evidence",
                    proof_stage=action.get("proof_stage") or MISSING_SENTINEL,
                    expected=list(expected_required),
                    actual=list(action.get("required_evidence") or ()),
                    **details,
                )
            )
        expected_refs = tuple(str(ref) for ref in expected_action.get("expected_evidence_refs") or ())
        actual_refs = tuple(str(ref) for ref in action.get("evidence_refs") or ())
        if actual_refs != expected_refs:
            failures.append(
                _failed(
                    "solver_rewrite_accepted_reclassification_action_evidence_refs",
                    proof_stage=action.get("proof_stage") or MISSING_SENTINEL,
                    expected=list(expected_refs),
                    actual=list(actual_refs),
                    **details,
                )
            )
        if action.get("raw_proof_obligation_id_present") is not True:
            failures.append(
                _failed(
                    "solver_rewrite_accepted_reclassification_action_raw_proof_id",
                    proof_stage=action.get("proof_stage") or MISSING_SENTINEL,
                    **details,
                )
            )
        if action.get("raw_object_target_key_present") is not True:
            failures.append(
                _failed(
                    "solver_rewrite_accepted_reclassification_action_raw_target",
                    proof_stage=action.get("proof_stage") or MISSING_SENTINEL,
                    **details,
                )
            )
        if not _return_coverage_object_target_key_is_specific(action.get("object_target_key")):
            failures.append(
                _failed(
                    "solver_rewrite_accepted_reclassification_action_target",
                    proof_stage=action.get("proof_stage") or MISSING_SENTINEL,
                    object_target_key=_jsonable(action.get("object_target_key")),
                    **details,
                )
            )
        if not _action_has_expected_id(action):
            failures.append(
                _failed(
                    "solver_rewrite_accepted_reclassification_action_proof_id",
                    proof_stage=action.get("proof_stage") or MISSING_SENTINEL,
                    proof_obligation_id=_jsonable(action.get("proof_obligation_id")),
                    **details,
                )
            )
    return tuple(failures)


def _accepted_reclassification_record_definition(
    record: Mapping[str, Any],
    expected_movements: Any,
) -> Optional[Mapping[str, Any]]:
    record_tuple = tuple(record.get("tuple") or ())
    for movement in expected_movements or ():
        if not isinstance(movement, Mapping):
            continue
        if movement.get("count_kind") != UnknownCountKind.REASON_RECORD.value:
            continue
        if tuple(movement.get("tuple") or ()) == record_tuple:
            return movement
    return None


def _accepted_reclassification_action_definitions(
    expected_movements: Any,
) -> Dict[str, Mapping[str, Any]]:
    definitions: Dict[str, Mapping[str, Any]] = {}
    for movement in expected_movements or ():
        if not isinstance(movement, Mapping):
            continue
        if movement.get("count_kind") != UnknownCountKind.PROOF_ACTION.value:
            continue
        expected_tuple = tuple(movement.get("tuple") or ())
        if len(expected_tuple) < 6:
            continue
        proof_stage = expected_tuple[5]
        if not isinstance(proof_stage, str) or not proof_stage:
            continue
        definitions[proof_stage] = movement
    return definitions


def _canonical_reclassifications(value: Any) -> Tuple[Any, ...]:
    canonical = []
    for entry in value or ():
        if not isinstance(entry, Mapping):
            continue
        canonical.append(
            {
                "status": entry.get("status"),
                "reason": entry.get("reason"),
                "accepted_movements": _canonical_movements(entry.get("accepted_movements")),
            }
        )
    return tuple(sorted(canonical, key=_canonical_json))


def _current_targets(entry: Any) -> Sequence[Any]:
    current = entry.get("current_observation") if isinstance(entry, Mapping) else None
    if not isinstance(current, Mapping):
        return ()
    targets = []
    for record in current.get("reason_records") or ():
        if not isinstance(record, Mapping):
            continue
        if record.get("reason_id") != "solver_proven_rewrite_no_change":
            continue
        if record.get("evidence_kind") != SOLVER_EVIDENCE_KIND:
            continue
        if not _object_target_key_is_specific_solver_rewrite_candidate(record.get("object_target_key")):
            continue
        if record.get("proof_obligation_id") is None:
            continue
        if not _record_has_expected_id(record):
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
        if action.get("reason_id") != "solver_proven_rewrite_no_change":
            continue
        if not _object_target_key_is_specific_solver_rewrite_candidate(action.get("object_target_key")):
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


def _missing_actions(entry: Mapping[str, Any]) -> Sequence[Dict[str, Any]]:
    current_targets = _canonical_targets(_current_targets(entry))
    action_keys = {
        (_canonical_json(action.get("object_target_key")), action.get("proof_kind"), action.get("proof_stage"))
        for action in _current_actions(entry)
    }
    missing = []
    for target in current_targets:
        key = (_canonical_json(target), SOLVER_PROOF_KIND, SOLVER_PROOF_STAGE)
        if key not in action_keys:
            missing.append(
                {
                    "object_target_key": target,
                    "proof_kind": SOLVER_PROOF_KIND,
                    "proof_stage": SOLVER_PROOF_STAGE,
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


def _record_has_expected_id(record: Mapping[str, Any]) -> bool:
    expected = build_proof_obligation_id(
        record.get("reason_id"),
        record.get("proof_stage"),
        record.get("recovery_proof_kind"),
        record.get("evidence_kind"),
        record.get("object_target_key"),
    )
    return _normalize_nested_tuple(record.get("proof_obligation_id")) == _normalize_nested_tuple(expected)


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
    return (
        tuple(action.get("tuple") or ()) == SOLVER_ACTION_TUPLE
        and action.get("status") == "planned"
        and action.get("stage") == "S_PAIRWISE"
        and action.get("proof_kind") == SOLVER_PROOF_KIND
        and action.get("proof_stage") == SOLVER_PROOF_STAGE
        and action.get("evidence_kind") == SOLVER_EVIDENCE_KIND
        and tuple(action.get("required_evidence") or ()) == SOLVER_REQUIRED_EVIDENCE
    )


def _expected_movements_match_definition(entry: Mapping[str, Any]) -> bool:
    return _canonical_movements(entry.get("expected_movements")) == _canonical_movements(
        DEFAULT_REPRESENTATIVES[0]["expected_movements"]
    )


def _object_target_key_is_specific_solver_rewrite_candidate(value: Any) -> bool:
    target = _normalize_nested_tuple(value)
    if not isinstance(target, tuple) or len(target) != 5 or target[0] != "solver_rewrite_candidate":
        return False
    if _nested_contains_diagnostic_reason(target):
        return False
    pair = target[1]
    stage = target[2]
    return (
        isinstance(pair, tuple)
        and len(pair) == 2
        and pair[0] == "pair"
        and _text_identity_is_specific(pair[1])
        and isinstance(stage, tuple)
        and len(stage) == 2
        and stage == ("rewrite_stage", SOLVER_PROOF_STAGE)
        and _solver_rewrite_side_is_specific(target[3], "left")
        and _solver_rewrite_side_is_specific(target[4], "right")
    )


def _solver_rewrite_side_is_specific(value: Any, expected_side: str) -> bool:
    side = _normalize_nested_tuple(value)
    if not isinstance(side, tuple) or len(side) != 7:
        return False
    if side[0] != "solver_rewrite_side" or side[1] != expected_side:
        return False
    return_storage = side[3]
    width = _return_storage_width(return_storage)
    return (
        _analysis_entry_key_is_specific(side[2])
        and _return_storage_is_specific(return_storage)
        and _unresolved_return_case_partition_member_is_specific(side[4], width)
        and _typed_expression_key_is_specific(side[5])
        and _guards_key_is_specific(side[6])
    )


def _typed_expression_key_is_specific(value: Any) -> bool:
    typed = _normalize_nested_tuple(value)
    return (
        isinstance(typed, tuple)
        and len(typed) == 2
        and typed[0] == "typed_expression_key"
        and _expression_provenance_is_specific(typed[1])
    )


def _guards_key_is_specific(value: Any) -> bool:
    guards = _normalize_nested_tuple(value)
    return (
        isinstance(guards, tuple)
        and len(guards) == 2
        and guards[0] == "guards"
        and isinstance(guards[1], tuple)
        and bool(guards[1])
        and all(_return_guard_like_key_is_specific(guard) for guard in guards[1])
    )


def _binary_direction_matches(entry: Mapping[str, Any], current: Mapping[str, Any]) -> bool:
    expected1 = entry.get("expected_observed_binary1_name")
    expected2 = entry.get("expected_observed_binary2_name")
    return (
        (not expected1 or current.get("observed_binary1_name") == expected1)
        and (not expected2 or current.get("observed_binary2_name") == expected2)
    )


def main(argv: Optional[Sequence[str]] = None) -> int:
    parser = argparse.ArgumentParser(description="Validate Phase 3 lane 7 solver rewrite representatives.")
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
        path = build_phase3_solver_rewrite_lane7_post_fix_gate(
            baseline_raw_dir=args.baseline_raw_dir,
            output_dir=args.output_dir,
            current_log_roots=current_roots,
            baseline_log_roots=baseline_roots,
            phase3_manifest_path=args.phase3_manifest,
            phase3_manifest_sha256=args.phase3_manifest_sha256,
        )
        if args.require_ready:
            validate_phase3_solver_rewrite_lane7_post_fix_gate(_read_json(path))
    else:
        path = build_phase3_solver_rewrite_lane7_manifest(
            baseline_raw_dir=args.baseline_raw_dir,
            output_dir=args.output_dir,
            current_log_roots=current_roots,
            baseline_log_roots=baseline_roots,
        )
        if args.require_ready:
            validate_phase3_solver_rewrite_lane7_manifest(_read_json(path))
    print(path)
    return 0


if __name__ == "__main__":  # pragma: no cover
    raise SystemExit(main())
