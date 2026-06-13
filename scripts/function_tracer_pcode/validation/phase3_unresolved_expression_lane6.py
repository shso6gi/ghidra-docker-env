# -*- coding: utf-8 -*-
"""Freeze Phase 3 lane 6 representatives for unresolved-expression work."""

from __future__ import annotations

import argparse
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Dict, Mapping, Optional, Sequence, Tuple

from .result_summary import STATUS_EQ, STATUS_TIMEOUT, STATUS_UNKNOWN, classify_result_payload
from .unknown_reason_summary import _extract_final_unknown_reasons, _global_reason_tuple_from_record
from .phase3_return_width_bridge_lane2 import (
    _canonical_json,
    _canonical_movements,
    _canonical_targets,
    _call_callee_key_is_specific,
    _completed_recovery_proof_summaries,
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
UNRESOLVED_INDEPENDENT_SEMANTIC_RECURRENCE_PROOF_SOURCE = (
    "independent_semantic_recurrence_solver_replay"
)
UNRESOLVED_DEFERRED_CALL_PROOF_STAGES = (
    "deferred_call_return_resolution",
    "deferred_call_result_equivalence",
)
UNRESOLVED_OPAQUE_VOID_PROOF_STAGES = (
    "opaque_unknown_return_origin_resolution",
    "opaque_unknown_return_value_equivalence",
)
UNRESOLVED_PROOF_STAGES = (
    UNRESOLVED_GENERIC_PROOF_STAGES
    + UNRESOLVED_PHI_CIRCULAR_PROOF_STAGES
    + UNRESOLVED_DEFERRED_CALL_PROOF_STAGES
    + UNRESOLVED_OPAQUE_VOID_PROOF_STAGES
)
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
    "B1": "function_call_test-arm64-clang-O0",
    "B2": "function_call_test-arm64-clang-O1",
    "B3": "function_call_test-arm64-clang-O2",
    "B10": "function_call_test-mips64-clang-O1",
    "B11": "function_call_test-mips64-clang-O2",
    "B12": "function_call_test-mips64-clang-O3",
    "B13": "function_call_test-mips64-gcc-O0",
    "B15": "function_call_test-mips64-gcc-O2",
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
    {
        "id": "representative-unresolved-expression-is-even-deferred-call-return-current-transition",
        "category": "function_call",
        "function": "fc_is_even",
        "binary_pair": "B10_B13",
        "expected_observed_binary1_name": FUNCTION_CALL_BINARY_NAMES["B10"],
        "expected_observed_binary2_name": FUNCTION_CALL_BINARY_NAMES["B13"],
        "required_reason_ids": ["unresolved_expression"],
        "role": "deferred-call return unresolved-expression current-transition diagnostic",
        "expected_movements": [
            _expected_reason_record("unresolved-expression-reason-record"),
        ],
    },
    {
        "id": "representative-unresolved-expression-is-odd-opaque-void-return-current-transition",
        "category": "function_call",
        "function": "fc_is_odd",
        "binary_pair": "B1_B2",
        "expected_observed_binary1_name": FUNCTION_CALL_BINARY_NAMES["B1"],
        "expected_observed_binary2_name": FUNCTION_CALL_BINARY_NAMES["B2"],
        "required_reason_ids": ["unresolved_expression"],
        "role": "opaque void return unresolved-expression current-transition diagnostic",
        "expected_movements": [
            _expected_reason_record("unresolved-expression-reason-record"),
        ],
    },
)

DEFAULT_TIMEOUT_TRANSITION_REPRESENTATIVES: Tuple[Mapping[str, Any], ...] = (
    {
        "id": "representative-recursive-sum-b10-b11-unresolved-to-timeout",
        "category": "function_call",
        "function": "fc_recursive_sum",
        "binary_pair": "B10_B11",
        "expected_observed_binary1_name": FUNCTION_CALL_BINARY_NAMES["B10"],
        "expected_observed_binary2_name": FUNCTION_CALL_BINARY_NAMES["B11"],
        "expected_baseline_result": STATUS_UNKNOWN,
        "expected_current_result": STATUS_TIMEOUT,
        "expected_baseline_reason_ids": ["sat_unsafety", "unresolved_expression"],
        "expected_current_reason_ids": ["solver_unknown_timeout"],
        "role": "current timeout transition representative for unresolved/sat recursive summary work",
    },
    {
        "id": "representative-recursive-sum-b10-b15-coverage-to-timeout",
        "category": "function_call",
        "function": "fc_recursive_sum",
        "binary_pair": "B10_B15",
        "expected_observed_binary1_name": FUNCTION_CALL_BINARY_NAMES["B10"],
        "expected_observed_binary2_name": FUNCTION_CALL_BINARY_NAMES["B15"],
        "expected_baseline_result": STATUS_UNKNOWN,
        "expected_current_result": STATUS_TIMEOUT,
        "expected_baseline_reason_ids": ["equivalence_blocking_unsafety", "return_coverage_gap"],
        "expected_current_reason_ids": ["solver_unknown_timeout"],
        "role": "current timeout transition representative for coverage/effect recursive summary work",
    },
    {
        "id": "representative-recursive-sum-b1-b3-unresolved-to-timeout",
        "category": "function_call",
        "function": "fc_recursive_sum",
        "binary_pair": "B1_B3",
        "expected_observed_binary1_name": FUNCTION_CALL_BINARY_NAMES["B1"],
        "expected_observed_binary2_name": FUNCTION_CALL_BINARY_NAMES["B3"],
        "expected_baseline_result": STATUS_UNKNOWN,
        "expected_current_result": STATUS_TIMEOUT,
        "expected_baseline_reason_ids": ["sat_unsafety", "unresolved_expression"],
        "expected_current_reason_ids": ["solver_unknown_timeout"],
        "role": "current timeout transition representative for arm64 recursive summary work",
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


def build_phase3_unresolved_expression_timeout_transition_audit(
    *,
    baseline_raw_dir: Path,
    output_dir: Path,
    current_log_roots: Mapping[str, Path],
    baseline_log_roots: Mapping[str, Path],
    representatives: Sequence[Mapping[str, Any]] = DEFAULT_TIMEOUT_TRANSITION_REPRESENTATIVES,
) -> Path:
    raw_dir = Path(baseline_raw_dir)
    output = Path(output_dir)
    output.mkdir(parents=True, exist_ok=True)
    baseline_manifest = _read_json(raw_dir / "artifact_manifest.json")
    target_keys = tuple(_entry_key(entry) for entry in representatives)
    current_records = _records_by_key(current_log_roots, target_keys=target_keys)
    baseline_records = _records_by_key(baseline_log_roots, target_keys=target_keys)
    entries = [
        _materialize_timeout_transition_entry(raw_entry, current_records, baseline_records)
        for raw_entry in representatives
    ]
    readiness = _timeout_transition_readiness(entries)
    manifest = {
        "manifest_version": MANIFEST_VERSION,
        "manifest_kind": "phase3_unresolved_expression_timeout_transition_representatives",
        "artifact_role": "derived_audit_timeout_transition_monitor",
        "baseline_id": baseline_manifest.get("baseline_id") or MISSING_SENTINEL,
        "baseline_git_head": baseline_manifest.get("git_head") or MISSING_SENTINEL,
        "created_at": datetime.now(timezone.utc).isoformat(),
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
                "concrete fc_recursive_sum function x binary_pair id",
                "baseline final result is UNKNOWN with recorded blocker reasons",
                "current final result is TIMEOUT with solver_unknown_timeout",
                "used only to monitor timeout movement while semantic lanes progress",
            ],
        },
        "phase3_lane6_timeout_transition_ready": readiness["ready"],
        "readiness": readiness,
        "entries": entries,
    }
    path = output / "unresolved_expression_timeout_transition_representatives.json"
    _write_json(path, manifest)
    return path


def validate_phase3_unresolved_expression_timeout_transition_audit(manifest: Mapping[str, Any]) -> None:
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
        failures.append(_failed("unresolved_expression_timeout_transition_readiness_missing"))
    if manifest.get("manifest_kind") != "phase3_unresolved_expression_timeout_transition_representatives":
        failures.append(_failed("unresolved_expression_timeout_transition_manifest_kind"))
    if not manifest.get("phase3_lane6_timeout_transition_ready"):
        failures.append(_failed("unresolved_expression_timeout_transition_not_ready"))
    if failures:
        raise ValueError(f"Phase 3 lane 6 timeout transition audit is not ready: {failures!r}")


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


def _materialize_timeout_transition_entry(
    raw_entry: Mapping[str, Any],
    current_records: Mapping[Tuple[str, str, str], Mapping[str, Any]],
    baseline_records: Mapping[Tuple[str, str, str], Mapping[str, Any]],
) -> Dict[str, Any]:
    entry = dict(raw_entry)
    key = _entry_key(raw_entry)
    entry["baseline_observation"] = _observation(raw_entry, baseline_records.get(key))
    entry["current_observation"] = _observation(raw_entry, current_records.get(key))
    entry["transition"] = {
        "from_final_result": entry["baseline_observation"].get("final_result") or MISSING_SENTINEL,
        "to_final_result": entry["current_observation"].get("final_result") or MISSING_SENTINEL,
        "from_reason_ids": list(entry["baseline_observation"].get("observed_reason_ids") or ()),
        "to_reason_ids": list(entry["current_observation"].get("observed_reason_ids") or ()),
    }
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
            "proof_action_object_evidence_status_counts": {},
            "pair_lowering_diagnostic_status_counts": {},
            "pair_lowering_diagnostic_relation_counts": {},
        }
    payload = record.get("payload") if isinstance(record.get("payload"), Mapping) else {}
    reasons = _extract_final_unknown_reasons(payload)
    reason_records = [_reason_to_dict(reason) for reason in reasons]
    proof_actions = [
        action.to_dict()
        for action in build_unknown_recovery_actions(reasons)
    ]
    unresolved_reason_records = [
        reason
        for reason in reason_records
        if isinstance(reason, Mapping) and reason.get("reason_id") == "unresolved_expression"
    ]
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
        "proof_actions": proof_actions,
        "completed_recovery_proof_evidence": _completed_recovery_proof_summaries(payload),
        "proof_action_object_evidence_status_counts": (
            _proof_action_object_evidence_status_counts(proof_actions)
        ),
        "pair_lowering_diagnostic_status_counts": (
            _pair_lowering_diagnostic_status_counts(unresolved_reason_records)
        ),
        "pair_lowering_diagnostic_relation_counts": (
            _pair_lowering_diagnostic_relation_counts(unresolved_reason_records)
        ),
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
        diagnostic_statuses = _pair_lowering_diagnostic_status_counts(unresolved_records)
        diagnostic_relations = _pair_lowering_diagnostic_relation_counts(unresolved_records)
        observations.append(
            {
                "category": category,
                "function": function,
                "binary_pair": binary_pair,
                "log_path": observation.get("log_path") or MISSING_SENTINEL,
                "final_result": observation.get("final_result") or MISSING_SENTINEL,
                "unresolved_expression_reason_record_count": len(unresolved_records),
                "observed_reason_ids": list(observation.get("observed_reason_ids") or ()),
                "proof_action_object_evidence_status_counts": (
                    observation.get("proof_action_object_evidence_status_counts") or {}
                ),
                "pair_lowering_diagnostic_status_counts": diagnostic_statuses,
                "pair_lowering_diagnostic_relation_counts": diagnostic_relations,
            }
        )
    return tuple(observations)


def _proof_action_object_evidence_status_counts(actions: Sequence[Mapping[str, Any]]) -> Dict[str, int]:
    counts: Dict[str, int] = {}
    for action in actions or ():
        if not isinstance(action, Mapping):
            continue
        if action.get("reason_id") != "unresolved_expression":
            continue
        if action.get("proof_kind") != UNRESOLVED_PROOF_KIND:
            continue
        if action.get("proof_stage") not in UNRESOLVED_PROOF_STAGES:
            continue
        if action.get("status") not in {"planned", "pending_proof", "proof_complete"}:
            continue
        status = _pending_action_object_evidence_status(action)
        counts[status] = counts.get(status, 0) + 1
    return dict(sorted(counts.items()))


def _pair_lowering_diagnostic_status_counts(reason_records: Sequence[Mapping[str, Any]]) -> Dict[str, int]:
    counts: Dict[str, int] = {}
    for reason in reason_records or ():
        target = _normalize_nested_tuple(reason.get("object_target_key"))
        for diagnostic in _nested_tuples_with_tag(target, "pair_lowering_diagnostic"):
            status = _pair_lowering_diagnostic_status(diagnostic)
            if status is None:
                continue
            counts[status] = counts.get(status, 0) + 1
    return dict(sorted(counts.items()))


def _pair_lowering_diagnostic_status(value: Any) -> Optional[str]:
    diagnostic = _normalize_nested_tuple(value)
    if not isinstance(diagnostic, tuple) or not diagnostic or diagnostic[0] != "pair_lowering_diagnostic":
        return None
    for item in diagnostic[1:]:
        if isinstance(item, tuple) and len(item) == 2 and item[0] == "status":
            return str(item[1])
    return None


def _pair_lowering_diagnostic_relation_counts(
    reason_records: Sequence[Mapping[str, Any]],
) -> Dict[str, int]:
    counts: Dict[str, int] = {}
    for reason in reason_records or ():
        target = _normalize_nested_tuple(reason.get("object_target_key"))
        for diagnostic in _nested_tuples_with_tag(target, "pair_lowering_diagnostic"):
            fields = _tuple_fields(diagnostic)
            for field_name in (
                "unknown_count_relation",
                "value_shape_relation",
                "phi_origin_shape_relation",
            ):
                relation = _relation_value(fields.get(field_name))
                if relation is None:
                    continue
                key = f"{field_name}:{relation}"
                counts[key] = counts.get(key, 0) + 1
    return dict(sorted(counts.items()))


def _relation_value(value: Any) -> Optional[str]:
    relation = _normalize_nested_tuple(value)
    if not isinstance(relation, tuple):
        return None
    for item in relation[1:]:
        if isinstance(item, tuple) and len(item) == 2 and item[0] == "relation":
            return str(item[1])
    return None


def _tuple_fields(value: Any) -> Dict[str, Any]:
    normalized = _normalize_nested_tuple(value)
    if not isinstance(normalized, tuple):
        return {}
    return {
        item[0]: item[1]
        for item in normalized[1:]
        if isinstance(item, tuple) and len(item) == 2 and isinstance(item[0], str)
    }


def _nested_tuples_with_tag(value: Any, tag: str) -> Tuple[Tuple[Any, ...], ...]:
    found: list[Tuple[Any, ...]] = []

    def visit(item: Any) -> None:
        normalized = _normalize_nested_tuple(item)
        if isinstance(normalized, tuple):
            if normalized and normalized[0] == tag:
                found.append(normalized)
            for child in normalized:
                visit(child)
        elif isinstance(item, Mapping):
            for child in item.values():
                visit(child)
        elif isinstance(item, list):
            for child in item:
                visit(child)

    visit(value)
    return tuple(found)


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


def _timeout_transition_readiness(entries: Sequence[Mapping[str, Any]]) -> Dict[str, Any]:
    checks = []
    for entry in entries:
        checks.extend(_timeout_transition_entry_readiness(entry))
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
        "transition_count": len(entries),
    }


def _timeout_transition_entry_readiness(entry: Mapping[str, Any]) -> Sequence[Dict[str, Any]]:
    checks = []
    baseline = entry.get("baseline_observation") if isinstance(entry.get("baseline_observation"), Mapping) else {}
    current = entry.get("current_observation") if isinstance(entry.get("current_observation"), Mapping) else {}
    details = _entry_details(entry)
    expected_baseline = entry.get("expected_baseline_result") or STATUS_UNKNOWN
    expected_current = entry.get("expected_current_result") or STATUS_TIMEOUT
    expected_baseline_reasons = sorted(str(reason) for reason in (entry.get("expected_baseline_reason_ids") or ()))
    expected_current_reasons = sorted(str(reason) for reason in (entry.get("expected_current_reason_ids") or ()))
    actual_baseline_reasons = sorted(str(reason) for reason in (baseline.get("observed_reason_ids") or ()))
    actual_current_reasons = sorted(str(reason) for reason in (current.get("observed_reason_ids") or ()))
    if baseline.get("log_status") == "present":
        checks.append(_ok("timeout_transition_baseline_log_present", **details))
    else:
        checks.append(_failed("timeout_transition_baseline_log_present", **details))
    if current.get("log_status") == "present":
        checks.append(_ok("timeout_transition_current_log_present", **details))
    else:
        checks.append(_failed("timeout_transition_current_log_present", **details))
    if baseline.get("final_result") == expected_baseline:
        checks.append(_ok("timeout_transition_baseline_result", result=expected_baseline, **details))
    else:
        checks.append(
            _failed(
                "timeout_transition_baseline_result",
                expected=expected_baseline,
                actual=baseline.get("final_result") or MISSING_SENTINEL,
                **details,
            )
        )
    if current.get("final_result") == expected_current:
        checks.append(_ok("timeout_transition_current_result", result=expected_current, **details))
    else:
        checks.append(
            _failed(
                "timeout_transition_current_result",
                expected=expected_current,
                actual=current.get("final_result") or MISSING_SENTINEL,
                **details,
            )
        )
    if actual_baseline_reasons == expected_baseline_reasons:
        checks.append(_ok("timeout_transition_baseline_reasons", reasons=actual_baseline_reasons, **details))
    else:
        checks.append(
            _failed(
                "timeout_transition_baseline_reasons",
                expected=expected_baseline_reasons,
                actual=actual_baseline_reasons,
                **details,
            )
        )
    if actual_current_reasons == expected_current_reasons:
        checks.append(_ok("timeout_transition_current_reasons", reasons=actual_current_reasons, **details))
    else:
        checks.append(
            _failed(
                "timeout_transition_current_reasons",
                expected=expected_current_reasons,
                actual=actual_current_reasons,
                **details,
            )
        )
    if _binary_direction_matches(entry, current):
        checks.append(_ok("timeout_transition_current_binary_direction", **details))
    else:
        checks.append(
            _failed(
                "timeout_transition_current_binary_direction",
                observed_binary1=current.get("observed_binary1_name") or MISSING_SENTINEL,
                observed_binary2=current.get("observed_binary2_name") or MISSING_SENTINEL,
                **details,
            )
        )
    return checks


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
    if result == STATUS_EQ:
        failures.extend(_completed_unresolved_expression_recovery_failures(entry, current))
        if failures:
            return "failed", failures
        return "completed_recovery", ()
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
    frozen_target_keys = {_unresolved_expression_target_identity_key(target) for target in frozen_targets}
    current_target_keys = {_unresolved_expression_target_identity_key(target) for target in current_targets}
    if (
        _unresolved_expression_targets_cleared_under_other_unknown(
            entry,
            frozen_targets=frozen_targets,
            current_targets=current_targets,
        )
    ):
        return "resolved_under_other_conservative_unknown", ()
    if not frozen_targets:
        failures.append(
            _failed(
                "unresolved_expression_missing_frozen_targets",
                **details,
            )
        )
    extra_current_keys = current_target_keys - frozen_target_keys
    if extra_current_keys:
        failures.append(
            _failed(
                "unresolved_expression_target_set_changed",
                expected=frozen_targets,
                actual=current_targets,
                **details,
            )
        )
    cleared_failures = _unresolved_expression_cleared_target_failures(
        entry,
        frozen_targets=frozen_targets,
        current_targets=current_targets,
    )
    failures.extend(cleared_failures)
    if failures:
        return "failed", failures
    invalid_completed = _invalid_unresolved_expression_completed_actions(entry, current_targets)
    if invalid_completed:
        failures.append(
            _failed(
                "unresolved_expression_completed_proof_evidence_invalid",
                invalid_actions=invalid_completed,
                **details,
            )
        )
        return "failed", failures
    if _unresolved_expression_proof_actions_complete(entry, current_targets, require_completed=True):
        return "proof_complete", ()
    if _unresolved_expression_proof_actions_complete(entry, current_targets):
        return "pending_proof", ()
    return "pending_object_evidence", ()


def _unresolved_expression_cleared_target_failures(
    entry: Mapping[str, Any],
    *,
    frozen_targets: Sequence[Any],
    current_targets: Sequence[Any],
) -> Sequence[Dict[str, Any]]:
    current_target_keys = {
        _unresolved_expression_target_identity_key(target)
        for target in current_targets
    }
    cleared_targets = [
        target
        for target in frozen_targets
        if _unresolved_expression_target_identity_key(target) not in current_target_keys
    ]
    if not cleared_targets:
        return ()
    current = entry.get("current_observation") if isinstance(entry.get("current_observation"), Mapping) else {}
    completed = tuple(current.get("completed_recovery_proof_evidence") or ())
    missing = [
        target
        for target in cleared_targets
        if not _completed_unresolved_expression_evidence_matches_target(completed, target)
    ]
    if not missing:
        return ()
    return (
        _failed(
            "unresolved_expression_cleared_target_missing_evidence",
            missing_targets=_jsonable(missing),
            completed_count=len(completed),
            **_entry_details(entry),
        ),
    )


def _completed_unresolved_expression_recovery_failures(
    entry: Mapping[str, Any],
    current: Mapping[str, Any],
) -> Sequence[Dict[str, Any]]:
    frozen_targets = _canonical_targets(entry.get("target_object_keys"))
    completed = tuple(current.get("completed_recovery_proof_evidence") or ())
    details = _entry_details(entry)
    failures: list[Dict[str, Any]] = []
    if not frozen_targets:
        failures.append(_failed("unresolved_expression_completed_recovery_missing_frozen_targets", **details))
        return tuple(failures)
    missing = [
        target
        for target in frozen_targets
        if not _completed_unresolved_expression_evidence_matches_target(completed, target)
    ]
    if missing:
        failures.append(
            _failed(
                "unresolved_expression_completed_recovery_missing_evidence",
                missing_targets=_jsonable(missing),
                completed_count=len(completed),
                **details,
            )
        )
    return tuple(failures)


def _completed_unresolved_expression_evidence_matches_target(
    completed: Sequence[Any],
    target: Any,
) -> bool:
    for item in completed:
        if not isinstance(item, Mapping):
            continue
        evidence = item.get("evidence")
        if not isinstance(evidence, Mapping):
            continue
        if evidence.get("reason_id") != "unresolved_expression":
            continue
        evidence_target = evidence.get("object_target_key")
        if not _object_target_key_is_specific_unresolved_expression(evidence_target):
            continue
        if (
            _unresolved_expression_completed_recovery_target_identity_key(evidence_target)
            != _unresolved_expression_completed_recovery_target_identity_key(target)
        ):
            continue
        if _completed_unresolved_expression_semantic_recurrence_matches_target(
            evidence,
            target=target,
            evidence_target=evidence_target,
        ):
            return True
    return False


def _completed_unresolved_expression_semantic_recurrence_matches_target(
    evidence: Mapping[str, Any],
    *,
    target: Any,
    evidence_target: Any,
) -> bool:
    if evidence.get("proof_source") == "semantic_recurrence_solver_replay":
        return False
    if evidence.get("proof_rule") != "phi_circular_independent_semantic_recurrence_proof":
        return False
    object_evidence = evidence.get("object_evidence")
    if str(evidence.get("status") or MISSING_SENTINEL) not in {"complete", "completed", "proven"} and not (
        isinstance(object_evidence, (tuple, list))
        and _nested_contains_value(object_evidence, ("status", "complete"))
    ):
        return False
    if evidence.get("object_derived") is not True:
        if not (
            isinstance(object_evidence, (tuple, list))
            and _nested_contains_value(object_evidence, ("object_derived", True))
        ):
            return False
    action = {
        "object_evidence": evidence.get("object_evidence"),
        "object_target_key": evidence_target,
    }
    return all(
        _unresolved_expression_completed_action_evidence_is_specific(
            action,
            stage=stage,
            target=target,
        )
        for stage in _required_unresolved_proof_stages_for_target(target)
    )


def _nested_contains_value(value: Any, needle: Any) -> bool:
    if value == needle:
        return True
    if isinstance(value, Mapping):
        return any(
            _nested_contains_value(key, needle) or _nested_contains_value(item, needle)
            for key, item in value.items()
        )
    if isinstance(value, Sequence) and not isinstance(value, (str, bytes)):
        return any(_nested_contains_value(item, needle) for item in value)
    return False


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
        if entry.get("post_fix_status") in {
            "pending_object_evidence",
            "pending_proof",
            "proof_complete",
            "completed_recovery",
        }:
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
    *,
    require_completed: bool = False,
) -> bool:
    target_keys = {_unresolved_expression_target_identity_key(target) for target in current_targets}
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
        if require_completed:
            if action.get("status") != "proof_complete":
                continue
        elif action.get("status") not in {"planned", "pending_proof", "proof_complete"}:
            continue
        if not _unresolved_expression_action_required_evidence_is_specific(
            action,
            stage=str(stage),
        ):
            continue
        proof_obligation_id = action.get("proof_obligation_id")
        if proof_obligation_id is None or _nested_contains_missing_sentinel(proof_obligation_id):
            continue
        target = action.get("object_target_key")
        if not _object_target_key_is_specific_unresolved_expression(target):
            continue
        if (
            stage in UNRESOLVED_PHI_CIRCULAR_PROOF_STAGES
            and not _target_has_specific_phi_circular_relation_evidence(target)
        ):
            continue
        if require_completed and not _unresolved_expression_completed_action_evidence_is_specific(
            action,
            stage=str(stage),
            target=target,
        ):
            continue
        target_key = _unresolved_expression_target_identity_key(target)
        if target_key not in stages_by_target:
            continue
        stages_by_target[target_key].add(str(stage))
    return all(
        stages == set(_required_unresolved_proof_stages_for_target(target))
        for target in current_targets
        for target_key, stages in (
            (
                _unresolved_expression_target_identity_key(target),
                stages_by_target[_unresolved_expression_target_identity_key(target)],
            ),
        )
    )


def _unresolved_expression_action_required_evidence_is_specific(
    action: Mapping[str, Any],
    *,
    stage: str,
) -> bool:
    required_evidence = action.get("required_evidence")
    if not isinstance(required_evidence, list) or not required_evidence:
        return False
    evidence = {str(item) for item in required_evidence if isinstance(item, str)}
    if len(evidence) != len(required_evidence):
        return False
    if stage == "phi_circular_guard_condition_lowering":
        return {
            "object_target_key",
            "multiequal_pcode_op_ref",
            "guard_condition_key",
            "guard_condition_literals",
            "pair_lowering_diagnostic",
            "unknown_count_relation",
            "typed_lowering_rule",
        }.issubset(evidence)
    if stage == "recursive_summary_guard_equivalence":
        return {
            "left_phi_origin",
            "right_phi_origin",
            "guard_condition_pair",
            "pair_lowering_diagnostic",
            "summary_parameter_binding",
            "value_shape_relation",
        }.issubset(evidence)
    return True


def _unresolved_expression_completed_action_evidence_is_specific(
    action: Mapping[str, Any],
    *,
    stage: str,
    target: Any,
) -> bool:
    evidence = _normalize_nested_tuple(action.get("object_evidence"))
    if not isinstance(evidence, tuple) or len(evidence) not in {7, 9}:
        return False
    if evidence[0] != "completed_unresolved_expression_proof":
        return False
    fields = {
        item[0]: item[1]
        for item in evidence[1:]
        if isinstance(item, tuple) and len(item) == 2 and isinstance(item[0], str)
    }
    if fields.get("object_derived") is not True:
        return False
    if fields.get("status") != "complete":
        return False
    if fields.get("proof_rule") == "phi_circular_full_shape_match":
        return False
    if fields.get("proof_rule") == "phi_circular_semantic_recurrence_proof":
        return False
    if fields.get("proof_rule") != "phi_circular_independent_semantic_recurrence_proof":
        return False
    completed_stages = fields.get("completed_stages")
    if not isinstance(completed_stages, tuple) or stage not in completed_stages:
        return False
    evidence_target = fields.get("object_target_key")
    if not _object_target_key_is_specific_unresolved_expression(evidence_target):
        return False
    if (
        _unresolved_expression_completed_recovery_target_identity_key(evidence_target)
        != _unresolved_expression_completed_recovery_target_identity_key(target)
    ):
        return False
    diagnostic = fields.get("pair_lowering_diagnostic")
    if not _pair_lowering_diagnostic_is_specific(diagnostic):
        return False
    diagnostic_fields = {
        item[0]: item[1]
        for item in _normalize_nested_tuple(diagnostic)[1:]
        if isinstance(item, tuple) and len(item) == 2 and isinstance(item[0], str)
    }
    if diagnostic_fields.get("status") != "full_shape_match":
        return False
    if diagnostic_fields.get("left_guard_literals") != diagnostic_fields.get("right_guard_literals"):
        return False
    if diagnostic_fields.get("left_value_shape") != diagnostic_fields.get("right_value_shape"):
        return False
    if diagnostic_fields.get("opposing_guard_literals"):
        return False
    if len(evidence) == 9:
        stage_evidence = fields.get("stage_evidence")
        semantic_proof = fields.get("semantic_recurrence_proof")
        if not isinstance(stage_evidence, tuple) or not isinstance(semantic_proof, tuple):
            return False
        matching_stage_evidence = [
            item
            for item in stage_evidence
            if _pending_stage_evidence_matches(
                item,
                stage=stage,
                target=target,
                diagnostic=diagnostic,
                completed_recovery=True,
            )
        ]
        if len(matching_stage_evidence) != 1:
            return False
        if not _semantic_recurrence_proof_is_specific(
            semantic_proof,
            stage=stage,
            target=target,
            diagnostic=diagnostic,
            stage_evidence=stage_evidence,
            completed_recovery=True,
        ):
            return False
    else:
        return False
    return True


def _invalid_unresolved_expression_completed_actions(
    entry: Mapping[str, Any],
    current_targets: Sequence[Any],
) -> Sequence[Dict[str, Any]]:
    target_keys = {_unresolved_expression_target_identity_key(target) for target in current_targets}
    if not target_keys:
        return ()
    invalid: list[Dict[str, Any]] = []
    current = entry.get("current_observation") if isinstance(entry.get("current_observation"), Mapping) else {}
    for action in current.get("proof_actions") or ():
        if not isinstance(action, Mapping):
            continue
        if action.get("reason_id") != "unresolved_expression":
            continue
        if action.get("status") != "proof_complete":
            continue
        stage = str(action.get("proof_stage") or MISSING_SENTINEL)
        target = action.get("object_target_key")
        target_key = _unresolved_expression_target_identity_key(target)
        if target_key not in target_keys:
            continue
        if not _unresolved_expression_completed_action_evidence_is_specific(
            action,
            stage=stage,
            target=target,
        ):
            invalid.append(
                {
                    "proof_stage": stage,
                    "proof_obligation_id": _jsonable(action.get("proof_obligation_id")),
                }
            )
    return tuple(invalid)


def _required_unresolved_proof_stages_for_target(target: Any) -> Tuple[str, ...]:
    if _target_contains_originated_phi_circular(target):
        return UNRESOLVED_PHI_CIRCULAR_PROOF_STAGES
    if _target_contains_deferred_call_unknown(target):
        return UNRESOLVED_DEFERRED_CALL_PROOF_STAGES
    if _target_contains_void_opaque_unknown(target):
        return UNRESOLVED_OPAQUE_VOID_PROOF_STAGES
    return UNRESOLVED_GENERIC_PROOF_STAGES


def _target_contains_void_opaque_unknown(value: Any) -> bool:
    normalized = _normalize_nested_tuple(value)
    if isinstance(normalized, tuple):
        if (
            len(normalized) >= 2
            and normalized[0] == "opaque_unknown"
            and normalized[1] == "void"
        ):
            return True
        return any(_target_contains_void_opaque_unknown(item) for item in normalized)
    if isinstance(normalized, list):
        return any(_target_contains_void_opaque_unknown(item) for item in normalized)
    if isinstance(normalized, dict):
        return any(
            _target_contains_void_opaque_unknown(key)
            or _target_contains_void_opaque_unknown(item)
            for key, item in normalized.items()
        )
    return False


def _target_contains_deferred_call_unknown(value: Any) -> bool:
    normalized = _normalize_nested_tuple(value)
    if isinstance(normalized, tuple):
        if (
            len(normalized) >= 4
            and normalized[0] == "deferred_call"
            and normalized[1] == "call_out_of_scope"
        ):
            return True
        if (
            len(normalized) >= 2
            and normalized[0] == "unresolved_kinds"
            and isinstance(normalized[1], tuple)
            and "deferred_call_unknown" in normalized[1]
        ):
            return True
        return any(_target_contains_deferred_call_unknown(item) for item in normalized)
    if isinstance(normalized, dict):
        return any(
            _target_contains_deferred_call_unknown(key)
            or _target_contains_deferred_call_unknown(item)
            for key, item in normalized.items()
        )
    return False


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
    if isinstance(normalized, list):
        return any(_target_contains_originated_phi_circular(item) for item in normalized)
    if isinstance(normalized, dict):
        return any(
            _target_contains_originated_phi_circular(key)
            or _target_contains_originated_phi_circular(item)
            for key, item in normalized.items()
        )
    return False


def _target_has_specific_phi_circular_relation_evidence(value: Any) -> bool:
    normalized = _normalize_nested_tuple(value)
    if isinstance(normalized, tuple):
        if normalized and normalized[0] == "phi_circular_evidence":
            scope = normalized[1] if len(normalized) > 1 else None
            if (
                isinstance(scope, tuple)
                and len(scope) == 2
                and scope[0] == "location_scope"
                and _text_identity_is_specific(scope[1])
            ):
                return _phi_circular_evidence_is_specific(normalized, str(scope[1]))
            return False
        return any(_target_has_specific_phi_circular_relation_evidence(item) for item in normalized)
    if isinstance(normalized, list):
        return any(_target_has_specific_phi_circular_relation_evidence(item) for item in normalized)
    if isinstance(normalized, dict):
        return any(
            _target_has_specific_phi_circular_relation_evidence(key)
            or _target_has_specific_phi_circular_relation_evidence(item)
            for key, item in normalized.items()
        )
    return False


def _pending_proof_obligations(entry: Mapping[str, Any]) -> Sequence[Dict[str, Any]]:
    target_keys = {
        _unresolved_expression_target_identity_key(target)
        for target in _canonical_targets(entry.get("target_object_keys"))
    }
    obligations = []
    for action in _current_unresolved_expression_actions(entry):
        target_key = _unresolved_expression_target_identity_key(action.get("object_target_key"))
        if target_key not in target_keys:
            continue
        evidence_status = _pending_action_object_evidence_status(action)
        obligations.append(
            {
                "reason_id": action.get("reason_id") or MISSING_SENTINEL,
                "proof_kind": action.get("proof_kind") or MISSING_SENTINEL,
                "proof_stage": action.get("proof_stage") or MISSING_SENTINEL,
                "evidence_kind": action.get("evidence_kind") or MISSING_SENTINEL,
                "required_evidence": list(action.get("required_evidence") or ()),
                "proof_obligation_id": _jsonable(action.get("proof_obligation_id")),
                "completed_evidence_present": False,
                "object_evidence_status": evidence_status,
                "semantic_proof_status": "pending_semantic_proof",
                "status": (
                    "semantic_proof_required"
                    if evidence_status == "object_evidence_collected"
                    else "pending_evidence"
                ),
            }
        )
    return tuple(sorted(obligations, key=_canonical_json))


def _unresolved_expression_target_identity_key(value: Any) -> str:
    return _canonical_json(_strip_diagnostic_target_evidence(_jsonable(value)))


def _unresolved_expression_completed_recovery_target_identity_key(value: Any) -> str:
    return _canonical_json(
        _strip_completed_recovery_target_evidence(
            _strip_diagnostic_target_evidence(_jsonable(value))
        )
    )


def _strip_diagnostic_target_evidence(value: Any) -> Any:
    if isinstance(value, list):
        if (
            value
            and isinstance(value[0], str)
            and value[0] in {"typed_lowering_evidence", "pair_lowering_diagnostic"}
        ):
            return None
        stripped = []
        for item in value:
            child = _strip_diagnostic_target_evidence(item)
            if child is not None:
                stripped.append(child)
        return stripped
    if isinstance(value, tuple):
        if (
            value
            and isinstance(value[0], str)
            and value[0] in {"typed_lowering_evidence", "pair_lowering_diagnostic"}
        ):
            return None
        stripped = []
        for item in value:
            child = _strip_diagnostic_target_evidence(item)
            if child is not None:
                stripped.append(child)
        return tuple(stripped)
    if isinstance(value, Mapping):
        return {
            str(key): child
            for key, item in sorted(value.items(), key=lambda item: str(item[0]))
            for child in (_strip_diagnostic_target_evidence(item),)
            if child is not None
        }
    return value


def _strip_completed_recovery_target_evidence(value: Any) -> Any:
    if isinstance(value, list):
        if len(value) >= 5 and value[0] == "return_storage" and value[1] == "return_value":
            return value[:4]
        if len(value) == 4 and value[0] == "return_storage" and value[1] == "return_value":
            return value[:3]
        return [_strip_completed_recovery_target_evidence(item) for item in value]
    if isinstance(value, tuple):
        if len(value) >= 5 and value[0] == "return_storage" and value[1] == "return_value":
            return value[:4]
        if len(value) == 4 and value[0] == "return_storage" and value[1] == "return_value":
            return value[:3]
        return tuple(_strip_completed_recovery_target_evidence(item) for item in value)
    if isinstance(value, Mapping):
        return {
            key: _strip_completed_recovery_target_evidence(item)
            for key, item in value.items()
        }
    return value


def _required_completion_actions(entry: Mapping[str, Any]) -> Sequence[Dict[str, Any]]:
    actions = []
    for action in _current_unresolved_expression_actions(entry):
        evidence_status = _pending_action_object_evidence_status(action)
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
                "object_evidence_status": evidence_status,
                "semantic_proof_status": "pending_semantic_proof",
                "object_target_key": _jsonable(action.get("object_target_key")),
                "proof_obligation_id": _jsonable(action.get("proof_obligation_id")),
            }
        )
    return tuple(sorted(actions, key=_canonical_json))


def _pending_action_object_evidence_status(action: Mapping[str, Any]) -> str:
    stage = str(action.get("proof_stage") or MISSING_SENTINEL)
    target = action.get("object_target_key")
    if stage in UNRESOLVED_PHI_CIRCULAR_PROOF_STAGES:
        if _unresolved_expression_pending_action_evidence_is_specific(
            action,
            stage=stage,
            target=target,
        ):
            return "object_evidence_collected"
        if action.get("object_evidence") is not None:
            return "object_evidence_invalid"
    if stage in UNRESOLVED_DEFERRED_CALL_PROOF_STAGES:
        if _unresolved_expression_deferred_call_pending_action_evidence_is_specific(
            action,
            stage=stage,
            target=target,
        ):
            return "object_evidence_collected"
        if action.get("object_evidence") is not None:
            return "object_evidence_invalid"
    if stage in UNRESOLVED_OPAQUE_VOID_PROOF_STAGES:
        if _unresolved_expression_opaque_unknown_pending_action_evidence_is_specific(
            action,
            stage=stage,
            target=target,
        ):
            return "object_evidence_collected"
        if action.get("object_evidence") is not None:
            return "object_evidence_invalid"
    return "pending_evidence"


def _unresolved_expression_deferred_call_pending_action_evidence_is_specific(
    action: Mapping[str, Any],
    *,
    stage: str,
    target: Any,
) -> bool:
    evidence = _normalize_nested_tuple(action.get("object_evidence"))
    if not isinstance(evidence, tuple) or len(evidence) != 9:
        return False
    if evidence[0] != "unresolved_expression_diagnostic_evidence":
        return False
    fields = _tuple_fields(evidence)
    if fields.get("object_derived") is not True:
        return False
    if fields.get("status") != "object_evidence_collected":
        return False
    if fields.get("diagnostic_rule") != "deferred_call_object_proof_content":
        return False
    evidence_target = fields.get("object_target_key")
    if not _object_target_key_is_specific_unresolved_expression(evidence_target):
        return False
    if _unresolved_expression_target_identity_key(evidence_target) != _unresolved_expression_target_identity_key(target):
        return False
    pending_stages = fields.get("pending_stages")
    if not isinstance(pending_stages, tuple) or stage not in pending_stages:
        return False
    if not set(pending_stages).issubset(set(UNRESOLVED_DEFERRED_CALL_PROOF_STAGES)):
        return False
    call_evidence = fields.get("deferred_call_evidence")
    if not _deferred_call_evidence_is_specific(call_evidence):
        return False
    stage_evidence = fields.get("stage_evidence")
    if not isinstance(stage_evidence, tuple):
        return False
    matching = [
        item
        for item in stage_evidence
        if _deferred_call_stage_evidence_matches(
            item,
            stage=stage,
            target=target,
            call_evidence=call_evidence,
        )
    ]
    return len(matching) == 1


def _deferred_call_stage_evidence_matches(
    value: Any,
    *,
    stage: str,
    target: Any,
    call_evidence: Any,
) -> bool:
    evidence = _normalize_nested_tuple(value)
    if not isinstance(evidence, tuple) or evidence[0] != "unresolved_expression_stage_evidence":
        return False
    fields = _tuple_fields(evidence)
    if fields.get("proof_stage") != stage:
        return False
    if fields.get("status") != "object_evidence_collected":
        return False
    if _unresolved_expression_target_identity_key(fields.get("object_target_key")) != _unresolved_expression_target_identity_key(target):
        return False
    if _canonical_json(fields.get("deferred_call_evidence")) != _canonical_json(call_evidence):
        return False
    required = fields.get("required_semantic_proof")
    if not isinstance(required, tuple) or not required or not all(_text_identity_is_specific(item) for item in required):
        return False
    if stage == "deferred_call_return_resolution":
        if fields.get("call_resolution_status") != "pending_semantic_proof":
            return False
    elif stage == "deferred_call_result_equivalence":
        if fields.get("result_equivalence_status") != "pending_semantic_proof":
            return False
    else:
        return False
    return _semantic_recurrence_query_plan_is_specific(
        fields.get("proof_query_plan"),
        expected_stage=stage,
        stage_fields=fields,
    )


def _deferred_call_evidence_is_specific(value: Any) -> bool:
    evidence = _normalize_nested_tuple(value)
    if not isinstance(evidence, tuple) or len(evidence) != 8:
        return False
    if evidence[0] != "deferred_call_object_evidence":
        return False
    fields = _tuple_fields(evidence)
    left_refs = fields.get("left_deferred_call_refs")
    right_refs = fields.get("right_deferred_call_refs")
    left_semantic_refs = fields.get("left_deferred_call_semantic_refs")
    right_semantic_refs = fields.get("right_deferred_call_semantic_refs")
    relation = fields.get("deferred_call_ref_relation")
    semantic_relation = fields.get("deferred_call_semantic_ref_relation")
    if not isinstance(left_refs, tuple) or not isinstance(right_refs, tuple):
        return False
    if not isinstance(left_semantic_refs, tuple) or not isinstance(right_semantic_refs, tuple):
        return False
    if not left_refs and not right_refs:
        return False
    if not all(_deferred_call_runtime_ref_is_specific(ref) for ref in left_refs + right_refs):
        return False
    if not all(
        _deferred_call_semantic_ref_is_specific(ref)
        for ref in left_semantic_refs + right_semantic_refs
    ):
        return False
    if _deferred_call_semantic_refs_from_runtime_refs(left_refs) != left_semantic_refs:
        return False
    if _deferred_call_semantic_refs_from_runtime_refs(right_refs) != right_semantic_refs:
        return False
    if not _deferred_call_ref_relation_is_specific(
        relation,
        left_count=len(left_refs),
        right_count=len(right_refs),
    ):
        return False
    if not _deferred_call_ref_relation_is_specific(
        semantic_relation,
        left_count=len(left_semantic_refs),
        right_count=len(right_semantic_refs),
    ):
        return False
    return fields.get("evidence_status") == "object_evidence_collected"


def _deferred_call_runtime_ref_is_specific(value: Any) -> bool:
    ref = _normalize_nested_tuple(value)
    return (
        isinstance(ref, tuple)
        and len(ref) == 2
        and ref[0] in {"unknown_runtime_ref", "runtime_ref"}
        and isinstance(ref[1], tuple)
        and len(ref[1]) >= 2
        and ref[1][0] == "deferred_call"
        and _nested_has_specific_leaf(ref[1])
        and not _nested_contains_missing_sentinel(ref[1])
    )


def _deferred_call_semantic_ref_is_specific(value: Any) -> bool:
    ref = _normalize_nested_tuple(value)
    if not isinstance(ref, tuple) or len(ref) != 3 or ref[0] != "deferred_call_semantic_ref":
        return False
    fields = _tuple_fields(ref)
    payload = fields.get("deferred_call_payload")
    forms = fields.get("ref_forms")
    return (
        isinstance(payload, tuple)
        and len(payload) >= 2
        and payload[0] == "deferred_call"
        and _nested_has_specific_leaf(payload)
        and not _nested_contains_missing_sentinel(payload)
        and isinstance(forms, tuple)
        and bool(forms)
        and all(form in {"unknown_runtime_ref", "runtime_ref"} for form in forms)
    )


def _deferred_call_semantic_refs_from_runtime_refs(refs: Tuple[Any, ...]) -> Tuple[Any, ...]:
    grouped: Dict[str, Dict[str, Any]] = {}
    for ref in refs:
        normalized = _normalize_nested_tuple(ref)
        if (
            not isinstance(normalized, tuple)
            or len(normalized) != 2
            or normalized[0] not in {"unknown_runtime_ref", "runtime_ref"}
            or not isinstance(normalized[1], tuple)
            or not normalized[1]
            or normalized[1][0] != "deferred_call"
        ):
            continue
        payload = normalized[1]
        key = _canonical_json(_jsonable(payload))
        entry = grouped.setdefault(key, {"payload": payload, "forms": set()})
        entry["forms"].add(normalized[0])
    return tuple(
        (
            "deferred_call_semantic_ref",
            ("deferred_call_payload", grouped[key]["payload"]),
            ("ref_forms", tuple(sorted(grouped[key]["forms"]))),
        )
        for key in sorted(grouped)
    )


def _deferred_call_ref_relation_is_specific(
    value: Any,
    *,
    left_count: int,
    right_count: int,
) -> bool:
    relation = _normalize_nested_tuple(value)
    if not isinstance(relation, tuple) or relation[0] != "deferred_call_ref_relation":
        return False
    fields = _tuple_fields(relation)
    if fields.get("relation") not in {
        "both_sides_deferred_call_unknown",
        "left_deferred_call_unknown_only",
        "right_deferred_call_unknown_only",
    }:
        return False
    return fields.get("left_count") == left_count and fields.get("right_count") == right_count


def _unresolved_expression_opaque_unknown_pending_action_evidence_is_specific(
    action: Mapping[str, Any],
    *,
    stage: str,
    target: Any,
) -> bool:
    evidence = _normalize_nested_tuple(action.get("object_evidence"))
    if not isinstance(evidence, tuple) or len(evidence) != 9:
        return False
    if evidence[0] != "unresolved_expression_diagnostic_evidence":
        return False
    fields = _tuple_fields(evidence)
    if fields.get("object_derived") is not True:
        return False
    if fields.get("status") != "object_evidence_collected":
        return False
    if fields.get("diagnostic_rule") != "opaque_unknown_return_object_proof_content":
        return False
    evidence_target = fields.get("object_target_key")
    if not _object_target_key_is_specific_unresolved_expression(evidence_target):
        return False
    if _unresolved_expression_target_identity_key(evidence_target) != _unresolved_expression_target_identity_key(target):
        return False
    pending_stages = fields.get("pending_stages")
    if not isinstance(pending_stages, tuple) or stage not in pending_stages:
        return False
    if not set(pending_stages).issubset(set(UNRESOLVED_OPAQUE_VOID_PROOF_STAGES)):
        return False
    opaque_evidence = fields.get("opaque_unknown_evidence")
    if not _opaque_unknown_return_evidence_is_specific(opaque_evidence):
        return False
    stage_evidence = fields.get("stage_evidence")
    if not isinstance(stage_evidence, tuple):
        return False
    matching = [
        item
        for item in stage_evidence
        if _opaque_unknown_stage_evidence_matches(
            item,
            stage=stage,
            target=target,
            opaque_evidence=opaque_evidence,
        )
    ]
    return len(matching) == 1


def _opaque_unknown_stage_evidence_matches(
    value: Any,
    *,
    stage: str,
    target: Any,
    opaque_evidence: Any,
) -> bool:
    evidence = _normalize_nested_tuple(value)
    if not isinstance(evidence, tuple) or evidence[0] != "unresolved_expression_stage_evidence":
        return False
    fields = _tuple_fields(evidence)
    if fields.get("proof_stage") != stage:
        return False
    if fields.get("status") != "object_evidence_collected":
        return False
    if _unresolved_expression_target_identity_key(fields.get("object_target_key")) != _unresolved_expression_target_identity_key(target):
        return False
    if _canonical_json(fields.get("opaque_unknown_evidence")) != _canonical_json(opaque_evidence):
        return False
    required = fields.get("required_semantic_proof")
    if not isinstance(required, tuple) or not required or not all(_text_identity_is_specific(item) for item in required):
        return False
    if stage == "opaque_unknown_return_origin_resolution":
        if fields.get("origin_resolution_status") != "pending_semantic_proof":
            return False
    elif stage == "opaque_unknown_return_value_equivalence":
        if fields.get("value_equivalence_status") != "pending_semantic_proof":
            return False
    else:
        return False
    return _semantic_recurrence_query_plan_is_specific(
        fields.get("proof_query_plan"),
        expected_stage=stage,
        stage_fields=fields,
    )


def _opaque_unknown_return_evidence_is_specific(value: Any) -> bool:
    evidence = _normalize_nested_tuple(value)
    if not isinstance(evidence, tuple) or len(evidence) != 5:
        return False
    if evidence[0] != "opaque_unknown_return_object_evidence":
        return False
    fields = _tuple_fields(evidence)
    opaque_refs = fields.get("opaque_unknown_refs")
    return_sides = fields.get("return_sides")
    width_policy = fields.get("return_width_policy")
    if not isinstance(opaque_refs, tuple) or not opaque_refs:
        return False
    if not all(_opaque_unknown_ref_is_specific(ref) for ref in opaque_refs):
        return False
    if not isinstance(return_sides, tuple) or len(return_sides) != 2:
        return False
    if not all(_opaque_return_side_evidence_is_specific(side) for side in return_sides):
        return False
    if not isinstance(width_policy, tuple) or len(width_policy) != 2:
        return False
    if not all(_return_storage_policy_is_specific(item) for item in width_policy):
        return False
    return fields.get("evidence_status") == "object_evidence_collected"


def _opaque_return_side_evidence_is_specific(value: Any) -> bool:
    side = _normalize_nested_tuple(value)
    if not isinstance(side, tuple) or side[0] != "return_side":
        return False
    fields = _tuple_fields(side)
    if fields.get("side") not in {"left", "right"}:
        return False
    if not _nested_has_specific_leaf(fields.get("function_ref")):
        return False
    if not _return_storage_policy_is_specific(fields.get("return_storage")):
        return False
    if not _return_case_origin_is_specific(fields.get("return_case_origin")):
        return False
    unresolved_locations = fields.get("unresolved_locations")
    if not isinstance(unresolved_locations, tuple) or unresolved_locations[0] != "unresolved_locations":
        return False
    opaque_refs = fields.get("opaque_unknown_refs")
    if not isinstance(opaque_refs, tuple):
        return False
    return all(_opaque_unknown_ref_is_specific(ref) for ref in opaque_refs)


def _opaque_unknown_ref_is_specific(value: Any) -> bool:
    ref = _normalize_nested_tuple(value)
    return (
        isinstance(ref, tuple)
        and len(ref) == 2
        and ref[0] in {"runtime_ref", "unknown_runtime_ref"}
        and isinstance(ref[1], tuple)
        and len(ref[1]) >= 2
        and ref[1][0] == "opaque_unknown"
        and ref[1][1] == "void"
        and not _nested_contains_missing_sentinel(ref)
    )


def _return_storage_policy_is_specific(value: Any) -> bool:
    storage = _normalize_nested_tuple(value)
    return (
        isinstance(storage, tuple)
        and len(storage) >= 4
        and storage[0] == "return_storage"
        and storage[1] == "return_value"
        and _nonnegative_int_like(storage[2])
    )


def _return_case_origin_is_specific(value: Any) -> bool:
    origin = _normalize_nested_tuple(value)
    if not isinstance(origin, tuple) or len(origin) < 6:
        return False
    if origin[0] != "return_case_partition_member":
        return False
    if not _nonnegative_int_like(origin[1]):
        return False
    if not isinstance(origin[2], tuple):
        return False
    return _nested_has_specific_leaf(origin[3]) and not _nested_contains_missing_sentinel(origin[3])


def _unresolved_expression_pending_action_evidence_is_specific(
    action: Mapping[str, Any],
    *,
    stage: str,
    target: Any,
) -> bool:
    evidence = _normalize_nested_tuple(action.get("object_evidence"))
    if not isinstance(evidence, tuple) or len(evidence) != 9:
        return False
    if evidence[0] != "unresolved_expression_diagnostic_evidence":
        return False
    fields = _tuple_fields(evidence)
    if fields.get("object_derived") is not True:
        return False
    if fields.get("status") != "object_evidence_collected":
        return False
    if fields.get("diagnostic_rule") != "phi_circular_full_shape_match":
        return False
    evidence_target = fields.get("object_target_key")
    if not _object_target_key_is_specific_unresolved_expression(evidence_target):
        return False
    if _unresolved_expression_target_identity_key(evidence_target) != _unresolved_expression_target_identity_key(target):
        return False
    diagnostic = fields.get("pair_lowering_diagnostic")
    if not _pair_lowering_diagnostic_is_specific(diagnostic):
        return False
    pending_stages = fields.get("pending_stages")
    if not isinstance(pending_stages, tuple) or stage not in pending_stages:
        return False
    stage_evidence = fields.get("stage_evidence")
    if not isinstance(stage_evidence, tuple):
        return False
    matching = [
        item
        for item in stage_evidence
        if _pending_stage_evidence_matches(
            item,
            stage=stage,
            target=target,
            diagnostic=diagnostic,
        )
    ]
    return len(matching) == 1


def _pending_stage_evidence_matches(
    value: Any,
    *,
    stage: str,
    target: Any,
    diagnostic: Any,
    completed_recovery: bool = False,
) -> bool:
    evidence = _normalize_nested_tuple(value)
    if not isinstance(evidence, tuple) or evidence[0] != "unresolved_expression_stage_evidence":
        return False
    fields = _tuple_fields(evidence)
    if fields.get("proof_stage") != stage:
        return False
    if fields.get("status") != "object_evidence_collected":
        return False
    evidence_target = fields.get("object_target_key")
    identity_key = (
        _unresolved_expression_completed_recovery_target_identity_key
        if completed_recovery
        else _unresolved_expression_target_identity_key
    )
    if identity_key(evidence_target) != identity_key(target):
        return False
    if _canonical_json(fields.get("pair_lowering_diagnostic")) != _canonical_json(diagnostic):
        return False
    if not _phi_origin_pair_is_specific(fields.get("phi_origin_pair")):
        return False
    if not _guard_condition_pair_is_specific(fields.get("guard_condition_pair")):
        return False
    required = fields.get("required_semantic_proof")
    if not isinstance(required, tuple) or not required or not all(_text_identity_is_specific(item) for item in required):
        return False
    if not _semantic_recurrence_query_plan_is_specific(
        fields.get("proof_query_plan"),
        expected_stage=stage,
        stage_fields=fields,
    ):
        return False
    if stage == "phi_circular_guard_condition_lowering":
        return (
            fields.get("typed_lowering_rule") == "phi_circular_guard_shape_preserving"
            and _guard_transition_relation_is_specific(
                fields.get("guard_transition_relation")
            )
        )
    if stage == "recursive_summary_guard_equivalence":
        return (
            _summary_parameter_binding_is_specific(fields.get("summary_parameter_binding"))
            and _recurrence_relation_is_specific(fields.get("recurrence_relation"))
        )
    return False


def _semantic_recurrence_proof_is_specific(
    value: Any,
    *,
    stage: str,
    target: Any,
    diagnostic: Any,
    stage_evidence: Any,
    completed_recovery: bool = False,
) -> bool:
    proof = _normalize_nested_tuple(value)
    if not isinstance(proof, tuple) or proof[0] != "semantic_recurrence_proof":
        return False
    fields = _tuple_fields(proof)
    if fields.get("proof_rule") != "phi_circular_independent_semantic_recurrence_proof":
        return False
    if fields.get("status") != "complete":
        return False
    completed_stages = fields.get("completed_stages")
    if not isinstance(completed_stages, tuple) or stage not in completed_stages:
        return False
    completed_stage_set = {str(item) for item in completed_stages}
    if not completed_stage_set or not completed_stage_set.issubset(
        set(UNRESOLVED_PHI_CIRCULAR_PROOF_STAGES)
    ):
        return False
    solver_hashes_by_stage = _semantic_recurrence_solver_hashes_by_stage(
        fields.get("solver_query_sha256_by_stage")
    )
    if set(solver_hashes_by_stage) != completed_stage_set:
        return False
    evidence_target = fields.get("object_target_key")
    identity_key = (
        _unresolved_expression_completed_recovery_target_identity_key
        if completed_recovery
        else _unresolved_expression_target_identity_key
    )
    if identity_key(evidence_target) != identity_key(target):
        return False
    if _canonical_json(fields.get("pair_lowering_diagnostic")) != _canonical_json(diagnostic):
        return False
    proof_queries = fields.get("proof_queries")
    if not isinstance(proof_queries, tuple) or not proof_queries:
        return False
    planned_queries = _semantic_recurrence_query_plan_fields_by_stage(stage_evidence)
    if not planned_queries:
        return False
    stages = set()
    for query in proof_queries:
        query_fields = _semantic_recurrence_query_fields(query)
        if not query_fields:
            return False
        query_stage = query_fields.get("query_stage")
        if query_stage not in UNRESOLVED_PHI_CIRCULAR_PROOF_STAGES:
            return False
        planned_fields = planned_queries.get(str(query_stage))
        if not planned_fields:
            return False
        if query_fields.get("query_id") != planned_fields.get("query_id"):
            return False
        if query_fields.get("assertion_kind") != planned_fields.get("assertion_kind"):
            return False
        if query_fields.get("expected_solver_result") != planned_fields.get("expected_solver_result"):
            return False
        if query_fields.get("query_hash") != planned_fields.get("query_hash"):
            return False
        if query_fields.get("object_content") != planned_fields.get("object_content"):
            return False
        if (
            query_fields.get("proof_source")
            != UNRESOLVED_INDEPENDENT_SEMANTIC_RECURRENCE_PROOF_SOURCE
        ):
            return False
        if query_fields.get("solver_query_sha256") != solver_hashes_by_stage.get(str(query_stage)):
            return False
        if query_fields.get("solver_result") != "unsat":
            return False
        if query_fields.get("query_status") != "proven":
            return False
        if not _semantic_recurrence_query_has_object_content(query_fields):
            return False
        stages.add(str(query_stage))
    return set(completed_stages).issubset(stages)


def _semantic_recurrence_solver_hashes_by_stage(value: Any) -> Dict[str, str]:
    hashes = _normalize_nested_tuple(value)
    if isinstance(hashes, Mapping):
        items = tuple(hashes.items())
    elif isinstance(hashes, tuple):
        items = hashes
    else:
        return {}
    result: Dict[str, str] = {}
    for item in items:
        if not isinstance(item, tuple) or len(item) != 2:
            return {}
        stage, digest = item
        if stage not in UNRESOLVED_PHI_CIRCULAR_PROOF_STAGES:
            return {}
        if not _sha256_hex_is_specific(digest):
            return {}
        stage = str(stage)
        if stage in result:
            return {}
        result[stage] = str(digest)
    return result


def _semantic_recurrence_query_plan_fields_by_stage(value: Any) -> Dict[str, Dict[str, Any]]:
    stage_evidence = _normalize_nested_tuple(value)
    if not isinstance(stage_evidence, tuple):
        return {}
    result: Dict[str, Dict[str, Any]] = {}
    for stage_item in stage_evidence:
        stage_tuple = _normalize_nested_tuple(stage_item)
        if not isinstance(stage_tuple, tuple) or stage_tuple[0] != "unresolved_expression_stage_evidence":
            continue
        stage_fields = _tuple_fields(stage_tuple)
        stage = stage_fields.get("proof_stage")
        if stage not in UNRESOLVED_PHI_CIRCULAR_PROOF_STAGES:
            continue
        plan = stage_fields.get("proof_query_plan")
        queries = _semantic_recurrence_query_plan_queries(plan)
        if len(queries) != 1:
            continue
        fields = _tuple_fields(queries[0])
        if not _semantic_recurrence_query_plan_fields_are_specific(
            fields,
            expected_stage=str(stage),
            stage_fields=stage_fields,
        ):
            continue
        result[str(stage)] = fields
    return result


def _semantic_recurrence_query_fields(value: Any) -> Dict[str, Any]:
    query = _normalize_nested_tuple(value)
    if not isinstance(query, tuple) or query[0] != "semantic_recurrence_query":
        return {}
    fields = _tuple_fields(query)
    for key in (
        "query_stage",
        "solver_result",
        "query_status",
        "query_id",
        "proof_source",
        "expected_solver_result",
        "assertion_kind",
        "query_hash",
        "solver_query_sha256",
    ):
        if not _text_identity_is_specific(fields.get(key)):
            return {}
    if not _sha256_hex_is_specific(fields.get("solver_query_sha256")):
        return {}
    return fields


def _semantic_recurrence_query_plan_queries(value: Any) -> Tuple[Any, ...]:
    plan = _normalize_nested_tuple(value)
    if not isinstance(plan, tuple):
        return ()
    if len(plan) == 2 and plan[0] == "proof_query_plan":
        queries = plan[1]
    else:
        queries = plan
    return queries if isinstance(queries, tuple) else ()


def _semantic_recurrence_query_plan_is_specific(
    value: Any,
    *,
    expected_stage: str,
    stage_fields: Mapping[str, Any],
) -> bool:
    queries = _semantic_recurrence_query_plan_queries(value)
    if not queries:
        return False
    for query in queries:
        query_tuple = _normalize_nested_tuple(query)
        if not isinstance(query_tuple, tuple) or query_tuple[0] != "semantic_recurrence_query":
            return False
        fields = _tuple_fields(query_tuple)
        if not _semantic_recurrence_query_plan_fields_are_specific(
            fields,
            expected_stage=expected_stage,
            stage_fields=stage_fields,
        ):
            return False
    return True


def _semantic_recurrence_query_plan_fields_are_specific(
    fields: Mapping[str, Any],
    *,
    expected_stage: str,
    stage_fields: Mapping[str, Any],
) -> bool:
    if not _text_identity_is_specific(fields.get("query_id")):
        return False
    if fields.get("query_stage") != expected_stage:
        return False
    if fields.get("query_status") != "planned":
        return False
    if fields.get("expected_solver_result") != "unsat":
        return False
    if fields.get("proof_source") != "object_derived_query_plan":
        return False
    if not _text_identity_is_specific(fields.get("assertion_kind")):
        return False
    if not _sha256_hex_is_specific(fields.get("query_hash")):
        return False
    if not _semantic_recurrence_query_has_object_content(
        fields,
        stage_fields=stage_fields,
    ):
        return False
    return True


def _semantic_recurrence_query_has_object_content(
    fields: Mapping[str, Any],
    *,
    stage_fields: Optional[Mapping[str, Any]] = None,
) -> bool:
    stage = fields.get("query_stage")
    object_content = fields.get("object_content")
    if not isinstance(object_content, tuple) or not object_content:
        return False
    if stage == "phi_circular_guard_condition_lowering":
        relation = fields.get("guard_transition_relation")
        if not _guard_transition_relation_is_specific(relation):
            return False
        if object_content != (("guard_transition_relation", relation),):
            return False
        if stage_fields is not None and _canonical_json(relation) != _canonical_json(
            stage_fields.get("guard_transition_relation")
        ):
            return False
        return True
    if stage == "recursive_summary_guard_equivalence":
        binding = fields.get("summary_parameter_binding")
        relation = fields.get("recurrence_relation")
        if not _summary_parameter_binding_is_specific(binding):
            return False
        if not _recurrence_relation_is_specific(relation):
            return False
        if object_content != (
            ("summary_parameter_binding", binding),
            ("recurrence_relation", relation),
        ):
            return False
        if stage_fields is not None:
            if _canonical_json(binding) != _canonical_json(
                stage_fields.get("summary_parameter_binding")
            ):
                return False
            if _canonical_json(relation) != _canonical_json(
                stage_fields.get("recurrence_relation")
            ):
                return False
        return True
    if stage in UNRESOLVED_DEFERRED_CALL_PROOF_STAGES:
        call_evidence = fields.get("deferred_call_evidence")
        if not _deferred_call_evidence_is_specific(call_evidence):
            return False
        if object_content != (("deferred_call_evidence", call_evidence),):
            return False
        if stage_fields is not None and _canonical_json(call_evidence) != _canonical_json(
            stage_fields.get("deferred_call_evidence")
        ):
            return False
        return True
    if stage in UNRESOLVED_OPAQUE_VOID_PROOF_STAGES:
        opaque_evidence = fields.get("opaque_unknown_evidence")
        if not _opaque_unknown_return_evidence_is_specific(opaque_evidence):
            return False
        if object_content != (("opaque_unknown_evidence", opaque_evidence),):
            return False
        if stage_fields is not None and _canonical_json(opaque_evidence) != _canonical_json(
            stage_fields.get("opaque_unknown_evidence")
        ):
            return False
        return True
    return False


def _sha256_hex_is_specific(value: Any) -> bool:
    if not isinstance(value, str) or len(value) != 64:
        return False
    return all(ch in "0123456789abcdef" for ch in value)


def _phi_origin_pair_is_specific(value: Any) -> bool:
    pair = _normalize_nested_tuple(value)
    if not isinstance(pair, tuple) or pair[0] != "phi_origin_pair":
        return False
    fields = _tuple_fields(pair)
    return (
        fields.get("relation") == "exact_match"
        and _phi_origin_shape_relation_is_specific(fields.get("phi_origin_shape_relation"))
        and _relation_value(fields.get("phi_origin_shape_relation")) == "exact_match"
    )


def _guard_condition_pair_is_specific(value: Any) -> bool:
    pair = _normalize_nested_tuple(value)
    if not isinstance(pair, tuple) or pair[0] != "guard_condition_pair":
        return False
    fields = _tuple_fields(pair)
    left = fields.get("left_guard_literals")
    right = fields.get("right_guard_literals")
    return (
        fields.get("relation") == "exact_match"
        and isinstance(left, tuple)
        and isinstance(right, tuple)
        and left == right
        and all(_guard_literal_is_specific(item) for item in left)
    )


def _summary_parameter_binding_is_specific(value: Any) -> bool:
    binding = _normalize_nested_tuple(value)
    if not isinstance(binding, tuple) or binding[0] != "summary_parameter_binding":
        return False
    fields = _tuple_fields(binding)
    return (
        fields.get("binding_status") == "object_evidence_collected"
        and fields.get("left_value_shape") == fields.get("right_value_shape")
        and _expression_shape_is_specific(fields.get("left_value_shape"))
        and _value_shape_relation_is_specific(fields.get("value_shape_relation"))
        and _relation_value(fields.get("value_shape_relation")) == "exact_match"
    )


def _guard_transition_relation_is_specific(value: Any) -> bool:
    relation = _normalize_nested_tuple(value)
    if not isinstance(relation, tuple) or relation[0] != "guard_transition_relation":
        return False
    fields = _tuple_fields(relation)
    return (
        fields.get("relation") == "exact_match"
        and fields.get("transition_status") == "object_evidence_collected"
        and _phi_origin_pair_is_specific(fields.get("phi_origin_pair"))
        and _guard_condition_pair_is_specific(fields.get("guard_condition_pair"))
        and fields.get("left_value_shape") == fields.get("right_value_shape")
        and _expression_shape_is_specific(fields.get("left_value_shape"))
        and _value_shape_relation_is_specific(fields.get("value_shape_relation"))
        and _relation_value(fields.get("value_shape_relation")) == "exact_match"
    )


def _recurrence_relation_is_specific(value: Any) -> bool:
    relation = _normalize_nested_tuple(value)
    if not isinstance(relation, tuple) or relation[0] != "recurrence_relation":
        return False
    fields = _tuple_fields(relation)
    return (
        fields.get("relation") == "exact_match"
        and fields.get("recurrence_status") == "object_evidence_collected"
        and _summary_parameter_binding_is_specific(fields.get("summary_parameter_binding"))
        and _guard_transition_relation_is_specific(fields.get("guard_transition_relation"))
        and fields.get("left_value_shape") == fields.get("right_value_shape")
        and _expression_shape_is_specific(fields.get("left_value_shape"))
        and _value_shape_relation_is_specific(fields.get("value_shape_relation"))
        and _relation_value(fields.get("value_shape_relation")) == "exact_match"
    )


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
        if (
            action.get("proof_stage") in UNRESOLVED_PHI_CIRCULAR_PROOF_STAGES
            and not _target_has_specific_phi_circular_relation_evidence(target)
        ):
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
    if not isinstance(target, tuple) or len(target) not in {4, 5} or target[0] != "unresolved_expression":
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
    if len(target) == 5 and not _pair_lowering_diagnostic_is_specific(target[4]):
        return False
    return left_ok and right_ok and (
        _side_has_unresolved_locations(target[2])
        or _side_has_unresolved_locations(target[3])
    )


def _pair_lowering_diagnostic_is_specific(value: Any) -> bool:
    diagnostic = _normalize_nested_tuple(value)
    if not isinstance(diagnostic, tuple) or len(diagnostic) not in {11, 13, 14}:
        return False
    if diagnostic[0] != "pair_lowering_diagnostic":
        return False
    fields = {
        item[0]: item[1]
        for item in diagnostic[1:]
        if isinstance(item, tuple) and len(item) == 2 and isinstance(item[0], str)
    }
    if fields.get("candidate_kind") != "phi_circular_guard_summary_relation":
        return False
    if fields.get("status") not in {
        "full_shape_match",
        "value_shape_mismatch",
        "guard_literal_conflict",
        "shape_unavailable",
        "condition_shape_mismatch",
    }:
        return False
    if not _nonnegative_int_like(fields.get("left_unknown_count")):
        return False
    if not _nonnegative_int_like(fields.get("right_unknown_count")):
        return False
    if "unknown_count_relation" in fields and not _unknown_count_relation_is_specific(
        fields.get("unknown_count_relation"),
        fields.get("left_unknown_count"),
        fields.get("right_unknown_count"),
    ):
        return False
    for key in ("left_value_shape", "right_value_shape"):
        if fields.get(key) is not None and not _expression_shape_is_specific(fields.get(key)):
            return False
    if "value_shape_relation" in fields and not _value_shape_relation_is_specific(
        fields.get("value_shape_relation"),
    ):
        return False
    if "phi_origin_shape_relation" in fields and not _phi_origin_shape_relation_is_specific(
        fields.get("phi_origin_shape_relation"),
    ):
        return False
    for key in ("left_guard_literals", "right_guard_literals"):
        literals = fields.get(key)
        if not isinstance(literals, tuple):
            return False
        if not all(_guard_literal_is_specific(item) for item in literals):
            return False
    opposing = fields.get("opposing_guard_literals")
    if not isinstance(opposing, tuple):
        return False
    if not all(_opposing_guard_literal_is_specific(item) for item in opposing):
        return False
    return fields.get("required_evidence") == (
        "guard_condition_pair",
        "summary_parameter_binding",
    )


def _phi_origin_shape_relation_is_specific(value: Any) -> bool:
    relation = _normalize_nested_tuple(value)
    if not isinstance(relation, tuple) or len(relation) != 4:
        return False
    if relation[0] != "phi_origin_shape_relation":
        return False
    fields = {
        item[0]: item[1]
        for item in relation[1:]
        if isinstance(item, tuple) and len(item) == 2 and isinstance(item[0], str)
    }
    if fields.get("relation") not in {
        "exact_match",
        "origin_shape_mismatch",
        "origin_shape_unavailable",
    }:
        return False
    for key in ("left_origin_shapes", "right_origin_shapes"):
        shapes = fields.get(key)
        if not isinstance(shapes, tuple):
            return False
        if not all(
            shape is None or _phi_origin_shape_is_specific(shape)
            for shape in shapes
        ):
            return False
    return True


def _phi_origin_shape_is_specific(value: Any) -> bool:
    shape = _normalize_nested_tuple(value)
    if not isinstance(shape, tuple) or len(shape) < 2:
        return False
    if shape[0] != "pcode_op_cross_binary_shape":
        return False
    fields = {
        item[0]: item[1]
        for item in shape[1:]
        if isinstance(item, tuple) and len(item) == 2 and isinstance(item[0], str)
    }
    if "relative_target_offset" in fields:
        for key in ("relative_target_offset", "seq_time", "seq_order", "local_op_ordinal"):
            if not _nonnegative_int_like(fields.get(key)):
                return False
        return _text_identity_is_specific(fields.get("target_space")) and fields.get("opcode") is not None
    if "address_offset" in fields:
        for key in ("address_offset", "seq_time", "seq_order", "block_index"):
            if fields.get(key) is not None and not _nonnegative_int_like(fields.get(key)):
                return False
        return _text_identity_is_specific(fields.get("mnemonic"))
    return False


def _unknown_count_relation_is_specific(
    value: Any,
    left_count: Any,
    right_count: Any,
) -> bool:
    relation = _normalize_nested_tuple(value)
    if not isinstance(relation, tuple) or len(relation) != 4:
        return False
    if relation[0] != "unknown_count_relation":
        return False
    fields = {
        item[0]: item[1]
        for item in relation[1:]
        if isinstance(item, tuple) and len(item) == 2 and isinstance(item[0], str)
    }
    if fields.get("relation") not in {"equal", "count_mismatch"}:
        return False
    if not _nonnegative_int_like(fields.get("left_count")):
        return False
    if not _nonnegative_int_like(fields.get("right_count")):
        return False
    if int(fields["left_count"]) != int(left_count) or int(fields["right_count"]) != int(right_count):
        return False
    expected = "equal" if int(left_count) == int(right_count) else "count_mismatch"
    return fields.get("relation") == expected


def _value_shape_relation_is_specific(value: Any) -> bool:
    relation = _normalize_nested_tuple(value)
    if not isinstance(relation, tuple) or len(relation) != 8:
        return False
    if relation[0] != "value_shape_relation":
        return False
    fields = {
        item[0]: item[1]
        for item in relation[1:]
        if isinstance(item, tuple) and len(item) == 2 and isinstance(item[0], str)
    }
    if fields.get("relation") not in {
        "exact_match",
        "summary_parameter_shift",
        "left_summary_parameter_right_constant",
        "left_constant_right_summary_parameter",
        "shape_mismatch",
        "shape_unavailable",
    }:
        return False
    for key in ("left_kind", "right_kind"):
        if fields.get(key) not in {"parameter", "const", "unknown", "unary", "binary", "intrinsic", "literal", "unavailable"}:
            return False
    for key in ("left_summary_parameter_index", "right_summary_parameter_index"):
        value = fields.get(key)
        if value is not None and not _nonnegative_int_like(value):
            return False
    for key in ("left_constant_value", "right_constant_value"):
        value = fields.get(key)
        if value is not None and not isinstance(value, int):
            return False
    return True


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
    if not isinstance(evidence, tuple) or len(evidence) not in {7, 8}:
        return False
    if evidence[0] != "typed_lowering_evidence":
        return False
    scope = evidence[1]
    expression_kind = evidence[2]
    expression_bits = evidence[3]
    typed_expression_key = evidence[4]
    unsupported = evidence[5]
    lowering_status = evidence[6]
    base_ok = (
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
    if not base_ok:
        return False
    if len(evidence) == 7:
        return True
    return _phi_circular_evidence_is_specific(evidence[7], expected_scope)


def _phi_circular_evidence_is_specific(value: Any, expected_scope: str) -> bool:
    evidence = _normalize_nested_tuple(value)
    if not isinstance(evidence, tuple) or len(evidence) not in {6, 7}:
        return False
    if evidence[0] != "phi_circular_evidence":
        return False
    scope = evidence[1]
    origins = evidence[2]
    guard_condition_key = evidence[3]
    if len(evidence) == 7:
        guard_condition_literals = evidence[4]
        summary_parameter_refs = evidence[5]
        relation_status = evidence[6]
    else:
        guard_condition_literals = None
        summary_parameter_refs = evidence[4]
        relation_status = evidence[5]
    if scope != ("location_scope", expected_scope):
        return False
    if (
        not isinstance(origins, tuple)
        or len(origins) != 2
        or origins[0] != "phi_origins"
        or not isinstance(origins[1], tuple)
        or not origins[1]
        or not all(_phi_circular_origin_detail_is_specific(origin) for origin in origins[1])
    ):
        return False
    if (
        not isinstance(guard_condition_key, tuple)
        or len(guard_condition_key) != 2
        or guard_condition_key[0] != "guard_condition_key"
    ):
        return False
    guard_key = guard_condition_key[1]
    if expected_scope == "guard_condition":
        if not _return_guard_like_key_is_specific(guard_key):
            return False
    elif guard_key is not None and not _return_guard_like_key_is_specific(guard_key):
        return False
    if guard_condition_literals is not None:
        if (
            not isinstance(guard_condition_literals, tuple)
            or len(guard_condition_literals) != 2
            or guard_condition_literals[0] != "guard_condition_literals"
            or not isinstance(guard_condition_literals[1], tuple)
            or not all(_guard_literal_is_specific(item) for item in guard_condition_literals[1])
        ):
            return False
    if (
        not isinstance(summary_parameter_refs, tuple)
        or len(summary_parameter_refs) != 2
        or summary_parameter_refs[0] != "summary_parameter_refs"
        or not isinstance(summary_parameter_refs[1], tuple)
    ):
        return False
    refs = summary_parameter_refs[1]
    if not all(_summary_parameter_ref_is_specific(ref) for ref in refs):
        return False
    return relation_status == ("relation_status", "pending_guard_summary_relation_proof")


def _guard_literal_is_specific(value: Any) -> bool:
    literal = _normalize_nested_tuple(value)
    return (
        isinstance(literal, tuple)
        and len(literal) == 3
        and literal[0] == "guard_literal"
        and isinstance(literal[1], bool)
        and _expression_shape_is_specific(literal[2])
    )


def _opposing_guard_literal_is_specific(value: Any) -> bool:
    literal = _normalize_nested_tuple(value)
    return (
        isinstance(literal, tuple)
        and len(literal) == 2
        and literal[0] == "opposing_guard_literal"
        and _expression_shape_is_specific(literal[1])
    )


def _expression_shape_is_specific(value: Any) -> bool:
    shape = _normalize_nested_tuple(value)
    if not isinstance(shape, tuple) or not shape:
        return False
    tag = shape[0]
    if tag == "const":
        return len(shape) == 3 and isinstance(shape[1], int) and _positive_int_like(shape[2])
    if tag == "literal":
        return len(shape) == 3 and _text_identity_is_specific(shape[1]) and _positive_int_like(shape[2])
    if tag == "parameter":
        return (
            len(shape) == 4
            and _text_identity_is_specific(shape[1])
            and _nonnegative_int_like(shape[2])
            and _positive_int_like(shape[3])
        )
    if tag == "unknown":
        return len(shape) == 3 and shape[1] == "phi_circular" and _positive_int_like(shape[2])
    if tag == "unary":
        return (
            len(shape) == 4
            and _text_identity_is_specific(shape[1])
            and _positive_int_like(shape[2])
            and _expression_shape_is_specific(shape[3])
        )
    if tag == "binary":
        return (
            len(shape) == 5
            and _text_identity_is_specific(shape[1])
            and _positive_int_like(shape[2])
            and _expression_shape_is_specific(shape[3])
            and _expression_shape_is_specific(shape[4])
        )
    if tag == "intrinsic":
        return (
            len(shape) == 5
            and _text_identity_is_specific(shape[1])
            and (shape[2] is None or _nonnegative_int_like(shape[2]))
            and _positive_int_like(shape[3])
            and isinstance(shape[4], tuple)
            and all(_expression_shape_is_specific(item) for item in shape[4])
        )
    return False


def _positive_int_like(value: Any) -> bool:
    return _nonnegative_int_like(value) and int(value) > 0


def _phi_circular_origin_detail_is_specific(value: Any) -> bool:
    detail = _normalize_nested_tuple(value)
    if not isinstance(detail, tuple) or len(detail) != 6:
        return False
    if detail[0] != "phi_origin":
        return False
    runtime_ref = detail[1]
    origin_kind = detail[2]
    pcode_op_ref = detail[3]
    unknown_expression = detail[4]
    bit_width = detail[5]
    return (
        isinstance(runtime_ref, tuple)
        and len(runtime_ref) == 2
        and runtime_ref[0] == "runtime_ref"
        and _nested_has_specific_leaf(runtime_ref[1])
        and not _nested_contains_missing_sentinel(runtime_ref[1])
        and origin_kind == ("origin_kind", "multiequal_pcode_op")
        and isinstance(pcode_op_ref, tuple)
        and len(pcode_op_ref) == 2
        and pcode_op_ref[0] == "pcode_op_ref"
        and _pcode_ref_is_specific(pcode_op_ref[1])
        and isinstance(unknown_expression, tuple)
        and len(unknown_expression) == 2
        and unknown_expression[0] == "unknown_expression"
        and _nested_has_specific_leaf(unknown_expression[1])
        and not _nested_contains_missing_sentinel(unknown_expression[1])
        and isinstance(bit_width, tuple)
        and len(bit_width) == 2
        and bit_width[0] == "bit_width"
        and _nonnegative_int_like(bit_width[1])
        and int(bit_width[1]) > 0
    )


def _summary_parameter_ref_is_specific(value: Any) -> bool:
    ref = _normalize_nested_tuple(value)
    if not isinstance(ref, tuple) or len(ref) != 5:
        return False
    if ref[0] != "summary_parameter":
        return False
    index = ref[1]
    name = ref[2]
    bit_width = ref[3]
    expression = ref[4]
    if (
        not isinstance(index, tuple)
        or len(index) != 2
        or index[0] != "index"
        or not _nonnegative_int_like(index[1])
    ):
        return False
    if (
        not isinstance(name, tuple)
        or len(name) != 2
        or name[0] != "name"
        or (name[1] is not None and not _text_identity_is_specific(name[1]))
    ):
        return False
    if not (int(index[1]) >= 10000 or str(name[1] or "").startswith("summary_rec_")):
        return False
    return (
        isinstance(bit_width, tuple)
        and len(bit_width) == 2
        and bit_width[0] == "bit_width"
        and _nonnegative_int_like(bit_width[1])
        and int(bit_width[1]) > 0
        and isinstance(expression, tuple)
        and len(expression) == 2
        and expression[0] == "expression"
        and _expression_provenance_is_specific(expression[1])
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
    if root == "runtime_ref":
        return _runtime_ref_provenance_is_specific(node[1])
    if _nested_contains_missing(node):
        return False
    if root == "storage":
        return _nested_has_specific_leaf(node[1]) and not _nested_contains_missing(node[1])
    if root == "expression_digest":
        return len(node) >= 5 and _text_identity_is_specific(node[1]) and _nested_has_specific_leaf(node[4])
    return False


def _runtime_ref_provenance_is_specific(value: Any) -> bool:
    runtime_key = _normalize_nested_tuple(value)
    if (
        isinstance(runtime_key, tuple)
        and len(runtime_key) >= 4
        and runtime_key[0] == "opaque_unknown"
        and runtime_key[1] == "void"
        and runtime_key[2] is None
        and runtime_key[3] is None
    ):
        return True
    return _nested_has_specific_leaf(runtime_key) and not _nested_contains_missing(runtime_key)


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
    parser.add_argument("--gate-stage", choices=("pre-fix", "post-fix", "timeout-transition-audit"), default="pre-fix")
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
    elif args.gate_stage == "timeout-transition-audit":
        path = build_phase3_unresolved_expression_timeout_transition_audit(
            baseline_raw_dir=args.baseline_raw_dir,
            output_dir=args.output_dir,
            current_log_roots=current_roots,
            baseline_log_roots=baseline_roots,
        )
        if args.require_ready:
            validate_phase3_unresolved_expression_timeout_transition_audit(_read_json(path))
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
