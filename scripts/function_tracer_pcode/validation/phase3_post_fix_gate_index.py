# -*- coding: utf-8 -*-
"""Build a fixed index over Phase 3 post-fix gate artifacts."""

from __future__ import annotations

import argparse
import json
from dataclasses import dataclass
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Callable, Dict, Mapping, Optional, Sequence

from .phase3_lane_index import (
    BASELINE_GIT_HEAD,
    BASELINE_ID,
    MANIFEST_VERSION,
    MISSING_SENTINEL,
    _failed,
    _failed_check_kinds,
    _file_ref,
    _ok,
    _read_json,
    _summary,
    _write_json,
)
from .phase3_method_b_closure_lane4 import (
    validate_phase3_method_b_closure_lane4_post_fix_gate,
)
from .phase3_readonly_identity_lane3 import (
    validate_phase3_readonly_identity_lane3_post_fix_gate,
)
from .phase3_return_coverage_lane1 import (
    validate_phase3_return_coverage_lane1_post_fix_gate,
)
from .phase3_return_width_bridge_lane2 import (
    validate_phase3_return_width_bridge_lane2_post_fix_gate,
)
from .phase3_sat_unsafety_lane5 import validate_phase3_sat_unsafety_lane5_post_fix_gate
from .phase3_solver_rewrite_lane7 import (
    validate_phase3_solver_rewrite_lane7_post_fix_gate,
)
from .phase3_solver_rewrite_proof_lane8 import (
    validate_phase3_solver_rewrite_proof_lane8_post_fix_gate,
)
from .phase3_solver_timeout_lane9 import (
    validate_phase3_solver_timeout_lane9_post_fix_gate,
)
from .phase3_unresolved_expression_lane6 import (
    validate_phase3_unresolved_expression_lane6_post_fix_gate,
)


PostFixGateValidator = Callable[[Mapping[str, Any]], None]


@dataclass(frozen=True)
class Phase3PostFixGateSpec:
    lane_number: int
    lane_id: str
    gate_relpath: str
    manifest_kind: str
    ready_key: str
    validator: PostFixGateValidator
    expected_entry_count: Optional[int] = None
    allowed_post_fix_statuses: Sequence[str] = ()
    expected_post_fix_status_counts: Optional[Mapping[str, int]] = None


DEFAULT_PHASE3_POST_FIX_GATE_SPECS: Sequence[Phase3PostFixGateSpec] = (
    Phase3PostFixGateSpec(
        lane_number=1,
        lane_id="phase3_return_coverage_lane1",
        gate_relpath=(
            "logs/equivalence_all/function_call_test_phase3_return_coverage_lane1_representatives/"
            "phase3_return_coverage_lane1_gate/return_coverage_lane1_post_fix_gate.json"
        ),
        manifest_kind="phase3_return_coverage_lane1_post_fix_gate",
        ready_key="phase3_lane1_post_fix_ready",
        validator=validate_phase3_return_coverage_lane1_post_fix_gate,
        expected_entry_count=2,
        allowed_post_fix_statuses=("completed_recovery", "pending_proof"),
        expected_post_fix_status_counts={"completed_recovery": 1, "pending_proof": 1},
    ),
    Phase3PostFixGateSpec(
        lane_number=2,
        lane_id="phase3_return_width_bridge_lane2",
        gate_relpath=(
            "logs/equivalence_all/function_call_test_phase3_return_width_bridge_lane2_representatives/"
            "phase3_return_width_bridge_lane2_gate/return_width_bridge_lane2_post_fix_gate.json"
        ),
        manifest_kind="phase3_return_width_bridge_lane2_post_fix_gate",
        ready_key="phase3_lane2_post_fix_ready",
        validator=validate_phase3_return_width_bridge_lane2_post_fix_gate,
        expected_entry_count=1,
        allowed_post_fix_statuses=("completed_recovery", "pending_proof"),
        expected_post_fix_status_counts={"pending_proof": 1},
    ),
    Phase3PostFixGateSpec(
        lane_number=3,
        lane_id="phase3_readonly_identity_lane3",
        gate_relpath=(
            "logs/equivalence_all/loop_test_phase3_readonly_identity_lane3_representatives/"
            "phase3_readonly_identity_lane3_gate/readonly_identity_lane3_post_fix_gate.json"
        ),
        manifest_kind="phase3_readonly_identity_lane3_post_fix_gate",
        ready_key="phase3_lane3_post_fix_ready",
        validator=validate_phase3_readonly_identity_lane3_post_fix_gate,
        expected_entry_count=1,
        allowed_post_fix_statuses=("completed_recovery", "pending_proof"),
        expected_post_fix_status_counts={"pending_proof": 1},
    ),
    Phase3PostFixGateSpec(
        lane_number=4,
        lane_id="phase3_method_b_closure_lane4",
        gate_relpath=(
            "logs/equivalence_all/loop_test_phase3_method_b_closure_lane4_representatives/"
            "phase3_method_b_closure_lane4_gate/method_b_closure_lane4_post_fix_gate.json"
        ),
        manifest_kind="phase3_method_b_closure_lane4_post_fix_gate",
        ready_key="phase3_lane4_post_fix_ready",
        validator=validate_phase3_method_b_closure_lane4_post_fix_gate,
        expected_entry_count=1,
        allowed_post_fix_statuses=("completed_recovery", "pending_proof"),
        expected_post_fix_status_counts={"pending_proof": 1},
    ),
    Phase3PostFixGateSpec(
        lane_number=5,
        lane_id="phase3_sat_unsafety_lane5",
        gate_relpath=(
            "logs/equivalence_all/function_call_test_phase3_sat_unsafety_lane5_representatives/"
            "phase3_sat_unsafety_lane5_gate/sat_unsafety_lane5_post_fix_gate.json"
        ),
        manifest_kind="phase3_sat_unsafety_lane5_post_fix_gate",
        ready_key="phase3_lane5_post_fix_ready",
        validator=validate_phase3_sat_unsafety_lane5_post_fix_gate,
        expected_entry_count=1,
        allowed_post_fix_statuses=("completed_recovery", "pending_proof"),
        expected_post_fix_status_counts={"pending_proof": 1},
    ),
    Phase3PostFixGateSpec(
        lane_number=6,
        lane_id="phase3_unresolved_expression_lane6",
        gate_relpath=(
            "logs/equivalence_all/function_call_test_phase3_unresolved_expression_lane6_representatives/"
            "phase3_unresolved_expression_lane6_gate/unresolved_expression_lane6_post_fix_gate.json"
        ),
        manifest_kind="phase3_unresolved_expression_lane6_post_fix_gate",
        ready_key="phase3_lane6_post_fix_ready",
        validator=validate_phase3_unresolved_expression_lane6_post_fix_gate,
        expected_entry_count=1,
        allowed_post_fix_statuses=("pending_object_evidence", "pending_proof"),
        expected_post_fix_status_counts={"pending_proof": 1},
    ),
    Phase3PostFixGateSpec(
        lane_number=7,
        lane_id="phase3_solver_rewrite_lane7",
        gate_relpath=(
            "logs/equivalence_all/loop_test_phase3_solver_rewrite_lane7_representatives/"
            "phase3_solver_rewrite_lane7_gate/solver_rewrite_lane7_post_fix_gate.json"
        ),
        manifest_kind="phase3_solver_rewrite_lane7_post_fix_gate",
        ready_key="phase3_lane7_post_fix_ready",
        validator=validate_phase3_solver_rewrite_lane7_post_fix_gate,
        expected_entry_count=1,
        allowed_post_fix_statuses=("pending_proof", "retired_to_return_coverage_gap"),
        expected_post_fix_status_counts={"retired_to_return_coverage_gap": 1},
    ),
    Phase3PostFixGateSpec(
        lane_number=8,
        lane_id="phase3_solver_rewrite_proof_lane8",
        gate_relpath=(
            "logs/equivalence_all/function_call_test_phase3_solver_rewrite_proof_lane8_representatives/"
            "phase3_solver_rewrite_proof_lane8_gate/solver_rewrite_proof_lane8_post_fix_gate.json"
        ),
        manifest_kind="phase3_solver_rewrite_proof_lane8_post_fix_gate",
        ready_key="phase3_lane8_post_fix_ready",
        validator=validate_phase3_solver_rewrite_proof_lane8_post_fix_gate,
        expected_entry_count=1,
        allowed_post_fix_statuses=("pending_proof", "retired_to_sat_unsafety"),
        expected_post_fix_status_counts={"retired_to_sat_unsafety": 1},
    ),
    Phase3PostFixGateSpec(
        lane_number=9,
        lane_id="phase3_solver_timeout_lane9",
        gate_relpath=(
            "logs/equivalence_all/function_call_test_phase3_solver_timeout_lane9_representatives/"
            "phase3_solver_timeout_lane9_gate/solver_timeout_lane9_post_fix_gate.json"
        ),
        manifest_kind="phase3_solver_timeout_lane9_post_fix_gate",
        ready_key="phase3_lane9_post_fix_ready",
        validator=validate_phase3_solver_timeout_lane9_post_fix_gate,
        expected_entry_count=1,
        allowed_post_fix_statuses=("completed_recovery", "pending_retry"),
        expected_post_fix_status_counts={"pending_retry": 1},
    ),
)


def build_phase3_post_fix_gate_index(
    *,
    repo_root: Path,
    output_dir: Path,
    gate_specs: Sequence[Phase3PostFixGateSpec] = DEFAULT_PHASE3_POST_FIX_GATE_SPECS,
) -> Path:
    repo = Path(repo_root).resolve()
    output = Path(output_dir)
    output.mkdir(parents=True, exist_ok=True)
    gates = [_materialize_post_fix_gate(repo, spec) for spec in gate_specs]
    checks = _post_fix_index_checks(gate_specs, gates)
    summary = _summary(checks)
    post_fix_status_counts = _post_fix_status_counts_from_gates(gates)
    expected_post_fix_status_counts = _expected_post_fix_status_counts_from_specs(gate_specs)
    manifest = {
        "manifest_version": MANIFEST_VERSION,
        "manifest_kind": "phase3_post_fix_gate_index",
        "artifact_role": "derived_audit_post_fix_gate_index",
        "created_at": datetime.now(timezone.utc).isoformat(),
        "repo_root": str(repo),
        "phase3_post_fix_gates_ready": summary["failed"] == 0,
        "expected_post_fix_status_counts": expected_post_fix_status_counts,
        "post_fix_status_counts": post_fix_status_counts,
        "summary": summary,
        "gates": gates,
        "checks": checks,
    }
    path = output / "phase3_post_fix_gate_index.json"
    _write_json(path, manifest)
    return path


def validate_phase3_post_fix_gate_index(
    manifest: Mapping[str, Any],
    *,
    repo_root: Path,
    gate_specs: Optional[Sequence[Phase3PostFixGateSpec]] = None,
) -> None:
    failures: list[str] = []
    if manifest.get("manifest_kind") != "phase3_post_fix_gate_index":
        failures.append("manifest_kind")
    if manifest.get("manifest_version") != MANIFEST_VERSION:
        failures.append("manifest_version")
    if manifest.get("artifact_role") != "derived_audit_post_fix_gate_index":
        failures.append("artifact_role")
    manifest_repo_root = manifest.get("repo_root")
    repo = Path(repo_root).resolve()
    if not isinstance(manifest_repo_root, str) or not manifest_repo_root:
        failures.append("repo_root")
    elif manifest_repo_root != str(repo):
        failures.append("repo_root")

    summary = manifest.get("summary")
    failed = summary.get("failed_kinds") if isinstance(summary, Mapping) else None
    failed_kinds = list(failed or ()) if isinstance(failed, (list, tuple)) else []
    summary_failed = summary.get("failed") if isinstance(summary, Mapping) else MISSING_SENTINEL
    if not isinstance(summary, Mapping):
        failures.append("summary")
    elif not isinstance(summary_failed, int):
        failures.append("summary_failed_count")

    checks = manifest.get("checks")
    failed_check_kinds: list[str] = []
    checks_is_sequence = isinstance(checks, (list, tuple))
    if not checks_is_sequence:
        failures.append("checks")
    else:
        failed_check_kinds = _failed_check_kinds(checks)
        computed_summary = _summary(checks)
        if isinstance(summary_failed, int) and summary_failed != len(failed_check_kinds):
            failures.append("summary_failed_count")
        if failed_kinds != failed_check_kinds:
            failures.append("summary_failed_kinds")
        if isinstance(summary, Mapping) and dict(summary) != computed_summary:
            failures.append("summary_consistency")

    observed_status_counts = manifest.get("post_fix_status_counts")
    if not isinstance(observed_status_counts, Mapping):
        failures.append("post_fix_status_counts")
    specs = tuple(gate_specs or DEFAULT_PHASE3_POST_FIX_GATE_SPECS)
    observed_expected_status_counts = manifest.get("expected_post_fix_status_counts")
    expected_status_counts = _expected_post_fix_status_counts_from_specs(specs)
    if not isinstance(observed_expected_status_counts, Mapping):
        failures.append("expected_post_fix_status_counts")
    elif dict(observed_expected_status_counts) != expected_status_counts:
        failures.append("expected_post_fix_status_counts")

    gates = manifest.get("gates")
    if not isinstance(gates, (list, tuple)):
        failures.append("gates")
    else:
        computed_status_counts = _post_fix_status_counts_from_gates(gates)
        if isinstance(observed_status_counts, Mapping) and dict(observed_status_counts) != computed_status_counts:
            failures.append("post_fix_status_counts")
        actual_rows = _gate_spec_rows_from_gates(gates)
        expected_rows = _gate_spec_rows_from_specs(specs)
        if actual_rows != expected_rows:
            failures.append("gate_specs")
        derived_checks = _post_fix_index_checks(specs, gates)
        if checks_is_sequence and list(checks) != list(derived_checks):
            failures.append("derived_checks")
        if failed_check_kinds != _failed_check_kinds(derived_checks):
            failures.append("derived_failed_kinds")
        if isinstance(manifest_repo_root, str) and manifest_repo_root:
            materialized_gates = [
                _materialize_post_fix_gate(repo, spec)
                for spec in specs
            ]
            materialized_checks = _post_fix_index_checks(specs, materialized_gates)
            if gates != materialized_gates:
                failures.append("materialized_gates")
            if isinstance(observed_status_counts, Mapping) and dict(observed_status_counts) != _post_fix_status_counts_from_gates(materialized_gates):
                failures.append("materialized_status_counts")
            if (
                isinstance(observed_expected_status_counts, Mapping)
                and dict(observed_expected_status_counts)
                != _expected_post_fix_status_counts_from_specs(specs)
            ):
                failures.append("materialized_expected_status_counts")
            if checks_is_sequence and list(checks) != list(materialized_checks):
                failures.append("materialized_checks")
            if failed_check_kinds != _failed_check_kinds(materialized_checks):
                failures.append("materialized_failed_kinds")

    ready = manifest.get("phase3_post_fix_gates_ready")
    if ready is True:
        if summary_failed != 0 or failed_kinds:
            failures.append("phase3_post_fix_gates_ready_summary_clean")
        if failed_check_kinds:
            failures.append("phase3_post_fix_gates_ready_checks_clean")
    elif ready is False:
        if not failed_kinds:
            failures.append("phase3_post_fix_gates_ready_failure_kinds")
        else:
            failures.extend(str(kind) for kind in failed_kinds)
    else:
        failures.append("phase3_post_fix_gates_ready")

    if not failures:
        return
    raise ValueError(f"Phase 3 post-fix gate index failed: {', '.join(dict.fromkeys(failures))}")


def _materialize_post_fix_gate(repo: Path, spec: Phase3PostFixGateSpec) -> Dict[str, Any]:
    path = repo / spec.gate_relpath
    gate: Dict[str, Any] = {
        "lane_number": spec.lane_number,
        "lane_id": spec.lane_id,
        "gate_relpath": spec.gate_relpath,
        "gate_ref": _file_ref(path),
        "expected_manifest_kind": spec.manifest_kind,
        "ready_key": spec.ready_key,
        "expected_entry_count": spec.expected_entry_count,
        "allowed_post_fix_statuses": list(spec.allowed_post_fix_statuses),
        "expected_post_fix_status_counts": _normalized_expected_status_counts(spec),
        "status": "missing",
        "observed_manifest_kind": MISSING_SENTINEL,
        "observed_artifact_role": MISSING_SENTINEL,
        "baseline_id": MISSING_SENTINEL,
        "baseline_git_head": MISSING_SENTINEL,
        "ready_value": MISSING_SENTINEL,
        "entry_count": MISSING_SENTINEL,
        "post_fix_summary": {},
        "post_fix_status_counts": {},
        "post_fix_obligation_summary": {},
        "validator_status": "not_run",
        "validator_error": MISSING_SENTINEL,
    }
    if not path.exists():
        return gate
    gate["status"] = "present" if path.is_file() else "not_file"
    if not path.is_file():
        return gate
    try:
        payload = _read_json(path)
    except (OSError, json.JSONDecodeError) as exc:
        gate["status"] = "invalid_json"
        gate["validator_status"] = "failed"
        gate["validator_error"] = str(exc)
        return gate
    if not isinstance(payload, Mapping):
        gate["status"] = "invalid_payload"
        gate["validator_status"] = "failed"
        gate["validator_error"] = f"gate payload must be an object, got {type(payload).__name__}"
        return gate
    gate["observed_manifest_kind"] = payload.get("manifest_kind") or MISSING_SENTINEL
    gate["observed_artifact_role"] = payload.get("artifact_role") or MISSING_SENTINEL
    gate["baseline_id"] = payload.get("baseline_id") or MISSING_SENTINEL
    gate["baseline_git_head"] = payload.get("baseline_git_head") or MISSING_SENTINEL
    gate["ready_value"] = payload.get(spec.ready_key, MISSING_SENTINEL)
    gate["entry_count"] = _post_fix_entry_count(payload)
    gate["post_fix_summary"] = _post_fix_summary(payload)
    gate["post_fix_status_counts"] = _post_fix_status_counts(payload)
    gate["post_fix_obligation_summary"] = _post_fix_obligation_summary(payload)
    try:
        spec.validator(payload)
    except Exception as exc:
        gate["validator_status"] = "failed"
        gate["validator_error"] = f"{type(exc).__name__}: {exc}"
    else:
        gate["validator_status"] = "passed"
    return gate


def _post_fix_status_counts(payload: Mapping[str, Any]) -> Dict[str, int]:
    counts: Dict[str, int] = {}
    entries = payload.get("entries")
    if not isinstance(entries, (list, tuple)):
        return counts
    for entry in entries:
        if not isinstance(entry, Mapping):
            continue
        status = entry.get("post_fix_status")
        if not isinstance(status, str) or not status:
            continue
        counts[status] = counts.get(status, 0) + 1
    return dict(sorted(counts.items()))


def _post_fix_obligation_summary(payload: Mapping[str, Any]) -> Dict[str, Any]:
    summary = {
        "pending_proof_entry_count": 0,
        "pending_proof_obligation_count": 0,
        "pending_proof_entries_missing_required_actions": [],
        "pending_proof_entries_missing_obligations": [],
        "pending_proof_invalid_obligations": [],
        "pending_proof_required_action_mismatches": [],
        "pending_retry_entry_count": 0,
        "pending_retry_obligation_count": 0,
        "pending_retry_entries_missing_required_actions": [],
        "pending_retry_entries_missing_obligations": [],
        "pending_retry_invalid_obligations": [],
        "pending_retry_required_action_mismatches": [],
    }
    entries = payload.get("entries")
    if not isinstance(entries, (list, tuple)):
        return summary
    for index, entry in enumerate(entries):
        if not isinstance(entry, Mapping):
            continue
        status = entry.get("post_fix_status")
        if status == "pending_proof":
            _add_pending_obligation_summary(
                summary,
                entry=entry,
                entry_index=index,
                status_prefix="pending_proof",
                obligation_key="pending_proof_obligations",
                allowed_obligation_statuses={"pending_evidence", "completed_evidence_present"},
            )
        elif status == "pending_retry":
            _add_pending_obligation_summary(
                summary,
                entry=entry,
                entry_index=index,
                status_prefix="pending_retry",
                obligation_key="pending_retry_obligations",
                allowed_obligation_statuses={"pending_retry", "completed_evidence_present"},
            )
    return summary


def _add_pending_obligation_summary(
    summary: Dict[str, Any],
    *,
    entry: Mapping[str, Any],
    entry_index: int,
    status_prefix: str,
    obligation_key: str,
    allowed_obligation_statuses: set[str],
) -> None:
    entry_id = str(entry.get("id") or f"entry[{entry_index}]")
    entry_count_key = f"{status_prefix}_entry_count"
    obligation_count_key = f"{status_prefix}_obligation_count"
    missing_required_key = f"{status_prefix}_entries_missing_required_actions"
    missing_key = f"{status_prefix}_entries_missing_obligations"
    invalid_key = f"{status_prefix}_invalid_obligations"
    mismatch_key = f"{status_prefix}_required_action_mismatches"
    summary[entry_count_key] += 1
    obligations = entry.get(obligation_key)
    if not isinstance(obligations, (list, tuple)) or not obligations:
        summary[missing_key].append(entry_id)
        return
    summary[obligation_count_key] += len(obligations)
    for obligation_index, obligation in enumerate(obligations):
        if _pending_obligation_is_valid(obligation, allowed_obligation_statuses):
            continue
        summary[invalid_key].append(
            {
                "entry_id": entry_id,
                "obligation_index": obligation_index,
            }
        )
    required_actions = entry.get("required_completion_actions")
    if not isinstance(required_actions, (list, tuple)) or not required_actions:
        summary[missing_required_key].append(entry_id)
        return
    required_keys = {
        _pending_obligation_required_key(action)
        for action in required_actions
        if isinstance(action, Mapping)
    }
    obligation_keys = {
        _pending_obligation_required_key(obligation)
        for obligation in obligations
        if isinstance(obligation, Mapping)
    }
    if required_keys != obligation_keys:
        summary[mismatch_key].append(
            {
                "entry_id": entry_id,
                "missing_required_actions": sorted(required_keys - obligation_keys),
                "unexpected_obligations": sorted(obligation_keys - required_keys),
            }
        )


def _pending_obligation_is_valid(
    obligation: Any,
    allowed_obligation_statuses: set[str],
) -> bool:
    if not isinstance(obligation, Mapping):
        return False
    for field_name in ("reason_id", "proof_kind", "proof_stage", "evidence_kind"):
        if not _specific_text(obligation.get(field_name)):
            return False
    proof_obligation_id = obligation.get("proof_obligation_id")
    if proof_obligation_id is None or _contains_missing_sentinel(proof_obligation_id):
        return False
    required_evidence = obligation.get("required_evidence")
    if (
        not isinstance(required_evidence, (list, tuple))
        or not required_evidence
        or not all(_specific_text(item) for item in required_evidence)
    ):
        return False
    if obligation.get("completed_evidence_present") not in {True, False}:
        return False
    status = obligation.get("status")
    return isinstance(status, str) and status in allowed_obligation_statuses


def _pending_obligation_required_key(value: Mapping[str, Any]) -> str:
    return json.dumps(
        {
            "reason_id": value.get("reason_id") or MISSING_SENTINEL,
            "proof_kind": value.get("proof_kind") or MISSING_SENTINEL,
            "proof_stage": value.get("proof_stage") or MISSING_SENTINEL,
            "evidence_kind": value.get("evidence_kind") or MISSING_SENTINEL,
            "required_evidence": list(value.get("required_evidence") or ()),
            "proof_obligation_id": value.get("proof_obligation_id") or MISSING_SENTINEL,
        },
        sort_keys=True,
        separators=(",", ":"),
    )


def _specific_text(value: Any) -> bool:
    return isinstance(value, str) and bool(value) and value != MISSING_SENTINEL


def _contains_missing_sentinel(value: Any) -> bool:
    if value == MISSING_SENTINEL:
        return True
    if isinstance(value, Mapping):
        return any(
            _contains_missing_sentinel(key) or _contains_missing_sentinel(item)
            for key, item in value.items()
        )
    if isinstance(value, (list, tuple)):
        return any(_contains_missing_sentinel(item) for item in value)
    return False


def _post_fix_entry_count(payload: Mapping[str, Any]) -> int:
    entries = payload.get("entries")
    return len(entries) if isinstance(entries, (list, tuple)) else 0


def _post_fix_status_counts_from_gates(gates: Sequence[Any]) -> Dict[str, int]:
    counts: Dict[str, int] = {}
    for gate in gates:
        if not isinstance(gate, Mapping):
            continue
        gate_counts = gate.get("post_fix_status_counts")
        if not isinstance(gate_counts, Mapping):
            continue
        for status, count in gate_counts.items():
            if not isinstance(status, str) or not isinstance(count, int):
                continue
            counts[status] = counts.get(status, 0) + count
    return dict(sorted(counts.items()))


def _post_fix_summary(payload: Mapping[str, Any]) -> Dict[str, Any]:
    gate = payload.get("post_fix_regression_gate")
    if isinstance(gate, Mapping) and isinstance(gate.get("summary"), Mapping):
        summary = gate.get("summary") or {}
        return {
            "failed": summary.get("failed", MISSING_SENTINEL),
            "failed_kinds": list(summary.get("failed_kinds") or ()),
        }
    checks = payload.get("checks")
    if isinstance(checks, (list, tuple)):
        failed = _failed_check_kinds(checks)
        return {"failed": len(failed), "failed_kinds": failed}
    return {}


def _post_fix_index_checks(
    specs: Sequence[Phase3PostFixGateSpec],
    gates: Sequence[Any],
) -> Sequence[Dict[str, Any]]:
    checks: list[Dict[str, Any]] = []
    expected_rows = _gate_spec_rows_from_specs(specs)
    actual_rows = _gate_spec_rows_from_gates(gates)
    checks.append(
        _ok("phase3_post_fix_gate_specs")
        if actual_rows == expected_rows
        else _failed("phase3_post_fix_gate_specs", expected=expected_rows, actual=actual_rows)
    )
    expected_global_status_counts = _expected_post_fix_status_counts_from_specs(specs)
    actual_global_status_counts = _post_fix_status_counts_from_gates(gates)
    if expected_global_status_counts:
        checks.append(
            _ok("phase3_post_fix_gate_status_counts_global_expected")
            if actual_global_status_counts == expected_global_status_counts
            else _failed(
                "phase3_post_fix_gate_status_counts_global_expected",
                expected=expected_global_status_counts,
                actual=actual_global_status_counts,
            )
        )
    spec_by_lane = {spec.lane_id: spec for spec in specs}
    for gate in gates:
        if not isinstance(gate, Mapping):
            checks.append(_failed("phase3_post_fix_gate_entry_mapping", actual=type(gate).__name__))
            continue
        lane_id = str(gate.get("lane_id") or MISSING_SENTINEL)
        spec = spec_by_lane.get(lane_id)
        details = {"lane_id": lane_id, "lane_number": gate.get("lane_number", MISSING_SENTINEL)}
        checks.append(
            _ok("phase3_post_fix_gate_present", **details)
            if gate.get("status") == "present"
            else _failed("phase3_post_fix_gate_present", gate_status=gate.get("status"), **details)
        )
        checks.append(
            _ok("phase3_post_fix_gate_manifest_kind", **details)
            if spec is not None and gate.get("observed_manifest_kind") == spec.manifest_kind
            else _failed(
                "phase3_post_fix_gate_manifest_kind",
                expected=spec.manifest_kind if spec is not None else MISSING_SENTINEL,
                actual=gate.get("observed_manifest_kind"),
                **details,
            )
        )
        checks.append(
            _ok("phase3_post_fix_gate_artifact_role", **details)
            if gate.get("observed_artifact_role") == "derived_audit_post_fix_gate"
            else _failed(
                "phase3_post_fix_gate_artifact_role",
                expected="derived_audit_post_fix_gate",
                actual=gate.get("observed_artifact_role"),
                **details,
            )
        )
        checks.append(
            _ok("phase3_post_fix_gate_baseline_id", **details)
            if gate.get("baseline_id") == BASELINE_ID
            else _failed(
                "phase3_post_fix_gate_baseline_id",
                expected=BASELINE_ID,
                actual=gate.get("baseline_id"),
                **details,
            )
        )
        checks.append(
            _ok("phase3_post_fix_gate_baseline_git_head", **details)
            if gate.get("baseline_git_head") == BASELINE_GIT_HEAD
            else _failed(
                "phase3_post_fix_gate_baseline_git_head",
                expected=BASELINE_GIT_HEAD,
                actual=gate.get("baseline_git_head"),
                **details,
            )
        )
        checks.append(
            _ok("phase3_post_fix_gate_ready", **details)
            if gate.get("ready_value") is True
            else _failed("phase3_post_fix_gate_ready", ready_value=gate.get("ready_value"), **details)
        )
        expected_entry_count = spec.expected_entry_count if spec is not None else None
        actual_entry_count = gate.get("entry_count", MISSING_SENTINEL)
        if expected_entry_count is not None:
            checks.append(
                _ok("phase3_post_fix_gate_entry_count", **details)
                if actual_entry_count == expected_entry_count
                else _failed(
                    "phase3_post_fix_gate_entry_count",
                    expected=expected_entry_count,
                    actual=actual_entry_count,
                    **details,
                )
            )
        status_counts = gate.get("post_fix_status_counts")
        status_count_total = (
            sum(count for count in status_counts.values() if isinstance(count, int))
            if isinstance(status_counts, Mapping)
            else MISSING_SENTINEL
        )
        checks.append(
            _ok("phase3_post_fix_gate_status_count_complete", **details)
            if status_count_total == actual_entry_count
            else _failed(
                "phase3_post_fix_gate_status_count_complete",
                entry_count=actual_entry_count,
                status_count_total=status_count_total,
                **details,
            )
        )
        allowed_statuses = set(spec.allowed_post_fix_statuses if spec is not None else ())
        unexpected_statuses = (
            sorted(str(status) for status in status_counts if status not in allowed_statuses)
            if isinstance(status_counts, Mapping) and allowed_statuses
            else []
        )
        checks.append(
            _ok("phase3_post_fix_gate_status_allowed", **details)
            if not unexpected_statuses
            else _failed(
                "phase3_post_fix_gate_status_allowed",
                allowed=sorted(allowed_statuses),
                unexpected=unexpected_statuses,
                **details,
            )
        )
        expected_status_counts = (
            _normalized_expected_status_counts(spec)
            if spec is not None
            else {}
        )
        actual_status_counts = (
            dict(sorted(status_counts.items()))
            if isinstance(status_counts, Mapping)
            else {}
        )
        if expected_status_counts:
            checks.append(
                _ok("phase3_post_fix_gate_status_counts_expected", **details)
                if actual_status_counts == expected_status_counts
                else _failed(
                    "phase3_post_fix_gate_status_counts_expected",
                    expected=expected_status_counts,
                    actual=actual_status_counts,
                    **details,
                )
            )
        obligation_summary = (
            gate.get("post_fix_obligation_summary")
            if isinstance(gate.get("post_fix_obligation_summary"), Mapping)
            else {}
        )
        pending_proof_missing = list(
            obligation_summary.get("pending_proof_entries_missing_obligations") or ()
        )
        pending_retry_missing = list(
            obligation_summary.get("pending_retry_entries_missing_obligations") or ()
        )
        pending_proof_missing_required = list(
            obligation_summary.get("pending_proof_entries_missing_required_actions") or ()
        )
        pending_retry_missing_required = list(
            obligation_summary.get("pending_retry_entries_missing_required_actions") or ()
        )
        pending_proof_invalid = list(
            obligation_summary.get("pending_proof_invalid_obligations") or ()
        )
        pending_retry_invalid = list(
            obligation_summary.get("pending_retry_invalid_obligations") or ()
        )
        pending_proof_mismatches = list(
            obligation_summary.get("pending_proof_required_action_mismatches") or ()
        )
        pending_retry_mismatches = list(
            obligation_summary.get("pending_retry_required_action_mismatches") or ()
        )
        obligation_failures = {
            "pending_proof_missing_required_actions": pending_proof_missing_required,
            "pending_retry_missing_required_actions": pending_retry_missing_required,
            "pending_proof_missing": pending_proof_missing,
            "pending_retry_missing": pending_retry_missing,
            "pending_proof_invalid": pending_proof_invalid,
            "pending_retry_invalid": pending_retry_invalid,
            "pending_proof_required_action_mismatches": pending_proof_mismatches,
            "pending_retry_required_action_mismatches": pending_retry_mismatches,
        }
        checks.append(
            _ok("phase3_post_fix_gate_pending_obligations_present", **details)
            if not any(obligation_failures.values())
            else _failed(
                "phase3_post_fix_gate_pending_obligations_present",
                **obligation_failures,
                **details,
            )
        )
        post_fix_summary = gate.get("post_fix_summary")
        summary_failed = (
            post_fix_summary.get("failed", MISSING_SENTINEL)
            if isinstance(post_fix_summary, Mapping)
            else MISSING_SENTINEL
        )
        summary_failed_kinds = (
            list(post_fix_summary.get("failed_kinds") or ())
            if isinstance(post_fix_summary, Mapping)
            else MISSING_SENTINEL
        )
        checks.append(
            _ok("phase3_post_fix_gate_summary_clean", **details)
            if summary_failed == 0 and summary_failed_kinds == []
            else _failed(
                "phase3_post_fix_gate_summary_clean",
                failed=summary_failed,
                failed_kinds=summary_failed_kinds,
                **details,
            )
        )
        checks.append(
            _ok("phase3_post_fix_gate_validator", **details)
            if gate.get("validator_status") == "passed"
            else _failed(
                "phase3_post_fix_gate_validator",
                validator_status=gate.get("validator_status"),
                validator_error=gate.get("validator_error"),
                **details,
            )
        )
    return checks


def _gate_spec_rows_from_specs(specs: Sequence[Phase3PostFixGateSpec]) -> list[Dict[str, Any]]:
    return [
        {
            "lane_number": spec.lane_number,
            "lane_id": spec.lane_id,
            "gate_relpath": spec.gate_relpath,
            "manifest_kind": spec.manifest_kind,
            "ready_key": spec.ready_key,
            "expected_entry_count": spec.expected_entry_count,
            "allowed_post_fix_statuses": list(spec.allowed_post_fix_statuses),
            "expected_post_fix_status_counts": _normalized_expected_status_counts(spec),
        }
        for spec in specs
    ]


def _gate_spec_rows_from_gates(gates: Sequence[Any]) -> list[Dict[str, Any]]:
    rows: list[Dict[str, Any]] = []
    for gate in gates:
        if not isinstance(gate, Mapping):
            rows.append({"invalid_gate_entry": type(gate).__name__})
            continue
        rows.append(
            {
                "lane_number": gate.get("lane_number"),
                "lane_id": gate.get("lane_id"),
                "gate_relpath": gate.get("gate_relpath"),
                "manifest_kind": gate.get("expected_manifest_kind"),
                "ready_key": gate.get("ready_key"),
                "expected_entry_count": gate.get("expected_entry_count"),
                "allowed_post_fix_statuses": list(gate.get("allowed_post_fix_statuses") or ()),
                "expected_post_fix_status_counts": dict(
                    sorted((gate.get("expected_post_fix_status_counts") or {}).items())
                )
                if isinstance(gate.get("expected_post_fix_status_counts"), Mapping)
                else {},
            }
        )
    return rows


def _normalized_expected_status_counts(spec: Phase3PostFixGateSpec) -> Dict[str, int]:
    counts = spec.expected_post_fix_status_counts
    if not counts:
        return {}
    return {
        str(status): int(count)
        for status, count in sorted(counts.items())
    }


def _expected_post_fix_status_counts_from_specs(
    specs: Sequence[Phase3PostFixGateSpec],
) -> Dict[str, int]:
    counts: Dict[str, int] = {}
    for spec in specs:
        for status, count in _normalized_expected_status_counts(spec).items():
            counts[status] = counts.get(status, 0) + count
    return dict(sorted(counts.items()))


def main(argv: Optional[Sequence[str]] = None) -> int:
    parser = argparse.ArgumentParser(
        description="Build a Phase 3 post-fix gate artifact index.",
    )
    parser.add_argument("--repo-root", default=".")
    parser.add_argument("--output-dir", required=True)
    parser.add_argument("--require-ready", action="store_true")
    args = parser.parse_args(argv)
    path = build_phase3_post_fix_gate_index(
        repo_root=Path(args.repo_root),
        output_dir=Path(args.output_dir),
    )
    if args.require_ready:
        validate_phase3_post_fix_gate_index(_read_json(path), repo_root=Path(args.repo_root))
    print(path)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
