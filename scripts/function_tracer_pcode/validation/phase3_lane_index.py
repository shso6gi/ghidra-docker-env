# -*- coding: utf-8 -*-
"""Build a fixed index over Phase 3 proof-lane audit manifests."""

from __future__ import annotations

import argparse
import os
import re
from dataclasses import dataclass
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Callable, Dict, Mapping, Optional, Sequence

from .phase3_method_b_closure_lane4 import validate_phase3_method_b_closure_lane4_manifest
from .phase3_readonly_identity_lane3 import validate_phase3_readonly_identity_lane3_manifest
from .phase3_return_coverage_lane1 import validate_phase3_return_coverage_lane1_manifest
from .phase3_return_width_bridge_lane2 import validate_phase3_return_width_bridge_lane2_manifest
from .phase3_sat_unsafety_lane5 import validate_phase3_sat_unsafety_lane5_manifest
from .phase3_solver_rewrite_lane7 import validate_phase3_solver_rewrite_lane7_manifest
from .phase3_solver_rewrite_proof_lane8 import validate_phase3_solver_rewrite_proof_lane8_manifest
from .phase3_solver_timeout_lane9 import validate_phase3_solver_timeout_lane9_manifest
from .phase3_unresolved_expression_lane6 import validate_phase3_unresolved_expression_lane6_manifest
from .phase3_return_width_bridge_lane2 import (
    _failed,
    _file_ref,
    _ok,
    _read_json,
    _sha256_file,
    _write_json,
)


MANIFEST_VERSION = 1
BASELINE_ID = "observed-v0@0a53352"
MISSING_SENTINEL = "<missing>"
LaneValidator = Callable[[Mapping[str, Any]], None]
_RUNNER_MANIFEST_PATH_RE = re.compile(
    r'PHASE3_MANIFEST_PATH="\$\{PHASE3_MANIFEST_PATH:-\$SCRIPT_DIR/(?P<path>[^"}]+)\}"'
)
_RUNNER_MANIFEST_SHA_RE = re.compile(
    r'PHASE3_MANIFEST_SHA256="\$\{PHASE3_MANIFEST_SHA256:-(?P<sha>[0-9a-f]{64})\}"'
)
_RUNNER_TARGET_SET_RE = re.compile(
    r'export (?P<var>FUNCTION_CALL_TARGET_SET|LOOP_TARGET_SET)="\$\{(?P=var):-(?P<value>[^"}]*)\}"'
)
_RUNNER_PAIR_FILTER_RE = re.compile(
    r'export (?P<var>FUNCTION_CALL_PAIR_FILTER|LOOP_PAIR_FILTER)="\$\{(?P=var):-(?P<value>[^"}]*)\}"'
)
_RUNNER_BASE_PATH_RE = re.compile(
    r'export BASE_PATH="\$\{BASE_PATH:-\$SCRIPT_DIR/(?P<path>[^"}]+)\}"'
)
_RUNNER_MATRIX_SCRIPT_RE = re.compile(
    r'bash "\$SCRIPT_DIR/(?P<path>(?:func_call|loop)_run_matrix_all_parallel_multifunc\.sh)"'
)


@dataclass(frozen=True)
class Phase3LaneSpec:
    lane_number: int
    lane_id: str
    target_reason_ids: Sequence[str]
    manifest_relpath: str
    runner_relpath: str
    manifest_kind: str
    ready_key: str
    validator: Optional[LaneValidator] = None
    lane_reason_ids: Optional[Sequence[str]] = None
    pending_proof_keeps_final_result: Optional[str] = None
    completion_required_for_recovery: Optional[Sequence[str]] = None
    required_recovery_actions: Optional[Sequence[str]] = None
    require_runner_manifest_ref: bool = False
    require_runner_target_filter: bool = False


DEFAULT_PHASE3_LANE_SPECS: Sequence[Phase3LaneSpec] = (
    Phase3LaneSpec(
        lane_number=1,
        lane_id="phase3_return_coverage_lane1",
        target_reason_ids=("return_coverage_gap",),
        lane_reason_ids=("return_coverage_gap", "return_coverage_inconclusive"),
        manifest_relpath="audit/phase3_return_coverage_lane1_reclassification/return_coverage_lane1_representatives.json",
        runner_relpath="phase3_run_function_call_return_coverage_lane1_representatives.sh",
        manifest_kind="phase3_return_coverage_lane1_representatives",
        ready_key="phase3_lane1_ready",
        validator=validate_phase3_return_coverage_lane1_manifest,
        pending_proof_keeps_final_result="UNKNOWN",
        completion_required_for_recovery=("return_partition_extraction", "return_guard_coverage"),
        required_recovery_actions=("return_coverage_proof_required",),
        require_runner_manifest_ref=True,
        require_runner_target_filter=True,
    ),
    Phase3LaneSpec(
        lane_number=2,
        lane_id="phase3_return_width_bridge_lane2",
        target_reason_ids=("return_width_bridge_missing",),
        manifest_relpath="audit/phase3_return_width_bridge_lane2/return_width_bridge_lane2_representatives.json",
        runner_relpath="phase3_run_function_call_return_width_bridge_lane2_representatives.sh",
        manifest_kind="phase3_return_width_bridge_lane2_representatives",
        ready_key="phase3_lane2_ready",
        validator=validate_phase3_return_width_bridge_lane2_manifest,
        pending_proof_keeps_final_result="UNKNOWN",
        completion_required_for_recovery=("abi_relation", "high_bit_relation"),
        required_recovery_actions=("abi_relation", "high_bit_relation"),
        require_runner_manifest_ref=True,
        require_runner_target_filter=True,
    ),
    Phase3LaneSpec(
        lane_number=3,
        lane_id="phase3_readonly_identity_lane3",
        target_reason_ids=("readonly_identity_missing",),
        manifest_relpath="audit/phase3_readonly_identity_lane3/readonly_identity_lane3_representatives.json",
        runner_relpath="phase3_run_loop_readonly_identity_lane3_representatives.sh",
        manifest_kind="phase3_readonly_identity_lane3_representatives",
        ready_key="phase3_lane3_ready",
        validator=validate_phase3_readonly_identity_lane3_manifest,
        pending_proof_keeps_final_result="UNKNOWN",
        completion_required_for_recovery=("readonly_operand_identity",),
        required_recovery_actions=("readonly_operand_identity",),
        require_runner_manifest_ref=True,
        require_runner_target_filter=True,
    ),
    Phase3LaneSpec(
        lane_number=4,
        lane_id="phase3_method_b_closure_lane4",
        target_reason_ids=("method_b_closure_blocked",),
        manifest_relpath="audit/phase3_method_b_closure_lane4/method_b_closure_lane4_representatives.json",
        runner_relpath="phase3_run_loop_method_b_closure_lane4_representatives.sh",
        manifest_kind="phase3_method_b_closure_lane4_representatives",
        ready_key="phase3_lane4_ready",
        validator=validate_phase3_method_b_closure_lane4_manifest,
        pending_proof_keeps_final_result="UNKNOWN",
        completion_required_for_recovery=("method_b_covering_case", "method_b_guard_partition"),
        required_recovery_actions=("method_b_covering_case", "method_b_guard_partition"),
        require_runner_manifest_ref=True,
        require_runner_target_filter=True,
    ),
    Phase3LaneSpec(
        lane_number=5,
        lane_id="phase3_sat_unsafety_lane5",
        target_reason_ids=("sat_unsafety",),
        manifest_relpath="audit/phase3_sat_unsafety_lane5/sat_unsafety_lane5_representatives.json",
        runner_relpath="phase3_run_function_call_sat_unsafety_lane5_representatives.sh",
        manifest_kind="phase3_sat_unsafety_lane5_representatives",
        ready_key="phase3_lane5_ready",
        validator=validate_phase3_sat_unsafety_lane5_manifest,
        require_runner_manifest_ref=True,
        require_runner_target_filter=True,
    ),
    Phase3LaneSpec(
        lane_number=6,
        lane_id="phase3_unresolved_expression_lane6",
        target_reason_ids=("unresolved_expression",),
        manifest_relpath="audit/phase3_unresolved_expression_lane6/unresolved_expression_lane6_representatives.json",
        runner_relpath="phase3_run_function_call_unresolved_expression_lane6_representatives.sh",
        manifest_kind="phase3_unresolved_expression_lane6_representatives",
        ready_key="phase3_lane6_ready",
        validator=validate_phase3_unresolved_expression_lane6_manifest,
        require_runner_manifest_ref=True,
        require_runner_target_filter=True,
    ),
    Phase3LaneSpec(
        lane_number=7,
        lane_id="phase3_solver_rewrite_lane7",
        target_reason_ids=("solver_proven_rewrite_no_change",),
        manifest_relpath="audit/phase3_solver_rewrite_lane7/solver_rewrite_lane7_representatives.json",
        runner_relpath="phase3_run_loop_solver_rewrite_lane7_representatives.sh",
        manifest_kind="phase3_solver_rewrite_lane7_representatives",
        ready_key="phase3_lane7_ready",
        validator=validate_phase3_solver_rewrite_lane7_manifest,
        require_runner_manifest_ref=True,
        require_runner_target_filter=True,
    ),
    Phase3LaneSpec(
        lane_number=8,
        lane_id="phase3_solver_rewrite_proof_lane8",
        target_reason_ids=("solver_proven_rewrite_proof_failed",),
        manifest_relpath="audit/phase3_solver_rewrite_proof_lane8/solver_rewrite_proof_lane8_representatives.json",
        runner_relpath="phase3_run_function_call_solver_rewrite_proof_lane8_representatives.sh",
        manifest_kind="phase3_solver_rewrite_proof_lane8_representatives",
        ready_key="phase3_lane8_ready",
        validator=validate_phase3_solver_rewrite_proof_lane8_manifest,
        require_runner_manifest_ref=True,
        require_runner_target_filter=True,
    ),
    Phase3LaneSpec(
        lane_number=9,
        lane_id="phase3_solver_timeout_lane9",
        target_reason_ids=("solver_unknown_timeout",),
        manifest_relpath="audit/phase3_solver_timeout_lane9/solver_timeout_lane9_representatives.json",
        runner_relpath="phase3_run_function_call_solver_timeout_lane9_representatives.sh",
        manifest_kind="phase3_solver_timeout_lane9_representatives",
        ready_key="phase3_lane9_ready",
        validator=validate_phase3_solver_timeout_lane9_manifest,
        pending_proof_keeps_final_result="TIMEOUT",
        completion_required_for_recovery=("solver_timeout_retry",),
        required_recovery_actions=("solver_timeout_retry",),
        require_runner_manifest_ref=True,
        require_runner_target_filter=True,
    ),
)


def build_phase3_lane_index(
    *,
    baseline_root: Path,
    output_dir: Path,
    repo_root: Optional[Path] = None,
    lane_specs: Sequence[Phase3LaneSpec] = DEFAULT_PHASE3_LANE_SPECS,
) -> Path:
    """Write a Phase 3 lane index manifest and return its path."""

    root = Path(baseline_root)
    repo = Path(repo_root) if repo_root is not None else Path.cwd()
    output = Path(output_dir)
    output.mkdir(parents=True, exist_ok=True)
    baseline_manifest = _read_json(root / "raw" / "artifact_manifest.json")
    lanes = [_materialize_lane(root, repo, spec) for spec in lane_specs]
    checks = _index_checks(baseline_manifest, lane_specs, lanes)
    summary = _summary(checks)
    manifest = {
        "manifest_version": MANIFEST_VERSION,
        "manifest_kind": "phase3_proof_lane_index",
        "artifact_role": "derived_audit_lane_index",
        "baseline_id": baseline_manifest.get("baseline_id") or MISSING_SENTINEL,
        "baseline_git_head": baseline_manifest.get("git_head") or MISSING_SENTINEL,
        "created_at": datetime.now(timezone.utc).isoformat(),
        "baseline_raw_artifact_ref": _file_ref(root / "raw" / "artifact_manifest.json"),
        "repo_root": str(repo),
        "phase3_lanes_ready": summary["failed"] == 0,
        "summary": summary,
        "lanes": lanes,
        "checks": checks,
    }
    path = output / "phase3_lane_index.json"
    _write_json(path, manifest)
    return path


def validate_phase3_lane_index(manifest: Mapping[str, Any]) -> None:
    if manifest.get("manifest_kind") != "phase3_proof_lane_index":
        raise ValueError("Phase 3 lane index manifest kind mismatch")
    if manifest.get("phase3_lanes_ready") is True:
        return
    summary = manifest.get("summary")
    failed = summary.get("failed_kinds") if isinstance(summary, Mapping) else None
    if not failed:
        raise ValueError("Phase 3 lane index readiness is false without failed gate kinds")
    raise ValueError(f"Phase 3 lane index failed: {', '.join(map(str, failed))}")


def _materialize_lane(root: Path, repo: Path, spec: Phase3LaneSpec) -> Dict[str, Any]:
    path = root / spec.manifest_relpath
    runner_path = repo / spec.runner_relpath
    lane: Dict[str, Any] = {
        "lane_number": spec.lane_number,
        "lane_id": spec.lane_id,
        "target_reason_ids": list(spec.target_reason_ids),
        "lane_reason_ids": list(_lane_reason_ids(spec)),
        "expected_proof_completion_gate": _expected_proof_completion_gate(spec),
        "require_runner_manifest_ref": spec.require_runner_manifest_ref,
        "require_runner_target_filter": spec.require_runner_target_filter,
        "expected_runner_manifest_relpath": _expected_runner_manifest_relpath(spec),
        "manifest_ref": _file_ref(path),
        "manifest_relpath": spec.manifest_relpath,
        "runner_ref": _file_ref(runner_path),
        "runner_relpath": spec.runner_relpath,
        "expected_manifest_kind": spec.manifest_kind,
        "ready_key": spec.ready_key,
        "status": "missing",
        "manifest_sha256": MISSING_SENTINEL,
        "observed_manifest_kind": MISSING_SENTINEL,
        "ready_value": MISSING_SENTINEL,
        "validator_status": "not_run",
        "runner_status": "missing",
        "runner_sha256": MISSING_SENTINEL,
        "runner_executable": False,
        "runner_manifest_relpath": MISSING_SENTINEL,
        "runner_manifest_sha256": MISSING_SENTINEL,
        "runner_target_category": MISSING_SENTINEL,
        "runner_target_var": MISSING_SENTINEL,
        "runner_pair_filter_var": MISSING_SENTINEL,
        "runner_base_path_relpath": MISSING_SENTINEL,
        "runner_matrix_script_relpath": MISSING_SENTINEL,
        "runner_target_functions": [],
        "runner_pair_filter": [],
        "expected_target_category": MISSING_SENTINEL,
        "expected_pair_filter_var": MISSING_SENTINEL,
        "expected_base_path_relpath": MISSING_SENTINEL,
        "expected_matrix_script_relpath": MISSING_SENTINEL,
        "expected_target_functions": [],
        "expected_pair_filter": [],
    }
    if runner_path.exists():
        lane["runner_status"] = "present" if runner_path.is_file() else "not_file"
        if runner_path.is_file():
            lane["runner_sha256"] = _sha256_file(runner_path)
            lane["runner_executable"] = os.access(runner_path, os.X_OK)
            runner_refs = _runner_manifest_refs(runner_path)
            lane["runner_manifest_relpath"] = runner_refs["manifest_relpath"]
            lane["runner_manifest_sha256"] = runner_refs["manifest_sha256"]
            runner_targets = _runner_target_filter(runner_path)
            lane["runner_target_category"] = runner_targets["category"]
            lane["runner_target_var"] = runner_targets["target_var"]
            lane["runner_pair_filter_var"] = runner_targets["pair_filter_var"]
            lane["runner_base_path_relpath"] = runner_targets["base_path_relpath"]
            lane["runner_matrix_script_relpath"] = runner_targets["matrix_script_relpath"]
            lane["runner_target_functions"] = runner_targets["target_functions"]
            lane["runner_pair_filter"] = runner_targets["pair_filter"]
    if not path.exists():
        return lane
    lane["status"] = "present"
    lane["manifest_sha256"] = _sha256_file(path)
    try:
        manifest = _read_json(path)
    except (OSError, ValueError) as exc:
        lane["status"] = "invalid_json"
        lane["validator_status"] = "failed"
        lane["validator_error"] = str(exc)
        return lane
    lane["observed_manifest_kind"] = manifest.get("manifest_kind") or MISSING_SENTINEL
    lane["ready_value"] = manifest.get(spec.ready_key, MISSING_SENTINEL)
    lane["observed_target_reason_ids"] = list(manifest.get("target_reason_ids") or ())
    expected_targets = _manifest_target_filter(manifest)
    lane["expected_target_category"] = expected_targets["category"]
    lane["expected_pair_filter_var"] = expected_targets["pair_filter_var"]
    lane["expected_base_path_relpath"] = expected_targets["base_path_relpath"]
    lane["expected_matrix_script_relpath"] = expected_targets["matrix_script_relpath"]
    lane["expected_target_functions"] = expected_targets["target_functions"]
    lane["expected_pair_filter"] = expected_targets["pair_filter"]
    lane["representative_entries"] = _representative_entries(manifest.get("entries"))
    implementation = manifest.get("implementation_manifest")
    if isinstance(implementation, Mapping):
        implementation_reason_ids = _implementation_reason_ids(implementation)
        lane["implementation_manifest"] = {
            "lane_id": implementation.get("lane_id") or MISSING_SENTINEL,
            "target_reason_id": implementation.get("target_reason_id") or MISSING_SENTINEL,
            "active_target_reason_id": implementation.get("active_target_reason_id") or MISSING_SENTINEL,
            "lane_reason_ids": list(implementation.get("lane_reason_ids") or ()),
            "implementation_reason_ids": list(implementation_reason_ids),
            "baseline_mode": implementation.get("baseline_mode") or MISSING_SENTINEL,
        }
        proof_gate = implementation.get("proof_completion_gate")
        if isinstance(proof_gate, Mapping):
            lane["proof_completion_gate"] = _materialize_proof_completion_gate(proof_gate)
    if spec.validator is not None:
        try:
            spec.validator(manifest)
        except ValueError as exc:
            lane["validator_status"] = "failed"
            lane["validator_error"] = str(exc)
        else:
            lane["validator_status"] = "passed"
    return lane


def _index_checks(
    baseline_manifest: Mapping[str, Any],
    specs: Sequence[Phase3LaneSpec],
    lanes: Sequence[Mapping[str, Any]],
) -> Sequence[Dict[str, Any]]:
    checks: list[Dict[str, Any]] = []
    checks.append(
        _ok("baseline_id")
        if baseline_manifest.get("baseline_id") == BASELINE_ID
        else _failed("baseline_id", expected=BASELINE_ID, actual=baseline_manifest.get("baseline_id"))
    )
    lane_numbers = [spec.lane_number for spec in specs]
    expected_lane_numbers = list(range(1, len(specs) + 1))
    checks.append(
        _ok("phase3_lane_order")
        if lane_numbers == expected_lane_numbers
        else _failed("phase3_lane_order", expected=expected_lane_numbers, actual=lane_numbers)
    )
    seen = set()
    for lane in lanes:
        details = {
            "lane_number": lane.get("lane_number"),
            "lane_id": lane.get("lane_id"),
            "manifest_relpath": lane.get("manifest_relpath"),
            "runner_relpath": lane.get("runner_relpath"),
        }
        lane_id = lane.get("lane_id")
        checks.append(
            _failed("phase3_lane_id_unique", **details)
            if lane_id in seen
            else _ok("phase3_lane_id_unique", **details)
        )
        seen.add(lane_id)
        checks.append(
            _ok("phase3_lane_manifest_present", **details)
            if lane.get("status") == "present"
            else _failed("phase3_lane_manifest_present", manifest_status=lane.get("status"), **details)
        )
        checks.append(
            _ok("phase3_lane_runner_present", **details)
            if lane.get("runner_status") == "present"
            else _failed("phase3_lane_runner_present", runner_status=lane.get("runner_status"), **details)
        )
        checks.append(
            _ok("phase3_lane_runner_executable", **details)
            if lane.get("runner_executable") is True
            else _failed(
                "phase3_lane_runner_executable",
                runner_status=lane.get("runner_status"),
                runner_executable=lane.get("runner_executable"),
                **details,
            )
        )
        if lane.get("require_runner_manifest_ref") is True:
            checks.append(
                _ok("phase3_lane_runner_manifest_path", **details)
                if lane.get("runner_manifest_relpath") == lane.get("expected_runner_manifest_relpath")
                else _failed(
                    "phase3_lane_runner_manifest_path",
                    expected=lane.get("expected_runner_manifest_relpath"),
                    actual=lane.get("runner_manifest_relpath"),
                    **details,
                )
            )
            checks.append(
                _ok("phase3_lane_runner_manifest_sha256", **details)
                if lane.get("runner_manifest_sha256") == lane.get("manifest_sha256")
                else _failed(
                    "phase3_lane_runner_manifest_sha256",
                    expected=lane.get("manifest_sha256"),
                    actual=lane.get("runner_manifest_sha256"),
                    **details,
                )
            )
        if lane.get("require_runner_target_filter") is True:
            checks.append(
                _ok("phase3_lane_runner_target_category", **details)
                if lane.get("runner_target_category") == lane.get("expected_target_category")
                else _failed(
                    "phase3_lane_runner_target_category",
                    expected=lane.get("expected_target_category"),
                    actual=lane.get("runner_target_category"),
                    **details,
                )
            )
            checks.append(
                _ok("phase3_lane_runner_target_set", **details)
                if lane.get("runner_target_functions") == lane.get("expected_target_functions")
                else _failed(
                    "phase3_lane_runner_target_set",
                    expected=lane.get("expected_target_functions"),
                    actual=lane.get("runner_target_functions"),
                    **details,
                )
            )
            checks.append(
                _ok("phase3_lane_runner_pair_filter_var", **details)
                if lane.get("runner_pair_filter_var") == lane.get("expected_pair_filter_var")
                else _failed(
                    "phase3_lane_runner_pair_filter_var",
                    expected=lane.get("expected_pair_filter_var"),
                    actual=lane.get("runner_pair_filter_var"),
                    target_var=lane.get("runner_target_var"),
                    **details,
                )
            )
            checks.append(
                _ok("phase3_lane_runner_pair_filter", **details)
                if lane.get("runner_pair_filter") == lane.get("expected_pair_filter")
                else _failed(
                    "phase3_lane_runner_pair_filter",
                    expected=lane.get("expected_pair_filter"),
                    actual=lane.get("runner_pair_filter"),
                    **details,
                )
            )
            checks.append(
                _ok("phase3_lane_runner_base_path", **details)
                if lane.get("runner_base_path_relpath") == lane.get("expected_base_path_relpath")
                else _failed(
                    "phase3_lane_runner_base_path",
                    expected=lane.get("expected_base_path_relpath"),
                    actual=lane.get("runner_base_path_relpath"),
                    **details,
                )
            )
            checks.append(
                _ok("phase3_lane_runner_matrix_script", **details)
                if lane.get("runner_matrix_script_relpath") == lane.get("expected_matrix_script_relpath")
                else _failed(
                    "phase3_lane_runner_matrix_script",
                    expected=lane.get("expected_matrix_script_relpath"),
                    actual=lane.get("runner_matrix_script_relpath"),
                    **details,
                )
            )
        checks.append(
            _ok("phase3_lane_manifest_kind", **details)
            if lane.get("observed_manifest_kind") == lane.get("expected_manifest_kind")
            else _failed(
                "phase3_lane_manifest_kind",
                expected=lane.get("expected_manifest_kind"),
                actual=lane.get("observed_manifest_kind"),
                **details,
            )
        )
        checks.append(
            _ok("phase3_lane_ready", **details)
            if lane.get("ready_value") is True
            else _failed("phase3_lane_ready", ready_key=lane.get("ready_key"), actual=lane.get("ready_value"), **details)
        )
        checks.append(
            _ok("phase3_lane_validator", **details)
            if lane.get("validator_status") in {"passed", "not_run"}
            else _failed("phase3_lane_validator", error=lane.get("validator_error"), **details)
        )
        representative_entries = lane.get("representative_entries")
        checks.append(
            _ok(
                "phase3_lane_representative_entries_present",
                representative_count=len(representative_entries),
                **details,
            )
            if isinstance(representative_entries, list) and len(representative_entries) > 0
            else _failed(
                "phase3_lane_representative_entries_present",
                representative_count=0,
                **details,
            )
        )
        incomplete_representatives = [
            entry
            for entry in representative_entries
            if isinstance(entry, Mapping) and not _representative_entry_is_concrete(entry)
        ] if isinstance(representative_entries, list) else []
        checks.append(
            _ok("phase3_lane_representative_entries_concrete", **details)
            if not incomplete_representatives
            else _failed(
                "phase3_lane_representative_entries_concrete",
                incomplete=incomplete_representatives,
                **details,
            )
        )
        expected_reasons = tuple(lane.get("target_reason_ids") or ())
        observed_reasons = tuple(lane.get("observed_target_reason_ids") or ())
        checks.append(
            _ok("phase3_lane_target_reason_ids", **details)
            if observed_reasons == expected_reasons
            else _failed(
                "phase3_lane_target_reason_ids",
                expected=list(expected_reasons),
                actual=list(observed_reasons),
                **details,
            )
        )
        implementation = lane.get("implementation_manifest")
        checks.append(
            _ok("phase3_lane_implementation_manifest", **details)
            if isinstance(implementation, Mapping)
            else _failed("phase3_lane_implementation_manifest", **details)
        )
        implementation_lane_id = implementation.get("lane_id") if isinstance(implementation, Mapping) else None
        checks.append(
            _ok("phase3_lane_implementation_lane_id", **details)
            if implementation_lane_id == lane_id
            else _failed(
                "phase3_lane_implementation_lane_id",
                expected=lane_id,
                actual=implementation_lane_id or MISSING_SENTINEL,
                **details,
            )
        )
        implementation_reasons = (
            tuple(implementation.get("implementation_reason_ids") or ())
            if isinstance(implementation, Mapping)
            else ()
        )
        expected_lane_reasons = tuple(lane.get("lane_reason_ids") or expected_reasons)
        checks.append(
            _ok("phase3_lane_implementation_reason_ids", **details)
            if implementation_reasons == expected_lane_reasons
            else _failed(
                "phase3_lane_implementation_reason_ids",
                expected=list(expected_lane_reasons),
                actual=list(implementation_reasons),
                **details,
            )
        )
        expected_proof_gate = lane.get("expected_proof_completion_gate")
        if isinstance(expected_proof_gate, Mapping):
            observed_proof_gate = lane.get("proof_completion_gate")
            checks.append(
                _ok("phase3_lane_proof_completion_gate", **details)
                if observed_proof_gate == expected_proof_gate
                else _failed(
                    "phase3_lane_proof_completion_gate",
                    expected=expected_proof_gate,
                    actual=observed_proof_gate or MISSING_SENTINEL,
                    **details,
                )
            )
    return tuple(checks)


def _summary(checks: Sequence[Mapping[str, Any]]) -> Dict[str, Any]:
    failed = [
        check
        for check in checks
        if isinstance(check, Mapping) and check.get("status") == "failed"
    ]
    return {
        "total": len(checks),
        "failed": len(failed),
        "failed_kinds": [check.get("kind") for check in failed],
    }


def _implementation_reason_ids(implementation: Mapping[str, Any]) -> tuple[str, ...]:
    reasons: list[str] = []
    for key in ("target_reason_id", "active_target_reason_id"):
        value = implementation.get(key)
        if value:
            reasons.append(str(value))
    for value in implementation.get("lane_reason_ids") or ():
        if value:
            reasons.append(str(value))
    return tuple(dict.fromkeys(reasons))


def _representative_entries(entries: Any) -> list[Dict[str, Any]]:
    if not isinstance(entries, (list, tuple)):
        return []
    representatives: list[Dict[str, Any]] = []
    for index, entry in enumerate(entries):
        if not isinstance(entry, Mapping):
            representatives.append(
                {
                    "index": index,
                    "id": MISSING_SENTINEL,
                    "function": MISSING_SENTINEL,
                    "binary_pair": MISSING_SENTINEL,
                }
            )
            continue
        representatives.append(
            {
                "index": index,
                "id": entry.get("id") or MISSING_SENTINEL,
                "function": entry.get("function") or MISSING_SENTINEL,
                "binary_pair": entry.get("binary_pair") or MISSING_SENTINEL,
            }
        )
    return representatives


def _representative_entry_is_concrete(entry: Mapping[str, Any]) -> bool:
    return all(entry.get(key) not in {None, "", MISSING_SENTINEL} for key in ("id", "function", "binary_pair"))


def _runner_manifest_refs(runner_path: Path) -> Dict[str, str]:
    try:
        content = runner_path.read_text(encoding="utf-8")
    except OSError:
        return {
            "manifest_relpath": MISSING_SENTINEL,
            "manifest_sha256": MISSING_SENTINEL,
        }
    path_match = _RUNNER_MANIFEST_PATH_RE.search(content)
    sha_match = _RUNNER_MANIFEST_SHA_RE.search(content)
    return {
        "manifest_relpath": path_match.group("path") if path_match else MISSING_SENTINEL,
        "manifest_sha256": sha_match.group("sha") if sha_match else MISSING_SENTINEL,
    }


def _runner_target_filter(runner_path: Path) -> Dict[str, Any]:
    try:
        content = runner_path.read_text(encoding="utf-8")
    except OSError:
        return _empty_target_filter()
    target_match = _RUNNER_TARGET_SET_RE.search(content)
    pair_match = _RUNNER_PAIR_FILTER_RE.search(content)
    base_path_match = _RUNNER_BASE_PATH_RE.search(content)
    matrix_match = _RUNNER_MATRIX_SCRIPT_RE.search(content)
    category = MISSING_SENTINEL
    if target_match:
        category = "function_call" if target_match.group("var") == "FUNCTION_CALL_TARGET_SET" else "loop"
    return {
        "category": category,
        "target_var": target_match.group("var") if target_match else MISSING_SENTINEL,
        "pair_filter_var": pair_match.group("var") if pair_match else MISSING_SENTINEL,
        "base_path_relpath": base_path_match.group("path") if base_path_match else MISSING_SENTINEL,
        "matrix_script_relpath": matrix_match.group("path") if matrix_match else MISSING_SENTINEL,
        "target_functions": _split_csv(target_match.group("value") if target_match else None),
        "pair_filter": _split_csv(pair_match.group("value") if pair_match else None),
    }


def _manifest_target_filter(manifest: Mapping[str, Any]) -> Dict[str, Any]:
    targets: list[tuple[str, str, str]] = []
    for section in ("entries", "retired_transitions"):
        raw_entries = manifest.get(section)
        if not isinstance(raw_entries, (list, tuple)):
            continue
        for entry in raw_entries:
            if not isinstance(entry, Mapping):
                continue
            category = entry.get("category")
            function = entry.get("function")
            binary_pair = entry.get("binary_pair")
            if category and function and binary_pair:
                targets.append((str(category), str(function), str(binary_pair)))
    if not targets:
        return _empty_target_filter()
    categories = tuple(dict.fromkeys(category for category, _, _ in targets))
    category = categories[0] if len(categories) == 1 else MISSING_SENTINEL
    functions = list(dict.fromkeys(function for _, function, _ in targets))
    pair_filter = [f"{function}:{binary_pair}" for _, function, binary_pair in targets]
    return {
        "category": category,
        "pair_filter_var": _expected_pair_filter_var(category),
        "base_path_relpath": _expected_base_path_relpath(category),
        "matrix_script_relpath": _expected_matrix_script_relpath(category),
        "target_functions": functions,
        "pair_filter": pair_filter,
    }


def _empty_target_filter() -> Dict[str, Any]:
    return {
        "category": MISSING_SENTINEL,
        "target_var": MISSING_SENTINEL,
        "pair_filter_var": MISSING_SENTINEL,
        "base_path_relpath": MISSING_SENTINEL,
        "matrix_script_relpath": MISSING_SENTINEL,
        "target_functions": [],
        "pair_filter": [],
    }


def _expected_pair_filter_var(category: str) -> str:
    if category == "function_call":
        return "FUNCTION_CALL_PAIR_FILTER"
    if category == "loop":
        return "LOOP_PAIR_FILTER"
    return MISSING_SENTINEL


def _expected_base_path_relpath(category: str) -> str:
    if category == "function_call":
        return "targets/cate1/function_call_test"
    if category == "loop":
        return "targets/cate1/loop_method_b_test"
    return MISSING_SENTINEL


def _expected_matrix_script_relpath(category: str) -> str:
    if category == "function_call":
        return "func_call_run_matrix_all_parallel_multifunc.sh"
    if category == "loop":
        return "loop_run_matrix_all_parallel_multifunc.sh"
    return MISSING_SENTINEL


def _split_csv(value: Any) -> list[str]:
    if not value:
        return []
    return [part.strip() for part in str(value).split(",") if part.strip()]


def _lane_reason_ids(spec: Phase3LaneSpec) -> tuple[str, ...]:
    return tuple(spec.lane_reason_ids or spec.target_reason_ids)


def _expected_runner_manifest_relpath(spec: Phase3LaneSpec) -> str:
    return f"artifacts/baselines/{BASELINE_ID}/{spec.manifest_relpath}"


def _expected_proof_completion_gate(spec: Phase3LaneSpec) -> Optional[Dict[str, Any]]:
    if spec.pending_proof_keeps_final_result is None:
        return None
    return {
        "eq_allowed_without_completed_proof": False,
        "pending_proof_keeps_final_result": spec.pending_proof_keeps_final_result,
        "completion_required_for_recovery": list(spec.completion_required_for_recovery or ()),
        "required_recovery_actions": list(spec.required_recovery_actions or ()),
    }


def _materialize_proof_completion_gate(proof_gate: Mapping[str, Any]) -> Dict[str, Any]:
    return {
        "eq_allowed_without_completed_proof": proof_gate.get("eq_allowed_without_completed_proof", MISSING_SENTINEL),
        "pending_proof_keeps_final_result": proof_gate.get("pending_proof_keeps_final_result") or MISSING_SENTINEL,
        "completion_required_for_recovery": _string_list(proof_gate.get("completion_required_for_recovery")),
        "required_recovery_actions": _required_recovery_actions(proof_gate),
    }


def _required_recovery_actions(proof_gate: Mapping[str, Any]) -> list[str]:
    actions = proof_gate.get("required_recovery_actions")
    if actions is not None:
        return _string_list(actions)
    action = proof_gate.get("required_recovery_action")
    if action:
        return [str(action)]
    return []


def _string_list(value: Any) -> list[str]:
    if value is None:
        return []
    if isinstance(value, str):
        return [value]
    try:
        return [str(item) for item in value if item]
    except TypeError:
        return [str(value)]


def main(argv: Optional[Sequence[str]] = None) -> int:
    parser = argparse.ArgumentParser(description="Build the Phase 3 proof-lane index manifest.")
    parser.add_argument(
        "--baseline-root",
        type=Path,
        default=Path("artifacts/baselines/observed-v0@0a53352"),
        help="baseline artifact root containing raw/ and audit/",
    )
    parser.add_argument(
        "--repo-root",
        type=Path,
        default=Path.cwd(),
        help="repository root containing Phase 3 representative runner scripts",
    )
    parser.add_argument("--output-dir", type=Path, required=True)
    parser.add_argument("--require-ready", action="store_true")
    args = parser.parse_args(argv)

    path = build_phase3_lane_index(
        baseline_root=args.baseline_root,
        output_dir=args.output_dir,
        repo_root=args.repo_root,
    )
    print(path)
    if args.require_ready:
        validate_phase3_lane_index(_read_json(path))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
