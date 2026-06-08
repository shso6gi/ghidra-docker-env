# -*- coding: utf-8 -*-
"""Build a fixed index over Phase 3 proof-lane audit manifests."""

from __future__ import annotations

import argparse
import json
import os
import re
import subprocess
import sys
import tempfile
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
BASELINE_GIT_HEAD = "0a53352cf3c9528abfb654906ed7b963474bedc5"
MISSING_SENTINEL = "<missing>"
DYNAMIC_TARGET_FILTER_DESTINATION = "<dynamic_target_filter_destination>"
NON_TARGET_FILTER_DESTINATION = "<non_target_filter_destination>"
LaneValidator = Callable[[Mapping[str, Any]], None]
RUNNER_GATE_SMOKE_TIMEOUT_SECONDS = 30
_SHELL_QUOTED_SPACE = "\x1f"
_RUNNER_MANIFEST_PATH_RE = re.compile(
    r'^(?!\s*#)\s*PHASE3_MANIFEST_PATH="\$\{PHASE3_MANIFEST_PATH:-\$SCRIPT_DIR/(?P<path>[^"}]+)\}"',
    re.MULTILINE,
)
_RUNNER_MANIFEST_SHA_RE = re.compile(
    r'^(?!\s*#)\s*PHASE3_MANIFEST_SHA256="\$\{PHASE3_MANIFEST_SHA256:-(?P<sha>[0-9a-f]{64})\}"',
    re.MULTILINE,
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
_RUNNER_TARGET_FILTER_ASSIGNMENT_VARS = (
    "FUNCTION_CALL_TARGET_SET",
    "LOOP_TARGET_SET",
    "FUNCTION_CALL_PAIR_FILTER",
    "LOOP_PAIR_FILTER",
    "BASE_PATH",
)
_RUNNER_CURRENT_LOG_ROOT_ARG_RE = re.compile(
    r'^(?!\s*#)\s*--current-log-root\s+"(?P<value>[^"]*)"\s*$',
    re.MULTILINE,
)
_RUNNER_BASELINE_LOG_ROOT_ARG_RE = re.compile(
    r'^(?!\s*#)\s*--baseline-log-root\s+"(?P<value>[^"]*)"\s*$',
    re.MULTILINE,
)
_RUNNER_CURRENT_LOG_ROOT_RE = re.compile(
    r'^(?P<category>function_call|loop)=\$(?P<var>OUTPUT_BASE_DIR)$'
)
_RUNNER_BASELINE_LOG_ROOT_RE = re.compile(
    r'^(?P<category>function_call|loop)=\$(?P<var>BASELINE_FUNCTION_CALL_LOG_ROOT|BASELINE_LOOP_LOG_ROOT)$'
)
_RUNNER_DEFAULT_ENV_RE = re.compile(
    r'^(?!\s*#)\s*(?:export\s+)?(?P<var>'
    r'VALIDATION_AUTO_BEFORE_SNAPSHOT|'
    r'VALIDATION_REQUIRE_BEFORE_DELTA|'
    r'VALIDATION_REQUIRE_BASELINE_MATCH|'
    r'VALIDATION_SKIP_COMPLETED|'
    r'VALIDATION_REQUIRE_PHASE2_OBJECT_KEYS|'
    r'VALIDATION_RUNNER_DRY_RUN|'
    r'PHASE3_REQUIRE_READY'
    r')="\$\{(?P=var):-(?P<value>[^"}]+)\}"\s*$',
    re.MULTILINE,
)
EXPECTED_RUNNER_SAFETY_DEFAULTS: Mapping[str, str] = {
    "VALIDATION_AUTO_BEFORE_SNAPSHOT": "0",
    "VALIDATION_REQUIRE_BEFORE_DELTA": "0",
    "VALIDATION_REQUIRE_BASELINE_MATCH": "0",
    "VALIDATION_SKIP_COMPLETED": "0",
    "VALIDATION_REQUIRE_PHASE2_OBJECT_KEYS": "1",
    "VALIDATION_RUNNER_DRY_RUN": "0",
    "PHASE3_REQUIRE_READY": "1",
}
EXPECTED_RUNNER_GATE_ARGS: Mapping[str, str] = {
    "--gate-stage": "post-fix",
    "--baseline-raw-dir": "$BASELINE_RAW_DIR",
    "--output-dir": "$PHASE3_GATE_OUTPUT_DIR",
    "--phase3-manifest": "$PHASE3_MANIFEST_PATH",
    "--phase3-manifest-sha256": "$PHASE3_MANIFEST_SHA256",
}


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
    gate_validator_module: Optional[str] = None
    require_runner_manifest_ref: bool = False
    require_runner_target_filter: bool = False
    require_runner_safety_defaults: bool = False


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
        gate_validator_module="scripts.function_tracer_pcode.validation.phase3_return_coverage_lane1",
        require_runner_manifest_ref=True,
        require_runner_target_filter=True,
        require_runner_safety_defaults=True,
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
        gate_validator_module="scripts.function_tracer_pcode.validation.phase3_return_width_bridge_lane2",
        require_runner_manifest_ref=True,
        require_runner_target_filter=True,
        require_runner_safety_defaults=True,
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
        gate_validator_module="scripts.function_tracer_pcode.validation.phase3_readonly_identity_lane3",
        require_runner_manifest_ref=True,
        require_runner_target_filter=True,
        require_runner_safety_defaults=True,
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
        gate_validator_module="scripts.function_tracer_pcode.validation.phase3_method_b_closure_lane4",
        require_runner_manifest_ref=True,
        require_runner_target_filter=True,
        require_runner_safety_defaults=True,
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
        gate_validator_module="scripts.function_tracer_pcode.validation.phase3_sat_unsafety_lane5",
        require_runner_manifest_ref=True,
        require_runner_target_filter=True,
        require_runner_safety_defaults=True,
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
        gate_validator_module="scripts.function_tracer_pcode.validation.phase3_unresolved_expression_lane6",
        require_runner_manifest_ref=True,
        require_runner_target_filter=True,
        require_runner_safety_defaults=True,
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
        gate_validator_module="scripts.function_tracer_pcode.validation.phase3_solver_rewrite_lane7",
        require_runner_manifest_ref=True,
        require_runner_target_filter=True,
        require_runner_safety_defaults=True,
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
        gate_validator_module="scripts.function_tracer_pcode.validation.phase3_solver_rewrite_proof_lane8",
        require_runner_manifest_ref=True,
        require_runner_target_filter=True,
        require_runner_safety_defaults=True,
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
        gate_validator_module="scripts.function_tracer_pcode.validation.phase3_solver_timeout_lane9",
        require_runner_manifest_ref=True,
        require_runner_target_filter=True,
        require_runner_safety_defaults=True,
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


def validate_phase3_lane_index(
    manifest: Mapping[str, Any],
    *,
    lane_specs: Optional[Sequence[Phase3LaneSpec]] = None,
) -> None:
    failures: list[str] = []
    if manifest.get("manifest_kind") != "phase3_proof_lane_index":
        failures.append("manifest_kind")
    if manifest.get("manifest_version") != MANIFEST_VERSION:
        failures.append("manifest_version")
    if manifest.get("artifact_role") != "derived_audit_lane_index":
        failures.append("artifact_role")
    if manifest.get("baseline_id") != BASELINE_ID:
        failures.append("baseline_id")
    if manifest.get("baseline_git_head") != BASELINE_GIT_HEAD:
        failures.append("baseline_git_head")

    summary = manifest.get("summary")
    failed = summary.get("failed_kinds") if isinstance(summary, Mapping) else None
    failed_kinds = list(failed or ()) if isinstance(failed, (list, tuple)) else []
    summary_failed = summary.get("failed") if isinstance(summary, Mapping) else MISSING_SENTINEL
    if not isinstance(summary, Mapping):
        failures.append("summary")
    elif not isinstance(summary_failed, int) or isinstance(summary_failed, bool):
        failures.append("summary_failed_count")

    checks = manifest.get("checks")
    failed_check_kinds: list[str] = []
    if not isinstance(checks, (list, tuple)):
        failures.append("checks")
    else:
        failed_check_kinds = _failed_check_kinds(checks)
        if isinstance(summary_failed, int) and summary_failed != len(failed_check_kinds):
            failures.append("summary_failed_count")
        if failed_kinds != failed_check_kinds:
            failures.append("summary_failed_kinds")
        computed_summary = _summary(checks)
        if isinstance(summary, Mapping) and not _strict_json_equal(dict(summary), computed_summary):
            failures.append("summary_consistency")

    lanes = manifest.get("lanes")
    if not isinstance(lanes, (list, tuple)):
        failures.append("lanes")
    else:
        specs = tuple(lane_specs or DEFAULT_PHASE3_LANE_SPECS)
        actual_lane_rows = _lane_spec_rows_from_lanes(lanes)
        expected_lane_rows = _lane_spec_rows_from_specs(specs)
        if actual_lane_rows != expected_lane_rows:
            failures.append("lane_specs")
        derived_checks = _index_checks(
            {
                "baseline_id": manifest.get("baseline_id"),
                "git_head": manifest.get("baseline_git_head"),
            },
            specs,
            lanes,
        )
        if isinstance(checks, (list, tuple)) and not _strict_json_equal(list(checks), list(derived_checks)):
            failures.append("derived_checks")
        if failed_check_kinds != _failed_check_kinds(derived_checks):
            failures.append("derived_failed_kinds")
        materialized_context = _materialized_lane_context(manifest)
        if materialized_context is None:
            failures.append("materialized_context_missing")
        else:
            materialized_lanes = [
                _materialize_lane(materialized_context["baseline_root"], materialized_context["repo_root"], spec)
                for spec in specs
            ]
            materialized_checks = _index_checks(
                {
                    "baseline_id": manifest.get("baseline_id"),
                    "git_head": manifest.get("baseline_git_head"),
                },
                specs,
                materialized_lanes,
            )
            if not _strict_json_equal(list(lanes), materialized_lanes):
                failures.append("materialized_lanes")
            if isinstance(checks, (list, tuple)) and not _strict_json_equal(list(checks), list(materialized_checks)):
                failures.append("materialized_checks")
            if failed_check_kinds != _failed_check_kinds(materialized_checks):
                failures.append("materialized_failed_kinds")

    ready = manifest.get("phase3_lanes_ready")
    if ready is True:
        if summary_failed != 0 or failed_kinds:
            failures.append("phase3_lanes_ready_summary_clean")
        if failed_check_kinds:
            failures.append("phase3_lanes_ready_checks_clean")
    elif ready is False:
        if not failed_kinds:
            failures.append("phase3_lanes_ready_failure_kinds")
        else:
            failures.extend(str(kind) for kind in failed_kinds)
    else:
        failures.append("phase3_lanes_ready")

    if not failures:
        return
    raise ValueError(f"Phase 3 lane index failed: {', '.join(dict.fromkeys(failures))}")


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
        "require_runner_safety_defaults": spec.require_runner_safety_defaults,
        "expected_runner_manifest_relpath": _expected_runner_manifest_relpath(spec),
        "manifest_ref": _file_ref(path),
        "manifest_relpath": spec.manifest_relpath,
        "runner_ref": _file_ref(runner_path),
        "runner_relpath": spec.runner_relpath,
        "expected_manifest_kind": spec.manifest_kind,
        "ready_key": spec.ready_key,
        "status": "missing",
        "observed_manifest_version": MISSING_SENTINEL,
        "observed_artifact_role": MISSING_SENTINEL,
        "lane_baseline_id": MISSING_SENTINEL,
        "lane_baseline_git_head": MISSING_SENTINEL,
        "lane_baseline_raw_artifact_ref": {},
        "expected_lane_baseline_raw_artifact_ref": _file_ref(root / "raw" / "artifact_manifest.json"),
        "manifest_sha256": MISSING_SENTINEL,
        "observed_manifest_kind": MISSING_SENTINEL,
        "ready_value": MISSING_SENTINEL,
        "manifest_readiness_ready": MISSING_SENTINEL,
        "manifest_readiness_summary": {},
        "manifest_readiness_failure_kinds": [],
        "manifest_readiness_failure_counts": {},
        "manifest_readiness_ready_entries": MISSING_SENTINEL,
        "manifest_readiness_failed_entries": MISSING_SENTINEL,
        "validator_status": "not_run",
        "validator_failure_kinds": [],
        "validator_failure_counts": {},
        "runner_status": "missing",
        "runner_sha256": MISSING_SENTINEL,
        "runner_executable": False,
        "runner_shebang": MISSING_SENTINEL,
        "runner_strict_mode_present": False,
        "runner_strict_mode_before_first_command": False,
        "runner_manifest_relpath": MISSING_SENTINEL,
        "runner_manifest_sha256": MISSING_SENTINEL,
        "runner_target_category": MISSING_SENTINEL,
        "runner_target_var": MISSING_SENTINEL,
        "runner_pair_filter_var": MISSING_SENTINEL,
        "runner_base_path_relpath": MISSING_SENTINEL,
        "runner_matrix_script_relpath": MISSING_SENTINEL,
        "runner_current_log_root_category": MISSING_SENTINEL,
        "runner_current_log_root_var": MISSING_SENTINEL,
        "runner_baseline_log_root_category": MISSING_SENTINEL,
        "runner_baseline_log_root_var": MISSING_SENTINEL,
        "runner_target_filter_counts": {},
        "runner_target_filter_invalid_mutations": [],
        "runner_target_filter_invalid_mutation_count": 0,
        "runner_target_filter_runtime_status": "not_run",
        "runner_target_filter_runtime_invocation_count": 0,
        "runner_target_filter_runtime_contract_matches_expected": False,
        "runner_target_filter_runtime_error": MISSING_SENTINEL,
        "runner_target_filter_runtime_failure_kind": MISSING_SENTINEL,
        "runner_target_filter_runtime_returncode": MISSING_SENTINEL,
        "runner_target_filter_runtime_expected_contract": {},
        "runner_target_filter_runtime_observed_contract": {},
        "runner_target_filter_runtime_observed_invocations": [],
        "runner_target_filter_runtime_contract_diff": [],
        "runner_log_root_arg_counts": {},
        "runner_safety_defaults": {},
        "runner_safety_duplicate_vars": [],
        "runner_require_ready_arg_present": False,
        "runner_gate_args_invoked": False,
        "runner_gate_validator_module": MISSING_SENTINEL,
        "runner_gate_validator_invocation_count": 0,
        "runner_required_gate_args": {
            flag: MISSING_SENTINEL
            for flag in EXPECTED_RUNNER_GATE_ARGS
        },
        "runner_required_gate_arg_counts": {
            flag: 0
            for flag in EXPECTED_RUNNER_GATE_ARGS
        },
        "runner_required_gate_args_missing": list(EXPECTED_RUNNER_GATE_ARGS),
        "runner_required_gate_args_duplicate": [],
        "runner_required_gate_args_value_mismatch": [],
        "runner_gate_args_unknown_args": [],
        "runner_gate_args_invalid_optional_args": [],
        "runner_gate_args_assignment_count": 0,
        "runner_gate_args_invalid_mutations": [],
        "runner_gate_args_invalid_mutation_count": 0,
        "runner_gate_smoke_status": "not_run",
        "runner_gate_smoke_validator_invocation_count": 0,
        "runner_gate_smoke_argv_matches_expected": False,
        "runner_gate_smoke_error": MISSING_SENTINEL,
        "runner_gate_smoke_failure_kind": MISSING_SENTINEL,
        "runner_gate_smoke_returncode": MISSING_SENTINEL,
        "runner_gate_smoke_expected_argv": [],
        "runner_gate_smoke_observed_argv": [],
        "runner_gate_smoke_observed_invocations": [],
        "runner_gate_smoke_argv_diff": [],
        "runner_target_functions": [],
        "runner_pair_filter": [],
        "representative_entry_duplicate_ids": [],
        "expected_target_category": MISSING_SENTINEL,
        "expected_pair_filter_var": MISSING_SENTINEL,
        "expected_base_path_relpath": MISSING_SENTINEL,
        "expected_matrix_script_relpath": MISSING_SENTINEL,
        "expected_current_log_root_category": MISSING_SENTINEL,
        "expected_current_log_root_var": MISSING_SENTINEL,
        "expected_baseline_log_root_category": MISSING_SENTINEL,
        "expected_baseline_log_root_var": MISSING_SENTINEL,
        "expected_gate_validator_module": spec.gate_validator_module or MISSING_SENTINEL,
        "expected_runner_safety_defaults": dict(EXPECTED_RUNNER_SAFETY_DEFAULTS),
        "expected_runner_gate_args": dict(EXPECTED_RUNNER_GATE_ARGS),
        "expected_target_functions": [],
        "expected_pair_filter": [],
    }
    if runner_path.exists():
        lane["runner_status"] = "present" if runner_path.is_file() else "not_file"
        if runner_path.is_file():
            lane["runner_sha256"] = _sha256_file(runner_path)
            lane["runner_executable"] = os.access(runner_path, os.X_OK)
            runner_shell = _runner_shell_contract(runner_path)
            lane["runner_shebang"] = runner_shell["shebang"]
            lane["runner_strict_mode_present"] = runner_shell["strict_mode_present"]
            lane["runner_strict_mode_before_first_command"] = runner_shell[
                "strict_mode_before_first_command"
            ]
            runner_refs = _runner_manifest_refs(runner_path)
            lane["runner_manifest_relpath"] = runner_refs["manifest_relpath"]
            lane["runner_manifest_sha256"] = runner_refs["manifest_sha256"]
            runner_targets = _runner_target_filter(runner_path)
            lane["runner_target_category"] = runner_targets["category"]
            lane["runner_target_var"] = runner_targets["target_var"]
            lane["runner_pair_filter_var"] = runner_targets["pair_filter_var"]
            lane["runner_base_path_relpath"] = runner_targets["base_path_relpath"]
            lane["runner_matrix_script_relpath"] = runner_targets["matrix_script_relpath"]
            lane["runner_current_log_root_category"] = runner_targets["current_log_root_category"]
            lane["runner_current_log_root_var"] = runner_targets["current_log_root_var"]
            lane["runner_baseline_log_root_category"] = runner_targets["baseline_log_root_category"]
            lane["runner_baseline_log_root_var"] = runner_targets["baseline_log_root_var"]
            lane["runner_target_filter_counts"] = runner_targets["target_filter_counts"]
            lane["runner_target_filter_invalid_mutations"] = runner_targets[
                "target_filter_invalid_mutations"
            ]
            lane["runner_target_filter_invalid_mutation_count"] = runner_targets[
                "target_filter_invalid_mutation_count"
            ]
            lane["runner_log_root_arg_counts"] = runner_targets["log_root_arg_counts"]
            runner_safety = _runner_safety_defaults(runner_path)
            lane["runner_safety_defaults"] = runner_safety["defaults"]
            lane["runner_safety_duplicate_vars"] = runner_safety["duplicate_vars"]
            lane["runner_require_ready_arg_present"] = runner_safety["require_ready_arg_present"]
            lane["runner_gate_args_invoked"] = runner_safety["gate_args_invoked"]
            lane["runner_gate_validator_module"] = runner_safety["gate_validator_module"]
            lane["runner_gate_validator_invocation_count"] = runner_safety["gate_validator_invocation_count"]
            lane["runner_required_gate_args"] = runner_safety["required_gate_args"]
            lane["runner_required_gate_arg_counts"] = runner_safety["required_gate_arg_counts"]
            lane["runner_required_gate_args_missing"] = runner_safety["required_gate_args_missing"]
            lane["runner_required_gate_args_duplicate"] = runner_safety["required_gate_args_duplicate"]
            lane["runner_required_gate_args_value_mismatch"] = runner_safety[
                "required_gate_args_value_mismatch"
            ]
            lane["runner_gate_args_unknown_args"] = runner_safety["gate_args_unknown_args"]
            lane["runner_gate_args_invalid_optional_args"] = runner_safety[
                "gate_args_invalid_optional_args"
            ]
            lane["runner_gate_args_assignment_count"] = runner_safety["gate_args_assignment_count"]
            lane["runner_gate_args_invalid_mutations"] = runner_safety["gate_args_invalid_mutations"]
            lane["runner_gate_args_invalid_mutation_count"] = runner_safety["gate_args_invalid_mutation_count"]
            lane["runner_gate_smoke_status"] = runner_safety["gate_smoke_status"]
            lane["runner_gate_smoke_validator_invocation_count"] = runner_safety[
                "gate_smoke_validator_invocation_count"
            ]
            lane["runner_gate_smoke_argv_matches_expected"] = runner_safety[
                "gate_smoke_argv_matches_expected"
            ]
            lane["runner_gate_smoke_error"] = runner_safety["gate_smoke_error"]
            lane["runner_gate_smoke_failure_kind"] = runner_safety["gate_smoke_failure_kind"]
            lane["runner_gate_smoke_returncode"] = runner_safety["gate_smoke_returncode"]
            lane["runner_gate_smoke_expected_argv"] = runner_safety["gate_smoke_expected_argv"]
            lane["runner_gate_smoke_observed_argv"] = runner_safety["gate_smoke_observed_argv"]
            lane["runner_gate_smoke_observed_invocations"] = runner_safety[
                "gate_smoke_observed_invocations"
            ]
            lane["runner_gate_smoke_argv_diff"] = runner_safety["gate_smoke_argv_diff"]
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
    lane["observed_manifest_version"] = manifest.get("manifest_version", MISSING_SENTINEL)
    lane["observed_manifest_kind"] = manifest.get("manifest_kind") or MISSING_SENTINEL
    lane["observed_artifact_role"] = manifest.get("artifact_role") or MISSING_SENTINEL
    lane["lane_baseline_id"] = manifest.get("baseline_id") or MISSING_SENTINEL
    lane["lane_baseline_git_head"] = manifest.get("baseline_git_head") or MISSING_SENTINEL
    lane["lane_baseline_raw_artifact_ref"] = (
        dict(manifest.get("baseline_raw_artifact_ref"))
        if isinstance(manifest.get("baseline_raw_artifact_ref"), Mapping)
        else {}
    )
    lane["ready_value"] = manifest.get(spec.ready_key, MISSING_SENTINEL)
    manifest_readiness = _manifest_readiness(manifest)
    lane["manifest_readiness_ready"] = manifest_readiness["ready"]
    lane["manifest_readiness_summary"] = manifest_readiness["summary"]
    lane["manifest_readiness_failure_kinds"] = manifest_readiness["failure_kinds"]
    lane["manifest_readiness_failure_counts"] = manifest_readiness["failure_counts"]
    lane["manifest_readiness_ready_entries"] = manifest_readiness["ready_entries"]
    lane["manifest_readiness_failed_entries"] = manifest_readiness["failed_entries"]
    lane["observed_target_reason_ids"] = list(manifest.get("target_reason_ids") or ())
    expected_targets = _manifest_target_filter(manifest)
    lane["expected_target_category"] = expected_targets["category"]
    lane["expected_target_var"] = expected_targets["target_var"]
    lane["expected_pair_filter_var"] = expected_targets["pair_filter_var"]
    lane["expected_base_path_relpath"] = expected_targets["base_path_relpath"]
    lane["expected_matrix_script_relpath"] = expected_targets["matrix_script_relpath"]
    lane["expected_current_log_root_category"] = expected_targets["current_log_root_category"]
    lane["expected_current_log_root_var"] = expected_targets["current_log_root_var"]
    lane["expected_baseline_log_root_category"] = expected_targets["baseline_log_root_category"]
    lane["expected_baseline_log_root_var"] = expected_targets["baseline_log_root_var"]
    lane["expected_target_functions"] = expected_targets["target_functions"]
    lane["expected_pair_filter"] = expected_targets["pair_filter"]
    if runner_path.is_file() and spec.require_runner_target_filter:
        runtime_contract = _runner_target_filter_runtime_contract(
            runner_path,
            expected_targets,
            manifest_path=path,
            manifest_sha256=lane["manifest_sha256"],
            require_safety_defaults=spec.require_runner_safety_defaults,
        )
        lane["runner_target_filter_runtime_status"] = runtime_contract["status"]
        lane["runner_target_filter_runtime_invocation_count"] = runtime_contract["invocation_count"]
        lane["runner_target_filter_runtime_contract_matches_expected"] = runtime_contract[
            "contract_matches_expected"
        ]
        lane["runner_target_filter_runtime_error"] = runtime_contract["error"] or MISSING_SENTINEL
        lane["runner_target_filter_runtime_failure_kind"] = runtime_contract["failure_kind"]
        lane["runner_target_filter_runtime_returncode"] = runtime_contract["returncode"]
        lane["runner_target_filter_runtime_expected_contract"] = runtime_contract["expected_contract"]
        lane["runner_target_filter_runtime_observed_contract"] = runtime_contract["observed_contract"]
        lane["runner_target_filter_runtime_observed_invocations"] = runtime_contract[
            "observed_invocations"
        ]
        lane["runner_target_filter_runtime_contract_diff"] = runtime_contract["contract_diff"]
        lane["runner_target_filter_runtime_contract_consistent"] = (
            _runner_target_runtime_contract_consistency(lane)["ok"]
        )
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
            lane["validator_failure_kinds"] = lane["manifest_readiness_failure_kinds"]
            lane["validator_failure_counts"] = lane["manifest_readiness_failure_counts"]
        else:
            lane["validator_status"] = "passed"
    lane["representative_entry_duplicate_ids"] = _duplicate_representative_ids(
        lane["representative_entries"]
    )
    return lane


def _index_checks(
    baseline_manifest: Mapping[str, Any],
    specs: Sequence[Phase3LaneSpec],
    lanes: Sequence[Any],
) -> Sequence[Dict[str, Any]]:
    checks: list[Dict[str, Any]] = []
    checks.append(
        _ok("baseline_id")
        if baseline_manifest.get("baseline_id") == BASELINE_ID
        else _failed("baseline_id", expected=BASELINE_ID, actual=baseline_manifest.get("baseline_id"))
    )
    baseline_git_head = baseline_manifest.get("git_head") or MISSING_SENTINEL
    checks.append(
        _ok("baseline_git_head")
        if baseline_git_head == BASELINE_GIT_HEAD
        else _failed(
            "baseline_git_head",
            expected=BASELINE_GIT_HEAD,
            actual=baseline_git_head,
        )
    )
    lane_numbers = [spec.lane_number for spec in specs]
    expected_lane_numbers = list(range(1, len(specs) + 1))
    checks.append(
        _ok("phase3_lane_order")
        if lane_numbers == expected_lane_numbers
        else _failed("phase3_lane_order", expected=expected_lane_numbers, actual=lane_numbers)
    )
    expected_lane_rows = _lane_spec_rows_from_specs(specs)
    actual_lane_rows = _lane_spec_rows_from_lanes(lanes)
    checks.append(
        _ok("phase3_lane_count")
        if len(actual_lane_rows) == len(expected_lane_rows)
        else _failed("phase3_lane_count", expected=len(expected_lane_rows), actual=len(actual_lane_rows))
    )
    checks.append(
        _ok("phase3_lane_spec_order")
        if actual_lane_rows == expected_lane_rows
        else _failed("phase3_lane_spec_order", expected=expected_lane_rows, actual=actual_lane_rows)
    )
    seen = set()
    for lane_index, lane in enumerate(lanes):
        if not isinstance(lane, Mapping):
            checks.append(
                _failed(
                    "phase3_lane_entry_mapping",
                    lane_index=lane_index,
                    actual_type=type(lane).__name__,
                )
            )
            continue
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
            expected_target_filter_complete = (
                lane.get("expected_target_category") in {"function_call", "loop"}
                and bool(lane.get("expected_target_functions"))
                and bool(lane.get("expected_pair_filter"))
            )
            checks.append(
                _ok("phase3_lane_runner_target_filter_gate_policy", **details)
                if lane.get("require_runner_safety_defaults") is True
                else _failed(
                    "phase3_lane_runner_target_filter_gate_policy",
                    require_runner_target_filter=lane.get("require_runner_target_filter"),
                    require_runner_safety_defaults=lane.get("require_runner_safety_defaults"),
                    policy="target-filter lanes must also require runner safety defaults and gate smoke",
                    **details,
                )
            )
            checks.append(
                _ok("phase3_lane_manifest_target_filter_complete", **details)
                if expected_target_filter_complete
                else _failed(
                    "phase3_lane_manifest_target_filter_complete",
                    expected_category=lane.get("expected_target_category"),
                    expected_functions=lane.get("expected_target_functions"),
                    expected_pair_filter=lane.get("expected_pair_filter"),
                    **details,
                )
            )
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
            target_filter_counts = lane.get("runner_target_filter_counts")
            checks.append(
                _ok("phase3_lane_runner_target_filter_unique", **details)
                if isinstance(target_filter_counts, Mapping)
                and target_filter_counts.get("target_set") == 1
                and target_filter_counts.get("pair_filter") == 1
                and target_filter_counts.get("base_path") == 1
                and target_filter_counts.get("matrix_script") == 1
                else _failed(
                    "phase3_lane_runner_target_filter_unique",
                    actual=target_filter_counts or {},
                    **details,
                )
            )
            checks.append(
                _ok("phase3_lane_runner_target_filter_immutable", **details)
                if lane.get("runner_target_filter_invalid_mutation_count") == 0
                else _failed(
                    "phase3_lane_runner_target_filter_immutable",
                    actual=target_filter_counts or {},
                    invalid_mutation_count=lane.get("runner_target_filter_invalid_mutation_count"),
                    invalid_mutations=lane.get("runner_target_filter_invalid_mutations"),
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
            log_root_counts = lane.get("runner_log_root_arg_counts")
            checks.append(
                _ok("phase3_lane_runner_log_root_args_unique", **details)
                if isinstance(log_root_counts, Mapping)
                and log_root_counts.get("current_log_root") == 1
                and log_root_counts.get("baseline_log_root") == 1
                else _failed(
                    "phase3_lane_runner_log_root_args_unique",
                    actual=log_root_counts or {},
                    **details,
                )
            )
            expected_current_log_root = {
                "category": lane.get("expected_current_log_root_category"),
                "var": lane.get("expected_current_log_root_var"),
            }
            actual_current_log_root = {
                "category": lane.get("runner_current_log_root_category"),
                "var": lane.get("runner_current_log_root_var"),
            }
            checks.append(
                _ok("phase3_lane_runner_current_log_root", **details)
                if actual_current_log_root == expected_current_log_root
                else _failed(
                    "phase3_lane_runner_current_log_root",
                    expected=expected_current_log_root,
                    actual=actual_current_log_root,
                    **details,
                )
            )
            expected_baseline_log_root = {
                "category": lane.get("expected_baseline_log_root_category"),
                "var": lane.get("expected_baseline_log_root_var"),
            }
            actual_baseline_log_root = {
                "category": lane.get("runner_baseline_log_root_category"),
                "var": lane.get("runner_baseline_log_root_var"),
            }
            checks.append(
                _ok("phase3_lane_runner_baseline_log_root", **details)
                if actual_baseline_log_root == expected_baseline_log_root
                else _failed(
                    "phase3_lane_runner_baseline_log_root",
                    expected=expected_baseline_log_root,
                    actual=actual_baseline_log_root,
                    **details,
                )
            )
            checks.append(
                _ok("phase3_lane_runner_target_filter_runtime_contract_consistent", **details)
                if lane.get("runner_target_filter_runtime_contract_consistent") is True
                and _runner_target_runtime_contract_consistency(lane)["ok"] is True
                else _failed(
                    "phase3_lane_runner_target_filter_runtime_contract_consistent",
                    stored_consistent=lane.get(
                        "runner_target_filter_runtime_contract_consistent"
                    ),
                    consistency=_runner_target_runtime_contract_consistency(lane),
                    **details,
                )
            )
            runtime_contract_consistency = _runner_target_runtime_contract_consistency(lane)
            checks.append(
                _ok("phase3_lane_runner_target_filter_runtime_contract", **details)
                if lane.get("runner_target_filter_runtime_status") == "passed"
                and lane.get("runner_target_filter_runtime_invocation_count") == 1
                and lane.get("runner_target_filter_runtime_contract_matches_expected") is True
                and lane.get("runner_target_filter_runtime_failure_kind") == "none"
                and lane.get("runner_target_filter_runtime_returncode") == 0
                and runtime_contract_consistency["ok"] is True
                and runtime_contract_consistency["expected_equals_observed"] is True
                else _failed(
                    "phase3_lane_runner_target_filter_runtime_contract",
                    smoke_status=lane.get("runner_target_filter_runtime_status"),
                    invocation_count=lane.get("runner_target_filter_runtime_invocation_count"),
                    contract_matches_expected=lane.get(
                        "runner_target_filter_runtime_contract_matches_expected"
                    ),
                    error=lane.get("runner_target_filter_runtime_error"),
                    failure_kind=lane.get("runner_target_filter_runtime_failure_kind"),
                    returncode=lane.get("runner_target_filter_runtime_returncode"),
                    expected_contract=lane.get(
                        "runner_target_filter_runtime_expected_contract"
                    ),
                    observed_contract=lane.get(
                        "runner_target_filter_runtime_observed_contract"
                    ),
                    observed_invocations=lane.get(
                        "runner_target_filter_runtime_observed_invocations"
                    ),
                    contract_diff=lane.get("runner_target_filter_runtime_contract_diff"),
                    consistency=runtime_contract_consistency,
                    **details,
                )
            )
        if lane.get("require_runner_safety_defaults") is True:
            checks.append(
                _ok("phase3_lane_runner_shell_contract", **details)
                if lane.get("runner_shebang") == "#!/usr/bin/env bash"
                and lane.get("runner_strict_mode_present") is True
                and lane.get("runner_strict_mode_before_first_command") is True
                else _failed(
                    "phase3_lane_runner_shell_contract",
                    shebang=lane.get("runner_shebang"),
                    strict_mode_present=lane.get("runner_strict_mode_present"),
                    strict_mode_before_first_command=lane.get("runner_strict_mode_before_first_command"),
                    **details,
                )
            )
            checks.append(
                _ok("phase3_lane_runner_safety_defaults_unique", **details)
                if not lane.get("runner_safety_duplicate_vars")
                else _failed(
                    "phase3_lane_runner_safety_defaults_unique",
                    duplicate_vars=lane.get("runner_safety_duplicate_vars"),
                    **details,
                )
            )
            checks.append(
                _ok("phase3_lane_runner_safety_defaults", **details)
                if lane.get("runner_safety_defaults") == lane.get("expected_runner_safety_defaults")
                else _failed(
                    "phase3_lane_runner_safety_defaults",
                    expected=lane.get("expected_runner_safety_defaults"),
                    actual=lane.get("runner_safety_defaults"),
                    **details,
                )
            )
            checks.append(
                _ok("phase3_lane_runner_require_ready_arg", **details)
                if lane.get("runner_require_ready_arg_present") is True
                else _failed(
                    "phase3_lane_runner_require_ready_arg",
                    actual=lane.get("runner_require_ready_arg_present"),
                    **details,
                )
            )
            checks.append(
                _ok("phase3_lane_runner_gate_args_invoked", **details)
                if lane.get("runner_gate_args_invoked") is True
                else _failed(
                    "phase3_lane_runner_gate_args_invoked",
                    actual=lane.get("runner_gate_args_invoked"),
                    invocation_count=lane.get("runner_gate_validator_invocation_count"),
                    **details,
                )
            )
            if lane.get("expected_gate_validator_module") != MISSING_SENTINEL:
                checks.append(
                    _ok("phase3_lane_runner_gate_validator_module", **details)
                    if lane.get("runner_gate_validator_module") == lane.get("expected_gate_validator_module")
                    else _failed(
                        "phase3_lane_runner_gate_validator_module",
                        expected=lane.get("expected_gate_validator_module"),
                        actual=lane.get("runner_gate_validator_module"),
                        invocation_count=lane.get("runner_gate_validator_invocation_count"),
                        **details,
                    )
                )
            required_gate_arg_counts = lane.get("runner_required_gate_arg_counts")
            checks.append(
                _ok("phase3_lane_runner_required_gate_args", **details)
                if lane.get("runner_required_gate_args") == lane.get("expected_runner_gate_args")
                and isinstance(required_gate_arg_counts, Mapping)
                and all(required_gate_arg_counts.get(flag) == 1 for flag in EXPECTED_RUNNER_GATE_ARGS)
                and lane.get("runner_gate_args_assignment_count") == 1
                else _failed(
                    "phase3_lane_runner_required_gate_args",
                    expected=lane.get("expected_runner_gate_args"),
                    actual=lane.get("runner_required_gate_args"),
                    counts=required_gate_arg_counts or {},
                    missing=lane.get("runner_required_gate_args_missing"),
                    duplicate=lane.get("runner_required_gate_args_duplicate"),
                    value_mismatch=lane.get("runner_required_gate_args_value_mismatch"),
                    unknown_args=lane.get("runner_gate_args_unknown_args"),
                    invalid_optional_args=lane.get("runner_gate_args_invalid_optional_args"),
                    assignment_count=lane.get("runner_gate_args_assignment_count"),
                    **details,
                )
            )
            checks.append(
                _ok("phase3_lane_runner_gate_args_immutable", **details)
                if lane.get("runner_gate_args_invalid_mutation_count") == 0
                else _failed(
                    "phase3_lane_runner_gate_args_immutable",
                    invalid_mutations=lane.get("runner_gate_args_invalid_mutations"),
                    invalid_mutation_count=lane.get("runner_gate_args_invalid_mutation_count"),
                    **details,
                )
            )
            checks.append(
                _ok("phase3_lane_runner_gate_smoke", **details)
                if lane.get("runner_gate_smoke_status") == "passed"
                and lane.get("runner_gate_smoke_validator_invocation_count") == 1
                and lane.get("runner_gate_smoke_argv_matches_expected") is True
                and lane.get("runner_gate_smoke_failure_kind") == "none"
                and lane.get("runner_gate_smoke_returncode") == 0
                else _failed(
                    "phase3_lane_runner_gate_smoke",
                    smoke_status=lane.get("runner_gate_smoke_status"),
                    invocation_count=lane.get("runner_gate_smoke_validator_invocation_count"),
                    argv_matches_expected=lane.get("runner_gate_smoke_argv_matches_expected"),
                    error=lane.get("runner_gate_smoke_error"),
                    failure_kind=lane.get("runner_gate_smoke_failure_kind"),
                    returncode=lane.get("runner_gate_smoke_returncode"),
                    expected_argv=lane.get("runner_gate_smoke_expected_argv"),
                    observed_argv=lane.get("runner_gate_smoke_observed_argv"),
                    observed_invocations=lane.get("runner_gate_smoke_observed_invocations"),
                    argv_diff=lane.get("runner_gate_smoke_argv_diff"),
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
            _ok("phase3_lane_manifest_version", **details)
            if lane.get("observed_manifest_version") == MANIFEST_VERSION
            else _failed(
                "phase3_lane_manifest_version",
                expected=MANIFEST_VERSION,
                actual=lane.get("observed_manifest_version"),
                **details,
            )
        )
        checks.append(
            _ok("phase3_lane_artifact_role_present", **details)
            if lane.get("observed_artifact_role") not in {None, "", MISSING_SENTINEL}
            else _failed(
                "phase3_lane_artifact_role_present",
                actual=lane.get("observed_artifact_role"),
                **details,
            )
        )
        checks.append(
            _ok("phase3_lane_baseline_id", **details)
            if lane.get("lane_baseline_id") == BASELINE_ID
            else _failed(
                "phase3_lane_baseline_id",
                expected=BASELINE_ID,
                actual=lane.get("lane_baseline_id"),
                **details,
            )
        )
        checks.append(
            _ok("phase3_lane_baseline_git_head", **details)
            if lane.get("lane_baseline_git_head") == BASELINE_GIT_HEAD
            else _failed(
                "phase3_lane_baseline_git_head",
                expected=BASELINE_GIT_HEAD,
                actual=lane.get("lane_baseline_git_head"),
                **details,
            )
        )
        checks.append(
            _ok("phase3_lane_baseline_raw_artifact_ref", **details)
            if lane.get("lane_baseline_raw_artifact_ref") == lane.get("expected_lane_baseline_raw_artifact_ref")
            else _failed(
                "phase3_lane_baseline_raw_artifact_ref",
                expected=lane.get("expected_lane_baseline_raw_artifact_ref"),
                actual=lane.get("lane_baseline_raw_artifact_ref"),
                **details,
            )
        )
        checks.append(
            _ok("phase3_lane_ready", **details)
            if lane.get("ready_value") is True
            else _failed("phase3_lane_ready", ready_key=lane.get("ready_key"), actual=lane.get("ready_value"), **details)
        )
        readiness_failure_counts = lane.get("manifest_readiness_failure_counts")
        readiness_failure_total = sum(
            count
            for count in (
                readiness_failure_counts.values()
                if isinstance(readiness_failure_counts, Mapping)
                else ()
            )
            if isinstance(count, int)
        )
        readiness_matches_ready_key = (
            lane.get("ready_value") is True
            and lane.get("manifest_readiness_ready") is True
            and not lane.get("manifest_readiness_failure_kinds")
            and readiness_failure_total == 0
        ) or (
            lane.get("ready_value") is False
            and lane.get("manifest_readiness_ready") is False
            and bool(lane.get("manifest_readiness_failure_kinds"))
        )
        checks.append(
            _ok("phase3_lane_readiness_consistent", **details)
            if readiness_matches_ready_key
            else _failed(
                "phase3_lane_readiness_consistent",
                ready_key=lane.get("ready_key"),
                ready_value=lane.get("ready_value"),
                readiness_ready=lane.get("manifest_readiness_ready"),
                failure_kinds=lane.get("manifest_readiness_failure_kinds"),
                failure_counts=lane.get("manifest_readiness_failure_counts"),
                **details,
            )
        )
        checks.append(
            _ok("phase3_lane_readiness_entry_counts", **details)
            if _readiness_entry_counts_consistent(lane)
            else _failed(
                "phase3_lane_readiness_entry_counts",
                ready_key=lane.get("ready_key"),
                ready_value=lane.get("ready_value"),
                readiness_ready=lane.get("manifest_readiness_ready"),
                readiness_summary=lane.get("manifest_readiness_summary"),
                ready_entries=lane.get("manifest_readiness_ready_entries"),
                failed_entries=lane.get("manifest_readiness_failed_entries"),
                failure_kinds=lane.get("manifest_readiness_failure_kinds"),
                representative_count=(
                    len(lane.get("representative_entries"))
                    if isinstance(lane.get("representative_entries"), list)
                    else MISSING_SENTINEL
                ),
                **details,
            )
        )
        if lane.get("ready_value") is False:
            checks.append(
                _ok("phase3_lane_readiness_failure_details", **details)
                if lane.get("manifest_readiness_failure_kinds")
                else _failed(
                    "phase3_lane_readiness_failure_details",
                    readiness_ready=lane.get("manifest_readiness_ready"),
                    readiness_summary=lane.get("manifest_readiness_summary"),
                    failure_kinds=lane.get("manifest_readiness_failure_kinds"),
                    failure_counts=lane.get("manifest_readiness_failure_counts"),
                    **details,
                )
            )
        checks.append(
            _ok("phase3_lane_validator", **details)
            if lane.get("validator_status") in {"passed", "not_run"}
            else _failed(
                "phase3_lane_validator",
                error=lane.get("validator_error"),
                structured_failure_kinds=lane.get("validator_failure_kinds"),
                structured_failure_counts=lane.get("validator_failure_counts"),
                **details,
            )
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
        duplicate_representative_ids = _duplicate_representative_ids(representative_entries)
        stored_duplicate_representative_ids = lane.get("representative_entry_duplicate_ids")
        checks.append(
            _ok("phase3_lane_representative_entry_ids_unique", **details)
            if duplicate_representative_ids == []
            else _failed(
                "phase3_lane_representative_entry_ids_unique",
                duplicate_ids=duplicate_representative_ids,
                **details,
            )
        )
        checks.append(
            _ok("phase3_lane_representative_entry_duplicate_ids_consistent", **details)
            if stored_duplicate_representative_ids == duplicate_representative_ids
            else _failed(
                "phase3_lane_representative_entry_duplicate_ids_consistent",
                expected=duplicate_representative_ids,
                actual=stored_duplicate_representative_ids,
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
    failed_kind_counts: Dict[str, int] = {}
    failed_lanes: Dict[str, Dict[str, Any]] = {}
    failed_index_kinds: list[str] = []
    for check in failed:
        kind = str(check.get("kind") or MISSING_SENTINEL)
        failed_kind_counts[kind] = failed_kind_counts.get(kind, 0) + 1
        lane_id = check.get("lane_id")
        if not lane_id:
            failed_index_kinds.append(kind)
            continue
        lane_key = str(lane_id)
        lane_summary = failed_lanes.setdefault(
            lane_key,
            {
                "lane_number": check.get("lane_number", MISSING_SENTINEL),
                "lane_id": lane_key,
                "failed": 0,
                "failed_kinds": [],
                "failed_kind_counts": {},
            },
        )
        lane_summary["failed"] += 1
        lane_summary["failed_kinds"].append(kind)
        lane_summary["failed_kind_counts"][kind] = lane_summary["failed_kind_counts"].get(kind, 0) + 1
    return {
        "total": len(checks),
        "failed": len(failed),
        "failed_kinds": [check.get("kind") for check in failed],
        "failed_kind_counts": failed_kind_counts,
        "failed_lanes": list(failed_lanes.values()),
        "failed_index_kinds": failed_index_kinds,
    }


def _failed_check_kinds(checks: Sequence[Any]) -> list[str]:
    return [
        str(check.get("kind") or MISSING_SENTINEL)
        for check in checks
        if isinstance(check, Mapping) and check.get("status") == "failed"
    ]


def _materialized_lane_context(manifest: Mapping[str, Any]) -> Optional[Dict[str, Path]]:
    repo_root = manifest.get("repo_root")
    if not isinstance(repo_root, str) or not repo_root:
        return None
    baseline_ref = manifest.get("baseline_raw_artifact_ref")
    if not isinstance(baseline_ref, Mapping):
        return None
    raw_manifest_path = baseline_ref.get("path")
    if not isinstance(raw_manifest_path, str) or not raw_manifest_path:
        return None
    path = Path(raw_manifest_path)
    if path.name != "artifact_manifest.json" or path.parent.name != "raw":
        return None
    baseline_root = path.parent.parent
    if not baseline_root.exists():
        return None
    repo = Path(repo_root)
    if not repo.exists():
        return None
    return {"baseline_root": baseline_root, "repo_root": repo}


def _strict_json_equal(left: Any, right: Any) -> bool:
    return _canonical_json(left) == _canonical_json(right)


def _canonical_json(value: Any) -> str:
    return json.dumps(value, sort_keys=True, separators=(",", ":"), default=str)


def _lane_spec_rows_from_specs(specs: Sequence[Phase3LaneSpec]) -> list[Dict[str, Any]]:
    return [
        {
            "lane_number": spec.lane_number,
            "lane_id": spec.lane_id,
            "manifest_relpath": spec.manifest_relpath,
            "runner_relpath": spec.runner_relpath,
        }
        for spec in specs
    ]


def _lane_spec_rows_from_lanes(lanes: Sequence[Any]) -> list[Dict[str, Any]]:
    return [
        {
            "lane_number": lane.get("lane_number", MISSING_SENTINEL),
            "lane_id": lane.get("lane_id", MISSING_SENTINEL),
            "manifest_relpath": lane.get("manifest_relpath", MISSING_SENTINEL),
            "runner_relpath": lane.get("runner_relpath", MISSING_SENTINEL),
        }
        for lane in lanes
        if isinstance(lane, Mapping)
    ]


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


def _duplicate_representative_ids(entries: Any) -> list[str]:
    if not isinstance(entries, (list, tuple)):
        return []
    seen: set[str] = set()
    duplicate_ids: list[str] = []
    for entry in entries:
        if not isinstance(entry, Mapping):
            continue
        entry_id = str(entry.get("id") or MISSING_SENTINEL)
        if entry_id == MISSING_SENTINEL:
            continue
        if entry_id in seen and entry_id not in duplicate_ids:
            duplicate_ids.append(entry_id)
        seen.add(entry_id)
    return duplicate_ids


def _manifest_readiness(manifest: Mapping[str, Any]) -> Dict[str, Any]:
    readiness = manifest.get("readiness")
    if not isinstance(readiness, Mapping):
        return {
            "ready": MISSING_SENTINEL,
            "summary": {},
            "failure_kinds": [],
            "failure_counts": {},
            "ready_entries": MISSING_SENTINEL,
            "failed_entries": MISSING_SENTINEL,
        }
    failure_kinds = sorted(str(kind) for kind in readiness.get("failure_kinds") or ())
    failure_counts = _manifest_readiness_failure_counts(readiness, fallback_kinds=failure_kinds)
    return {
        "ready": readiness.get("ready", MISSING_SENTINEL),
        "summary": dict(readiness.get("summary") or {}) if isinstance(readiness.get("summary"), Mapping) else {},
        "failure_kinds": failure_kinds,
        "failure_counts": failure_counts,
        "ready_entries": readiness.get("ready_entries", MISSING_SENTINEL),
        "failed_entries": readiness.get("failed_entries", MISSING_SENTINEL),
    }


def _manifest_readiness_failure_counts(
    readiness: Mapping[str, Any],
    *,
    fallback_kinds: Sequence[str],
) -> Dict[str, int]:
    raw_counts = readiness.get("failure_counts")
    if isinstance(raw_counts, Mapping):
        return {
            str(kind): int(count)
            for kind, count in sorted(raw_counts.items(), key=lambda item: str(item[0]))
            if isinstance(count, int)
        }
    checks = readiness.get("checks")
    if isinstance(checks, (list, tuple)):
        counts: Dict[str, int] = {}
        for check in checks:
            if not isinstance(check, Mapping) or check.get("status") != "failed":
                continue
            kind = str(check.get("kind") or MISSING_SENTINEL)
            counts[kind] = counts.get(kind, 0) + 1
        if counts:
            return dict(sorted(counts.items()))
    return {kind: 1 for kind in fallback_kinds}


def _readiness_entry_counts_consistent(lane: Mapping[str, Any]) -> bool:
    ready_entries = lane.get("manifest_readiness_ready_entries", MISSING_SENTINEL)
    failed_entries = lane.get("manifest_readiness_failed_entries", MISSING_SENTINEL)
    if ready_entries == MISSING_SENTINEL and failed_entries == MISSING_SENTINEL:
        return True
    if not isinstance(ready_entries, int) or not isinstance(failed_entries, int):
        return False
    if ready_entries < 0 or failed_entries < 0:
        return False
    representative_entries = lane.get("representative_entries")
    if not isinstance(representative_entries, list):
        return False
    if ready_entries + failed_entries != len(representative_entries):
        return False
    readiness_summary = lane.get("manifest_readiness_summary")
    if isinstance(readiness_summary, Mapping):
        expected_summary = {
            "total": ready_entries + failed_entries,
            "passed": ready_entries,
            "failed": failed_entries,
        }
        for key, expected_value in expected_summary.items():
            if key not in readiness_summary:
                continue
            actual_value = readiness_summary.get(key)
            if not isinstance(actual_value, int) or actual_value != expected_value:
                return False
    if lane.get("ready_value") is True:
        return failed_entries == 0
    if lane.get("ready_value") is False and lane.get("manifest_readiness_failure_kinds"):
        return failed_entries > 0
    return True


def _runner_shell_contract(runner_path: Path) -> Dict[str, Any]:
    try:
        lines = runner_path.read_text(encoding="utf-8").splitlines()
    except OSError:
        return {
            "shebang": MISSING_SENTINEL,
            "strict_mode_present": False,
            "strict_mode_before_first_command": False,
        }
    top_level = _runner_active_top_level_mask(lines)
    first_command = next(
        (
            line.strip()
            for index, line in enumerate(lines)
            if index < len(top_level)
            and top_level[index]
            and line.strip()
            and not line.strip().startswith("#")
            and not line.strip().startswith("#!")
        ),
        MISSING_SENTINEL,
    )
    return {
        "shebang": lines[0].strip() if lines else MISSING_SENTINEL,
        "strict_mode_present": any(
            index < len(top_level)
            and top_level[index]
            and line.strip() == "set -euo pipefail"
            for index, line in enumerate(lines)
        ),
        "strict_mode_before_first_command": first_command == "set -euo pipefail",
    }


def _runner_manifest_refs(runner_path: Path) -> Dict[str, str]:
    try:
        lines = runner_path.read_text(encoding="utf-8").splitlines()
    except OSError:
        return {
            "manifest_relpath": MISSING_SENTINEL,
            "manifest_sha256": MISSING_SENTINEL,
        }
    top_level = _runner_active_top_level_mask(lines)
    path_match = next(
        (
            match
            for index, line in enumerate(lines)
            if index < len(top_level)
            and top_level[index]
            for match in (_RUNNER_MANIFEST_PATH_RE.match(line),)
            if match
        ),
        None,
    )
    sha_match = next(
        (
            match
            for index, line in enumerate(lines)
            if index < len(top_level)
            and top_level[index]
            for match in (_RUNNER_MANIFEST_SHA_RE.match(line),)
            if match
        ),
        None,
    )
    return {
        "manifest_relpath": path_match.group("path") if path_match else MISSING_SENTINEL,
        "manifest_sha256": sha_match.group("sha") if sha_match else MISSING_SENTINEL,
    }


def _runner_target_filter(runner_path: Path) -> Dict[str, Any]:
    try:
        lines = runner_path.read_text(encoding="utf-8").splitlines()
    except OSError:
        return _empty_target_filter()
    top_level = _runner_active_top_level_mask(lines)
    active_line_items = [
        (index + 1, line)
        for index, line in enumerate(lines)
        if index < len(top_level) and top_level[index]
    ]
    active_lines = [line for _, line in active_line_items]
    invalid_mutations = _runner_target_filter_invalid_mutations(active_line_items)
    target_matches = [
        match for line in active_lines for match in (_RUNNER_TARGET_SET_RE.match(line),) if match
    ]
    pair_matches = [
        match for line in active_lines for match in (_RUNNER_PAIR_FILTER_RE.match(line),) if match
    ]
    base_path_matches = [
        match for line in active_lines for match in (_RUNNER_BASE_PATH_RE.match(line),) if match
    ]
    matrix_matches = [
        match for line in active_lines for match in (_RUNNER_MATRIX_SCRIPT_RE.match(line),) if match
    ]
    target_match = target_matches[0] if target_matches else None
    pair_match = pair_matches[0] if pair_matches else None
    base_path_match = base_path_matches[0] if base_path_matches else None
    matrix_match = matrix_matches[0] if matrix_matches else None
    current_log_root_args = [
        match
        for line in active_lines
        for match in (_RUNNER_CURRENT_LOG_ROOT_ARG_RE.match(line),)
        if match
    ]
    baseline_log_root_args = [
        match
        for line in active_lines
        for match in (_RUNNER_BASELINE_LOG_ROOT_ARG_RE.match(line),)
        if match
    ]
    current_log_root_match = (
        _RUNNER_CURRENT_LOG_ROOT_RE.fullmatch(current_log_root_args[0].group("value"))
        if len(current_log_root_args) == 1
        else None
    )
    baseline_log_root_match = (
        _RUNNER_BASELINE_LOG_ROOT_RE.fullmatch(baseline_log_root_args[0].group("value"))
        if len(baseline_log_root_args) == 1
        else None
    )
    category = MISSING_SENTINEL
    if target_match:
        category = "function_call" if target_match.group("var") == "FUNCTION_CALL_TARGET_SET" else "loop"
    return {
        "category": category,
        "target_var": target_match.group("var") if target_match else MISSING_SENTINEL,
        "pair_filter_var": pair_match.group("var") if pair_match else MISSING_SENTINEL,
        "base_path_relpath": base_path_match.group("path") if base_path_match else MISSING_SENTINEL,
        "matrix_script_relpath": matrix_match.group("path") if matrix_match else MISSING_SENTINEL,
        "current_log_root_category": (
            current_log_root_match.group("category") if current_log_root_match else MISSING_SENTINEL
        ),
        "current_log_root_var": current_log_root_match.group("var") if current_log_root_match else MISSING_SENTINEL,
        "baseline_log_root_category": (
            baseline_log_root_match.group("category") if baseline_log_root_match else MISSING_SENTINEL
        ),
        "baseline_log_root_var": (
            baseline_log_root_match.group("var") if baseline_log_root_match else MISSING_SENTINEL
        ),
        "log_root_arg_counts": {
            "current_log_root": len(current_log_root_args),
            "baseline_log_root": len(baseline_log_root_args),
        },
        "target_filter_counts": {
            "target_set": len(target_matches),
            "pair_filter": len(pair_matches),
            "base_path": len(base_path_matches),
            "matrix_script": len(matrix_matches),
            "invalid_mutations": len(invalid_mutations),
        },
        "target_filter_invalid_mutations": invalid_mutations,
        "target_filter_invalid_mutation_count": len(invalid_mutations),
        "target_functions": _split_csv(target_match.group("value") if target_match else None),
        "pair_filter": _split_csv(pair_match.group("value") if pair_match else None),
    }


def _runner_target_filter_invalid_mutations(
    lines: Sequence[tuple[int, str]],
) -> list[Dict[str, Any]]:
    invalid: list[Dict[str, Any]] = []
    aliases: Dict[str, str] = {}
    for line_number, line in lines:
        code = _runner_shell_structure_code(line.strip())
        if not code or _canonical_runner_target_filter_line(code):
            continue
        vars_on_line = _runner_target_filter_mutated_vars(code, aliases)
        vars_on_line = list(dict.fromkeys(vars_on_line))
        if not vars_on_line:
            continue
        invalid.append(
            {
                "line": line_number,
                "vars": vars_on_line,
                "code": code,
            }
        )
    return invalid


def _runner_target_filter_mutated_vars(
    code: str,
    aliases: Optional[Dict[str, str]] = None,
) -> list[str]:
    aliases = aliases if aliases is not None else {}
    vars_on_line: list[str] = []
    for words in _shell_command_words(_shell_assignment_scan_code(code)):
        if not words:
            continue
        command_index = _shell_command_index(words)
        leading_assignments = words[:command_index]
        vars_on_line.extend(_target_filter_assignment_word_var(word) for word in leading_assignments)
        if command_index >= len(words):
            _record_target_filter_aliases(aliases, leading_assignments)
            continue
        effective = _effective_shell_command(words[command_index], words[command_index + 1:])
        if effective is None:
            continue
        command, args = effective
        if command == "unset":
            vars_on_line.extend(_target_filter_named_or_assignment_var(arg, aliases) for arg in args)
            continue
        if command == "export" and _shell_words_have_option(args, "n"):
            vars_on_line.extend(_target_filter_named_or_assignment_var(arg, aliases) for arg in args)
            continue
        if command == "export":
            vars_on_line.extend(_target_filter_assignment_word_var(arg) for arg in args)
            continue
        if command in {"declare", "typeset"}:
            vars_on_line.extend(_target_filter_assignment_word_var(arg) for arg in args)
            continue
        if command == "readonly":
            vars_on_line.extend(_target_filter_named_or_assignment_var(arg, aliases) for arg in args)
            continue
        if command == "printf":
            vars_on_line.extend(_printf_v_destination_vars(args, aliases))
            continue
        if command == "read":
            vars_on_line.extend(_read_destination_vars(args, aliases))
            continue
        if command in {"mapfile", "readarray"}:
            vars_on_line.extend(_mapfile_destination_vars(args, aliases))
            continue
        if command == "env":
            vars_on_line.extend(_env_target_filter_vars(args))
            continue
        if command == "eval":
            vars_on_line.extend(_eval_target_filter_vars(args, aliases))
    return list(dict.fromkeys(var for var in vars_on_line if var is not None))


def _shell_command_words(scan_code: str) -> list[list[str]]:
    commands: list[list[str]] = []
    words: list[str] = []
    current: list[str] = []
    index = 0
    while index < len(scan_code):
        char = scan_code[index]
        next_char = scan_code[index + 1] if index + 1 < len(scan_code) else ""
        if char.isspace():
            if current:
                words.append("".join(current).replace(_SHELL_QUOTED_SPACE, " "))
                current = []
            index += 1
            continue
        if char == ";" or (char == "&" and next_char == "&") or (char == "|" and next_char == "|"):
            if current:
                words.append("".join(current).replace(_SHELL_QUOTED_SPACE, " "))
                current = []
            if words:
                commands.append(words)
                words = []
            index += 2 if char in {"&", "|"} else 1
            continue
        current.append(char)
        index += 1
    if current:
        words.append("".join(current).replace(_SHELL_QUOTED_SPACE, " "))
    if words:
        commands.append(words)
    return commands


def _target_filter_assignment_word_var(word: str) -> Optional[str]:
    name = _shell_assignment_word_name(word)
    if name in _RUNNER_TARGET_FILTER_ASSIGNMENT_VARS:
        return name
    return None


def _target_filter_named_or_assignment_var(
    word: str,
    aliases: Optional[Mapping[str, str]] = None,
) -> Optional[str]:
    if word.startswith("-"):
        return None
    if word in _RUNNER_TARGET_FILTER_ASSIGNMENT_VARS:
        return word
    direct = _target_filter_assignment_word_var(word)
    if direct is not None:
        return direct
    return _target_filter_indirect_word_var(word, aliases or {})


def _shell_assignment_word_name(word: str) -> Optional[str]:
    if not word or not (word[0].isalpha() or word[0] == "_"):
        return None
    index = 1
    while index < len(word) and (word[index].isalnum() or word[index] == "_"):
        index += 1
    suffix = word[index:]
    if suffix.startswith("=") or suffix.startswith("+="):
        return word[:index]
    return None


def _shell_assignment_word_parts(word: str) -> Optional[tuple[str, str]]:
    name = _shell_assignment_word_name(word)
    if name is None:
        return None
    suffix = word[len(name):]
    if suffix.startswith("+="):
        return name, suffix[2:]
    if suffix.startswith("="):
        return name, suffix[1:]
    return None


def _record_target_filter_aliases(aliases: Dict[str, str], words: Sequence[str]) -> None:
    for word in words:
        parts = _shell_assignment_word_parts(word)
        if parts is None:
            continue
        name, value = parts
        if name in _RUNNER_TARGET_FILTER_ASSIGNMENT_VARS:
            continue
        if value in _RUNNER_TARGET_FILTER_ASSIGNMENT_VARS:
            aliases[name] = value
        elif _word_has_shell_expansion(value):
            aliases[name] = DYNAMIC_TARGET_FILTER_DESTINATION
        else:
            aliases[name] = NON_TARGET_FILTER_DESTINATION


def _target_filter_indirect_word_var(word: str, aliases: Mapping[str, str]) -> Optional[str]:
    referenced_names = _shell_expansion_names(word)
    if not referenced_names:
        return None
    resolved: list[str] = []
    for name in referenced_names:
        target = aliases.get(name)
        if target in _RUNNER_TARGET_FILTER_ASSIGNMENT_VARS:
            resolved.append(target)
        elif target == DYNAMIC_TARGET_FILTER_DESTINATION or target is None:
            resolved.append(DYNAMIC_TARGET_FILTER_DESTINATION)
    if resolved:
        return resolved[0]
    return None


def _word_has_shell_expansion(word: str) -> bool:
    return bool(_shell_expansion_names(word) or "$(" in word or "`" in word)


def _shell_expansion_names(word: str) -> list[str]:
    names: list[str] = []
    for match in re.finditer(r'\$(?P<braced>\{(?P<braced_name>[A-Za-z_][A-Za-z0-9_]*)\}|(?P<plain>[A-Za-z_][A-Za-z0-9_]*))', word):
        names.append(match.group("braced_name") or match.group("plain"))
    return names


def _effective_shell_command(command: str, args: Sequence[str]) -> Optional[tuple[str, Sequence[str]]]:
    if command == "builtin":
        if not args:
            return None
        if args[0] == "--":
            return (args[1], args[2:]) if len(args) > 1 else None
        return args[0], args[1:]
    if command == "command":
        index = 0
        while index < len(args) and args[index].startswith("-") and args[index] != "--":
            if "v" in args[index][1:] or "V" in args[index][1:]:
                return None
            index += 1
        if index < len(args) and args[index] == "--":
            index += 1
        if index >= len(args):
            return None
        return args[index], args[index + 1:]
    return command, args


def _shell_command_index(words: Sequence[str]) -> int:
    index = 0
    while index < len(words) and _shell_assignment_word_name(words[index]) is not None:
        index += 1
    return index


def _shell_words_have_option(words: Sequence[str], option: str) -> bool:
    return any(word.startswith("-") and not word.startswith("--") and option in word[1:] for word in words)


def _printf_v_destination_vars(
    args: Sequence[str],
    aliases: Optional[Mapping[str, str]] = None,
) -> list[str]:
    for index, word in enumerate(args):
        if word == "--":
            return []
        if word == "-v" and index + 1 < len(args):
            return [_target_filter_named_or_assignment_var(args[index + 1], aliases)]
        if word.startswith("-v") and len(word) > 2:
            return [_target_filter_named_or_assignment_var(word[2:], aliases)]
        if not word.startswith("-"):
            return []
    return []


def _read_destination_vars(
    args: Sequence[str],
    aliases: Optional[Mapping[str, str]] = None,
) -> list[str]:
    destinations: list[Optional[str]] = []
    index = 0
    while index < len(args):
        word = args[index]
        if _shell_redirection_word(word):
            break
        if word == "--":
            index += 1
            break
        if word == "-a":
            if index + 1 < len(args):
                destinations.append(_target_filter_named_or_assignment_var(args[index + 1], aliases))
            index += 2
            continue
        if word.startswith("-a") and len(word) > 2:
            destinations.append(_target_filter_named_or_assignment_var(word[2:], aliases))
            index += 1
            continue
        if word in {"-d", "-n", "-N", "-p", "-t", "-u"}:
            index += 2
            continue
        if word.startswith("-"):
            index += 1
            continue
        break
    for word in args[index:]:
        if _shell_redirection_word(word):
            break
        destinations.append(_target_filter_named_or_assignment_var(word, aliases))
    return [var for var in destinations if var is not None]


def _mapfile_destination_vars(
    args: Sequence[str],
    aliases: Optional[Mapping[str, str]] = None,
) -> list[str]:
    index = 0
    while index < len(args):
        word = args[index]
        if _shell_redirection_word(word):
            return []
        if word == "--":
            index += 1
            break
        if word in {"-C", "-c", "-d", "-n", "-O", "-s", "-u"}:
            index += 2
            continue
        if word.startswith("-"):
            index += 1
            continue
        break
    if index >= len(args) or _shell_redirection_word(args[index]):
        return []
    return [_target_filter_named_or_assignment_var(args[index], aliases)]


def _env_target_filter_vars(args: Sequence[str]) -> list[Optional[str]]:
    vars_on_line: list[Optional[str]] = []
    index = 0
    while index < len(args):
        word = args[index]
        if word == "--":
            index += 1
            break
        if word == "-u" and index + 1 < len(args):
            vars_on_line.append(_target_filter_named_or_assignment_var(args[index + 1]))
            index += 2
            continue
        if word.startswith("-u") and len(word) > 2:
            vars_on_line.append(_target_filter_named_or_assignment_var(word[2:]))
            index += 1
            continue
        if word.startswith("-"):
            index += 1
            continue
        var = _target_filter_assignment_word_var(word)
        if var is None:
            break
        vars_on_line.append(var)
        index += 1
    return vars_on_line


def _eval_target_filter_vars(
    args: Sequence[str],
    aliases: Optional[Mapping[str, str]] = None,
) -> list[str]:
    vars_on_line: list[str] = []
    for word in args:
        vars_on_line.extend(_target_filter_vars_mentioned_in_word(word))
        indirect = _target_filter_indirect_word_var(word, aliases or {})
        if indirect is not None:
            vars_on_line.append(indirect)
    return list(dict.fromkeys(vars_on_line))


def _target_filter_vars_mentioned_in_word(word: str) -> list[str]:
    vars_on_line: list[str] = []
    for var in _RUNNER_TARGET_FILTER_ASSIGNMENT_VARS:
        if re.search(rf'(?<![A-Za-z0-9_]){re.escape(var)}(?![A-Za-z0-9_])', word):
            vars_on_line.append(var)
    return vars_on_line


def _shell_redirection_word(word: str) -> bool:
    return word.startswith("<") or word.startswith(">") or word in {"|", "|&"}


def _canonical_runner_target_filter_line(code: str) -> bool:
    return any(
        pattern.fullmatch(code) is not None
        for pattern in (
            _RUNNER_TARGET_SET_RE,
            _RUNNER_PAIR_FILTER_RE,
            _RUNNER_BASE_PATH_RE,
            _RUNNER_MATRIX_SCRIPT_RE,
        )
    )


def _runner_safety_defaults(runner_path: Path) -> Dict[str, Any]:
    try:
        lines = runner_path.read_text(encoding="utf-8").splitlines()
    except OSError:
        return {
            "defaults": {},
            "duplicate_vars": [],
            "require_ready_arg_present": False,
            "gate_args_invoked": False,
            "gate_validator_module": MISSING_SENTINEL,
            "gate_validator_invocation_count": 0,
            "required_gate_args": {
                flag: MISSING_SENTINEL
                for flag in EXPECTED_RUNNER_GATE_ARGS
            },
            "required_gate_arg_counts": {
                flag: 0
                for flag in EXPECTED_RUNNER_GATE_ARGS
            },
            "required_gate_args_missing": list(EXPECTED_RUNNER_GATE_ARGS),
            "required_gate_args_duplicate": [],
            "required_gate_args_value_mismatch": [],
            "gate_args_unknown_args": [],
            "gate_args_invalid_optional_args": [],
            "gate_args_assignment_count": 0,
            "gate_args_invalid_mutations": [],
            "gate_args_invalid_mutation_count": 0,
            "gate_smoke_status": "not_run",
            "gate_smoke_validator_invocation_count": 0,
            "gate_smoke_argv_matches_expected": False,
            "gate_smoke_error": MISSING_SENTINEL,
            "gate_smoke_failure_kind": MISSING_SENTINEL,
            "gate_smoke_returncode": MISSING_SENTINEL,
            "gate_smoke_expected_argv": [],
            "gate_smoke_observed_argv": [],
            "gate_smoke_observed_invocations": [],
            "gate_smoke_argv_diff": [],
        }
    defaults: Dict[str, str] = {}
    duplicate_vars: list[str] = []
    top_level = _runner_active_top_level_mask(lines)
    for index, line in enumerate(lines):
        if index >= len(top_level) or not top_level[index]:
            continue
        match = _RUNNER_DEFAULT_ENV_RE.match(line)
        if not match:
            continue
        var = match.group("var")
        if var in defaults:
            duplicate_vars.append(var)
            continue
        defaults[var] = match.group("value")
    gate_probe = _runner_gate_contract(runner_path)
    return {
        "defaults": defaults,
        "duplicate_vars": list(dict.fromkeys(duplicate_vars)),
        "require_ready_arg_present": gate_probe["require_ready_arg_present"],
        "gate_args_invoked": gate_probe["gate_args_invoked"],
        "gate_validator_module": gate_probe["gate_validator_module"],
        "gate_validator_invocation_count": gate_probe["gate_validator_invocation_count"],
        "required_gate_args": gate_probe["required_gate_args"],
        "required_gate_arg_counts": gate_probe["required_gate_arg_counts"],
        "required_gate_args_missing": gate_probe["required_gate_args_missing"],
        "required_gate_args_duplicate": gate_probe["required_gate_args_duplicate"],
        "required_gate_args_value_mismatch": gate_probe["required_gate_args_value_mismatch"],
        "gate_args_unknown_args": gate_probe["gate_args_unknown_args"],
        "gate_args_invalid_optional_args": gate_probe["gate_args_invalid_optional_args"],
        "gate_args_assignment_count": gate_probe["gate_args_assignment_count"],
        "gate_args_invalid_mutations": gate_probe["gate_args_invalid_mutations"],
        "gate_args_invalid_mutation_count": gate_probe["gate_args_invalid_mutation_count"],
        "gate_smoke_status": gate_probe["gate_smoke_status"],
        "gate_smoke_validator_invocation_count": gate_probe["gate_smoke_validator_invocation_count"],
        "gate_smoke_argv_matches_expected": gate_probe["gate_smoke_argv_matches_expected"],
        "gate_smoke_error": gate_probe["gate_smoke_error"],
        "gate_smoke_failure_kind": gate_probe["gate_smoke_failure_kind"],
        "gate_smoke_returncode": gate_probe["gate_smoke_returncode"],
        "gate_smoke_expected_argv": gate_probe["gate_smoke_expected_argv"],
        "gate_smoke_observed_argv": gate_probe["gate_smoke_observed_argv"],
        "gate_smoke_observed_invocations": gate_probe["gate_smoke_observed_invocations"],
        "gate_smoke_argv_diff": gate_probe["gate_smoke_argv_diff"],
    }


def _runner_gate_contract(runner_path: Path) -> Dict[str, Any]:
    empty = _empty_runner_gate_contract()
    try:
        content = runner_path.read_text(encoding="utf-8")
    except OSError:
        return empty

    lines = content.splitlines()
    top_level = _runner_static_top_level_mask(lines)
    validator_starts = _runner_gate_validator_starts(lines, top_level)
    canonical_validator = _canonical_runner_gate_validator_invocation(lines, validator_starts)
    validator_limit = canonical_validator["start"] if canonical_validator else (
        validator_starts[0]["index"] if validator_starts else len(lines)
    )
    gate_block = _runner_gate_args_block(lines, top_level, validator_limit)
    parsed_args = _static_gate_args(gate_block["args"])
    gate_arg_diagnostics = _gate_arg_diagnostics(parsed_args)
    require_ready = _runner_require_ready_block(lines, validator_limit)
    invalid_mutations = list(gate_block["invalid_mutations"])
    invalid_mutations.extend(require_ready["invalid_mutations"])
    invalid_mutations.extend(
        _runner_gate_args_forbidden_lines(
            lines,
            validator_limit,
            gate_block["ranges"],
            require_ready["ranges"],
        )
    )

    if len(validator_starts) != 1:
        if validator_starts:
            invalid_mutations.append(f"runner invoked gate validator {len(validator_starts)} times")
    elif canonical_validator is None:
        invalid_mutations.append("validator did not consume PHASE3_GATE_ARGS array")

    if parsed_args["values"] != dict(EXPECTED_RUNNER_GATE_ARGS) or any(
        parsed_args["counts"].get(flag) != 1 for flag in EXPECTED_RUNNER_GATE_ARGS
    ):
        invalid_mutations.append("static PHASE3_GATE_ARGS differed from expected gate arguments")
    if parsed_args["unknown_args"]:
        invalid_mutations.append(
            "static PHASE3_GATE_ARGS contained unexpected arguments: "
            + ", ".join(parsed_args["unknown_args"])
        )
    if parsed_args["invalid_optional_args"]:
        invalid_mutations.append(
            "static PHASE3_GATE_ARGS contained invalid optional arguments: "
            + ", ".join(parsed_args["invalid_optional_args"])
        )

    smoke_result = _runner_gate_smoke_result(
        runner_path,
        canonical_validator["module"] if canonical_validator else MISSING_SENTINEL,
        gate_block["args"],
        require_ready["present"],
    )
    smoke_error = smoke_result["error"]
    if smoke_error:
        invalid_mutations.append(smoke_error)

    module = (
        validator_starts[0]["module"]
        if validator_starts
        else MISSING_SENTINEL
    )
    return {
        "require_ready_arg_present": require_ready["present"],
        "gate_args_invoked": len(validator_starts) == 1,
        "gate_validator_module": module,
        "gate_validator_invocation_count": len(validator_starts),
        "required_gate_args": parsed_args["values"],
        "required_gate_arg_counts": parsed_args["counts"],
        "required_gate_args_missing": gate_arg_diagnostics["missing"],
        "required_gate_args_duplicate": gate_arg_diagnostics["duplicate"],
        "required_gate_args_value_mismatch": gate_arg_diagnostics["value_mismatch"],
        "gate_args_unknown_args": gate_arg_diagnostics["unknown_args"],
        "gate_args_invalid_optional_args": gate_arg_diagnostics["invalid_optional_args"],
        "gate_args_assignment_count": gate_block["assignment_count"],
        "gate_args_invalid_mutations": list(dict.fromkeys(invalid_mutations)),
        "gate_args_invalid_mutation_count": len(list(dict.fromkeys(invalid_mutations))),
        "gate_smoke_status": smoke_result["status"],
        "gate_smoke_validator_invocation_count": smoke_result["validator_invocation_count"],
        "gate_smoke_argv_matches_expected": smoke_result["argv_matches_expected"],
        "gate_smoke_error": smoke_result["error"] or MISSING_SENTINEL,
        "gate_smoke_failure_kind": smoke_result["failure_kind"],
        "gate_smoke_returncode": smoke_result["returncode"],
        "gate_smoke_expected_argv": smoke_result["expected_argv"],
        "gate_smoke_observed_argv": smoke_result["observed_argv"],
        "gate_smoke_observed_invocations": smoke_result["observed_invocations"],
        "gate_smoke_argv_diff": smoke_result["argv_diff"],
    }


def _empty_runner_gate_contract() -> Dict[str, Any]:
    return {
        "require_ready_arg_present": False,
        "gate_args_invoked": False,
        "gate_validator_module": MISSING_SENTINEL,
        "gate_validator_invocation_count": 0,
        "required_gate_args": {
            flag: MISSING_SENTINEL
            for flag in EXPECTED_RUNNER_GATE_ARGS
        },
        "required_gate_arg_counts": {
            flag: 0
            for flag in EXPECTED_RUNNER_GATE_ARGS
        },
        "required_gate_args_missing": list(EXPECTED_RUNNER_GATE_ARGS),
        "required_gate_args_duplicate": [],
        "required_gate_args_value_mismatch": [],
        "gate_args_unknown_args": [],
        "gate_args_invalid_optional_args": [],
        "gate_args_assignment_count": 0,
        "gate_args_invalid_mutations": [],
        "gate_args_invalid_mutation_count": 0,
        "gate_smoke_status": "not_run",
        "gate_smoke_validator_invocation_count": 0,
        "gate_smoke_argv_matches_expected": False,
        "gate_smoke_error": MISSING_SENTINEL,
        "gate_smoke_failure_kind": MISSING_SENTINEL,
        "gate_smoke_returncode": MISSING_SENTINEL,
        "gate_smoke_expected_argv": [],
        "gate_smoke_observed_argv": [],
        "gate_smoke_observed_invocations": [],
        "gate_smoke_argv_diff": [],
    }


def _runner_static_top_level_mask(lines: Sequence[str]) -> list[bool]:
    mask: list[bool] = []
    function_depth = 0
    pending_function_body = False
    for line in lines:
        stripped = line.strip()
        code = _runner_shell_structure_code(stripped)
        mask.append(function_depth == 0 and not pending_function_body)
        if not code:
            continue
        if pending_function_body and code.startswith("{"):
            function_depth = max(1, _shell_brace_delta(code))
            pending_function_body = False
            continue
        if pending_function_body:
            pending_function_body = False
        if function_depth > 0:
            function_depth = max(0, function_depth + _shell_brace_delta(code))
            continue
        if _line_starts_shell_function(code):
            if "{" in code:
                function_depth = max(0, _shell_brace_delta(code[code.find("{"):]))
            else:
                pending_function_body = True
            continue
    return mask


def _shell_brace_delta(code: str) -> int:
    delta = 0
    single_quote = False
    double_quote = False
    parameter_expansion_depth = 0
    index = 0
    while index < len(code):
        char = code[index]
        next_char = code[index + 1] if index + 1 < len(code) else ""
        if char == "\\":
            index += 2
            continue
        if single_quote:
            if char == "'":
                single_quote = False
            index += 1
            continue
        if double_quote:
            if char == '"':
                double_quote = False
            index += 1
            continue
        if parameter_expansion_depth > 0:
            if char == "{":
                parameter_expansion_depth += 1
            elif char == "}":
                parameter_expansion_depth -= 1
            index += 1
            continue
        if char == "'":
            single_quote = True
        elif char == '"':
            double_quote = True
        elif char == "$" and next_char == "{":
            parameter_expansion_depth = 1
            index += 2
            continue
        elif char == "{":
            delta += 1
        elif char == "}":
            delta -= 1
        index += 1
    return delta


def _shell_assignment_scan_code(code: str) -> str:
    out: list[str] = []
    single_quote = False
    double_quote = False
    parameter_expansion_depth = 0
    index = 0
    while index < len(code):
        char = code[index]
        next_char = code[index + 1] if index + 1 < len(code) else ""
        if char == "\\":
            out.append(next_char if (single_quote or double_quote) and next_char else " ")
            index += 2
            continue
        if single_quote:
            if char == "'":
                single_quote = False
            else:
                out.append(_SHELL_QUOTED_SPACE if char.isspace() else char)
            index += 1
            continue
        if double_quote:
            if char == '"':
                double_quote = False
            else:
                out.append(_SHELL_QUOTED_SPACE if char.isspace() else char)
            index += 1
            continue
        if parameter_expansion_depth > 0:
            if char == "{":
                parameter_expansion_depth += 1
            elif char == "}":
                parameter_expansion_depth -= 1
            out.append(char)
            index += 1
            continue
        if char == "'":
            single_quote = True
        elif char == '"':
            double_quote = True
        elif char == "$" and next_char == "{":
            parameter_expansion_depth = 1
            out.extend((char, next_char))
            index += 2
            continue
        else:
            out.append(char)
        index += 1
    return "".join(out)


def _runner_active_top_level_mask(lines: Sequence[str]) -> list[bool]:
    function_top_level = _runner_static_top_level_mask(lines)
    mask: list[bool] = []
    compound_depth = 0
    subshell_depth = 0
    guard_block_depth = 0
    pending_guard_block = False
    for index, line in enumerate(lines):
        stripped = line.strip()
        code = _runner_shell_structure_code(stripped)
        opens_guard_block = (
            re.search(r'(?:&&|\|\|)\s*\{\s*$', code) is not None
            or (pending_guard_block and code == "{")
        )
        opens_subshell = code.startswith("(")
        active = (
            function_top_level[index]
            and compound_depth == 0
            and subshell_depth == 0
            and guard_block_depth == 0
            and not opens_guard_block
            and not opens_subshell
        )
        mask.append(active)
        if not function_top_level[index] or not code:
            continue
        pending_guard_block = False
        if re.match(r'^(?:fi|done|esac)\b', code):
            compound_depth = max(0, compound_depth - 1)
        if code == ")":
            subshell_depth = max(0, subshell_depth - 1)
        if code == "}":
            guard_block_depth = max(0, guard_block_depth - 1)
        if re.match(r'^(?:if|for|while|until|case|select)\b', code):
            compound_depth += 1
        if opens_subshell:
            subshell_depth += 1
        if opens_guard_block:
            guard_block_depth += 1
        pending_guard_block = re.search(r'(?:&&|\|\|)\s*\\$', code) is not None
    return mask


def _runner_shell_structure_code(stripped: str) -> str:
    if not stripped or stripped.startswith("#"):
        return ""
    return re.sub(r'\s+#.*$', '', stripped).strip()


def _line_starts_shell_function(stripped: str) -> bool:
    return bool(
        re.match(r'^(?:function\s+)?[A-Za-z_][A-Za-z0-9_]*\s*\(\)\s*(?:\{.*)?$', stripped)
        or re.match(r'^function\s+[A-Za-z_][A-Za-z0-9_]*\s*(?:\{.*)?$', stripped)
    )


def _runner_gate_validator_starts(lines: Sequence[str], top_level: Sequence[bool]) -> list[Dict[str, Any]]:
    starts: list[Dict[str, Any]] = []
    pattern = re.compile(
        r'^\s*"\$PYTHON_BIN"\s+-m\s+'
        r'(?P<module>scripts\.function_tracer_pcode\.validation\.[A-Za-z0-9_\.]+)'
        r'(?P<suffix>.*)$'
    )
    for index, line in enumerate(lines):
        if index >= len(top_level) or not top_level[index]:
            continue
        match = pattern.match(line)
        if not match:
            continue
        starts.append(
            {
                "index": index,
                "module": match.group("module"),
                "suffix": match.group("suffix").strip(),
            }
        )
    return starts


def _canonical_runner_gate_validator_invocation(
    lines: Sequence[str],
    validator_starts: Sequence[Mapping[str, Any]],
) -> Optional[Dict[str, Any]]:
    if len(validator_starts) != 1:
        return None
    start = validator_starts[0]
    index = int(start["index"])
    if start.get("suffix") != "\\":
        return None
    if index + 1 >= len(lines):
        return None
    if lines[index + 1].strip() != '"${PHASE3_GATE_ARGS[@]}"':
        return None
    return {
        "start": index,
        "end": index + 1,
        "module": start["module"],
    }


def _runner_gate_args_block(
    lines: Sequence[str],
    top_level: Sequence[bool],
    validator_limit: int,
) -> Dict[str, Any]:
    starts = [
        index
        for index, line in enumerate(lines[:validator_limit])
        if index < len(top_level) and top_level[index] and line.strip() == "PHASE3_GATE_ARGS=("
    ]
    invalid_mutations: list[str] = []
    if len(starts) != 1:
        if not starts:
            invalid_mutations.append("PHASE3_GATE_ARGS block missing")
        else:
            invalid_mutations.append(f"runner defined PHASE3_GATE_ARGS {len(starts)} times")
        return {
            "args": [],
            "ranges": [],
            "assignment_count": 0,
            "invalid_mutations": invalid_mutations,
        }
    start = starts[0]
    args: list[str] = []
    end: Optional[int] = None
    for index in range(start + 1, validator_limit):
        stripped = lines[index].strip()
        if stripped == ")":
            end = index
            break
        if stripped and not stripped.startswith("#"):
            args.append(stripped)
    if end is None:
        invalid_mutations.append("PHASE3_GATE_ARGS block is unterminated")
        end = start
    parsed = _static_gate_args(args)
    assignment_count = 1 if _static_gate_args_valid(parsed, require_ready=False) else 0
    return {
        "args": args,
        "ranges": [(start, end)],
        "assignment_count": assignment_count,
        "invalid_mutations": invalid_mutations,
    }


def _runner_require_ready_block(lines: Sequence[str], validator_limit: int) -> Dict[str, Any]:
    ranges: list[tuple[int, int]] = []
    invalid_mutations: list[str] = []
    ready_line_indexes = [
        index
        for index, line in enumerate(lines[:validator_limit])
        if line.strip() == "PHASE3_GATE_ARGS+=(--require-ready)"
    ]
    for index in ready_line_indexes:
        if (
            index - 1 >= 0
            and index + 1 < validator_limit
            and lines[index - 1].strip() == 'if [[ "$PHASE3_REQUIRE_READY" != "0" ]]; then'
            and lines[index + 1].strip() == "fi"
        ):
            ranges.append((index - 1, index + 1))
        else:
            invalid_mutations.append("PHASE3_GATE_ARGS --require-ready append is not in the canonical guard")
    if len(ranges) > 1:
        invalid_mutations.append(f"runner appended --require-ready {len(ranges)} times")
    return {
        "present": len(ranges) == 1,
        "ranges": ranges,
        "invalid_mutations": invalid_mutations,
    }


def _static_gate_args(args: Sequence[str]) -> Dict[str, Any]:
    values: Dict[str, list[str]] = {flag: [] for flag in EXPECTED_RUNNER_GATE_ARGS}
    optional_values: Dict[str, list[str]] = {
        "--current-log-root": [],
        "--baseline-log-root": [],
        "--phase1-dir": [],
        "--phase1-current-log-root": [],
    }
    unknown_args: list[str] = []
    for raw in args:
        parsed = _split_static_gate_arg(raw)
        if parsed is None:
            unknown_args.append(raw)
            continue
        flag, value = parsed
        if flag in values:
            values[flag].append(_normalize_static_gate_value(value))
        elif flag in optional_values:
            optional_values[flag].append(_normalize_static_gate_value(value))
        else:
            unknown_args.append(raw)
    invalid_optional_args = _invalid_optional_gate_args(optional_values)
    return {
        "values": {
            flag: observed[0] if len(observed) == 1 else MISSING_SENTINEL
            for flag, observed in values.items()
        },
        "counts": {
            flag: len(observed)
            for flag, observed in values.items()
        },
        "optional_values": optional_values,
        "optional_counts": {
            flag: len(observed)
            for flag, observed in optional_values.items()
        },
        "unknown_args": unknown_args,
        "invalid_optional_args": invalid_optional_args,
    }


def _split_static_gate_arg(raw: str) -> Optional[tuple[str, str]]:
    stripped = raw.strip()
    if not stripped.startswith("--"):
        return None
    parts = stripped.split(None, 1)
    if len(parts) != 2:
        return None
    flag, value = parts
    value = value.strip()
    if len(value) >= 2 and value[0] == value[-1] == '"':
        value = value[1:-1]
    return flag, value


def _normalize_static_gate_value(value: str) -> str:
    return value


def _static_gate_args_valid(parsed: Mapping[str, Any], *, require_ready: bool) -> bool:
    return (
        parsed["values"] == dict(EXPECTED_RUNNER_GATE_ARGS)
        and all(parsed["counts"].get(flag) == 1 for flag in EXPECTED_RUNNER_GATE_ARGS)
        and not parsed["unknown_args"]
        and not parsed["invalid_optional_args"]
        and not require_ready
    )


def _gate_arg_diagnostics(parsed: Mapping[str, Any]) -> Dict[str, Any]:
    counts = parsed.get("counts") if isinstance(parsed.get("counts"), Mapping) else {}
    values = parsed.get("values") if isinstance(parsed.get("values"), Mapping) else {}
    missing: list[str] = []
    duplicate: list[str] = []
    value_mismatch: list[Dict[str, Any]] = []
    for flag, expected in EXPECTED_RUNNER_GATE_ARGS.items():
        count = counts.get(flag, 0)
        if count == 0:
            missing.append(flag)
            continue
        if count > 1:
            duplicate.append(flag)
            continue
        actual = values.get(flag, MISSING_SENTINEL)
        if actual != expected:
            value_mismatch.append(
                {
                    "flag": flag,
                    "expected": expected,
                    "actual": actual,
                }
            )
    return {
        "missing": missing,
        "duplicate": duplicate,
        "value_mismatch": value_mismatch,
        "unknown_args": list(parsed.get("unknown_args") or ()),
        "invalid_optional_args": list(parsed.get("invalid_optional_args") or ()),
    }


def _invalid_optional_gate_args(optional_values: Mapping[str, Sequence[str]]) -> list[str]:
    allowed = {
        "--current-log-root": {
            "function_call=$OUTPUT_BASE_DIR",
            "loop=$OUTPUT_BASE_DIR",
        },
        "--baseline-log-root": {
            "function_call=$BASELINE_FUNCTION_CALL_LOG_ROOT",
            "loop=$BASELINE_LOOP_LOG_ROOT",
        },
        "--phase1-dir": {
            "$PHASE1_DIR",
        },
        "--phase1-current-log-root": {
            "function_call=$OUTPUT_BASE_DIR",
            "loop=$OUTPUT_BASE_DIR",
            "function_call=$PHASE1_FUNCTION_CALL_LOG_ROOT",
            "loop=$PHASE1_LOOP_LOG_ROOT",
        },
    }
    invalid: list[str] = []
    for flag, observed in optional_values.items():
        if flag == "--phase1-current-log-root":
            invalid.extend(_invalid_phase1_current_log_roots(observed, allowed[flag]))
            continue
        if len(observed) > 1:
            invalid.append(f"{flag}=<duplicate>")
            continue
        if len(observed) == 1 and observed[0] not in allowed[flag]:
            invalid.append(f"{flag}={observed[0]}")
    return invalid


def _invalid_phase1_current_log_roots(
    observed: Sequence[str],
    allowed: set[str],
) -> list[str]:
    invalid: list[str] = []
    seen_categories: set[str] = set()
    for value in observed:
        if value not in allowed:
            invalid.append(f"--phase1-current-log-root={value}")
            continue
        category = value.split("=", 1)[0]
        if category in seen_categories:
            invalid.append(f"--phase1-current-log-root={category}=<duplicate>")
            continue
        seen_categories.add(category)
    return invalid


def _runner_gate_args_forbidden_lines(
    lines: Sequence[str],
    validator_limit: int,
    gate_ranges: Sequence[tuple[int, int]],
    require_ready_ranges: Sequence[tuple[int, int]],
) -> list[str]:
    invalid: list[str] = []
    allowed = set()
    for start, end in (*gate_ranges, *require_ready_ranges):
        allowed.update(range(start, end + 1))
    post_gate_start = max((end + 1 for _, end in gate_ranges), default=None)
    for index, line in enumerate(lines[:validator_limit]):
        if index in allowed:
            continue
        stripped = line.strip()
        if not stripped or stripped.startswith("#"):
            continue
        if "PHASE3_GATE_ARGS" in stripped:
            invalid.append(f"unexpected PHASE3_GATE_ARGS line before validator: {stripped}")
            continue
        if post_gate_start is not None and index >= post_gate_start:
            invalid.append(f"unexpected command between PHASE3_GATE_ARGS block and validator: {stripped}")
    return invalid


def _runner_gate_smoke_result(
    runner_path: Path,
    validator_module: str,
    gate_args: Sequence[str],
    include_require_ready: bool,
) -> Dict[str, Any]:
    with tempfile.TemporaryDirectory(prefix="phase3-lane-runner-smoke-") as tmp_name:
        tmp = Path(tmp_name)
        stub_dir = tmp / "bin"
        stub_dir.mkdir()
        _write_runner_smoke_stub(stub_dir / "bash")
        stub_python = tmp / "validator_python"
        invocation_log = tmp / "validator-invocations.jsonl"
        _write_runner_smoke_python_stub(stub_python, invocation_log)
        env = _runner_smoke_environment(runner_path, tmp, stub_dir, stub_python)
        expected_audit_argv = _expected_runner_smoke_audit_argv(
            validator_module,
            gate_args,
            include_require_ready,
        )
        expected_argv = _expected_runner_smoke_argv(
            validator_module,
            gate_args,
            include_require_ready,
            env,
        )
        try:
            completed = subprocess.run(
                [_bash_executable(), str(runner_path)],
                cwd=str(runner_path.parent),
                env=env,
                text=True,
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
                timeout=RUNNER_GATE_SMOKE_TIMEOUT_SECONDS,
                check=False,
            )
        except (OSError, subprocess.TimeoutExpired) as exc:
            return _runner_gate_smoke_failed(
                f"runner smoke execution failed: {exc}",
                failure_kind="execution_error",
                expected_argv=expected_audit_argv,
            )
        try:
            invocations = _read_runner_smoke_invocations(invocation_log)
        except ValueError as exc:
            return _runner_gate_smoke_failed(
                f"runner smoke validator invocation log was invalid: {exc}",
                failure_kind="invalid_invocation_log",
                expected_argv=expected_audit_argv,
                returncode=completed.returncode,
            )
        invocation_count = len(invocations)
        observed_audit_invocations = [
            _normalize_runner_smoke_argv(invocation, env) for invocation in invocations
        ]
        observed_audit_argv = observed_audit_invocations[0] if observed_audit_invocations else []
        argv_matches_expected = (
            invocation_count == 1
            and expected_argv is not None
            and invocations[0] == expected_argv
        )
        if completed.returncode != 0:
            return _runner_gate_smoke_failed(
                f"runner smoke execution failed: returncode={completed.returncode}",
                failure_kind="nonzero_exit",
                invocation_count=invocation_count,
                argv_matches_expected=argv_matches_expected,
                returncode=completed.returncode,
                expected_argv=expected_audit_argv,
                observed_argv=observed_audit_argv,
                observed_invocations=observed_audit_invocations,
            )
        if invocation_count != 1:
            return _runner_gate_smoke_failed(
                f"runner smoke validator invocation count was {invocation_count}",
                failure_kind="validator_invocation_count",
                invocation_count=invocation_count,
                returncode=completed.returncode,
                expected_argv=expected_audit_argv,
                observed_argv=observed_audit_argv,
                observed_invocations=observed_audit_invocations,
            )
        if expected_argv is None:
            return _runner_gate_smoke_failed(
                "runner smoke expected validator argv was unavailable",
                failure_kind="expected_argv_unavailable",
                invocation_count=invocation_count,
                returncode=completed.returncode,
                expected_argv=expected_audit_argv,
                observed_argv=observed_audit_argv,
                observed_invocations=observed_audit_invocations,
            )
        if invocations[0] != expected_argv:
            return _runner_gate_smoke_failed(
                "runner smoke validator argv differed from expected gate arguments",
                failure_kind="argv_mismatch",
                invocation_count=invocation_count,
                returncode=completed.returncode,
                expected_argv=expected_audit_argv,
                observed_argv=observed_audit_argv,
                observed_invocations=observed_audit_invocations,
            )
        return {
            "status": "passed",
            "validator_invocation_count": invocation_count,
            "argv_matches_expected": True,
            "error": None,
            "failure_kind": "none",
            "returncode": completed.returncode,
            "expected_argv": expected_audit_argv,
            "observed_argv": observed_audit_argv,
            "observed_invocations": observed_audit_invocations,
            "argv_diff": [],
        }


def _runner_target_filter_runtime_contract(
    runner_path: Path,
    expected_targets: Mapping[str, Any],
    *,
    manifest_path: Path,
    manifest_sha256: str,
    require_safety_defaults: bool,
) -> Dict[str, Any]:
    with tempfile.TemporaryDirectory(prefix="phase3-lane-target-smoke-") as tmp_name:
        tmp = Path(tmp_name)
        stub_dir = tmp / "bin"
        stub_dir.mkdir()
        invocation_log = tmp / "matrix-invocations.jsonl"
        _write_runner_matrix_smoke_bash_stub(stub_dir / "bash", invocation_log)
        stub_python = tmp / "validator_python"
        _write_runner_smoke_python_stub(stub_python, tmp / "validator-invocations.jsonl")
        env = _runner_smoke_environment(
            runner_path,
            tmp,
            stub_dir,
            stub_python,
            manifest_path=manifest_path,
            manifest_sha256=manifest_sha256,
        )
        expected_contract = _expected_runner_target_runtime_contract(
            expected_targets,
            require_safety_defaults=require_safety_defaults,
        )
        try:
            completed = subprocess.run(
                [_bash_executable(), str(runner_path)],
                cwd=str(runner_path.parent),
                env=env,
                text=True,
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
                timeout=RUNNER_GATE_SMOKE_TIMEOUT_SECONDS,
                check=False,
            )
        except (OSError, subprocess.TimeoutExpired) as exc:
            return _runner_target_runtime_failed(
                f"runner target runtime smoke execution failed: {exc}",
                failure_kind="execution_error",
                expected_contract=expected_contract,
            )
        try:
            invocations = _read_runner_matrix_smoke_invocations(invocation_log)
        except ValueError as exc:
            return _runner_target_runtime_failed(
                f"runner target runtime smoke invocation log was invalid: {exc}",
                failure_kind="invalid_invocation_log",
                expected_contract=expected_contract,
                returncode=completed.returncode,
            )
        invocation_count = len(invocations)
        observed_contracts = [
            _observed_runner_target_runtime_contract(invocation, env, runner_path)
            for invocation in invocations
        ]
        observed_contract = observed_contracts[0] if observed_contracts else {}
        contract_matches_expected = (
            invocation_count == 1
            and expected_contract is not None
            and observed_contract == expected_contract
        )
        if completed.returncode != 0:
            return _runner_target_runtime_failed(
                f"runner target runtime smoke execution failed: returncode={completed.returncode}",
                failure_kind="nonzero_exit",
                invocation_count=invocation_count,
                contract_matches_expected=contract_matches_expected,
                returncode=completed.returncode,
                expected_contract=expected_contract,
                observed_contract=observed_contract,
                observed_invocations=observed_contracts,
            )
        if invocation_count != 1:
            return _runner_target_runtime_failed(
                f"runner target runtime smoke matrix invocation count was {invocation_count}",
                failure_kind="matrix_invocation_count",
                invocation_count=invocation_count,
                returncode=completed.returncode,
                expected_contract=expected_contract,
                observed_contract=observed_contract,
                observed_invocations=observed_contracts,
            )
        if expected_contract is None:
            return _runner_target_runtime_failed(
                "runner target runtime expected contract was unavailable",
                failure_kind="expected_contract_unavailable",
                invocation_count=invocation_count,
                returncode=completed.returncode,
                expected_contract=None,
                observed_contract=observed_contract,
                observed_invocations=observed_contracts,
            )
        if observed_contract != expected_contract:
            return _runner_target_runtime_failed(
                "runner target runtime contract differed from expected target filter",
                failure_kind="contract_mismatch",
                invocation_count=invocation_count,
                returncode=completed.returncode,
                expected_contract=expected_contract,
                observed_contract=observed_contract,
                observed_invocations=observed_contracts,
            )
        return {
            "status": "passed",
            "invocation_count": invocation_count,
            "contract_matches_expected": True,
            "error": None,
            "failure_kind": "none",
            "returncode": completed.returncode,
            "expected_contract": expected_contract,
            "observed_contract": observed_contract,
            "observed_invocations": observed_contracts,
            "contract_diff": [],
        }


def _runner_target_runtime_failed(
    error: str,
    *,
    failure_kind: str,
    invocation_count: int = 0,
    contract_matches_expected: bool = False,
    returncode: Any = MISSING_SENTINEL,
    expected_contract: Optional[Mapping[str, Any]] = None,
    observed_contract: Optional[Mapping[str, Any]] = None,
    observed_invocations: Optional[Sequence[Mapping[str, Any]]] = None,
) -> Dict[str, Any]:
    expected = dict(expected_contract or {})
    observed = dict(observed_contract or {})
    return {
        "status": "failed",
        "invocation_count": invocation_count,
        "contract_matches_expected": contract_matches_expected,
        "error": error,
        "failure_kind": failure_kind,
        "returncode": returncode,
        "expected_contract": expected,
        "observed_contract": observed,
        "observed_invocations": [dict(item) for item in observed_invocations or ()],
        "contract_diff": _mapping_diff(expected, observed),
    }


def _runner_target_runtime_contract_consistency(lane: Mapping[str, Any]) -> Dict[str, Any]:
    expected = lane.get("runner_target_filter_runtime_expected_contract")
    observed = lane.get("runner_target_filter_runtime_observed_contract")
    stored_diff = lane.get("runner_target_filter_runtime_contract_diff")
    observed_invocations = lane.get("runner_target_filter_runtime_observed_invocations")
    invocation_count = lane.get("runner_target_filter_runtime_invocation_count")

    expected_is_mapping = isinstance(expected, Mapping)
    observed_is_mapping = isinstance(observed, Mapping)
    stored_diff_is_list = isinstance(stored_diff, list)
    observed_invocations_is_list = isinstance(observed_invocations, list)

    computed_diff = (
        _mapping_diff(expected, observed)
        if expected_is_mapping and observed_is_mapping
        else []
    )
    observed_invocation_count = (
        len(observed_invocations) if observed_invocations_is_list else MISSING_SENTINEL
    )
    if observed_invocations_is_list and observed_invocations:
        first_observed_invocation = observed_invocations[0]
    else:
        first_observed_invocation = {}
    first_observed_invocation_matches = (
        observed_is_mapping
        and isinstance(first_observed_invocation, Mapping)
        and first_observed_invocation == observed
    )
    expected_equals_observed = (
        expected == observed if expected_is_mapping and observed_is_mapping else False
    )
    ok = (
        expected_is_mapping
        and observed_is_mapping
        and stored_diff_is_list
        and observed_invocations_is_list
        and stored_diff == computed_diff
        and observed_invocation_count == invocation_count
        and first_observed_invocation_matches
    )
    return {
        "ok": ok,
        "expected_is_mapping": expected_is_mapping,
        "observed_is_mapping": observed_is_mapping,
        "stored_diff_is_list": stored_diff_is_list,
        "observed_invocations_is_list": observed_invocations_is_list,
        "stored_diff": stored_diff if stored_diff_is_list else MISSING_SENTINEL,
        "computed_diff": computed_diff,
        "observed_invocation_count": observed_invocation_count,
        "reported_invocation_count": invocation_count,
        "first_observed_invocation_matches": first_observed_invocation_matches,
        "expected_equals_observed": expected_equals_observed,
    }


def _runner_gate_smoke_failed(
    error: str,
    *,
    failure_kind: str,
    invocation_count: int = 0,
    argv_matches_expected: bool = False,
    returncode: Any = MISSING_SENTINEL,
    expected_argv: Optional[Sequence[str]] = None,
    observed_argv: Optional[Sequence[str]] = None,
    observed_invocations: Optional[Sequence[Sequence[str]]] = None,
) -> Dict[str, Any]:
    return {
        "status": "failed",
        "validator_invocation_count": invocation_count,
        "argv_matches_expected": argv_matches_expected,
        "error": error,
        "failure_kind": failure_kind,
        "returncode": returncode,
        "expected_argv": list(expected_argv or ()),
        "observed_argv": list(observed_argv or ()),
        "observed_invocations": [list(argv) for argv in observed_invocations or ()],
        "argv_diff": _argv_diff(expected_argv or (), observed_argv or ()),
    }


def _argv_diff(expected: Sequence[str], observed: Sequence[str]) -> list[Dict[str, Any]]:
    expected_values = [str(item) for item in expected]
    observed_values = [str(item) for item in observed]
    diff: list[Dict[str, Any]] = []
    for index in range(max(len(expected_values), len(observed_values))):
        expected_value = expected_values[index] if index < len(expected_values) else MISSING_SENTINEL
        observed_value = observed_values[index] if index < len(observed_values) else MISSING_SENTINEL
        if expected_value == observed_value:
            continue
        diff.append(
            {
                "index": index,
                "expected": expected_value,
                "observed": observed_value,
            }
        )
    return diff


def _mapping_diff(expected: Mapping[str, Any], observed: Mapping[str, Any]) -> list[Dict[str, Any]]:
    diff: list[Dict[str, Any]] = []
    keys = sorted(set(expected) | set(observed))
    for key in keys:
        expected_value = expected.get(key, MISSING_SENTINEL)
        observed_value = observed.get(key, MISSING_SENTINEL)
        if expected_value == observed_value:
            continue
        diff.append(
            {
                "key": key,
                "expected": expected_value,
                "observed": observed_value,
            }
        )
    return diff


def _write_runner_smoke_stub(path: Path) -> None:
    path.write_text("#!/bin/sh\nexit 0\n", encoding="utf-8")
    path.chmod(0o755)


def _write_runner_matrix_smoke_bash_stub(path: Path, invocation_log: Path) -> None:
    matrix_scripts = (
        "func_call_run_matrix_all_parallel_multifunc.sh",
        "loop_run_matrix_all_parallel_multifunc.sh",
    )
    env_keys = (
        "FUNCTION_CALL_TARGET_SET",
        "LOOP_TARGET_SET",
        "FUNCTION_CALL_PAIR_FILTER",
        "LOOP_PAIR_FILTER",
        "BASE_PATH",
        "OUTPUT_BASE_DIR",
        "BASELINE_FUNCTION_CALL_LOG_ROOT",
        "BASELINE_LOOP_LOG_ROOT",
        "VALIDATION_RUNNER_DRY_RUN",
    )
    path.write_text(
        f"#!{sys.executable}\n"
        "import json\n"
        "import os\n"
        "import sys\n"
        "from pathlib import Path\n"
        f"matrix_scripts = {matrix_scripts!r}\n"
        f"env_keys = {env_keys!r}\n"
        f"invocation_log = {str(invocation_log)!r}\n"
        "argv = sys.argv[1:]\n"
        "script = next((arg for arg in argv if Path(arg).name in matrix_scripts), None)\n"
        "if script is not None:\n"
        "    payload = {\n"
        "        'argv': argv,\n"
        "        'script': script,\n"
        "        'env': {key: os.environ.get(key) for key in env_keys},\n"
        "    }\n"
        "    with open(invocation_log, 'a', encoding='utf-8') as handle:\n"
        "        json.dump(payload, handle, sort_keys=True)\n"
        "        handle.write('\\n')\n"
        "    sys.exit(0)\n"
        "real_bash = os.environ.get('PHASE3_REAL_BASH')\n"
        "if not real_bash:\n"
        "    sys.exit(127)\n"
        "os.execv(real_bash, [real_bash, *argv])\n",
        encoding="utf-8",
    )
    path.chmod(0o755)


def _write_runner_smoke_python_stub(path: Path, invocation_log: Path) -> None:
    path.write_text(
        f"#!{sys.executable}\n"
        "import json\n"
        "import sys\n"
        f"with open({str(invocation_log)!r}, 'a', encoding='utf-8') as handle:\n"
        "    json.dump(sys.argv[1:], handle)\n"
        "    handle.write('\\n')\n",
        encoding="utf-8",
    )
    path.chmod(0o755)


def _read_runner_matrix_smoke_invocations(invocation_log: Path) -> list[Dict[str, Any]]:
    if not invocation_log.exists():
        return []
    invocations: list[Dict[str, Any]] = []
    for raw in invocation_log.read_text(encoding="utf-8").splitlines():
        loaded = json.loads(raw)
        if not isinstance(loaded, Mapping):
            raise ValueError("non-object matrix invocation record")
        argv = loaded.get("argv")
        env = loaded.get("env")
        script = loaded.get("script")
        if not isinstance(argv, list) or not all(isinstance(item, str) for item in argv):
            raise ValueError("non-string matrix argv record")
        if not isinstance(script, str):
            raise ValueError("missing matrix script record")
        if not isinstance(env, Mapping):
            raise ValueError("missing matrix env record")
        if not all(value is None or isinstance(value, str) for value in env.values()):
            raise ValueError("non-string matrix env record")
        invocations.append(
            {
                "argv": argv,
                "script": script,
                "env": dict(env),
            }
        )
    return invocations


def _read_runner_smoke_invocations(invocation_log: Path) -> list[list[str]]:
    if not invocation_log.exists():
        return []
    invocations: list[list[str]] = []
    for raw in invocation_log.read_text(encoding="utf-8").splitlines():
        loaded = json.loads(raw)
        if not isinstance(loaded, list) or not all(isinstance(item, str) for item in loaded):
            raise ValueError("non-string argv record")
        invocations.append(loaded)
    return invocations


def _expected_runner_smoke_argv(
    validator_module: str,
    gate_args: Sequence[str],
    include_require_ready: bool,
    env: Mapping[str, str],
) -> Optional[list[str]]:
    if validator_module == MISSING_SENTINEL:
        return None
    argv = ["-m", validator_module]
    for raw in gate_args:
        parsed = _split_static_gate_arg(raw)
        if parsed is None:
            return None
        flag, value = parsed
        argv.extend([flag, _resolve_runner_smoke_gate_value(value, env)])
    if include_require_ready:
        argv.append("--require-ready")
    return argv


def _expected_runner_target_runtime_contract(
    expected_targets: Mapping[str, Any],
    *,
    require_safety_defaults: bool,
) -> Optional[Dict[str, Any]]:
    category = expected_targets.get("category")
    if category not in {"function_call", "loop"}:
        return None
    target_var = _expected_target_var(str(category))
    pair_filter_var = expected_targets.get("pair_filter_var")
    baseline_var = expected_targets.get("baseline_log_root_var")
    if (
        target_var == MISSING_SENTINEL
        or pair_filter_var == MISSING_SENTINEL
        or baseline_var == MISSING_SENTINEL
    ):
        return None
    return {
        "category": str(category),
        "matrix_script_relpath": str(expected_targets.get("matrix_script_relpath") or MISSING_SENTINEL),
        "target_var": target_var,
        "target_set": ",".join(str(item) for item in expected_targets.get("target_functions") or ()),
        "pair_filter_var": str(pair_filter_var),
        "pair_filter": ",".join(str(item) for item in expected_targets.get("pair_filter") or ()),
        "base_path_relpath": str(expected_targets.get("base_path_relpath") or MISSING_SENTINEL),
        "current_log_root": f"{category}=$OUTPUT_BASE_DIR",
        "baseline_log_root": f"{category}=${baseline_var}",
        "validation_runner_dry_run": (
            EXPECTED_RUNNER_SAFETY_DEFAULTS["VALIDATION_RUNNER_DRY_RUN"]
            if require_safety_defaults
            else MISSING_SENTINEL
        ),
    }


def _observed_runner_target_runtime_contract(
    invocation: Mapping[str, Any],
    smoke_env: Mapping[str, str],
    runner_path: Path,
) -> Dict[str, Any]:
    env = invocation.get("env") if isinstance(invocation.get("env"), Mapping) else {}
    script = str(invocation.get("script") or "")
    script_relpath = _normalize_runner_path_relpath(script, runner_path.parent)
    category = _category_for_matrix_script(script_relpath)
    target_var = _expected_target_var(category)
    pair_filter_var = _expected_pair_filter_var(category)
    baseline_var = _expected_baseline_log_root_var(category)
    target_set = _runtime_env_value(env, target_var)
    pair_filter = _runtime_env_value(env, pair_filter_var)
    base_path = _runtime_env_value(env, "BASE_PATH")
    current_log_root_value = _normalize_runtime_env_value(
        _runtime_env_value(env, "OUTPUT_BASE_DIR"),
        smoke_env,
    )
    baseline_log_root_value = _normalize_runtime_env_value(
        _runtime_env_value(env, baseline_var),
        smoke_env,
    )
    return {
        "category": category,
        "matrix_script_relpath": script_relpath,
        "target_var": target_var,
        "target_set": target_set,
        "pair_filter_var": pair_filter_var,
        "pair_filter": pair_filter,
        "base_path_relpath": _normalize_runner_path_relpath(base_path, runner_path.parent),
        "current_log_root": (
            f"{category}={current_log_root_value}"
            if category != MISSING_SENTINEL and current_log_root_value != MISSING_SENTINEL
            else MISSING_SENTINEL
        ),
        "baseline_log_root": (
            f"{category}={baseline_log_root_value}"
            if category != MISSING_SENTINEL and baseline_log_root_value != MISSING_SENTINEL
            else MISSING_SENTINEL
        ),
        "validation_runner_dry_run": _runtime_env_value(env, "VALIDATION_RUNNER_DRY_RUN"),
    }


def _runtime_env_value(env: Mapping[str, Any], key: str) -> str:
    if key == MISSING_SENTINEL:
        return MISSING_SENTINEL
    value = env.get(key)
    return str(value) if value is not None else MISSING_SENTINEL


def _normalize_runner_path_relpath(value: str, repo: Path) -> str:
    if not value or value == MISSING_SENTINEL:
        return MISSING_SENTINEL
    path = Path(value)
    if path.is_absolute():
        try:
            return path.relative_to(repo).as_posix()
        except ValueError:
            return str(path)
    return value


def _normalize_runtime_env_value(value: str, smoke_env: Mapping[str, str]) -> str:
    if not value or value == MISSING_SENTINEL:
        return MISSING_SENTINEL
    for name, replacement in sorted(smoke_env.items(), key=lambda item: len(item[1]), reverse=True):
        if not replacement:
            continue
        if value == replacement:
            return f"${name}"
    return value


def _category_for_matrix_script(script_relpath: str) -> str:
    if Path(script_relpath).name == "func_call_run_matrix_all_parallel_multifunc.sh":
        return "function_call"
    if Path(script_relpath).name == "loop_run_matrix_all_parallel_multifunc.sh":
        return "loop"
    return MISSING_SENTINEL


def _expected_runner_smoke_audit_argv(
    validator_module: str,
    gate_args: Sequence[str],
    include_require_ready: bool,
) -> list[str]:
    if validator_module == MISSING_SENTINEL:
        return []
    argv = ["-m", validator_module]
    for raw in gate_args:
        parsed = _split_static_gate_arg(raw)
        if parsed is None:
            return []
        flag, value = parsed
        argv.extend([flag, value])
    if include_require_ready:
        argv.append("--require-ready")
    return argv


def _resolve_runner_smoke_gate_value(value: str, env: Mapping[str, str]) -> str:
    resolved = value
    for name in sorted(_RUNNER_SMOKE_GATE_VALUE_ENV_KEYS, key=len, reverse=True):
        replacement = env.get(name)
        if replacement is None:
            continue
        resolved = resolved.replace("${" + name + "}", replacement)
        resolved = resolved.replace("$" + name, replacement)
    return resolved


def _normalize_runner_smoke_argv(argv: Sequence[str], env: Mapping[str, str]) -> list[str]:
    normalized = [str(item) for item in argv]
    replacements = [
        (value, f"${name}")
        for name in _RUNNER_SMOKE_GATE_VALUE_ENV_KEYS
        for value in (env.get(name),)
        if value
    ]
    for value, placeholder in sorted(replacements, key=lambda item: len(item[0]), reverse=True):
        normalized = [item.replace(value, placeholder) for item in normalized]
    return normalized


_RUNNER_SMOKE_GATE_VALUE_ENV_KEYS = (
    "BASELINE_FUNCTION_CALL_LOG_ROOT",
    "BASELINE_LOOP_LOG_ROOT",
    "PHASE1_FUNCTION_CALL_LOG_ROOT",
    "PHASE1_LOOP_LOG_ROOT",
    "PHASE3_MANIFEST_SHA256",
    "PHASE3_GATE_OUTPUT_DIR",
    "PHASE3_MANIFEST_PATH",
    "BASELINE_RAW_DIR",
    "OUTPUT_BASE_DIR",
    "PHASE1_DIR",
)


def _runner_smoke_environment(
    runner_path: Path,
    tmp: Path,
    stub_dir: Path,
    stub_python: Path,
    *,
    manifest_path: Optional[Path] = None,
    manifest_sha256: Optional[str] = None,
) -> Dict[str, str]:
    env = dict(os.environ)
    for key in (
        *EXPECTED_RUNNER_SAFETY_DEFAULTS,
        *_RUNNER_TARGET_FILTER_ASSIGNMENT_VARS,
        "PYTHON_BIN",
        "SCRIPT_DIR",
        "OUTPUT_BASE_DIR",
        "PHASE3_GATE_OUTPUT_DIR",
        "RUNNER_TMP_ROOT",
        "BASELINE_RAW_DIR",
        "BASELINE_FUNCTION_CALL_LOG_ROOT",
        "BASELINE_LOOP_LOG_ROOT",
        "PHASE1_FUNCTION_CALL_LOG_ROOT",
        "PHASE1_LOOP_LOG_ROOT",
        "PHASE1_DIR",
        "PHASE3_MANIFEST_PATH",
        "PHASE3_MANIFEST_SHA256",
        "PARALLEL_JOBS",
    ):
        env.pop(key, None)
    env["PATH"] = f"{stub_dir}{os.pathsep}{os.environ.get('PATH', '')}"
    env["PHASE3_REAL_BASH"] = _bash_executable()
    env["PYTHON_BIN"] = str(stub_python)
    env["SCRIPT_DIR"] = str(runner_path.parent)
    env["OUTPUT_BASE_DIR"] = str(tmp / "output")
    env["PHASE3_GATE_OUTPUT_DIR"] = str(tmp / "gate")
    env["RUNNER_TMP_ROOT"] = str(tmp / "runner_tmp")
    env["BASELINE_RAW_DIR"] = str(runner_path.parent / "artifacts" / "baselines" / BASELINE_ID / "raw")
    env["BASELINE_FUNCTION_CALL_LOG_ROOT"] = str(Path(env["BASELINE_RAW_DIR"]) / "logs" / "function_call")
    env["BASELINE_LOOP_LOG_ROOT"] = str(Path(env["BASELINE_RAW_DIR"]) / "logs" / "loop")
    env["PHASE1_DIR"] = str(runner_path.parent / "artifacts" / "baselines" / BASELINE_ID / "phase1")
    env["PHASE1_FUNCTION_CALL_LOG_ROOT"] = str(runner_path.parent / "logs" / "equivalence_all" / "function_call_test")
    env["PHASE1_LOOP_LOG_ROOT"] = str(runner_path.parent / "logs" / "equivalence_all" / "loop_method_b_test")
    if manifest_path is not None:
        env["PHASE3_MANIFEST_PATH"] = str(manifest_path)
    else:
        refs = _runner_manifest_refs(runner_path)
        if refs["manifest_relpath"] != MISSING_SENTINEL:
            env["PHASE3_MANIFEST_PATH"] = str(runner_path.parent / refs["manifest_relpath"])
        else:
            env["PHASE3_MANIFEST_PATH"] = str(tmp / "phase3_manifest.json")
    if manifest_sha256 is not None:
        env["PHASE3_MANIFEST_SHA256"] = str(manifest_sha256)
    else:
        refs = _runner_manifest_refs(runner_path)
        if refs["manifest_sha256"] != MISSING_SENTINEL:
            env["PHASE3_MANIFEST_SHA256"] = str(refs["manifest_sha256"])
        else:
            env["PHASE3_MANIFEST_SHA256"] = "0" * 64
    return env


def _bash_executable() -> str:
    for candidate in ("/bin/bash", "/usr/bin/bash"):
        if Path(candidate).exists():
            return candidate
    return "bash"


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
        "target_var": _expected_target_var(category),
        "pair_filter_var": _expected_pair_filter_var(category),
        "base_path_relpath": _expected_base_path_relpath(category),
        "matrix_script_relpath": _expected_matrix_script_relpath(category),
        "current_log_root_category": category,
        "current_log_root_var": "OUTPUT_BASE_DIR" if category in {"function_call", "loop"} else MISSING_SENTINEL,
        "baseline_log_root_category": category,
        "baseline_log_root_var": _expected_baseline_log_root_var(category),
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
        "current_log_root_category": MISSING_SENTINEL,
        "current_log_root_var": MISSING_SENTINEL,
        "baseline_log_root_category": MISSING_SENTINEL,
        "baseline_log_root_var": MISSING_SENTINEL,
        "target_filter_counts": {
            "target_set": 0,
            "pair_filter": 0,
            "base_path": 0,
            "matrix_script": 0,
            "invalid_mutations": 0,
        },
        "target_filter_invalid_mutations": [],
        "target_filter_invalid_mutation_count": 0,
        "log_root_arg_counts": {
            "current_log_root": 0,
            "baseline_log_root": 0,
        },
        "target_functions": [],
        "pair_filter": [],
    }


def _expected_target_var(category: str) -> str:
    if category == "function_call":
        return "FUNCTION_CALL_TARGET_SET"
    if category == "loop":
        return "LOOP_TARGET_SET"
    return MISSING_SENTINEL


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


def _expected_baseline_log_root_var(category: str) -> str:
    if category == "function_call":
        return "BASELINE_FUNCTION_CALL_LOG_ROOT"
    if category == "loop":
        return "BASELINE_LOOP_LOG_ROOT"
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
