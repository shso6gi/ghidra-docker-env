# -*- coding: utf-8 -*-
"""Build a fixed index over Phase 3 post-fix gate artifacts."""

from __future__ import annotations

import argparse
import hashlib
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
OBLIGATION_COUNT_KEYS: Sequence[str] = (
    "pending_proof_entry_count",
    "pending_proof_obligation_count",
    "pending_retry_entry_count",
    "pending_retry_obligation_count",
)


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
    expected_post_fix_obligation_counts: Optional[Mapping[str, int]] = None
    expected_post_fix_entry_identities: Sequence[Mapping[str, str]] = ()
    expected_post_fix_entry_states: Sequence[Mapping[str, Any]] = ()
    expected_required_completion_action_hashes: Sequence[Mapping[str, str]] = ()
    expected_post_fix_summary_source: str = "post_fix_regression_gate"


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
        allowed_post_fix_statuses=(
            "completed_recovery",
            "completed_recovery_with_operational_unknown",
            "pending_proof",
        ),
        expected_post_fix_status_counts={
            "completed_recovery": 1,
            "completed_recovery_with_operational_unknown": 1,
        },
        expected_post_fix_obligation_counts={
            "pending_proof_entry_count": 0,
            "pending_proof_obligation_count": 0,
            "pending_retry_entry_count": 0,
            "pending_retry_obligation_count": 0,
        },
        expected_post_fix_entry_identities=(
            {
                "id": "representative-return-coverage-gap-recursive-simple",
                "function": "fc_recursive_sum",
                "binary_pair": "B11_B15",
            },
            {
                "id": "representative-return-coverage-gap-even-both-sides",
                "function": "fc_is_even",
                "binary_pair": "B11_B12",
            },
        ),
        expected_post_fix_entry_states=(
            {
                "id": "representative-return-coverage-gap-recursive-simple",
                "function": "fc_recursive_sum",
                "binary_pair": "B11_B15",
                "post_fix_status": "completed_recovery",
                "pending_proof_obligation_count": 0,
                "pending_retry_obligation_count": 0,
                "required_completion_action_count": 0,
            },
            {
                "id": "representative-return-coverage-gap-even-both-sides",
                "function": "fc_is_even",
                "binary_pair": "B11_B12",
                "post_fix_status": "completed_recovery_with_operational_unknown",
                "pending_proof_obligation_count": 0,
                "pending_retry_obligation_count": 0,
                "required_completion_action_count": 0,
            },
        ),
        expected_required_completion_action_hashes=(
            {
                "id": "representative-return-coverage-gap-recursive-simple",
                "required_completion_actions_sha256": (
                    "4f53cda18c2baa0c0354bb5f9a3ecbe5ed12ab4d8e11ba873c2f11161202b945"
                ),
            },
            {
                "id": "representative-return-coverage-gap-even-both-sides",
                "required_completion_actions_sha256": (
                    "4f53cda18c2baa0c0354bb5f9a3ecbe5ed12ab4d8e11ba873c2f11161202b945"
                ),
            },
        ),
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
        expected_post_fix_status_counts={"completed_recovery": 1},
        expected_post_fix_obligation_counts={
            "pending_proof_entry_count": 0,
            "pending_proof_obligation_count": 0,
            "pending_retry_entry_count": 0,
            "pending_retry_obligation_count": 0,
        },
        expected_post_fix_entry_identities=(
            {
                "id": "representative-return-width-bridge-apply-indirect-width-high-bit-near-miss",
                "function": "fc_apply_indirect",
                "binary_pair": "B10_B13",
            },
        ),
        expected_post_fix_entry_states=(
            {
                "id": "representative-return-width-bridge-apply-indirect-width-high-bit-near-miss",
                "function": "fc_apply_indirect",
                "binary_pair": "B10_B13",
                "post_fix_status": "completed_recovery",
                "pending_proof_obligation_count": 0,
                "pending_retry_obligation_count": 0,
                "required_completion_action_count": 0,
            },
        ),
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
        expected_post_fix_obligation_counts={
            "pending_proof_entry_count": 1,
            "pending_proof_obligation_count": 1,
            "pending_retry_entry_count": 0,
            "pending_retry_obligation_count": 0,
        },
        expected_post_fix_entry_identities=(
            {
                "id": "representative-readonly-identity-even-index-step2-count-mismatch",
                "function": "lmb_sum_even_index_step2",
                "binary_pair": "B10_B13",
            },
        ),
        expected_post_fix_entry_states=(
            {
                "id": "representative-readonly-identity-even-index-step2-count-mismatch",
                "function": "lmb_sum_even_index_step2",
                "binary_pair": "B10_B13",
                "post_fix_status": "pending_proof",
                "pending_proof_obligation_count": 1,
                "pending_retry_obligation_count": 0,
                "required_completion_action_count": 1,
            },
        ),
        expected_required_completion_action_hashes=(
            {
                "id": "representative-readonly-identity-even-index-step2-count-mismatch",
                "required_completion_actions_sha256": (
                    "2d6d2003dead6532e894ef3c3c412a9361204e968e575268afd863b47c28029f"
                ),
            },
        ),
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
        expected_post_fix_obligation_counts={
            "pending_proof_entry_count": 1,
            "pending_proof_obligation_count": 2,
            "pending_retry_entry_count": 0,
            "pending_retry_obligation_count": 0,
        },
        expected_post_fix_entry_identities=(
            {
                "id": "representative-method-b-even-index-step2-covering-guard",
                "function": "lmb_sum_even_index_step2",
                "binary_pair": "B10_B13",
            },
        ),
        expected_post_fix_entry_states=(
            {
                "id": "representative-method-b-even-index-step2-covering-guard",
                "function": "lmb_sum_even_index_step2",
                "binary_pair": "B10_B13",
                "post_fix_status": "pending_proof",
                "pending_proof_obligation_count": 2,
                "pending_retry_obligation_count": 0,
                "required_completion_action_count": 2,
            },
        ),
        expected_required_completion_action_hashes=(
            {
                "id": "representative-method-b-even-index-step2-covering-guard",
                "required_completion_actions_sha256": (
                    "8a04d1c734b20463e67118b0d72dee8264c45563b531cb0bfe3443536e6236b3"
                ),
            },
        ),
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
        expected_post_fix_obligation_counts={
            "pending_proof_entry_count": 1,
            "pending_proof_obligation_count": 1,
            "pending_retry_entry_count": 0,
            "pending_retry_obligation_count": 0,
        },
        expected_post_fix_entry_identities=(
            {
                "id": "representative-sat-unsafety-is-even-guard",
                "function": "fc_is_even",
                "binary_pair": "B9_B10",
            },
        ),
        expected_post_fix_entry_states=(
            {
                "id": "representative-sat-unsafety-is-even-guard",
                "function": "fc_is_even",
                "binary_pair": "B9_B10",
                "post_fix_status": "pending_proof",
                "pending_proof_obligation_count": 1,
                "pending_retry_obligation_count": 0,
                "required_completion_action_count": 1,
            },
        ),
        expected_required_completion_action_hashes=(
            {
                "id": "representative-sat-unsafety-is-even-guard",
                "required_completion_actions_sha256": (
                    "d3f2bb28ea94dbf0160747c5912f084d0bde3df7967f4adb6e295944d2bb0c51"
                ),
            },
        ),
        expected_post_fix_summary_source="top_level_checks",
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
        expected_entry_count=3,
        allowed_post_fix_statuses=(
            "pending_object_evidence",
            "pending_proof",
            "proof_complete",
            "resolved_under_other_conservative_unknown",
        ),
        expected_post_fix_status_counts={"pending_proof": 3},
        expected_post_fix_obligation_counts={
            "pending_proof_entry_count": 3,
            "pending_proof_obligation_count": 24,
            "pending_retry_entry_count": 0,
            "pending_retry_obligation_count": 0,
        },
        expected_post_fix_entry_identities=(
            {
                "id": "representative-unresolved-expression-is-even-recursive-summary-current-transition",
                "function": "fc_is_even",
                "binary_pair": "B11_B12",
            },
            {
                "id": "representative-unresolved-expression-is-even-deferred-call-return-current-transition",
                "function": "fc_is_even",
                "binary_pair": "B10_B13",
            },
            {
                "id": "representative-unresolved-expression-is-odd-opaque-void-return-current-transition",
                "function": "fc_is_odd",
                "binary_pair": "B1_B2",
            },
        ),
        expected_post_fix_entry_states=(
            {
                "id": "representative-unresolved-expression-is-even-recursive-summary-current-transition",
                "function": "fc_is_even",
                "binary_pair": "B11_B12",
                "post_fix_status": "pending_proof",
                "pending_proof_obligation_count": 14,
                "pending_retry_obligation_count": 0,
                "required_completion_action_count": 14,
            },
            {
                "id": "representative-unresolved-expression-is-even-deferred-call-return-current-transition",
                "function": "fc_is_even",
                "binary_pair": "B10_B13",
                "post_fix_status": "pending_proof",
                "pending_proof_obligation_count": 8,
                "pending_retry_obligation_count": 0,
                "required_completion_action_count": 8,
            },
            {
                "id": "representative-unresolved-expression-is-odd-opaque-void-return-current-transition",
                "function": "fc_is_odd",
                "binary_pair": "B1_B2",
                "post_fix_status": "pending_proof",
                "pending_proof_obligation_count": 2,
                "pending_retry_obligation_count": 0,
                "required_completion_action_count": 2,
            },
        ),
        expected_required_completion_action_hashes=(
            {
                "id": "representative-unresolved-expression-is-even-recursive-summary-current-transition",
                "required_completion_actions_sha256": (
                    "27312a6f83dc29b3fdb787cac2b283fed98a934dd0bc2feaa8283522eca2783f"
                ),
            },
            {
                "id": "representative-unresolved-expression-is-even-deferred-call-return-current-transition",
                "required_completion_actions_sha256": (
                    "c25c782c296a181d96a80f43260a29b03758700625fbdbb6662ea028fddeff8a"
                ),
            },
            {
                "id": "representative-unresolved-expression-is-odd-opaque-void-return-current-transition",
                "required_completion_actions_sha256": (
                    "c41aa1f18262cb9c63cf66337635b2e0e1b5d69688320f93a5a2273254f47a5a"
                ),
            },
        ),
        expected_post_fix_summary_source="top_level_checks",
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
        expected_post_fix_obligation_counts={
            "pending_proof_entry_count": 0,
            "pending_proof_obligation_count": 0,
            "pending_retry_entry_count": 0,
            "pending_retry_obligation_count": 0,
        },
        expected_post_fix_entry_identities=(
            {
                "id": "representative-solver-rewrite-no-change-prefix-loop-mips64",
                "function": "lmb_sum_prefix_loop",
                "binary_pair": "B12_B16",
            },
        ),
        expected_post_fix_entry_states=(
            {
                "id": "representative-solver-rewrite-no-change-prefix-loop-mips64",
                "function": "lmb_sum_prefix_loop",
                "binary_pair": "B12_B16",
                "post_fix_status": "retired_to_return_coverage_gap",
                "pending_proof_obligation_count": 0,
                "pending_retry_obligation_count": 0,
                "required_completion_action_count": 2,
            },
        ),
        expected_required_completion_action_hashes=(
            {
                "id": "representative-solver-rewrite-no-change-prefix-loop-mips64",
                "required_completion_actions_sha256": (
                    "fb8682c6f35dcef799f2c2992e9076620694434fdc28411284599fe84ba2f45e"
                ),
            },
        ),
        expected_post_fix_summary_source="top_level_checks",
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
        expected_post_fix_obligation_counts={
            "pending_proof_entry_count": 0,
            "pending_proof_obligation_count": 0,
            "pending_retry_entry_count": 0,
            "pending_retry_obligation_count": 0,
        },
        expected_post_fix_entry_identities=(
            {
                "id": "representative-solver-rewrite-proof-retired-to-sat-unsafety-recursive-sum-arm64-mips64",
                "function": "fc_recursive_sum",
                "binary_pair": "B8_B10",
            },
        ),
        expected_post_fix_entry_states=(
            {
                "id": "representative-solver-rewrite-proof-retired-to-sat-unsafety-recursive-sum-arm64-mips64",
                "function": "fc_recursive_sum",
                "binary_pair": "B8_B10",
                "post_fix_status": "retired_to_sat_unsafety",
                "pending_proof_obligation_count": 0,
                "pending_retry_obligation_count": 0,
                "required_completion_action_count": 0,
            },
        ),
        expected_required_completion_action_hashes=(
            {
                "id": (
                    "representative-solver-rewrite-proof-retired-to-sat-unsafety-"
                    "recursive-sum-arm64-mips64"
                ),
                "required_completion_actions_sha256": (
                    "4f53cda18c2baa0c0354bb5f9a3ecbe5ed12ab4d8e11ba873c2f11161202b945"
                ),
            },
        ),
        expected_post_fix_summary_source="top_level_checks",
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
        expected_post_fix_obligation_counts={
            "pending_proof_entry_count": 0,
            "pending_proof_obligation_count": 0,
            "pending_retry_entry_count": 1,
            "pending_retry_obligation_count": 1,
        },
        expected_post_fix_entry_identities=(
            {
                "id": "representative-solver-timeout-long-branch-dispatch-arm64-mips64",
                "function": "fc_long_branch_dispatch",
                "binary_pair": "B8_B9",
            },
        ),
        expected_post_fix_entry_states=(
            {
                "id": "representative-solver-timeout-long-branch-dispatch-arm64-mips64",
                "function": "fc_long_branch_dispatch",
                "binary_pair": "B8_B9",
                "post_fix_status": "pending_retry",
                "pending_proof_obligation_count": 0,
                "pending_retry_obligation_count": 1,
                "required_completion_action_count": 1,
            },
        ),
        expected_required_completion_action_hashes=(
            {
                "id": "representative-solver-timeout-long-branch-dispatch-arm64-mips64",
                "required_completion_actions_sha256": (
                    "bc2ac85998b5f5a256775da724b4a5375b8db60521cd2ed9248ce6ce03537b30"
                ),
            },
        ),
    ),
)


def build_phase3_post_fix_gate_index(
    *,
    repo_root: Path,
    output_dir: Path,
    gate_specs: Sequence[Phase3PostFixGateSpec] = DEFAULT_PHASE3_POST_FIX_GATE_SPECS,
) -> Path:
    repo = Path(repo_root).resolve()
    specs = _normalized_gate_specs(gate_specs)
    output = Path(output_dir)
    output.mkdir(parents=True, exist_ok=True)
    gates = [_materialize_post_fix_gate(repo, spec) for spec in specs]
    checks = _post_fix_index_checks(specs, gates)
    summary = _summary(checks)
    post_fix_status_counts = _post_fix_status_counts_from_gates(gates)
    expected_post_fix_status_counts = _expected_post_fix_status_counts_from_specs(specs)
    post_fix_obligation_counts = _post_fix_obligation_counts_from_gates(gates)
    expected_post_fix_obligation_counts = _expected_post_fix_obligation_counts_from_specs(specs)
    manifest = {
        "manifest_version": MANIFEST_VERSION,
        "manifest_kind": "phase3_post_fix_gate_index",
        "artifact_role": "derived_audit_post_fix_gate_index",
        "created_at": datetime.now(timezone.utc).isoformat(),
        "repo_root": str(repo),
        "phase3_post_fix_gates_ready": summary["failed"] == 0,
        "expected_post_fix_status_counts": expected_post_fix_status_counts,
        "post_fix_status_counts": post_fix_status_counts,
        "expected_post_fix_obligation_counts": expected_post_fix_obligation_counts,
        "post_fix_obligation_counts": post_fix_obligation_counts,
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
    if not isinstance(manifest, Mapping):
        raise ValueError(
            f"Phase 3 post-fix gate index failed: manifest must be an object, "
            f"got {type(manifest).__name__}"
        )
    failures: list[str] = []
    if manifest.get("manifest_kind") != "phase3_post_fix_gate_index":
        failures.append("manifest_kind")
    if manifest.get("manifest_version") != MANIFEST_VERSION:
        failures.append("manifest_version")
    if manifest.get("artifact_role") != "derived_audit_post_fix_gate_index":
        failures.append("artifact_role")
    if not _valid_created_at(manifest.get("created_at")):
        failures.append("created_at")
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
    elif not isinstance(summary_failed, int) or isinstance(summary_failed, bool):
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
        if isinstance(summary, Mapping) and not _strict_json_equal(dict(summary), computed_summary):
            failures.append("summary_consistency")

    observed_status_counts = manifest.get("post_fix_status_counts")
    if not isinstance(observed_status_counts, Mapping):
        failures.append("post_fix_status_counts")
    specs = _normalized_gate_specs(
        DEFAULT_PHASE3_POST_FIX_GATE_SPECS if gate_specs is None else gate_specs
    )
    observed_expected_status_counts = manifest.get("expected_post_fix_status_counts")
    expected_status_counts = _expected_post_fix_status_counts_from_specs(specs)
    if not isinstance(observed_expected_status_counts, Mapping):
        failures.append("expected_post_fix_status_counts")
    elif not _strict_json_equal(dict(observed_expected_status_counts), expected_status_counts):
        failures.append("expected_post_fix_status_counts")
    observed_obligation_counts = manifest.get("post_fix_obligation_counts")
    if not isinstance(observed_obligation_counts, Mapping):
        failures.append("post_fix_obligation_counts")
    observed_expected_obligation_counts = manifest.get("expected_post_fix_obligation_counts")
    expected_obligation_counts = _expected_post_fix_obligation_counts_from_specs(specs)
    if not isinstance(observed_expected_obligation_counts, Mapping):
        failures.append("expected_post_fix_obligation_counts")
    elif not _strict_json_equal(dict(observed_expected_obligation_counts), expected_obligation_counts):
        failures.append("expected_post_fix_obligation_counts")

    gates = manifest.get("gates")
    if not isinstance(gates, (list, tuple)):
        failures.append("gates")
    else:
        computed_status_counts = _post_fix_status_counts_from_gates(gates)
        if (
            isinstance(observed_status_counts, Mapping)
            and not _strict_json_equal(dict(observed_status_counts), computed_status_counts)
        ):
            failures.append("post_fix_status_counts")
        computed_obligation_counts = _post_fix_obligation_counts_from_gates(gates)
        if (
            isinstance(observed_obligation_counts, Mapping)
            and not _strict_json_equal(dict(observed_obligation_counts), computed_obligation_counts)
        ):
            failures.append("post_fix_obligation_counts")
        actual_rows = _gate_spec_rows_from_gates(gates)
        expected_rows = _gate_spec_rows_from_specs(specs)
        if not _strict_json_equal(actual_rows, expected_rows):
            failures.append("gate_specs")
        derived_checks = _post_fix_index_checks(specs, gates)
        if checks_is_sequence and not _strict_json_equal(list(checks), list(derived_checks)):
            failures.append("derived_checks")
        if failed_check_kinds != _failed_check_kinds(derived_checks):
            failures.append("derived_failed_kinds")
        if not isinstance(manifest_repo_root, str) or not manifest_repo_root:
            failures.append("materialized_context_missing")
        else:
            materialized_gates = [
                _materialize_post_fix_gate(repo, spec)
                for spec in specs
            ]
            materialized_checks = _post_fix_index_checks(specs, materialized_gates)
            if not _strict_json_equal(gates, materialized_gates):
                failures.append("materialized_gates")
            if (
                isinstance(observed_status_counts, Mapping)
                and not _strict_json_equal(
                    dict(observed_status_counts),
                    _post_fix_status_counts_from_gates(materialized_gates),
                )
            ):
                failures.append("materialized_status_counts")
            if (
                isinstance(observed_obligation_counts, Mapping)
                and not _strict_json_equal(
                    dict(observed_obligation_counts),
                    _post_fix_obligation_counts_from_gates(materialized_gates),
                )
            ):
                failures.append("materialized_obligation_counts")
            if (
                isinstance(observed_expected_status_counts, Mapping)
                and not _strict_json_equal(
                    dict(observed_expected_status_counts),
                    _expected_post_fix_status_counts_from_specs(specs),
                )
            ):
                failures.append("materialized_expected_status_counts")
            if (
                isinstance(observed_expected_obligation_counts, Mapping)
                and not _strict_json_equal(
                    dict(observed_expected_obligation_counts),
                    _expected_post_fix_obligation_counts_from_specs(specs),
                )
            ):
                failures.append("materialized_expected_obligation_counts")
            if checks_is_sequence and not _strict_json_equal(list(checks), list(materialized_checks)):
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
        "expected_entry_count": _normalized_expected_entry_count(spec),
        "allowed_post_fix_statuses": _normalized_allowed_post_fix_statuses(spec),
        "expected_post_fix_summary_source": _normalized_expected_summary_source(spec),
        "expected_post_fix_entry_identities": _normalized_expected_entry_identities(spec),
        "expected_post_fix_entry_states": _normalized_expected_entry_states(spec),
        "expected_required_completion_action_hashes": (
            _normalized_expected_required_action_hashes(spec)
        ),
        "expected_post_fix_status_counts": _normalized_expected_status_counts(spec),
        "expected_post_fix_obligation_counts": _normalized_expected_obligation_counts(spec),
        "status": "missing",
        "observed_manifest_kind": MISSING_SENTINEL,
        "observed_artifact_role": MISSING_SENTINEL,
        "baseline_id": MISSING_SENTINEL,
        "baseline_git_head": MISSING_SENTINEL,
        "ready_value": MISSING_SENTINEL,
        "entry_count": MISSING_SENTINEL,
        "post_fix_invalid_entry_ids": [],
        "post_fix_duplicate_entry_ids": [],
        "post_fix_invalid_entry_metadata": [],
        "post_fix_required_completion_action_hashes": [],
        "post_fix_summary_source": MISSING_SENTINEL,
        "post_fix_summary_check_count": MISSING_SENTINEL,
        "post_fix_summary_consistency_failures": [],
        "post_fix_summary_invalid_checks": [],
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
    gate["post_fix_invalid_entry_ids"] = _post_fix_invalid_entry_ids(payload)
    gate["post_fix_duplicate_entry_ids"] = _post_fix_duplicate_entry_ids(payload)
    gate["post_fix_invalid_entry_metadata"] = _post_fix_invalid_entry_metadata(payload)
    gate["post_fix_entry_identities"] = _post_fix_entry_identities(payload)
    gate["post_fix_entry_states"] = _post_fix_entry_states(payload)
    gate["post_fix_required_completion_action_hashes"] = (
        _post_fix_required_completion_action_hashes(payload)
    )
    summary_info = _post_fix_summary_info(payload)
    gate["post_fix_summary_source"] = summary_info["source"]
    gate["post_fix_summary_check_count"] = summary_info["check_count"]
    gate["post_fix_summary_consistency_failures"] = summary_info["consistency_failures"]
    gate["post_fix_summary_invalid_checks"] = summary_info["invalid_checks"]
    gate["post_fix_summary"] = summary_info["summary"]
    gate["post_fix_status_counts"] = _post_fix_status_counts(payload)
    gate["post_fix_obligation_summary"] = _post_fix_obligation_summary(payload)
    gate["extra_current_unresolved_expression_summary"] = (
        _extra_current_unresolved_expression_summary(payload)
    )
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


def _extra_current_unresolved_expression_summary(payload: Mapping[str, Any]) -> Dict[str, Any]:
    observations = payload.get("extra_current_unresolved_expression_observations")
    if not isinstance(observations, (list, tuple)):
        observations = ()
    post_fix_summary = payload.get("post_fix_summary")
    declared_count = (
        post_fix_summary.get("extra_current_unresolved_expression_count")
        if isinstance(post_fix_summary, Mapping)
        else None
    )
    if not isinstance(declared_count, int) or isinstance(declared_count, bool):
        declared_count = len(observations)
    identities = []
    for observation in observations:
        if not isinstance(observation, Mapping):
            continue
        identities.append(
            {
                "category": observation.get("category") or MISSING_SENTINEL,
                "function": observation.get("function") or MISSING_SENTINEL,
                "binary_pair": observation.get("binary_pair") or MISSING_SENTINEL,
                "unresolved_expression_reason_record_count": (
                    observation.get("unresolved_expression_reason_record_count")
                    if isinstance(observation.get("unresolved_expression_reason_record_count"), int)
                    and not isinstance(observation.get("unresolved_expression_reason_record_count"), bool)
                    else MISSING_SENTINEL
                ),
            }
        )
    return {
        "count": declared_count,
        "observed_count": len(identities),
        "identities": sorted(identities, key=lambda item: repr(item)),
    }


def _post_fix_obligation_summary(payload: Mapping[str, Any]) -> Dict[str, Any]:
    summary = {
        "pending_proof_entry_count": 0,
        "pending_proof_obligation_count": 0,
        "pending_proof_entries_missing_required_actions": [],
        "pending_proof_entries_missing_obligations": [],
        "pending_proof_invalid_obligations": [],
        "pending_proof_duplicate_obligations": [],
        "pending_proof_duplicate_obligation_ids": [],
        "pending_proof_duplicate_obligation_ids_across_entries": [],
        "pending_proof_invalid_required_actions": [],
        "pending_proof_duplicate_required_actions": [],
        "pending_proof_duplicate_required_action_ids": [],
        "pending_proof_duplicate_required_action_ids_across_entries": [],
        "pending_proof_required_action_mismatches": [],
        "pending_retry_entry_count": 0,
        "pending_retry_obligation_count": 0,
        "pending_retry_entries_missing_required_actions": [],
        "pending_retry_entries_missing_obligations": [],
        "pending_retry_invalid_obligations": [],
        "pending_retry_duplicate_obligations": [],
        "pending_retry_duplicate_obligation_ids": [],
        "pending_retry_duplicate_obligation_ids_across_entries": [],
        "pending_retry_invalid_required_actions": [],
        "pending_retry_duplicate_required_actions": [],
        "pending_retry_duplicate_required_action_ids": [],
        "pending_retry_duplicate_required_action_ids_across_entries": [],
        "pending_retry_required_action_mismatches": [],
        "duplicate_obligation_ids_across_statuses": [],
        "duplicate_required_action_ids_across_statuses": [],
        "non_pending_entries_with_pending_obligations": [],
        "entries_with_unexpected_pending_obligations": [],
        "entries_with_unexpected_required_actions": [],
        "retired_invalid_required_actions": [],
        "retired_duplicate_required_action_ids": [],
        "retired_duplicate_required_action_ids_across_entries": [],
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
                allowed_obligation_statuses={
                    "pending_evidence",
                    "semantic_proof_required",
                    "completed_evidence_present",
                },
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
    summary["pending_proof_duplicate_obligation_ids_across_entries"] = (
        _duplicate_proof_obligation_ids_across_entries(
            entries,
            post_fix_status="pending_proof",
            value_key="pending_proof_obligations",
        )
    )
    summary["pending_retry_duplicate_obligation_ids_across_entries"] = (
        _duplicate_proof_obligation_ids_across_entries(
            entries,
            post_fix_status="pending_retry",
            value_key="pending_retry_obligations",
        )
    )
    summary["pending_proof_duplicate_required_action_ids_across_entries"] = (
        _duplicate_proof_obligation_ids_across_entries(
            entries,
            post_fix_status="pending_proof",
            value_key="required_completion_actions",
        )
    )
    summary["pending_retry_duplicate_required_action_ids_across_entries"] = (
        _duplicate_proof_obligation_ids_across_entries(
            entries,
            post_fix_status="pending_retry",
            value_key="required_completion_actions",
        )
    )
    status_obligation_keys = {
        "pending_proof": "pending_proof_obligations",
        "pending_retry": "pending_retry_obligations",
    }
    summary["duplicate_obligation_ids_across_statuses"] = (
        _duplicate_proof_obligation_ids_across_statuses(entries, status_obligation_keys)
    )
    status_action_keys = {
        "pending_proof": "required_completion_actions",
        "pending_retry": "required_completion_actions",
    }
    summary["duplicate_required_action_ids_across_statuses"] = (
        _duplicate_proof_obligation_ids_across_statuses(entries, status_action_keys)
    )
    summary["non_pending_entries_with_pending_obligations"] = (
        _non_pending_entries_with_pending_obligations(entries)
    )
    summary["entries_with_unexpected_pending_obligations"] = (
        _entries_with_unexpected_pending_obligations(entries)
    )
    summary["entries_with_unexpected_required_actions"] = (
        _entries_with_unexpected_required_actions(entries)
    )
    summary["retired_invalid_required_actions"] = _retired_invalid_required_actions(entries)
    summary["retired_duplicate_required_action_ids"] = (
        _retired_duplicate_required_action_ids(entries)
    )
    summary["retired_duplicate_required_action_ids_across_entries"] = (
        _retired_duplicate_required_action_ids_across_entries(entries)
    )
    return summary


def _post_fix_obligation_counts_from_summary(summary: Mapping[str, Any]) -> Dict[str, int]:
    return {key: _int_count(summary.get(key)) for key in OBLIGATION_COUNT_KEYS}


def _post_fix_obligation_counts_from_gates(gates: Sequence[Any]) -> Dict[str, int]:
    counts = _empty_obligation_counts()
    for gate in gates:
        if not isinstance(gate, Mapping):
            continue
        summary = gate.get("post_fix_obligation_summary")
        if not isinstance(summary, Mapping):
            continue
        gate_counts = _post_fix_obligation_counts_from_summary(summary)
        for key, value in gate_counts.items():
            counts[key] += value
    return counts


def _empty_obligation_counts() -> Dict[str, int]:
    return {key: 0 for key in OBLIGATION_COUNT_KEYS}


def _int_count(value: Any) -> int:
    return value if _is_non_negative_int_count(value) else 0


def _is_non_negative_int_count(value: Any) -> bool:
    return isinstance(value, int) and not isinstance(value, bool) and value >= 0


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
    duplicate_key = f"{status_prefix}_duplicate_obligations"
    duplicate_id_key = f"{status_prefix}_duplicate_obligation_ids"
    invalid_required_key = f"{status_prefix}_invalid_required_actions"
    duplicate_required_key = f"{status_prefix}_duplicate_required_actions"
    duplicate_required_id_key = f"{status_prefix}_duplicate_required_action_ids"
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
    duplicate_obligation_keys = _duplicate_pending_required_action_keys(obligations)
    if duplicate_obligation_keys:
        summary[duplicate_key].append(
            {
                "entry_id": entry_id,
                "duplicate_obligations": duplicate_obligation_keys,
            }
        )
    duplicate_obligation_ids = _duplicate_proof_obligation_ids(obligations)
    if duplicate_obligation_ids:
        summary[duplicate_id_key].append(
            {
                "entry_id": entry_id,
                "duplicate_proof_obligation_ids": duplicate_obligation_ids,
            }
        )
    required_actions = entry.get("required_completion_actions")
    if not isinstance(required_actions, (list, tuple)) or not required_actions:
        summary[missing_required_key].append(entry_id)
        return
    for action_index, action in enumerate(required_actions):
        if _pending_required_action_is_valid(action):
            continue
        summary[invalid_required_key].append(
            {
                "entry_id": entry_id,
                "required_action_index": action_index,
            }
        )
    required_keys = {
        _pending_obligation_required_key(action)
        for action in required_actions
        if isinstance(action, Mapping)
    }
    duplicate_required_keys = _duplicate_pending_required_action_keys(required_actions)
    if duplicate_required_keys:
        summary[duplicate_required_key].append(
            {
                "entry_id": entry_id,
                "duplicate_required_actions": duplicate_required_keys,
            }
        )
    duplicate_required_ids = _duplicate_proof_obligation_ids(required_actions)
    if duplicate_required_ids:
        summary[duplicate_required_id_key].append(
            {
                "entry_id": entry_id,
                "duplicate_proof_obligation_ids": duplicate_required_ids,
            }
        )
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
    if not _concrete_key_value(proof_obligation_id):
        return False
    if not _required_evidence_is_valid(obligation.get("required_evidence")):
        return False
    if obligation.get("completed_evidence_present") not in {True, False}:
        return False
    status = obligation.get("status")
    return isinstance(status, str) and status in allowed_obligation_statuses


def _duplicate_pending_required_action_keys(actions: Sequence[Any]) -> list[str]:
    seen: set[str] = set()
    duplicates: list[str] = []
    for action in actions:
        if not isinstance(action, Mapping):
            continue
        key = _pending_obligation_required_key(action)
        if key in seen and key not in duplicates:
            duplicates.append(key)
        seen.add(key)
    return duplicates


def _duplicate_proof_obligation_ids(values: Sequence[Any]) -> list[str]:
    seen: set[str] = set()
    duplicates: list[str] = []
    for value in values:
        if not isinstance(value, Mapping):
            continue
        proof_obligation_id = value.get("proof_obligation_id")
        if proof_obligation_id is None:
            continue
        key = _proof_obligation_id_key(proof_obligation_id)
        if key in seen and key not in duplicates:
            duplicates.append(key)
        seen.add(key)
    return duplicates


def _duplicate_proof_obligation_ids_across_entries(
    entries: Sequence[Any],
    *,
    post_fix_status: str,
    value_key: str,
) -> list[Dict[str, Any]]:
    entry_ids_by_obligation_id: Dict[str, list[str]] = {}
    for entry_index, entry in enumerate(entries):
        if not isinstance(entry, Mapping):
            continue
        if entry.get("post_fix_status") != post_fix_status:
            continue
        entry_id = str(entry.get("id") or f"entry[{entry_index}]")
        values = entry.get(value_key)
        if not isinstance(values, (list, tuple)):
            continue
        for value in values:
            if not isinstance(value, Mapping):
                continue
            proof_obligation_id = value.get("proof_obligation_id")
            if proof_obligation_id is None:
                continue
            key = _proof_obligation_id_key(proof_obligation_id)
            entry_ids = entry_ids_by_obligation_id.setdefault(key, [])
            if entry_id not in entry_ids:
                entry_ids.append(entry_id)
    return [
        {
            "proof_obligation_id": key,
            "entry_ids": entry_ids,
        }
        for key, entry_ids in sorted(entry_ids_by_obligation_id.items())
        if len(entry_ids) > 1
    ]


def _duplicate_proof_obligation_ids_across_statuses(
    entries: Sequence[Any],
    value_key_by_status: Mapping[str, str],
) -> list[Dict[str, Any]]:
    refs_by_obligation_id: Dict[str, list[Dict[str, str]]] = {}
    for entry_index, entry in enumerate(entries):
        if not isinstance(entry, Mapping):
            continue
        status = entry.get("post_fix_status")
        if not isinstance(status, str) or status not in value_key_by_status:
            continue
        entry_id = str(entry.get("id") or f"entry[{entry_index}]")
        values = entry.get(value_key_by_status[status])
        if not isinstance(values, (list, tuple)):
            continue
        for value in values:
            if not isinstance(value, Mapping):
                continue
            proof_obligation_id = value.get("proof_obligation_id")
            if proof_obligation_id is None:
                continue
            key = _proof_obligation_id_key(proof_obligation_id)
            ref = {"entry_id": entry_id, "post_fix_status": status}
            refs = refs_by_obligation_id.setdefault(key, [])
            if ref not in refs:
                refs.append(ref)
    return [
        {
            "proof_obligation_id": key,
            "refs": refs,
        }
        for key, refs in sorted(refs_by_obligation_id.items())
        if len({ref["post_fix_status"] for ref in refs}) > 1
    ]


def _non_pending_entries_with_pending_obligations(entries: Sequence[Any]) -> list[Dict[str, Any]]:
    offenders: list[Dict[str, Any]] = []
    for entry_index, entry in enumerate(entries):
        if not isinstance(entry, Mapping):
            continue
        status = entry.get("post_fix_status")
        if status in {"pending_proof", "pending_retry"}:
            continue
        pending_fields: list[str] = []
        for field_name in ("pending_proof_obligations", "pending_retry_obligations"):
            values = entry.get(field_name)
            if isinstance(values, (list, tuple)) and values:
                pending_fields.append(field_name)
        if pending_fields:
            offenders.append(
                {
                    "entry_id": str(entry.get("id") or f"entry[{entry_index}]"),
                    "post_fix_status": str(status or MISSING_SENTINEL),
                    "pending_fields": pending_fields,
                }
            )
    return offenders


def _entries_with_unexpected_pending_obligations(entries: Sequence[Any]) -> list[Dict[str, Any]]:
    offenders: list[Dict[str, Any]] = []
    unexpected_fields_by_status = {
        "pending_proof": ("pending_retry_obligations",),
        "pending_retry": ("pending_proof_obligations",),
    }
    for entry_index, entry in enumerate(entries):
        if not isinstance(entry, Mapping):
            continue
        status = entry.get("post_fix_status")
        unexpected_fields = unexpected_fields_by_status.get(status)
        if unexpected_fields is None:
            continue
        pending_fields: list[str] = []
        for field_name in unexpected_fields:
            values = entry.get(field_name)
            if isinstance(values, (list, tuple)) and values:
                pending_fields.append(field_name)
        if pending_fields:
            offenders.append(
                {
                    "entry_id": str(entry.get("id") or f"entry[{entry_index}]"),
                    "post_fix_status": str(status or MISSING_SENTINEL),
                    "pending_fields": pending_fields,
                }
            )
    return offenders


def _entries_with_unexpected_required_actions(entries: Sequence[Any]) -> list[Dict[str, str]]:
    offenders: list[Dict[str, str]] = []
    for entry_index, entry in enumerate(entries):
        if not isinstance(entry, Mapping):
            continue
        status = entry.get("post_fix_status")
        if _post_fix_status_allows_required_actions(status):
            continue
        actions = entry.get("required_completion_actions")
        if not isinstance(actions, (list, tuple)) or not actions:
            continue
        offenders.append(
            {
                "entry_id": str(entry.get("id") or f"entry[{entry_index}]"),
                "post_fix_status": str(status or MISSING_SENTINEL),
            }
        )
    return offenders


def _retired_invalid_required_actions(entries: Sequence[Any]) -> list[Dict[str, Any]]:
    invalid: list[Dict[str, Any]] = []
    for entry_index, entry in enumerate(entries):
        if not isinstance(entry, Mapping):
            continue
        status = entry.get("post_fix_status")
        if not (isinstance(status, str) and status.startswith("retired_to_")):
            continue
        actions = entry.get("required_completion_actions")
        if actions is None:
            continue
        if not isinstance(actions, (list, tuple)):
            invalid.append(
                {
                    "entry_id": str(entry.get("id") or f"entry[{entry_index}]"),
                    "post_fix_status": status,
                    "required_action_index": MISSING_SENTINEL,
                }
            )
            continue
        for action_index, action in enumerate(actions):
            if _retired_required_action_is_valid(action):
                continue
            invalid.append(
                {
                    "entry_id": str(entry.get("id") or f"entry[{entry_index}]"),
                    "post_fix_status": status,
                    "required_action_index": action_index,
                }
            )
    return invalid


def _retired_duplicate_required_action_ids(entries: Sequence[Any]) -> list[Dict[str, Any]]:
    duplicates: list[Dict[str, Any]] = []
    for entry_index, entry in enumerate(entries):
        if not isinstance(entry, Mapping):
            continue
        status = entry.get("post_fix_status")
        if not (isinstance(status, str) and status.startswith("retired_to_")):
            continue
        actions = entry.get("required_completion_actions")
        if not isinstance(actions, (list, tuple)):
            continue
        duplicate_ids = _duplicate_proof_obligation_ids(actions)
        if not duplicate_ids:
            continue
        duplicates.append(
            {
                "entry_id": str(entry.get("id") or f"entry[{entry_index}]"),
                "post_fix_status": status,
                "duplicate_proof_obligation_ids": duplicate_ids,
            }
        )
    return duplicates


def _retired_duplicate_required_action_ids_across_entries(
    entries: Sequence[Any],
) -> list[Dict[str, Any]]:
    refs_by_obligation_id: Dict[str, list[Dict[str, str]]] = {}
    for entry_index, entry in enumerate(entries):
        if not isinstance(entry, Mapping):
            continue
        status = entry.get("post_fix_status")
        if not (isinstance(status, str) and status.startswith("retired_to_")):
            continue
        entry_id = str(entry.get("id") or f"entry[{entry_index}]")
        actions = entry.get("required_completion_actions")
        if not isinstance(actions, (list, tuple)):
            continue
        for action in actions:
            if not isinstance(action, Mapping):
                continue
            proof_obligation_id = action.get("proof_obligation_id")
            if proof_obligation_id is None:
                continue
            key = _proof_obligation_id_key(proof_obligation_id)
            ref = {"entry_id": entry_id, "post_fix_status": status}
            refs = refs_by_obligation_id.setdefault(key, [])
            if ref not in refs:
                refs.append(ref)
    return [
        {
            "proof_obligation_id": key,
            "refs": refs,
        }
        for key, refs in sorted(refs_by_obligation_id.items())
        if len(refs) > 1
    ]


def _retired_required_action_is_valid(action: Any) -> bool:
    if not isinstance(action, Mapping):
        return False
    if not _specific_text(action.get("evidence_kind")):
        return False
    if not _specific_text(action.get("stage")):
        return False
    action_tuple = action.get("tuple")
    if not isinstance(action_tuple, (list, tuple)) or _contains_missing_sentinel(action_tuple):
        return False
    if len(action_tuple) < 7:
        return False
    if action_tuple[0] != "proof_action":
        return False
    if not all(_specific_text(item) for item in action_tuple[:7]):
        return False
    proof_obligation_id = action.get("proof_obligation_id")
    if not _concrete_key_value(proof_obligation_id):
        return False
    object_target_key = action.get("object_target_key")
    if not _concrete_key_value(object_target_key):
        return False
    return _required_evidence_is_valid(action.get("required_evidence"))


def _post_fix_status_allows_required_actions(status: Any) -> bool:
    return status in {"pending_proof", "pending_retry"} or (
        isinstance(status, str) and status.startswith("retired_to_")
    )


def _proof_obligation_id_key(value: Any) -> str:
    return json.dumps(value, sort_keys=True, separators=(",", ":"))


def _strict_json_equal(left: Any, right: Any) -> bool:
    try:
        return (
            json.dumps(left, sort_keys=True, separators=(",", ":"))
            == json.dumps(right, sort_keys=True, separators=(",", ":"))
        )
    except TypeError:
        return False


def _post_fix_status_counts_match_expected_or_progress(
    spec: Optional[Phase3PostFixGateSpec],
    actual: Mapping[str, Any],
    expected: Mapping[str, Any],
) -> bool:
    actual_counts = dict(sorted(actual.items())) if isinstance(actual, Mapping) else {}
    expected_counts = dict(sorted(expected.items())) if isinstance(expected, Mapping) else {}
    if _strict_json_equal(actual_counts, expected_counts):
        return True
    if spec is None or not _proof_complete_progress_allowed(spec):
        return False
    return _status_counts_match_pending_to_complete_progress(actual_counts, expected_counts)


def _post_fix_global_status_counts_match_expected_or_progress(
    specs: Sequence[Phase3PostFixGateSpec],
    gates: Sequence[Any],
    actual: Mapping[str, Any],
    expected: Mapping[str, Any],
) -> bool:
    actual_counts = dict(sorted(actual.items())) if isinstance(actual, Mapping) else {}
    expected_counts = dict(sorted(expected.items())) if isinstance(expected, Mapping) else {}
    if _strict_json_equal(actual_counts, expected_counts):
        return True
    if not _status_counts_match_pending_to_complete_progress(actual_counts, expected_counts):
        return False
    spec_by_lane = {spec.lane_id: spec for spec in specs}
    for gate in gates:
        if not isinstance(gate, Mapping):
            continue
        lane_id = str(gate.get("lane_id") or MISSING_SENTINEL)
        spec = spec_by_lane.get(lane_id)
        expected_gate_counts = _normalized_expected_status_counts(spec) if spec is not None else {}
        actual_gate_counts = (
            gate.get("post_fix_status_counts")
            if isinstance(gate.get("post_fix_status_counts"), Mapping)
            else {}
        )
        if not _post_fix_status_counts_match_expected_or_progress(
            spec,
            actual_gate_counts,
            expected_gate_counts,
        ):
            return False
    return True


def _status_counts_match_pending_to_complete_progress(
    actual: Mapping[str, Any],
    expected: Mapping[str, Any],
) -> bool:
    if not all(_is_non_negative_int_count(value) for value in actual.values()):
        return False
    if not all(_is_non_negative_int_count(value) for value in expected.values()):
        return False
    expected_pending = int(expected.get("pending_proof", 0))
    actual_pending = int(actual.get("pending_proof", 0))
    expected_complete = int(expected.get("proof_complete", 0))
    actual_complete = int(actual.get("proof_complete", 0))
    completed_delta = actual_complete - expected_complete
    if completed_delta <= 0:
        return False
    if expected_pending - actual_pending != completed_delta:
        return False
    keys = set(actual) | set(expected)
    for key in keys - {"pending_proof", "proof_complete"}:
        if int(actual.get(key, 0)) != int(expected.get(key, 0)):
            return False
    return sum(int(value) for value in actual.values()) == sum(
        int(value) for value in expected.values()
    )


def _post_fix_obligation_counts_match_expected_or_progress(
    spec: Optional[Phase3PostFixGateSpec],
    status_counts: Any,
    actual: Mapping[str, Any],
    expected: Mapping[str, Any],
) -> bool:
    actual_counts = dict(sorted(actual.items())) if isinstance(actual, Mapping) else {}
    expected_counts = dict(sorted(expected.items())) if isinstance(expected, Mapping) else {}
    if _strict_json_equal(actual_counts, expected_counts):
        return True
    if spec is None or not _proof_complete_progress_allowed(spec):
        return False
    if not _status_counts_match_pending_to_complete_progress(
        status_counts if isinstance(status_counts, Mapping) else {},
        _normalized_expected_status_counts(spec),
    ):
        return False
    return _obligation_counts_match_pending_to_complete_progress(
        actual_counts,
        expected_counts,
    )


def _post_fix_global_obligation_counts_match_expected_or_progress(
    specs: Sequence[Phase3PostFixGateSpec],
    gates: Sequence[Any],
    actual: Mapping[str, Any],
    expected: Mapping[str, Any],
) -> bool:
    actual_counts = dict(sorted(actual.items())) if isinstance(actual, Mapping) else {}
    expected_counts = dict(sorted(expected.items())) if isinstance(expected, Mapping) else {}
    if _strict_json_equal(actual_counts, expected_counts):
        return True
    spec_by_lane = {spec.lane_id: spec for spec in specs}
    for gate in gates:
        if not isinstance(gate, Mapping):
            continue
        lane_id = str(gate.get("lane_id") or MISSING_SENTINEL)
        spec = spec_by_lane.get(lane_id)
        obligation_summary = (
            gate.get("post_fix_obligation_summary")
            if isinstance(gate.get("post_fix_obligation_summary"), Mapping)
            else {}
        )
        if not _post_fix_obligation_counts_match_expected_or_progress(
            spec,
            gate.get("post_fix_status_counts"),
            _post_fix_obligation_counts_from_summary(obligation_summary),
            _normalized_expected_obligation_counts(spec) if spec is not None else {},
        ):
            return False
    return _obligation_counts_match_pending_to_complete_progress(
        actual_counts,
        expected_counts,
    )


def _obligation_counts_match_pending_to_complete_progress(
    actual: Mapping[str, Any],
    expected: Mapping[str, Any],
) -> bool:
    for key in ("pending_retry_entry_count", "pending_retry_obligation_count"):
        if int(actual.get(key, 0)) != int(expected.get(key, 0)):
            return False
    if int(actual.get("pending_proof_entry_count", 0)) > int(
        expected.get("pending_proof_entry_count", 0)
    ):
        return False
    if int(actual.get("pending_proof_obligation_count", 0)) > int(
        expected.get("pending_proof_obligation_count", 0)
    ):
        return False
    return any(
        int(actual.get(key, 0)) < int(expected.get(key, 0))
        for key in ("pending_proof_entry_count", "pending_proof_obligation_count")
    )


def _post_fix_entry_states_match_expected_or_progress(
    spec: Optional[Phase3PostFixGateSpec],
    actual: Any,
    expected: Sequence[Mapping[str, Any]],
) -> bool:
    if _strict_json_equal(actual, expected):
        return True
    if spec is None or not _proof_complete_progress_allowed(spec):
        return False
    if not isinstance(actual, (list, tuple)):
        return False
    actual_by_id = {
        item.get("id"): item
        for item in actual
        if isinstance(item, Mapping) and _specific_text(item.get("id"))
    }
    if len(actual_by_id) != len(actual):
        return False
    for expected_state in expected:
        if not isinstance(expected_state, Mapping):
            return False
        actual_state = actual_by_id.get(expected_state.get("id"))
        if actual_state is None:
            return False
        if _strict_json_equal(actual_state, expected_state):
            continue
        if not _entry_state_is_pending_to_complete_progress(actual_state, expected_state):
            return False
    return len(actual_by_id) == len(expected)


def _entry_state_is_pending_to_complete_progress(
    actual: Mapping[str, Any],
    expected: Mapping[str, Any],
) -> bool:
    for key in ("id", "function", "binary_pair"):
        if actual.get(key) != expected.get(key):
            return False
    if expected.get("post_fix_status") != "pending_proof":
        return False
    if actual.get("post_fix_status") != "proof_complete":
        return False
    return (
        int(actual.get("pending_proof_obligation_count", 0)) == 0
        and int(actual.get("pending_retry_obligation_count", 0)) == 0
        and int(actual.get("required_completion_action_count", 0)) == 0
        and int(expected.get("pending_proof_obligation_count", 0)) > 0
    )


def _post_fix_action_hashes_match_expected_or_progress(
    spec: Optional[Phase3PostFixGateSpec],
    actual_states: Any,
    actual_hashes: Any,
    expected_hashes: Sequence[Mapping[str, str]],
) -> bool:
    if _strict_json_equal(actual_hashes, expected_hashes):
        return True
    if spec is None or not _proof_complete_progress_allowed(spec):
        return False
    if not isinstance(actual_hashes, (list, tuple)):
        return False
    actual_hash_by_id = {
        item.get("id"): item.get("required_completion_actions_sha256")
        for item in actual_hashes
        if isinstance(item, Mapping) and _specific_text(item.get("id"))
    }
    state_by_id = (
        {
            item.get("id"): item
            for item in actual_states
            if isinstance(item, Mapping) and _specific_text(item.get("id"))
        }
        if isinstance(actual_states, (list, tuple))
        else {}
    )
    empty_hash = _required_completion_actions_sha256([])
    for expected_hash in expected_hashes:
        entry_id = expected_hash.get("id") if isinstance(expected_hash, Mapping) else None
        if entry_id not in actual_hash_by_id:
            return False
        if actual_hash_by_id[entry_id] == expected_hash.get("required_completion_actions_sha256"):
            continue
        state = state_by_id.get(entry_id)
        if not (
            isinstance(state, Mapping)
            and state.get("post_fix_status") == "proof_complete"
            and actual_hash_by_id[entry_id] == empty_hash
        ):
            return False
    return len(actual_hash_by_id) == len(expected_hashes)


def _proof_complete_progress_allowed(spec: Phase3PostFixGateSpec) -> bool:
    allowed = set(_normalized_allowed_post_fix_statuses(spec))
    expected = _normalized_expected_status_counts(spec)
    return "proof_complete" in allowed and int(expected.get("pending_proof", 0)) > 0


def _pending_required_action_is_valid(action: Any) -> bool:
    if not isinstance(action, Mapping):
        return False
    for field_name in ("reason_id", "proof_kind", "proof_stage", "evidence_kind"):
        if not _specific_text(action.get(field_name)):
            return False
    proof_obligation_id = action.get("proof_obligation_id")
    if not _concrete_key_value(proof_obligation_id):
        return False
    return _required_evidence_is_valid(action.get("required_evidence"))


def _pending_obligation_required_key(value: Mapping[str, Any]) -> str:
    return json.dumps(
        {
            "reason_id": value.get("reason_id") or MISSING_SENTINEL,
            "proof_kind": value.get("proof_kind") or MISSING_SENTINEL,
            "proof_stage": value.get("proof_stage") or MISSING_SENTINEL,
            "evidence_kind": value.get("evidence_kind") or MISSING_SENTINEL,
            "required_evidence": _required_evidence_key(value.get("required_evidence")),
            "proof_obligation_id": value.get("proof_obligation_id") or MISSING_SENTINEL,
        },
        sort_keys=True,
        separators=(",", ":"),
    )


def _required_evidence_key(value: Any) -> Any:
    if isinstance(value, (list, tuple)):
        return list(value)
    return MISSING_SENTINEL


def _required_evidence_is_valid(value: Any) -> bool:
    return (
        isinstance(value, (list, tuple))
        and bool(value)
        and all(_specific_text(item) for item in value)
        and len(set(value)) == len(value)
    )


def _concrete_key_value(value: Any) -> bool:
    if _specific_text(value):
        return True
    if isinstance(value, (list, tuple)):
        return bool(value) and not _contains_missing_sentinel(value)
    if isinstance(value, Mapping):
        return bool(value) and not _contains_missing_sentinel(value)
    return False


def _specific_text(value: Any) -> bool:
    return (
        isinstance(value, str)
        and bool(value.strip())
        and value != MISSING_SENTINEL
    )


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


def _post_fix_invalid_entry_ids(payload: Mapping[str, Any]) -> list[Dict[str, Any]]:
    entries = payload.get("entries")
    if not isinstance(entries, (list, tuple)):
        return []
    invalid: list[Dict[str, Any]] = []
    for entry_index, entry in enumerate(entries):
        if not isinstance(entry, Mapping):
            invalid.append(
                {
                    "entry_index": entry_index,
                    "entry_id": type(entry).__name__,
                }
            )
            continue
        entry_id = entry.get("id")
        if _specific_text(entry_id):
            continue
        invalid.append(
            {
                "entry_index": entry_index,
                "entry_id": str(entry_id or MISSING_SENTINEL),
            }
        )
    return invalid


def _post_fix_duplicate_entry_ids(payload: Mapping[str, Any]) -> list[str]:
    entries = payload.get("entries")
    if not isinstance(entries, (list, tuple)):
        return []
    seen: set[str] = set()
    duplicates: list[str] = []
    for entry in entries:
        if not isinstance(entry, Mapping):
            continue
        entry_id = entry.get("id")
        if not _specific_text(entry_id):
            continue
        if entry_id in seen and entry_id not in duplicates:
            duplicates.append(entry_id)
        seen.add(entry_id)
    return duplicates


def _post_fix_invalid_entry_metadata(payload: Mapping[str, Any]) -> list[Dict[str, Any]]:
    entries = payload.get("entries")
    if not isinstance(entries, (list, tuple)):
        return []
    invalid: list[Dict[str, Any]] = []
    for entry_index, entry in enumerate(entries):
        if not isinstance(entry, Mapping):
            invalid.append(
                {
                    "entry_index": entry_index,
                    "field": MISSING_SENTINEL,
                    "value": type(entry).__name__,
                }
            )
            continue
        entry_id = str(entry.get("id") or f"entry[{entry_index}]")
        for field_name in ("function", "binary_pair", "post_fix_status"):
            value = entry.get(field_name)
            if _specific_text(value):
                continue
            invalid.append(
                {
                    "entry_index": entry_index,
                    "entry_id": entry_id,
                    "field": field_name,
                    "value": str(value or MISSING_SENTINEL),
                }
            )
    return invalid


def _post_fix_entry_identities(payload: Mapping[str, Any]) -> list[Dict[str, str]]:
    entries = payload.get("entries")
    if not isinstance(entries, (list, tuple)):
        return []
    identities: list[Dict[str, str]] = []
    for entry in entries:
        if not isinstance(entry, Mapping):
            continue
        identities.append(
            {
                "id": str(entry.get("id") or MISSING_SENTINEL),
                "function": str(entry.get("function") or MISSING_SENTINEL),
                "binary_pair": str(entry.get("binary_pair") or MISSING_SENTINEL),
            }
        )
    return identities


def _post_fix_entry_states(payload: Mapping[str, Any]) -> list[Dict[str, Any]]:
    entries = payload.get("entries")
    if not isinstance(entries, (list, tuple)):
        return []
    states: list[Dict[str, Any]] = []
    for entry in entries:
        if not isinstance(entry, Mapping):
            continue
        pending_proof_obligations = entry.get("pending_proof_obligations")
        pending_retry_obligations = entry.get("pending_retry_obligations")
        required_completion_actions = entry.get("required_completion_actions")
        states.append(
            {
                "id": str(entry.get("id") or MISSING_SENTINEL),
                "function": str(entry.get("function") or MISSING_SENTINEL),
                "binary_pair": str(entry.get("binary_pair") or MISSING_SENTINEL),
                "post_fix_status": str(entry.get("post_fix_status") or MISSING_SENTINEL),
                "pending_proof_obligation_count": (
                    len(pending_proof_obligations)
                    if isinstance(pending_proof_obligations, (list, tuple))
                    else 0
                ),
                "pending_retry_obligation_count": (
                    len(pending_retry_obligations)
                    if isinstance(pending_retry_obligations, (list, tuple))
                    else 0
                ),
                "required_completion_action_count": _entry_required_action_count(
                    required_completion_actions
                ),
            }
        )
    return states


def _post_fix_required_completion_action_hashes(
    payload: Mapping[str, Any],
) -> list[Dict[str, str]]:
    entries = payload.get("entries")
    if not isinstance(entries, (list, tuple)):
        return []
    hashes: list[Dict[str, str]] = []
    for entry in entries:
        if not isinstance(entry, Mapping):
            continue
        entry_id = entry.get("id")
        if not _specific_text(entry_id):
            continue
        hashes.append(
            {
                "id": entry_id,
                "required_completion_actions_sha256": _required_completion_actions_sha256(
                    entry.get("required_completion_actions")
                ),
            }
        )
    return hashes


def _required_completion_actions_sha256(actions: Any) -> str:
    normalized_actions = actions if isinstance(actions, (list, tuple)) else []
    canonical = json.dumps(
        normalized_actions,
        sort_keys=True,
        separators=(",", ":"),
    )
    return hashlib.sha256(canonical.encode("utf-8")).hexdigest()


def _entry_required_action_count(actions: Any) -> Any:
    if actions is None:
        return 0
    if isinstance(actions, (list, tuple)):
        return len(actions)
    return MISSING_SENTINEL


def _post_fix_status_counts_from_gates(gates: Sequence[Any]) -> Dict[str, int]:
    counts: Dict[str, int] = {}
    for gate in gates:
        if not isinstance(gate, Mapping):
            continue
        gate_counts = gate.get("post_fix_status_counts")
        if not isinstance(gate_counts, Mapping):
            continue
        for status, count in gate_counts.items():
            if not isinstance(status, str) or not _is_non_negative_int_count(count):
                continue
            counts[status] = counts.get(status, 0) + count
    return dict(sorted(counts.items()))


def _invalid_status_counts(status_counts: Any) -> list[Dict[str, str]]:
    if not isinstance(status_counts, Mapping):
        return [{"status": MISSING_SENTINEL, "count": type(status_counts).__name__}]
    invalid: list[Dict[str, str]] = []
    for status, count in status_counts.items():
        if (
            isinstance(status, str)
            and status
            and _is_non_negative_int_count(count)
        ):
            continue
        invalid.append(
            {
                "status": str(status) if isinstance(status, str) else type(status).__name__,
                "count": str(count) if isinstance(count, (str, int, bool)) else type(count).__name__,
            }
        )
    return invalid


def _invalid_obligation_summary_counts(summary: Mapping[str, Any]) -> list[Dict[str, str]]:
    invalid: list[Dict[str, str]] = []
    for field_name in OBLIGATION_COUNT_KEYS:
        count = summary.get(field_name, MISSING_SENTINEL)
        if _is_non_negative_int_count(count):
            continue
        invalid.append(
            {
                "field": field_name,
                "count": str(count) if isinstance(count, (str, int, bool)) else type(count).__name__,
            }
        )
    return invalid


def _post_fix_summary_info(payload: Mapping[str, Any]) -> Dict[str, Any]:
    gate = payload.get("post_fix_regression_gate")
    if isinstance(gate, Mapping) and isinstance(gate.get("summary"), Mapping):
        checks = gate.get("checks")
        has_nested_checks = isinstance(checks, (list, tuple))
        stored_summary = gate.get("summary") or {}
        stored_core = _stored_post_fix_summary_core(
            stored_summary,
            include_count_fields=has_nested_checks,
        )
        if has_nested_checks:
            computed_core = _post_fix_summary_core_from_checks(checks)
            consistency_failures = _post_fix_summary_core_mismatches(
                stored_core,
                computed_core,
            )
            invalid_checks = _invalid_summary_checks(checks)
            summary_core = computed_core
        else:
            consistency_failures = []
            invalid_checks = []
            summary_core = stored_core
        return {
            "source": "post_fix_regression_gate",
            "check_count": summary_core.get("total", MISSING_SENTINEL),
            "consistency_failures": consistency_failures,
            "invalid_checks": invalid_checks,
            "summary": summary_core,
        }
    checks = payload.get("checks")
    if isinstance(checks, (list, tuple)):
        failed = _failed_check_kinds(checks)
        return {
            "source": "top_level_checks",
            "check_count": len(checks),
            "consistency_failures": [],
            "invalid_checks": _invalid_summary_checks(checks),
            "summary": {"failed": len(failed), "failed_kinds": failed},
        }
    return {
        "source": MISSING_SENTINEL,
        "check_count": MISSING_SENTINEL,
        "consistency_failures": [],
        "invalid_checks": [],
        "summary": {},
    }


def _stored_post_fix_summary_core(
    summary: Mapping[str, Any],
    *,
    include_count_fields: bool = False,
) -> Dict[str, Any]:
    failed_kinds = summary.get("failed_kinds")
    core = {
        "failed": summary.get("failed", MISSING_SENTINEL),
        "failed_kinds": (
            list(failed_kinds)
            if isinstance(failed_kinds, (list, tuple))
            else MISSING_SENTINEL
        ),
    }
    if include_count_fields:
        return {
            "total": summary.get("total", MISSING_SENTINEL),
            "passed": summary.get("passed", MISSING_SENTINEL),
            **core,
        }
    return core


def _post_fix_summary_core_from_checks(checks: Sequence[Any]) -> Dict[str, Any]:
    failed = [
        check
        for check in checks
        if isinstance(check, Mapping) and check.get("status") == "failed"
    ]
    return {
        "total": len(checks),
        "passed": sum(
            1
            for check in checks
            if isinstance(check, Mapping) and check.get("status") == "ok"
        ),
        "failed": len(failed),
        "failed_kinds": sorted({str(check.get("kind")) for check in failed}),
    }


def _invalid_summary_checks(checks: Sequence[Any]) -> list[Dict[str, Any]]:
    invalid: list[Dict[str, Any]] = []
    for check_index, check in enumerate(checks):
        if not isinstance(check, Mapping):
            invalid.append(
                {
                    "check_index": check_index,
                    "field": MISSING_SENTINEL,
                    "value": type(check).__name__,
                }
            )
            continue
        kind = check.get("kind")
        if not _specific_text(kind):
            invalid.append(
                {
                    "check_index": check_index,
                    "field": "kind",
                    "value": str(kind or MISSING_SENTINEL),
                }
            )
        status = check.get("status")
        if status not in {"ok", "failed"}:
            invalid.append(
                {
                    "check_index": check_index,
                    "field": "status",
                    "value": str(status or MISSING_SENTINEL),
                }
            )
    return invalid


def _post_fix_summary_core_mismatches(
    stored: Mapping[str, Any],
    computed: Mapping[str, Any],
) -> list[Dict[str, Any]]:
    mismatches: list[Dict[str, Any]] = []
    for field_name in ("total", "passed", "failed", "failed_kinds"):
        if _strict_json_equal(stored.get(field_name), computed.get(field_name)):
            continue
        mismatches.append(
            {
                "field": field_name,
                "stored": stored.get(field_name, MISSING_SENTINEL),
                "computed": computed.get(field_name, MISSING_SENTINEL),
            }
        )
    return mismatches


def _post_fix_index_checks(
    specs: Sequence[Phase3PostFixGateSpec],
    gates: Sequence[Any],
) -> Sequence[Dict[str, Any]]:
    checks: list[Dict[str, Any]] = []
    expected_rows = _gate_spec_rows_from_specs(specs)
    actual_rows = _gate_spec_rows_from_gates(gates)
    checks.append(
        _ok("phase3_post_fix_gate_specs")
        if _strict_json_equal(actual_rows, expected_rows)
        else _failed("phase3_post_fix_gate_specs", expected=expected_rows, actual=actual_rows)
    )
    expected_global_status_counts = _expected_post_fix_status_counts_from_specs(specs)
    actual_global_status_counts = _post_fix_status_counts_from_gates(gates)
    if expected_global_status_counts:
        checks.append(
            _ok("phase3_post_fix_gate_status_counts_global_expected")
            if _post_fix_global_status_counts_match_expected_or_progress(
                specs,
                gates,
                actual_global_status_counts,
                expected_global_status_counts,
            )
            else _failed(
                "phase3_post_fix_gate_status_counts_global_expected",
                expected=expected_global_status_counts,
                actual=actual_global_status_counts,
            )
        )
    expected_global_obligation_counts = _expected_post_fix_obligation_counts_from_specs(specs)
    actual_global_obligation_counts = _post_fix_obligation_counts_from_gates(gates)
    if expected_global_obligation_counts:
        checks.append(
            _ok("phase3_post_fix_gate_obligation_counts_global_expected")
            if _post_fix_global_obligation_counts_match_expected_or_progress(
                specs,
                gates,
                actual_global_obligation_counts,
                expected_global_obligation_counts,
            )
            else _failed(
                "phase3_post_fix_gate_obligation_counts_global_expected",
                expected=expected_global_obligation_counts,
                actual=actual_global_obligation_counts,
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
                if _strict_json_equal(actual_entry_count, expected_entry_count)
                else _failed(
                    "phase3_post_fix_gate_entry_count",
                    expected=expected_entry_count,
                    actual=actual_entry_count,
                    **details,
                )
            )
        invalid_entry_ids = gate.get("post_fix_invalid_entry_ids")
        checks.append(
            _ok("phase3_post_fix_gate_entry_ids_concrete", **details)
            if invalid_entry_ids == []
            else _failed(
                "phase3_post_fix_gate_entry_ids_concrete",
                invalid_entry_ids=invalid_entry_ids,
                **details,
            )
        )
        duplicate_entry_ids = gate.get("post_fix_duplicate_entry_ids")
        checks.append(
            _ok("phase3_post_fix_gate_entry_ids_unique", **details)
            if duplicate_entry_ids == []
            else _failed(
                "phase3_post_fix_gate_entry_ids_unique",
                duplicate_entry_ids=duplicate_entry_ids,
                **details,
            )
        )
        invalid_entry_metadata = gate.get("post_fix_invalid_entry_metadata")
        checks.append(
            _ok("phase3_post_fix_gate_entry_metadata_concrete", **details)
            if invalid_entry_metadata == []
            else _failed(
                "phase3_post_fix_gate_entry_metadata_concrete",
                invalid_entry_metadata=invalid_entry_metadata,
                **details,
            )
        )
        expected_entry_identities = (
            _normalized_expected_entry_identities(spec)
            if spec is not None
            else []
        )
        actual_entry_identities = gate.get("post_fix_entry_identities")
        if expected_entry_identities:
            checks.append(
                _ok("phase3_post_fix_gate_entry_identities_expected", **details)
                if _strict_json_equal(actual_entry_identities, expected_entry_identities)
                else _failed(
                    "phase3_post_fix_gate_entry_identities_expected",
                    expected=expected_entry_identities,
                    actual=actual_entry_identities,
                    **details,
                )
            )
        expected_entry_states = (
            _normalized_expected_entry_states(spec)
            if spec is not None
            else []
        )
        actual_entry_states = gate.get("post_fix_entry_states")
        if expected_entry_states:
            checks.append(
                _ok("phase3_post_fix_gate_entry_states_expected", **details)
                if _post_fix_entry_states_match_expected_or_progress(
                    spec,
                    actual_entry_states,
                    expected_entry_states,
                )
                else _failed(
                    "phase3_post_fix_gate_entry_states_expected",
                    expected=expected_entry_states,
                    actual=actual_entry_states,
                    **details,
                )
            )
        expected_action_hashes = (
            _normalized_expected_required_action_hashes(spec)
            if spec is not None
            else []
        )
        actual_action_hashes = gate.get("post_fix_required_completion_action_hashes")
        if expected_action_hashes:
            checks.append(
                _ok("phase3_post_fix_gate_required_action_hashes_expected", **details)
                if _post_fix_action_hashes_match_expected_or_progress(
                    spec,
                    gate.get("post_fix_entry_states"),
                    actual_action_hashes,
                    expected_action_hashes,
                )
                else _failed(
                    "phase3_post_fix_gate_required_action_hashes_expected",
                    expected=expected_action_hashes,
                    actual=actual_action_hashes,
                    **details,
                )
            )
        expected_summary_source = (
            _normalized_expected_summary_source(spec)
            if spec is not None
            else MISSING_SENTINEL
        )
        summary_source = gate.get("post_fix_summary_source", MISSING_SENTINEL)
        checks.append(
            _ok("phase3_post_fix_gate_summary_source", **details)
            if summary_source == expected_summary_source
            else _failed(
                "phase3_post_fix_gate_summary_source",
                expected=expected_summary_source,
                actual=summary_source,
                **details,
            )
        )
        summary_check_count = gate.get("post_fix_summary_check_count", MISSING_SENTINEL)
        checks.append(
            _ok("phase3_post_fix_gate_summary_checks_present", **details)
            if (
                expected_summary_source != "top_level_checks"
                or (
                    _is_non_negative_int_count(summary_check_count)
                    and summary_check_count > 0
                )
            )
            else _failed(
                "phase3_post_fix_gate_summary_checks_present",
                check_count=summary_check_count,
                **details,
            )
        )
        summary_consistency_failures = gate.get("post_fix_summary_consistency_failures")
        checks.append(
            _ok("phase3_post_fix_gate_summary_consistent", **details)
            if summary_consistency_failures == []
            else _failed(
                "phase3_post_fix_gate_summary_consistent",
                consistency_failures=summary_consistency_failures,
                **details,
            )
        )
        summary_invalid_checks = gate.get("post_fix_summary_invalid_checks")
        checks.append(
            _ok("phase3_post_fix_gate_summary_checks_valid", **details)
            if summary_invalid_checks == []
            else _failed(
                "phase3_post_fix_gate_summary_checks_valid",
                invalid_checks=summary_invalid_checks,
                **details,
            )
        )
        status_counts = gate.get("post_fix_status_counts")
        invalid_status_counts = _invalid_status_counts(status_counts)
        checks.append(
            _ok("phase3_post_fix_gate_status_counts_valid", **details)
            if not invalid_status_counts
            else _failed(
                "phase3_post_fix_gate_status_counts_valid",
                invalid_status_counts=invalid_status_counts,
                **details,
            )
        )
        status_count_total = (
            sum(count for count in status_counts.values() if _is_non_negative_int_count(count))
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
                if _post_fix_status_counts_match_expected_or_progress(
                    spec,
                    actual_status_counts,
                    expected_status_counts,
                )
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
        expected_obligation_counts = (
            _normalized_expected_obligation_counts(spec)
            if spec is not None
            else {}
        )
        actual_obligation_counts = _post_fix_obligation_counts_from_summary(obligation_summary)
        invalid_obligation_counts = _invalid_obligation_summary_counts(obligation_summary)
        if expected_obligation_counts:
            checks.append(
                _ok("phase3_post_fix_gate_obligation_counts_expected", **details)
                if _post_fix_obligation_counts_match_expected_or_progress(
                    spec,
                    gate.get("post_fix_status_counts"),
                    actual_obligation_counts,
                    expected_obligation_counts,
                )
                else _failed(
                    "phase3_post_fix_gate_obligation_counts_expected",
                    expected=expected_obligation_counts,
                    actual=actual_obligation_counts,
                    **details,
                )
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
        pending_proof_duplicate = list(
            obligation_summary.get("pending_proof_duplicate_obligations") or ()
        )
        pending_retry_duplicate = list(
            obligation_summary.get("pending_retry_duplicate_obligations") or ()
        )
        pending_proof_duplicate_ids = list(
            obligation_summary.get("pending_proof_duplicate_obligation_ids") or ()
        )
        pending_retry_duplicate_ids = list(
            obligation_summary.get("pending_retry_duplicate_obligation_ids") or ()
        )
        pending_proof_duplicate_ids_across_entries = list(
            obligation_summary.get("pending_proof_duplicate_obligation_ids_across_entries")
            or ()
        )
        pending_retry_duplicate_ids_across_entries = list(
            obligation_summary.get("pending_retry_duplicate_obligation_ids_across_entries")
            or ()
        )
        pending_proof_invalid_required = list(
            obligation_summary.get("pending_proof_invalid_required_actions") or ()
        )
        pending_retry_invalid_required = list(
            obligation_summary.get("pending_retry_invalid_required_actions") or ()
        )
        pending_proof_duplicate_required = list(
            obligation_summary.get("pending_proof_duplicate_required_actions") or ()
        )
        pending_retry_duplicate_required = list(
            obligation_summary.get("pending_retry_duplicate_required_actions") or ()
        )
        pending_proof_duplicate_required_ids = list(
            obligation_summary.get("pending_proof_duplicate_required_action_ids") or ()
        )
        pending_retry_duplicate_required_ids = list(
            obligation_summary.get("pending_retry_duplicate_required_action_ids") or ()
        )
        pending_proof_duplicate_required_ids_across_entries = list(
            obligation_summary.get(
                "pending_proof_duplicate_required_action_ids_across_entries"
            )
            or ()
        )
        pending_retry_duplicate_required_ids_across_entries = list(
            obligation_summary.get(
                "pending_retry_duplicate_required_action_ids_across_entries"
            )
            or ()
        )
        duplicate_obligation_ids_across_statuses = list(
            obligation_summary.get("duplicate_obligation_ids_across_statuses") or ()
        )
        duplicate_required_action_ids_across_statuses = list(
            obligation_summary.get("duplicate_required_action_ids_across_statuses") or ()
        )
        non_pending_with_pending_obligations = list(
            obligation_summary.get("non_pending_entries_with_pending_obligations") or ()
        )
        unexpected_pending_obligations = list(
            obligation_summary.get("entries_with_unexpected_pending_obligations") or ()
        )
        unexpected_required_actions = list(
            obligation_summary.get("entries_with_unexpected_required_actions") or ()
        )
        retired_invalid_required_actions = list(
            obligation_summary.get("retired_invalid_required_actions") or ()
        )
        retired_duplicate_required_action_ids = list(
            obligation_summary.get("retired_duplicate_required_action_ids") or ()
        )
        retired_duplicate_required_action_ids_across_entries = list(
            obligation_summary.get("retired_duplicate_required_action_ids_across_entries")
            or ()
        )
        pending_proof_mismatches = list(
            obligation_summary.get("pending_proof_required_action_mismatches") or ()
        )
        pending_retry_mismatches = list(
            obligation_summary.get("pending_retry_required_action_mismatches") or ()
        )
        obligation_failures = {
            "invalid_obligation_counts": invalid_obligation_counts,
            "pending_proof_missing_required_actions": pending_proof_missing_required,
            "pending_retry_missing_required_actions": pending_retry_missing_required,
            "pending_proof_missing": pending_proof_missing,
            "pending_retry_missing": pending_retry_missing,
            "pending_proof_invalid": pending_proof_invalid,
            "pending_retry_invalid": pending_retry_invalid,
            "pending_proof_duplicate_obligations": pending_proof_duplicate,
            "pending_retry_duplicate_obligations": pending_retry_duplicate,
            "pending_proof_duplicate_obligation_ids": pending_proof_duplicate_ids,
            "pending_retry_duplicate_obligation_ids": pending_retry_duplicate_ids,
            "pending_proof_duplicate_obligation_ids_across_entries": (
                pending_proof_duplicate_ids_across_entries
            ),
            "pending_retry_duplicate_obligation_ids_across_entries": (
                pending_retry_duplicate_ids_across_entries
            ),
            "pending_proof_invalid_required_actions": pending_proof_invalid_required,
            "pending_retry_invalid_required_actions": pending_retry_invalid_required,
            "pending_proof_duplicate_required_actions": pending_proof_duplicate_required,
            "pending_retry_duplicate_required_actions": pending_retry_duplicate_required,
            "pending_proof_duplicate_required_action_ids": pending_proof_duplicate_required_ids,
            "pending_retry_duplicate_required_action_ids": pending_retry_duplicate_required_ids,
            "pending_proof_duplicate_required_action_ids_across_entries": (
                pending_proof_duplicate_required_ids_across_entries
            ),
            "pending_retry_duplicate_required_action_ids_across_entries": (
                pending_retry_duplicate_required_ids_across_entries
            ),
            "duplicate_obligation_ids_across_statuses": (
                duplicate_obligation_ids_across_statuses
            ),
            "duplicate_required_action_ids_across_statuses": (
                duplicate_required_action_ids_across_statuses
            ),
            "non_pending_entries_with_pending_obligations": (
                non_pending_with_pending_obligations
            ),
            "entries_with_unexpected_pending_obligations": unexpected_pending_obligations,
            "entries_with_unexpected_required_actions": unexpected_required_actions,
            "retired_invalid_required_actions": retired_invalid_required_actions,
            "retired_duplicate_required_action_ids": retired_duplicate_required_action_ids,
            "retired_duplicate_required_action_ids_across_entries": (
                retired_duplicate_required_action_ids_across_entries
            ),
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
            if (
                _is_non_negative_int_count(summary_failed)
                and summary_failed == 0
                and summary_failed_kinds == []
            )
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
            "expected_entry_count": _normalized_expected_entry_count(spec),
            "allowed_post_fix_statuses": _normalized_allowed_post_fix_statuses(spec),
            "expected_post_fix_summary_source": _normalized_expected_summary_source(spec),
            "expected_post_fix_entry_identities": _normalized_expected_entry_identities(spec),
            "expected_post_fix_entry_states": _normalized_expected_entry_states(spec),
            "expected_required_completion_action_hashes": (
                _normalized_expected_required_action_hashes(spec)
            ),
            "expected_post_fix_status_counts": _normalized_expected_status_counts(spec),
            "expected_post_fix_obligation_counts": _normalized_expected_obligation_counts(spec),
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
                "allowed_post_fix_statuses": list(gate.get("allowed_post_fix_statuses") or ())
                if isinstance(gate.get("allowed_post_fix_statuses"), (list, tuple))
                else [],
                "expected_post_fix_summary_source": gate.get(
                    "expected_post_fix_summary_source"
                ),
                "expected_post_fix_entry_identities": list(
                    gate.get("expected_post_fix_entry_identities") or ()
                )
                if isinstance(gate.get("expected_post_fix_entry_identities"), (list, tuple))
                else [],
                "expected_post_fix_entry_states": list(
                    gate.get("expected_post_fix_entry_states") or ()
                )
                if isinstance(gate.get("expected_post_fix_entry_states"), (list, tuple))
                else [],
                "expected_required_completion_action_hashes": list(
                    gate.get("expected_required_completion_action_hashes") or ()
                )
                if isinstance(
                    gate.get("expected_required_completion_action_hashes"),
                    (list, tuple),
                )
                else [],
                "expected_post_fix_status_counts": dict(
                    sorted((gate.get("expected_post_fix_status_counts") or {}).items())
                )
                if isinstance(gate.get("expected_post_fix_status_counts"), Mapping)
                else {},
                "expected_post_fix_obligation_counts": dict(
                    sorted((gate.get("expected_post_fix_obligation_counts") or {}).items())
                )
                if isinstance(gate.get("expected_post_fix_obligation_counts"), Mapping)
                else {},
            }
        )
    return rows


def _normalized_gate_specs(
    gate_specs: Sequence[Phase3PostFixGateSpec],
) -> tuple[Phase3PostFixGateSpec, ...]:
    if not isinstance(gate_specs, (list, tuple)) or not gate_specs:
        raise ValueError("gate_specs must be a non-empty sequence")
    normalized = tuple(gate_specs)
    for index, spec in enumerate(normalized):
        if not isinstance(spec, Phase3PostFixGateSpec):
            raise ValueError(f"gate_specs[{index}] must be a Phase3PostFixGateSpec")
        if not _is_non_negative_int_count(spec.lane_number) or spec.lane_number == 0:
            raise ValueError(f"gate_specs[{index}].lane_number must be a positive integer")
        _normalized_expected_text(spec.lane_id, field_name=f"gate_specs[{index}].lane_id")
        _normalized_expected_text(
            spec.gate_relpath,
            field_name=f"gate_specs[{index}].gate_relpath",
        )
        _normalized_expected_text(
            spec.manifest_kind,
            field_name=f"gate_specs[{index}].manifest_kind",
        )
        _normalized_expected_text(spec.ready_key, field_name=f"gate_specs[{index}].ready_key")
        _normalized_expected_entry_count(spec)
        _normalized_allowed_post_fix_statuses(spec)
        _normalized_expected_summary_source(spec)
        _normalized_expected_status_counts(spec)
        _normalized_expected_obligation_counts(spec)
        _normalized_expected_entry_identities(spec)
        _normalized_expected_entry_states(spec)
        _normalized_expected_required_action_hashes(spec)
        _validate_expected_spec_consistency(spec)
    _reject_duplicate_spec_field(normalized, field_name="lane_number")
    _reject_duplicate_spec_field(normalized, field_name="lane_id")
    _reject_duplicate_spec_field(normalized, field_name="gate_relpath")
    return normalized


def _reject_duplicate_spec_field(
    specs: Sequence[Phase3PostFixGateSpec],
    *,
    field_name: str,
) -> None:
    seen: set[Any] = set()
    duplicates: list[Any] = []
    for spec in specs:
        value = getattr(spec, field_name)
        if value in seen and value not in duplicates:
            duplicates.append(value)
        seen.add(value)
    if duplicates:
        raise ValueError(f"gate_specs must have unique {field_name}: {duplicates!r}")


def _normalized_expected_entry_count(spec: Phase3PostFixGateSpec) -> int:
    count = _normalized_expected_count(
        spec.expected_entry_count,
        field_name=f"{spec.lane_id}: expected_entry_count",
    )
    if count == 0:
        raise ValueError(f"{spec.lane_id}: expected_entry_count must be positive")
    return count


def _normalized_allowed_post_fix_statuses(spec: Phase3PostFixGateSpec) -> list[str]:
    statuses = spec.allowed_post_fix_statuses
    if not isinstance(statuses, (list, tuple)) or not statuses:
        raise ValueError(f"{spec.lane_id}: allowed_post_fix_statuses must be non-empty")
    normalized: list[str] = []
    for index, status in enumerate(statuses):
        text = _normalized_expected_text(
            status,
            field_name=f"{spec.lane_id}: allowed_post_fix_statuses[{index}]",
        )
        if text not in normalized:
            normalized.append(text)
    if len(normalized) != len(statuses):
        raise ValueError(f"{spec.lane_id}: allowed_post_fix_statuses must be unique")
    return normalized


def _normalized_expected_summary_source(spec: Phase3PostFixGateSpec) -> str:
    source = _normalized_expected_text(
        spec.expected_post_fix_summary_source,
        field_name=f"{spec.lane_id}: expected_post_fix_summary_source",
    )
    if source not in {"post_fix_regression_gate", "top_level_checks"}:
        raise ValueError(
            f"{spec.lane_id}: expected_post_fix_summary_source must be recognized"
        )
    return source


def _normalized_expected_status_counts(spec: Phase3PostFixGateSpec) -> Dict[str, int]:
    counts = spec.expected_post_fix_status_counts
    if counts is None:
        return {}
    if not isinstance(counts, Mapping):
        raise ValueError(f"{spec.lane_id}: expected_post_fix_status_counts must be an object")
    if not counts:
        return {}
    allowed_statuses = set(_normalized_allowed_post_fix_statuses(spec))
    expected_entry_count = _normalized_expected_entry_count(spec)
    normalized: Dict[str, int] = {}
    for status, count in sorted(counts.items(), key=lambda item: str(item[0])):
        if not _specific_text(status):
            raise ValueError(
                f"{spec.lane_id}: expected_post_fix_status_counts has an invalid status key"
            )
        if status not in allowed_statuses:
            raise ValueError(
                f"{spec.lane_id}: expected_post_fix_status_counts[{status}] is not allowed"
            )
        normalized[status] = _normalized_expected_count(
            count,
            field_name=f"{spec.lane_id}: expected_post_fix_status_counts[{status}]",
        )
        if normalized[status] == 0:
            raise ValueError(
                f"{spec.lane_id}: expected_post_fix_status_counts[{status}] "
                "must be positive"
            )
    if sum(normalized.values()) != expected_entry_count:
        raise ValueError(
            f"{spec.lane_id}: expected_post_fix_status_counts total must match "
            "expected_entry_count"
        )
    return normalized


def _expected_post_fix_status_counts_from_specs(
    specs: Sequence[Phase3PostFixGateSpec],
) -> Dict[str, int]:
    counts: Dict[str, int] = {}
    for spec in specs:
        for status, count in _normalized_expected_status_counts(spec).items():
            counts[status] = counts.get(status, 0) + count
    return dict(sorted(counts.items()))


def _normalized_expected_entry_identities(
    spec: Phase3PostFixGateSpec,
) -> list[Dict[str, str]]:
    expected_identities = spec.expected_post_fix_entry_identities
    if not isinstance(expected_identities, (list, tuple)):
        raise ValueError(
            f"{spec.lane_id}: expected_post_fix_entry_identities must be a sequence"
        )
    identities: list[Dict[str, str]] = []
    for entry_index, entry in enumerate(expected_identities):
        if not isinstance(entry, Mapping):
            raise ValueError(
                f"{spec.lane_id}: expected_post_fix_entry_identities[{entry_index}] "
                "must be an object"
            )
        identities.append(
            {
                "id": _normalized_expected_text(
                    entry.get("id"),
                    field_name=(
                        f"{spec.lane_id}: expected_post_fix_entry_identities"
                        f"[{entry_index}].id"
                    ),
                ),
                "function": _normalized_expected_text(
                    entry.get("function"),
                    field_name=(
                        f"{spec.lane_id}: expected_post_fix_entry_identities"
                        f"[{entry_index}].function"
                    ),
                ),
                "binary_pair": _normalized_expected_text(
                    entry.get("binary_pair"),
                    field_name=(
                        f"{spec.lane_id}: expected_post_fix_entry_identities"
                        f"[{entry_index}].binary_pair"
                    ),
                ),
            }
        )
    _reject_duplicate_expected_entry_ids(
        identities,
        field_name=f"{spec.lane_id}: expected_post_fix_entry_identities",
    )
    if identities and len(identities) != _normalized_expected_entry_count(spec):
        raise ValueError(
            f"{spec.lane_id}: expected_post_fix_entry_identities count must match "
            "expected_entry_count"
        )
    return identities


def _normalized_expected_entry_states(
    spec: Phase3PostFixGateSpec,
) -> list[Dict[str, Any]]:
    expected_states = spec.expected_post_fix_entry_states
    if not isinstance(expected_states, (list, tuple)):
        raise ValueError(f"{spec.lane_id}: expected_post_fix_entry_states must be a sequence")
    allowed_statuses = set(_normalized_allowed_post_fix_statuses(spec))
    states: list[Dict[str, Any]] = []
    for entry_index, entry in enumerate(expected_states):
        if not isinstance(entry, Mapping):
            raise ValueError(
                f"{spec.lane_id}: expected_post_fix_entry_states[{entry_index}] "
                "must be an object"
            )
        entry_id = _normalized_expected_text(
            entry.get("id"),
            field_name=f"{spec.lane_id}: expected_post_fix_entry_states[{entry_index}].id",
        )
        post_fix_status = _normalized_expected_text(
            entry.get("post_fix_status"),
            field_name=(
                f"{spec.lane_id}: expected_post_fix_entry_states[{entry_id}]"
                ".post_fix_status"
            ),
        )
        if post_fix_status not in allowed_statuses:
            raise ValueError(
                f"{spec.lane_id}: expected_post_fix_entry_states[{entry_id}]"
                ".post_fix_status is not allowed"
            )
        pending_proof_obligation_count = _normalized_expected_count(
            entry.get("pending_proof_obligation_count", 0),
            field_name=(
                f"{spec.lane_id}: expected_post_fix_entry_states[{entry_id}]"
                ".pending_proof_obligation_count"
            ),
        )
        pending_retry_obligation_count = _normalized_expected_count(
            entry.get("pending_retry_obligation_count", 0),
            field_name=(
                f"{spec.lane_id}: expected_post_fix_entry_states[{entry_id}]"
                ".pending_retry_obligation_count"
            ),
        )
        required_completion_action_count = _normalized_expected_count(
            entry.get(
                "required_completion_action_count",
                pending_proof_obligation_count + pending_retry_obligation_count,
            ),
            field_name=(
                f"{spec.lane_id}: expected_post_fix_entry_states[{entry_id}]"
                ".required_completion_action_count"
            ),
        )
        if (
            post_fix_status != "pending_proof"
            and pending_proof_obligation_count != 0
        ):
            raise ValueError(
                f"{spec.lane_id}: expected_post_fix_entry_states[{entry_id}]"
                ".pending_proof_obligation_count is only valid for pending_proof"
            )
        if (
            post_fix_status != "pending_retry"
            and pending_retry_obligation_count != 0
        ):
            raise ValueError(
                f"{spec.lane_id}: expected_post_fix_entry_states[{entry_id}]"
                ".pending_retry_obligation_count is only valid for pending_retry"
            )
        if post_fix_status == "pending_proof" and pending_proof_obligation_count == 0:
            raise ValueError(
                f"{spec.lane_id}: expected_post_fix_entry_states[{entry_id}]"
                ".pending_proof_obligation_count must be positive"
            )
        if post_fix_status == "pending_retry" and pending_retry_obligation_count == 0:
            raise ValueError(
                f"{spec.lane_id}: expected_post_fix_entry_states[{entry_id}]"
                ".pending_retry_obligation_count must be positive"
            )
        if (
            post_fix_status == "pending_proof"
            and required_completion_action_count != pending_proof_obligation_count
        ):
            raise ValueError(
                f"{spec.lane_id}: expected_post_fix_entry_states[{entry_id}]"
                ".required_completion_action_count must match pending_proof_obligation_count"
            )
        if (
            post_fix_status == "pending_retry"
            and required_completion_action_count != pending_retry_obligation_count
        ):
            raise ValueError(
                f"{spec.lane_id}: expected_post_fix_entry_states[{entry_id}]"
                ".required_completion_action_count must match pending_retry_obligation_count"
            )
        states.append(
            {
                "id": entry_id,
                "function": _normalized_expected_text(
                    entry.get("function"),
                    field_name=(
                        f"{spec.lane_id}: expected_post_fix_entry_states[{entry_id}]"
                        ".function"
                    ),
                ),
                "binary_pair": _normalized_expected_text(
                    entry.get("binary_pair"),
                    field_name=(
                        f"{spec.lane_id}: expected_post_fix_entry_states[{entry_id}]"
                        ".binary_pair"
                    ),
                ),
                "post_fix_status": post_fix_status,
                "pending_proof_obligation_count": pending_proof_obligation_count,
                "pending_retry_obligation_count": pending_retry_obligation_count,
                "required_completion_action_count": required_completion_action_count,
            }
        )
    _reject_duplicate_expected_entry_ids(
        states,
        field_name=f"{spec.lane_id}: expected_post_fix_entry_states",
    )
    if states and len(states) != _normalized_expected_entry_count(spec):
        raise ValueError(
            f"{spec.lane_id}: expected_post_fix_entry_states count must match "
            "expected_entry_count"
        )
    return states


def _normalized_expected_required_action_hashes(
    spec: Phase3PostFixGateSpec,
) -> list[Dict[str, str]]:
    expected_hashes = spec.expected_required_completion_action_hashes
    if not isinstance(expected_hashes, (list, tuple)):
        raise ValueError(
            f"{spec.lane_id}: expected_required_completion_action_hashes must be a sequence"
        )
    hashes: list[Dict[str, str]] = []
    for entry_index, entry in enumerate(expected_hashes):
        if not isinstance(entry, Mapping):
            raise ValueError(
                f"{spec.lane_id}: expected_required_completion_action_hashes[{entry_index}] "
                "must be an object"
            )
        entry_id = _normalized_expected_text(
            entry.get("id"),
            field_name=(
                f"{spec.lane_id}: expected_required_completion_action_hashes"
                f"[{entry_index}].id"
            ),
        )
        digest = _normalized_expected_text(
            entry.get("required_completion_actions_sha256"),
            field_name=(
                f"{spec.lane_id}: expected_required_completion_action_hashes"
                f"[{entry_id}].required_completion_actions_sha256"
            ),
        )
        if not _is_sha256_hex(digest):
            raise ValueError(
                f"{spec.lane_id}: expected_required_completion_action_hashes"
                f"[{entry_id}].required_completion_actions_sha256 must be sha256 hex"
            )
        hashes.append(
            {
                "id": entry_id,
                "required_completion_actions_sha256": digest,
            }
        )
    _reject_duplicate_expected_entry_ids(
        hashes,
        field_name=f"{spec.lane_id}: expected_required_completion_action_hashes",
    )
    if hashes and len(hashes) != _normalized_expected_entry_count(spec):
        raise ValueError(
            f"{spec.lane_id}: expected_required_completion_action_hashes count must match "
            "expected_entry_count"
        )
    return hashes


def _validate_expected_spec_consistency(spec: Phase3PostFixGateSpec) -> None:
    identities = _normalized_expected_entry_identities(spec)
    states = _normalized_expected_entry_states(spec)
    action_hashes = _normalized_expected_required_action_hashes(spec)
    if not states:
        if action_hashes:
            raise ValueError(
                f"{spec.lane_id}: expected_required_completion_action_hashes "
                "requires expected_post_fix_entry_states"
            )
        return
    state_identities = [
        {
            "id": state["id"],
            "function": state["function"],
            "binary_pair": state["binary_pair"],
        }
        for state in states
    ]
    if identities and not _strict_json_equal(identities, state_identities):
        raise ValueError(
            f"{spec.lane_id}: expected_post_fix_entry_identities must match "
            "expected_post_fix_entry_states"
        )
    status_counts = _normalized_expected_status_counts(spec)
    state_status_counts = _expected_status_counts_from_entry_states(states)
    if status_counts and not _strict_json_equal(status_counts, state_status_counts):
        raise ValueError(
            f"{spec.lane_id}: expected_post_fix_status_counts must match "
            "expected_post_fix_entry_states"
        )
    obligation_counts = _normalized_expected_obligation_counts(spec)
    state_obligation_counts = _expected_obligation_counts_from_entry_states(states)
    if obligation_counts and not _strict_json_equal(obligation_counts, state_obligation_counts):
        raise ValueError(
            f"{spec.lane_id}: expected_post_fix_obligation_counts must match "
            "expected_post_fix_entry_states"
        )
    if action_hashes and [item["id"] for item in action_hashes] != [
        state["id"] for state in states
    ]:
        raise ValueError(
            f"{spec.lane_id}: expected_required_completion_action_hashes must match "
            "expected_post_fix_entry_states"
        )


def _expected_status_counts_from_entry_states(
    states: Sequence[Mapping[str, Any]],
) -> Dict[str, int]:
    counts: Dict[str, int] = {}
    for state in states:
        status = state.get("post_fix_status")
        if not isinstance(status, str):
            continue
        counts[status] = counts.get(status, 0) + 1
    return dict(sorted(counts.items()))


def _expected_obligation_counts_from_entry_states(
    states: Sequence[Mapping[str, Any]],
) -> Dict[str, int]:
    counts = _empty_obligation_counts()
    for state in states:
        pending_proof_count = _int_count(state.get("pending_proof_obligation_count"))
        pending_retry_count = _int_count(state.get("pending_retry_obligation_count"))
        if pending_proof_count:
            counts["pending_proof_entry_count"] += 1
            counts["pending_proof_obligation_count"] += pending_proof_count
        if pending_retry_count:
            counts["pending_retry_entry_count"] += 1
            counts["pending_retry_obligation_count"] += pending_retry_count
    return dict(sorted(counts.items()))


def _normalized_expected_obligation_counts(spec: Phase3PostFixGateSpec) -> Dict[str, int]:
    counts = spec.expected_post_fix_obligation_counts
    if counts is None:
        return {}
    if not isinstance(counts, Mapping):
        raise ValueError(f"{spec.lane_id}: expected_post_fix_obligation_counts must be an object")
    if not counts:
        return {}
    normalized = _empty_obligation_counts()
    for key, count in sorted(counts.items(), key=lambda item: str(item[0])):
        key_text = _normalized_expected_text(
            key,
            field_name=f"{spec.lane_id}: expected_post_fix_obligation_counts key",
        )
        if key_text not in OBLIGATION_COUNT_KEYS:
            raise ValueError(
                f"{spec.lane_id}: expected_post_fix_obligation_counts[{key_text}] "
                "is not a recognized obligation count"
            )
        normalized[key_text] = _normalized_expected_count(
            count,
            field_name=f"{spec.lane_id}: expected_post_fix_obligation_counts[{key_text}]",
        )
    return dict(sorted(normalized.items()))


def _reject_duplicate_expected_entry_ids(
    entries: Sequence[Mapping[str, Any]],
    *,
    field_name: str,
) -> None:
    seen: set[str] = set()
    duplicates: list[str] = []
    for entry in entries:
        entry_id = entry.get("id")
        if not isinstance(entry_id, str):
            continue
        if entry_id in seen and entry_id not in duplicates:
            duplicates.append(entry_id)
        seen.add(entry_id)
    if duplicates:
        raise ValueError(f"{field_name} must have unique ids: {duplicates!r}")


def _normalized_expected_count(value: Any, *, field_name: str) -> int:
    if not _is_non_negative_int_count(value):
        raise ValueError(f"{field_name} must be a non-negative integer count")
    return value


def _normalized_expected_text(value: Any, *, field_name: str) -> str:
    if not _specific_text(value):
        raise ValueError(f"{field_name} must be a concrete non-empty string")
    return value


def _is_sha256_hex(value: str) -> bool:
    return len(value) == 64 and all(char in "0123456789abcdef" for char in value)


def _valid_created_at(value: Any) -> bool:
    if not _specific_text(value):
        return False
    try:
        parsed = datetime.fromisoformat(value)
    except ValueError:
        return False
    return parsed.tzinfo is not None


def _expected_post_fix_obligation_counts_from_specs(
    specs: Sequence[Phase3PostFixGateSpec],
) -> Dict[str, int]:
    counts = _empty_obligation_counts()
    any_expected = False
    for spec in specs:
        expected = _normalized_expected_obligation_counts(spec)
        if not expected:
            continue
        any_expected = True
        for key, count in expected.items():
            counts[key] = counts.get(key, 0) + count
    return dict(sorted(counts.items())) if any_expected else {}


def phase3_post_fix_gate_index_text_summary(manifest: Mapping[str, Any]) -> str:
    """Return a compact operator-facing summary for a built gate index."""

    summary = manifest.get("summary")
    failed = (
        summary.get("failed", MISSING_SENTINEL)
        if isinstance(summary, Mapping)
        else MISSING_SENTINEL
    )
    ready = manifest.get("phase3_post_fix_gates_ready", MISSING_SENTINEL)
    status_counts = manifest.get("post_fix_status_counts")
    obligation_counts = manifest.get("post_fix_obligation_counts")
    lines = [
        "Phase 3 post-fix gate summary",
        f"ready={ready} failed_checks={failed}",
        f"post_fix_status_counts={_format_count_mapping(status_counts)}",
        f"post_fix_obligation_counts={_format_count_mapping(obligation_counts)}",
        "lanes:",
    ]
    for gate in manifest.get("gates") or ():
        if not isinstance(gate, Mapping):
            continue
        lane_number = gate.get("lane_number", MISSING_SENTINEL)
        lane_id = gate.get("lane_id", MISSING_SENTINEL)
        gate_ready = gate.get("ready_value", gate.get("ready", MISSING_SENTINEL))
        entry_count = gate.get("entry_count", MISSING_SENTINEL)
        gate_status_counts = _format_count_mapping(gate.get("post_fix_status_counts"))
        gate_obligation_counts = _format_obligation_counts(
            gate.get("post_fix_obligation_summary")
        )
        lines.append(
            "  "
            f"lane{lane_number} {lane_id}: "
            f"ready={gate_ready} entries={entry_count} "
            f"statuses={gate_status_counts} obligations={gate_obligation_counts}"
        )
    return "\n".join(lines)


def _format_count_mapping(value: Any) -> str:
    if not isinstance(value, Mapping) or not value:
        return "{}"
    return "{" + ", ".join(
        f"{key}:{value[key]}" for key in sorted(value, key=str)
    ) + "}"


def _format_obligation_counts(value: Any) -> str:
    if not isinstance(value, Mapping):
        return "{}"
    counts = {
        key: value.get(key)
        for key in OBLIGATION_COUNT_KEYS
        if isinstance(value.get(key), int) and value.get(key) > 0
    }
    return _format_count_mapping(counts)


def main(argv: Optional[Sequence[str]] = None) -> int:
    parser = argparse.ArgumentParser(
        description="Build a Phase 3 post-fix gate artifact index.",
    )
    parser.add_argument("--repo-root", default=".")
    parser.add_argument("--output-dir", required=True)
    parser.add_argument("--require-ready", action="store_true")
    parser.add_argument(
        "--print-summary",
        action="store_true",
        help="Print a compact lane/status summary after writing the index.",
    )
    args = parser.parse_args(argv)
    path = build_phase3_post_fix_gate_index(
        repo_root=Path(args.repo_root),
        output_dir=Path(args.output_dir),
    )
    manifest = _read_json(path)
    if args.require_ready:
        validate_phase3_post_fix_gate_index(manifest, repo_root=Path(args.repo_root))
    print(path)
    if args.print_summary:
        print(phase3_post_fix_gate_index_text_summary(manifest))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
