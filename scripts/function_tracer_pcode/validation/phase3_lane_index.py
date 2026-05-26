# -*- coding: utf-8 -*-
"""Build a fixed index over Phase 3 proof-lane audit manifests."""

from __future__ import annotations

import argparse
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


@dataclass(frozen=True)
class Phase3LaneSpec:
    lane_number: int
    lane_id: str
    target_reason_ids: Sequence[str]
    manifest_relpath: str
    manifest_kind: str
    ready_key: str
    validator: Optional[LaneValidator] = None


DEFAULT_PHASE3_LANE_SPECS: Sequence[Phase3LaneSpec] = (
    Phase3LaneSpec(
        lane_number=1,
        lane_id="phase3_return_coverage_lane1",
        target_reason_ids=("return_coverage_gap",),
        manifest_relpath="audit/phase3_return_coverage_lane1_reclassification/return_coverage_lane1_representatives.json",
        manifest_kind="phase3_return_coverage_lane1_representatives",
        ready_key="phase3_lane1_ready",
        validator=validate_phase3_return_coverage_lane1_manifest,
    ),
    Phase3LaneSpec(
        lane_number=2,
        lane_id="phase3_return_width_bridge_lane2",
        target_reason_ids=("return_width_bridge_missing",),
        manifest_relpath="audit/phase3_return_width_bridge_lane2/return_width_bridge_lane2_representatives.json",
        manifest_kind="phase3_return_width_bridge_lane2_representatives",
        ready_key="phase3_lane2_ready",
        validator=validate_phase3_return_width_bridge_lane2_manifest,
    ),
    Phase3LaneSpec(
        lane_number=3,
        lane_id="phase3_readonly_identity_lane3",
        target_reason_ids=("readonly_identity_missing",),
        manifest_relpath="audit/phase3_readonly_identity_lane3/readonly_identity_lane3_representatives.json",
        manifest_kind="phase3_readonly_identity_lane3_representatives",
        ready_key="phase3_lane3_ready",
        validator=validate_phase3_readonly_identity_lane3_manifest,
    ),
    Phase3LaneSpec(
        lane_number=4,
        lane_id="phase3_method_b_closure_lane4",
        target_reason_ids=("method_b_closure_blocked",),
        manifest_relpath="audit/phase3_method_b_closure_lane4/method_b_closure_lane4_representatives.json",
        manifest_kind="phase3_method_b_closure_lane4_representatives",
        ready_key="phase3_lane4_ready",
        validator=validate_phase3_method_b_closure_lane4_manifest,
    ),
    Phase3LaneSpec(
        lane_number=5,
        lane_id="phase3_sat_unsafety_lane5",
        target_reason_ids=("sat_unsafety",),
        manifest_relpath="audit/phase3_sat_unsafety_lane5/sat_unsafety_lane5_representatives.json",
        manifest_kind="phase3_sat_unsafety_lane5_representatives",
        ready_key="phase3_lane5_ready",
        validator=validate_phase3_sat_unsafety_lane5_manifest,
    ),
    Phase3LaneSpec(
        lane_number=6,
        lane_id="phase3_unresolved_expression_lane6",
        target_reason_ids=("unresolved_expression",),
        manifest_relpath="audit/phase3_unresolved_expression_lane6/unresolved_expression_lane6_representatives.json",
        manifest_kind="phase3_unresolved_expression_lane6_representatives",
        ready_key="phase3_lane6_ready",
        validator=validate_phase3_unresolved_expression_lane6_manifest,
    ),
    Phase3LaneSpec(
        lane_number=7,
        lane_id="phase3_solver_rewrite_lane7",
        target_reason_ids=("solver_proven_rewrite_no_change",),
        manifest_relpath="audit/phase3_solver_rewrite_lane7/solver_rewrite_lane7_representatives.json",
        manifest_kind="phase3_solver_rewrite_lane7_representatives",
        ready_key="phase3_lane7_ready",
        validator=validate_phase3_solver_rewrite_lane7_manifest,
    ),
    Phase3LaneSpec(
        lane_number=8,
        lane_id="phase3_solver_rewrite_proof_lane8",
        target_reason_ids=("solver_proven_rewrite_proof_failed",),
        manifest_relpath="audit/phase3_solver_rewrite_proof_lane8/solver_rewrite_proof_lane8_representatives.json",
        manifest_kind="phase3_solver_rewrite_proof_lane8_representatives",
        ready_key="phase3_lane8_ready",
        validator=validate_phase3_solver_rewrite_proof_lane8_manifest,
    ),
    Phase3LaneSpec(
        lane_number=9,
        lane_id="phase3_solver_timeout_lane9",
        target_reason_ids=("solver_unknown_timeout",),
        manifest_relpath="audit/phase3_solver_timeout_lane9/solver_timeout_lane9_representatives.json",
        manifest_kind="phase3_solver_timeout_lane9_representatives",
        ready_key="phase3_lane9_ready",
        validator=validate_phase3_solver_timeout_lane9_manifest,
    ),
)


def build_phase3_lane_index(
    *,
    baseline_root: Path,
    output_dir: Path,
    lane_specs: Sequence[Phase3LaneSpec] = DEFAULT_PHASE3_LANE_SPECS,
) -> Path:
    """Write a Phase 3 lane index manifest and return its path."""

    root = Path(baseline_root)
    output = Path(output_dir)
    output.mkdir(parents=True, exist_ok=True)
    baseline_manifest = _read_json(root / "raw" / "artifact_manifest.json")
    lanes = [_materialize_lane(root, spec) for spec in lane_specs]
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


def _materialize_lane(root: Path, spec: Phase3LaneSpec) -> Dict[str, Any]:
    path = root / spec.manifest_relpath
    lane: Dict[str, Any] = {
        "lane_number": spec.lane_number,
        "lane_id": spec.lane_id,
        "target_reason_ids": list(spec.target_reason_ids),
        "manifest_ref": _file_ref(path),
        "manifest_relpath": spec.manifest_relpath,
        "expected_manifest_kind": spec.manifest_kind,
        "ready_key": spec.ready_key,
        "status": "missing",
        "manifest_sha256": MISSING_SENTINEL,
        "observed_manifest_kind": MISSING_SENTINEL,
        "ready_value": MISSING_SENTINEL,
        "validator_status": "not_run",
    }
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
    implementation = manifest.get("implementation_manifest")
    if isinstance(implementation, Mapping):
        lane["implementation_manifest"] = {
            "lane_id": implementation.get("lane_id") or MISSING_SENTINEL,
            "target_reason_id": implementation.get("target_reason_id") or MISSING_SENTINEL,
            "baseline_mode": implementation.get("baseline_mode") or MISSING_SENTINEL,
        }
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


def main(argv: Optional[Sequence[str]] = None) -> int:
    parser = argparse.ArgumentParser(description="Build the Phase 3 proof-lane index manifest.")
    parser.add_argument(
        "--baseline-root",
        type=Path,
        default=Path("artifacts/baselines/observed-v0@0a53352"),
        help="baseline artifact root containing raw/ and audit/",
    )
    parser.add_argument("--output-dir", type=Path, required=True)
    parser.add_argument("--require-ready", action="store_true")
    args = parser.parse_args(argv)

    path = build_phase3_lane_index(
        baseline_root=args.baseline_root,
        output_dir=args.output_dir,
    )
    print(path)
    if args.require_ready:
        validate_phase3_lane_index(_read_json(path))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
