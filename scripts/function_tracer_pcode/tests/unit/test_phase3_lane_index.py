# -*- coding: utf-8 -*-

import json
from pathlib import Path

import pytest

from scripts.function_tracer_pcode.validation.phase3_lane_index import (
    DEFAULT_PHASE3_LANE_SPECS,
    Phase3LaneSpec,
    build_phase3_lane_index,
    validate_phase3_lane_index,
)


def _write_baseline(root: Path, *, baseline_id: str = "observed-v0@0a53352") -> None:
    raw = root / "raw"
    raw.mkdir(parents=True)
    (raw / "artifact_manifest.json").write_text(
        json.dumps(
            {
                "baseline_id": baseline_id,
                "git_head": "0a53352cf3c9528abfb654906ed7b963474bedc5",
            },
            sort_keys=True,
        )
    )


def _write_manifest(root: Path, spec: Phase3LaneSpec, *, ready=True, target_reason_ids=None) -> None:
    path = root / spec.manifest_relpath
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(
        json.dumps(
            {
                "manifest_kind": spec.manifest_kind,
                spec.ready_key: ready,
                "target_reason_ids": list(target_reason_ids if target_reason_ids is not None else spec.target_reason_ids),
                "implementation_manifest": {
                    "lane_id": spec.lane_id,
                    "target_reason_id": next(iter(spec.target_reason_ids), "<missing>"),
                    "baseline_mode": "unit-test",
                },
            },
            sort_keys=True,
        )
    )


def _write_runner(repo: Path, spec: Phase3LaneSpec, *, executable=True) -> None:
    path = repo / spec.runner_relpath
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text("#!/usr/bin/env bash\nset -euo pipefail\n")
    path.chmod(0o755 if executable else 0o644)


def _validator(manifest):
    if manifest.get("validator_should_fail"):
        raise ValueError("validator failure")


def _specs():
    return (
        Phase3LaneSpec(
            lane_number=1,
            lane_id="lane_one",
            target_reason_ids=("reason_one",),
            manifest_relpath="audit/lane_one/manifest.json",
            runner_relpath="run_lane_one.sh",
            manifest_kind="lane_one_manifest",
            ready_key="lane_one_ready",
            validator=_validator,
        ),
        Phase3LaneSpec(
            lane_number=2,
            lane_id="lane_two",
            target_reason_ids=("reason_two",),
            manifest_relpath="audit/lane_two/manifest.json",
            runner_relpath="run_lane_two.sh",
            manifest_kind="lane_two_manifest",
            ready_key="lane_two_ready",
            validator=_validator,
        ),
    )


def test_phase3_lane_index_builds_ready_index_for_custom_specs(tmp_path):
    baseline = tmp_path / "baseline"
    repo = tmp_path / "repo"
    _write_baseline(baseline)
    for spec in _specs():
        _write_manifest(baseline, spec)
        _write_runner(repo, spec)

    path = build_phase3_lane_index(
        baseline_root=baseline,
        repo_root=repo,
        output_dir=tmp_path / "out",
        lane_specs=_specs(),
    )

    manifest = json.loads(path.read_text())
    assert manifest["manifest_kind"] == "phase3_proof_lane_index"
    assert manifest["phase3_lanes_ready"] is True
    assert [lane["lane_id"] for lane in manifest["lanes"]] == ["lane_one", "lane_two"]
    assert all(lane["manifest_sha256"] != "<missing>" for lane in manifest["lanes"])
    assert all(lane["runner_sha256"] != "<missing>" for lane in manifest["lanes"])
    validate_phase3_lane_index(manifest)


def test_phase3_lane_index_default_specs_cover_all_plan_lanes():
    assert [spec.lane_number for spec in DEFAULT_PHASE3_LANE_SPECS] == list(range(1, 10))
    assert [spec.lane_id for spec in DEFAULT_PHASE3_LANE_SPECS] == [
        "phase3_return_coverage_lane1",
        "phase3_return_width_bridge_lane2",
        "phase3_readonly_identity_lane3",
        "phase3_method_b_closure_lane4",
        "phase3_sat_unsafety_lane5",
        "phase3_unresolved_expression_lane6",
        "phase3_solver_rewrite_lane7",
        "phase3_solver_rewrite_proof_lane8",
        "phase3_solver_timeout_lane9",
    ]
    assert [spec.runner_relpath for spec in DEFAULT_PHASE3_LANE_SPECS] == [
        "phase3_run_function_call_return_coverage_lane1_representatives.sh",
        "phase3_run_function_call_return_width_bridge_lane2_representatives.sh",
        "phase3_run_loop_readonly_identity_lane3_representatives.sh",
        "phase3_run_loop_method_b_closure_lane4_representatives.sh",
        "phase3_run_function_call_sat_unsafety_lane5_representatives.sh",
        "phase3_run_function_call_unresolved_expression_lane6_representatives.sh",
        "phase3_run_loop_solver_rewrite_lane7_representatives.sh",
        "phase3_run_function_call_solver_rewrite_proof_lane8_representatives.sh",
        "phase3_run_function_call_solver_timeout_lane9_representatives.sh",
    ]


def test_phase3_lane_index_rejects_missing_manifest(tmp_path):
    baseline = tmp_path / "baseline"
    repo = tmp_path / "repo"
    _write_baseline(baseline)
    specs = _specs()
    _write_manifest(baseline, specs[0])
    for spec in specs:
        _write_runner(repo, spec)

    path = build_phase3_lane_index(
        baseline_root=baseline,
        repo_root=repo,
        output_dir=tmp_path / "out",
        lane_specs=specs,
    )
    manifest = json.loads(path.read_text())

    assert manifest["phase3_lanes_ready"] is False
    assert "phase3_lane_manifest_present" in manifest["summary"]["failed_kinds"]
    with pytest.raises(ValueError, match="phase3_lane_manifest_present"):
        validate_phase3_lane_index(manifest)


def test_phase3_lane_index_rejects_target_reason_drift(tmp_path):
    baseline = tmp_path / "baseline"
    repo = tmp_path / "repo"
    _write_baseline(baseline)
    specs = _specs()
    for spec in specs:
        _write_manifest(
            baseline,
            spec,
            target_reason_ids=("wrong_reason",) if spec.lane_id == "lane_two" else None,
        )
        _write_runner(repo, spec)

    path = build_phase3_lane_index(
        baseline_root=baseline,
        repo_root=repo,
        output_dir=tmp_path / "out",
        lane_specs=specs,
    )
    manifest = json.loads(path.read_text())

    assert "phase3_lane_target_reason_ids" in manifest["summary"]["failed_kinds"]


def test_phase3_lane_index_rejects_validator_failure(tmp_path):
    baseline = tmp_path / "baseline"
    repo = tmp_path / "repo"
    _write_baseline(baseline)
    specs = _specs()
    for spec in specs:
        _write_manifest(baseline, spec)
        _write_runner(repo, spec)
    failing_path = baseline / specs[1].manifest_relpath
    payload = json.loads(failing_path.read_text())
    payload["validator_should_fail"] = True
    failing_path.write_text(json.dumps(payload, sort_keys=True))

    path = build_phase3_lane_index(
        baseline_root=baseline,
        repo_root=repo,
        output_dir=tmp_path / "out",
        lane_specs=specs,
    )
    manifest = json.loads(path.read_text())

    assert "phase3_lane_validator" in manifest["summary"]["failed_kinds"]


def test_phase3_lane_index_rejects_wrong_baseline_id(tmp_path):
    baseline = tmp_path / "baseline"
    repo = tmp_path / "repo"
    _write_baseline(baseline, baseline_id="wrong-baseline")
    for spec in _specs():
        _write_manifest(baseline, spec)
        _write_runner(repo, spec)

    path = build_phase3_lane_index(
        baseline_root=baseline,
        repo_root=repo,
        output_dir=tmp_path / "out",
        lane_specs=_specs(),
    )
    manifest = json.loads(path.read_text())

    assert "baseline_id" in manifest["summary"]["failed_kinds"]


def test_phase3_lane_index_rejects_missing_runner(tmp_path):
    baseline = tmp_path / "baseline"
    repo = tmp_path / "repo"
    _write_baseline(baseline)
    specs = _specs()
    for spec in specs:
        _write_manifest(baseline, spec)
    _write_runner(repo, specs[0])

    path = build_phase3_lane_index(
        baseline_root=baseline,
        repo_root=repo,
        output_dir=tmp_path / "out",
        lane_specs=specs,
    )
    manifest = json.loads(path.read_text())

    assert manifest["phase3_lanes_ready"] is False
    assert "phase3_lane_runner_present" in manifest["summary"]["failed_kinds"]


def test_phase3_lane_index_rejects_non_executable_runner(tmp_path):
    baseline = tmp_path / "baseline"
    repo = tmp_path / "repo"
    _write_baseline(baseline)
    specs = _specs()
    for spec in specs:
        _write_manifest(baseline, spec)
        _write_runner(repo, spec, executable=spec.lane_id != "lane_two")

    path = build_phase3_lane_index(
        baseline_root=baseline,
        repo_root=repo,
        output_dir=tmp_path / "out",
        lane_specs=specs,
    )
    manifest = json.loads(path.read_text())

    assert manifest["phase3_lanes_ready"] is False
    assert "phase3_lane_runner_executable" in manifest["summary"]["failed_kinds"]
