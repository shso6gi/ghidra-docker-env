# -*- coding: utf-8 -*-

import json
import typing
from pathlib import Path

import pytest

from scripts.function_tracer_pcode.validation import phase3_lane_index
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


def _write_manifest(
    root: Path,
    spec: Phase3LaneSpec,
    *,
    ready=True,
    target_reason_ids=None,
    implementation_lane_id=None,
    implementation_target_reason_id=None,
    implementation_lane_reason_ids=None,
    proof_completion_gate=None,
    entries=None,
) -> None:
    path = root / spec.manifest_relpath
    path.parent.mkdir(parents=True, exist_ok=True)
    impl_target = (
        implementation_target_reason_id
        if implementation_target_reason_id is not None
        else next(iter(spec.target_reason_ids), "<missing>")
    )
    implementation_manifest = {
        "lane_id": implementation_lane_id or spec.lane_id,
        "target_reason_id": impl_target,
        "lane_reason_ids": list(
            implementation_lane_reason_ids
            if implementation_lane_reason_ids is not None
            else spec.target_reason_ids
        ),
        "baseline_mode": "unit-test",
    }
    if proof_completion_gate is not None:
        implementation_manifest["proof_completion_gate"] = proof_completion_gate
    elif spec.pending_proof_keeps_final_result is not None:
        implementation_manifest["proof_completion_gate"] = {
            "eq_allowed_without_completed_proof": False,
            "pending_proof_keeps_final_result": spec.pending_proof_keeps_final_result,
            "completion_required_for_recovery": list(spec.completion_required_for_recovery or ()),
            "required_recovery_actions": list(spec.required_recovery_actions or ()),
        }
    path.write_text(
        json.dumps(
            {
                "manifest_kind": spec.manifest_kind,
                spec.ready_key: ready,
                "target_reason_ids": list(target_reason_ids if target_reason_ids is not None else spec.target_reason_ids),
                "entries": list(
                    entries
                    if entries is not None
                    else (
                        {
                            "id": f"{spec.lane_id}-representative",
                            "function": f"{spec.lane_id}_function",
                            "binary_pair": "B1_B2",
                        },
                    )
                ),
                "implementation_manifest": implementation_manifest,
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
    assert DEFAULT_PHASE3_LANE_SPECS[0].target_reason_ids == ("return_coverage_gap",)
    assert DEFAULT_PHASE3_LANE_SPECS[0].lane_reason_ids == (
        "return_coverage_gap",
        "return_coverage_inconclusive",
    )
    assert all(spec.lane_reason_ids is None for spec in DEFAULT_PHASE3_LANE_SPECS[1:])
    assert DEFAULT_PHASE3_LANE_SPECS[0].pending_proof_keeps_final_result == "UNKNOWN"
    assert DEFAULT_PHASE3_LANE_SPECS[8].pending_proof_keeps_final_result == "TIMEOUT"
    assert DEFAULT_PHASE3_LANE_SPECS[0].required_recovery_actions == ("return_coverage_proof_required",)
    assert DEFAULT_PHASE3_LANE_SPECS[8].required_recovery_actions == ("solver_timeout_retry",)


def test_phase3_lane_index_type_hints_resolve():
    hints = typing.get_type_hints(phase3_lane_index._implementation_reason_ids)

    assert hints["return"] == tuple[str, ...]


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


def test_phase3_lane_index_rejects_implementation_reason_drift(tmp_path):
    baseline = tmp_path / "baseline"
    repo = tmp_path / "repo"
    _write_baseline(baseline)
    specs = _specs()
    for spec in specs:
        _write_manifest(
            baseline,
            spec,
            implementation_target_reason_id="wrong_reason" if spec.lane_id == "lane_two" else None,
            implementation_lane_reason_ids=("wrong_reason",) if spec.lane_id == "lane_two" else None,
        )
        _write_runner(repo, spec)

    path = build_phase3_lane_index(
        baseline_root=baseline,
        repo_root=repo,
        output_dir=tmp_path / "out",
        lane_specs=specs,
    )
    manifest = json.loads(path.read_text())

    assert manifest["phase3_lanes_ready"] is False
    assert "phase3_lane_implementation_reason_ids" in manifest["summary"]["failed_kinds"]
    assert "phase3_lane_target_reason_ids" not in manifest["summary"]["failed_kinds"]


def test_phase3_lane_index_rejects_implementation_reason_scope_expansion(tmp_path):
    baseline = tmp_path / "baseline"
    repo = tmp_path / "repo"
    _write_baseline(baseline)
    specs = _specs()
    for spec in specs:
        _write_manifest(
            baseline,
            spec,
            implementation_lane_reason_ids=(
                tuple(spec.target_reason_ids) + ("unexpected_reason",)
                if spec.lane_id == "lane_two"
                else None
            ),
        )
        _write_runner(repo, spec)

    path = build_phase3_lane_index(
        baseline_root=baseline,
        repo_root=repo,
        output_dir=tmp_path / "out",
        lane_specs=specs,
    )
    manifest = json.loads(path.read_text())

    assert manifest["phase3_lanes_ready"] is False
    assert "phase3_lane_implementation_reason_ids" in manifest["summary"]["failed_kinds"]
    assert "phase3_lane_target_reason_ids" not in manifest["summary"]["failed_kinds"]


def test_phase3_lane_index_rejects_implementation_lane_id_drift(tmp_path):
    baseline = tmp_path / "baseline"
    repo = tmp_path / "repo"
    _write_baseline(baseline)
    specs = _specs()
    for spec in specs:
        _write_manifest(
            baseline,
            spec,
            implementation_lane_id="wrong_lane" if spec.lane_id == "lane_two" else None,
        )
        _write_runner(repo, spec)

    path = build_phase3_lane_index(
        baseline_root=baseline,
        repo_root=repo,
        output_dir=tmp_path / "out",
        lane_specs=specs,
    )
    manifest = json.loads(path.read_text())

    assert manifest["phase3_lanes_ready"] is False
    assert "phase3_lane_implementation_lane_id" in manifest["summary"]["failed_kinds"]


def test_phase3_lane_index_rejects_missing_representative_entries(tmp_path):
    baseline = tmp_path / "baseline"
    repo = tmp_path / "repo"
    _write_baseline(baseline)
    specs = _specs()
    for spec in specs:
        _write_manifest(
            baseline,
            spec,
            entries=[] if spec.lane_id == "lane_two" else None,
        )
        _write_runner(repo, spec)

    path = build_phase3_lane_index(
        baseline_root=baseline,
        repo_root=repo,
        output_dir=tmp_path / "out",
        lane_specs=specs,
    )
    manifest = json.loads(path.read_text())

    assert manifest["phase3_lanes_ready"] is False
    assert "phase3_lane_representative_entries_present" in manifest["summary"]["failed_kinds"]


def test_phase3_lane_index_rejects_incomplete_representative_entries(tmp_path):
    baseline = tmp_path / "baseline"
    repo = tmp_path / "repo"
    _write_baseline(baseline)
    specs = _specs()
    for spec in specs:
        _write_manifest(
            baseline,
            spec,
            entries=(
                [{"id": "missing-binary-pair", "function": "sample"}]
                if spec.lane_id == "lane_two"
                else None
            ),
        )
        _write_runner(repo, spec)

    path = build_phase3_lane_index(
        baseline_root=baseline,
        repo_root=repo,
        output_dir=tmp_path / "out",
        lane_specs=specs,
    )
    manifest = json.loads(path.read_text())

    assert manifest["phase3_lanes_ready"] is False
    assert "phase3_lane_representative_entries_concrete" in manifest["summary"]["failed_kinds"]


def test_phase3_lane_index_accepts_expected_proof_completion_gate(tmp_path):
    baseline = tmp_path / "baseline"
    repo = tmp_path / "repo"
    _write_baseline(baseline)
    spec = Phase3LaneSpec(
        lane_number=1,
        lane_id="proof_lane",
        target_reason_ids=("proof_reason",),
        manifest_relpath="audit/proof_lane/manifest.json",
        runner_relpath="run_proof_lane.sh",
        manifest_kind="proof_lane_manifest",
        ready_key="proof_lane_ready",
        pending_proof_keeps_final_result="UNKNOWN",
        completion_required_for_recovery=("stage_one",),
        required_recovery_actions=("action_one",),
    )
    _write_manifest(
        baseline,
        spec,
        proof_completion_gate={
            "eq_allowed_without_completed_proof": False,
            "pending_proof_keeps_final_result": "UNKNOWN",
            "completion_required_for_recovery": ["stage_one"],
            "required_recovery_action": "action_one",
        },
    )
    _write_runner(repo, spec)

    path = build_phase3_lane_index(
        baseline_root=baseline,
        repo_root=repo,
        output_dir=tmp_path / "out",
        lane_specs=(spec,),
    )
    manifest = json.loads(path.read_text())

    assert manifest["phase3_lanes_ready"] is True
    assert manifest["lanes"][0]["proof_completion_gate"] == {
        "eq_allowed_without_completed_proof": False,
        "pending_proof_keeps_final_result": "UNKNOWN",
        "completion_required_for_recovery": ["stage_one"],
        "required_recovery_actions": ["action_one"],
    }
    validate_phase3_lane_index(manifest)


def test_phase3_lane_index_rejects_proof_completion_gate_drift(tmp_path):
    baseline = tmp_path / "baseline"
    repo = tmp_path / "repo"
    _write_baseline(baseline)
    spec = Phase3LaneSpec(
        lane_number=1,
        lane_id="timeout_lane",
        target_reason_ids=("solver_unknown_timeout",),
        manifest_relpath="audit/timeout_lane/manifest.json",
        runner_relpath="run_timeout_lane.sh",
        manifest_kind="timeout_lane_manifest",
        ready_key="timeout_lane_ready",
        pending_proof_keeps_final_result="TIMEOUT",
        completion_required_for_recovery=("solver_timeout_retry",),
        required_recovery_actions=("solver_timeout_retry",),
    )
    _write_manifest(
        baseline,
        spec,
        proof_completion_gate={
            "eq_allowed_without_completed_proof": False,
            "pending_proof_keeps_final_result": "UNKNOWN",
            "completion_required_for_recovery": ["solver_timeout_retry"],
            "required_recovery_actions": ["solver_timeout_retry"],
        },
    )
    _write_runner(repo, spec)

    path = build_phase3_lane_index(
        baseline_root=baseline,
        repo_root=repo,
        output_dir=tmp_path / "out",
        lane_specs=(spec,),
    )
    manifest = json.loads(path.read_text())

    assert manifest["phase3_lanes_ready"] is False
    assert "phase3_lane_proof_completion_gate" in manifest["summary"]["failed_kinds"]


def test_phase3_lane_index_rejects_proof_completion_gate_eq_without_proof(tmp_path):
    baseline = tmp_path / "baseline"
    repo = tmp_path / "repo"
    _write_baseline(baseline)
    spec = Phase3LaneSpec(
        lane_number=1,
        lane_id="proof_lane",
        target_reason_ids=("proof_reason",),
        manifest_relpath="audit/proof_lane/manifest.json",
        runner_relpath="run_proof_lane.sh",
        manifest_kind="proof_lane_manifest",
        ready_key="proof_lane_ready",
        pending_proof_keeps_final_result="UNKNOWN",
        completion_required_for_recovery=("stage_one",),
        required_recovery_actions=("action_one",),
    )
    _write_manifest(
        baseline,
        spec,
        proof_completion_gate={
            "eq_allowed_without_completed_proof": True,
            "pending_proof_keeps_final_result": "UNKNOWN",
            "completion_required_for_recovery": ["stage_one"],
            "required_recovery_actions": ["action_one"],
        },
    )
    _write_runner(repo, spec)

    path = build_phase3_lane_index(
        baseline_root=baseline,
        repo_root=repo,
        output_dir=tmp_path / "out",
        lane_specs=(spec,),
    )
    manifest = json.loads(path.read_text())

    assert manifest["phase3_lanes_ready"] is False
    assert "phase3_lane_proof_completion_gate" in manifest["summary"]["failed_kinds"]


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
