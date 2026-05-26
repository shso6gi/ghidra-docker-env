# -*- coding: utf-8 -*-

import hashlib
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
    category="function_call",
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
                            "category": category,
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


def _manifest_sha256(root: Path, spec: Phase3LaneSpec) -> str:
    return hashlib.sha256((root / spec.manifest_relpath).read_bytes()).hexdigest()


def _write_runner(
    repo: Path,
    spec: Phase3LaneSpec,
    *,
    executable=True,
    manifest_sha256=None,
    manifest_relpath=None,
    target_category=None,
    pair_category=None,
    base_category=None,
    matrix_category=None,
    safety_defaults=None,
    require_ready_arg=False,
    invoke_gate_args=False,
    target_functions=None,
    pair_filter=None,
) -> None:
    path = repo / spec.runner_relpath
    path.parent.mkdir(parents=True, exist_ok=True)
    declared_manifest = manifest_relpath or f"artifacts/baselines/observed-v0@0a53352/{spec.manifest_relpath}"
    lines = [
        "#!/usr/bin/env bash",
        "set -euo pipefail",
    ]
    if manifest_sha256 is not None:
        lines.extend(
            [
                f'PHASE3_MANIFEST_PATH="${{PHASE3_MANIFEST_PATH:-$SCRIPT_DIR/{declared_manifest}}}"',
                f'PHASE3_MANIFEST_SHA256="${{PHASE3_MANIFEST_SHA256:-{manifest_sha256}}}"',
            ]
        )
    if safety_defaults is not None:
        for name, value in safety_defaults.items():
            prefix = "export " if name != "PHASE3_REQUIRE_READY" else ""
            lines.append(f'{prefix}{name}="${{{name}:-{value}}}"')
    if target_category is not None:
        if target_category == "function_call":
            target_var = "FUNCTION_CALL_TARGET_SET"
        else:
            target_var = "LOOP_TARGET_SET"
        resolved_pair_category = pair_category or target_category
        if resolved_pair_category == "function_call":
            pair_var = "FUNCTION_CALL_PAIR_FILTER"
        else:
            pair_var = "LOOP_PAIR_FILTER"
        lines.extend(
            [
                f'export {target_var}="${{{target_var}:-{",".join(target_functions or ())}}}"',
                f'export {pair_var}="${{{pair_var}:-{",".join(pair_filter or ())}}}"',
                f'export BASE_PATH="${{BASE_PATH:-$SCRIPT_DIR/{_base_path_for_category(base_category or target_category)}}}"',
            ]
        )
        lines.append(f'bash "$SCRIPT_DIR/{_matrix_script_for_category(matrix_category or target_category)}"')
    if require_ready_arg:
        lines.extend(
            [
                'if [[ "$PHASE3_REQUIRE_READY" != "0" ]]; then',
                "    PHASE3_GATE_ARGS+=(--require-ready)",
                "fi",
            ]
        )
    if invoke_gate_args:
        lines.extend(
            [
                '"$PYTHON_BIN" -m scripts.function_tracer_pcode.validation.phase3_runner_safety_lane \\',
                '    "${PHASE3_GATE_ARGS[@]}"',
            ]
        )
    path.write_text("\n".join(lines) + "\n")
    path.chmod(0o755 if executable else 0o644)


def _safety_defaults(**overrides):
    defaults = {
        "VALIDATION_AUTO_BEFORE_SNAPSHOT": "0",
        "VALIDATION_REQUIRE_BEFORE_DELTA": "0",
        "VALIDATION_REQUIRE_BASELINE_MATCH": "0",
        "VALIDATION_SKIP_COMPLETED": "0",
        "VALIDATION_REQUIRE_PHASE2_OBJECT_KEYS": "1",
        "VALIDATION_RUNNER_DRY_RUN": "0",
        "PHASE3_REQUIRE_READY": "1",
    }
    defaults.update(overrides)
    return defaults


def _base_path_for_category(category: str) -> str:
    if category == "function_call":
        return "targets/cate1/function_call_test"
    return "targets/cate1/loop_method_b_test"


def _matrix_script_for_category(category: str) -> str:
    if category == "function_call":
        return "func_call_run_matrix_all_parallel_multifunc.sh"
    return "loop_run_matrix_all_parallel_multifunc.sh"


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
    assert all(spec.require_runner_manifest_ref for spec in DEFAULT_PHASE3_LANE_SPECS)
    assert all(spec.require_runner_target_filter for spec in DEFAULT_PHASE3_LANE_SPECS)
    assert all(spec.require_runner_safety_defaults for spec in DEFAULT_PHASE3_LANE_SPECS)


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


def test_phase3_lane_index_accepts_runner_manifest_ref(tmp_path):
    baseline = tmp_path / "baseline"
    repo = tmp_path / "repo"
    _write_baseline(baseline)
    spec = Phase3LaneSpec(
        lane_number=1,
        lane_id="runner_manifest_lane",
        target_reason_ids=("reason_one",),
        manifest_relpath="audit/runner_manifest_lane/manifest.json",
        runner_relpath="run_runner_manifest_lane.sh",
        manifest_kind="runner_manifest_lane_manifest",
        ready_key="runner_manifest_lane_ready",
        require_runner_manifest_ref=True,
    )
    _write_manifest(baseline, spec)
    _write_runner(repo, spec, manifest_sha256=_manifest_sha256(baseline, spec))

    path = build_phase3_lane_index(
        baseline_root=baseline,
        repo_root=repo,
        output_dir=tmp_path / "out",
        lane_specs=(spec,),
    )
    manifest = json.loads(path.read_text())

    assert manifest["phase3_lanes_ready"] is True
    lane = manifest["lanes"][0]
    assert lane["runner_manifest_relpath"] == "artifacts/baselines/observed-v0@0a53352/audit/runner_manifest_lane/manifest.json"
    assert lane["runner_manifest_sha256"] == lane["manifest_sha256"]


def test_phase3_lane_index_rejects_runner_manifest_path_drift(tmp_path):
    baseline = tmp_path / "baseline"
    repo = tmp_path / "repo"
    _write_baseline(baseline)
    spec = Phase3LaneSpec(
        lane_number=1,
        lane_id="runner_manifest_lane",
        target_reason_ids=("reason_one",),
        manifest_relpath="audit/runner_manifest_lane/manifest.json",
        runner_relpath="run_runner_manifest_lane.sh",
        manifest_kind="runner_manifest_lane_manifest",
        ready_key="runner_manifest_lane_ready",
        require_runner_manifest_ref=True,
    )
    _write_manifest(baseline, spec)
    _write_runner(
        repo,
        spec,
        manifest_sha256=_manifest_sha256(baseline, spec),
        manifest_relpath="artifacts/baselines/observed-v0@0a53352/audit/other_lane/manifest.json",
    )

    path = build_phase3_lane_index(
        baseline_root=baseline,
        repo_root=repo,
        output_dir=tmp_path / "out",
        lane_specs=(spec,),
    )
    manifest = json.loads(path.read_text())

    assert manifest["phase3_lanes_ready"] is False
    assert "phase3_lane_runner_manifest_path" in manifest["summary"]["failed_kinds"]


def test_phase3_lane_index_rejects_runner_manifest_sha_drift(tmp_path):
    baseline = tmp_path / "baseline"
    repo = tmp_path / "repo"
    _write_baseline(baseline)
    spec = Phase3LaneSpec(
        lane_number=1,
        lane_id="runner_manifest_lane",
        target_reason_ids=("reason_one",),
        manifest_relpath="audit/runner_manifest_lane/manifest.json",
        runner_relpath="run_runner_manifest_lane.sh",
        manifest_kind="runner_manifest_lane_manifest",
        ready_key="runner_manifest_lane_ready",
        require_runner_manifest_ref=True,
    )
    _write_manifest(baseline, spec)
    _write_runner(repo, spec, manifest_sha256="0" * 64)

    path = build_phase3_lane_index(
        baseline_root=baseline,
        repo_root=repo,
        output_dir=tmp_path / "out",
        lane_specs=(spec,),
    )
    manifest = json.loads(path.read_text())

    assert manifest["phase3_lanes_ready"] is False
    assert "phase3_lane_runner_manifest_sha256" in manifest["summary"]["failed_kinds"]


def test_phase3_lane_index_accepts_runner_target_filter(tmp_path):
    baseline = tmp_path / "baseline"
    repo = tmp_path / "repo"
    _write_baseline(baseline)
    spec = Phase3LaneSpec(
        lane_number=1,
        lane_id="runner_target_lane",
        target_reason_ids=("reason_one",),
        manifest_relpath="audit/runner_target_lane/manifest.json",
        runner_relpath="run_runner_target_lane.sh",
        manifest_kind="runner_target_lane_manifest",
        ready_key="runner_target_lane_ready",
        require_runner_target_filter=True,
    )
    _write_manifest(
        baseline,
        spec,
        entries=[
            {
                "id": "entry-one",
                "category": "function_call",
                "function": "sample_one",
                "binary_pair": "B1_B2",
            },
            {
                "id": "entry-two",
                "category": "function_call",
                "function": "sample_two",
                "binary_pair": "B3_B4",
            },
        ],
    )
    _write_runner(
        repo,
        spec,
        target_category="function_call",
        target_functions=("sample_one", "sample_two"),
        pair_filter=("sample_one:B1_B2", "sample_two:B3_B4"),
    )

    path = build_phase3_lane_index(
        baseline_root=baseline,
        repo_root=repo,
        output_dir=tmp_path / "out",
        lane_specs=(spec,),
    )
    manifest = json.loads(path.read_text())

    assert manifest["phase3_lanes_ready"] is True
    lane = manifest["lanes"][0]
    assert lane["expected_target_functions"] == ["sample_one", "sample_two"]
    assert lane["runner_target_var"] == "FUNCTION_CALL_TARGET_SET"
    assert lane["runner_pair_filter_var"] == "FUNCTION_CALL_PAIR_FILTER"
    assert lane["runner_base_path_relpath"] == "targets/cate1/function_call_test"
    assert lane["runner_matrix_script_relpath"] == "func_call_run_matrix_all_parallel_multifunc.sh"
    assert lane["runner_pair_filter"] == ["sample_one:B1_B2", "sample_two:B3_B4"]


def test_phase3_lane_index_rejects_runner_target_filter_drift(tmp_path):
    baseline = tmp_path / "baseline"
    repo = tmp_path / "repo"
    _write_baseline(baseline)
    spec = Phase3LaneSpec(
        lane_number=1,
        lane_id="runner_target_lane",
        target_reason_ids=("reason_one",),
        manifest_relpath="audit/runner_target_lane/manifest.json",
        runner_relpath="run_runner_target_lane.sh",
        manifest_kind="runner_target_lane_manifest",
        ready_key="runner_target_lane_ready",
        require_runner_target_filter=True,
    )
    _write_manifest(baseline, spec)
    _write_runner(
        repo,
        spec,
        target_category="function_call",
        target_functions=("wrong_function",),
        pair_filter=("wrong_function:B1_B2",),
    )

    path = build_phase3_lane_index(
        baseline_root=baseline,
        repo_root=repo,
        output_dir=tmp_path / "out",
        lane_specs=(spec,),
    )
    manifest = json.loads(path.read_text())

    assert manifest["phase3_lanes_ready"] is False
    assert "phase3_lane_runner_target_set" in manifest["summary"]["failed_kinds"]
    assert "phase3_lane_runner_pair_filter" in manifest["summary"]["failed_kinds"]


def test_phase3_lane_index_rejects_runner_target_category_drift(tmp_path):
    baseline = tmp_path / "baseline"
    repo = tmp_path / "repo"
    _write_baseline(baseline)
    spec = Phase3LaneSpec(
        lane_number=1,
        lane_id="runner_target_lane",
        target_reason_ids=("reason_one",),
        manifest_relpath="audit/runner_target_lane/manifest.json",
        runner_relpath="run_runner_target_lane.sh",
        manifest_kind="runner_target_lane_manifest",
        ready_key="runner_target_lane_ready",
        require_runner_target_filter=True,
    )
    _write_manifest(baseline, spec, category="loop")
    _write_runner(
        repo,
        spec,
        target_category="function_call",
        target_functions=("runner_target_lane_function",),
        pair_filter=("runner_target_lane_function:B1_B2",),
    )

    path = build_phase3_lane_index(
        baseline_root=baseline,
        repo_root=repo,
        output_dir=tmp_path / "out",
        lane_specs=(spec,),
    )
    manifest = json.loads(path.read_text())

    assert manifest["phase3_lanes_ready"] is False
    assert "phase3_lane_runner_target_category" in manifest["summary"]["failed_kinds"]


def test_phase3_lane_index_accepts_runner_safety_defaults(tmp_path):
    baseline = tmp_path / "baseline"
    repo = tmp_path / "repo"
    _write_baseline(baseline)
    spec = Phase3LaneSpec(
        lane_number=1,
        lane_id="runner_safety_lane",
        target_reason_ids=("reason_one",),
        manifest_relpath="audit/runner_safety_lane/manifest.json",
        runner_relpath="run_runner_safety_lane.sh",
        manifest_kind="runner_safety_lane_manifest",
        ready_key="runner_safety_lane_ready",
        require_runner_safety_defaults=True,
    )
    _write_manifest(baseline, spec)
    _write_runner(
        repo,
        spec,
        safety_defaults=_safety_defaults(),
        require_ready_arg=True,
        invoke_gate_args=True,
    )

    path = build_phase3_lane_index(
        baseline_root=baseline,
        repo_root=repo,
        output_dir=tmp_path / "out",
        lane_specs=(spec,),
    )
    manifest = json.loads(path.read_text())

    assert manifest["phase3_lanes_ready"] is True
    lane = manifest["lanes"][0]
    assert lane["runner_safety_defaults"] == _safety_defaults()
    assert lane["runner_safety_duplicate_vars"] == []
    assert lane["runner_require_ready_arg_present"] is True
    assert lane["runner_gate_args_invoked"] is True


def test_phase3_lane_index_rejects_runner_safety_default_drift(tmp_path):
    baseline = tmp_path / "baseline"
    repo = tmp_path / "repo"
    _write_baseline(baseline)
    spec = Phase3LaneSpec(
        lane_number=1,
        lane_id="runner_safety_lane",
        target_reason_ids=("reason_one",),
        manifest_relpath="audit/runner_safety_lane/manifest.json",
        runner_relpath="run_runner_safety_lane.sh",
        manifest_kind="runner_safety_lane_manifest",
        ready_key="runner_safety_lane_ready",
        require_runner_safety_defaults=True,
    )
    _write_manifest(baseline, spec)
    _write_runner(
        repo,
        spec,
        safety_defaults=_safety_defaults(VALIDATION_REQUIRE_PHASE2_OBJECT_KEYS="0"),
        require_ready_arg=True,
        invoke_gate_args=True,
    )

    path = build_phase3_lane_index(
        baseline_root=baseline,
        repo_root=repo,
        output_dir=tmp_path / "out",
        lane_specs=(spec,),
    )
    manifest = json.loads(path.read_text())

    assert manifest["phase3_lanes_ready"] is False
    assert "phase3_lane_runner_safety_defaults" in manifest["summary"]["failed_kinds"]


def test_phase3_lane_index_rejects_runner_missing_require_ready_arg(tmp_path):
    baseline = tmp_path / "baseline"
    repo = tmp_path / "repo"
    _write_baseline(baseline)
    spec = Phase3LaneSpec(
        lane_number=1,
        lane_id="runner_safety_lane",
        target_reason_ids=("reason_one",),
        manifest_relpath="audit/runner_safety_lane/manifest.json",
        runner_relpath="run_runner_safety_lane.sh",
        manifest_kind="runner_safety_lane_manifest",
        ready_key="runner_safety_lane_ready",
        require_runner_safety_defaults=True,
    )
    _write_manifest(baseline, spec)
    _write_runner(repo, spec, safety_defaults=_safety_defaults(), require_ready_arg=False, invoke_gate_args=True)

    path = build_phase3_lane_index(
        baseline_root=baseline,
        repo_root=repo,
        output_dir=tmp_path / "out",
        lane_specs=(spec,),
    )
    manifest = json.loads(path.read_text())

    assert manifest["phase3_lanes_ready"] is False
    assert "phase3_lane_runner_require_ready_arg" in manifest["summary"]["failed_kinds"]


def test_phase3_lane_index_rejects_runner_commented_safety_defaults(tmp_path):
    baseline = tmp_path / "baseline"
    repo = tmp_path / "repo"
    _write_baseline(baseline)
    spec = Phase3LaneSpec(
        lane_number=1,
        lane_id="runner_safety_lane",
        target_reason_ids=("reason_one",),
        manifest_relpath="audit/runner_safety_lane/manifest.json",
        runner_relpath="run_runner_safety_lane.sh",
        manifest_kind="runner_safety_lane_manifest",
        ready_key="runner_safety_lane_ready",
        require_runner_safety_defaults=True,
    )
    _write_manifest(baseline, spec)
    path = repo / spec.runner_relpath
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(
        "\n".join(
            [
                "#!/usr/bin/env bash",
                '# export VALIDATION_RUNNER_DRY_RUN="${VALIDATION_RUNNER_DRY_RUN:-0}"',
                '# PHASE3_REQUIRE_READY="${PHASE3_REQUIRE_READY:-1}"',
                "# PHASE3_GATE_ARGS+=(--require-ready)",
                '# "$PYTHON_BIN" -m scripts.function_tracer_pcode.validation.phase3_runner_safety_lane \\',
                '#     "${PHASE3_GATE_ARGS[@]}"',
            ]
        )
        + "\n"
    )
    path.chmod(0o755)

    index_path = build_phase3_lane_index(
        baseline_root=baseline,
        repo_root=repo,
        output_dir=tmp_path / "out",
        lane_specs=(spec,),
    )
    manifest = json.loads(index_path.read_text())

    assert manifest["phase3_lanes_ready"] is False
    lane = manifest["lanes"][0]
    assert lane["runner_safety_defaults"] == {}
    assert lane["runner_require_ready_arg_present"] is False
    assert lane["runner_gate_args_invoked"] is False
    assert "phase3_lane_runner_safety_defaults" in manifest["summary"]["failed_kinds"]
    assert "phase3_lane_runner_require_ready_arg" in manifest["summary"]["failed_kinds"]
    assert "phase3_lane_runner_gate_args_invoked" in manifest["summary"]["failed_kinds"]


def test_phase3_lane_index_rejects_runner_duplicate_safety_defaults(tmp_path):
    baseline = tmp_path / "baseline"
    repo = tmp_path / "repo"
    _write_baseline(baseline)
    spec = Phase3LaneSpec(
        lane_number=1,
        lane_id="runner_safety_lane",
        target_reason_ids=("reason_one",),
        manifest_relpath="audit/runner_safety_lane/manifest.json",
        runner_relpath="run_runner_safety_lane.sh",
        manifest_kind="runner_safety_lane_manifest",
        ready_key="runner_safety_lane_ready",
        require_runner_safety_defaults=True,
    )
    _write_manifest(baseline, spec)
    _write_runner(
        repo,
        spec,
        safety_defaults=_safety_defaults(),
        require_ready_arg=True,
        invoke_gate_args=True,
    )
    runner_path = repo / spec.runner_relpath
    with runner_path.open("a", encoding="utf-8") as handle:
        handle.write('export VALIDATION_RUNNER_DRY_RUN="${VALIDATION_RUNNER_DRY_RUN:-0}"\n')

    path = build_phase3_lane_index(
        baseline_root=baseline,
        repo_root=repo,
        output_dir=tmp_path / "out",
        lane_specs=(spec,),
    )
    manifest = json.loads(path.read_text())

    assert manifest["phase3_lanes_ready"] is False
    assert manifest["lanes"][0]["runner_safety_duplicate_vars"] == ["VALIDATION_RUNNER_DRY_RUN"]
    assert "phase3_lane_runner_safety_defaults_unique" in manifest["summary"]["failed_kinds"]


def test_phase3_lane_index_rejects_runner_gate_args_not_invoked(tmp_path):
    baseline = tmp_path / "baseline"
    repo = tmp_path / "repo"
    _write_baseline(baseline)
    spec = Phase3LaneSpec(
        lane_number=1,
        lane_id="runner_safety_lane",
        target_reason_ids=("reason_one",),
        manifest_relpath="audit/runner_safety_lane/manifest.json",
        runner_relpath="run_runner_safety_lane.sh",
        manifest_kind="runner_safety_lane_manifest",
        ready_key="runner_safety_lane_ready",
        require_runner_safety_defaults=True,
    )
    _write_manifest(baseline, spec)
    _write_runner(repo, spec, safety_defaults=_safety_defaults(), require_ready_arg=True, invoke_gate_args=False)

    path = build_phase3_lane_index(
        baseline_root=baseline,
        repo_root=repo,
        output_dir=tmp_path / "out",
        lane_specs=(spec,),
    )
    manifest = json.loads(path.read_text())

    assert manifest["phase3_lanes_ready"] is False
    assert "phase3_lane_runner_gate_args_invoked" in manifest["summary"]["failed_kinds"]


@pytest.mark.parametrize(
    "fake_command",
    (
        'echo \'"$PYTHON_BIN" -m scripts.function_tracer_pcode.validation.fake "${PHASE3_GATE_ARGS[@]}"\'',
        'GATE_CALL=\'"$PYTHON_BIN" -m scripts.function_tracer_pcode.validation.fake "${PHASE3_GATE_ARGS[@]}"\'',
    ),
)
def test_phase3_lane_index_rejects_non_executed_gate_args_strings(tmp_path, fake_command):
    baseline = tmp_path / "baseline"
    repo = tmp_path / "repo"
    _write_baseline(baseline)
    spec = Phase3LaneSpec(
        lane_number=1,
        lane_id="runner_safety_lane",
        target_reason_ids=("reason_one",),
        manifest_relpath="audit/runner_safety_lane/manifest.json",
        runner_relpath="run_runner_safety_lane.sh",
        manifest_kind="runner_safety_lane_manifest",
        ready_key="runner_safety_lane_ready",
        require_runner_safety_defaults=True,
    )
    _write_manifest(baseline, spec)
    _write_runner(repo, spec, safety_defaults=_safety_defaults(), require_ready_arg=True, invoke_gate_args=False)
    runner_path = repo / spec.runner_relpath
    with runner_path.open("a", encoding="utf-8") as handle:
        handle.write(fake_command + "\n")

    path = build_phase3_lane_index(
        baseline_root=baseline,
        repo_root=repo,
        output_dir=tmp_path / "out",
        lane_specs=(spec,),
    )
    manifest = json.loads(path.read_text())

    assert manifest["phase3_lanes_ready"] is False
    assert manifest["lanes"][0]["runner_gate_args_invoked"] is False
    assert "phase3_lane_runner_gate_args_invoked" in manifest["summary"]["failed_kinds"]


@pytest.mark.parametrize(
    ("target_category", "pair_category", "function_name"),
    (
        ("function_call", "loop", "runner_target_lane_function"),
        ("loop", "function_call", "runner_target_lane_function"),
    ),
)
def test_phase3_lane_index_rejects_runner_target_pair_env_var_mismatch(
    tmp_path,
    target_category,
    pair_category,
    function_name,
):
    baseline = tmp_path / "baseline"
    repo = tmp_path / "repo"
    _write_baseline(baseline)
    spec = Phase3LaneSpec(
        lane_number=1,
        lane_id="runner_target_lane",
        target_reason_ids=("reason_one",),
        manifest_relpath="audit/runner_target_lane/manifest.json",
        runner_relpath="run_runner_target_lane.sh",
        manifest_kind="runner_target_lane_manifest",
        ready_key="runner_target_lane_ready",
        require_runner_target_filter=True,
    )
    _write_manifest(baseline, spec, category=target_category)
    _write_runner(
        repo,
        spec,
        target_category=target_category,
        pair_category=pair_category,
        target_functions=(function_name,),
        pair_filter=(f"{function_name}:B1_B2",),
    )

    path = build_phase3_lane_index(
        baseline_root=baseline,
        repo_root=repo,
        output_dir=tmp_path / "out",
        lane_specs=(spec,),
    )
    manifest = json.loads(path.read_text())

    assert manifest["phase3_lanes_ready"] is False
    assert "phase3_lane_runner_pair_filter_var" in manifest["summary"]["failed_kinds"]
    assert "phase3_lane_runner_target_set" not in manifest["summary"]["failed_kinds"]
    assert "phase3_lane_runner_pair_filter" not in manifest["summary"]["failed_kinds"]


@pytest.mark.parametrize(
    ("target_category", "base_category"),
    (
        ("function_call", "loop"),
        ("loop", "function_call"),
    ),
)
def test_phase3_lane_index_rejects_runner_base_path_category_mismatch(
    tmp_path,
    target_category,
    base_category,
):
    baseline = tmp_path / "baseline"
    repo = tmp_path / "repo"
    _write_baseline(baseline)
    spec = Phase3LaneSpec(
        lane_number=1,
        lane_id="runner_target_lane",
        target_reason_ids=("reason_one",),
        manifest_relpath="audit/runner_target_lane/manifest.json",
        runner_relpath="run_runner_target_lane.sh",
        manifest_kind="runner_target_lane_manifest",
        ready_key="runner_target_lane_ready",
        require_runner_target_filter=True,
    )
    _write_manifest(baseline, spec, category=target_category)
    _write_runner(
        repo,
        spec,
        target_category=target_category,
        base_category=base_category,
        target_functions=("runner_target_lane_function",),
        pair_filter=("runner_target_lane_function:B1_B2",),
    )

    path = build_phase3_lane_index(
        baseline_root=baseline,
        repo_root=repo,
        output_dir=tmp_path / "out",
        lane_specs=(spec,),
    )
    manifest = json.loads(path.read_text())

    assert manifest["phase3_lanes_ready"] is False
    assert "phase3_lane_runner_base_path" in manifest["summary"]["failed_kinds"]
    assert "phase3_lane_runner_target_set" not in manifest["summary"]["failed_kinds"]
    assert "phase3_lane_runner_pair_filter" not in manifest["summary"]["failed_kinds"]


@pytest.mark.parametrize(
    ("target_category", "matrix_category"),
    (
        ("function_call", "loop"),
        ("loop", "function_call"),
    ),
)
def test_phase3_lane_index_rejects_runner_matrix_script_category_mismatch(
    tmp_path,
    target_category,
    matrix_category,
):
    baseline = tmp_path / "baseline"
    repo = tmp_path / "repo"
    _write_baseline(baseline)
    spec = Phase3LaneSpec(
        lane_number=1,
        lane_id="runner_target_lane",
        target_reason_ids=("reason_one",),
        manifest_relpath="audit/runner_target_lane/manifest.json",
        runner_relpath="run_runner_target_lane.sh",
        manifest_kind="runner_target_lane_manifest",
        ready_key="runner_target_lane_ready",
        require_runner_target_filter=True,
    )
    _write_manifest(baseline, spec, category=target_category)
    _write_runner(
        repo,
        spec,
        target_category=target_category,
        matrix_category=matrix_category,
        target_functions=("runner_target_lane_function",),
        pair_filter=("runner_target_lane_function:B1_B2",),
    )

    path = build_phase3_lane_index(
        baseline_root=baseline,
        repo_root=repo,
        output_dir=tmp_path / "out",
        lane_specs=(spec,),
    )
    manifest = json.loads(path.read_text())

    assert manifest["phase3_lanes_ready"] is False
    assert "phase3_lane_runner_matrix_script" in manifest["summary"]["failed_kinds"]
    assert "phase3_lane_runner_target_set" not in manifest["summary"]["failed_kinds"]
    assert "phase3_lane_runner_pair_filter" not in manifest["summary"]["failed_kinds"]


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
