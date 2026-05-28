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


DEFAULT_BASELINE_GIT_HEAD = phase3_lane_index.BASELINE_GIT_HEAD


def _write_baseline(
    root: Path,
    *,
    baseline_id: str = "observed-v0@0a53352",
    git_head: str | None = DEFAULT_BASELINE_GIT_HEAD,
) -> None:
    raw = root / "raw"
    raw.mkdir(parents=True)
    payload = {"baseline_id": baseline_id}
    if git_head is not None:
        payload["git_head"] = git_head
    (raw / "artifact_manifest.json").write_text(json.dumps(payload, sort_keys=True))


def _baseline_raw_ref(root: Path) -> dict[str, str]:
    raw_manifest_path = root / "raw" / "artifact_manifest.json"
    return {
        "path": str(raw_manifest_path),
        "sha256": hashlib.sha256(raw_manifest_path.read_bytes()).hexdigest(),
    }


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
    manifest_version=1,
    artifact_role="unit_test_phase3_lane_manifest",
    baseline_id=None,
    baseline_git_head=None,
    include_baseline_git_head=True,
    baseline_raw_artifact_ref=None,
    readiness=None,
    include_readiness=True,
    entries=None,
) -> None:
    path = root / spec.manifest_relpath
    path.parent.mkdir(parents=True, exist_ok=True)
    raw_manifest_path = root / "raw" / "artifact_manifest.json"
    baseline_manifest = json.loads(raw_manifest_path.read_text())
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
    payload = {
        spec.ready_key: ready,
        "baseline_id": baseline_id if baseline_id is not None else baseline_manifest["baseline_id"],
        "baseline_raw_artifact_ref": (
            baseline_raw_artifact_ref
            if baseline_raw_artifact_ref is not None
            else _baseline_raw_ref(root)
        ),
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
    }
    if include_baseline_git_head:
        payload["baseline_git_head"] = (
            baseline_git_head if baseline_git_head is not None else baseline_manifest["git_head"]
        )
    if manifest_version is not None:
        payload["manifest_version"] = manifest_version
    if artifact_role is not None:
        payload["artifact_role"] = artifact_role
    payload["manifest_kind"] = spec.manifest_kind
    if readiness is not None:
        payload["readiness"] = readiness
    elif include_readiness and ready is True:
        payload["readiness"] = {
            "ready": True,
            "failure_kinds": [],
            "failure_counts": {},
            "ready_entries": len(payload["entries"]),
            "failed_entries": 0,
        }
    path.write_text(json.dumps(payload, sort_keys=True))


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
    current_log_root_category=None,
    baseline_log_root_category=None,
    baseline_log_root_var_category=None,
    safety_defaults=None,
    require_ready_arg=False,
    invoke_gate_args=False,
    gate_validator_module="scripts.function_tracer_pcode.validation.phase3_runner_safety_lane",
    include_required_gate_args=None,
    required_gate_arg_overrides=None,
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
    include_required_gate_args = (
        safety_defaults is not None
        if include_required_gate_args is None
        else include_required_gate_args
    )
    if include_required_gate_args or current_log_root_category is not None or baseline_log_root_category is not None:
        resolved_current_log_root_category = current_log_root_category or target_category or "function_call"
        resolved_baseline_log_root_category = baseline_log_root_category or resolved_current_log_root_category
        resolved_baseline_log_root_var_category = (
            baseline_log_root_var_category or resolved_baseline_log_root_category
        )
        gate_args = []
        if include_required_gate_args:
            required_gate_args = {
                "--gate-stage": "post-fix",
                "--baseline-raw-dir": '"$BASELINE_RAW_DIR"',
                "--output-dir": '"$PHASE3_GATE_OUTPUT_DIR"',
                "--phase3-manifest": '"$PHASE3_MANIFEST_PATH"',
                "--phase3-manifest-sha256": '"$PHASE3_MANIFEST_SHA256"',
            }
            required_gate_args.update(required_gate_arg_overrides or {})
            gate_args.extend(f"    {flag} {value}" for flag, value in required_gate_args.items())
        if current_log_root_category is not None or baseline_log_root_category is not None:
            gate_args.extend(
                [
                    f'    --current-log-root "{resolved_current_log_root_category}=$OUTPUT_BASE_DIR"',
                    (
                        f'    --baseline-log-root "{resolved_baseline_log_root_category}'
                        f'=${_baseline_log_root_var_for_category(resolved_baseline_log_root_var_category)}"'
                    ),
                ]
            )
        lines.extend(["PHASE3_GATE_ARGS=(", *gate_args, ")"])
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
                f'"$PYTHON_BIN" -m {gate_validator_module} \\',
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


def _expected_runner_safety_gate_smoke_argv():
    return [
        "-m",
        "scripts.function_tracer_pcode.validation.phase3_runner_safety_lane",
        "--gate-stage",
        "post-fix",
        "--baseline-raw-dir",
        "$BASELINE_RAW_DIR",
        "--output-dir",
        "$PHASE3_GATE_OUTPUT_DIR",
        "--phase3-manifest",
        "$PHASE3_MANIFEST_PATH",
        "--phase3-manifest-sha256",
        "$PHASE3_MANIFEST_SHA256",
        "--require-ready",
    ]


def _base_path_for_category(category: str) -> str:
    if category == "function_call":
        return "targets/cate1/function_call_test"
    return "targets/cate1/loop_method_b_test"


def _matrix_script_for_category(category: str) -> str:
    if category == "function_call":
        return "func_call_run_matrix_all_parallel_multifunc.sh"
    return "loop_run_matrix_all_parallel_multifunc.sh"


def _baseline_log_root_var_for_category(category: str) -> str:
    if category == "function_call":
        return "BASELINE_FUNCTION_CALL_LOG_ROOT"
    return "BASELINE_LOOP_LOG_ROOT"


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
    assert manifest["summary"]["failed_kind_counts"] == {}
    assert manifest["summary"]["failed_lanes"] == []
    assert manifest["summary"]["failed_index_kinds"] == []
    assert [lane["lane_id"] for lane in manifest["lanes"]] == ["lane_one", "lane_two"]
    assert all(lane["manifest_sha256"] != "<missing>" for lane in manifest["lanes"])
    assert all(lane["runner_sha256"] != "<missing>" for lane in manifest["lanes"])
    for lane in manifest["lanes"]:
        assert lane["observed_manifest_version"] == 1
        assert lane["observed_artifact_role"] == "unit_test_phase3_lane_manifest"
        assert lane["lane_baseline_id"] == "observed-v0@0a53352"
        assert lane["lane_baseline_git_head"] == "0a53352cf3c9528abfb654906ed7b963474bedc5"
        assert lane["lane_baseline_raw_artifact_ref"] == _baseline_raw_ref(baseline)
    validate_phase3_lane_index(manifest, lane_specs=_specs())


def test_phase3_lane_index_validator_rejects_ready_true_with_failed_summary(tmp_path):
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
    manifest["summary"]["failed"] = 1
    manifest["summary"]["failed_kinds"] = ["phase3_lane_ready"]

    with pytest.raises(ValueError, match="phase3_lanes_ready_summary_clean"):
        validate_phase3_lane_index(manifest)


def test_phase3_lane_index_validator_rejects_ready_true_with_failed_check(tmp_path):
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
    manifest["checks"].append({"kind": "phase3_lane_ready", "status": "failed"})

    with pytest.raises(ValueError, match="phase3_lanes_ready_checks_clean"):
        validate_phase3_lane_index(manifest)


def test_phase3_lane_index_validator_rejects_ready_true_identity_drift(tmp_path):
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
    manifest["baseline_git_head"] = "wrong-head"

    with pytest.raises(ValueError, match="baseline_git_head"):
        validate_phase3_lane_index(manifest)


def test_phase3_lane_index_validator_rejects_tampered_lane_without_failed_check(tmp_path):
    baseline = tmp_path / "baseline"
    repo = tmp_path / "repo"
    _write_baseline(baseline)
    specs = _specs()
    for spec in specs:
        _write_manifest(baseline, spec)
        _write_runner(repo, spec)

    path = build_phase3_lane_index(
        baseline_root=baseline,
        repo_root=repo,
        output_dir=tmp_path / "out",
        lane_specs=specs,
    )
    manifest = json.loads(path.read_text())
    manifest["lanes"][0]["lane_baseline_git_head"] = "wrong-head"

    with pytest.raises(ValueError, match="derived_failed_kinds"):
        validate_phase3_lane_index(manifest, lane_specs=specs)


def test_phase3_lane_index_validator_rejects_missing_lane_entry(tmp_path):
    baseline = tmp_path / "baseline"
    repo = tmp_path / "repo"
    _write_baseline(baseline)
    specs = _specs()
    for spec in specs:
        _write_manifest(baseline, spec)
        _write_runner(repo, spec)

    path = build_phase3_lane_index(
        baseline_root=baseline,
        repo_root=repo,
        output_dir=tmp_path / "out",
        lane_specs=specs,
    )
    manifest = json.loads(path.read_text())
    manifest["lanes"] = manifest["lanes"][:-1]

    with pytest.raises(ValueError, match="lane_specs"):
        validate_phase3_lane_index(manifest, lane_specs=specs)


def test_phase3_lane_index_validator_rejects_forged_default_index_without_default_lanes():
    manifest = {
        "manifest_version": 1,
        "manifest_kind": "phase3_proof_lane_index",
        "artifact_role": "derived_audit_lane_index",
        "baseline_id": "observed-v0@0a53352",
        "baseline_git_head": DEFAULT_BASELINE_GIT_HEAD,
        "phase3_lanes_ready": True,
        "summary": {
            "failed": 0,
            "failed_kinds": [],
        },
        "checks": [],
        "lanes": [],
    }

    with pytest.raises(ValueError, match="lane_specs"):
        validate_phase3_lane_index(manifest)


def test_phase3_lane_index_validator_recomputes_duplicate_representative_ids(tmp_path):
    baseline = tmp_path / "baseline"
    repo = tmp_path / "repo"
    _write_baseline(baseline)
    spec = _specs()[0]
    _write_manifest(baseline, spec)
    _write_runner(repo, spec)

    path = build_phase3_lane_index(
        baseline_root=baseline,
        repo_root=repo,
        output_dir=tmp_path / "out",
        lane_specs=(spec,),
    )
    manifest = json.loads(path.read_text())
    manifest["lanes"][0]["representative_entries"] = [
        {
            "index": 0,
            "id": "hidden-duplicate-representative-id",
            "function": "function_one",
            "binary_pair": "B1_B2",
        },
        {
            "index": 1,
            "id": "hidden-duplicate-representative-id",
            "function": "function_two",
            "binary_pair": "B3_B4",
        },
    ]
    manifest["lanes"][0]["representative_entry_duplicate_ids"] = []

    with pytest.raises(ValueError, match="derived_failed_kinds"):
        validate_phase3_lane_index(manifest, lane_specs=(spec,))


def test_phase3_lane_index_validator_recomputes_readiness_entry_counts_from_representatives(tmp_path):
    baseline = tmp_path / "baseline"
    repo = tmp_path / "repo"
    _write_baseline(baseline)
    spec = _specs()[0]
    _write_manifest(baseline, spec)
    _write_runner(repo, spec)

    path = build_phase3_lane_index(
        baseline_root=baseline,
        repo_root=repo,
        output_dir=tmp_path / "out",
        lane_specs=(spec,),
    )
    manifest = json.loads(path.read_text())
    manifest["lanes"][0]["manifest_readiness_ready_entries"] = 999

    with pytest.raises(ValueError, match="derived_failed_kinds"):
        validate_phase3_lane_index(manifest, lane_specs=(spec,))


def test_phase3_lane_index_validator_rejects_non_mapping_lane_entries(tmp_path):
    baseline = tmp_path / "baseline"
    repo = tmp_path / "repo"
    _write_baseline(baseline)
    specs = _specs()
    for spec in specs:
        _write_manifest(baseline, spec)
        _write_runner(repo, spec)

    path = build_phase3_lane_index(
        baseline_root=baseline,
        repo_root=repo,
        output_dir=tmp_path / "out",
        lane_specs=specs,
    )
    manifest = json.loads(path.read_text())
    manifest["lanes"][0] = "not-a-mapping"

    with pytest.raises(ValueError, match="lane_specs"):
        validate_phase3_lane_index(manifest, lane_specs=specs)


def test_phase3_lane_index_rejects_lane_manifest_version_drift(tmp_path):
    baseline = tmp_path / "baseline"
    repo = tmp_path / "repo"
    _write_baseline(baseline)
    specs = _specs()
    for spec in specs:
        _write_manifest(
            baseline,
            spec,
            manifest_version=2 if spec.lane_id == "lane_two" else 1,
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
    assert "phase3_lane_manifest_version" in manifest["summary"]["failed_kinds"]
    failed_lanes = {entry["lane_id"]: entry for entry in manifest["summary"]["failed_lanes"]}
    assert failed_lanes["lane_two"]["failed_kinds"] == ["phase3_lane_manifest_version"]


def test_phase3_lane_index_rejects_lane_manifest_missing_artifact_role(tmp_path):
    baseline = tmp_path / "baseline"
    repo = tmp_path / "repo"
    _write_baseline(baseline)
    specs = _specs()
    for spec in specs:
        _write_manifest(
            baseline,
            spec,
            artifact_role=None if spec.lane_id == "lane_two" else "unit_test_phase3_lane_manifest",
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
    assert "phase3_lane_artifact_role_present" in manifest["summary"]["failed_kinds"]
    failed_lanes = {entry["lane_id"]: entry for entry in manifest["summary"]["failed_lanes"]}
    assert failed_lanes["lane_two"]["failed_kinds"] == ["phase3_lane_artifact_role_present"]


def test_phase3_lane_index_rejects_lane_manifest_baseline_identity_drift(tmp_path):
    baseline = tmp_path / "baseline"
    repo = tmp_path / "repo"
    _write_baseline(baseline)
    specs = _specs()
    for spec in specs:
        _write_manifest(
            baseline,
            spec,
            baseline_id="wrong-baseline" if spec.lane_id == "lane_two" else None,
            baseline_git_head="wrong-head" if spec.lane_id == "lane_two" else None,
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
    assert "phase3_lane_baseline_id" in manifest["summary"]["failed_kinds"]
    assert "phase3_lane_baseline_git_head" in manifest["summary"]["failed_kinds"]
    failed_lanes = {entry["lane_id"]: entry for entry in manifest["summary"]["failed_lanes"]}
    assert failed_lanes["lane_two"]["failed_kind_counts"]["phase3_lane_baseline_id"] == 1
    assert failed_lanes["lane_two"]["failed_kind_counts"]["phase3_lane_baseline_git_head"] == 1


def test_phase3_lane_index_rejects_missing_raw_and_lane_baseline_git_head(tmp_path):
    baseline = tmp_path / "baseline"
    repo = tmp_path / "repo"
    _write_baseline(baseline, git_head=None)
    specs = _specs()
    for spec in specs:
        _write_manifest(baseline, spec, include_baseline_git_head=False)
        _write_runner(repo, spec)

    path = build_phase3_lane_index(
        baseline_root=baseline,
        repo_root=repo,
        output_dir=tmp_path / "out",
        lane_specs=specs,
    )
    manifest = json.loads(path.read_text())

    assert manifest["phase3_lanes_ready"] is False
    assert manifest["baseline_git_head"] == "<missing>"
    assert "baseline_git_head" in manifest["summary"]["failed_kinds"]
    assert "phase3_lane_baseline_git_head" in manifest["summary"]["failed_kinds"]
    assert manifest["summary"]["failed_kind_counts"]["baseline_git_head"] == 1
    assert manifest["summary"]["failed_kind_counts"]["phase3_lane_baseline_git_head"] == len(specs)
    assert manifest["summary"]["failed_index_kinds"] == ["baseline_git_head"]
    assert all(lane["lane_baseline_git_head"] == "<missing>" for lane in manifest["lanes"])
    assert all(
        lane["failed_kind_counts"]["phase3_lane_baseline_git_head"] == 1
        for lane in manifest["summary"]["failed_lanes"]
    )


def test_phase3_lane_index_rejects_wrong_raw_and_lane_baseline_git_head(tmp_path):
    baseline = tmp_path / "baseline"
    repo = tmp_path / "repo"
    _write_baseline(baseline, git_head="wrong-head")
    specs = _specs()
    for spec in specs:
        _write_manifest(baseline, spec)
        _write_runner(repo, spec)

    path = build_phase3_lane_index(
        baseline_root=baseline,
        repo_root=repo,
        output_dir=tmp_path / "out",
        lane_specs=specs,
    )
    manifest = json.loads(path.read_text())

    assert manifest["phase3_lanes_ready"] is False
    assert manifest["baseline_git_head"] == "wrong-head"
    assert "baseline_git_head" in manifest["summary"]["failed_kinds"]
    assert "phase3_lane_baseline_git_head" in manifest["summary"]["failed_kinds"]
    assert manifest["summary"]["failed_kind_counts"]["baseline_git_head"] == 1
    assert manifest["summary"]["failed_kind_counts"]["phase3_lane_baseline_git_head"] == len(specs)
    assert manifest["summary"]["failed_index_kinds"] == ["baseline_git_head"]
    assert all(lane["lane_baseline_git_head"] == "wrong-head" for lane in manifest["lanes"])
    assert all(
        lane["failed_kind_counts"]["phase3_lane_baseline_git_head"] == 1
        for lane in manifest["summary"]["failed_lanes"]
    )


def test_phase3_lane_index_rejects_lane_manifest_baseline_raw_artifact_ref_drift(tmp_path):
    baseline = tmp_path / "baseline"
    repo = tmp_path / "repo"
    _write_baseline(baseline)
    specs = _specs()
    for spec in specs:
        _write_manifest(
            baseline,
            spec,
            baseline_raw_artifact_ref={
                "path": "wrong/raw/artifact_manifest.json",
                "sha256": "0" * 64,
            } if spec.lane_id == "lane_two" else None,
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
    assert "phase3_lane_baseline_raw_artifact_ref" in manifest["summary"]["failed_kinds"]
    lane = next(lane for lane in manifest["lanes"] if lane["lane_id"] == "lane_two")
    assert lane["expected_lane_baseline_raw_artifact_ref"] == _baseline_raw_ref(baseline)
    assert lane["lane_baseline_raw_artifact_ref"] == {
        "path": "wrong/raw/artifact_manifest.json",
        "sha256": "0" * 64,
    }


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
    assert [spec.gate_validator_module for spec in DEFAULT_PHASE3_LANE_SPECS] == [
        "scripts.function_tracer_pcode.validation.phase3_return_coverage_lane1",
        "scripts.function_tracer_pcode.validation.phase3_return_width_bridge_lane2",
        "scripts.function_tracer_pcode.validation.phase3_readonly_identity_lane3",
        "scripts.function_tracer_pcode.validation.phase3_method_b_closure_lane4",
        "scripts.function_tracer_pcode.validation.phase3_sat_unsafety_lane5",
        "scripts.function_tracer_pcode.validation.phase3_unresolved_expression_lane6",
        "scripts.function_tracer_pcode.validation.phase3_solver_rewrite_lane7",
        "scripts.function_tracer_pcode.validation.phase3_solver_rewrite_proof_lane8",
        "scripts.function_tracer_pcode.validation.phase3_solver_timeout_lane9",
    ]
    assert all(spec.require_runner_manifest_ref for spec in DEFAULT_PHASE3_LANE_SPECS)
    assert all(spec.require_runner_target_filter for spec in DEFAULT_PHASE3_LANE_SPECS)
    assert all(spec.require_runner_safety_defaults for spec in DEFAULT_PHASE3_LANE_SPECS)


def test_phase3_lane_index_type_hints_resolve():
    hints = typing.get_type_hints(phase3_lane_index._implementation_reason_ids)

    assert hints["return"] == tuple[str, ...]


@pytest.mark.parametrize(
    ("code", "expected_delta"),
    (
        ("{", 1),
        ("}", -1),
        ('echo "{"', 0),
        ("echo '{'", 0),
        ('echo "${VALUE:-{}}"', 0),
        ('unused_contract() { echo "{"', 1),
        ('echo "${VALUE:-{}}" }', -1),
    ),
)
def test_phase3_lane_index_shell_brace_delta_ignores_quotes_and_parameter_expansions(
    code,
    expected_delta,
):
    assert phase3_lane_index._shell_brace_delta(code) == expected_delta


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
    assert manifest["summary"]["failed_kind_counts"]["phase3_lane_manifest_present"] == 1
    failed_lanes = {entry["lane_id"]: entry for entry in manifest["summary"]["failed_lanes"]}
    assert failed_lanes["lane_two"]["failed_kind_counts"]["phase3_lane_manifest_present"] == 1
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
    assert manifest["summary"]["failed_kind_counts"]["phase3_lane_target_reason_ids"] == 1
    failed_lanes = {entry["lane_id"]: entry for entry in manifest["summary"]["failed_lanes"]}
    assert failed_lanes["lane_two"]["failed_kinds"] == ["phase3_lane_target_reason_ids"]


def test_phase3_lane_index_records_manifest_readiness_failure_details(tmp_path):
    baseline = tmp_path / "baseline"
    repo = tmp_path / "repo"
    _write_baseline(baseline)
    spec = _specs()[0]
    _write_manifest(
        baseline,
        spec,
        ready=False,
        readiness={
            "ready": False,
            "ready_entries": 1,
            "failed_entries": 2,
            "summary": {
                "total": 3,
                "passed": 1,
                "failed": 2,
            },
            "failure_kinds": ["missing_object_key", "missing_reason_tuple"],
            "failure_counts": {
                "missing_object_key": 1,
                "missing_reason_tuple": 2,
            },
            "checks": [
                {"kind": "missing_object_key", "status": "failed"},
                {"kind": "missing_reason_tuple", "status": "failed"},
                {"kind": "missing_reason_tuple", "status": "failed"},
            ],
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
    lane = manifest["lanes"][0]

    assert manifest["phase3_lanes_ready"] is False
    assert lane["manifest_readiness_ready"] is False
    assert lane["manifest_readiness_summary"] == {"failed": 2, "passed": 1, "total": 3}
    assert lane["manifest_readiness_failure_kinds"] == [
        "missing_object_key",
        "missing_reason_tuple",
    ]
    assert lane["manifest_readiness_failure_counts"] == {
        "missing_object_key": 1,
        "missing_reason_tuple": 2,
    }
    assert lane["manifest_readiness_ready_entries"] == 1
    assert lane["manifest_readiness_failed_entries"] == 2
    assert "phase3_lane_ready" in manifest["summary"]["failed_kinds"]
    assert "phase3_lane_readiness_failure_details" not in manifest["summary"]["failed_kinds"]


def test_phase3_lane_index_rejects_ready_true_with_failed_readiness_entry_count(tmp_path):
    baseline = tmp_path / "baseline"
    repo = tmp_path / "repo"
    _write_baseline(baseline)
    spec = _specs()[0]
    _write_manifest(
        baseline,
        spec,
        ready=True,
        readiness={
            "ready": True,
            "ready_entries": 1,
            "failed_entries": 1,
            "failure_kinds": [],
            "failure_counts": {},
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
    lane = manifest["lanes"][0]

    assert manifest["phase3_lanes_ready"] is False
    assert lane["manifest_readiness_ready"] is True
    assert lane["manifest_readiness_failed_entries"] == 1
    assert "phase3_lane_readiness_entry_counts" in manifest["summary"]["failed_kinds"]
    assert "phase3_lane_readiness_consistent" not in manifest["summary"]["failed_kinds"]


def test_phase3_lane_index_rejects_readiness_entry_count_mismatch_with_representatives(tmp_path):
    baseline = tmp_path / "baseline"
    repo = tmp_path / "repo"
    _write_baseline(baseline)
    spec = _specs()[0]
    _write_manifest(
        baseline,
        spec,
        ready=True,
        readiness={
            "ready": True,
            "ready_entries": 999,
            "failed_entries": 0,
            "failure_kinds": [],
            "failure_counts": {},
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
    assert "phase3_lane_readiness_entry_counts" in manifest["summary"]["failed_kinds"]


@pytest.mark.parametrize(
    "readiness_summary",
    (
        {"total": 999, "passed": 1, "failed": 0},
        {"total": 1, "passed": 999, "failed": 0},
        {"total": 1, "passed": 1, "failed": 999},
    ),
)
def test_phase3_lane_index_rejects_readiness_summary_entry_count_mismatch(
    tmp_path,
    readiness_summary,
):
    baseline = tmp_path / "baseline"
    repo = tmp_path / "repo"
    _write_baseline(baseline)
    spec = _specs()[0]
    _write_manifest(
        baseline,
        spec,
        ready=True,
        readiness={
            "ready": True,
            "ready_entries": 1,
            "failed_entries": 0,
            "summary": readiness_summary,
            "failure_kinds": [],
            "failure_counts": {},
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
    assert "phase3_lane_readiness_entry_counts" in manifest["summary"]["failed_kinds"]


def test_phase3_lane_index_rejects_ready_false_without_readiness_failure_details(tmp_path):
    baseline = tmp_path / "baseline"
    repo = tmp_path / "repo"
    _write_baseline(baseline)
    spec = _specs()[0]
    _write_manifest(baseline, spec, ready=False)
    _write_runner(repo, spec)

    path = build_phase3_lane_index(
        baseline_root=baseline,
        repo_root=repo,
        output_dir=tmp_path / "out",
        lane_specs=(spec,),
    )
    manifest = json.loads(path.read_text())
    lane = manifest["lanes"][0]

    assert manifest["phase3_lanes_ready"] is False
    assert lane["manifest_readiness_ready"] == "<missing>"
    assert lane["manifest_readiness_failure_kinds"] == []
    assert "phase3_lane_ready" in manifest["summary"]["failed_kinds"]
    assert "phase3_lane_readiness_failure_details" in manifest["summary"]["failed_kinds"]


def test_phase3_lane_index_rejects_ready_true_without_readiness_block(tmp_path):
    baseline = tmp_path / "baseline"
    repo = tmp_path / "repo"
    _write_baseline(baseline)
    spec = _specs()[0]
    _write_manifest(baseline, spec, ready=True, include_readiness=False)
    _write_runner(repo, spec)

    path = build_phase3_lane_index(
        baseline_root=baseline,
        repo_root=repo,
        output_dir=tmp_path / "out",
        lane_specs=(spec,),
    )
    manifest = json.loads(path.read_text())
    lane = manifest["lanes"][0]

    assert manifest["phase3_lanes_ready"] is False
    assert lane["ready_value"] is True
    assert lane["manifest_readiness_ready"] == "<missing>"
    assert "phase3_lane_readiness_consistent" in manifest["summary"]["failed_kinds"]


def test_phase3_lane_index_rejects_ready_true_with_failed_readiness(tmp_path):
    baseline = tmp_path / "baseline"
    repo = tmp_path / "repo"
    _write_baseline(baseline)
    spec = _specs()[0]
    _write_manifest(
        baseline,
        spec,
        ready=True,
        readiness={
            "ready": False,
            "failure_kinds": ["missing_object_key"],
            "failure_counts": {"missing_object_key": 1},
            "ready_entries": 0,
            "failed_entries": 1,
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
    lane = manifest["lanes"][0]

    assert manifest["phase3_lanes_ready"] is False
    assert lane["ready_value"] is True
    assert lane["manifest_readiness_ready"] is False
    assert "phase3_lane_readiness_consistent" in manifest["summary"]["failed_kinds"]


def test_phase3_lane_index_records_validator_structured_failure_details(tmp_path):
    baseline = tmp_path / "baseline"
    repo = tmp_path / "repo"
    _write_baseline(baseline)
    spec = _specs()[0]
    _write_manifest(
        baseline,
        spec,
        ready=False,
        readiness={
            "ready": False,
            "summary": {"total": 1, "passed": 0, "failed": 1},
            "failure_kinds": ["validator_structured_failure"],
            "checks": [
                {"kind": "validator_structured_failure", "status": "failed"},
            ],
        },
    )
    path = baseline / spec.manifest_relpath
    payload = json.loads(path.read_text())
    payload["validator_should_fail"] = True
    path.write_text(json.dumps(payload, sort_keys=True))
    _write_runner(repo, spec)

    index_path = build_phase3_lane_index(
        baseline_root=baseline,
        repo_root=repo,
        output_dir=tmp_path / "out",
        lane_specs=(spec,),
    )
    manifest = json.loads(index_path.read_text())
    lane = manifest["lanes"][0]
    validator_check = next(
        check for check in manifest["checks"] if check["kind"] == "phase3_lane_validator"
    )

    assert lane["validator_status"] == "failed"
    assert lane["validator_failure_kinds"] == ["validator_structured_failure"]
    assert lane["validator_failure_counts"] == {"validator_structured_failure": 1}
    assert validator_check["structured_failure_kinds"] == ["validator_structured_failure"]
    assert validator_check["structured_failure_counts"] == {"validator_structured_failure": 1}
    assert "phase3_lane_validator" in manifest["summary"]["failed_kinds"]


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


def test_phase3_lane_index_rejects_duplicate_representative_entry_ids(tmp_path):
    baseline = tmp_path / "baseline"
    repo = tmp_path / "repo"
    _write_baseline(baseline)
    spec = Phase3LaneSpec(
        lane_number=1,
        lane_id="representative_lane",
        target_reason_ids=("reason_one",),
        manifest_relpath="audit/representative_lane/manifest.json",
        runner_relpath="run_representative_lane.sh",
        manifest_kind="representative_lane_manifest",
        ready_key="representative_lane_ready",
    )
    _write_manifest(
        baseline,
        spec,
        entries=(
            {
                "id": "duplicate-representative-id",
                "category": "function_call",
                "function": "representative_lane_function",
                "binary_pair": "B1_B2",
            },
            {
                "id": "duplicate-representative-id",
                "category": "function_call",
                "function": "representative_lane_other_function",
                "binary_pair": "B3_B4",
            },
        ),
    )
    _write_runner(repo, spec)

    path = build_phase3_lane_index(
        baseline_root=baseline,
        repo_root=repo,
        output_dir=tmp_path / "out",
        lane_specs=(spec,),
    )
    manifest = json.loads(path.read_text())
    lane = manifest["lanes"][0]

    assert manifest["phase3_lanes_ready"] is False
    assert lane["representative_entry_duplicate_ids"] == ["duplicate-representative-id"]
    assert "phase3_lane_representative_entry_ids_unique" in manifest["summary"]["failed_kinds"]
    assert "phase3_lane_representative_entries_concrete" not in manifest["summary"]["failed_kinds"]


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


def test_phase3_lane_index_ignores_commented_runner_manifest_ref(tmp_path):
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
    correct_sha = _manifest_sha256(baseline, spec)
    _write_runner(repo, spec, manifest_sha256=correct_sha)
    runner_path = repo / spec.runner_relpath
    declared_manifest = f"artifacts/baselines/observed-v0@0a53352/{spec.manifest_relpath}"
    correct_path_line = (
        f'PHASE3_MANIFEST_PATH="${{PHASE3_MANIFEST_PATH:-$SCRIPT_DIR/{declared_manifest}}}"'
    )
    wrong_path_line = (
        'PHASE3_MANIFEST_PATH="${PHASE3_MANIFEST_PATH:-$SCRIPT_DIR/'
        'artifacts/baselines/observed-v0@0a53352/audit/other_lane/manifest.json}"'
    )
    correct_sha_line = f'PHASE3_MANIFEST_SHA256="${{PHASE3_MANIFEST_SHA256:-{correct_sha}}}"'
    wrong_sha = "0" * 64
    wrong_sha_line = f'PHASE3_MANIFEST_SHA256="${{PHASE3_MANIFEST_SHA256:-{wrong_sha}}}"'
    content = runner_path.read_text()
    content = content.replace(correct_path_line, f"# {correct_path_line}\n{wrong_path_line}", 1)
    content = content.replace(correct_sha_line, f"# {correct_sha_line}\n{wrong_sha_line}", 1)
    runner_path.write_text(content)

    path = build_phase3_lane_index(
        baseline_root=baseline,
        repo_root=repo,
        output_dir=tmp_path / "out",
        lane_specs=(spec,),
    )
    manifest = json.loads(path.read_text())
    lane = manifest["lanes"][0]

    assert manifest["phase3_lanes_ready"] is False
    assert lane["runner_manifest_relpath"] == (
        "artifacts/baselines/observed-v0@0a53352/audit/other_lane/manifest.json"
    )
    assert lane["runner_manifest_sha256"] == wrong_sha
    assert "phase3_lane_runner_manifest_path" in manifest["summary"]["failed_kinds"]
    assert "phase3_lane_runner_manifest_sha256" in manifest["summary"]["failed_kinds"]


@pytest.mark.parametrize(
    "stale_prefix",
    (
        (
            "stale_manifest_ref() {\n"
            "PHASE3_MANIFEST_PATH=\"${PHASE3_MANIFEST_PATH:-$SCRIPT_DIR/"
            "artifacts/baselines/observed-v0@0a53352/audit/runner_manifest_lane/manifest.json}\"\n"
            "}\n"
        ),
        (
            "if [[ -n \"${PHASE3_STALE_REF:-}\" ]]; then\n"
            "PHASE3_MANIFEST_PATH=\"${PHASE3_MANIFEST_PATH:-$SCRIPT_DIR/"
            "artifacts/baselines/observed-v0@0a53352/audit/runner_manifest_lane/manifest.json}\"\n"
            "fi\n"
        ),
    ),
)
def test_phase3_lane_index_ignores_non_top_level_runner_manifest_ref(tmp_path, stale_prefix):
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
    correct_sha = _manifest_sha256(baseline, spec)
    _write_runner(repo, spec, manifest_sha256=correct_sha)
    runner_path = repo / spec.runner_relpath
    declared_manifest = f"artifacts/baselines/observed-v0@0a53352/{spec.manifest_relpath}"
    correct_path_line = (
        f'PHASE3_MANIFEST_PATH="${{PHASE3_MANIFEST_PATH:-$SCRIPT_DIR/{declared_manifest}}}"'
    )
    wrong_path_line = (
        'PHASE3_MANIFEST_PATH="${PHASE3_MANIFEST_PATH:-$SCRIPT_DIR/'
        'artifacts/baselines/observed-v0@0a53352/audit/other_lane/manifest.json}"'
    )
    content = runner_path.read_text()
    content = stale_prefix + content.replace(correct_path_line, wrong_path_line, 1)
    runner_path.write_text(content)

    path = build_phase3_lane_index(
        baseline_root=baseline,
        repo_root=repo,
        output_dir=tmp_path / "out",
        lane_specs=(spec,),
    )
    manifest = json.loads(path.read_text())
    lane = manifest["lanes"][0]

    assert manifest["phase3_lanes_ready"] is False
    assert lane["runner_manifest_relpath"] == (
        "artifacts/baselines/observed-v0@0a53352/audit/other_lane/manifest.json"
    )
    assert lane["runner_manifest_sha256"] == correct_sha
    assert "phase3_lane_runner_manifest_path" in manifest["summary"]["failed_kinds"]
    assert "phase3_lane_runner_manifest_sha256" not in manifest["summary"]["failed_kinds"]


@pytest.mark.parametrize(
    ("block_start", "block_end"),
    (
        ('[[ -n "${PHASE3_STALE_CONTRACT:-}" ]] && {', "}"),
        ('[[ -n "${PHASE3_STALE_CONTRACT:-}" ]] && \\\n{', "}"),
        ("( # stale contract", ") # end stale contract"),
        ("( :", ")"),
        (
            'if [[ -n "${PHASE3_STALE_CONTRACT:-}" ]]; then\n'
            'if [[ -n "${PHASE3_INNER_CONTRACT:-}" ]]; then\n'
            ":\n"
            "fi",
            "fi",
        ),
        ("(\n(\n:\n)", ")"),
        (
            '[[ -n "${PHASE3_STALE_CONTRACT:-}" ]] && {\n'
            '[[ -n "${PHASE3_INNER_CONTRACT:-}" ]] && {\n'
            ":\n"
            "}",
            "}",
        ),
        (
            'unused_contract() {\n'
            '[[ -n "${PHASE3_INNER_CONTRACT:-}" ]] && {\n'
            ":\n"
            "}",
            "}",
        ),
    ),
)
def test_phase3_lane_index_ignores_guarded_or_commented_subshell_runner_manifest_ref(
    tmp_path,
    block_start,
    block_end,
):
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
    correct_sha = _manifest_sha256(baseline, spec)
    _write_runner(repo, spec, manifest_sha256=correct_sha)
    runner_path = repo / spec.runner_relpath
    declared_manifest = f"artifacts/baselines/observed-v0@0a53352/{spec.manifest_relpath}"
    correct_path_line = (
        f'PHASE3_MANIFEST_PATH="${{PHASE3_MANIFEST_PATH:-$SCRIPT_DIR/{declared_manifest}}}"'
    )
    wrong_path_line = (
        'PHASE3_MANIFEST_PATH="${PHASE3_MANIFEST_PATH:-$SCRIPT_DIR/'
        'artifacts/baselines/observed-v0@0a53352/audit/other_lane/manifest.json}"'
    )
    content = runner_path.read_text()
    content = content.replace(
        correct_path_line,
        "\n".join((block_start, correct_path_line, block_end, wrong_path_line)),
        1,
    )
    runner_path.write_text(content)

    path = build_phase3_lane_index(
        baseline_root=baseline,
        repo_root=repo,
        output_dir=tmp_path / "out",
        lane_specs=(spec,),
    )
    manifest = json.loads(path.read_text())
    lane = manifest["lanes"][0]

    assert manifest["phase3_lanes_ready"] is False
    assert lane["runner_manifest_relpath"] == (
        "artifacts/baselines/observed-v0@0a53352/audit/other_lane/manifest.json"
    )
    assert lane["runner_manifest_sha256"] == correct_sha
    assert "phase3_lane_runner_manifest_path" in manifest["summary"]["failed_kinds"]
    assert "phase3_lane_runner_manifest_sha256" not in manifest["summary"]["failed_kinds"]


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
        require_runner_safety_defaults=True,
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
        current_log_root_category="function_call",
        baseline_log_root_category="function_call",
        safety_defaults=_safety_defaults(),
        require_ready_arg=True,
        invoke_gate_args=True,
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
    assert lane["runner_current_log_root_category"] == "function_call"
    assert lane["runner_current_log_root_var"] == "OUTPUT_BASE_DIR"
    assert lane["runner_baseline_log_root_category"] == "function_call"
    assert lane["runner_baseline_log_root_var"] == "BASELINE_FUNCTION_CALL_LOG_ROOT"
    assert lane["runner_log_root_arg_counts"] == {
        "current_log_root": 1,
        "baseline_log_root": 1,
    }
    assert lane["runner_target_filter_counts"] == {
        "target_set": 1,
        "pair_filter": 1,
        "base_path": 1,
        "matrix_script": 1,
        "invalid_mutations": 0,
    }
    assert lane["runner_target_filter_invalid_mutation_count"] == 0
    assert lane["runner_target_filter_invalid_mutations"] == []
    assert lane["runner_pair_filter"] == ["sample_one:B1_B2", "sample_two:B3_B4"]
    expected_runtime_contract = {
        "category": "function_call",
        "matrix_script_relpath": "func_call_run_matrix_all_parallel_multifunc.sh",
        "target_var": "FUNCTION_CALL_TARGET_SET",
        "target_set": "sample_one,sample_two",
        "pair_filter_var": "FUNCTION_CALL_PAIR_FILTER",
        "pair_filter": "sample_one:B1_B2,sample_two:B3_B4",
        "base_path_relpath": "targets/cate1/function_call_test",
        "current_log_root": "function_call=$OUTPUT_BASE_DIR",
        "baseline_log_root": "function_call=$BASELINE_FUNCTION_CALL_LOG_ROOT",
        "validation_runner_dry_run": "0",
    }
    assert lane["runner_target_filter_runtime_status"] == "passed"
    assert lane["runner_target_filter_runtime_invocation_count"] == 1
    assert lane["runner_target_filter_runtime_contract_matches_expected"] is True
    assert lane["runner_target_filter_runtime_failure_kind"] == "none"
    assert lane["runner_target_filter_runtime_returncode"] == 0
    assert lane["runner_target_filter_runtime_expected_contract"] == expected_runtime_contract
    assert lane["runner_target_filter_runtime_observed_contract"] == expected_runtime_contract
    assert lane["runner_target_filter_runtime_contract_diff"] == []
    assert lane["runner_target_filter_runtime_contract_consistent"] is True
    assert lane["runner_gate_smoke_status"] == "passed"
    assert lane["runner_gate_smoke_validator_invocation_count"] == 1


def test_phase3_lane_index_rejects_tampered_runtime_contract_consistency(tmp_path):
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
        require_runner_safety_defaults=True,
    )
    _write_manifest(baseline, spec)
    _write_runner(
        repo,
        spec,
        target_category="function_call",
        current_log_root_category="function_call",
        baseline_log_root_category="function_call",
        safety_defaults=_safety_defaults(),
        require_ready_arg=True,
        invoke_gate_args=True,
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
    lane = manifest["lanes"][0]
    lane["runner_target_filter_runtime_observed_contract"]["target_set"] = "evil_function"
    lane["runner_target_filter_runtime_contract_matches_expected"] = True
    lane["runner_target_filter_runtime_contract_diff"] = []
    lane["runner_target_filter_runtime_contract_consistent"] = True

    with pytest.raises(ValueError, match="derived_failed_kinds"):
        validate_phase3_lane_index(manifest, lane_specs=(spec,))


def test_phase3_lane_index_rejects_target_filter_only_spec_without_gate_policy(tmp_path):
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
        current_log_root_category="function_call",
        baseline_log_root_category="function_call",
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
    lane = manifest["lanes"][0]

    assert manifest["phase3_lanes_ready"] is False
    assert lane["runner_target_filter_runtime_status"] == "passed"
    assert lane["runner_target_filter_runtime_contract_matches_expected"] is True
    assert lane["runner_target_filter_runtime_observed_contract"]["validation_runner_dry_run"] == (
        phase3_lane_index.MISSING_SENTINEL
    )
    assert "phase3_lane_runner_target_filter_gate_policy" in manifest["summary"]["failed_kinds"]
    assert "phase3_lane_runner_target_filter_runtime_contract" not in manifest["summary"]["failed_kinds"]


@pytest.mark.parametrize(
    ("override_line", "expected_var"),
    (
        ('export FUNCTION_CALL_TARGET_SET="evil_function"', "FUNCTION_CALL_TARGET_SET"),
        ('export LOOP_TARGET_SET="evil_loop"', "LOOP_TARGET_SET"),
        ('FUNCTION_CALL_TARGET_SET+="evil_function"', "FUNCTION_CALL_TARGET_SET"),
        ('FUNCTION_CALL_PAIR_FILTER="evil_function:B1_B2"', "FUNCTION_CALL_PAIR_FILTER"),
        ('FUNCTION_CALL_PAIR_FILTER+="evil_function:B1_B2"', "FUNCTION_CALL_PAIR_FILTER"),
        ('LOOP_PAIR_FILTER="evil_loop:B1_B2"', "LOOP_PAIR_FILTER"),
        ('unset FUNCTION_CALL_TARGET_SET', "FUNCTION_CALL_TARGET_SET"),
        ('unset "FUNCTION_CALL_TARGET_SET"', "FUNCTION_CALL_TARGET_SET"),
        ('unset -v LOOP_TARGET_SET', "LOOP_TARGET_SET"),
        ('export -n FUNCTION_CALL_PAIR_FILTER', "FUNCTION_CALL_PAIR_FILTER"),
        ('export -n "FUNCTION_CALL_PAIR_FILTER"', "FUNCTION_CALL_PAIR_FILTER"),
        ('declare FUNCTION_CALL_TARGET_SET="evil_function"', "FUNCTION_CALL_TARGET_SET"),
        ('typeset LOOP_PAIR_FILTER="evil_loop:B1_B2"', "LOOP_PAIR_FILTER"),
        ('readonly BASE_PATH="/tmp/evil"', "BASE_PATH"),
        ('export BASE_PATH="/tmp/evil"', "BASE_PATH"),
        ('printf -v FUNCTION_CALL_TARGET_SET evil_function', "FUNCTION_CALL_TARGET_SET"),
        ('printf -v "FUNCTION_CALL_TARGET_SET" evil_function', "FUNCTION_CALL_TARGET_SET"),
        ('read -r FUNCTION_CALL_TARGET_SET <<< evil_function', "FUNCTION_CALL_TARGET_SET"),
        ('read -p "prompt" FUNCTION_CALL_TARGET_SET <<< evil_function', "FUNCTION_CALL_TARGET_SET"),
        ('IFS= read -r FUNCTION_CALL_PAIR_FILTER <<< evil_function:B1_B2', "FUNCTION_CALL_PAIR_FILTER"),
        ('mapfile -t LOOP_TARGET_SET <<< evil_loop', "LOOP_TARGET_SET"),
        ('readarray -t LOOP_PAIR_FILTER <<< evil_loop:B1_B2', "LOOP_PAIR_FILTER"),
        ('eval "FUNCTION_CALL_TARGET_SET=evil_function"', "FUNCTION_CALL_TARGET_SET"),
        ('eval FUNCTION_CALL_PAIR_FILTER=evil_function:B1_B2', "FUNCTION_CALL_PAIR_FILTER"),
        ('builtin printf -v FUNCTION_CALL_TARGET_SET evil_function', "FUNCTION_CALL_TARGET_SET"),
        ('command unset FUNCTION_CALL_TARGET_SET', "FUNCTION_CALL_TARGET_SET"),
        ('builtin eval FUNCTION_CALL_PAIR_FILTER=evil_function:B1_B2', "FUNCTION_CALL_PAIR_FILTER"),
        ('target=FUNCTION_CALL_TARGET_SET; printf -v "$target" evil_function', "FUNCTION_CALL_TARGET_SET"),
        ('target=FUNCTION_CALL_TARGET_SET; printf -v ${target} evil_function', "FUNCTION_CALL_TARGET_SET"),
        ('target=FUNCTION_CALL_TARGET_SET; unset "$target"', "FUNCTION_CALL_TARGET_SET"),
        ('target=FUNCTION_CALL_PAIR_FILTER; builtin eval "$target=evil_function:B1_B2"', "FUNCTION_CALL_PAIR_FILTER"),
        ('true && export LOOP_TARGET_SET="evil_loop"', "LOOP_TARGET_SET"),
        ('false || LOOP_PAIR_FILTER="evil_loop:B1_B2"', "LOOP_PAIR_FILTER"),
        ('unused_contract() { :; }; export FUNCTION_CALL_TARGET_SET="evil_function"', "FUNCTION_CALL_TARGET_SET"),
    ),
)
def test_phase3_lane_index_rejects_noncanonical_runner_target_filter_assignment(
    tmp_path,
    override_line,
    expected_var,
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
        require_runner_safety_defaults=True,
    )
    _write_manifest(baseline, spec)
    _write_runner(
        repo,
        spec,
        target_category="function_call",
        current_log_root_category="function_call",
        baseline_log_root_category="function_call",
        safety_defaults=_safety_defaults(),
        require_ready_arg=True,
        invoke_gate_args=True,
        target_functions=("runner_target_lane_function",),
        pair_filter=("runner_target_lane_function:B1_B2",),
    )
    runner_path = repo / spec.runner_relpath
    lines = runner_path.read_text(encoding="utf-8").splitlines()
    matrix_index = next(
        index
        for index, line in enumerate(lines)
        if line.startswith('bash "$SCRIPT_DIR/')
    )
    lines.insert(matrix_index, override_line)
    runner_path.write_text("\n".join(lines) + "\n", encoding="utf-8")

    path = build_phase3_lane_index(
        baseline_root=baseline,
        repo_root=repo,
        output_dir=tmp_path / "out",
        lane_specs=(spec,),
    )
    manifest = json.loads(path.read_text())
    lane = manifest["lanes"][0]

    assert manifest["phase3_lanes_ready"] is False
    assert lane["runner_target_filter_counts"]["invalid_mutations"] == 1
    assert lane["runner_target_filter_invalid_mutation_count"] == 1
    assert lane["runner_target_filter_invalid_mutations"][0]["vars"] == [expected_var]
    assert "phase3_lane_runner_target_filter_immutable" in manifest["summary"]["failed_kinds"]
    assert "phase3_lane_runner_target_set" not in manifest["summary"]["failed_kinds"]


@pytest.mark.parametrize(
    ("override_line", "diff_key"),
    (
        (
            'target=FUNCTION_CALL_; target+=TARGET_SET; printf -v "$target" evil_function',
            "target_set",
        ),
        (
            'target=FUNCTION_CALL_TARGET_SET; export "$target=evil_function"',
            "target_set",
        ),
        (
            'target=FUNCTION_CALL_TARGET_SET; declare "$target=evil_function"',
            "target_set",
        ),
        (
            'target=FUNCTION_CALL_TARGET_SET; typeset "$target=evil_function"',
            "target_set",
        ),
        (
            'target=FUNCTION_CALL_PAIR_FILTER; export "$target=evil_function:B1_B2"',
            "pair_filter",
        ),
        (
            'target=FUNCTION_CALL_PAIR_FILTER; declare "$target=evil_function:B1_B2"',
            "pair_filter",
        ),
        (
            'target=FUNCTION_CALL_PAIR_FILTER; typeset "$target=evil_function:B1_B2"',
            "pair_filter",
        ),
    ),
)
def test_phase3_lane_index_runtime_contract_rejects_target_filter_bypass(
    tmp_path,
    override_line,
    diff_key,
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
    _write_manifest(baseline, spec)
    _write_runner(
        repo,
        spec,
        target_category="function_call",
        current_log_root_category="function_call",
        baseline_log_root_category="function_call",
        target_functions=("runner_target_lane_function",),
        pair_filter=("runner_target_lane_function:B1_B2",),
    )
    runner_path = repo / spec.runner_relpath
    lines = runner_path.read_text(encoding="utf-8").splitlines()
    matrix_index = next(
        index
        for index, line in enumerate(lines)
        if line.startswith('bash "$SCRIPT_DIR/')
    )
    lines.insert(matrix_index, override_line)
    runner_path.write_text("\n".join(lines) + "\n", encoding="utf-8")

    path = build_phase3_lane_index(
        baseline_root=baseline,
        repo_root=repo,
        output_dir=tmp_path / "out",
        lane_specs=(spec,),
    )
    manifest = json.loads(path.read_text())
    lane = manifest["lanes"][0]

    assert manifest["phase3_lanes_ready"] is False
    assert lane["runner_target_filter_invalid_mutation_count"] == 0
    assert lane["runner_target_filter_runtime_status"] == "failed"
    assert lane["runner_target_filter_runtime_failure_kind"] == "contract_mismatch"
    assert lane["runner_target_filter_runtime_invocation_count"] == 1
    assert diff_key in {
        diff["key"]
        for diff in lane["runner_target_filter_runtime_contract_diff"]
    }
    assert "phase3_lane_runner_target_filter_runtime_contract" in manifest["summary"]["failed_kinds"]
    assert "phase3_lane_runner_target_filter_immutable" not in manifest["summary"]["failed_kinds"]


def test_phase3_lane_index_runtime_contract_uses_non_dry_run_branch(tmp_path):
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
        require_runner_safety_defaults=True,
    )
    _write_manifest(baseline, spec)
    _write_runner(
        repo,
        spec,
        target_category="function_call",
        current_log_root_category="function_call",
        baseline_log_root_category="function_call",
        safety_defaults=_safety_defaults(),
        require_ready_arg=True,
        invoke_gate_args=True,
        target_functions=("runner_target_lane_function",),
        pair_filter=("runner_target_lane_function:B1_B2",),
    )
    runner_path = repo / spec.runner_relpath
    lines = runner_path.read_text(encoding="utf-8").splitlines()
    matrix_index = next(
        index
        for index, line in enumerate(lines)
        if line.startswith('bash "$SCRIPT_DIR/')
    )
    lines[matrix_index:matrix_index] = [
        'if [[ "${VALIDATION_RUNNER_DRY_RUN:-0}" == "0" ]]; then',
        "    FUNCTION_CALL_TARGET_SET=evil_function",
        "fi",
    ]
    runner_path.write_text("\n".join(lines) + "\n", encoding="utf-8")

    path = build_phase3_lane_index(
        baseline_root=baseline,
        repo_root=repo,
        output_dir=tmp_path / "out",
        lane_specs=(spec,),
    )
    manifest = json.loads(path.read_text())
    lane = manifest["lanes"][0]

    assert manifest["phase3_lanes_ready"] is False
    assert lane["runner_target_filter_invalid_mutation_count"] == 0
    assert lane["runner_target_filter_runtime_status"] == "failed"
    assert lane["runner_target_filter_runtime_failure_kind"] == "contract_mismatch"
    assert lane["runner_target_filter_runtime_observed_contract"]["target_set"] == "evil_function"
    assert lane["runner_target_filter_runtime_observed_contract"]["validation_runner_dry_run"] == "0"
    assert lane["runner_gate_smoke_status"] == "passed"
    assert "phase3_lane_runner_target_filter_runtime_contract" in manifest["summary"]["failed_kinds"]
    assert "phase3_lane_runner_gate_smoke" not in manifest["summary"]["failed_kinds"]


@pytest.mark.parametrize(
    ("matrix_mutation", "expected_invocation_count"),
    (
        ("remove", 0),
        ("duplicate", 2),
    ),
)
def test_phase3_lane_index_runtime_contract_requires_one_matrix_invocation(
    tmp_path,
    matrix_mutation,
    expected_invocation_count,
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
        require_runner_safety_defaults=True,
    )
    _write_manifest(baseline, spec)
    _write_runner(
        repo,
        spec,
        target_category="function_call",
        current_log_root_category="function_call",
        baseline_log_root_category="function_call",
        safety_defaults=_safety_defaults(),
        require_ready_arg=True,
        invoke_gate_args=True,
        target_functions=("runner_target_lane_function",),
        pair_filter=("runner_target_lane_function:B1_B2",),
    )
    runner_path = repo / spec.runner_relpath
    lines = runner_path.read_text(encoding="utf-8").splitlines()
    matrix_index = next(
        index
        for index, line in enumerate(lines)
        if line.startswith('bash "$SCRIPT_DIR/')
    )
    matrix_line = lines[matrix_index]
    if matrix_mutation == "remove":
        del lines[matrix_index]
    else:
        lines.insert(matrix_index + 1, matrix_line)
    runner_path.write_text("\n".join(lines) + "\n", encoding="utf-8")

    path = build_phase3_lane_index(
        baseline_root=baseline,
        repo_root=repo,
        output_dir=tmp_path / "out",
        lane_specs=(spec,),
    )
    manifest = json.loads(path.read_text())
    lane = manifest["lanes"][0]

    assert manifest["phase3_lanes_ready"] is False
    assert lane["runner_target_filter_runtime_status"] == "failed"
    assert lane["runner_target_filter_runtime_failure_kind"] == "matrix_invocation_count"
    assert lane["runner_target_filter_runtime_invocation_count"] == expected_invocation_count
    assert len(lane["runner_target_filter_runtime_observed_invocations"]) == (
        expected_invocation_count
    )
    assert "phase3_lane_runner_target_filter_runtime_contract" in manifest["summary"]["failed_kinds"]


@pytest.mark.parametrize(
    "override_line",
    (
        'eval "FUNCTION_CALL_TARGET_SET=evil_function"',
        "builtin printf -v FUNCTION_CALL_TARGET_SET evil_function",
        "command unset FUNCTION_CALL_TARGET_SET",
        "builtin eval FUNCTION_CALL_PAIR_FILTER=evil_function:B1_B2",
        'target=FUNCTION_CALL_TARGET_SET; printf -v "$target" evil_function',
        "target=FUNCTION_CALL_TARGET_SET; printf -v ${target} evil_function",
        'target=FUNCTION_CALL_TARGET_SET; unset "$target"',
        'target=FUNCTION_CALL_PAIR_FILTER; builtin eval "$target=evil_function:B1_B2"',
    ),
)
def test_phase3_lane_index_runtime_contract_rejects_previous_target_filter_bypasses(
    tmp_path,
    override_line,
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
    _write_manifest(baseline, spec)
    _write_runner(
        repo,
        spec,
        target_category="function_call",
        current_log_root_category="function_call",
        baseline_log_root_category="function_call",
        target_functions=("runner_target_lane_function",),
        pair_filter=("runner_target_lane_function:B1_B2",),
    )
    runner_path = repo / spec.runner_relpath
    lines = runner_path.read_text(encoding="utf-8").splitlines()
    matrix_index = next(
        index
        for index, line in enumerate(lines)
        if line.startswith('bash "$SCRIPT_DIR/')
    )
    lines.insert(matrix_index, override_line)
    runner_path.write_text("\n".join(lines) + "\n", encoding="utf-8")

    path = build_phase3_lane_index(
        baseline_root=baseline,
        repo_root=repo,
        output_dir=tmp_path / "out",
        lane_specs=(spec,),
    )
    manifest = json.loads(path.read_text())
    lane = manifest["lanes"][0]

    assert manifest["phase3_lanes_ready"] is False
    assert lane["runner_target_filter_runtime_status"] == "failed"
    assert lane["runner_target_filter_runtime_failure_kind"] == "contract_mismatch"
    assert lane["runner_target_filter_runtime_invocation_count"] == 1
    assert "phase3_lane_runner_target_filter_runtime_contract" in manifest["summary"]["failed_kinds"]


def test_phase3_lane_index_runtime_contract_accepts_target_filter_diagnostics(tmp_path):
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
        require_runner_safety_defaults=True,
    )
    _write_manifest(baseline, spec)
    _write_runner(
        repo,
        spec,
        target_category="function_call",
        current_log_root_category="function_call",
        baseline_log_root_category="function_call",
        safety_defaults=_safety_defaults(),
        require_ready_arg=True,
        invoke_gate_args=True,
        target_functions=("runner_target_lane_function",),
        pair_filter=("runner_target_lane_function:B1_B2",),
    )
    runner_path = repo / spec.runner_relpath
    lines = runner_path.read_text(encoding="utf-8").splitlines()
    matrix_index = next(
        index
        for index, line in enumerate(lines)
        if line.startswith('bash "$SCRIPT_DIR/')
    )
    lines[matrix_index:matrix_index] = [
        'echo "FUNCTION_CALL_TARGET_SET=evil_function"',
        "printf '%s' FUNCTION_CALL_PAIR_FILTER=evil_function:B1_B2",
        "command -v unset >/dev/null",
    ]
    runner_path.write_text("\n".join(lines) + "\n", encoding="utf-8")

    path = build_phase3_lane_index(
        baseline_root=baseline,
        repo_root=repo,
        output_dir=tmp_path / "out",
        lane_specs=(spec,),
    )
    manifest = json.loads(path.read_text())
    lane = manifest["lanes"][0]

    assert manifest["phase3_lanes_ready"] is True
    assert lane["runner_target_filter_invalid_mutation_count"] == 0
    assert lane["runner_target_filter_runtime_status"] == "passed"
    assert lane["runner_target_filter_runtime_contract_matches_expected"] is True
    assert lane["runner_gate_smoke_status"] == "passed"


@pytest.mark.parametrize(
    ("code", "expected_vars"),
    (
        ('FUNCTION_CALL_TARGET_SET+="evil_function"', ["FUNCTION_CALL_TARGET_SET"]),
        ('unset FUNCTION_CALL_TARGET_SET', ["FUNCTION_CALL_TARGET_SET"]),
        ('unset "FUNCTION_CALL_TARGET_SET"', ["FUNCTION_CALL_TARGET_SET"]),
        ('unset -v LOOP_TARGET_SET', ["LOOP_TARGET_SET"]),
        ('export -n FUNCTION_CALL_PAIR_FILTER', ["FUNCTION_CALL_PAIR_FILTER"]),
        ('export -n "FUNCTION_CALL_PAIR_FILTER"', ["FUNCTION_CALL_PAIR_FILTER"]),
        ('declare -x FUNCTION_CALL_TARGET_SET="evil_function"', ["FUNCTION_CALL_TARGET_SET"]),
        ('typeset LOOP_PAIR_FILTER="evil_loop:B1_B2"', ["LOOP_PAIR_FILTER"]),
        ('readonly BASE_PATH="/tmp/evil"', ["BASE_PATH"]),
        ('printf -v FUNCTION_CALL_TARGET_SET evil_function', ["FUNCTION_CALL_TARGET_SET"]),
        ('printf -v "FUNCTION_CALL_TARGET_SET" evil_function', ["FUNCTION_CALL_TARGET_SET"]),
        ('printf -vFUNCTION_CALL_TARGET_SET evil_function', ["FUNCTION_CALL_TARGET_SET"]),
        ('read -r FUNCTION_CALL_TARGET_SET <<< evil_function', ["FUNCTION_CALL_TARGET_SET"]),
        ('read -p "prompt" FUNCTION_CALL_TARGET_SET <<< evil_function', ["FUNCTION_CALL_TARGET_SET"]),
        ('IFS= read -r FUNCTION_CALL_PAIR_FILTER <<< evil_function:B1_B2', ["FUNCTION_CALL_PAIR_FILTER"]),
        ('read -a LOOP_TARGET_SET <<< evil_loop', ["LOOP_TARGET_SET"]),
        ('mapfile -t LOOP_TARGET_SET <<< evil_loop', ["LOOP_TARGET_SET"]),
        ('readarray -t LOOP_PAIR_FILTER <<< evil_loop:B1_B2', ["LOOP_PAIR_FILTER"]),
        ('env FUNCTION_CALL_TARGET_SET=evil_function bash run.sh', ["FUNCTION_CALL_TARGET_SET"]),
        ('eval "FUNCTION_CALL_TARGET_SET=evil_function"', ["FUNCTION_CALL_TARGET_SET"]),
        ('eval FUNCTION_CALL_PAIR_FILTER=evil_function:B1_B2', ["FUNCTION_CALL_PAIR_FILTER"]),
        ('builtin printf -v FUNCTION_CALL_TARGET_SET evil_function', ["FUNCTION_CALL_TARGET_SET"]),
        ('command unset FUNCTION_CALL_TARGET_SET', ["FUNCTION_CALL_TARGET_SET"]),
        ('builtin eval FUNCTION_CALL_PAIR_FILTER=evil_function:B1_B2', ["FUNCTION_CALL_PAIR_FILTER"]),
        ('command -v unset FUNCTION_CALL_TARGET_SET', []),
        ('command -V printf FUNCTION_CALL_TARGET_SET', []),
        ('target=FUNCTION_CALL_TARGET_SET; printf -v "$target" evil_function', ["FUNCTION_CALL_TARGET_SET"]),
        ('target=FUNCTION_CALL_TARGET_SET; printf -v ${target} evil_function', ["FUNCTION_CALL_TARGET_SET"]),
        ('target=FUNCTION_CALL_TARGET_SET; unset "$target"', ["FUNCTION_CALL_TARGET_SET"]),
        ('target=FUNCTION_CALL_PAIR_FILTER; builtin eval "$target=evil_function:B1_B2"', ["FUNCTION_CALL_PAIR_FILTER"]),
        ('target=foo; printf -v "$target" evil_function', []),
        ('printf -v "$target" evil_function', [phase3_lane_index.DYNAMIC_TARGET_FILTER_DESTINATION]),
        ('printf -v ${target} evil_function', [phase3_lane_index.DYNAMIC_TARGET_FILTER_DESTINATION]),
        ('target=$maybe; read "$target" <<< evil_function', [phase3_lane_index.DYNAMIC_TARGET_FILTER_DESTINATION]),
        ('target=${maybe}; read "$target" <<< evil_function', [phase3_lane_index.DYNAMIC_TARGET_FILTER_DESTINATION]),
        ('echo "FUNCTION_CALL_TARGET_SET+=evil_function"', []),
        ("echo 'unset FUNCTION_CALL_TARGET_SET'", []),
        ('echo "${FUNCTION_CALL_TARGET_SET:-evil_function}"', []),
        ('echo FUNCTION_CALL_TARGET_SET=runner_target_lane_function', []),
        ('echo "FUNCTION_CALL_TARGET_SET"', []),
        ("printf '%s' FUNCTION_CALL_TARGET_SET=runner_target_lane_function", []),
        ("printf '%s' 'FUNCTION_CALL_TARGET_SET=runner_target_lane_function'", []),
        ('printf "%s" FUNCTION_CALL_PAIR_FILTER=runner_target_lane_function:B1_B2', []),
    ),
)
def test_phase3_lane_index_runner_target_filter_mutation_scanner(code, expected_vars):
    assert phase3_lane_index._runner_target_filter_mutated_vars(code) == expected_vars


def test_phase3_lane_index_rejects_top_level_target_override_after_quoted_function_brace(tmp_path):
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
        current_log_root_category="function_call",
        baseline_log_root_category="function_call",
        target_functions=("runner_target_lane_function",),
        pair_filter=("runner_target_lane_function:B1_B2",),
    )
    runner_path = repo / spec.runner_relpath
    with runner_path.open("a", encoding="utf-8") as handle:
        handle.write(
            "\n".join(
                (
                    "unused_contract() {",
                    '    echo "{"',
                    "}",
                    'export FUNCTION_CALL_TARGET_SET="${FUNCTION_CALL_TARGET_SET:-evil_function}"',
                    'echo "}"',
                )
            )
            + "\n"
        )

    path = build_phase3_lane_index(
        baseline_root=baseline,
        repo_root=repo,
        output_dir=tmp_path / "out",
        lane_specs=(spec,),
    )
    manifest = json.loads(path.read_text())
    lane = manifest["lanes"][0]

    assert manifest["phase3_lanes_ready"] is False
    assert lane["runner_target_filter_counts"]["target_set"] == 2
    assert "phase3_lane_runner_target_filter_unique" in manifest["summary"]["failed_kinds"]
    assert "phase3_lane_runner_target_set" not in manifest["summary"]["failed_kinds"]


def test_phase3_lane_index_rejects_commented_runner_target_filter(tmp_path):
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
        current_log_root_category="function_call",
        baseline_log_root_category="function_call",
        target_functions=("runner_target_lane_function",),
        pair_filter=("runner_target_lane_function:B1_B2",),
    )
    runner_path = repo / spec.runner_relpath
    runner_path.write_text(
        "\n".join(
            "# " + line
            if line.startswith("export FUNCTION_CALL_TARGET_SET")
            or line.startswith("export FUNCTION_CALL_PAIR_FILTER")
            or line.startswith("export BASE_PATH")
            or line.startswith('bash "$SCRIPT_DIR/')
            or line.strip().startswith("--current-log-root")
            or line.strip().startswith("--baseline-log-root")
            else line
            for line in runner_path.read_text().splitlines()
        )
        + "\n"
    )

    path = build_phase3_lane_index(
        baseline_root=baseline,
        repo_root=repo,
        output_dir=tmp_path / "out",
        lane_specs=(spec,),
    )
    manifest = json.loads(path.read_text())
    lane = manifest["lanes"][0]

    assert manifest["phase3_lanes_ready"] is False
    assert lane["runner_target_functions"] == []
    assert lane["runner_pair_filter"] == []
    assert lane["runner_log_root_arg_counts"] == {
        "current_log_root": 0,
        "baseline_log_root": 0,
    }
    assert "phase3_lane_runner_target_category" in manifest["summary"]["failed_kinds"]
    assert "phase3_lane_runner_log_root_args_unique" in manifest["summary"]["failed_kinds"]


def test_phase3_lane_index_rejects_function_scoped_runner_target_filter(tmp_path):
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
        current_log_root_category="function_call",
        baseline_log_root_category="function_call",
        target_functions=("runner_target_lane_function",),
        pair_filter=("runner_target_lane_function:B1_B2",),
    )
    runner_path = repo / spec.runner_relpath
    target_lines = []
    remaining_lines = []
    for line in runner_path.read_text().splitlines():
        if (
            line.startswith("export FUNCTION_CALL_TARGET_SET")
            or line.startswith("export FUNCTION_CALL_PAIR_FILTER")
            or line.startswith("export BASE_PATH")
            or line.startswith('bash "$SCRIPT_DIR/')
            or line.strip().startswith("--current-log-root")
            or line.strip().startswith("--baseline-log-root")
        ):
            target_lines.append(line)
        else:
            remaining_lines.append(line)
    insertion_index = remaining_lines.index("set -euo pipefail") + 1
    function_block = ["stale_target_filter() {", *target_lines, "}"]
    runner_path.write_text(
        "\n".join(remaining_lines[:insertion_index] + function_block + remaining_lines[insertion_index:])
        + "\n"
    )

    path = build_phase3_lane_index(
        baseline_root=baseline,
        repo_root=repo,
        output_dir=tmp_path / "out",
        lane_specs=(spec,),
    )
    manifest = json.loads(path.read_text())
    lane = manifest["lanes"][0]

    assert manifest["phase3_lanes_ready"] is False
    assert lane["runner_target_functions"] == []
    assert lane["runner_pair_filter"] == []
    assert lane["runner_log_root_arg_counts"] == {
        "current_log_root": 0,
        "baseline_log_root": 0,
    }
    assert "phase3_lane_runner_target_category" in manifest["summary"]["failed_kinds"]
    assert "phase3_lane_runner_log_root_args_unique" in manifest["summary"]["failed_kinds"]


def test_phase3_lane_index_rejects_subshell_scoped_runner_target_filter(tmp_path):
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
        current_log_root_category="function_call",
        baseline_log_root_category="function_call",
        target_functions=("runner_target_lane_function",),
        pair_filter=("runner_target_lane_function:B1_B2",),
    )
    runner_path = repo / spec.runner_relpath
    target_lines = []
    remaining_lines = []
    for line in runner_path.read_text().splitlines():
        if (
            line.startswith("export FUNCTION_CALL_TARGET_SET")
            or line.startswith("export FUNCTION_CALL_PAIR_FILTER")
            or line.startswith("export BASE_PATH")
            or line.startswith('bash "$SCRIPT_DIR/')
            or line.strip().startswith("--current-log-root")
            or line.strip().startswith("--baseline-log-root")
        ):
            target_lines.append(line)
        else:
            remaining_lines.append(line)
    insertion_index = remaining_lines.index("set -euo pipefail") + 1
    subshell_block = ["(", *target_lines, ")"]
    runner_path.write_text(
        "\n".join(remaining_lines[:insertion_index] + subshell_block + remaining_lines[insertion_index:])
        + "\n"
    )

    path = build_phase3_lane_index(
        baseline_root=baseline,
        repo_root=repo,
        output_dir=tmp_path / "out",
        lane_specs=(spec,),
    )
    manifest = json.loads(path.read_text())
    lane = manifest["lanes"][0]

    assert manifest["phase3_lanes_ready"] is False
    assert lane["runner_target_functions"] == []
    assert lane["runner_pair_filter"] == []
    assert lane["runner_log_root_arg_counts"] == {
        "current_log_root": 0,
        "baseline_log_root": 0,
    }
    assert "phase3_lane_runner_target_category" in manifest["summary"]["failed_kinds"]
    assert "phase3_lane_runner_log_root_args_unique" in manifest["summary"]["failed_kinds"]


@pytest.mark.parametrize(
    ("block_start", "block_end"),
    (
        ('[[ -n "${PHASE3_STALE_CONTRACT:-}" ]] && {', "}"),
        ('[[ -n "${PHASE3_STALE_CONTRACT:-}" ]] && \\\n{', "}"),
        ("( # stale contract", ") # end stale contract"),
        ("( :", ")"),
        (
            'if [[ -n "${PHASE3_STALE_CONTRACT:-}" ]]; then\n'
            'if [[ -n "${PHASE3_INNER_CONTRACT:-}" ]]; then\n'
            ":\n"
            "fi",
            "fi",
        ),
        ("(\n(\n:\n)", ")"),
        (
            '[[ -n "${PHASE3_STALE_CONTRACT:-}" ]] && {\n'
            '[[ -n "${PHASE3_INNER_CONTRACT:-}" ]] && {\n'
            ":\n"
            "}",
            "}",
        ),
        (
            'unused_contract() {\n'
            '[[ -n "${PHASE3_INNER_CONTRACT:-}" ]] && {\n'
            ":\n"
            "}",
            "}",
        ),
    ),
)
def test_phase3_lane_index_rejects_guarded_or_commented_subshell_runner_target_filter(
    tmp_path,
    block_start,
    block_end,
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
    _write_manifest(baseline, spec)
    _write_runner(
        repo,
        spec,
        target_category="function_call",
        current_log_root_category="function_call",
        baseline_log_root_category="function_call",
        target_functions=("runner_target_lane_function",),
        pair_filter=("runner_target_lane_function:B1_B2",),
    )
    runner_path = repo / spec.runner_relpath
    target_lines = []
    remaining_lines = []
    for line in runner_path.read_text().splitlines():
        if (
            line.startswith("export FUNCTION_CALL_TARGET_SET")
            or line.startswith("export FUNCTION_CALL_PAIR_FILTER")
            or line.startswith("export BASE_PATH")
            or line.startswith('bash "$SCRIPT_DIR/')
            or line.strip().startswith("--current-log-root")
            or line.strip().startswith("--baseline-log-root")
        ):
            target_lines.append(line)
        else:
            remaining_lines.append(line)
    insertion_index = remaining_lines.index("set -euo pipefail") + 1
    guarded_block = [block_start, *target_lines, block_end]
    runner_path.write_text(
        "\n".join(remaining_lines[:insertion_index] + guarded_block + remaining_lines[insertion_index:])
        + "\n"
    )

    path = build_phase3_lane_index(
        baseline_root=baseline,
        repo_root=repo,
        output_dir=tmp_path / "out",
        lane_specs=(spec,),
    )
    manifest = json.loads(path.read_text())
    lane = manifest["lanes"][0]

    assert manifest["phase3_lanes_ready"] is False
    assert lane["runner_target_functions"] == []
    assert lane["runner_pair_filter"] == []
    assert lane["runner_log_root_arg_counts"] == {
        "current_log_root": 0,
        "baseline_log_root": 0,
    }
    assert "phase3_lane_runner_target_category" in manifest["summary"]["failed_kinds"]
    assert "phase3_lane_runner_log_root_args_unique" in manifest["summary"]["failed_kinds"]


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
        current_log_root_category="function_call",
        baseline_log_root_category="function_call",
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
        current_log_root_category="function_call",
        baseline_log_root_category="function_call",
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


def test_phase3_lane_index_rejects_incomplete_manifest_target_filter(tmp_path):
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
                "id": "entry-without-category",
                "function": "sample_one",
                "binary_pair": "B1_B2",
            },
        ],
    )
    _write_runner(repo, spec)

    path = build_phase3_lane_index(
        baseline_root=baseline,
        repo_root=repo,
        output_dir=tmp_path / "out",
        lane_specs=(spec,),
    )
    manifest = json.loads(path.read_text())
    lane = manifest["lanes"][0]

    assert manifest["phase3_lanes_ready"] is False
    assert lane["representative_entries"] == [
        {
            "index": 0,
            "id": "entry-without-category",
            "function": "sample_one",
            "binary_pair": "B1_B2",
        }
    ]
    assert "phase3_lane_representative_entries_concrete" not in manifest["summary"]["failed_kinds"]
    assert "phase3_lane_manifest_target_filter_complete" in manifest["summary"]["failed_kinds"]


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
    assert lane["runner_shebang"] == "#!/usr/bin/env bash"
    assert lane["runner_strict_mode_present"] is True
    assert lane["runner_safety_defaults"] == _safety_defaults()
    assert lane["runner_safety_duplicate_vars"] == []
    assert lane["runner_require_ready_arg_present"] is True
    assert lane["runner_gate_args_invoked"] is True
    assert lane["runner_gate_validator_module"] == "scripts.function_tracer_pcode.validation.phase3_runner_safety_lane"
    assert lane["runner_gate_validator_invocation_count"] == 1
    assert lane["runner_required_gate_args"] == {
        "--gate-stage": "post-fix",
        "--baseline-raw-dir": "$BASELINE_RAW_DIR",
        "--output-dir": "$PHASE3_GATE_OUTPUT_DIR",
        "--phase3-manifest": "$PHASE3_MANIFEST_PATH",
        "--phase3-manifest-sha256": "$PHASE3_MANIFEST_SHA256",
    }
    assert lane["runner_required_gate_arg_counts"] == {
        "--gate-stage": 1,
        "--baseline-raw-dir": 1,
        "--output-dir": 1,
        "--phase3-manifest": 1,
        "--phase3-manifest-sha256": 1,
    }
    assert lane["runner_required_gate_args_missing"] == []
    assert lane["runner_required_gate_args_duplicate"] == []
    assert lane["runner_required_gate_args_value_mismatch"] == []
    assert lane["runner_gate_args_unknown_args"] == []
    assert lane["runner_gate_args_invalid_optional_args"] == []
    assert lane["runner_gate_args_assignment_count"] == 1
    assert lane["runner_gate_args_invalid_mutation_count"] == 0
    assert lane["runner_gate_args_invalid_mutations"] == []
    assert lane["runner_gate_smoke_status"] == "passed"
    assert lane["runner_gate_smoke_validator_invocation_count"] == 1
    assert lane["runner_gate_smoke_argv_matches_expected"] is True
    assert lane["runner_gate_smoke_error"] == "<missing>"
    assert lane["runner_gate_smoke_failure_kind"] == "none"
    assert lane["runner_gate_smoke_returncode"] == 0
    assert lane["runner_gate_smoke_expected_argv"] == _expected_runner_safety_gate_smoke_argv()
    assert lane["runner_gate_smoke_observed_argv"] == lane["runner_gate_smoke_expected_argv"]
    assert lane["runner_gate_smoke_observed_invocations"] == [
        lane["runner_gate_smoke_expected_argv"]
    ]
    assert lane["runner_gate_smoke_argv_diff"] == []


def test_phase3_lane_index_rejects_function_scoped_runner_safety_defaults(tmp_path):
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
    moved_defaults = []
    remaining_lines = []
    for line in runner_path.read_text().splitlines():
        if line.startswith("export VALIDATION_"):
            moved_defaults.append(line)
        else:
            remaining_lines.append(line)
    insertion_index = remaining_lines.index("set -euo pipefail") + 1
    function_block = ["stale_safety_defaults() {", *moved_defaults, "}"]
    runner_path.write_text(
        "\n".join(remaining_lines[:insertion_index] + function_block + remaining_lines[insertion_index:])
        + "\n"
    )

    path = build_phase3_lane_index(
        baseline_root=baseline,
        repo_root=repo,
        output_dir=tmp_path / "out",
        lane_specs=(spec,),
    )
    manifest = json.loads(path.read_text())
    lane = manifest["lanes"][0]

    assert manifest["phase3_lanes_ready"] is False
    assert lane["runner_safety_defaults"] == {"PHASE3_REQUIRE_READY": "1"}
    assert lane["runner_gate_smoke_status"] == "passed"
    assert "phase3_lane_runner_safety_defaults" in manifest["summary"]["failed_kinds"]


def test_phase3_lane_index_rejects_subshell_scoped_runner_safety_defaults(tmp_path):
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
    moved_defaults = []
    remaining_lines = []
    for line in runner_path.read_text().splitlines():
        if line.startswith("export VALIDATION_"):
            moved_defaults.append(line)
        else:
            remaining_lines.append(line)
    insertion_index = remaining_lines.index("set -euo pipefail") + 1
    subshell_block = ["(", *moved_defaults, ")"]
    runner_path.write_text(
        "\n".join(remaining_lines[:insertion_index] + subshell_block + remaining_lines[insertion_index:])
        + "\n"
    )

    path = build_phase3_lane_index(
        baseline_root=baseline,
        repo_root=repo,
        output_dir=tmp_path / "out",
        lane_specs=(spec,),
    )
    manifest = json.loads(path.read_text())
    lane = manifest["lanes"][0]

    assert manifest["phase3_lanes_ready"] is False
    assert lane["runner_safety_defaults"] == {"PHASE3_REQUIRE_READY": "1"}
    assert lane["runner_gate_smoke_status"] == "passed"
    assert "phase3_lane_runner_safety_defaults" in manifest["summary"]["failed_kinds"]


@pytest.mark.parametrize(
    ("block_start", "block_end"),
    (
        ('[[ -n "${PHASE3_STALE_CONTRACT:-}" ]] && {', "}"),
        ('[[ -n "${PHASE3_STALE_CONTRACT:-}" ]] && \\\n{', "}"),
        ("( # stale contract", ") # end stale contract"),
        ("( :", ")"),
        (
            'if [[ -n "${PHASE3_STALE_CONTRACT:-}" ]]; then\n'
            'if [[ -n "${PHASE3_INNER_CONTRACT:-}" ]]; then\n'
            ":\n"
            "fi",
            "fi",
        ),
        ("(\n(\n:\n)", ")"),
        (
            '[[ -n "${PHASE3_STALE_CONTRACT:-}" ]] && {\n'
            '[[ -n "${PHASE3_INNER_CONTRACT:-}" ]] && {\n'
            ":\n"
            "}",
            "}",
        ),
        (
            'unused_contract() {\n'
            '[[ -n "${PHASE3_INNER_CONTRACT:-}" ]] && {\n'
            ":\n"
            "}",
            "}",
        ),
    ),
)
def test_phase3_lane_index_rejects_guarded_or_commented_subshell_runner_safety_defaults(
    tmp_path,
    block_start,
    block_end,
):
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
    moved_defaults = []
    remaining_lines = []
    for line in runner_path.read_text().splitlines():
        if line.startswith("export VALIDATION_"):
            moved_defaults.append(line)
        else:
            remaining_lines.append(line)
    insertion_index = remaining_lines.index("set -euo pipefail") + 1
    guarded_block = [block_start, *moved_defaults, block_end]
    runner_path.write_text(
        "\n".join(remaining_lines[:insertion_index] + guarded_block + remaining_lines[insertion_index:])
        + "\n"
    )

    path = build_phase3_lane_index(
        baseline_root=baseline,
        repo_root=repo,
        output_dir=tmp_path / "out",
        lane_specs=(spec,),
    )
    manifest = json.loads(path.read_text())
    lane = manifest["lanes"][0]

    assert manifest["phase3_lanes_ready"] is False
    assert lane["runner_safety_defaults"] == {"PHASE3_REQUIRE_READY": "1"}
    assert lane["runner_gate_smoke_status"] == "passed"
    assert "phase3_lane_runner_safety_defaults" in manifest["summary"]["failed_kinds"]


def test_phase3_lane_index_rejects_runner_missing_bash_shebang(tmp_path):
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
    runner_path.write_text(runner_path.read_text().replace("#!/usr/bin/env bash\n", "", 1))

    path = build_phase3_lane_index(
        baseline_root=baseline,
        repo_root=repo,
        output_dir=tmp_path / "out",
        lane_specs=(spec,),
    )
    manifest = json.loads(path.read_text())
    lane = manifest["lanes"][0]

    assert manifest["phase3_lanes_ready"] is False
    assert lane["runner_shebang"] == "set -euo pipefail"
    assert "phase3_lane_runner_shell_contract" in manifest["summary"]["failed_kinds"]


def test_phase3_lane_index_rejects_runner_missing_strict_mode(tmp_path):
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
    runner_path.write_text(runner_path.read_text().replace("set -euo pipefail\n", "", 1))

    path = build_phase3_lane_index(
        baseline_root=baseline,
        repo_root=repo,
        output_dir=tmp_path / "out",
        lane_specs=(spec,),
    )
    manifest = json.loads(path.read_text())
    lane = manifest["lanes"][0]

    assert manifest["phase3_lanes_ready"] is False
    assert lane["runner_shebang"] == "#!/usr/bin/env bash"
    assert lane["runner_strict_mode_present"] is False
    assert "phase3_lane_runner_shell_contract" in manifest["summary"]["failed_kinds"]


def test_phase3_lane_index_rejects_runner_command_before_strict_mode(tmp_path):
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
    runner_path.write_text(
        runner_path.read_text().replace(
            "#!/usr/bin/env bash\nset -euo pipefail\n",
            "#!/usr/bin/env bash\necho pre-strict command >/dev/null\nset -euo pipefail\n",
            1,
        )
    )

    path = build_phase3_lane_index(
        baseline_root=baseline,
        repo_root=repo,
        output_dir=tmp_path / "out",
        lane_specs=(spec,),
    )
    manifest = json.loads(path.read_text())
    lane = manifest["lanes"][0]

    assert manifest["phase3_lanes_ready"] is False
    assert lane["runner_strict_mode_present"] is True
    assert lane["runner_strict_mode_before_first_command"] is False
    assert "phase3_lane_runner_shell_contract" in manifest["summary"]["failed_kinds"]


@pytest.mark.parametrize(
    ("failure_kind", "returncode"),
    (
        ("argv_mismatch", 0),
        ("none", 1),
    ),
)
def test_phase3_lane_index_rejects_inconsistent_successful_runner_gate_smoke(
    tmp_path,
    monkeypatch,
    failure_kind,
    returncode,
):
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

    def fake_smoke_result(*_args, **_kwargs):
        argv = _expected_runner_safety_gate_smoke_argv()
        return {
            "status": "passed",
            "validator_invocation_count": 1,
            "argv_matches_expected": True,
            "error": None,
            "failure_kind": failure_kind,
            "returncode": returncode,
            "expected_argv": argv,
            "observed_argv": argv,
            "observed_invocations": [argv],
            "argv_diff": [],
        }

    monkeypatch.setattr(phase3_lane_index, "_runner_gate_smoke_result", fake_smoke_result)

    path = build_phase3_lane_index(
        baseline_root=baseline,
        repo_root=repo,
        output_dir=tmp_path / "out",
        lane_specs=(spec,),
    )
    manifest = json.loads(path.read_text())

    assert manifest["phase3_lanes_ready"] is False
    lane = manifest["lanes"][0]
    assert lane["runner_gate_smoke_status"] == "passed"
    assert lane["runner_gate_smoke_failure_kind"] == failure_kind
    assert lane["runner_gate_smoke_returncode"] == returncode
    assert "phase3_lane_runner_gate_smoke" in manifest["summary"]["failed_kinds"]


def test_phase3_lane_index_rejects_hardcoded_validator_args_without_gate_array(tmp_path):
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
    runner_path = repo / spec.runner_relpath
    runner_path.parent.mkdir(parents=True, exist_ok=True)
    lines = [
        "#!/usr/bin/env bash",
        "set -euo pipefail",
    ]
    for name, value in _safety_defaults().items():
        prefix = "export " if name != "PHASE3_REQUIRE_READY" else ""
        lines.append(f'{prefix}{name}="${{{name}:-{value}}}"')
    lines.append(
        '"$PYTHON_BIN" -m scripts.function_tracer_pcode.validation.phase3_runner_safety_lane '
        '--gate-stage post-fix '
        '--baseline-raw-dir "$BASELINE_RAW_DIR" '
        '--output-dir "$PHASE3_GATE_OUTPUT_DIR" '
        '--phase3-manifest "$PHASE3_MANIFEST_PATH" '
        '--phase3-manifest-sha256 "$PHASE3_MANIFEST_SHA256" '
        "--require-ready"
    )
    runner_path.write_text("\n".join(lines) + "\n")
    runner_path.chmod(0o755)

    path = build_phase3_lane_index(
        baseline_root=baseline,
        repo_root=repo,
        output_dir=tmp_path / "out",
        lane_specs=(spec,),
    )
    manifest = json.loads(path.read_text())

    assert manifest["phase3_lanes_ready"] is False
    lane = manifest["lanes"][0]
    assert lane["runner_gate_args_invoked"] is True
    assert lane["runner_gate_args_assignment_count"] == 0
    assert all(value == "<missing>" for value in lane["runner_required_gate_args"].values())
    assert lane["runner_gate_args_invalid_mutation_count"] >= 1
    assert "phase3_lane_runner_required_gate_args" in manifest["summary"]["failed_kinds"]
    assert "phase3_lane_runner_gate_args_immutable" in manifest["summary"]["failed_kinds"]


@pytest.mark.parametrize(
    ("forged_arg", "expected_invoked"),
    (
        ('"__phase3_gate_args_array_probe__"', True),
        ('"$PHASE3_GATE_ARRAY_SENTINEL"', True),
    ),
)
def test_phase3_lane_index_rejects_forged_public_gate_array_sentinel(
    tmp_path,
    forged_arg,
    expected_invoked,
):
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
    runner_path.write_text(
        runner_path.read_text().replace(
            '    "${PHASE3_GATE_ARGS[@]}"',
            f"    {forged_arg} \\\n"
            "    --gate-stage post-fix \\\n"
            '    --baseline-raw-dir "$BASELINE_RAW_DIR" \\\n'
            '    --output-dir "$PHASE3_GATE_OUTPUT_DIR" \\\n'
            '    --phase3-manifest "$PHASE3_MANIFEST_PATH" \\\n'
            '    --phase3-manifest-sha256 "$PHASE3_MANIFEST_SHA256" \\\n'
            "    --require-ready",
        )
    )

    path = build_phase3_lane_index(
        baseline_root=baseline,
        repo_root=repo,
        output_dir=tmp_path / "out",
        lane_specs=(spec,),
    )
    manifest = json.loads(path.read_text())

    assert manifest["phase3_lanes_ready"] is False
    lane = manifest["lanes"][0]
    assert lane["runner_gate_args_invoked"] is expected_invoked
    if expected_invoked:
        assert lane["runner_gate_args_assignment_count"] == 1
        assert lane["runner_gate_args_invalid_mutation_count"] >= 1
        assert "phase3_lane_runner_gate_args_immutable" in manifest["summary"]["failed_kinds"]
        assert "validator did not consume PHASE3_GATE_ARGS array" in lane["runner_gate_args_invalid_mutations"]
    else:
        assert "phase3_lane_runner_gate_args_invoked" in manifest["summary"]["failed_kinds"]


def test_phase3_lane_index_rejects_single_gate_array_element_with_hardcoded_args(tmp_path):
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
    runner_path.write_text(
        runner_path.read_text().replace(
            '    "${PHASE3_GATE_ARGS[@]}"',
            '    "${PHASE3_GATE_ARGS[0]}" \\\n'
            "    --gate-stage post-fix \\\n"
            '    --baseline-raw-dir "$BASELINE_RAW_DIR" \\\n'
            '    --output-dir "$PHASE3_GATE_OUTPUT_DIR" \\\n'
            '    --phase3-manifest "$PHASE3_MANIFEST_PATH" \\\n'
            '    --phase3-manifest-sha256 "$PHASE3_MANIFEST_SHA256" \\\n'
            "    --require-ready",
        )
    )

    path = build_phase3_lane_index(
        baseline_root=baseline,
        repo_root=repo,
        output_dir=tmp_path / "out",
        lane_specs=(spec,),
    )
    manifest = json.loads(path.read_text())

    assert manifest["phase3_lanes_ready"] is False
    lane = manifest["lanes"][0]
    assert lane["runner_gate_args_invoked"] is True
    assert lane["runner_gate_args_assignment_count"] == 1
    assert lane["runner_gate_args_invalid_mutation_count"] >= 1
    assert "phase3_lane_runner_gate_args_immutable" in manifest["summary"]["failed_kinds"]
    assert "validator did not consume PHASE3_GATE_ARGS array" in lane["runner_gate_args_invalid_mutations"]


def test_phase3_lane_index_rejects_marker_prefix_forged_from_gate_array_element(tmp_path):
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
    runner_path.write_text(
        runner_path.read_text().replace(
            '    "${PHASE3_GATE_ARGS[@]}"',
            '    "${PHASE3_GATE_ARGS[0]%start}start" \\\n'
            '    "${PHASE3_GATE_ARGS[0]%start}arg:0" --gate-stage \\\n'
            '    "${PHASE3_GATE_ARGS[0]%start}arg:1" post-fix \\\n'
            '    "${PHASE3_GATE_ARGS[0]%start}arg:2" --baseline-raw-dir \\\n'
            '    "${PHASE3_GATE_ARGS[0]%start}arg:3" "$BASELINE_RAW_DIR" \\\n'
            '    "${PHASE3_GATE_ARGS[0]%start}arg:4" --output-dir \\\n'
            '    "${PHASE3_GATE_ARGS[0]%start}arg:5" "$PHASE3_GATE_OUTPUT_DIR" \\\n'
            '    "${PHASE3_GATE_ARGS[0]%start}arg:6" --phase3-manifest \\\n'
            '    "${PHASE3_GATE_ARGS[0]%start}arg:7" "$PHASE3_MANIFEST_PATH" \\\n'
            '    "${PHASE3_GATE_ARGS[0]%start}arg:8" --phase3-manifest-sha256 \\\n'
            '    "${PHASE3_GATE_ARGS[0]%start}arg:9" "$PHASE3_MANIFEST_SHA256" \\\n'
            '    "${PHASE3_GATE_ARGS[0]%start}arg:10" --require-ready \\\n'
            '    "${PHASE3_GATE_ARGS[0]%start}end:11"',
        )
    )

    path = build_phase3_lane_index(
        baseline_root=baseline,
        repo_root=repo,
        output_dir=tmp_path / "out",
        lane_specs=(spec,),
    )
    manifest = json.loads(path.read_text())

    assert manifest["phase3_lanes_ready"] is False
    lane = manifest["lanes"][0]
    assert lane["runner_gate_args_invoked"] is True
    assert lane["runner_gate_args_assignment_count"] == 1
    assert lane["runner_gate_args_invalid_mutation_count"] >= 1
    assert "phase3_lane_runner_gate_args_immutable" in manifest["summary"]["failed_kinds"]
    assert "validator did not consume PHASE3_GATE_ARGS array" in lane["runner_gate_args_invalid_mutations"]


def test_phase3_lane_index_rejects_full_array_decoy_literal_with_forged_markers(tmp_path):
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
    runner_path.write_text(
        runner_path.read_text().replace(
            '    "${PHASE3_GATE_ARGS[@]}"',
            '    "${PHASE3_GATE_ARGS[0]%start}start" \\\n'
            '    "${PHASE3_GATE_ARGS[0]%start}arg:0" --gate-stage \\\n'
            '    "${PHASE3_GATE_ARGS[0]%start}arg:1" post-fix \\\n'
            '    "${PHASE3_GATE_ARGS[0]%start}arg:2" --baseline-raw-dir \\\n'
            '    "${PHASE3_GATE_ARGS[0]%start}arg:3" "$BASELINE_RAW_DIR" \\\n'
            '    "${PHASE3_GATE_ARGS[0]%start}arg:4" --output-dir \\\n'
            '    "${PHASE3_GATE_ARGS[0]%start}arg:5" "$PHASE3_GATE_OUTPUT_DIR" \\\n'
            '    "${PHASE3_GATE_ARGS[0]%start}arg:6" --phase3-manifest \\\n'
            '    "${PHASE3_GATE_ARGS[0]%start}arg:7" "$PHASE3_MANIFEST_PATH" \\\n'
            '    "${PHASE3_GATE_ARGS[0]%start}arg:8" --phase3-manifest-sha256 \\\n'
            '    "${PHASE3_GATE_ARGS[0]%start}arg:9" "$PHASE3_MANIFEST_SHA256" \\\n'
            '    "${PHASE3_GATE_ARGS[0]%start}arg:10" --require-ready \\\n'
            '    "${PHASE3_GATE_ARGS[0]%start}end:11" \\\n'
            "    <<< '\"${PHASE3_GATE_ARGS[@]}\"'",
        )
    )

    path = build_phase3_lane_index(
        baseline_root=baseline,
        repo_root=repo,
        output_dir=tmp_path / "out",
        lane_specs=(spec,),
    )
    manifest = json.loads(path.read_text())

    assert manifest["phase3_lanes_ready"] is False
    lane = manifest["lanes"][0]
    assert lane["runner_gate_args_invoked"] is True
    assert lane["runner_gate_args_invalid_mutation_count"] >= 1
    assert "phase3_lane_runner_gate_args_immutable" in manifest["summary"]["failed_kinds"]
    assert "validator did not consume PHASE3_GATE_ARGS array" in lane["runner_gate_args_invalid_mutations"]


@pytest.mark.parametrize(
    "helper_mutation",
    (
        "__phase3_gate_probe_command_uses_full_gate_array() { return 0; }",
        "unset -f __phase3_gate_probe_command_uses_full_gate_array",
    ),
)
def test_phase3_lane_index_rejects_probe_helper_mutation_before_forged_markers(
    tmp_path,
    helper_mutation,
):
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
    runner_text = runner_path.read_text().replace(
        '"$PYTHON_BIN" -m',
        helper_mutation + '\n"$PYTHON_BIN" -m',
        1,
    )
    runner_text = runner_text.replace(
        '    "${PHASE3_GATE_ARGS[@]}"',
        '    "${PHASE3_GATE_ARGS[0]%start}start" \\\n'
        '    "${PHASE3_GATE_ARGS[0]%start}arg:0" --gate-stage \\\n'
        '    "${PHASE3_GATE_ARGS[0]%start}arg:1" post-fix \\\n'
        '    "${PHASE3_GATE_ARGS[0]%start}arg:2" --baseline-raw-dir \\\n'
        '    "${PHASE3_GATE_ARGS[0]%start}arg:3" "$BASELINE_RAW_DIR" \\\n'
        '    "${PHASE3_GATE_ARGS[0]%start}arg:4" --output-dir \\\n'
        '    "${PHASE3_GATE_ARGS[0]%start}arg:5" "$PHASE3_GATE_OUTPUT_DIR" \\\n'
        '    "${PHASE3_GATE_ARGS[0]%start}arg:6" --phase3-manifest \\\n'
        '    "${PHASE3_GATE_ARGS[0]%start}arg:7" "$PHASE3_MANIFEST_PATH" \\\n'
        '    "${PHASE3_GATE_ARGS[0]%start}arg:8" --phase3-manifest-sha256 \\\n'
        '    "${PHASE3_GATE_ARGS[0]%start}arg:9" "$PHASE3_MANIFEST_SHA256" \\\n'
        '    "${PHASE3_GATE_ARGS[0]%start}arg:10" --require-ready \\\n'
        '    "${PHASE3_GATE_ARGS[0]%start}end:11"',
    )
    runner_path.write_text(runner_text)

    path = build_phase3_lane_index(
        baseline_root=baseline,
        repo_root=repo,
        output_dir=tmp_path / "out",
        lane_specs=(spec,),
    )
    manifest = json.loads(path.read_text())

    assert manifest["phase3_lanes_ready"] is False
    lane = manifest["lanes"][0]
    assert lane["runner_gate_args_invoked"] is True
    assert lane["runner_gate_args_invalid_mutation_count"] >= 1
    assert "phase3_lane_runner_gate_args_immutable" in manifest["summary"]["failed_kinds"]
    assert "validator did not consume PHASE3_GATE_ARGS array" in lane["runner_gate_args_invalid_mutations"]


def test_phase3_lane_index_rejects_gate_args_mutation_history_even_if_restored(tmp_path):
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
    runner_path.write_text(
        runner_path.read_text().replace(
            "PHASE3_GATE_ARGS=(",
            "PHASE3_GATE_ARGS=(--gate-stage pre-fix)\nPHASE3_GATE_ARGS=(",
            1,
        )
    )

    path = build_phase3_lane_index(
        baseline_root=baseline,
        repo_root=repo,
        output_dir=tmp_path / "out",
        lane_specs=(spec,),
    )
    manifest = json.loads(path.read_text())

    assert manifest["phase3_lanes_ready"] is False
    lane = manifest["lanes"][0]
    assert lane["runner_gate_args_invoked"] is True
    assert lane["runner_gate_args_assignment_count"] == 1
    assert lane["runner_gate_args_invalid_mutation_count"] >= 1
    assert "phase3_lane_runner_gate_args_immutable" in manifest["summary"]["failed_kinds"]


def test_phase3_lane_index_rejects_runner_failure_after_gate_validator(tmp_path):
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
        handle.write("false\n")

    path = build_phase3_lane_index(
        baseline_root=baseline,
        repo_root=repo,
        output_dir=tmp_path / "out",
        lane_specs=(spec,),
    )
    manifest = json.loads(path.read_text())

    assert manifest["phase3_lanes_ready"] is False
    lane = manifest["lanes"][0]
    assert lane["runner_gate_args_invoked"] is True
    assert lane["runner_gate_args_invalid_mutation_count"] >= 1
    assert "phase3_lane_runner_gate_args_immutable" in manifest["summary"]["failed_kinds"]
    assert "runner smoke execution failed: returncode=1" in lane["runner_gate_args_invalid_mutations"]
    assert "phase3_lane_runner_gate_smoke" in manifest["summary"]["failed_kinds"]
    assert lane["runner_gate_smoke_status"] == "failed"
    assert lane["runner_gate_smoke_validator_invocation_count"] == 1
    assert lane["runner_gate_smoke_argv_matches_expected"] is True
    assert lane["runner_gate_smoke_error"] == "runner smoke execution failed: returncode=1"
    assert lane["runner_gate_smoke_failure_kind"] == "nonzero_exit"
    assert lane["runner_gate_smoke_returncode"] == 1


def test_phase3_lane_index_rejects_runner_gate_smoke_argv_mismatch(tmp_path):
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
    runner_path.write_text(
        runner_path.read_text().replace(
            "PHASE3_GATE_ARGS=(",
            'PHASE3_GATE_OUTPUT_DIR="/tmp/phase3-wrong-gate-output"\nPHASE3_GATE_ARGS=(',
            1,
        )
    )

    path = build_phase3_lane_index(
        baseline_root=baseline,
        repo_root=repo,
        output_dir=tmp_path / "out",
        lane_specs=(spec,),
    )
    manifest = json.loads(path.read_text())

    assert manifest["phase3_lanes_ready"] is False
    lane = manifest["lanes"][0]
    assert lane["runner_gate_args_invoked"] is True
    assert lane["runner_gate_args_assignment_count"] == 1
    assert lane["runner_required_gate_args"] == {
        "--gate-stage": "post-fix",
        "--baseline-raw-dir": "$BASELINE_RAW_DIR",
        "--output-dir": "$PHASE3_GATE_OUTPUT_DIR",
        "--phase3-manifest": "$PHASE3_MANIFEST_PATH",
        "--phase3-manifest-sha256": "$PHASE3_MANIFEST_SHA256",
    }
    assert lane["runner_gate_smoke_status"] == "failed"
    assert lane["runner_gate_smoke_validator_invocation_count"] == 1
    assert lane["runner_gate_smoke_argv_matches_expected"] is False
    assert lane["runner_gate_smoke_error"] == "runner smoke validator argv differed from expected gate arguments"
    assert lane["runner_gate_smoke_failure_kind"] == "argv_mismatch"
    assert lane["runner_gate_smoke_returncode"] == 0
    assert lane["runner_gate_smoke_expected_argv"] == _expected_runner_safety_gate_smoke_argv()
    assert lane["runner_gate_smoke_observed_argv"] == [
        "-m",
        "scripts.function_tracer_pcode.validation.phase3_runner_safety_lane",
        "--gate-stage",
        "post-fix",
        "--baseline-raw-dir",
        "$BASELINE_RAW_DIR",
        "--output-dir",
        "/tmp/phase3-wrong-gate-output",
        "--phase3-manifest",
        "$PHASE3_MANIFEST_PATH",
        "--phase3-manifest-sha256",
        "$PHASE3_MANIFEST_SHA256",
        "--require-ready",
    ]
    assert lane["runner_gate_smoke_observed_invocations"] == [
        lane["runner_gate_smoke_observed_argv"]
    ]
    assert lane["runner_gate_smoke_argv_diff"] == [
        {
            "index": 7,
            "expected": "$PHASE3_GATE_OUTPUT_DIR",
            "observed": "/tmp/phase3-wrong-gate-output",
        }
    ]
    assert "phase3_lane_runner_gate_smoke" in manifest["summary"]["failed_kinds"]


@pytest.mark.parametrize("early_exit", ("exit 0", "exec true"))
def test_phase3_lane_index_rejects_unreached_gate_validator(tmp_path, early_exit):
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
    runner_path.write_text(
        runner_path.read_text().replace(
            '"$PYTHON_BIN" -m',
            early_exit + '\n"$PYTHON_BIN" -m',
            1,
        )
    )

    path = build_phase3_lane_index(
        baseline_root=baseline,
        repo_root=repo,
        output_dir=tmp_path / "out",
        lane_specs=(spec,),
    )
    manifest = json.loads(path.read_text())

    assert manifest["phase3_lanes_ready"] is False
    lane = manifest["lanes"][0]
    assert lane["runner_gate_args_invoked"] is True
    assert lane["runner_gate_args_invalid_mutation_count"] >= 1
    assert "phase3_lane_runner_gate_args_immutable" in manifest["summary"]["failed_kinds"]
    assert "runner smoke validator invocation count was 0" in lane["runner_gate_args_invalid_mutations"]


@pytest.mark.parametrize(
    "tamper_lines",
    (
        (
            "__PHASE3_GATE_PROBE_IN_TRAP=1",
            "PHASE3_GATE_ARGS=(--gate-stage pre-fix)",
            "PHASE3_GATE_ARGS=(",
            "    --gate-stage post-fix",
            '    --baseline-raw-dir "$BASELINE_RAW_DIR"',
            '    --output-dir "$PHASE3_GATE_OUTPUT_DIR"',
            '    --phase3-manifest "$PHASE3_MANIFEST_PATH"',
            '    --phase3-manifest-sha256 "$PHASE3_MANIFEST_SHA256"',
            ")",
            "PHASE3_GATE_ARGS+=(--require-ready)",
            "unset __PHASE3_GATE_PROBE_IN_TRAP",
        ),
        (
            "PHASE3_RUNNER_PROBE_PYTHON=/bin/true",
            "PHASE3_GATE_ARGS=(--gate-stage pre-fix)",
            "PHASE3_GATE_ARGS=(",
            "    --gate-stage post-fix",
            '    --baseline-raw-dir "$BASELINE_RAW_DIR"',
            '    --output-dir "$PHASE3_GATE_OUTPUT_DIR"',
            '    --phase3-manifest "$PHASE3_MANIFEST_PATH"',
            '    --phase3-manifest-sha256 "$PHASE3_MANIFEST_SHA256"',
            ")",
            "PHASE3_GATE_ARGS+=(--require-ready)",
            "unset PHASE3_RUNNER_PROBE_PYTHON",
        ),
    ),
)
def test_phase3_lane_index_rejects_runtime_probe_variable_tampering(
    tmp_path,
    tamper_lines,
):
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
    runner_path.write_text(
        runner_path.read_text().replace(
            '"$PYTHON_BIN" -m',
            "\n".join(tamper_lines) + '\n"$PYTHON_BIN" -m',
            1,
        )
    )

    path = build_phase3_lane_index(
        baseline_root=baseline,
        repo_root=repo,
        output_dir=tmp_path / "out",
        lane_specs=(spec,),
    )
    manifest = json.loads(path.read_text())

    assert manifest["phase3_lanes_ready"] is False
    lane = manifest["lanes"][0]
    assert lane["runner_gate_args_invoked"] is True
    assert lane["runner_gate_args_invalid_mutation_count"] >= 1
    assert "phase3_lane_runner_gate_args_immutable" in manifest["summary"]["failed_kinds"]


@pytest.mark.parametrize(
    "extra_line",
    (
        "PHASE3_GATE_ARGS+=(--unexpected-option value)",
        'PHASE3_GATE_ARGS+=(--current-log-root "function_call=/tmp/wrong")',
        "PHASE3_GATE_ARGS+=(--require-ready)",
    ),
)
def test_phase3_lane_index_rejects_extra_runtime_gate_args(tmp_path, extra_line):
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
    runner_path.write_text(
        runner_path.read_text().replace(
            '"$PYTHON_BIN" -m',
            extra_line + '\n"$PYTHON_BIN" -m',
            1,
        )
    )

    path = build_phase3_lane_index(
        baseline_root=baseline,
        repo_root=repo,
        output_dir=tmp_path / "out",
        lane_specs=(spec,),
    )
    manifest = json.loads(path.read_text())

    assert manifest["phase3_lanes_ready"] is False
    lane = manifest["lanes"][0]
    assert lane["runner_gate_args_invoked"] is True
    assert lane["runner_gate_args_assignment_count"] == 1
    assert lane["runner_gate_args_invalid_mutation_count"] >= 1
    assert "phase3_lane_runner_gate_args_immutable" in manifest["summary"]["failed_kinds"]


def test_phase3_lane_index_accepts_expected_runner_gate_validator_module(tmp_path):
    baseline = tmp_path / "baseline"
    repo = tmp_path / "repo"
    _write_baseline(baseline)
    expected_module = "scripts.function_tracer_pcode.validation.phase3_expected_lane"
    spec = Phase3LaneSpec(
        lane_number=1,
        lane_id="runner_safety_lane",
        target_reason_ids=("reason_one",),
        manifest_relpath="audit/runner_safety_lane/manifest.json",
        runner_relpath="run_runner_safety_lane.sh",
        manifest_kind="runner_safety_lane_manifest",
        ready_key="runner_safety_lane_ready",
        gate_validator_module=expected_module,
        require_runner_safety_defaults=True,
    )
    _write_manifest(baseline, spec)
    _write_runner(
        repo,
        spec,
        safety_defaults=_safety_defaults(),
        require_ready_arg=True,
        invoke_gate_args=True,
        gate_validator_module=expected_module,
    )

    path = build_phase3_lane_index(
        baseline_root=baseline,
        repo_root=repo,
        output_dir=tmp_path / "out",
        lane_specs=(spec,),
    )
    manifest = json.loads(path.read_text())

    assert manifest["phase3_lanes_ready"] is True
    assert manifest["lanes"][0]["runner_gate_validator_module"] == expected_module


def test_phase3_lane_index_rejects_wrong_runner_gate_validator_module(tmp_path):
    baseline = tmp_path / "baseline"
    repo = tmp_path / "repo"
    _write_baseline(baseline)
    expected_module = "scripts.function_tracer_pcode.validation.phase3_expected_lane"
    spec = Phase3LaneSpec(
        lane_number=1,
        lane_id="runner_safety_lane",
        target_reason_ids=("reason_one",),
        manifest_relpath="audit/runner_safety_lane/manifest.json",
        runner_relpath="run_runner_safety_lane.sh",
        manifest_kind="runner_safety_lane_manifest",
        ready_key="runner_safety_lane_ready",
        gate_validator_module=expected_module,
        require_runner_safety_defaults=True,
    )
    _write_manifest(baseline, spec)
    _write_runner(
        repo,
        spec,
        safety_defaults=_safety_defaults(),
        require_ready_arg=True,
        invoke_gate_args=True,
        gate_validator_module="scripts.function_tracer_pcode.validation.phase3_wrong_lane",
    )

    path = build_phase3_lane_index(
        baseline_root=baseline,
        repo_root=repo,
        output_dir=tmp_path / "out",
        lane_specs=(spec,),
    )
    manifest = json.loads(path.read_text())

    assert manifest["phase3_lanes_ready"] is False
    lane = manifest["lanes"][0]
    assert lane["runner_gate_args_invoked"] is True
    assert lane["runner_gate_validator_module"] == "scripts.function_tracer_pcode.validation.phase3_wrong_lane"
    assert "phase3_lane_runner_gate_validator_module" in manifest["summary"]["failed_kinds"]


def test_phase3_lane_index_rejects_missing_required_runner_gate_arg(tmp_path):
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
        required_gate_arg_overrides={"--phase3-manifest-sha256": "<missing>"},
    )
    runner_path = repo / spec.runner_relpath
    runner_path.write_text(
        runner_path.read_text().replace("    --phase3-manifest-sha256 <missing>\n", "")
    )

    path = build_phase3_lane_index(
        baseline_root=baseline,
        repo_root=repo,
        output_dir=tmp_path / "out",
        lane_specs=(spec,),
    )
    manifest = json.loads(path.read_text())

    assert manifest["phase3_lanes_ready"] is False
    lane = manifest["lanes"][0]
    assert lane["runner_required_gate_arg_counts"]["--phase3-manifest-sha256"] == 0
    assert lane["runner_required_gate_args_missing"] == ["--phase3-manifest-sha256"]
    assert lane["runner_required_gate_args_duplicate"] == []
    assert lane["runner_required_gate_args_value_mismatch"] == []
    assert "phase3_lane_runner_required_gate_args" in manifest["summary"]["failed_kinds"]


def test_phase3_lane_index_rejects_duplicate_required_runner_gate_arg(tmp_path):
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
    runner_path.write_text(
        runner_path.read_text().replace(
            ")\nif [[",
            '    --phase3-manifest-sha256 "$PHASE3_MANIFEST_SHA256"\n)\nif [[',
            1,
        )
    )

    path = build_phase3_lane_index(
        baseline_root=baseline,
        repo_root=repo,
        output_dir=tmp_path / "out",
        lane_specs=(spec,),
    )
    manifest = json.loads(path.read_text())

    assert manifest["phase3_lanes_ready"] is False
    lane = manifest["lanes"][0]
    assert lane["runner_required_gate_arg_counts"]["--phase3-manifest-sha256"] == 2
    assert lane["runner_required_gate_args_missing"] == []
    assert lane["runner_required_gate_args_duplicate"] == ["--phase3-manifest-sha256"]
    assert lane["runner_required_gate_args_value_mismatch"] == []
    assert "phase3_lane_runner_required_gate_args" in manifest["summary"]["failed_kinds"]


def test_phase3_lane_index_rejects_wrong_required_runner_gate_arg_value(tmp_path):
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
        required_gate_arg_overrides={"--gate-stage": "pre-fix"},
    )

    path = build_phase3_lane_index(
        baseline_root=baseline,
        repo_root=repo,
        output_dir=tmp_path / "out",
        lane_specs=(spec,),
    )
    manifest = json.loads(path.read_text())

    assert manifest["phase3_lanes_ready"] is False
    lane = manifest["lanes"][0]
    assert lane["runner_required_gate_args"]["--gate-stage"] == "pre-fix"
    assert lane["runner_required_gate_args_missing"] == []
    assert lane["runner_required_gate_args_duplicate"] == []
    assert lane["runner_required_gate_args_value_mismatch"] == [
        {
            "flag": "--gate-stage",
            "expected": "post-fix",
            "actual": "pre-fix",
        }
    ]
    assert "phase3_lane_runner_required_gate_args" in manifest["summary"]["failed_kinds"]


def test_phase3_lane_index_rejects_phase3_gate_args_reassignment_before_validator(tmp_path):
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
    runner_path.write_text(
        runner_path.read_text().replace(
            '"$PYTHON_BIN" -m',
            'PHASE3_GATE_ARGS=()\n"$PYTHON_BIN" -m',
            1,
        )
    )

    path = build_phase3_lane_index(
        baseline_root=baseline,
        repo_root=repo,
        output_dir=tmp_path / "out",
        lane_specs=(spec,),
    )
    manifest = json.loads(path.read_text())

    assert manifest["phase3_lanes_ready"] is False
    lane = manifest["lanes"][0]
    assert lane["runner_gate_args_assignment_count"] == 1
    assert lane["runner_gate_args_invalid_mutation_count"] >= 1
    assert lane["runner_gate_args_invoked"] is True
    assert "phase3_lane_runner_gate_args_immutable" in manifest["summary"]["failed_kinds"]


@pytest.mark.parametrize(
    "mutation_lines",
    (
        ("unset PHASE3_GATE_ARGS",),
        ("unset PHASE3_GATE_ARGS[0]",),
        ("unset 'PHASE3_GATE_ARGS[0]'",),
        ("unset -v PHASE3_GATE_ARGS[0]",),
        ("unset 'PHASE3_GATE_ARGS[@]'",),
        ("builtin unset PHASE3_GATE_ARGS[0]",),
        ("command unset PHASE3_GATE_ARGS[0]",),
        ("builtin unset 'PHASE3_GATE_ARGS[0]",),
        ("command unset 'PHASE3_GATE_ARGS[0]",),
        ('PHASE3_GATE_ARGS=("${OTHER_ARGS[@]}")',),
        ("PHASE3_GATE_ARGS+=(--gate-stage pre-fix)",),
        ("PHASE3_GATE_ARGS[1]=pre-fix",),
        ("declare -a PHASE3_GATE_ARGS=(bad)",),
        ("typeset -a PHASE3_GATE_ARGS=(bad)",),
        ("readonly -a PHASE3_GATE_ARGS=(bad)",),
        ("declare -n GATE_ALIAS=PHASE3_GATE_ARGS", "GATE_ALIAS=(--gate-stage pre-fix)"),
        ("typeset -n GATE_ALIAS=PHASE3_GATE_ARGS", "GATE_ALIAS=(--gate-stage pre-fix)"),
        ("builtin declare -n GATE_ALIAS=PHASE3_GATE_ARGS", "GATE_ALIAS=(--gate-stage pre-fix)"),
        ("command declare -n GATE_ALIAS=PHASE3_GATE_ARGS", "GATE_ALIAS=(--gate-stage pre-fix)"),
        ("builtin typeset -n GATE_ALIAS=PHASE3_GATE_ARGS", "GATE_ALIAS=(--gate-stage pre-fix)"),
        ("command typeset -n GATE_ALIAS=PHASE3_GATE_ARGS", "GATE_ALIAS=(--gate-stage pre-fix)"),
        ("eval 'PHASE3_GATE_ARGS=(--gate-stage pre-fix)'",),
        ("eval 'unset PHASE3_GATE_ARGS'",),
        ('builtin eval "PHASE3_GATE_ARGS=(--gate-stage pre-fix)"',),
        ("builtin printf -v PHASE3_GATE_ARGS %s pre-fix",),
        ('command eval "PHASE3_GATE_ARGS=(--gate-stage pre-fix)"',),
        ("command printf -v PHASE3_GATE_ARGS %s pre-fix",),
        ('read -a PHASE3_GATE_ARGS <<< "--gate-stage pre-fix"',),
        ('readarray -t PHASE3_GATE_ARGS <<< "--gate-stage pre-fix"',),
        ('mapfile -t PHASE3_GATE_ARGS <<< "--gate-stage pre-fix"',),
        ("printf -v PHASE3_GATE_ARGS %s pre-fix",),
    ),
)
def test_phase3_lane_index_rejects_phase3_gate_args_mutation_before_validator(
    tmp_path,
    mutation_lines,
):
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
    runner_path.write_text(
        runner_path.read_text().replace(
            '"$PYTHON_BIN" -m',
            "\n".join(mutation_lines) + '\n"$PYTHON_BIN" -m',
            1,
        )
    )

    path = build_phase3_lane_index(
        baseline_root=baseline,
        repo_root=repo,
        output_dir=tmp_path / "out",
        lane_specs=(spec,),
    )
    manifest = json.loads(path.read_text())

    assert manifest["phase3_lanes_ready"] is False
    lane = manifest["lanes"][0]
    assert (
        lane["runner_gate_args_invalid_mutation_count"] >= 1
        or lane["runner_gate_args_invoked"] is False
    )
    assert (
        "phase3_lane_runner_gate_args_immutable" in manifest["summary"]["failed_kinds"]
        or "phase3_lane_runner_gate_args_invoked" in manifest["summary"]["failed_kinds"]
    )


@pytest.mark.parametrize(
    "mutation_lines",
    (
        (
            "GATE_ALIAS=PHASE3_GATE_ARGS",
            "declare -n GATE_ALIAS",
            "GATE_ALIAS=(--gate-stage pre-fix)",
        ),
        (
            "PHASE3_REF=PHASE3_GATE_ARGS",
            "typeset -n PHASE3_REF",
            "PHASE3_REF=(--gate-stage pre-fix)",
        ),
        (
            "declare -n GATE_ALIAS",
            "GATE_ALIAS=PHASE3_GATE_ARGS",
            "GATE_ALIAS=(--gate-stage pre-fix)",
        ),
        (
            "declare -n GATE_ALIAS; "
            "GATE_ALIAS=PHASE3_GATE_ARGS; "
            "GATE_ALIAS=(--gate-stage pre-fix)",
        ),
    ),
)
def test_phase3_lane_index_rejects_two_step_nameref_gate_args_mutation(
    tmp_path,
    mutation_lines,
):
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
    runner_path.write_text(
        runner_path.read_text().replace(
            '"$PYTHON_BIN" -m',
            "\n".join(mutation_lines) + '\n"$PYTHON_BIN" -m',
            1,
        )
    )

    path = build_phase3_lane_index(
        baseline_root=baseline,
        repo_root=repo,
        output_dir=tmp_path / "out",
        lane_specs=(spec,),
    )
    manifest = json.loads(path.read_text())

    assert manifest["phase3_lanes_ready"] is False
    lane = manifest["lanes"][0]
    assert lane["runner_gate_args_invoked"] is True
    assert lane["runner_gate_args_assignment_count"] == 1
    assert lane["runner_gate_args_invalid_mutation_count"] >= 1
    assert "phase3_lane_runner_gate_args_immutable" in manifest["summary"]["failed_kinds"]


@pytest.mark.parametrize(
    "mutation_lines",
    (
        (
            "target=PHASE3_GATE_ARGS",
            'unset "$target"',
        ),
        (
            "target=PHASE3_GATE_ARGS",
            'printf -v "$target" %s pre-fix',
        ),
        (
            "target=PHASE3_GATE_ARGS",
            'read "$target" <<< pre-fix',
        ),
        (
            "target=PHASE3_GATE_ARGS",
            'eval "$target=(--gate-stage pre-fix)"',
        ),
        (
            "target=PHASE3_GATE_ARGS",
            'declare "$target=pre-fix"',
        ),
        (
            "target=PHASE3_GATE_ARGS",
            'unset "${target}"',
        ),
        (
            "export target=PHASE3_GATE_ARGS",
            'unset "$target"',
        ),
        (
            "declare target=PHASE3_GATE_ARGS",
            'printf -v "$target" %s pre-fix',
        ),
        (
            "target=PHASE3_GATE_ARGS",
            'export "$target=pre-fix"',
        ),
    ),
)
def test_phase3_lane_index_rejects_variable_alias_builtin_gate_args_mutation(
    tmp_path,
    mutation_lines,
):
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
    runner_path.write_text(
        runner_path.read_text().replace(
            '"$PYTHON_BIN" -m',
            "\n".join(mutation_lines) + '\n"$PYTHON_BIN" -m',
            1,
        )
    )

    path = build_phase3_lane_index(
        baseline_root=baseline,
        repo_root=repo,
        output_dir=tmp_path / "out",
        lane_specs=(spec,),
    )
    manifest = json.loads(path.read_text())

    assert manifest["phase3_lanes_ready"] is False
    lane = manifest["lanes"][0]
    assert lane["runner_gate_args_invoked"] is True
    assert lane["runner_gate_args_assignment_count"] == 1
    assert lane["runner_gate_args_invalid_mutation_count"] >= 1
    assert "phase3_lane_runner_gate_args_immutable" in manifest["summary"]["failed_kinds"]


@pytest.mark.parametrize(
    "mutation_lines",
    (
        ("target=PHASE3_GATE_ARGS", 'target2="$target"', 'unset "$target2"'),
        ("target=PHASE3_GATE_ARGS", 'target2="$target"', 'printf -v "$target2" %s pre-fix'),
        ("target=PHASE3_GATE_ARGS", 'target2="$target"', 'read "$target2" <<< pre-fix'),
        ("target=PHASE3_GATE_ARGS", 'target2="$target"', 'eval "$target2=(--gate-stage pre-fix)"'),
        ("target=PHASE3_GATE_ARGS", 'target2="$target"', 'declare "$target2=pre-fix"'),
        ("target=PHASE3_GATE_ARGS", 'target2="$target"', 'export "$target2=pre-fix"'),
    ),
)
def test_phase3_lane_index_rejects_transitive_alias_gate_args_mutation(
    tmp_path,
    mutation_lines,
):
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
    runner_path.write_text(
        runner_path.read_text().replace(
            '"$PYTHON_BIN" -m',
            "\n".join(mutation_lines) + '\n"$PYTHON_BIN" -m',
            1,
        )
    )

    path = build_phase3_lane_index(
        baseline_root=baseline,
        repo_root=repo,
        output_dir=tmp_path / "out",
        lane_specs=(spec,),
    )
    manifest = json.loads(path.read_text())

    assert manifest["phase3_lanes_ready"] is False
    lane = manifest["lanes"][0]
    assert lane["runner_gate_args_invoked"] is True
    assert lane["runner_gate_args_invalid_mutation_count"] >= 1
    assert "phase3_lane_runner_gate_args_immutable" in manifest["summary"]["failed_kinds"]


@pytest.mark.parametrize(
    "mutation_lines",
    (
        ("target=PHASE3_", "target+=GATE_ARGS", 'printf -v "$target" %s pre-fix'),
        ("target=PHASE3_", "target+=GATE_ARGS", 'eval "$target=(--gate-stage pre-fix)"'),
        ("target=PHASE3_", "target+=GATE_ARGS", 'unset "$target"'),
        ("target=PHASE3_", "target+=GATE_ARGS", 'read "$target" <<< pre-fix'),
    ),
)
def test_phase3_lane_index_rejects_split_name_alias_gate_args_mutation(
    tmp_path,
    mutation_lines,
):
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
    runner_path.write_text(
        runner_path.read_text().replace(
            '"$PYTHON_BIN" -m',
            "\n".join(mutation_lines) + '\n"$PYTHON_BIN" -m',
            1,
        )
    )

    path = build_phase3_lane_index(
        baseline_root=baseline,
        repo_root=repo,
        output_dir=tmp_path / "out",
        lane_specs=(spec,),
    )
    manifest = json.loads(path.read_text())

    assert manifest["phase3_lanes_ready"] is False
    lane = manifest["lanes"][0]
    assert lane["runner_gate_args_invoked"] is True
    assert lane["runner_gate_args_invalid_mutation_count"] >= 1
    assert "phase3_lane_runner_gate_args_immutable" in manifest["summary"]["failed_kinds"]


@pytest.mark.parametrize("disable_debug_trap", ("trap - DEBUG", "builtin trap - DEBUG"))
def test_phase3_lane_index_rejects_gate_args_restore_after_debug_trap_disabled(
    tmp_path,
    disable_debug_trap,
):
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
    restore_lines = "\n".join(
        (
            disable_debug_trap,
            "PHASE3_GATE_ARGS=(--gate-stage pre-fix)",
            "PHASE3_GATE_ARGS=(",
            "    --gate-stage post-fix",
            '    --baseline-raw-dir "$BASELINE_RAW_DIR"',
            '    --output-dir "$PHASE3_GATE_OUTPUT_DIR"',
            '    --phase3-manifest "$PHASE3_MANIFEST_PATH"',
            '    --phase3-manifest-sha256 "$PHASE3_MANIFEST_SHA256"',
            ")",
            "PHASE3_GATE_ARGS+=(--require-ready)",
            "trap '__phase3_gate_probe_debug_trap' DEBUG",
        )
    )
    runner_path.write_text(
        runner_path.read_text().replace(
            '"$PYTHON_BIN" -m',
            restore_lines + '\n"$PYTHON_BIN" -m',
            1,
        )
    )

    path = build_phase3_lane_index(
        baseline_root=baseline,
        repo_root=repo,
        output_dir=tmp_path / "out",
        lane_specs=(spec,),
    )
    manifest = json.loads(path.read_text())

    assert manifest["phase3_lanes_ready"] is False
    lane = manifest["lanes"][0]
    assert lane["runner_gate_args_invoked"] is True
    assert lane["runner_gate_args_invalid_mutation_count"] >= 1
    assert "phase3_lane_runner_gate_args_immutable" in manifest["summary"]["failed_kinds"]


@pytest.mark.parametrize(
    "function_definition",
    (
        "mutate_gate_args() { PHASE3_GATE_ARGS=(--gate-stage pre-fix); }",
        'mutate_gate_args() { target=PHASE3_GATE_ARGS; unset "$target"; }',
        'mutate_gate_args() { target=PHASE3_GATE_ARGS; printf -v "$target" %s pre-fix; }',
        'mutate_gate_args() { local target=PHASE3_GATE_ARGS; unset "$target"; }',
        "\n".join(
            (
                "mutate_gate_args()",
                "{",
                "    PHASE3_GATE_ARGS=(--gate-stage pre-fix)",
                "}",
            )
        ),
        "\n".join(
            (
                "function mutate_gate_args",
                "{",
                "    unset PHASE3_GATE_ARGS[0]",
                "}",
            )
        ),
    ),
)
def test_phase3_lane_index_rejects_called_function_that_mutates_gate_args(
    tmp_path,
    function_definition,
):
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
    runner_text = runner_path.read_text()
    runner_text = runner_text.replace(
        "PHASE3_GATE_ARGS=(",
        function_definition + "\nPHASE3_GATE_ARGS=(",
        1,
    )
    runner_text = runner_text.replace(
        '"$PYTHON_BIN" -m',
        'mutate_gate_args\n"$PYTHON_BIN" -m',
        1,
    )
    runner_path.write_text(runner_text)

    path = build_phase3_lane_index(
        baseline_root=baseline,
        repo_root=repo,
        output_dir=tmp_path / "out",
        lane_specs=(spec,),
    )
    manifest = json.loads(path.read_text())

    assert manifest["phase3_lanes_ready"] is False
    lane = manifest["lanes"][0]
    assert lane["runner_gate_args_invoked"] is True
    assert lane["runner_gate_args_assignment_count"] == 1
    assert lane["runner_gate_args_invalid_mutation_count"] >= 1
    assert "phase3_lane_runner_gate_args_immutable" in manifest["summary"]["failed_kinds"]


@pytest.mark.parametrize(
    "call_line",
    (
        "if mutate_gate_args; then :; fi",
        "! mutate_gate_args",
        "time mutate_gate_args",
    ),
)
def test_phase3_lane_index_rejects_control_prefix_mutating_function_call(
    tmp_path,
    call_line,
):
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
    runner_text = runner_path.read_text()
    runner_text = runner_text.replace(
        "PHASE3_GATE_ARGS=(",
        "mutate_gate_args() { PHASE3_GATE_ARGS=(--gate-stage pre-fix); }\nPHASE3_GATE_ARGS=(",
        1,
    )
    runner_text = runner_text.replace(
        '"$PYTHON_BIN" -m',
        call_line + '\n"$PYTHON_BIN" -m',
        1,
    )
    runner_path.write_text(runner_text)

    path = build_phase3_lane_index(
        baseline_root=baseline,
        repo_root=repo,
        output_dir=tmp_path / "out",
        lane_specs=(spec,),
    )
    manifest = json.loads(path.read_text())

    assert manifest["phase3_lanes_ready"] is False
    lane = manifest["lanes"][0]
    assert lane["runner_gate_args_invoked"] is True
    assert lane["runner_gate_args_invalid_mutation_count"] >= 1
    assert "phase3_lane_runner_gate_args_immutable" in manifest["summary"]["failed_kinds"]


def test_phase3_lane_index_rejects_function_internal_mutation_even_if_restored(tmp_path):
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
    restore_function = "\n".join(
        (
            "mutate_gate_args()",
            "{",
            "    PHASE3_GATE_ARGS=(--gate-stage pre-fix)",
            "    PHASE3_GATE_ARGS=(",
            "        --gate-stage post-fix",
            '        --baseline-raw-dir "$BASELINE_RAW_DIR"',
            '        --output-dir "$PHASE3_GATE_OUTPUT_DIR"',
            '        --phase3-manifest "$PHASE3_MANIFEST_PATH"',
            '        --phase3-manifest-sha256 "$PHASE3_MANIFEST_SHA256"',
            "    )",
            "    PHASE3_GATE_ARGS+=(--require-ready)",
            "}",
        )
    )
    runner_text = runner_path.read_text()
    runner_text = runner_text.replace(
        "PHASE3_GATE_ARGS=(",
        restore_function + "\nPHASE3_GATE_ARGS=(",
        1,
    )
    runner_text = runner_text.replace(
        '"$PYTHON_BIN" -m',
        'mutate_gate_args\n"$PYTHON_BIN" -m',
        1,
    )
    runner_path.write_text(runner_text)

    path = build_phase3_lane_index(
        baseline_root=baseline,
        repo_root=repo,
        output_dir=tmp_path / "out",
        lane_specs=(spec,),
    )
    manifest = json.loads(path.read_text())

    assert manifest["phase3_lanes_ready"] is False
    lane = manifest["lanes"][0]
    assert lane["runner_gate_args_invoked"] is True
    assert lane["runner_required_gate_args"] == {
        "--gate-stage": "post-fix",
        "--baseline-raw-dir": "$BASELINE_RAW_DIR",
        "--output-dir": "$PHASE3_GATE_OUTPUT_DIR",
        "--phase3-manifest": "$PHASE3_MANIFEST_PATH",
        "--phase3-manifest-sha256": "$PHASE3_MANIFEST_SHA256",
    }
    assert lane["runner_gate_args_invalid_mutation_count"] >= 1
    assert "phase3_lane_runner_gate_args_immutable" in manifest["summary"]["failed_kinds"]


@pytest.mark.parametrize("disable_functrace", ("set +o functrace", "set +T"))
def test_phase3_lane_index_rejects_function_internal_restore_after_functrace_disabled(
    tmp_path,
    disable_functrace,
):
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
    restore_function = "\n".join(
        (
            "mutate_gate_args()",
            "{",
            "    PHASE3_GATE_ARGS=(--gate-stage pre-fix)",
            "    PHASE3_GATE_ARGS=(",
            "        --gate-stage post-fix",
            '        --baseline-raw-dir "$BASELINE_RAW_DIR"',
            '        --output-dir "$PHASE3_GATE_OUTPUT_DIR"',
            '        --phase3-manifest "$PHASE3_MANIFEST_PATH"',
            '        --phase3-manifest-sha256 "$PHASE3_MANIFEST_SHA256"',
            "    )",
            "    PHASE3_GATE_ARGS+=(--require-ready)",
            "}",
        )
    )
    runner_text = runner_path.read_text()
    runner_text = runner_text.replace(
        "PHASE3_GATE_ARGS=(",
        restore_function + "\nPHASE3_GATE_ARGS=(",
        1,
    )
    runner_text = runner_text.replace(
        '"$PYTHON_BIN" -m',
        disable_functrace + '\nmutate_gate_args\n"$PYTHON_BIN" -m',
        1,
    )
    runner_path.write_text(runner_text)

    path = build_phase3_lane_index(
        baseline_root=baseline,
        repo_root=repo,
        output_dir=tmp_path / "out",
        lane_specs=(spec,),
    )
    manifest = json.loads(path.read_text())

    assert manifest["phase3_lanes_ready"] is False
    lane = manifest["lanes"][0]
    assert lane["runner_gate_args_invoked"] is True
    assert lane["runner_required_gate_args"] == {
        "--gate-stage": "post-fix",
        "--baseline-raw-dir": "$BASELINE_RAW_DIR",
        "--output-dir": "$PHASE3_GATE_OUTPUT_DIR",
        "--phase3-manifest": "$PHASE3_MANIFEST_PATH",
        "--phase3-manifest-sha256": "$PHASE3_MANIFEST_SHA256",
    }
    assert lane["runner_gate_args_invalid_mutation_count"] >= 1
    assert "phase3_lane_runner_gate_args_immutable" in manifest["summary"]["failed_kinds"]


@pytest.mark.parametrize(
    "function_definition",
    (
        "mutate_gate_args() { PHASE3_GATE_ARGS=(--gate-stage pre-fix); }",
        "\n".join(
            (
                "mutate_gate_args()",
                "{",
                "    PHASE3_GATE_ARGS=(--gate-stage pre-fix)",
                "}",
            )
        ),
    ),
)
def test_phase3_lane_index_rejects_uncalled_mutating_function_definition_before_validator(
    tmp_path,
    function_definition,
):
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
    runner_path.write_text(
        runner_path.read_text().replace(
            '"$PYTHON_BIN" -m',
            function_definition + '\n"$PYTHON_BIN" -m',
            1,
        )
    )

    path = build_phase3_lane_index(
        baseline_root=baseline,
        repo_root=repo,
        output_dir=tmp_path / "out",
        lane_specs=(spec,),
    )
    manifest = json.loads(path.read_text())

    assert manifest["phase3_lanes_ready"] is False
    lane = manifest["lanes"][0]
    assert lane["runner_gate_args_invoked"] is True
    assert lane["runner_gate_args_invalid_mutation_count"] >= 1
    assert "phase3_lane_runner_gate_args_immutable" in manifest["summary"]["failed_kinds"]


@pytest.mark.parametrize(
    "mutation_lines",
    (
        ("target=PHASE3_GATE_ARGS", "declare target=OTHER", 'unset "$target"'),
        ("target=PHASE3_GATE_ARGS", "typeset target=OTHER", 'unset "$target"'),
        ("target=PHASE3_GATE_ARGS", "readonly target=OTHER", 'unset "$target"'),
        ("target=PHASE3_GATE_ARGS", "export target=OTHER", 'unset "$target"'),
        (
            "target=PHASE3_GATE_ARGS",
            'reset_alias() { local target=OTHER; unset "$target"; }',
            "reset_alias",
        ),
    ),
)
def test_phase3_lane_index_rejects_alias_reassignment_before_indirect_unset(
    tmp_path,
    mutation_lines,
):
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
    runner_path.write_text(
        runner_path.read_text().replace(
            '"$PYTHON_BIN" -m',
            "\n".join(mutation_lines) + '\n"$PYTHON_BIN" -m',
            1,
        )
    )

    path = build_phase3_lane_index(
        baseline_root=baseline,
        repo_root=repo,
        output_dir=tmp_path / "out",
        lane_specs=(spec,),
    )
    manifest = json.loads(path.read_text())

    assert manifest["phase3_lanes_ready"] is False
    lane = manifest["lanes"][0]
    assert lane["runner_gate_args_invoked"] is True
    assert lane["runner_gate_args_invalid_mutation_count"] >= 1
    assert "phase3_lane_runner_gate_args_immutable" in manifest["summary"]["failed_kinds"]


@pytest.mark.parametrize(
    ("mutation_line", "expected_fragment"),
    (
        (
            'if [[ "$PHASE3_REQUIRE_READY" != "0" ]]; then '
            "PHASE3_GATE_ARGS=(--gate-stage pre-fix); fi",
            "PHASE3_GATE_ARGS=(--gate-stage pre-fix)",
        ),
        (
            "true && PHASE3_GATE_ARGS=(--gate-stage pre-fix)",
            "PHASE3_GATE_ARGS=(--gate-stage pre-fix)",
        ),
        (
            "foo; PHASE3_GATE_ARGS=(--gate-stage pre-fix)",
            "PHASE3_GATE_ARGS=(--gate-stage pre-fix)",
        ),
        (
            'case "$PHASE3_REQUIRE_READY" in 1) PHASE3_GATE_ARGS=(--gate-stage pre-fix);; esac',
            "PHASE3_GATE_ARGS=(--gate-stage pre-fix)",
        ),
        (
            'case "$PHASE3_REQUIRE_READY" in 1) unset PHASE3_GATE_ARGS;; esac',
            "unset PHASE3_GATE_ARGS",
        ),
    ),
)
def test_phase3_lane_index_rejects_inline_phase3_gate_args_mutation_before_validator(
    tmp_path,
    mutation_line,
    expected_fragment,
):
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
    runner_path.write_text(
        runner_path.read_text().replace(
            '"$PYTHON_BIN" -m',
            mutation_line + '\n"$PYTHON_BIN" -m',
            1,
        )
    )

    path = build_phase3_lane_index(
        baseline_root=baseline,
        repo_root=repo,
        output_dir=tmp_path / "out",
        lane_specs=(spec,),
    )
    manifest = json.loads(path.read_text())

    assert manifest["phase3_lanes_ready"] is False
    lane = manifest["lanes"][0]
    assert (
        lane["runner_gate_args_invalid_mutation_count"] >= 1
        or lane["runner_gate_args_invoked"] is False
    )
    assert (
        "phase3_lane_runner_gate_args_immutable" in manifest["summary"]["failed_kinds"]
        or "phase3_lane_runner_gate_args_invoked" in manifest["summary"]["failed_kinds"]
    )


def test_phase3_lane_index_rejects_required_gate_args_defined_after_validator_invocation(tmp_path):
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
        include_required_gate_args=False,
    )
    runner_path = repo / spec.runner_relpath
    with runner_path.open("a", encoding="utf-8") as handle:
        handle.write(
            "\n".join(
                [
                    "PHASE3_GATE_ARGS=(",
                    "    --gate-stage post-fix",
                    '    --baseline-raw-dir "$BASELINE_RAW_DIR"',
                    '    --output-dir "$PHASE3_GATE_OUTPUT_DIR"',
                    '    --phase3-manifest "$PHASE3_MANIFEST_PATH"',
                    '    --phase3-manifest-sha256 "$PHASE3_MANIFEST_SHA256"',
                    ")",
                ]
            )
            + "\n"
        )

    path = build_phase3_lane_index(
        baseline_root=baseline,
        repo_root=repo,
        output_dir=tmp_path / "out",
        lane_specs=(spec,),
    )
    manifest = json.loads(path.read_text())

    assert manifest["phase3_lanes_ready"] is False
    lane = manifest["lanes"][0]
    assert lane["runner_gate_args_invoked"] is True
    assert lane["runner_gate_args_assignment_count"] == 0
    assert all(count == 0 for count in lane["runner_required_gate_arg_counts"].values())
    assert "phase3_lane_runner_required_gate_args" in manifest["summary"]["failed_kinds"]


def test_phase3_lane_index_ignores_required_gate_args_in_other_arrays(tmp_path):
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
        include_required_gate_args=False,
    )
    runner_path = repo / spec.runner_relpath
    with runner_path.open("a", encoding="utf-8") as handle:
        handle.write(
            "\n".join(
                [
                    "OTHER_ARGS=(",
                    "    --gate-stage post-fix",
                    '    --baseline-raw-dir "$BASELINE_RAW_DIR"',
                    '    --output-dir "$PHASE3_GATE_OUTPUT_DIR"',
                    '    --phase3-manifest "$PHASE3_MANIFEST_PATH"',
                    '    --phase3-manifest-sha256 "$PHASE3_MANIFEST_SHA256"',
                    ")",
                ]
            )
            + "\n"
        )

    path = build_phase3_lane_index(
        baseline_root=baseline,
        repo_root=repo,
        output_dir=tmp_path / "out",
        lane_specs=(spec,),
    )
    manifest = json.loads(path.read_text())

    assert manifest["phase3_lanes_ready"] is False
    lane = manifest["lanes"][0]
    assert all(count == 0 for count in lane["runner_required_gate_arg_counts"].values())
    assert "phase3_lane_runner_required_gate_args" in manifest["summary"]["failed_kinds"]


def test_phase3_lane_index_ignores_required_gate_args_inside_uncalled_function(tmp_path):
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
        include_required_gate_args=False,
    )
    runner_path = repo / spec.runner_relpath
    with runner_path.open("a", encoding="utf-8") as handle:
        handle.write(
            "\n".join(
                [
                    "unused_gate_args() {",
                    "    PHASE3_GATE_ARGS=(",
                    "        --gate-stage post-fix",
                    '        --baseline-raw-dir "$BASELINE_RAW_DIR"',
                    '        --output-dir "$PHASE3_GATE_OUTPUT_DIR"',
                    '        --phase3-manifest "$PHASE3_MANIFEST_PATH"',
                    '        --phase3-manifest-sha256 "$PHASE3_MANIFEST_SHA256"',
                    "    )",
                    "}",
                ]
            )
            + "\n"
        )

    path = build_phase3_lane_index(
        baseline_root=baseline,
        repo_root=repo,
        output_dir=tmp_path / "out",
        lane_specs=(spec,),
    )
    manifest = json.loads(path.read_text())

    assert manifest["phase3_lanes_ready"] is False
    lane = manifest["lanes"][0]
    assert all(count == 0 for count in lane["runner_required_gate_arg_counts"].values())
    assert "phase3_lane_runner_required_gate_args" in manifest["summary"]["failed_kinds"]


@pytest.mark.parametrize(
    "wrapper_lines",
    (
        (
            "function unused_gate_args {",
            "    PHASE3_GATE_ARGS=(",
            "        --gate-stage post-fix",
            '        --baseline-raw-dir "$BASELINE_RAW_DIR"',
            '        --output-dir "$PHASE3_GATE_OUTPUT_DIR"',
            '        --phase3-manifest "$PHASE3_MANIFEST_PATH"',
            '        --phase3-manifest-sha256 "$PHASE3_MANIFEST_SHA256"',
            "    )",
            "}",
        ),
        (
            "function unused_gate_args { # comment",
            "    PHASE3_GATE_ARGS=(",
            "        --gate-stage post-fix",
            '        --baseline-raw-dir "$BASELINE_RAW_DIR"',
            '        --output-dir "$PHASE3_GATE_OUTPUT_DIR"',
            '        --phase3-manifest "$PHASE3_MANIFEST_PATH"',
            '        --phase3-manifest-sha256 "$PHASE3_MANIFEST_SHA256"',
            "    )",
            "}",
        ),
        (
            "unused_gate_args()",
            "{",
            "    PHASE3_GATE_ARGS=(",
            "        --gate-stage post-fix",
            '        --baseline-raw-dir "$BASELINE_RAW_DIR"',
            '        --output-dir "$PHASE3_GATE_OUTPUT_DIR"',
            '        --phase3-manifest "$PHASE3_MANIFEST_PATH"',
            '        --phase3-manifest-sha256 "$PHASE3_MANIFEST_SHA256"',
            "    )",
            "}",
        ),
        (
            "unused_gate_args() { # comment",
            "    PHASE3_GATE_ARGS=(",
            "        --gate-stage post-fix",
            '        --baseline-raw-dir "$BASELINE_RAW_DIR"',
            '        --output-dir "$PHASE3_GATE_OUTPUT_DIR"',
            '        --phase3-manifest "$PHASE3_MANIFEST_PATH"',
            '        --phase3-manifest-sha256 "$PHASE3_MANIFEST_SHA256"',
            "    )",
            "}",
        ),
        (
            "function unused_gate_args",
            "{",
            "    PHASE3_GATE_ARGS=(",
            "        --gate-stage post-fix",
            '        --baseline-raw-dir "$BASELINE_RAW_DIR"',
            '        --output-dir "$PHASE3_GATE_OUTPUT_DIR"',
            '        --phase3-manifest "$PHASE3_MANIFEST_PATH"',
            '        --phase3-manifest-sha256 "$PHASE3_MANIFEST_SHA256"',
            "    )",
            "}",
        ),
        (
            "if false; then",
            "    PHASE3_GATE_ARGS=(",
            "        --gate-stage post-fix",
            '        --baseline-raw-dir "$BASELINE_RAW_DIR"',
            '        --output-dir "$PHASE3_GATE_OUTPUT_DIR"',
            '        --phase3-manifest "$PHASE3_MANIFEST_PATH"',
            '        --phase3-manifest-sha256 "$PHASE3_MANIFEST_SHA256"',
            "    )",
            "fi",
        ),
        (
            "if false; then # comment",
            "    PHASE3_GATE_ARGS=(",
            "        --gate-stage post-fix",
            '        --baseline-raw-dir "$BASELINE_RAW_DIR"',
            '        --output-dir "$PHASE3_GATE_OUTPUT_DIR"',
            '        --phase3-manifest "$PHASE3_MANIFEST_PATH"',
            '        --phase3-manifest-sha256 "$PHASE3_MANIFEST_SHA256"',
            "    )",
            "fi",
        ),
        (
            "if false",
            "then",
            "    PHASE3_GATE_ARGS=(",
            "        --gate-stage post-fix",
            '        --baseline-raw-dir "$BASELINE_RAW_DIR"',
            '        --output-dir "$PHASE3_GATE_OUTPUT_DIR"',
            '        --phase3-manifest "$PHASE3_MANIFEST_PATH"',
            '        --phase3-manifest-sha256 "$PHASE3_MANIFEST_SHA256"',
            "    )",
            "fi",
        ),
        (
            "(",
            "    PHASE3_GATE_ARGS=(",
            "        --gate-stage post-fix",
            '        --baseline-raw-dir "$BASELINE_RAW_DIR"',
            '        --output-dir "$PHASE3_GATE_OUTPUT_DIR"',
            '        --phase3-manifest "$PHASE3_MANIFEST_PATH"',
            '        --phase3-manifest-sha256 "$PHASE3_MANIFEST_SHA256"',
            "    )",
            ")",
        ),
        (
            "{",
            "    PHASE3_GATE_ARGS=(",
            "        --gate-stage post-fix",
            '        --baseline-raw-dir "$BASELINE_RAW_DIR"',
            '        --output-dir "$PHASE3_GATE_OUTPUT_DIR"',
            '        --phase3-manifest "$PHASE3_MANIFEST_PATH"',
            '        --phase3-manifest-sha256 "$PHASE3_MANIFEST_SHA256"',
            "    )",
            "}",
        ),
    ),
)
def test_phase3_lane_index_ignores_required_gate_args_inside_uncalled_shell_scopes(
    tmp_path,
    wrapper_lines,
):
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
        include_required_gate_args=False,
    )
    runner_path = repo / spec.runner_relpath
    with runner_path.open("a", encoding="utf-8") as handle:
        handle.write("\n".join(wrapper_lines) + "\n")

    path = build_phase3_lane_index(
        baseline_root=baseline,
        repo_root=repo,
        output_dir=tmp_path / "out",
        lane_specs=(spec,),
    )
    manifest = json.loads(path.read_text())

    assert manifest["phase3_lanes_ready"] is False
    lane = manifest["lanes"][0]
    assert all(count == 0 for count in lane["runner_required_gate_arg_counts"].values())
    assert "phase3_lane_runner_required_gate_args" in manifest["summary"]["failed_kinds"]


def test_phase3_lane_index_rejects_duplicate_runner_gate_validator_invocations(tmp_path):
    baseline = tmp_path / "baseline"
    repo = tmp_path / "repo"
    _write_baseline(baseline)
    expected_module = "scripts.function_tracer_pcode.validation.phase3_expected_lane"
    spec = Phase3LaneSpec(
        lane_number=1,
        lane_id="runner_safety_lane",
        target_reason_ids=("reason_one",),
        manifest_relpath="audit/runner_safety_lane/manifest.json",
        runner_relpath="run_runner_safety_lane.sh",
        manifest_kind="runner_safety_lane_manifest",
        ready_key="runner_safety_lane_ready",
        gate_validator_module=expected_module,
        require_runner_safety_defaults=True,
    )
    _write_manifest(baseline, spec)
    _write_runner(
        repo,
        spec,
        safety_defaults=_safety_defaults(),
        require_ready_arg=True,
        invoke_gate_args=True,
        gate_validator_module=expected_module,
    )
    runner_path = repo / spec.runner_relpath
    with runner_path.open("a", encoding="utf-8") as handle:
        handle.write(f'"$PYTHON_BIN" -m {expected_module} "${{PHASE3_GATE_ARGS[@]}}"\n')

    path = build_phase3_lane_index(
        baseline_root=baseline,
        repo_root=repo,
        output_dir=tmp_path / "out",
        lane_specs=(spec,),
    )
    manifest = json.loads(path.read_text())

    assert manifest["phase3_lanes_ready"] is False
    lane = manifest["lanes"][0]
    assert lane["runner_gate_args_invoked"] is False
    assert lane["runner_gate_validator_invocation_count"] == 2
    expected_invocation = _expected_runner_safety_gate_smoke_argv()
    expected_invocation[1] = expected_module
    assert lane["runner_gate_smoke_expected_argv"] == []
    assert lane["runner_gate_smoke_failure_kind"] == "validator_invocation_count"
    assert lane["runner_gate_smoke_observed_argv"] == expected_invocation
    assert lane["runner_gate_smoke_observed_invocations"] == [
        expected_invocation,
        expected_invocation,
    ]
    assert "phase3_lane_runner_gate_args_invoked" in manifest["summary"]["failed_kinds"]


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
    "fake_command",
    (
        'echo \'"$PYTHON_BIN" -m scripts.function_tracer_pcode.validation.fake "${PHASE3_GATE_ARGS[@]}"\'',
        'GATE_CALL=\'"$PYTHON_BIN" -m scripts.function_tracer_pcode.validation.fake "${PHASE3_GATE_ARGS[@]}"\'',
    ),
)
def test_phase3_lane_index_rejects_non_executed_gate_arg_strings_before_valid_validator(
    tmp_path,
    fake_command,
):
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
    _write_runner(repo, spec, safety_defaults=_safety_defaults(), require_ready_arg=True, invoke_gate_args=True)
    runner_path = repo / spec.runner_relpath
    runner_path.write_text(
        runner_path.read_text().replace(
            '"$PYTHON_BIN" -m',
            fake_command + '\n"$PYTHON_BIN" -m',
            1,
        )
    )

    path = build_phase3_lane_index(
        baseline_root=baseline,
        repo_root=repo,
        output_dir=tmp_path / "out",
        lane_specs=(spec,),
    )
    manifest = json.loads(path.read_text())

    assert manifest["phase3_lanes_ready"] is False
    lane = manifest["lanes"][0]
    assert lane["runner_gate_args_invoked"] is True
    assert lane["runner_gate_args_assignment_count"] == 1
    assert lane["runner_gate_args_invalid_mutation_count"] >= 1
    assert "phase3_lane_runner_gate_args_immutable" in manifest["summary"]["failed_kinds"]


@pytest.mark.parametrize(
    "side_effect_line",
    (
        'echo "$((PHASE3_GATE_ARGS[1]=0))"',
        'GATE_CALL="$((PHASE3_GATE_ARGS[1]=0))"',
    ),
)
def test_phase3_lane_index_rejects_side_effect_gate_arg_expansions_before_validator(
    tmp_path,
    side_effect_line,
):
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
    _write_runner(repo, spec, safety_defaults=_safety_defaults(), require_ready_arg=True, invoke_gate_args=True)
    runner_path = repo / spec.runner_relpath
    runner_path.write_text(
        runner_path.read_text().replace(
            '"$PYTHON_BIN" -m',
            side_effect_line + '\n"$PYTHON_BIN" -m',
            1,
        )
    )

    path = build_phase3_lane_index(
        baseline_root=baseline,
        repo_root=repo,
        output_dir=tmp_path / "out",
        lane_specs=(spec,),
    )
    manifest = json.loads(path.read_text())

    assert manifest["phase3_lanes_ready"] is False
    lane = manifest["lanes"][0]
    assert lane["runner_gate_args_invoked"] is True
    assert lane["runner_gate_args_invalid_mutation_count"] >= 1
    assert "phase3_lane_runner_gate_args_immutable" in manifest["summary"]["failed_kinds"]


@pytest.mark.parametrize(
    "wrapper_lines",
    (
        (
            'unused_gate() { "$PYTHON_BIN" -m scripts.function_tracer_pcode.validation.fake '
            '"${PHASE3_GATE_ARGS[@]}"; }',
        ),
        (
            'if false; then "$PYTHON_BIN" -m scripts.function_tracer_pcode.validation.fake '
            '"${PHASE3_GATE_ARGS[@]}"; fi',
        ),
        (
            "unused_gate()",
            "{",
            '"$PYTHON_BIN" -m scripts.function_tracer_pcode.validation.fake "${PHASE3_GATE_ARGS[@]}"',
            "}",
        ),
        (
            "function unused_gate",
            "{",
            '"$PYTHON_BIN" -m scripts.function_tracer_pcode.validation.fake "${PHASE3_GATE_ARGS[@]}"',
            "}",
        ),
    ),
)
def test_phase3_lane_index_rejects_gate_invocation_inside_uncalled_shell_scopes(
    tmp_path,
    wrapper_lines,
):
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
        handle.write("\n".join(wrapper_lines) + "\n")

    path = build_phase3_lane_index(
        baseline_root=baseline,
        repo_root=repo,
        output_dir=tmp_path / "out",
        lane_specs=(spec,),
    )
    manifest = json.loads(path.read_text())

    assert manifest["phase3_lanes_ready"] is False
    lane = manifest["lanes"][0]
    assert lane["runner_gate_args_invoked"] is False
    assert lane["runner_gate_validator_invocation_count"] == 0
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
        current_log_root_category=target_category,
        baseline_log_root_category=target_category,
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
        current_log_root_category=target_category,
        baseline_log_root_category=target_category,
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
        current_log_root_category=target_category,
        baseline_log_root_category=target_category,
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


@pytest.mark.parametrize(
    ("target_category", "current_log_root_category"),
    (
        ("function_call", "loop"),
        ("loop", "function_call"),
    ),
)
def test_phase3_lane_index_rejects_runner_current_log_root_category_mismatch(
    tmp_path,
    target_category,
    current_log_root_category,
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
        current_log_root_category=current_log_root_category,
        baseline_log_root_category=target_category,
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
    assert "phase3_lane_runner_current_log_root" in manifest["summary"]["failed_kinds"]
    assert "phase3_lane_runner_baseline_log_root" not in manifest["summary"]["failed_kinds"]
    assert "phase3_lane_runner_target_set" not in manifest["summary"]["failed_kinds"]
    assert "phase3_lane_runner_pair_filter" not in manifest["summary"]["failed_kinds"]


@pytest.mark.parametrize(
    ("target_category", "baseline_log_root_category", "baseline_log_root_var_category"),
    (
        ("function_call", "function_call", "loop"),
        ("loop", "function_call", "loop"),
    ),
)
def test_phase3_lane_index_rejects_runner_baseline_log_root_category_or_var_mismatch(
    tmp_path,
    target_category,
    baseline_log_root_category,
    baseline_log_root_var_category,
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
        current_log_root_category=target_category,
        baseline_log_root_category=baseline_log_root_category,
        baseline_log_root_var_category=baseline_log_root_var_category,
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
    assert "phase3_lane_runner_baseline_log_root" in manifest["summary"]["failed_kinds"]
    assert "phase3_lane_runner_current_log_root" not in manifest["summary"]["failed_kinds"]
    assert "phase3_lane_runner_target_set" not in manifest["summary"]["failed_kinds"]
    assert "phase3_lane_runner_pair_filter" not in manifest["summary"]["failed_kinds"]


def test_phase3_lane_index_rejects_runner_duplicate_or_invalid_extra_log_root_args(tmp_path):
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
    _write_manifest(baseline, spec, category="function_call")
    _write_runner(
        repo,
        spec,
        target_category="function_call",
        current_log_root_category="function_call",
        baseline_log_root_category="function_call",
        target_functions=("runner_target_lane_function",),
        pair_filter=("runner_target_lane_function:B1_B2",),
    )
    runner_path = repo / spec.runner_relpath
    with runner_path.open("a", encoding="utf-8") as handle:
        handle.write('    --current-log-root "function_call=$OTHER_OUTPUT_BASE_DIR"\n')

    path = build_phase3_lane_index(
        baseline_root=baseline,
        repo_root=repo,
        output_dir=tmp_path / "out",
        lane_specs=(spec,),
    )
    manifest = json.loads(path.read_text())

    assert manifest["phase3_lanes_ready"] is False
    assert manifest["lanes"][0]["runner_log_root_arg_counts"] == {
        "current_log_root": 2,
        "baseline_log_root": 1,
    }
    assert "phase3_lane_runner_log_root_args_unique" in manifest["summary"]["failed_kinds"]


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
    validate_phase3_lane_index(manifest, lane_specs=(spec,))


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
    assert manifest["summary"]["failed_kind_counts"]["baseline_id"] == 1
    assert manifest["summary"]["failed_index_kinds"] == ["baseline_id"]


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
