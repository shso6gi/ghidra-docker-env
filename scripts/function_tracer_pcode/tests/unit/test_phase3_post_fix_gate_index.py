# -*- coding: utf-8 -*-

import json
from pathlib import Path

import pytest

from scripts.function_tracer_pcode.validation import phase3_lane_index
from scripts.function_tracer_pcode.validation.phase3_post_fix_gate_index import (
    Phase3PostFixGateSpec,
    build_phase3_post_fix_gate_index,
    validate_phase3_post_fix_gate_index,
)


def _validator(manifest):
    if manifest.get("ready") is not True:
        raise ValueError("gate is not ready")


def _spec(lane_number: int, lane_id: str) -> Phase3PostFixGateSpec:
    return Phase3PostFixGateSpec(
        lane_number=lane_number,
        lane_id=lane_id,
        gate_relpath=f"logs/{lane_id}/gate.json",
        manifest_kind=f"{lane_id}_post_fix_gate",
        ready_key="ready",
        validator=_validator,
        expected_entry_count=1,
        allowed_post_fix_statuses=("completed_recovery", "pending_proof"),
    )


def _write_gate(
    repo: Path,
    spec: Phase3PostFixGateSpec,
    *,
    ready=True,
    summary_failed=None,
    summary_failed_kinds=None,
    post_fix_status="pending_proof",
    manifest_kind=None,
    artifact_role="derived_audit_post_fix_gate",
    baseline_id="observed-v0@0a53352",
    baseline_git_head=phase3_lane_index.BASELINE_GIT_HEAD,
    omit_pending_obligations=False,
    pending_obligation_updates=None,
    include_required_completion_actions=True,
    omit_required_completion_actions=False,
    required_action_updates=None,
) -> None:
    path = repo / spec.gate_relpath
    path.parent.mkdir(parents=True, exist_ok=True)
    entry = {"id": f"{spec.lane_id}-entry", "post_fix_status": post_fix_status}
    obligation = None
    if not omit_pending_obligations and post_fix_status in {"pending_proof", "pending_retry"}:
        obligation = {
            "reason_id": "reason_one",
            "proof_kind": "proof_kind_one",
            "proof_stage": "proof_stage_one",
            "evidence_kind": "evidence_kind_one",
            "required_evidence": ["evidence_kind_one"],
            "proof_obligation_id": ["proof", spec.lane_id, "proof_stage_one"],
            "completed_evidence_present": False,
            "status": "pending_evidence" if post_fix_status == "pending_proof" else "pending_retry",
        }
        obligation.update(pending_obligation_updates or {})
        if post_fix_status == "pending_proof":
            entry["pending_proof_obligations"] = [obligation]
        else:
            entry["pending_retry_obligations"] = [obligation]
    if (
        include_required_completion_actions
        and not omit_required_completion_actions
        and obligation is not None
    ):
        required_action = {
            key: obligation[key]
            for key in (
                "reason_id",
                "proof_kind",
                "proof_stage",
                "evidence_kind",
                "required_evidence",
                "proof_obligation_id",
            )
        }
        required_action.update(required_action_updates or {})
        entry["required_completion_actions"] = [required_action]
    path.write_text(
        json.dumps(
            {
                "manifest_version": 1,
                "manifest_kind": manifest_kind or spec.manifest_kind,
                "artifact_role": artifact_role,
                "baseline_id": baseline_id,
                "baseline_git_head": baseline_git_head,
                spec.ready_key: ready,
                "post_fix_regression_gate": {
                    "summary": {
                        "failed": (
                            summary_failed
                            if summary_failed is not None
                            else (0 if ready else 1)
                        ),
                        "failed_kinds": (
                            summary_failed_kinds
                            if summary_failed_kinds is not None
                            else ([] if ready else ["unit_failure"])
                        ),
                    }
                },
                "entries": [entry],
            },
            sort_keys=True,
        )
    )


def test_phase3_post_fix_gate_index_accepts_ready_gates(tmp_path):
    repo = tmp_path / "repo"
    specs = (_spec(1, "lane_one"), _spec(2, "lane_two"))
    for spec in specs:
        _write_gate(repo, spec)

    path = build_phase3_post_fix_gate_index(
        repo_root=repo,
        output_dir=tmp_path / "out",
        gate_specs=specs,
    )
    manifest = json.loads(path.read_text())

    assert manifest["phase3_post_fix_gates_ready"] is True
    assert manifest["summary"]["failed"] == 0
    assert [gate["lane_id"] for gate in manifest["gates"]] == ["lane_one", "lane_two"]
    validate_phase3_post_fix_gate_index(manifest, repo_root=repo, gate_specs=specs)


def test_phase3_post_fix_gate_index_summarizes_post_fix_status_counts(tmp_path):
    repo = tmp_path / "repo"
    specs = (_spec(1, "lane_one"), _spec(2, "lane_two"))
    _write_gate(repo, specs[0], post_fix_status="pending_proof")
    _write_gate(repo, specs[1], post_fix_status="completed_recovery")

    path = build_phase3_post_fix_gate_index(
        repo_root=repo,
        output_dir=tmp_path / "out",
        gate_specs=specs,
    )
    manifest = json.loads(path.read_text())

    assert manifest["post_fix_status_counts"] == {
        "completed_recovery": 1,
        "pending_proof": 1,
    }
    assert manifest["gates"][0]["post_fix_status_counts"] == {"pending_proof": 1}
    assert manifest["gates"][1]["post_fix_status_counts"] == {"completed_recovery": 1}
    validate_phase3_post_fix_gate_index(manifest, repo_root=repo, gate_specs=specs)


def test_phase3_post_fix_gate_index_accepts_expected_status_distribution(tmp_path):
    repo = tmp_path / "repo"
    spec = Phase3PostFixGateSpec(
        lane_number=1,
        lane_id="lane_one",
        gate_relpath="logs/lane_one/gate.json",
        manifest_kind="lane_one_post_fix_gate",
        ready_key="ready",
        validator=_validator,
        expected_entry_count=2,
        allowed_post_fix_statuses=("completed_recovery", "pending_proof"),
        expected_post_fix_status_counts={"completed_recovery": 1, "pending_proof": 1},
    )
    _write_gate(repo, spec, post_fix_status="pending_proof")
    gate_path = repo / spec.gate_relpath
    gate = json.loads(gate_path.read_text())
    gate["entries"].append(
        {
            "id": "lane_one-completed",
            "post_fix_status": "completed_recovery",
        }
    )
    gate_path.write_text(json.dumps(gate, sort_keys=True))

    path = build_phase3_post_fix_gate_index(
        repo_root=repo,
        output_dir=tmp_path / "out",
        gate_specs=(spec,),
    )
    manifest = json.loads(path.read_text())

    assert manifest["phase3_post_fix_gates_ready"] is True
    assert manifest["expected_post_fix_status_counts"] == {
        "completed_recovery": 1,
        "pending_proof": 1,
    }
    assert manifest["gates"][0]["expected_post_fix_status_counts"] == {
        "completed_recovery": 1,
        "pending_proof": 1,
    }
    assert manifest["gates"][0]["post_fix_status_counts"] == {
        "completed_recovery": 1,
        "pending_proof": 1,
    }
    validate_phase3_post_fix_gate_index(manifest, repo_root=repo, gate_specs=(spec,))


def test_phase3_post_fix_gate_index_rejects_allowed_status_distribution_drift(tmp_path):
    repo = tmp_path / "repo"
    spec = Phase3PostFixGateSpec(
        lane_number=1,
        lane_id="lane_one",
        gate_relpath="logs/lane_one/gate.json",
        manifest_kind="lane_one_post_fix_gate",
        ready_key="ready",
        validator=_validator,
        expected_entry_count=2,
        allowed_post_fix_statuses=("completed_recovery", "pending_proof"),
        expected_post_fix_status_counts={"completed_recovery": 1, "pending_proof": 1},
    )
    _write_gate(repo, spec, post_fix_status="pending_proof")
    gate_path = repo / spec.gate_relpath
    gate = json.loads(gate_path.read_text())
    second_entry = dict(gate["entries"][0])
    second_entry["id"] = "lane_one-second-pending-proof"
    gate["entries"].append(second_entry)
    gate_path.write_text(json.dumps(gate, sort_keys=True))

    path = build_phase3_post_fix_gate_index(
        repo_root=repo,
        output_dir=tmp_path / "out",
        gate_specs=(spec,),
    )
    manifest = json.loads(path.read_text())

    assert manifest["phase3_post_fix_gates_ready"] is False
    assert manifest["gates"][0]["post_fix_status_counts"] == {"pending_proof": 2}
    assert "phase3_post_fix_gate_status_counts_expected" in manifest["summary"]["failed_kinds"]
    assert (
        "phase3_post_fix_gate_status_counts_global_expected"
        in manifest["summary"]["failed_kinds"]
    )
    with pytest.raises(ValueError, match="phase3_post_fix_gate_status_counts_expected"):
        validate_phase3_post_fix_gate_index(manifest, repo_root=repo, gate_specs=(spec,))


def test_phase3_post_fix_gate_index_rejects_tampered_expected_status_counts(tmp_path):
    repo = tmp_path / "repo"
    spec = Phase3PostFixGateSpec(
        lane_number=1,
        lane_id="lane_one",
        gate_relpath="logs/lane_one/gate.json",
        manifest_kind="lane_one_post_fix_gate",
        ready_key="ready",
        validator=_validator,
        expected_entry_count=1,
        allowed_post_fix_statuses=("pending_proof",),
        expected_post_fix_status_counts={"pending_proof": 1},
    )
    _write_gate(repo, spec, post_fix_status="pending_proof")
    path = build_phase3_post_fix_gate_index(
        repo_root=repo,
        output_dir=tmp_path / "out",
        gate_specs=(spec,),
    )
    manifest = json.loads(path.read_text())
    manifest["expected_post_fix_status_counts"] = {}

    with pytest.raises(ValueError, match="expected_post_fix_status_counts"):
        validate_phase3_post_fix_gate_index(manifest, repo_root=repo, gate_specs=(spec,))


def test_phase3_post_fix_gate_index_rejects_tampered_status_counts(tmp_path):
    repo = tmp_path / "repo"
    specs = (_spec(1, "lane_one"),)
    _write_gate(repo, specs[0], post_fix_status="pending_proof")
    path = build_phase3_post_fix_gate_index(
        repo_root=repo,
        output_dir=tmp_path / "out",
        gate_specs=specs,
    )
    manifest = json.loads(path.read_text())
    manifest["post_fix_status_counts"] = {}

    with pytest.raises(ValueError, match="post_fix_status_counts"):
        validate_phase3_post_fix_gate_index(manifest, repo_root=repo, gate_specs=specs)


def test_phase3_post_fix_gate_index_rejects_missing_gate(tmp_path):
    repo = tmp_path / "repo"
    specs = (_spec(1, "lane_one"),)

    path = build_phase3_post_fix_gate_index(
        repo_root=repo,
        output_dir=tmp_path / "out",
        gate_specs=specs,
    )
    manifest = json.loads(path.read_text())

    assert manifest["phase3_post_fix_gates_ready"] is False
    assert "phase3_post_fix_gate_present" in manifest["summary"]["failed_kinds"]
    with pytest.raises(ValueError, match="phase3_post_fix_gate_present"):
        validate_phase3_post_fix_gate_index(manifest, repo_root=repo, gate_specs=specs)


def test_phase3_post_fix_gate_index_rejects_non_mapping_gate_payload(tmp_path):
    repo = tmp_path / "repo"
    specs = (_spec(1, "lane_one"),)
    path = repo / specs[0].gate_relpath
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(["not", "a", "gate"]))

    index_path = build_phase3_post_fix_gate_index(
        repo_root=repo,
        output_dir=tmp_path / "out",
        gate_specs=specs,
    )
    manifest = json.loads(index_path.read_text())
    gate = manifest["gates"][0]

    assert manifest["phase3_post_fix_gates_ready"] is False
    assert gate["status"] == "invalid_payload"
    assert gate["validator_status"] == "failed"
    assert "gate payload must be an object" in gate["validator_error"]
    with pytest.raises(ValueError, match="phase3_post_fix_gate_present"):
        validate_phase3_post_fix_gate_index(manifest, repo_root=repo, gate_specs=specs)


def test_phase3_post_fix_gate_index_records_validator_exception(tmp_path):
    def exploding_validator(_manifest):
        raise RuntimeError("validator crashed")

    repo = tmp_path / "repo"
    spec = Phase3PostFixGateSpec(
        lane_number=1,
        lane_id="lane_one",
        gate_relpath="logs/lane_one/gate.json",
        manifest_kind="lane_one_post_fix_gate",
        ready_key="ready",
        validator=exploding_validator,
    )
    _write_gate(repo, spec)

    path = build_phase3_post_fix_gate_index(
        repo_root=repo,
        output_dir=tmp_path / "out",
        gate_specs=(spec,),
    )
    manifest = json.loads(path.read_text())
    gate = manifest["gates"][0]

    assert manifest["phase3_post_fix_gates_ready"] is False
    assert gate["validator_status"] == "failed"
    assert gate["validator_error"] == "RuntimeError: validator crashed"
    assert "phase3_post_fix_gate_validator" in manifest["summary"]["failed_kinds"]
    with pytest.raises(ValueError, match="phase3_post_fix_gate_validator"):
        validate_phase3_post_fix_gate_index(manifest, repo_root=repo, gate_specs=(spec,))


def test_phase3_post_fix_gate_index_recomputes_tampered_ready_value(tmp_path):
    repo = tmp_path / "repo"
    specs = (_spec(1, "lane_one"),)
    _write_gate(repo, specs[0])
    path = build_phase3_post_fix_gate_index(
        repo_root=repo,
        output_dir=tmp_path / "out",
        gate_specs=specs,
    )
    manifest = json.loads(path.read_text())
    manifest["gates"][0]["ready_value"] = False

    with pytest.raises(ValueError, match="derived_failed_kinds"):
        validate_phase3_post_fix_gate_index(manifest, repo_root=repo, gate_specs=specs)


def test_phase3_post_fix_gate_index_rejects_hidden_check_list(tmp_path):
    repo = tmp_path / "repo"
    specs = (_spec(1, "lane_one"),)
    _write_gate(repo, specs[0])
    path = build_phase3_post_fix_gate_index(
        repo_root=repo,
        output_dir=tmp_path / "out",
        gate_specs=specs,
    )
    manifest = json.loads(path.read_text())
    manifest["checks"] = []
    manifest["summary"] = {
        "total": 0,
        "failed": 0,
        "failed_kinds": [],
        "failed_kind_counts": {},
        "failed_lanes": [],
        "failed_index_kinds": [],
    }

    with pytest.raises(ValueError, match="derived_checks"):
        validate_phase3_post_fix_gate_index(manifest, repo_root=repo, gate_specs=specs)


def test_phase3_post_fix_gate_index_rejects_tampered_summary_counts(tmp_path):
    repo = tmp_path / "repo"
    specs = (_spec(1, "lane_one"),)
    _write_gate(repo, specs[0])
    path = build_phase3_post_fix_gate_index(
        repo_root=repo,
        output_dir=tmp_path / "out",
        gate_specs=specs,
    )
    manifest = json.loads(path.read_text())
    manifest["summary"]["total"] = 0

    with pytest.raises(ValueError, match="summary_consistency"):
        validate_phase3_post_fix_gate_index(manifest, repo_root=repo, gate_specs=specs)


def test_phase3_post_fix_gate_index_rejects_deleted_gate_after_index_build(tmp_path):
    repo = tmp_path / "repo"
    specs = (_spec(1, "lane_one"),)
    _write_gate(repo, specs[0])
    path = build_phase3_post_fix_gate_index(
        repo_root=repo,
        output_dir=tmp_path / "out",
        gate_specs=specs,
    )
    manifest = json.loads(path.read_text())
    (repo / specs[0].gate_relpath).unlink()

    with pytest.raises(ValueError, match="materialized_gates"):
        validate_phase3_post_fix_gate_index(manifest, repo_root=repo, gate_specs=specs)


def test_phase3_post_fix_gate_index_rejects_gate_baseline_head_drift(tmp_path):
    repo = tmp_path / "repo"
    specs = (_spec(1, "lane_one"),)
    _write_gate(repo, specs[0], baseline_git_head="wrong-head")

    path = build_phase3_post_fix_gate_index(
        repo_root=repo,
        output_dir=tmp_path / "out",
        gate_specs=specs,
    )
    manifest = json.loads(path.read_text())

    assert manifest["phase3_post_fix_gates_ready"] is False
    assert "phase3_post_fix_gate_baseline_git_head" in manifest["summary"]["failed_kinds"]
    with pytest.raises(ValueError, match="phase3_post_fix_gate_baseline_git_head"):
        validate_phase3_post_fix_gate_index(manifest, repo_root=repo, gate_specs=specs)


def test_phase3_post_fix_gate_index_rejects_gate_summary_failure(tmp_path):
    repo = tmp_path / "repo"
    specs = (_spec(1, "lane_one"),)
    _write_gate(
        repo,
        specs[0],
        summary_failed=1,
        summary_failed_kinds=["hidden_post_fix_failure"],
    )

    path = build_phase3_post_fix_gate_index(
        repo_root=repo,
        output_dir=tmp_path / "out",
        gate_specs=specs,
    )
    manifest = json.loads(path.read_text())

    assert manifest["phase3_post_fix_gates_ready"] is False
    assert "phase3_post_fix_gate_summary_clean" in manifest["summary"]["failed_kinds"]
    with pytest.raises(ValueError, match="phase3_post_fix_gate_summary_clean"):
        validate_phase3_post_fix_gate_index(manifest, repo_root=repo, gate_specs=specs)


def test_phase3_post_fix_gate_index_rejects_hidden_gate_entries(tmp_path):
    repo = tmp_path / "repo"
    specs = (_spec(1, "lane_one"),)
    _write_gate(repo, specs[0])
    gate_path = repo / specs[0].gate_relpath
    gate = json.loads(gate_path.read_text())
    gate["entries"] = []
    gate_path.write_text(json.dumps(gate, sort_keys=True))

    path = build_phase3_post_fix_gate_index(
        repo_root=repo,
        output_dir=tmp_path / "out",
        gate_specs=specs,
    )
    manifest = json.loads(path.read_text())

    assert manifest["phase3_post_fix_gates_ready"] is False
    assert manifest["gates"][0]["entry_count"] == 0
    assert "phase3_post_fix_gate_entry_count" in manifest["summary"]["failed_kinds"]
    with pytest.raises(ValueError, match="phase3_post_fix_gate_entry_count"):
        validate_phase3_post_fix_gate_index(manifest, repo_root=repo, gate_specs=specs)


def test_phase3_post_fix_gate_index_rejects_entries_without_status(tmp_path):
    repo = tmp_path / "repo"
    specs = (_spec(1, "lane_one"),)
    _write_gate(repo, specs[0])
    gate_path = repo / specs[0].gate_relpath
    gate = json.loads(gate_path.read_text())
    gate["entries"] = [{}]
    gate_path.write_text(json.dumps(gate, sort_keys=True))

    path = build_phase3_post_fix_gate_index(
        repo_root=repo,
        output_dir=tmp_path / "out",
        gate_specs=specs,
    )
    manifest = json.loads(path.read_text())

    assert manifest["phase3_post_fix_gates_ready"] is False
    assert manifest["gates"][0]["entry_count"] == 1
    assert manifest["gates"][0]["post_fix_status_counts"] == {}
    assert "phase3_post_fix_gate_status_count_complete" in manifest["summary"]["failed_kinds"]
    with pytest.raises(ValueError, match="phase3_post_fix_gate_status_count_complete"):
        validate_phase3_post_fix_gate_index(manifest, repo_root=repo, gate_specs=specs)


def test_phase3_post_fix_gate_index_rejects_unexpected_post_fix_status(tmp_path):
    repo = tmp_path / "repo"
    specs = (_spec(1, "lane_one"),)
    _write_gate(repo, specs[0], post_fix_status="forged_ready")

    path = build_phase3_post_fix_gate_index(
        repo_root=repo,
        output_dir=tmp_path / "out",
        gate_specs=specs,
    )
    manifest = json.loads(path.read_text())

    assert manifest["phase3_post_fix_gates_ready"] is False
    assert manifest["post_fix_status_counts"] == {"forged_ready": 1}
    assert "phase3_post_fix_gate_status_allowed" in manifest["summary"]["failed_kinds"]
    with pytest.raises(ValueError, match="phase3_post_fix_gate_status_allowed"):
        validate_phase3_post_fix_gate_index(manifest, repo_root=repo, gate_specs=specs)


def test_phase3_post_fix_gate_index_rejects_pending_proof_without_obligations(tmp_path):
    repo = tmp_path / "repo"
    specs = (_spec(1, "lane_one"),)
    _write_gate(repo, specs[0], post_fix_status="pending_proof", omit_pending_obligations=True)

    path = build_phase3_post_fix_gate_index(
        repo_root=repo,
        output_dir=tmp_path / "out",
        gate_specs=specs,
    )
    manifest = json.loads(path.read_text())

    assert manifest["phase3_post_fix_gates_ready"] is False
    gate = manifest["gates"][0]
    assert gate["post_fix_obligation_summary"]["pending_proof_entry_count"] == 1
    assert gate["post_fix_obligation_summary"]["pending_proof_obligation_count"] == 0
    assert gate["post_fix_obligation_summary"]["pending_proof_entries_missing_obligations"] == [
        "lane_one-entry"
    ]
    assert "phase3_post_fix_gate_pending_obligations_present" in manifest["summary"]["failed_kinds"]
    with pytest.raises(ValueError, match="phase3_post_fix_gate_pending_obligations_present"):
        validate_phase3_post_fix_gate_index(manifest, repo_root=repo, gate_specs=specs)


def test_phase3_post_fix_gate_index_rejects_pending_retry_without_obligations(tmp_path):
    repo = tmp_path / "repo"
    spec = Phase3PostFixGateSpec(
        lane_number=9,
        lane_id="lane_retry",
        gate_relpath="logs/lane_retry/gate.json",
        manifest_kind="lane_retry_post_fix_gate",
        ready_key="ready",
        validator=_validator,
        expected_entry_count=1,
        allowed_post_fix_statuses=("pending_retry",),
    )
    _write_gate(repo, spec, post_fix_status="pending_retry", omit_pending_obligations=True)

    path = build_phase3_post_fix_gate_index(
        repo_root=repo,
        output_dir=tmp_path / "out",
        gate_specs=(spec,),
    )
    manifest = json.loads(path.read_text())

    assert manifest["phase3_post_fix_gates_ready"] is False
    gate = manifest["gates"][0]
    assert gate["post_fix_obligation_summary"]["pending_retry_entry_count"] == 1
    assert gate["post_fix_obligation_summary"]["pending_retry_obligation_count"] == 0
    assert gate["post_fix_obligation_summary"]["pending_retry_entries_missing_obligations"] == [
        "lane_retry-entry"
    ]
    assert "phase3_post_fix_gate_pending_obligations_present" in manifest["summary"]["failed_kinds"]
    with pytest.raises(ValueError, match="phase3_post_fix_gate_pending_obligations_present"):
        validate_phase3_post_fix_gate_index(manifest, repo_root=repo, gate_specs=(spec,))


def test_phase3_post_fix_gate_index_rejects_malformed_pending_obligation(tmp_path):
    repo = tmp_path / "repo"
    specs = (_spec(1, "lane_one"),)
    _write_gate(
        repo,
        specs[0],
        post_fix_status="pending_proof",
        pending_obligation_updates={"proof_obligation_id": ["proof", "<missing>"]},
    )

    path = build_phase3_post_fix_gate_index(
        repo_root=repo,
        output_dir=tmp_path / "out",
        gate_specs=specs,
    )
    manifest = json.loads(path.read_text())

    assert manifest["phase3_post_fix_gates_ready"] is False
    invalid = manifest["gates"][0]["post_fix_obligation_summary"]["pending_proof_invalid_obligations"]
    assert invalid == [{"entry_id": "lane_one-entry", "obligation_index": 0}]
    assert "phase3_post_fix_gate_pending_obligations_present" in manifest["summary"]["failed_kinds"]
    with pytest.raises(ValueError, match="phase3_post_fix_gate_pending_obligations_present"):
        validate_phase3_post_fix_gate_index(manifest, repo_root=repo, gate_specs=specs)


def test_phase3_post_fix_gate_index_rejects_pending_obligation_required_action_mismatch(tmp_path):
    repo = tmp_path / "repo"
    specs = (_spec(1, "lane_one"),)
    _write_gate(
        repo,
        specs[0],
        post_fix_status="pending_proof",
        include_required_completion_actions=True,
        required_action_updates={"proof_obligation_id": ["proof", "lane_one", "different"]},
    )

    path = build_phase3_post_fix_gate_index(
        repo_root=repo,
        output_dir=tmp_path / "out",
        gate_specs=specs,
    )
    manifest = json.loads(path.read_text())

    assert manifest["phase3_post_fix_gates_ready"] is False
    mismatches = manifest["gates"][0]["post_fix_obligation_summary"][
        "pending_proof_required_action_mismatches"
    ]
    assert len(mismatches) == 1
    assert mismatches[0]["entry_id"] == "lane_one-entry"
    assert mismatches[0]["missing_required_actions"]
    assert mismatches[0]["unexpected_obligations"]
    assert "phase3_post_fix_gate_pending_obligations_present" in manifest["summary"]["failed_kinds"]
    with pytest.raises(ValueError, match="phase3_post_fix_gate_pending_obligations_present"):
        validate_phase3_post_fix_gate_index(manifest, repo_root=repo, gate_specs=specs)


def test_phase3_post_fix_gate_index_rejects_pending_obligation_without_required_actions(tmp_path):
    repo = tmp_path / "repo"
    specs = (_spec(1, "lane_one"),)
    _write_gate(
        repo,
        specs[0],
        post_fix_status="pending_proof",
        omit_required_completion_actions=True,
    )

    path = build_phase3_post_fix_gate_index(
        repo_root=repo,
        output_dir=tmp_path / "out",
        gate_specs=specs,
    )
    manifest = json.loads(path.read_text())

    assert manifest["phase3_post_fix_gates_ready"] is False
    missing = manifest["gates"][0]["post_fix_obligation_summary"][
        "pending_proof_entries_missing_required_actions"
    ]
    assert missing == ["lane_one-entry"]
    assert "phase3_post_fix_gate_pending_obligations_present" in manifest["summary"]["failed_kinds"]
    with pytest.raises(ValueError, match="phase3_post_fix_gate_pending_obligations_present"):
        validate_phase3_post_fix_gate_index(manifest, repo_root=repo, gate_specs=specs)


def test_phase3_post_fix_gate_index_rejects_manifest_repo_root_drift(tmp_path):
    repo = tmp_path / "repo"
    specs = (_spec(1, "lane_one"),)
    _write_gate(repo, specs[0])
    path = build_phase3_post_fix_gate_index(
        repo_root=repo,
        output_dir=tmp_path / "out",
        gate_specs=specs,
    )
    manifest = json.loads(path.read_text())
    manifest["repo_root"] = str(tmp_path / "forged-repo")

    with pytest.raises(ValueError, match="repo_root"):
        validate_phase3_post_fix_gate_index(manifest, repo_root=repo, gate_specs=specs)
