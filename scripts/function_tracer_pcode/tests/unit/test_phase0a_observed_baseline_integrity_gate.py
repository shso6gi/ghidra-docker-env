# -*- coding: utf-8 -*-

import json
from pathlib import Path

import pytest

from scripts.function_tracer_pcode.validation.phase0a_observed_baseline_integrity_gate import (
    build_phase0a_observed_baseline_integrity_gate,
    validate_phase0a_observed_baseline_integrity_gate,
)


def test_phase0a_observed_baseline_integrity_gate_accepts_fixture(tmp_path):
    raw_dir = _write_fixture(tmp_path)

    path = build_phase0a_observed_baseline_integrity_gate(
        baseline_raw_dir=raw_dir,
        output_dir=tmp_path / "gate",
    )
    gate = json.loads(path.read_text())

    assert gate["phase0a_observed_baseline_integrity_ready"] is True
    assert gate["raw_evidence"]["indexed_file_count"] == 2
    validate_phase0a_observed_baseline_integrity_gate(gate)


def test_phase0a_observed_baseline_integrity_gate_rejects_missing_raw_log(tmp_path):
    raw_dir = _write_fixture(tmp_path)
    (raw_dir / "logs" / "function_call" / "fc_demo" / "fc_demo_B1_B2.log").unlink()

    path = build_phase0a_observed_baseline_integrity_gate(
        baseline_raw_dir=raw_dir,
        output_dir=tmp_path / "gate",
    )
    gate = json.loads(path.read_text())

    assert gate["phase0a_observed_baseline_integrity_ready"] is False
    with pytest.raises(ValueError, match="file_content_hashes_validated"):
        validate_phase0a_observed_baseline_integrity_gate(gate)


def test_phase0a_observed_baseline_integrity_gate_rejects_hash_drift(tmp_path):
    raw_dir = _write_fixture(tmp_path)
    (raw_dir / "logs" / "loop" / "lmb_demo" / "lmb_demo_B1_B2.log").write_text("changed\n", encoding="utf-8")

    path = build_phase0a_observed_baseline_integrity_gate(
        baseline_raw_dir=raw_dir,
        output_dir=tmp_path / "gate",
    )
    gate = json.loads(path.read_text())

    assert gate["phase0a_observed_baseline_integrity_ready"] is False
    with pytest.raises(ValueError, match="file_content_hashes_validated"):
        validate_phase0a_observed_baseline_integrity_gate(gate)


def test_phase0a_observed_baseline_integrity_gate_rejects_missing_dirty_snapshot_hash(tmp_path):
    raw_dir = _write_fixture(tmp_path)
    manifest_path = raw_dir / "artifact_manifest.json"
    manifest = json.loads(manifest_path.read_text())
    manifest["dirty_state"] = {"is_dirty": True}
    manifest_path.write_text(json.dumps(manifest), encoding="utf-8")

    path = build_phase0a_observed_baseline_integrity_gate(
        baseline_raw_dir=raw_dir,
        output_dir=tmp_path / "gate",
        validate_file_content_hashes=False,
    )
    gate = json.loads(path.read_text())

    assert gate["phase0a_observed_baseline_integrity_ready"] is False
    with pytest.raises(ValueError, match="dirty_snapshot_hash_present"):
        validate_phase0a_observed_baseline_integrity_gate(gate)


def test_phase0a_observed_baseline_integrity_gate_rejects_tampered_ready_raw_evidence(tmp_path):
    raw_dir = _write_fixture(tmp_path)

    path = build_phase0a_observed_baseline_integrity_gate(
        baseline_raw_dir=raw_dir,
        output_dir=tmp_path / "gate",
    )
    gate = json.loads(path.read_text())
    assert gate["phase0a_observed_baseline_integrity_ready"] is True

    gate["raw_evidence"]["indexed_file_count"] = 999
    gate["summary"]["failed"] = False

    with pytest.raises(ValueError, match="materialized_raw_evidence"):
        validate_phase0a_observed_baseline_integrity_gate(gate)


def test_phase0a_observed_baseline_integrity_gate_rejects_missing_materialized_context(tmp_path):
    raw_dir = _write_fixture(tmp_path)

    path = build_phase0a_observed_baseline_integrity_gate(
        baseline_raw_dir=raw_dir,
        output_dir=tmp_path / "gate",
    )
    gate = json.loads(path.read_text())
    assert gate["phase0a_observed_baseline_integrity_ready"] is True

    gate.pop("baseline_raw_artifact_ref")
    gate["raw_evidence"]["indexed_file_count"] = 999

    with pytest.raises(ValueError, match="materialized_context_missing"):
        validate_phase0a_observed_baseline_integrity_gate(gate)


def _write_fixture(tmp_path: Path) -> Path:
    raw_dir = tmp_path / "raw"
    raw_dir.mkdir()
    function_log = raw_dir / "logs" / "function_call" / "fc_demo" / "fc_demo_B1_B2.log"
    loop_log = raw_dir / "logs" / "loop" / "lmb_demo" / "lmb_demo_B1_B2.log"
    function_log.parent.mkdir(parents=True)
    loop_log.parent.mkdir(parents=True)
    function_log.write_text("Result: EQUIVALENT\n", encoding="utf-8")
    loop_log.write_text("Result: UNKNOWN\n", encoding="utf-8")
    (raw_dir / "function_call_20_manifest.json").write_text("{}", encoding="utf-8")
    (raw_dir / "loop_5_manifest.json").write_text("{}", encoding="utf-8")
    workspace_state = raw_dir / "workspace_state"
    workspace_state.mkdir()
    (workspace_state / "git_status_short.txt").write_text(" M demo\n", encoding="utf-8")
    (workspace_state / "git_diff_stat.txt").write_text("demo | 1 +\n", encoding="utf-8")
    (workspace_state / "untracked_file_hashes.json").write_text("{}", encoding="utf-8")
    (workspace_state / "dirty_diff.patch").write_text("diff --git a/demo b/demo\n", encoding="utf-8")

    hashes = {
        "logs/function_call/fc_demo/fc_demo_B1_B2.log": _sha256(function_log),
        "logs/loop/lmb_demo/lmb_demo_B1_B2.log": _sha256(loop_log),
    }
    (raw_dir / "file_hashes.json").write_text(json.dumps(hashes), encoding="utf-8")
    manifest = {
        "manifest_version": 1,
        "baseline_id": "observed-v0@0a53352",
        "git_head": "0a53352cf3c9528abfb654906ed7b963474bedc5",
        "dirty_state": {
            "is_dirty": True,
            "dirty_snapshot_hash": "a" * 64,
        },
        "artifact_storage": {
            "raw_evidence_git_policy": "external_not_committed",
            "raw_evidence_root": "logs",
            "raw_evidence_hash_index_path": "file_hashes.json",
            "raw_evidence_complete_in_freeze_dir": True,
            "tracked_metadata_paths": [
                "README.md",
                "artifact_manifest.json",
                "file_hashes.json",
                "workspace_state/git_status_short.txt",
                "workspace_state/git_diff_stat.txt",
                "workspace_state/untracked_file_hashes.json",
                "workspace_state/dirty_diff.patch",
                "function_call_20_manifest.json",
                "loop_5_manifest.json",
            ],
        },
        "file_content_hashes": hashes,
        "recovered_manifests": {
            "function_call": "function_call_20_manifest.json",
            "loop": "loop_5_manifest.json",
        },
        "source_paths": [
            {
                "category": "function_call",
                "raw_copy_path": "logs/function_call",
                "file_count": 1,
            },
            {
                "category": "loop",
                "raw_copy_path": "logs/loop",
                "file_count": 1,
            },
        ],
    }
    (raw_dir / "README.md").write_text("# baseline\n", encoding="utf-8")
    (raw_dir / "artifact_manifest.json").write_text(json.dumps(manifest), encoding="utf-8")
    return raw_dir


def _sha256(path: Path) -> str:
    import hashlib

    return hashlib.sha256(path.read_bytes()).hexdigest()
