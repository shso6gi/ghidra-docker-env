# -*- coding: utf-8 -*-

import hashlib
import json
from pathlib import Path

import pytest

from scripts.function_tracer_pcode.validation.phase0d_not_eq_audit_gate import (
    build_phase0d_not_eq_audit_gate,
    validate_phase0d_not_eq_audit_gate,
)


def test_phase0d_not_eq_audit_gate_accepts_unresolved_observed_audit(tmp_path):
    raw_dir, audit_path, oracle_path = _write_fixture(tmp_path)

    path = build_phase0d_not_eq_audit_gate(
        baseline_raw_dir=raw_dir,
        audit_manifest=audit_path,
        oracle_manifest=oracle_path,
        output_dir=tmp_path / "gate",
        expected_entry_count=1,
        expected_classification_counts={"unresolved": 1},
        expected_oracle_review_status_counts={"draft": 1},
        **_fixture_expected_posture_counts(),
    )
    gate = json.loads(path.read_text())

    assert gate["phase0d_not_eq_audit_ready"] is True
    assert gate["classification_counts"] == {"unresolved": 1}
    assert gate["oracle_review_status_counts"] == {"draft": 1}
    validate_phase0d_not_eq_audit_gate(gate)
    tampered_summary = json.loads(json.dumps(gate))
    tampered_summary["summary"]["failed_kinds"] = ["hidden_phase0d_failure"]
    tampered_summary["summary"]["failed"] = 1
    with pytest.raises(ValueError, match="hidden_phase0d_failure"):
        validate_phase0d_not_eq_audit_gate(tampered_summary)
    tampered_checks = json.loads(json.dumps(gate))
    tampered_checks["checks"].append({"kind": "hidden_phase0d_check_failure", "status": "failed"})
    with pytest.raises(ValueError, match="hidden_phase0d_check_failure"):
        validate_phase0d_not_eq_audit_gate(tampered_checks)
    tampered_context = json.loads(json.dumps(gate))
    del tampered_context["checks"]
    with pytest.raises(ValueError, match="checks_missing"):
        validate_phase0d_not_eq_audit_gate(tampered_context)
    tampered_audit_ref = json.loads(json.dumps(gate))
    tampered_audit_ref["audit_manifest_ref"]["sha256"] = "0" * 64
    with pytest.raises(ValueError, match="materialized_audit_manifest_ref"):
        validate_phase0d_not_eq_audit_gate(tampered_audit_ref)
    missing_context = json.loads(json.dumps(gate))
    del missing_context["baseline_raw_artifact_ref"]
    with pytest.raises(ValueError, match="materialized_context_missing"):
        validate_phase0d_not_eq_audit_gate(missing_context)


def test_phase0d_not_eq_audit_gate_rejects_unexpected_ground_truth(tmp_path):
    raw_dir, audit_path, oracle_path = _write_fixture(tmp_path)
    audit = json.loads(audit_path.read_text())
    audit["entries"][0]["classification"] = "ground_truth_not_eq"
    audit["classification_counts"] = {"ground_truth_not_eq": 1}
    audit["entries"][0]["oracle_manifest_ref"]["oracle_review_status"] = "accepted"
    audit["entries"][0]["oracle_exception"] = {"status": "accepted", "review_status": "accepted"}
    audit["entries"][0]["counterexample_model_ref"] = {
        "counterexample_present": True,
        "solver_model_present": True,
        "replay_status": "replayed",
    }
    audit["entries"][0]["replay_harness"] = {"status": "available"}
    audit["entries"][0]["coverage_status"] = {
        "status": "reported_pairwise_no_unknown_or_error_pairs",
        "unknown_pairs": 0,
        "error_pairs": 0,
    }
    audit["entries"][0]["input_width_policy"] = {"status": "abi_storage_width_proven"}
    audit["entries"][0]["return_compare_width"] = {"status": "smt_type_widths_proven"}
    audit["entries"][0]["ub_exclusion_rule"] = {"status": "proven"}
    audit_path.write_text(json.dumps(audit), encoding="utf-8")
    oracle = json.loads(oracle_path.read_text())
    oracle["entries"][0]["oracle_review_status"] = "accepted"
    oracle_path.write_text(json.dumps(oracle), encoding="utf-8")

    path = build_phase0d_not_eq_audit_gate(
        baseline_raw_dir=raw_dir,
        audit_manifest=audit_path,
        oracle_manifest=oracle_path,
        output_dir=tmp_path / "gate",
        expected_entry_count=1,
        expected_classification_counts={"unresolved": 1},
        expected_oracle_review_status_counts={"draft": 1},
        **_fixture_expected_posture_counts(),
    )
    gate = json.loads(path.read_text())

    assert gate["phase0d_not_eq_audit_ready"] is False
    with pytest.raises(ValueError, match="not_eq_audit_classification_counts_expected"):
        validate_phase0d_not_eq_audit_gate(gate)


def test_phase0d_not_eq_audit_gate_rejects_missing_dirty_snapshot_hash(tmp_path):
    raw_dir, audit_path, oracle_path = _write_fixture(tmp_path)
    raw_manifest = json.loads((raw_dir / "artifact_manifest.json").read_text())
    raw_manifest["dirty_state"] = {"is_dirty": True}
    (raw_dir / "artifact_manifest.json").write_text(json.dumps(raw_manifest), encoding="utf-8")

    path = build_phase0d_not_eq_audit_gate(
        baseline_raw_dir=raw_dir,
        audit_manifest=audit_path,
        oracle_manifest=oracle_path,
        output_dir=tmp_path / "gate",
        expected_entry_count=1,
        expected_classification_counts={"unresolved": 1},
        expected_oracle_review_status_counts={"draft": 1},
        **_fixture_expected_posture_counts(),
    )
    gate = json.loads(path.read_text())

    assert gate["phase0d_not_eq_audit_ready"] is False
    with pytest.raises(ValueError, match="dirty_snapshot_hash_present"):
        validate_phase0d_not_eq_audit_gate(gate)


def test_phase0d_not_eq_audit_gate_rejects_missing_required_entry_field(tmp_path):
    raw_dir, audit_path, oracle_path = _write_fixture(tmp_path)
    audit = json.loads(audit_path.read_text())
    del audit["entries"][0]["coverage_status_source"]
    audit_path.write_text(json.dumps(audit), encoding="utf-8")

    path = build_phase0d_not_eq_audit_gate(
        baseline_raw_dir=raw_dir,
        audit_manifest=audit_path,
        oracle_manifest=oracle_path,
        output_dir=tmp_path / "gate",
        expected_entry_count=1,
        expected_classification_counts={"unresolved": 1},
        expected_oracle_review_status_counts={"draft": 1},
        **_fixture_expected_posture_counts(),
    )
    gate = json.loads(path.read_text())

    assert gate["phase0d_not_eq_audit_ready"] is False
    assert "not_eq_audit_required_fields_present" in gate["summary"]["failed_kinds"]
    with pytest.raises(ValueError, match="not_eq_audit_required_fields_present"):
        validate_phase0d_not_eq_audit_gate(gate)


def test_phase0d_not_eq_audit_gate_rejects_tampered_source_log(tmp_path):
    raw_dir, audit_path, oracle_path = _write_fixture(tmp_path)
    source_log = raw_dir / "logs" / "function_call" / "fc_guarded_call" / "fc_guarded_call_B10_B11.log"
    source_log.write_text(source_log.read_text() + "\n# tampered\n", encoding="utf-8")

    path = build_phase0d_not_eq_audit_gate(
        baseline_raw_dir=raw_dir,
        audit_manifest=audit_path,
        oracle_manifest=oracle_path,
        output_dir=tmp_path / "gate",
        expected_entry_count=1,
        expected_classification_counts={"unresolved": 1},
        expected_oracle_review_status_counts={"draft": 1},
        **_fixture_expected_posture_counts(),
    )
    gate = json.loads(path.read_text())

    assert gate["phase0d_not_eq_audit_ready"] is False
    assert "not_eq_audit_source_log_hashes_match" in gate["summary"]["failed_kinds"]
    with pytest.raises(ValueError, match="not_eq_audit_source_log_hashes_match"):
        validate_phase0d_not_eq_audit_gate(gate)


def test_phase0d_not_eq_audit_gate_rejects_binary_pair_side_mismatch(tmp_path):
    raw_dir, audit_path, oracle_path = _write_fixture(tmp_path)
    audit = json.loads(audit_path.read_text())
    audit["entries"][0]["binary_pair"] = "B10_B12"
    audit_path.write_text(json.dumps(audit), encoding="utf-8")

    path = build_phase0d_not_eq_audit_gate(
        baseline_raw_dir=raw_dir,
        audit_manifest=audit_path,
        oracle_manifest=oracle_path,
        output_dir=tmp_path / "gate",
        expected_entry_count=1,
        expected_classification_counts={"unresolved": 1},
        expected_oracle_review_status_counts={"draft": 1},
        **_fixture_expected_posture_counts(),
    )
    gate = json.loads(path.read_text())

    assert gate["phase0d_not_eq_audit_ready"] is False
    assert "not_eq_audit_binary_pair_matches_sides" in gate["summary"]["failed_kinds"]
    with pytest.raises(ValueError, match="not_eq_audit_binary_pair_matches_sides"):
        validate_phase0d_not_eq_audit_gate(gate)


def test_phase0d_not_eq_audit_gate_rejects_unreviewed_pair_scoped_oracle(tmp_path):
    raw_dir, audit_path, oracle_path = _write_fixture(tmp_path)
    oracle = json.loads(oracle_path.read_text())
    oracle["entries"][0]["oracle_scope"] = "pair"
    oracle["entries"][0]["scope_target"]["binary_pair"] = "B10_B11"
    oracle["entries"][0]["entry_key"] = "function_call:fc_guarded_call:B10_B11"
    audit = json.loads(audit_path.read_text())
    audit["entries"][0]["oracle_manifest_ref"]["entry_key"] = "function_call:fc_guarded_call:B10_B11"
    audit_path.write_text(json.dumps(audit), encoding="utf-8")
    oracle_path.write_text(json.dumps(oracle), encoding="utf-8")

    path = build_phase0d_not_eq_audit_gate(
        baseline_raw_dir=raw_dir,
        audit_manifest=audit_path,
        oracle_manifest=oracle_path,
        output_dir=tmp_path / "gate",
        expected_entry_count=1,
        expected_classification_counts={"unresolved": 1},
        expected_oracle_review_status_counts={"draft": 1},
        **_fixture_expected_posture_counts(),
    )
    gate = json.loads(path.read_text())

    assert gate["phase0d_not_eq_audit_ready"] is False
    assert "oracle_pair_scope_absent_until_exception_review" in gate["summary"]["failed_kinds"]
    with pytest.raises(ValueError, match="oracle_pair_scope_absent_until_exception_review"):
        validate_phase0d_not_eq_audit_gate(gate)


def _write_fixture(tmp_path: Path):
    raw_dir = tmp_path / "raw"
    raw_dir.mkdir()
    source_log = raw_dir / "logs" / "function_call" / "fc_guarded_call" / "fc_guarded_call_B10_B11.log"
    source_log.parent.mkdir(parents=True)
    source_log.write_text("Result: NOT EQUIVALENT\n", encoding="utf-8")
    source_log_rel = "logs/function_call/fc_guarded_call/fc_guarded_call_B10_B11.log"
    source_log_sha256 = hashlib.sha256(source_log.read_bytes()).hexdigest()
    raw_manifest = {
        "baseline_id": "observed-v0@0a53352",
        "git_head": "0a53352cf3c9528abfb654906ed7b963474bedc5",
        "dirty_state": {
            "is_dirty": True,
            "dirty_snapshot_hash": "a" * 64,
        },
    }
    (raw_dir / "artifact_manifest.json").write_text(json.dumps(raw_manifest), encoding="utf-8")
    audit_path = tmp_path / "audit.json"
    oracle_path = tmp_path / "oracle.json"
    audit = {
        "manifest_version": 1,
        "audit_kind": "not_eq_ground_truth_audit",
        "baseline_id": "observed-v0@0a53352",
        "baseline_git_head": "0a53352cf3c9528abfb654906ed7b963474bedc5",
        "entry_count": 1,
        "classification_enum": [
            "ground_truth_not_eq",
            "suspected_false_not_eq",
            "ub_or_domain_mismatch",
            "unresolved",
        ],
        "classification_counts": {"unresolved": 1},
        "entries": [
            {
                "function": "fc_guarded_call",
                "category": "function_call",
                "binary_pair": "B10_B11",
                "left_binary_id": "B10",
                "right_binary_id": "B11",
                "side_or_role": "left_vs_right",
                "current_result": "NOT_EQ",
                "expected_equivalent": True,
                "classification": "unresolved",
                "oracle_manifest_ref": {
                    "entry_key": "function_call:fc_guarded_call",
                    "oracle_review_status": "draft",
                    "expected_equivalent": True,
                },
                "oracle_exception": {
                    "status": "missing",
                    "required_if_expected_equivalent_conflict": True,
                },
                "eq_goal_exclusion": {
                    "status": "missing",
                    "required_if_expected_equivalent_conflict": True,
                },
                "counterexample_model_ref": {
                    "counterexample_present": True,
                    "solver_model_present": True,
                    "replay_status": "missing",
                },
                "sat_unsafety_status": {
                    "status": "not_reported_in_final_payload",
                    "active_reason_ids": [],
                },
                "coverage_status": {
                    "status": "reported_pairwise_no_unknown_or_error_pairs",
                    "unknown_pairs": 0,
                    "error_pairs": 0,
                },
                "coverage_status_source": "/pairwise_stats",
                "coverage_gap_status": {
                    "status": "not_reported_in_final_payload",
                    "active_reason_ids": [],
                },
                "call_memory_effect_status": {
                    "status": "not_reported_in_final_payload",
                    "active_reason_ids": [],
                },
                "target_proof_lane": "not_eq_counterexample_replay",
                "oracle_decision_status": "draft_expected_equivalent_not_reviewed",
                "replay_harness": {
                    "status": "missing",
                    "required_for_ground_truth_not_eq": True,
                },
                "input_width_policy": {
                    "status": "captured_from_effective_signatures",
                    "proof_status": "missing",
                },
                "return_compare_width": {
                    "status": "requires_replay_for_width_proof",
                    "proof_status": "missing",
                },
                "memory_initial_state": {
                    "status": "not_reported_in_final_payload",
                },
                "ub_exclusion_rule": {
                    "status": "not_audited",
                    "required_for_ground_truth_not_eq": True,
                },
                "audit_source": {
                    "baseline_id": "observed-v0@0a53352",
                    "log_path": source_log_rel,
                    "log_sha256": source_log_sha256,
                    "payload_index": 0,
                },
            }
        ],
    }
    oracle = {
        "manifest_version": 1,
        "oracle_manifest_kind": "same_source_expected_equivalence_draft",
        "baseline_id": "observed-v0@0a53352",
        "baseline_git_head": "0a53352cf3c9528abfb654906ed7b963474bedc5",
        "entries": [
            {
                "function": "fc_guarded_call",
                "category": "function_call",
                "oracle_scope": "function_category",
                "scope_target": {
                    "category": "function_call",
                    "function": "fc_guarded_call",
                },
                "manifest_version": 1,
                "oracle_owner": "phase_0d_bootstrap",
                "oracle_review_status": "draft",
                "expected_equivalent": True,
                "oracle_source": "same_source_default_pending_review",
                "oracle_exception_reason": None,
                "domain_assumptions": ["same-source default"],
                "last_verified_by_evidence": {"status": "not_reviewed"},
                "entry_key": "function_call:fc_guarded_call",
            }
        ],
    }
    audit_path.write_text(json.dumps(audit), encoding="utf-8")
    oracle_path.write_text(json.dumps(oracle), encoding="utf-8")
    return raw_dir, audit_path, oracle_path


def _fixture_expected_posture_counts():
    return {
        "expected_target_proof_lane_counts": {
            "not_eq_counterexample_replay": 1,
        },
        "expected_replay_status_counts": {
            "missing": 1,
        },
        "expected_coverage_status_source_counts": {
            "/pairwise_stats": 1,
        },
        "expected_audit_category_counts": {
            "function_call": 1,
        },
        "expected_oracle_scope_counts": {
            "function_category": 1,
        },
        "expected_oracle_expected_equivalent_counts": {
            "true": 1,
        },
    }
