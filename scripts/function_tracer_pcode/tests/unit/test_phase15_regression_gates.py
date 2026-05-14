# -*- coding: utf-8 -*-

import json
from pathlib import Path

import pytest

from scripts.function_tracer_pcode.validation.freeze_observed_baseline import (
    freeze_observed_baseline,
)
from scripts.function_tracer_pcode.validation.phase15_regression_gates import (
    build_phase15_regression_gates,
    validate_phase15_regression_gates,
)
from scripts.function_tracer_pcode.validation.unknown_reason_summary import (
    RESULT_JSON_BEGIN,
    RESULT_JSON_END,
)


def _payload(function_name, left_name, right_name, is_equivalent, *, unknown_reasons=()):
    return {
        "function1_name": function_name,
        "function2_name": function_name,
        "binary1_name": left_name,
        "binary2_name": right_name,
        "is_equivalent": is_equivalent,
        "is_timeout": False,
        "error_message": None,
        "unknown_reasons": list(unknown_reasons),
        "unknown_recovery_backlog": {},
    }


def _reason(reason_id):
    return {
        "reason_id": reason_id,
        "decision_effect": "blocks_equivalence",
        "reason_scope": "function",
        "recovery_proof_kind": "call_effect_summary_proof",
    }


def _write_log(root: Path, function_name: str, left: str, right: str, payload):
    function_dir = root / function_name
    function_dir.mkdir(parents=True, exist_ok=True)
    if payload["is_equivalent"] is True:
        result = "EQUIVALENT"
    elif payload["is_equivalent"] is False:
        result = "NOT EQUIVALENT"
    else:
        result = "UNKNOWN"
    path = function_dir / f"{function_name}_{left}_{right}.log"
    path.write_text(
        "\n".join(
            [
                f"Result: {result}",
                RESULT_JSON_BEGIN,
                json.dumps(payload),
                RESULT_JSON_END,
            ]
        )
    )
    return path


def _write_phase1_manifests(phase1_dir: Path):
    phase1_dir.mkdir(parents=True)
    positive = {
        "manifest_kind": "positive_concrete_pairs",
        "entries": [
            {
                "id": "positive-control",
                "function": "fc_positive",
                "category": "function_call",
                "binary_pair": "B1_B2",
                "left_binary_id": "B1",
                "right_binary_id": "B2",
                "current_result": "EQ",
                "expected_result": "EQ",
                "object_evidence_status": "verified",
                "object_evidence_ref": {
                    "path": "object_evidence/positive_object_evidence.json",
                    "sha256": "a" * 64,
                },
                "object_evidence_summary": {
                    "object_facts": {
                        "left": {"call_count": 0},
                        "right": {"call_count": 0},
                    }
                },
                "source_artifact": {
                    "log_path": "logs/function_call/fc_positive/fc_positive_B1_B2.log",
                    "log_sha256": "b" * 64,
                },
            }
        ],
    }
    negative = {
        "manifest_kind": "negative_concrete_pairs",
        "entries": [
            {
                "id": "negative-guard",
                "function": "fc_negative",
                "category": "function_call",
                "binary_pair": "B1_B2",
                "left_binary_id": "B1",
                "right_binary_id": "B2",
                "current_result": "UNKNOWN",
                "expected_result": "UNKNOWN",
                "must_not_be_equivalent": True,
                "negative_case": "call/memory side-effect mismatch",
                "required_reason_ids": ["equivalence_blocking_unsafety"],
                "observed_reason_ids": ["equivalence_blocking_unsafety"],
                "observed_reason_records": [
                    {
                        "reason_id": "equivalence_blocking_unsafety",
                        "decision_effect": "blocks_equivalence",
                        "reason_scope": "function",
                        "recovery_proof_kind": "call_effect_summary_proof",
                        "proof_stage": "<missing>",
                        "action_status": "<missing>",
                    }
                ],
                "unknown_allowance": {
                    "allowance_kind": "explicit_proof_obligation",
                    "failure_origin": "false_eq_guard",
                    "proof_obligation": "call_effect_summary_proof",
                },
                "source_artifact": {
                    "log_path": "logs/function_call/fc_negative/fc_negative_B1_B2.log",
                    "log_sha256": "c" * 64,
                },
            }
        ],
    }
    representative = {
        "manifest_kind": "representative_concrete_pairs",
        "entries": [
            {
                "id": "representative-guard",
                "function": "fc_negative",
                "category": "function_call",
                "binary_pair": "B1_B2",
                "left_binary_id": "B1",
                "right_binary_id": "B2",
                "current_result": "UNKNOWN",
                "required_reason_ids": ["equivalence_blocking_unsafety"],
                "observed_reason_ids": ["equivalence_blocking_unsafety"],
                "observed_reason_records": [
                    {
                        "reason_id": "equivalence_blocking_unsafety",
                        "decision_effect": "blocks_equivalence",
                        "reason_scope": "function",
                        "recovery_proof_kind": "call_effect_summary_proof",
                        "proof_stage": "<missing>",
                        "action_status": "<missing>",
                    }
                ],
                "expected_movement": {
                    "reason_id": "equivalence_blocking_unsafety",
                    "decision_effect": "blocks_equivalence",
                    "reason_scope": "function",
                    "recovery_proof_kind": "call_effect_summary_proof",
                    "proof_stage": "object_evidence_collected",
                    "action_status": "pending_proof",
                },
                "source_artifact": {
                    "log_path": "logs/function_call/fc_negative/fc_negative_B1_B2.log",
                    "log_sha256": "c" * 64,
                },
            }
        ],
    }
    synthetic = {
        "manifest_kind": "synthetic_positive_manifest",
        "synthetic_positive_required": False,
        "entries": [],
        "planned_negative_synthetic_entries": [],
        "synthetic_negative_entries": [],
    }
    index = {
        "manifest_kind": "phase1_concrete_manifest_index",
        "baseline_id": "observed-v0@0a53352",
        "phase1_ready": True,
        "blocking_issue_kinds": [],
        "manifests": {
            "positive": "positive_manifest.json",
            "negative": "negative_manifest.json",
            "representative": "representative_manifest.json",
            "synthetic": "synthetic_manifest.json",
        },
        "readiness": {"phase1_ready": True, "blocking_issues": []},
    }
    for name, payload in (
        ("positive_manifest.json", positive),
        ("negative_manifest.json", negative),
        ("representative_manifest.json", representative),
        ("synthetic_manifest.json", synthetic),
        ("phase1_manifest_index.json", index),
    ):
        (phase1_dir / name).write_text(json.dumps(payload))


def _fixture(
    tmp_path,
    *,
    current_positive_payload=None,
    current_negative_payload=None,
    unverified_positive=False,
):
    source_root = tmp_path / "source_logs" / "function_call"
    _write_log(
        source_root,
        "fc_positive",
        "B1",
        "B2",
        _payload("fc_positive", "left-bin", "right-bin", True),
    )
    _write_log(
        source_root,
        "fc_negative",
        "B1",
        "B2",
        _payload(
            "fc_negative",
            "left-bin",
            "right-bin",
            None,
            unknown_reasons=(_reason("equivalence_blocking_unsafety"),),
        ),
    )
    baseline_root = tmp_path / "artifacts" / "observed-v0@0a53352"
    freeze_observed_baseline(
        baseline_id="observed-v0@0a53352",
        git_head="0a53352",
        output_root=baseline_root,
        source_roots={"function_call": source_root},
        workspace_root=Path.cwd(),
    )
    phase1_dir = baseline_root / "phase1"
    _write_phase1_manifests(phase1_dir)
    if unverified_positive:
        positive_path = phase1_dir / "positive_manifest.json"
        positive = json.loads(positive_path.read_text())
        positive["entries"][0]["object_evidence_status"] = "not_verified"
        positive_path.write_text(json.dumps(positive))

    current_root = tmp_path / "current_logs" / "function_call"
    _write_log(
        current_root,
        "fc_positive",
        "B1",
        "B2",
        current_positive_payload
        or _payload("fc_positive", "left-bin", "right-bin", True),
    )
    _write_log(
        current_root,
        "fc_negative",
        "B1",
        "B2",
        current_negative_payload
        or _payload(
            "fc_negative",
            "left-bin",
            "right-bin",
            None,
            unknown_reasons=(_reason("equivalence_blocking_unsafety"),),
        ),
    )
    return baseline_root, phase1_dir, current_root


def test_phase15_regression_gate_accepts_prefix_exact_match(tmp_path):
    baseline_root, phase1_dir, current_root = _fixture(tmp_path)

    gate_path = build_phase15_regression_gates(
        baseline_raw_dir=baseline_root / "raw",
        phase1_dir=phase1_dir,
        output_dir=baseline_root / "phase1_5",
        current_log_roots={"function_call": current_root},
    )

    gate = json.loads(gate_path.read_text())
    assert gate["phase1_5_ready"] is True
    assert gate["stage"] == "pre_semantic_fix"
    assert gate["gate_summary"]["failed"] == 0
    assert gate["gate_summary"]["baseline_comparison_mode"] == "exact_match"
    validate_phase15_regression_gates(gate)


def test_phase15_regression_gate_rejects_false_eq_guard_regression(tmp_path):
    baseline_root, phase1_dir, current_root = _fixture(
        tmp_path,
        current_negative_payload=_payload("fc_negative", "left-bin", "right-bin", True),
    )

    gate_path = build_phase15_regression_gates(
        baseline_raw_dir=baseline_root / "raw",
        phase1_dir=phase1_dir,
        output_dir=baseline_root / "phase1_5",
        current_log_roots={"function_call": current_root},
    )

    gate = json.loads(gate_path.read_text())
    assert gate["phase1_5_ready"] is False
    assert "false_eq_guard_regression" in gate["gate_summary"]["failed_kinds"]
    with pytest.raises(ValueError, match="false_eq_guard_regression"):
        validate_phase15_regression_gates(gate)


def test_phase15_regression_gate_rejects_positive_pair_result_regression(tmp_path):
    baseline_root, phase1_dir, current_root = _fixture(
        tmp_path,
        current_positive_payload=_payload("fc_positive", "left-bin", "right-bin", None),
    )

    gate_path = build_phase15_regression_gates(
        baseline_raw_dir=baseline_root / "raw",
        phase1_dir=phase1_dir,
        output_dir=baseline_root / "phase1_5",
        current_log_roots={"function_call": current_root},
    )

    gate = json.loads(gate_path.read_text())
    assert gate["phase1_5_ready"] is False
    assert "positive_concrete_pair_regression" in gate["gate_summary"]["failed_kinds"]


def test_phase15_regression_gate_rejects_representative_reason_tuple_regression(tmp_path):
    baseline_root, phase1_dir, current_root = _fixture(
        tmp_path,
        current_negative_payload=_payload(
            "fc_negative",
            "left-bin",
            "right-bin",
            None,
            unknown_reasons=(_reason("return_coverage_gap"),),
        ),
    )

    gate_path = build_phase15_regression_gates(
        baseline_raw_dir=baseline_root / "raw",
        phase1_dir=phase1_dir,
        output_dir=baseline_root / "phase1_5",
        current_log_roots={"function_call": current_root},
    )

    gate = json.loads(gate_path.read_text())
    assert gate["phase1_5_ready"] is False
    assert "representative_record_tuple_regression" in gate["gate_summary"]["failed_kinds"]
    assert "proof_action_multiset_regression" in gate["gate_summary"]["failed_kinds"]


def test_phase15_regression_gate_rejects_unverified_positive_object_evidence(tmp_path):
    baseline_root, phase1_dir, current_root = _fixture(tmp_path, unverified_positive=True)

    gate_path = build_phase15_regression_gates(
        baseline_raw_dir=baseline_root / "raw",
        phase1_dir=phase1_dir,
        output_dir=baseline_root / "phase1_5",
        current_log_roots={"function_call": current_root},
    )

    gate = json.loads(gate_path.read_text())
    assert gate["phase1_5_ready"] is False
    assert "object_derived_evidence_emission_regression" in gate["gate_summary"]["failed_kinds"]
