# -*- coding: utf-8 -*-

import json
from pathlib import Path

import pytest

from scripts.function_tracer_pcode.validation.freeze_observed_baseline import (
    freeze_observed_baseline,
)
from scripts.function_tracer_pcode.validation.phase1_concrete_manifest_gate import (
    build_phase1_concrete_manifest_gate,
    validate_phase1_concrete_manifest_gate,
)
from scripts.function_tracer_pcode.validation.phase1_concrete_manifests import (
    NEGATIVE_MINIMUM_CASES,
    build_phase1_concrete_manifests,
)
from scripts.function_tracer_pcode.validation.unknown_reason_summary import (
    RESULT_JSON_BEGIN,
    RESULT_JSON_END,
)


def test_phase1_concrete_manifest_gate_validates_frozen_ready_artifacts(tmp_path):
    baseline_root, phase1_dir = _ready_phase1_fixture(tmp_path)

    gate_path = build_phase1_concrete_manifest_gate(
        phase1_dir=phase1_dir,
        baseline_raw_dir=baseline_root / "raw",
        output_dir=tmp_path / "gate",
    )

    gate = json.loads(gate_path.read_text())
    assert gate["phase1_concrete_manifest_ready"] is True
    assert gate["summary"]["failed"] == 0
    assert gate["counts"]["positive"] == 1
    assert gate["counts"]["negative"] == len(NEGATIVE_MINIMUM_CASES)
    assert gate["counts"]["synthetic_negative"] == 2
    validate_phase1_concrete_manifest_gate(gate)


def test_phase1_concrete_manifest_gate_rejects_tampered_source_log(tmp_path):
    baseline_root, phase1_dir = _ready_phase1_fixture(tmp_path)
    log_path = baseline_root / "raw" / "logs" / "function_call" / "fc_positive" / "fc_positive_B1_B2.log"
    log_path.write_text(log_path.read_text() + "\n# tampered\n")

    gate_path = build_phase1_concrete_manifest_gate(
        phase1_dir=phase1_dir,
        baseline_raw_dir=baseline_root / "raw",
        output_dir=tmp_path / "gate",
    )

    gate = json.loads(gate_path.read_text())
    assert gate["phase1_concrete_manifest_ready"] is False
    assert "phase1_source_log_hash" in gate["summary"]["failed_kinds"]
    with pytest.raises(ValueError, match="phase1_source_log_hash"):
        validate_phase1_concrete_manifest_gate(gate)


def test_phase1_concrete_manifest_gate_rejects_duplicate_concrete_entry_id(tmp_path):
    baseline_root, phase1_dir = _ready_phase1_fixture(tmp_path)
    negative_path = phase1_dir / "negative_manifest.json"
    negative = json.loads(negative_path.read_text())
    negative["entries"][0]["id"] = "positive-control"
    negative_path.write_text(json.dumps(negative), encoding="utf-8")

    gate_path = build_phase1_concrete_manifest_gate(
        phase1_dir=phase1_dir,
        baseline_raw_dir=baseline_root / "raw",
        output_dir=tmp_path / "gate",
    )

    gate = json.loads(gate_path.read_text())
    assert gate["phase1_concrete_manifest_ready"] is False
    assert "phase1_entry_ids_globally_unique" in gate["summary"]["failed_kinds"]
    with pytest.raises(ValueError, match="phase1_entry_ids_globally_unique"):
        validate_phase1_concrete_manifest_gate(gate)


def _ready_phase1_fixture(tmp_path: Path):
    source_root = tmp_path / "logs" / "function_call_test"
    _write_log(
        source_root,
        "fc_positive",
        "B1",
        "B2",
        _payload("fc_positive", "left-bin", "right-bin", True),
    )
    _write_log(
        source_root,
        "fc_negative_guard",
        "B1",
        "B2",
        _payload(
            "fc_negative_guard",
            "left-bin",
            "right-bin",
            None,
            unknown_reasons=tuple(_reason(reason_id) for reason_id in _required_reason_ids()),
        ),
    )
    baseline_root = tmp_path / "artifacts" / "observed-v0@0a53352"
    freeze_observed_baseline(
        baseline_id="observed-v0@0a53352",
        git_head="0a53352cf3c9528abfb654906ed7b963474bedc5",
        output_root=baseline_root,
        source_roots={"function_call": source_root},
        workspace_root=Path.cwd(),
    )
    phase1_dir = baseline_root / "phase1"
    _write_positive_object_evidence(phase1_dir)
    _write_synthetic_negative_artifact(phase1_dir)
    build_phase1_concrete_manifests(
        baseline_raw_dir=baseline_root / "raw",
        output_dir=phase1_dir,
        plan=_ready_phase1_plan(),
    )
    return baseline_root, phase1_dir


def _ready_phase1_plan():
    negative_plan = []
    synthetic_cases = {"call target mismatch", "argument storage mismatch"}
    for idx, case in enumerate(NEGATIVE_MINIMUM_CASES):
        if case in synthetic_cases:
            continue
        reason_id = _case_reason_id(case)
        negative_plan.append(
            {
                "id": f"negative-{idx}",
                "category": "function_call",
                "function": "fc_negative_guard",
                "binary_pair": "B1_B2",
                "expected_result": "UNKNOWN",
                "must_not_be_equivalent": True,
                "negative_case": case,
                "required_reason_ids": [reason_id],
                "unknown_allowance": {
                    "allowance_kind": "explicit_proof_obligation",
                    "failure_origin": "false_eq_guard",
                    "proof_obligation": f"proof-{idx}",
                },
            }
        )
    return {
        "positive": [
            {
                "id": "positive-control",
                "category": "function_call",
                "function": "fc_positive",
                "binary_pair": "B1_B2",
                "expected_result": "EQ",
                "role": "direct-call control",
            }
        ],
        "negative": negative_plan,
        "representative": [
            {
                "id": "representative-guard",
                "category": "function_call",
                "function": "fc_negative_guard",
                "binary_pair": "B1_B2",
                "current_result": "UNKNOWN",
                "required_reason_ids": ["equivalence_blocking_unsafety"],
                "expected_movement": {
                    "reason_id": "equivalence_blocking_unsafety",
                    "decision_effect": "blocks_equivalence",
                    "reason_scope": "function",
                    "recovery_proof_kind": "call_effect_summary_proof",
                    "proof_stage": "object_evidence_collected",
                    "action_status": "pending_proof",
                },
            }
        ],
        "synthetic": {
            "synthetic_positive_required": False,
            "entries": [],
            "planned_negative_synthetic_entries": [
                {"id": "synthetic-negative-call-target-mismatch", "artifact_status": "planned_not_created"},
                {"id": "synthetic-negative-argument-storage-mismatch", "artifact_status": "planned_not_created"},
            ],
        },
    }


def _write_positive_object_evidence(phase1_dir: Path):
    evidence_dir = phase1_dir / "object_evidence"
    evidence_dir.mkdir(parents=True)
    (evidence_dir / "positive_object_evidence.json").write_text(
        json.dumps(
            {
                "manifest_kind": "phase1_positive_object_evidence",
                "entries": [
                    {
                        "entry_id": "positive-control",
                        "status": "verified",
                        "category": "function_call",
                        "function": "fc_positive",
                        "binary_pair": "B1_B2",
                        "evidence_source": {
                            "kind": "pyghidra_object_probe",
                            "path": "object_evidence/pyghidra/positive-control.json",
                            "sha256": "a" * 64,
                        },
                        "shape_confirmation": {
                            "role": "direct-call control",
                            "object_facts": {
                                "left": {"call_count": 1},
                                "right": {"call_count": 1},
                            },
                        },
                    }
                ],
            }
        )
    )


def _write_synthetic_negative_artifact(phase1_dir: Path):
    synthetic_dir = phase1_dir / "synthetic_negative"
    synthetic_dir.mkdir(parents=True)
    (synthetic_dir / "synthetic_negative_artifact_manifest.json").write_text(
        json.dumps(
            {
                "manifest_kind": "phase1_synthetic_negative_artifact",
                "synthetic_negative_baseline_id": "synthetic-negative-v0@test",
                "entries": [
                    _synthetic_negative_entry(
                        "synthetic-negative-call-target-mismatch",
                        "call target mismatch",
                        "syn_call_target_mismatch",
                        "S1",
                        "S2",
                    ),
                    _synthetic_negative_entry(
                        "synthetic-negative-argument-storage-mismatch",
                        "argument storage mismatch",
                        "syn_argument_storage_mismatch",
                        "S3",
                        "S4",
                    ),
                ],
            }
        )
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


def _write_log(root: Path, function_name: str, left: str, right: str, payload):
    function_dir = root / function_name
    function_dir.mkdir(parents=True, exist_ok=True)
    result = "UNKNOWN"
    if payload["is_equivalent"] is True:
        result = "EQUIVALENT"
    elif payload["is_equivalent"] is False:
        result = "NOT EQUIVALENT"
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


def _reason(reason_id):
    return {
        "reason_id": reason_id,
        "decision_effect": "blocks_equivalence",
        "reason_scope": "function",
        "recovery_proof_kind": "call_effect_summary_proof",
    }


def _required_reason_ids():
    return sorted({_case_reason_id(case) for case in NEGATIVE_MINIMUM_CASES} | {"equivalence_blocking_unsafety"})


def _case_reason_id(case):
    return {
        "call/memory side-effect mismatch": "equivalence_blocking_unsafety",
        "width/high-bit near-miss": "return_width_bridge_missing",
        "readonly count mismatch": "readonly_identity_missing",
        "return partition miss": "return_coverage_gap",
        "guard coverage miss": "sat_unsafety",
        "inconclusive return coverage near-miss": "return_coverage_inconclusive",
        "Method-B wrong-tail / guard partition miss": "method_b_closure_blocked",
        "call target mismatch": "equivalence_blocking_unsafety",
        "argument storage mismatch": "equivalence_blocking_unsafety",
    }[case]


def _synthetic_negative_entry(entry_id, negative_case, function, left, right):
    return {
        "id": entry_id,
        "category": "synthetic_negative",
        "function": function,
        "binary_pair": f"{left}_{right}",
        "left_binary_id": left,
        "right_binary_id": right,
        "current_result": "NOT_EQ",
        "expected_result": "NOT_EQ",
        "must_not_be_equivalent": True,
        "negative_case": negative_case,
        "artifact_status": "created",
        "synthetic_negative_baseline_id": "synthetic-negative-v0@test",
        "binary_hashes": {left: "b" * 64, right: "c" * 64},
        "source_revision": {"kind": "embedded_source", "sha256": "d" * 64},
        "build_flags": ["gcc", "-O0"],
        "build_import_decompiler_settings": {
            "ghidra_version": "test",
            "language_id": "x86:LE:64:default",
            "compiler_spec_id": "gcc",
        },
        "expected_counts": {
            "final_result": {"NOT_EQ": 1},
            "validation_unknown_unit": {},
        },
        "ground_truth_source": {
            "classification": "ground_truth_not_eq",
            "oracle_review_status": "accepted",
            "expected_equivalent": False,
            "oracle_exception": False,
            "eq_goal_excluded": True,
            "counterexample_replay_status": "passed",
            "abi_storage_width_proof": "passed",
            "return_compare_width_proof": "passed",
            "ub_exclusion_rule": "defined_inputs_only",
            "coverage_status": "complete",
            "sat_unsafety_status": "none",
            "call_memory_effect_status": "supported",
        },
        "object_evidence": {
            "evidence_source": "synthetic_ghidra_object_manifest",
            "object_facts": {"kind": negative_case},
        },
    }
