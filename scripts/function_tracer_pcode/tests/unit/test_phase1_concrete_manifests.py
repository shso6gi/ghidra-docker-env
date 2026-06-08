# -*- coding: utf-8 -*-

import json
from pathlib import Path

import pytest

from scripts.function_tracer_pcode.validation.freeze_observed_baseline import (
    freeze_observed_baseline,
)
from scripts.function_tracer_pcode.validation.phase1_concrete_manifests import (
    NEGATIVE_MINIMUM_CASES,
    build_phase1_concrete_manifests,
    validate_phase1_readiness,
    validate_negative_manifest,
    validate_positive_manifest,
    validate_synthetic_manifest,
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


def test_build_phase1_manifests_materializes_concrete_ids_and_synthetic_status(tmp_path):
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
    plan = {
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
        "negative": [
            {
                "id": "negative-guard",
                "category": "function_call",
                "function": "fc_negative_guard",
                "binary_pair": "B1_B2",
                "expected_result": "UNKNOWN",
                "must_not_be_equivalent": True,
                "negative_case": "call/memory side-effect mismatch",
                "required_reason_ids": ["equivalence_blocking_unsafety"],
                "unknown_allowance": {
                    "allowance_kind": "explicit_proof_obligation",
                    "failure_origin": "false_eq_guard",
                    "proof_obligation": "call_effect_summary_proof",
                },
            }
        ],
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
        },
    }

    index_path = build_phase1_concrete_manifests(
        baseline_raw_dir=baseline_root / "raw",
        output_dir=baseline_root / "phase1",
        plan=plan,
    )

    index = json.loads(index_path.read_text())
    assert index["phase1_ready"] is False
    assert "missing_negative_minimum_cases" in index["blocking_issue_kinds"]
    assert "positive_object_evidence_not_verified" in index["blocking_issue_kinds"]

    positive = json.loads((baseline_root / "phase1" / index["manifests"]["positive"]).read_text())
    negative = json.loads((baseline_root / "phase1" / index["manifests"]["negative"]).read_text())
    synthetic = json.loads((baseline_root / "phase1" / index["manifests"]["synthetic"]).read_text())

    assert positive["entries"][0]["object_evidence_status"] == "not_verified"
    assert negative["entries"][0]["function"] == "fc_negative_guard"
    assert negative["entries"][0]["binary_pair"] == "B1_B2"
    assert negative["entries"][0]["must_not_be_equivalent"] is True
    assert negative["entries"][0]["current_result"] == "UNKNOWN"
    assert negative["entries"][0]["source_artifact"]["log_sha256"]
    assert "argument storage mismatch" in negative["minimum_case_coverage"]["missing_cases"]
    assert synthetic["synthetic_positive_required"] is False
    assert synthetic["entries"] == []
    assert synthetic["planned_negative_synthetic_count"] == 0


def test_negative_manifest_rejects_unknown_without_conservative_allowance():
    manifest = {
        "entries": [
            {
                "id": "bad",
                "expected_result": "UNKNOWN",
                "must_not_be_equivalent": True,
            }
        ]
    }

    with pytest.raises(ValueError, match="conservative UNKNOWN allowance"):
        validate_negative_manifest(manifest)


def test_negative_manifest_rejects_parser_failure_unknown():
    manifest = {
        "entries": [
            {
                "id": "bad",
                "expected_result": "UNKNOWN",
                "must_not_be_equivalent": True,
                "unknown_allowance": {
                    "allowance_kind": "explicit_proof_obligation",
                    "failure_origin": "parser_failure",
                    "proof_obligation": "return_coverage_completion",
                },
            }
        ]
    }

    with pytest.raises(ValueError, match="parser/internal/extraction/schema"):
        validate_negative_manifest(manifest)


def test_negative_manifest_rejects_not_eq_without_ground_truth_evidence():
    manifest = {
        "entries": [
            {
                "id": "bad-not-eq",
                "expected_result": "NOT_EQ",
                "must_not_be_equivalent": True,
                "ground_truth_source": {
                    "classification": "unresolved",
                    "oracle_review_status": "draft",
                },
            }
        ]
    }

    with pytest.raises(ValueError, match="ground_truth_not_eq"):
        validate_negative_manifest(manifest)


def test_negative_manifest_rejects_not_eq_without_width_and_coverage_proofs():
    manifest = {
        "entries": [
            {
                "id": "bad-not-eq",
                "function": "synthetic",
                "category": "synthetic_negative",
                "binary_pair": "S1_S2",
                "left_binary_id": "S1",
                "right_binary_id": "S2",
                "expected_result": "NOT_EQ",
                "must_not_be_equivalent": True,
                "ground_truth_source": {
                    "classification": "ground_truth_not_eq",
                    "oracle_review_status": "accepted",
                    "expected_equivalent": False,
                    "counterexample_replay_status": "passed",
                },
            }
        ]
    }

    with pytest.raises(ValueError, match="ground_truth_not_eq"):
        validate_negative_manifest(manifest)


def test_phase1_readiness_rejects_missing_mandatory_negative_cases():
    index = {
        "phase1_ready": False,
        "readiness": {
            "blocking_issues": [
                {
                    "kind": "missing_negative_minimum_cases",
                    "missing_cases": ["call target mismatch"],
                }
            ]
        },
    }

    with pytest.raises(ValueError, match="missing_negative_minimum_cases"):
        validate_phase1_readiness(index)


def test_positive_manifest_rejects_ready_without_object_evidence():
    manifest = {
        "entries": [
            {
                "id": "positive",
                "function": "fc_positive",
                "category": "function_call",
                "binary_pair": "B1_B2",
                "left_binary_id": "B1",
                "right_binary_id": "B2",
                "expected_result": "EQ",
                "current_result": "EQ",
                "object_evidence_status": "not_verified",
            }
        ]
    }

    with pytest.raises(ValueError, match="object evidence"):
        validate_positive_manifest(manifest, require_object_evidence=True)


def test_build_phase1_readiness_accepts_created_synthetic_negatives_and_verified_positive_evidence(tmp_path):
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
                        "evidence_source": {
                            "kind": "pyghidra_analysis_json",
                            "path": "object_evidence/pyghidra/positive-control.json",
                            "sha256": "a" * 64,
                        },
                        "shape_confirmation": {
                            "role": "direct-call control",
                            "object_facts": {
                                "left": {"return_count": 1, "deferred_call_count": 0},
                                "right": {"return_count": 1, "deferred_call_count": 0},
                            },
                        },
                    }
                ],
            }
        )
    )
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
    negative_plan = [
        {
            "id": f"negative-{idx}",
            "category": "function_call",
            "function": "fc_negative_guard",
            "binary_pair": "B1_B2",
            "expected_result": "UNKNOWN",
            "must_not_be_equivalent": True,
            "negative_case": case,
            "unknown_allowance": {
                "allowance_kind": "explicit_proof_obligation",
                "failure_origin": "false_eq_guard",
                "proof_obligation": f"proof-{idx}",
            },
        }
        for idx, case in enumerate(NEGATIVE_MINIMUM_CASES)
        if case not in {"call target mismatch", "argument storage mismatch"}
    ]
    plan = {
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
        "representative": [],
        "synthetic": {
            "synthetic_positive_required": False,
            "entries": [],
            "planned_negative_synthetic_entries": [
                {
                    "id": "synthetic-negative-call-target-mismatch",
                    "artifact_status": "planned_not_created",
                },
                {
                    "id": "synthetic-negative-argument-storage-mismatch",
                    "artifact_status": "planned_not_created",
                },
            ],
        },
    }

    index_path = build_phase1_concrete_manifests(
        baseline_raw_dir=baseline_root / "raw",
        output_dir=phase1_dir,
        plan=plan,
    )

    index = json.loads(index_path.read_text())
    assert index["phase1_ready"] is True
    assert index["blocking_issue_kinds"] == []
    assert index["counts"]["synthetic_negative"] == 2
    assert index["counts"]["planned_negative_synthetic"] == 0

    positive = json.loads((phase1_dir / index["manifests"]["positive"]).read_text())
    negative = json.loads((phase1_dir / index["manifests"]["negative"]).read_text())
    synthetic = json.loads((phase1_dir / index["manifests"]["synthetic"]).read_text())

    assert positive["entries"][0]["object_evidence_status"] == "verified"
    assert len(positive["entries"][0]["object_evidence_ref"]["sha256"]) == 64
    assert negative["minimum_case_coverage"]["missing_cases"] == []
    assert [entry["negative_case"] for entry in synthetic["synthetic_negative_entries"]] == [
        "call target mismatch",
        "argument storage mismatch",
    ]
    validate_phase1_readiness(index)
    tampered_readiness = json.loads(json.dumps(index))
    tampered_readiness["readiness"]["blocking_issues"] = [
        {"kind": "hidden_phase1_blocking_issue"}
    ]
    with pytest.raises(ValueError, match="hidden_phase1_blocking_issue"):
        validate_phase1_readiness(tampered_readiness)
    tampered_context = json.loads(json.dumps(index))
    del tampered_context["readiness"]
    with pytest.raises(ValueError, match="readiness_missing"):
        validate_phase1_readiness(tampered_context)


def test_synthetic_manifest_rejects_created_negative_without_oracle_and_artifact_fields():
    manifest = {
        "entries": [],
        "synthetic_negative_entries": [
            {
                "id": "synthetic-negative-call-target-mismatch",
                "artifact_status": "created",
                "function": "syn_call_target_mismatch",
                "binary_pair": "S1_S2",
                "left_binary_id": "S1",
                "right_binary_id": "S2",
                "expected_result": "NOT_EQ",
                "must_not_be_equivalent": True,
                "negative_case": "call target mismatch",
            }
        ],
    }

    with pytest.raises(ValueError, match="ground_truth_source"):
        validate_synthetic_manifest(manifest)


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
        "binary_hashes": {
            left: "b" * 64,
            right: "c" * 64,
        },
        "source_revision": {
            "kind": "embedded_source",
            "sha256": "d" * 64,
        },
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
            "oracle_source": "synthetic_negative_fixture",
            "oracle_exception": False,
            "eq_goal_excluded": True,
            "counterexample_replay_status": "passed",
            "counterexample": {"status": "replayed", "input": {"x": 1}},
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
