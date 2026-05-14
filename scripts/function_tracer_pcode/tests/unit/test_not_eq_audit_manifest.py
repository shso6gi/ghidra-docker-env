# -*- coding: utf-8 -*-

import json
from pathlib import Path

import pytest

from scripts.function_tracer_pcode.validation.freeze_observed_baseline import (
    freeze_observed_baseline,
)
from scripts.function_tracer_pcode.validation.not_eq_audit_manifest import (
    build_not_eq_audit_manifest,
    validate_not_eq_audit_manifest,
)
from scripts.function_tracer_pcode.validation.unknown_reason_summary import (
    RESULT_JSON_BEGIN,
    RESULT_JSON_END,
)


def _payload(function_name, left_name, right_name, is_equivalent, **extra):
    payload = {
        "function1_name": function_name,
        "function2_name": function_name,
        "binary1_name": left_name,
        "binary2_name": right_name,
        "is_equivalent": is_equivalent,
        "is_timeout": False,
        "error_message": None,
        "unknown_reasons": [],
        "unknown_recovery_backlog": {},
    }
    payload.update(extra)
    return payload


def _write_log(root: Path, function_name: str, left: str, right: str, payload):
    function_dir = root / function_name
    function_dir.mkdir(parents=True, exist_ok=True)
    path = function_dir / f"{function_name}_{left}_{right}.log"
    result_line = "Result: NOT EQUIVALENT" if payload["is_equivalent"] is False else "Result: EQUIVALENT"
    path.write_text(
        "\n".join(
            [
                result_line,
                RESULT_JSON_BEGIN,
                json.dumps(payload),
                RESULT_JSON_END,
            ]
        )
    )
    return path


def _not_eq_payload(function_name="fc_guarded_call"):
    return _payload(
        function_name,
        "function_call_test-gcc-O0",
        "function_call_test-clang-O1",
        False,
        counterexample={
            "parameters": {"param_1_1": "0x1", "param_1_2": "0x1"},
            "return_value1": "0x2",
            "return_value2": "0x3",
        },
        solver_results={
            "is_equivalent": False,
            "first_definitive": {
                "status": "SAT",
                "solver_name": "pairwise_aggregate",
                "model": {"param_1_1": 1, "param_1_2": 1},
            },
            "all_results": [
                {
                    "status": "SAT",
                    "solver_name": "pairwise_aggregate",
                    "model": {"param_1_1": 1, "param_1_2": 1},
                }
            ],
        },
        pairwise_stats={
            "total_pairs": 2,
            "sat_pairs": 1,
            "unknown_pairs": 0,
            "error_pairs": 0,
        },
        sat_pair_info={"i": 0, "j": 1, "pair_stage": "with-ineq"},
        effective_function1_signature={"return_type": "int", "parameters": []},
        effective_function2_signature={"return_type": "int", "parameters": []},
        debug_trace={"final_result": False, "attempts": []},
    )


def test_build_not_eq_audit_manifest_lists_not_eq_entries_with_required_fields(tmp_path):
    source_root = tmp_path / "logs" / "function_call_test"
    _write_log(source_root, "fc_guarded_call", "B10", "B2", _not_eq_payload())
    _write_log(
        source_root,
        "fc_equiv_direct",
        "B1",
        "B2",
        _payload("fc_equiv_direct", "function_call_test-gcc-O0", "function_call_test-gcc-O1", True),
    )
    baseline_root = tmp_path / "artifacts" / "observed-v0@0a53352"
    freeze_observed_baseline(
        baseline_id="observed-v0@0a53352",
        git_head="0a53352",
        output_root=baseline_root,
        source_roots={"function_call": source_root},
        workspace_root=Path.cwd(),
    )

    audit_path = build_not_eq_audit_manifest(
        baseline_raw_dir=baseline_root / "raw",
        output_path=baseline_root / "audit" / "not_eq_audit_manifest.json",
        oracle_output_path=baseline_root / "derived_oracle" / "oracle_manifest_draft.json",
    )

    audit = json.loads(audit_path.read_text())
    oracle = json.loads((baseline_root / "derived_oracle" / "oracle_manifest_draft.json").read_text())
    entry = audit["entries"][0]

    assert audit["entry_count"] == 1
    assert audit["classification_counts"] == {"unresolved": 1}
    assert oracle["entries"][0]["oracle_review_status"] == "draft"
    assert entry["function"] == "fc_guarded_call"
    assert entry["binary_pair"] == "B2_B10"
    assert entry["left_binary_id"] == "B10"
    assert entry["right_binary_id"] == "B2"
    assert entry["current_result"] == "NOT_EQ"
    assert entry["expected_equivalent"] is True
    assert entry["classification"] == "unresolved"
    assert entry["oracle_manifest_ref"]["oracle_review_status"] == "draft"
    assert entry["counterexample_model_ref"]["counterexample_present"] is True
    assert entry["counterexample_model_ref"]["solver_model_present"] is True
    assert entry["sat_unsafety_status"]["status"] == "not_reported_in_final_payload"
    assert entry["coverage_status_source"] == "/pairwise_stats"
    assert entry["coverage_gap_status"]["status"] == "not_reported_in_final_payload"
    assert entry["call_memory_effect_status"]["status"] == "not_reported_in_final_payload"
    assert entry["target_proof_lane"] == "not_eq_counterexample_replay"
    assert entry["oracle_decision_status"] == "draft_expected_equivalent_not_reviewed"
    assert entry["replay_harness"]["status"] == "missing"


def test_validate_not_eq_audit_manifest_rejects_invalid_classification():
    audit = {
        "entries": [
            {
                "classification": "probably_not_eq",
                "oracle_manifest_ref": {"oracle_review_status": "draft"},
            }
        ]
    }

    with pytest.raises(ValueError, match="invalid NOT_EQ audit classification"):
        validate_not_eq_audit_manifest(audit)


def test_validate_not_eq_audit_manifest_requires_accepted_evidence_for_ground_truth():
    audit = {
        "entries": [
            {
                "classification": "ground_truth_not_eq",
                "oracle_manifest_ref": {"oracle_review_status": "draft"},
                "counterexample_model_ref": {"replay_status": "missing"},
                "sat_unsafety_status": {"status": "not_reported_in_final_payload"},
                "coverage_gap_status": {"status": "not_reported_in_final_payload"},
                "call_memory_effect_status": {"status": "not_reported_in_final_payload"},
            }
        ]
    }

    with pytest.raises(ValueError, match="accepted oracle"):
        validate_not_eq_audit_manifest(audit)


def test_validate_ground_truth_rejects_expected_equivalent_conflict_without_override():
    audit = {"entries": [_complete_ground_truth_entry(include_oracle_exception=False)]}

    with pytest.raises(ValueError, match="expected_equivalent=true"):
        validate_not_eq_audit_manifest(audit)


def test_validate_ground_truth_rejects_incomplete_width_and_ub_proofs():
    entry = _complete_ground_truth_entry()
    entry["input_width_policy"] = {"status": "captured_from_effective_signatures"}
    entry["return_compare_width"] = {"status": "requires_replay_for_width_proof"}
    entry["ub_exclusion_rule"] = {"status": "not_audited"}

    with pytest.raises(ValueError, match="ABI/storage width proof"):
        validate_not_eq_audit_manifest({"entries": [entry]})


def test_validate_ground_truth_accepts_complete_phase_0d_evidence():
    validate_not_eq_audit_manifest({"entries": [_complete_ground_truth_entry()]})


def _complete_ground_truth_entry(include_oracle_exception=True):
    oracle_exception = {"status": "accepted", "review_status": "accepted"}
    entry = {
        "classification": "ground_truth_not_eq",
        "expected_equivalent": True,
        "oracle_manifest_ref": {
            "oracle_review_status": "accepted",
            "expected_equivalent": True,
        },
        "oracle_exception": oracle_exception,
        "eq_goal_exclusion": {"status": "missing"},
        "counterexample_model_ref": {
            "counterexample_present": True,
            "solver_model_present": True,
            "replay_status": "replayed",
        },
        "replay_harness": {"status": "available"},
        "sat_unsafety_status": {"status": "not_reported_in_final_payload"},
        "coverage_status": {
            "status": "reported_pairwise_no_unknown_or_error_pairs",
            "unknown_pairs": 0,
            "error_pairs": 0,
        },
        "coverage_gap_status": {"status": "not_reported_in_final_payload"},
        "call_memory_effect_status": {"status": "not_reported_in_final_payload"},
        "input_width_policy": {"status": "abi_storage_width_proven"},
        "return_compare_width": {"status": "smt_type_widths_proven"},
        "ub_exclusion_rule": {"status": "proven"},
    }
    if not include_oracle_exception:
        entry.pop("oracle_exception", None)
    return entry
