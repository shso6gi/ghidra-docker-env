# -*- coding: utf-8 -*-

import json
from pathlib import Path

import pytest

from scripts.function_tracer_pcode.equivalence.unknown_reason import (
    UnknownReasonId,
    make_unknown_reason,
)
from scripts.function_tracer_pcode.validation.phase3_return_coverage_lane1 import (
    DEFAULT_REPRESENTATIVES,
    FUNCTION_CALL_BINARY_NAMES,
    build_phase3_return_coverage_lane1_manifest,
    validate_phase3_return_coverage_lane1_manifest,
)
from scripts.function_tracer_pcode.validation.unknown_reason_summary import (
    RESULT_JSON_BEGIN,
    RESULT_JSON_END,
)


REPRESENTATIVES = (
    ("fc_recursive_sum", "B11", "B15", ("function2:return_coverage_gap",)),
    (
        "fc_is_odd",
        "B11",
        "B16",
        ("function1:return_coverage_gap", "function2:return_coverage_inconclusive"),
    ),
    (
        "fc_is_even",
        "B11",
        "B12",
        ("function1:return_coverage_gap", "function2:return_coverage_gap"),
    ),
)


def _write_artifact_manifest(root: Path):
    root.mkdir(parents=True)
    (root / "artifact_manifest.json").write_text(
        json.dumps(
            {
                "baseline_id": "observed-v0@0a53352",
                "git_head": "0a53352cf3c9528abfb654906ed7b963474bedc5",
            }
        )
    )


def _payload(function: str, left_name: str, right_name: str, reasons):
    return {
        "function1_name": function,
        "function2_name": function,
        "binary1_name": left_name,
        "binary2_name": right_name,
        "is_equivalent": None,
        "is_timeout": False,
        "error_message": None,
        "pairwise_stats": {
            "total_pairs": 4,
            "unsat_pairs": 4,
            "unknown_pairs": 0,
            "sat_pairs": 0,
        },
        "debug_trace": {
            "final_result": None,
            "attempts": [
                {
                    "attempt_id": 0,
                    "phase": "P0_BASE",
                    "result": None,
                    "transition_reason": "UNKNOWN",
                    "pairwise_decisive": {
                        "total_pairs": 4,
                        "unsat_pairs": 4,
                        "unknown_pairs": 0,
                        "sat_pairs": 0,
                    },
                    "solver_results": {"all_results": [{"status": "UNKNOWN"}]},
                    "final_smt": "\n".join(
                        [
                            "; Pairwise Query: Pair (1,0)",
                            "; Case1[1]: (0 < param_1)",
                            "; Case2[0]: (param_1 == 0)",
                            "(check-sat)",
                        ]
                    ),
                    "unknown_reasons": [reason.to_dict() for reason in reasons],
                }
            ],
        },
        "unknown_reasons": [reason.to_dict() for reason in reasons],
    }


def _payload_binary_name(binary_id: str) -> str:
    return FUNCTION_CALL_BINARY_NAMES.get(binary_id, binary_id)


def _reason_from_ref(ref: str):
    reason_id = ref.split(":", 1)[1]
    return make_unknown_reason(
        reason_id,
        stage="S_PAIRWISE",
        detail=ref,
        evidence_refs=(ref,),
    )


def _write_log(root: Path, function: str, left: str, right: str, reasons):
    path = root / function / f"{function}_{left}_{right}.log"
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(
        "\n".join(
            [
                "Result: UNKNOWN",
                RESULT_JSON_BEGIN,
                json.dumps(
                    _payload(
                        function,
                        _payload_binary_name(left),
                        _payload_binary_name(right),
                        reasons,
                    )
                ),
                RESULT_JSON_END,
            ]
        )
    )


def _write_log_with_payload_names(
    root: Path,
    function: str,
    left: str,
    right: str,
    payload_left: str,
    payload_right: str,
    reasons,
):
    path = root / function / f"{function}_{left}_{right}.log"
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(
        "\n".join(
            [
                "Result: UNKNOWN",
                RESULT_JSON_BEGIN,
                json.dumps(
                    _payload(
                        function,
                        _payload_binary_name(payload_left),
                        _payload_binary_name(payload_right),
                        reasons,
                    )
                ),
                RESULT_JSON_END,
            ]
        )
    )


def _write_representative_logs(root: Path):
    for function, left, right, refs in REPRESENTATIVES:
        _write_log(root, function, left, right, [_reason_from_ref(ref) for ref in refs])


def test_build_phase3_return_coverage_manifest_freezes_concrete_representatives(tmp_path):
    raw_dir = tmp_path / "baseline" / "raw"
    current_root = tmp_path / "current" / "function_call"
    baseline_root = tmp_path / "baseline_logs" / "function_call"
    _write_artifact_manifest(raw_dir)
    _write_representative_logs(current_root)
    _write_representative_logs(baseline_root)

    path = build_phase3_return_coverage_lane1_manifest(
        baseline_raw_dir=raw_dir,
        output_dir=tmp_path / "phase3",
        current_log_roots={"function_call": current_root},
        baseline_log_roots={"function_call": baseline_root},
    )

    manifest = json.loads(path.read_text())
    assert manifest["baseline_id"] == "observed-v0@0a53352"
    assert manifest["phase3_lane1_ready"] is True
    assert manifest["readiness"]["covered_target_reason_ids"] == [
        "return_coverage_gap",
        "return_coverage_inconclusive",
    ]
    assert {entry["selection_status"] for entry in manifest["entries"]} == {"ready"}
    recursive = manifest["entries"][0]
    assert recursive["function"] == "fc_recursive_sum"
    assert recursive["binary_pair"] == "B11_B15"
    assert recursive["expected_observed_left_binary_id"] == "B11"
    assert recursive["expected_observed_right_binary_id"] == "B15"
    assert recursive["expected_observed_binary1_name"] == FUNCTION_CALL_BINARY_NAMES["B11"]
    assert recursive["expected_observed_binary2_name"] == FUNCTION_CALL_BINARY_NAMES["B15"]
    assert recursive["current_observation"]["observed_left_binary_id"] == "B11"
    assert recursive["current_observation"]["observed_right_binary_id"] == "B15"
    assert recursive["current_observation"]["observed_binary1_name"] == FUNCTION_CALL_BINARY_NAMES["B11"]
    assert recursive["current_observation"]["observed_binary2_name"] == FUNCTION_CALL_BINARY_NAMES["B15"]
    diagnostic = recursive["current_observation"]["return_case_grid_diagnostic"]
    assert diagnostic["source_kind"] == "raw_smt_diagnostic"
    assert diagnostic["object_derived"] is False
    assert diagnostic["evidence_role"] == "diagnostic_only"
    assert diagnostic["attempts"][0]["rows"] == [
        {
            "pair": [1, 0],
            "case1": {"index": 1, "condition": "(0 < param_1)"},
            "case2": {"index": 0, "condition": "(param_1 == 0)"},
        }
    ]
    assert recursive["expected_movements"][0]["tuple"] == [
        "reason_record",
        "return_coverage_gap",
        "blocks_equivalence",
        "function",
        "return_coverage_completion",
        "<missing>",
        "<missing>",
    ]
    assert recursive["expected_movements"][0]["expected_evidence_refs"] == [
        "function2:return_coverage_gap"
    ]
    assert recursive["current_observation"]["proof_action_tuples"]
    inconclusive = manifest["entries"][1]
    assert inconclusive["expected_movements"][1]["required_evidence"] == [
        "case_guard_disjunction",
        "normalized_guard_formula",
        "solver_model_or_timeout",
    ]
    validate_phase3_return_coverage_lane1_manifest(manifest)


def test_phase3_return_coverage_manifest_requires_baseline_and_current_reasons(tmp_path):
    raw_dir = tmp_path / "baseline" / "raw"
    current_root = tmp_path / "current" / "function_call"
    baseline_root = tmp_path / "baseline_logs" / "function_call"
    _write_artifact_manifest(raw_dir)
    _write_representative_logs(current_root)
    _write_representative_logs(baseline_root)
    missing_reason_log = baseline_root / "fc_is_odd" / "fc_is_odd_B11_B16.log"
    _write_log(
        baseline_root,
        "fc_is_odd",
        "B11",
        "B16",
        [make_unknown_reason(UnknownReasonId.RETURN_COVERAGE_GAP)],
    )
    assert missing_reason_log.is_file()

    path = build_phase3_return_coverage_lane1_manifest(
        baseline_raw_dir=raw_dir,
        output_dir=tmp_path / "phase3",
        current_log_roots={"function_call": current_root},
        baseline_log_roots={"function_call": baseline_root},
    )

    manifest = json.loads(path.read_text())
    assert manifest["phase3_lane1_ready"] is False
    assert "baseline_missing_return_coverage_inconclusive" in manifest["readiness"]["failure_kinds"]
    with pytest.raises(ValueError, match="baseline_missing_return_coverage_inconclusive"):
        validate_phase3_return_coverage_lane1_manifest(manifest)


def test_phase3_return_coverage_manifest_rejects_stale_expected_evidence(tmp_path):
    raw_dir = tmp_path / "baseline" / "raw"
    current_root = tmp_path / "current" / "function_call"
    baseline_root = tmp_path / "baseline_logs" / "function_call"
    _write_artifact_manifest(raw_dir)
    _write_representative_logs(current_root)
    _write_representative_logs(baseline_root)
    representatives = [dict(entry) for entry in DEFAULT_REPRESENTATIVES]
    movements = [dict(item) for item in representatives[1]["expected_movements"]]
    movements[1]["required_evidence"] = [
        "normalized_smt_guard",
        "case_guard_disjunction",
        "path_feasibility",
    ]
    representatives[1]["expected_movements"] = movements

    path = build_phase3_return_coverage_lane1_manifest(
        baseline_raw_dir=raw_dir,
        output_dir=tmp_path / "phase3",
        current_log_roots={"function_call": current_root},
        baseline_log_roots={"function_call": baseline_root},
        representatives=representatives,
    )

    manifest = json.loads(path.read_text())
    assert manifest["phase3_lane1_ready"] is False
    assert (
        "current_expected_proof_action_evidence_mismatch:inconclusive-smt-disambiguation"
        in manifest["readiness"]["failure_kinds"]
    )
    assert (
        "baseline_expected_proof_action_evidence_mismatch:inconclusive-smt-disambiguation"
        in manifest["readiness"]["failure_kinds"]
    )


def test_phase3_return_coverage_manifest_rejects_missing_expected_tuple(tmp_path):
    raw_dir = tmp_path / "baseline" / "raw"
    current_root = tmp_path / "current" / "function_call"
    baseline_root = tmp_path / "baseline_logs" / "function_call"
    _write_artifact_manifest(raw_dir)
    _write_representative_logs(current_root)
    _write_representative_logs(baseline_root)
    representatives = [dict(entry) for entry in DEFAULT_REPRESENTATIVES]
    movements = [dict(item) for item in representatives[0]["expected_movements"]]
    movements[0]["tuple"] = [
        "reason_record",
        "return_coverage_inconclusive",
        "blocks_decision",
        "function",
        "return_coverage_completion",
        "return_coverage_smt_disambiguation",
        "<missing>",
    ]
    representatives[0]["expected_movements"] = movements

    path = build_phase3_return_coverage_lane1_manifest(
        baseline_raw_dir=raw_dir,
        output_dir=tmp_path / "phase3",
        current_log_roots={"function_call": current_root},
        baseline_log_roots={"function_call": baseline_root},
        representatives=representatives,
    )

    manifest = json.loads(path.read_text())
    assert manifest["phase3_lane1_ready"] is False
    assert "current_expected_reason_tuple_missing:gap-reason-record" in manifest["readiness"]["failure_kinds"]
    assert "baseline_expected_reason_tuple_missing:gap-reason-record" in manifest["readiness"]["failure_kinds"]


def test_phase3_return_coverage_manifest_rejects_wrong_expected_scope(tmp_path):
    raw_dir = tmp_path / "baseline" / "raw"
    current_root = tmp_path / "current" / "function_call"
    baseline_root = tmp_path / "baseline_logs" / "function_call"
    _write_artifact_manifest(raw_dir)
    _write_representative_logs(current_root)
    _write_representative_logs(baseline_root)
    representatives = [dict(entry) for entry in DEFAULT_REPRESENTATIVES]
    movements = [dict(item) for item in representatives[0]["expected_movements"]]
    movements[0]["stage"] = "WRONG_STAGE"
    movements[1]["aggregation_unit"] = "wrong_unit"
    movements[2]["pair_or_case"] = "wrong_case"
    representatives[0]["expected_movements"] = movements

    path = build_phase3_return_coverage_lane1_manifest(
        baseline_raw_dir=raw_dir,
        output_dir=tmp_path / "phase3",
        current_log_roots={"function_call": current_root},
        baseline_log_roots={"function_call": baseline_root},
        representatives=representatives,
    )

    manifest = json.loads(path.read_text())
    assert manifest["phase3_lane1_ready"] is False
    failures = manifest["readiness"]["failure_kinds"]
    assert "current_expected_reason_scope_mismatch:gap-reason-record" in failures
    assert "baseline_expected_reason_scope_mismatch:gap-reason-record" in failures
    assert "current_expected_proof_action_scope_mismatch:gap-return-partition-extraction" in failures
    assert "baseline_expected_proof_action_scope_mismatch:gap-return-partition-extraction" in failures
    assert "current_expected_proof_action_scope_mismatch:gap-return-guard-coverage" in failures
    assert "baseline_expected_proof_action_scope_mismatch:gap-return-guard-coverage" in failures


def test_phase3_return_coverage_manifest_rejects_missing_both_side_gap(tmp_path):
    raw_dir = tmp_path / "baseline" / "raw"
    current_root = tmp_path / "current" / "function_call"
    baseline_root = tmp_path / "baseline_logs" / "function_call"
    _write_artifact_manifest(raw_dir)
    _write_representative_logs(current_root)
    _write_representative_logs(baseline_root)
    one_sided = [_reason_from_ref("function1:return_coverage_gap")]
    _write_log(current_root, "fc_is_even", "B11", "B12", one_sided)
    _write_log(baseline_root, "fc_is_even", "B11", "B12", one_sided)

    path = build_phase3_return_coverage_lane1_manifest(
        baseline_raw_dir=raw_dir,
        output_dir=tmp_path / "phase3",
        current_log_roots={"function_call": current_root},
        baseline_log_roots={"function_call": baseline_root},
    )

    manifest = json.loads(path.read_text())
    assert manifest["phase3_lane1_ready"] is False
    failures = manifest["readiness"]["failure_kinds"]
    assert "current_expected_reason_evidence_refs_mismatch:gap-reason-record-function2" in failures
    assert "baseline_expected_reason_evidence_refs_mismatch:gap-reason-record-function2" in failures
    assert (
        "current_expected_proof_action_evidence_refs_mismatch:gap-return-partition-extraction-function2"
        in failures
    )
    assert (
        "baseline_expected_proof_action_evidence_refs_mismatch:gap-return-guard-coverage-function2"
        in failures
    )


def test_phase3_return_coverage_manifest_rejects_reversed_log_direction(tmp_path):
    raw_dir = tmp_path / "baseline" / "raw"
    current_root = tmp_path / "current" / "function_call"
    baseline_root = tmp_path / "baseline_logs" / "function_call"
    _write_artifact_manifest(raw_dir)
    _write_representative_logs(current_root)
    _write_representative_logs(baseline_root)
    reversed_reason = [_reason_from_ref("function2:return_coverage_gap")]
    _write_log(current_root, "fc_recursive_sum", "B15", "B11", reversed_reason)
    _write_log(baseline_root, "fc_recursive_sum", "B15", "B11", reversed_reason)

    path = build_phase3_return_coverage_lane1_manifest(
        baseline_raw_dir=raw_dir,
        output_dir=tmp_path / "phase3",
        current_log_roots={"function_call": current_root},
        baseline_log_roots={"function_call": baseline_root},
    )

    manifest = json.loads(path.read_text())
    assert manifest["phase3_lane1_ready"] is False
    failures = manifest["readiness"]["failure_kinds"]
    assert "current_observed_direction_mismatch" in failures
    assert "baseline_observed_direction_mismatch" in failures


def test_phase3_return_coverage_manifest_rejects_reversed_payload_direction(tmp_path):
    raw_dir = tmp_path / "baseline" / "raw"
    current_root = tmp_path / "current" / "function_call"
    baseline_root = tmp_path / "baseline_logs" / "function_call"
    _write_artifact_manifest(raw_dir)
    _write_representative_logs(current_root)
    _write_representative_logs(baseline_root)
    reversed_reason = [_reason_from_ref("function2:return_coverage_gap")]
    _write_log_with_payload_names(
        current_root,
        "fc_recursive_sum",
        "B11",
        "B15",
        "B15",
        "B11",
        reversed_reason,
    )
    _write_log_with_payload_names(
        baseline_root,
        "fc_recursive_sum",
        "B11",
        "B15",
        "B15",
        "B11",
        reversed_reason,
    )

    path = build_phase3_return_coverage_lane1_manifest(
        baseline_raw_dir=raw_dir,
        output_dir=tmp_path / "phase3",
        current_log_roots={"function_call": current_root},
        baseline_log_roots={"function_call": baseline_root},
    )

    manifest = json.loads(path.read_text())
    assert manifest["phase3_lane1_ready"] is False
    failures = manifest["readiness"]["failure_kinds"]
    assert "current_observed_payload_direction_mismatch" in failures
    assert "baseline_observed_payload_direction_mismatch" in failures
