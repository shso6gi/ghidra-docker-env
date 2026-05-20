# -*- coding: utf-8 -*-

import json
from pathlib import Path

import pytest

from scripts.function_tracer_pcode.equivalence.strategies.base import CheckStrategy
from scripts.function_tracer_pcode.equivalence.unknown_reason import (
    UnknownRecoveryActionStatus,
    UnknownReasonId,
    make_unknown_reason,
)
from scripts.function_tracer_pcode.model import Expression, ReturnInfo
from scripts.function_tracer_pcode.model.runtime_refs import PcodeOpRef
from scripts.function_tracer_pcode.validation.phase3_return_coverage_lane1 import (
    DEFAULT_REPRESENTATIVES,
    FUNCTION_CALL_BINARY_NAMES,
    _object_target_key_is_specific,
    build_phase3_return_coverage_lane1_manifest,
    validate_phase3_return_coverage_lane1_manifest,
)
from scripts.function_tracer_pcode.validation.unknown_reason_summary import (
    RESULT_JSON_BEGIN,
    RESULT_JSON_END,
)


class _NoopStrategy(CheckStrategy):
    def check(self, analysis1, analysis2, save_formula=False):
        raise NotImplementedError


REPRESENTATIVES = (
    ("fc_recursive_sum", "B11", "B15", ("function2:return_coverage_gap",)),
    (
        "fc_is_even",
        "B11",
        "B12",
        ("function1:return_coverage_gap", "function2:return_coverage_gap"),
    ),
)

RETIRED_TRANSITIONS = (
    ("fc_is_odd", "B15", "B8", "B8", "B15"),
    ("fc_is_odd", "B11", "B16", "B11", "B16"),
    ("fc_is_odd", "B12", "B16", "B12", "B16"),
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
    side = ref.split(":", 1)[0]
    return make_unknown_reason(
        reason_id,
        stage="S_PAIRWISE",
        detail=ref,
        evidence_refs=(ref,),
        object_target_key=(
            "return_coverage",
            side,
            ("function_ref", ("function", side, 0x1000)),
            reason_id,
            ("return_storage", "return_value", 32, False, "int"),
            (
                "return_partition",
                (
                    (
                        "return_case",
                        0,
                        "0x1000",
                        ("pcode_op", "ram", 0x1000, "ram", 0x1004, 0, "RETURN", 0),
                        None,
                        0,
                        ("expression", ("constant", 1, 4)),
                        (("return_guard", False, ("condition", side), ("expression", ("parameter", "x", 0, 4))),),
                    ),
                ),
            ),
            (
                "guard_disjunction",
                (
                    (
                        0,
                        (("return_guard", False, ("condition", side), ("expression", ("parameter", "x", 0, 4))),),
                    ),
                ),
            ),
        ),
        recovery_action="return_coverage_proof_required",
        action_status=UnknownRecoveryActionStatus.PENDING_PROOF,
    )


def _legacy_reason_from_ref(ref: str):
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


def _write_eq_log(root: Path, function: str, left: str, right: str):
    path = root / function / f"{function}_{left}_{right}.log"
    path.parent.mkdir(parents=True, exist_ok=True)
    payload = _payload(
        function,
        _payload_binary_name(left),
        _payload_binary_name(right),
        [],
    )
    payload["is_equivalent"] = True
    payload["debug_trace"]["final_result"] = True
    payload["debug_trace"]["attempts"][0]["result"] = True
    payload["unknown_reasons"] = []
    payload["debug_trace"]["unknown_reasons"] = []
    path.write_text(
        "\n".join(
            [
                "Result: EQUIVALENT",
                RESULT_JSON_BEGIN,
                json.dumps(payload),
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


def _write_retired_transition_logs(baseline_root: Path, current_root: Path):
    for function, baseline_left, baseline_right, current_left, current_right in RETIRED_TRANSITIONS:
        _write_log(
            baseline_root,
            function,
            baseline_left,
            baseline_right,
            [
                _legacy_reason_from_ref("function1:return_coverage_gap"),
                _legacy_reason_from_ref("function2:return_coverage_inconclusive"),
            ],
        )
        _write_log(
            current_root,
            function,
            current_left,
            current_right,
            [
                _reason_from_ref("function1:return_coverage_gap"),
                _reason_from_ref("function2:return_coverage_gap"),
            ],
        )


def _write_minimal_phase1_manifests(phase1_dir: Path):
    phase1_dir.mkdir(parents=True)
    (phase1_dir / "positive_manifest.json").write_text(
        json.dumps(
            {
                "entries": [
                    {
                        "id": "positive-fixture-eq",
                        "category": "function_call",
                        "function": "fc_positive_fixture",
                        "binary_pair": "B11_B12",
                    }
                ]
            }
        )
    )
    (phase1_dir / "negative_manifest.json").write_text(
        json.dumps(
            {
                "entries": [
                    {
                        "id": "negative-inconclusive-return-coverage-near-miss",
                        "category": "function_call",
                        "function": "fc_is_odd",
                        "binary_pair": "B11_B16",
                        "expected_result": "UNKNOWN",
                        "must_not_be_equivalent": True,
                        "required_reason_ids": ["return_coverage_inconclusive"],
                    }
                ]
            }
        )
    )


def test_build_phase3_return_coverage_manifest_freezes_concrete_representatives(tmp_path):
    raw_dir = tmp_path / "baseline" / "raw"
    current_root = tmp_path / "current" / "function_call"
    baseline_root = tmp_path / "baseline_logs" / "function_call"
    phase1_dir = tmp_path / "phase1"
    _write_artifact_manifest(raw_dir)
    _write_representative_logs(current_root)
    _write_representative_logs(baseline_root)
    _write_retired_transition_logs(baseline_root, current_root)
    _write_eq_log(current_root, "fc_positive_fixture", "B11", "B12")
    _write_minimal_phase1_manifests(phase1_dir)

    path = build_phase3_return_coverage_lane1_manifest(
        baseline_raw_dir=raw_dir,
        output_dir=tmp_path / "phase3",
        current_log_roots={"function_call": current_root},
        baseline_log_roots={"function_call": baseline_root},
        phase1_dir=phase1_dir,
    )

    manifest = json.loads(path.read_text())
    assert manifest["baseline_id"] == "observed-v0@0a53352"
    assert manifest["phase3_lane1_ready"] is True
    assert manifest["target_reason_ids"] == ["return_coverage_gap"]
    assert manifest["retired_reason_ids"] == ["return_coverage_inconclusive"]
    assert manifest["readiness"]["covered_target_reason_ids"] == ["return_coverage_gap"]
    assert {entry["selection_status"] for entry in manifest["entries"]} == {"ready"}
    assert {entry["selection_status"] for entry in manifest["retired_transitions"]} == {
        "retired_by_reclassification"
    }
    retired_inventory = manifest["retired_reason_inventory"]["return_coverage_inconclusive"]
    assert retired_inventory["status"] == "retired_by_reclassification"
    assert retired_inventory["reason_record"]["baseline_tuple_counts"] == [
        {
            "count": 3,
            "tuple": [
                "reason_record",
                "return_coverage_inconclusive",
                "blocks_decision",
                "function",
                "return_coverage_completion",
                "return_coverage_smt_disambiguation",
                "<missing>",
            ],
        }
    ]
    assert retired_inventory["reason_record"]["current_tuple_counts"] == []
    assert retired_inventory["proof_action"]["baseline_tuple_counts"] == [
        {
            "count": 3,
            "tuple": [
                "proof_action",
                "return_coverage_inconclusive",
                "blocks_decision",
                "function",
                "return_coverage_completion",
                "return_coverage_smt_disambiguation",
                "planned",
            ],
        }
    ]
    assert retired_inventory["proof_action"]["current_tuple_counts"] == []
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
        "pending_proof",
    ]
    assert recursive["expected_movements"][0]["expected_evidence_refs"] == [
        "function2:return_coverage_gap"
    ]
    assert recursive["current_observation"]["proof_action_tuples"]
    action = recursive["current_observation"]["proof_actions"][0]
    assert action["status"] == "pending_proof"
    assert action["object_target_key"][0] == "return_coverage"
    assert action["proof_obligation_id"][0] == "return_coverage_gap"
    assert action["proof_obligation_id"][3] == "missing_return_guard"
    transition = next(
        item
        for item in manifest["retired_transitions"]
        if item["binary_pair"] == "B8_B15"
    )
    assert transition["baseline_observation"]["observed_left_binary_id"] == "B15"
    assert transition["baseline_observation"]["observed_right_binary_id"] == "B8"
    assert transition["current_observation"]["observed_reason_ids"] == ["return_coverage_gap"]
    assert transition["final_result_invariant"] == {
        "baseline_final_result": "UNKNOWN",
        "current_final_result": "UNKNOWN",
        "false_eq": False,
        "final_result_unchanged_unknown": True,
        "timeout": False,
    }
    implementation = manifest["implementation_manifest"]
    assert implementation["active_target_reason_id"] == "return_coverage_gap"
    assert implementation["proof_completion_gate"] == {
        "completion_required_for_recovery": [
            "return_partition_extraction",
            "return_guard_coverage",
        ],
        "eq_allowed_without_completed_proof": False,
        "pending_proof_keeps_final_result": "UNKNOWN",
        "required_recovery_action": "return_coverage_proof_required",
    }
    pre_fix_gate = manifest["pre_fix_regression_gate"]
    assert pre_fix_gate["ready"] is True
    assert pre_fix_gate["summary"]["failed_kinds"] == []
    assert "current_logs_exact_match" in pre_fix_gate["summary"]["locked_gates"]
    assert "return_coverage_gap_object_evidence_proof_id" in {
        check["kind"] for check in pre_fix_gate["checks"]
    }
    validate_phase3_return_coverage_lane1_manifest(manifest)


def test_phase3_return_coverage_pre_fix_gate_checks_phase1_positive_negative(tmp_path):
    raw_dir = tmp_path / "baseline" / "raw"
    current_root = tmp_path / "current" / "function_call"
    baseline_root = tmp_path / "baseline_logs" / "function_call"
    phase1_dir = tmp_path / "phase1"
    _write_artifact_manifest(raw_dir)
    _write_representative_logs(current_root)
    _write_representative_logs(baseline_root)
    _write_retired_transition_logs(baseline_root, current_root)
    _write_eq_log(current_root, "fc_positive_fixture", "B11", "B12")
    _write_minimal_phase1_manifests(phase1_dir)

    path = build_phase3_return_coverage_lane1_manifest(
        baseline_raw_dir=raw_dir,
        output_dir=tmp_path / "phase3",
        current_log_roots={"function_call": current_root},
        baseline_log_roots={"function_call": baseline_root},
        phase1_dir=phase1_dir,
    )

    manifest = json.loads(path.read_text())
    checks = manifest["pre_fix_regression_gate"]["checks"]
    assert manifest["phase3_lane1_ready"] is True
    assert {
        (check["kind"], check.get("entry_id"), check["status"])
        for check in checks
        if check["kind"] in {
            "positive_representative_non_regression",
            "negative_representative_non_regression",
        }
    } == {
        ("positive_representative_non_regression", "positive-fixture-eq", "ok"),
        (
            "negative_representative_non_regression",
            "negative-inconclusive-return-coverage-near-miss",
            "ok",
        ),
    }
    negative_check = next(
        check
        for check in checks
        if check.get("entry_id") == "negative-inconclusive-return-coverage-near-miss"
    )
    assert (
        negative_check["reclassification"]
        == "return_coverage_inconclusive_retired_to_return_coverage_gap"
    )


def test_phase3_return_coverage_pre_fix_gate_rejects_missing_phase1_dir(tmp_path):
    raw_dir = tmp_path / "baseline" / "raw"
    current_root = tmp_path / "current" / "function_call"
    baseline_root = tmp_path / "baseline_logs" / "function_call"
    _write_artifact_manifest(raw_dir)
    _write_representative_logs(current_root)
    _write_representative_logs(baseline_root)
    _write_retired_transition_logs(baseline_root, current_root)

    path = build_phase3_return_coverage_lane1_manifest(
        baseline_raw_dir=raw_dir,
        output_dir=tmp_path / "phase3",
        current_log_roots={"function_call": current_root},
        baseline_log_roots={"function_call": baseline_root},
        phase1_dir=tmp_path / "definitely-missing-phase1",
    )

    manifest = json.loads(path.read_text())
    assert manifest["phase3_lane1_ready"] is False
    assert manifest["pre_fix_regression_gate"]["summary"]["failed_kinds"] == [
        "phase1_positive_negative_manifest_available"
    ]
    with pytest.raises(ValueError, match="phase1_positive_negative_manifest_available"):
        validate_phase3_return_coverage_lane1_manifest(manifest)


def test_phase3_return_coverage_pre_fix_gate_does_not_use_baseline_for_missing_current(tmp_path):
    raw_dir = tmp_path / "baseline" / "raw"
    current_root = tmp_path / "current" / "function_call"
    baseline_root = tmp_path / "baseline_logs" / "function_call"
    phase1_dir = tmp_path / "phase1"
    _write_artifact_manifest(raw_dir)
    _write_representative_logs(current_root)
    _write_representative_logs(baseline_root)
    _write_retired_transition_logs(baseline_root, current_root)
    _write_eq_log(current_root, "fc_positive_fixture", "B11", "B12")
    _write_log(
        baseline_root,
        "fc_missing_current_negative",
        "B11",
        "B12",
        [_reason_from_ref("function1:return_coverage_gap")],
    )
    phase1_dir.mkdir(parents=True)
    (phase1_dir / "positive_manifest.json").write_text(
        json.dumps(
            {
                "entries": [
                    {
                        "id": "positive-fixture-eq",
                        "category": "function_call",
                        "function": "fc_positive_fixture",
                        "binary_pair": "B11_B12",
                    }
                ]
            }
        )
    )
    (phase1_dir / "negative_manifest.json").write_text(
        json.dumps(
            {
                "entries": [
                    {
                        "id": "negative-missing-current",
                        "category": "function_call",
                        "function": "fc_missing_current_negative",
                        "binary_pair": "B11_B12",
                        "expected_result": "UNKNOWN",
                        "must_not_be_equivalent": True,
                        "required_reason_ids": ["return_coverage_gap"],
                    }
                ]
            }
        )
    )

    path = build_phase3_return_coverage_lane1_manifest(
        baseline_raw_dir=raw_dir,
        output_dir=tmp_path / "phase3",
        current_log_roots={"function_call": current_root},
        baseline_log_roots={"function_call": baseline_root},
        phase1_dir=phase1_dir,
    )

    manifest = json.loads(path.read_text())
    assert manifest["phase3_lane1_ready"] is False
    failed = [
        check
        for check in manifest["pre_fix_regression_gate"]["checks"]
        if check.get("entry_id") == "negative-missing-current"
    ]
    assert failed == [
        {
            "kind": "negative_representative_non_regression",
            "status": "failed",
            "entry_id": "negative-missing-current",
            "error": "missing log",
        }
    ]


def test_phase3_return_coverage_manifest_allows_legacy_baseline_missing_action_detail(tmp_path):
    raw_dir = tmp_path / "baseline" / "raw"
    current_root = tmp_path / "current" / "function_call"
    baseline_root = tmp_path / "baseline_logs" / "function_call"
    phase1_dir = tmp_path / "phase1"
    _write_artifact_manifest(raw_dir)
    _write_representative_logs(current_root)
    _write_representative_logs(baseline_root)
    phase1_dir.mkdir(parents=True)
    (phase1_dir / "positive_manifest.json").write_text(json.dumps({"entries": []}))
    (phase1_dir / "negative_manifest.json").write_text(json.dumps({"entries": []}))
    legacy_baseline_reason = [
        make_unknown_reason(
            UnknownReasonId.RETURN_COVERAGE_GAP,
            stage="S_PAIRWISE",
            detail="function2:return_coverage_gap",
            evidence_refs=("function2:return_coverage_gap",),
        )
    ]
    _write_log(baseline_root, "fc_recursive_sum", "B11", "B15", legacy_baseline_reason)

    path = build_phase3_return_coverage_lane1_manifest(
        baseline_raw_dir=raw_dir,
        output_dir=tmp_path / "phase3",
        current_log_roots={"function_call": current_root},
        baseline_log_roots={"function_call": baseline_root},
        phase1_dir=phase1_dir,
        retired_transitions=(),
    )

    manifest = json.loads(path.read_text())
    assert manifest["phase3_lane1_ready"] is True
    recursive = manifest["entries"][0]
    assert recursive["baseline_observation"]["reason_record_tuples"] == [
        [
            "reason_record",
            "return_coverage_gap",
            "blocks_equivalence",
            "function",
            "return_coverage_completion",
            "<missing>",
            "<missing>",
        ]
    ]
    assert recursive["current_observation"]["reason_record_tuples"] == [
        [
            "reason_record",
            "return_coverage_gap",
            "blocks_equivalence",
            "function",
            "return_coverage_completion",
            "<missing>",
            "pending_proof",
        ]
    ]
    validate_phase3_return_coverage_lane1_manifest(manifest)


def test_phase3_return_coverage_manifest_rejects_current_inconclusive_not_retired(tmp_path):
    raw_dir = tmp_path / "baseline" / "raw"
    current_root = tmp_path / "current" / "function_call"
    baseline_root = tmp_path / "baseline_logs" / "function_call"
    _write_artifact_manifest(raw_dir)
    _write_representative_logs(current_root)
    _write_representative_logs(baseline_root)
    _write_retired_transition_logs(baseline_root, current_root)
    _write_log(
        current_root,
        "fc_is_odd",
        "B11",
        "B16",
        [
            _reason_from_ref("function1:return_coverage_gap"),
            _reason_from_ref("function2:return_coverage_gap"),
            _reason_from_ref("function2:return_coverage_inconclusive"),
        ],
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
    assert "current_retired_reason_still_active:return_coverage_inconclusive" in failures
    assert "retired_reason_inventory_mismatch:return_coverage_inconclusive" in failures


def test_phase3_return_coverage_manifest_rejects_retired_baseline_tuple_drift(tmp_path):
    raw_dir = tmp_path / "baseline" / "raw"
    current_root = tmp_path / "current" / "function_call"
    baseline_root = tmp_path / "baseline_logs" / "function_call"
    _write_artifact_manifest(raw_dir)
    _write_representative_logs(current_root)
    _write_representative_logs(baseline_root)
    _write_retired_transition_logs(baseline_root, current_root)
    _write_log(
        baseline_root,
        "fc_is_odd",
        "B11",
        "B16",
        [
            _legacy_reason_from_ref("function1:return_coverage_gap"),
            _reason_from_ref("function2:return_coverage_inconclusive"),
        ],
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
    assert "baseline_retired_reason_tuple_missing:return_coverage_inconclusive" in failures
    assert "baseline_retired_proof_action_tuple_missing:return_coverage_inconclusive" in failures
    assert "retired_reason_inventory_mismatch:return_coverage_inconclusive" in failures


def test_phase3_return_coverage_manifest_requires_current_active_reason(tmp_path):
    raw_dir = tmp_path / "baseline" / "raw"
    current_root = tmp_path / "current" / "function_call"
    baseline_root = tmp_path / "baseline_logs" / "function_call"
    _write_artifact_manifest(raw_dir)
    _write_representative_logs(current_root)
    _write_representative_logs(baseline_root)
    _write_log(
        current_root,
        "fc_recursive_sum",
        "B11",
        "B15",
        [make_unknown_reason(UnknownReasonId.RETURN_COVERAGE_INCONCLUSIVE)],
    )

    path = build_phase3_return_coverage_lane1_manifest(
        baseline_raw_dir=raw_dir,
        output_dir=tmp_path / "phase3",
        current_log_roots={"function_call": current_root},
        baseline_log_roots={"function_call": baseline_root},
        retired_transitions=(),
    )

    manifest = json.loads(path.read_text())
    assert manifest["phase3_lane1_ready"] is False
    assert "current_missing_return_coverage_gap" in manifest["readiness"]["failure_kinds"]
    with pytest.raises(ValueError, match="current_missing_return_coverage_gap"):
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
    movements[2]["required_evidence"] = [
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
        retired_transitions=(),
    )

    manifest = json.loads(path.read_text())
    assert manifest["phase3_lane1_ready"] is False
    assert (
        "current_expected_proof_action_evidence_mismatch:gap-return-partition-extraction-function1"
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
        retired_transitions=(),
    )

    manifest = json.loads(path.read_text())
    assert manifest["phase3_lane1_ready"] is False
    assert "current_expected_reason_tuple_missing:gap-reason-record" in manifest["readiness"]["failure_kinds"]


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
        retired_transitions=(),
    )

    manifest = json.loads(path.read_text())
    assert manifest["phase3_lane1_ready"] is False
    failures = manifest["readiness"]["failure_kinds"]
    assert "current_expected_reason_scope_mismatch:gap-reason-record" in failures
    assert "current_expected_proof_action_scope_mismatch:gap-return-partition-extraction" in failures
    assert "current_expected_proof_action_scope_mismatch:gap-return-guard-coverage" in failures


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
        retired_transitions=(),
    )

    manifest = json.loads(path.read_text())
    assert manifest["phase3_lane1_ready"] is False
    failures = manifest["readiness"]["failure_kinds"]
    assert "current_expected_reason_evidence_refs_mismatch:gap-reason-record-function2" in failures
    assert (
        "current_expected_proof_action_evidence_refs_mismatch:gap-return-partition-extraction-function2"
        in failures
    )


def test_phase3_return_coverage_manifest_binds_detail_to_same_side_candidate(tmp_path):
    raw_dir = tmp_path / "baseline" / "raw"
    current_root = tmp_path / "current" / "function_call"
    baseline_root = tmp_path / "baseline_logs" / "function_call"
    _write_artifact_manifest(raw_dir)
    _write_representative_logs(current_root)
    _write_representative_logs(baseline_root)
    function2_legacy_reason = make_unknown_reason(
        UnknownReasonId.RETURN_COVERAGE_GAP,
        stage="S_PAIRWISE",
        detail="function2:return_coverage_gap",
        evidence_refs=("function2:return_coverage_gap",),
        recovery_action="return_coverage_proof_required",
        action_status=UnknownRecoveryActionStatus.PENDING_PROOF,
    )
    _write_log(
        current_root,
        "fc_is_even",
        "B11",
        "B12",
        [
            _reason_from_ref("function1:return_coverage_gap"),
            function2_legacy_reason,
        ],
    )

    path = build_phase3_return_coverage_lane1_manifest(
        baseline_raw_dir=raw_dir,
        output_dir=tmp_path / "phase3",
        current_log_roots={"function_call": current_root},
        baseline_log_roots={"function_call": baseline_root},
        retired_transitions=(),
    )

    manifest = json.loads(path.read_text())
    assert manifest["phase3_lane1_ready"] is False
    failures = manifest["readiness"]["failure_kinds"]
    assert "current_expected_reason_object_target_mismatch:gap-reason-record-function2" in failures
    assert (
        "current_expected_proof_action_object_target_mismatch:gap-return-partition-extraction-function2"
        in failures
    )
    assert (
        "current_expected_proof_action_id_mismatch:gap-return-partition-extraction-function2"
        in failures
    )
    assert "current_expected_reason_object_target_mismatch:gap-reason-record-function1" not in failures


def test_phase3_return_coverage_manifest_rejects_missing_object_proof_detail(tmp_path):
    raw_dir = tmp_path / "baseline" / "raw"
    current_root = tmp_path / "current" / "function_call"
    baseline_root = tmp_path / "baseline_logs" / "function_call"
    _write_artifact_manifest(raw_dir)
    _write_representative_logs(current_root)
    _write_representative_logs(baseline_root)
    legacy_reason = [
        make_unknown_reason(
            UnknownReasonId.RETURN_COVERAGE_GAP,
            stage="S_PAIRWISE",
            detail="function2:return_coverage_gap",
            evidence_refs=("function2:return_coverage_gap",),
            recovery_action="return_coverage_proof_required",
            action_status=UnknownRecoveryActionStatus.PENDING_PROOF,
        )
    ]
    _write_log(current_root, "fc_recursive_sum", "B11", "B15", legacy_reason)
    _write_log(baseline_root, "fc_recursive_sum", "B11", "B15", legacy_reason)

    path = build_phase3_return_coverage_lane1_manifest(
        baseline_raw_dir=raw_dir,
        output_dir=tmp_path / "phase3",
        current_log_roots={"function_call": current_root},
        baseline_log_roots={"function_call": baseline_root},
        retired_transitions=(),
    )

    manifest = json.loads(path.read_text())
    assert manifest["phase3_lane1_ready"] is False
    failures = manifest["readiness"]["failure_kinds"]
    assert "current_expected_reason_object_target_mismatch:gap-reason-record" in failures


def test_phase3_return_coverage_manifest_rejects_weak_return_coverage_object_key(tmp_path):
    raw_dir = tmp_path / "baseline" / "raw"
    current_root = tmp_path / "current" / "function_call"
    baseline_root = tmp_path / "baseline_logs" / "function_call"
    _write_artifact_manifest(raw_dir)
    _write_representative_logs(current_root)
    _write_representative_logs(baseline_root)
    weak_reason = [
        make_unknown_reason(
            UnknownReasonId.RETURN_COVERAGE_GAP,
            stage="S_PAIRWISE",
            detail="function2:return_coverage_gap",
            evidence_refs=("function2:return_coverage_gap",),
            object_target_key=("return_coverage", "function2:return_coverage_gap"),
            recovery_action="return_coverage_proof_required",
            action_status=UnknownRecoveryActionStatus.PENDING_PROOF,
        )
    ]
    _write_log(current_root, "fc_recursive_sum", "B11", "B15", weak_reason)
    _write_log(baseline_root, "fc_recursive_sum", "B11", "B15", weak_reason)

    path = build_phase3_return_coverage_lane1_manifest(
        baseline_raw_dir=raw_dir,
        output_dir=tmp_path / "phase3",
        current_log_roots={"function_call": current_root},
        baseline_log_roots={"function_call": baseline_root},
        retired_transitions=(),
    )

    manifest = json.loads(path.read_text())
    assert manifest["phase3_lane1_ready"] is False
    failures = manifest["readiness"]["failure_kinds"]
    assert "current_expected_reason_object_target_mismatch:gap-reason-record" in failures


def test_phase3_return_coverage_manifest_rejects_log_prose_return_coverage_object_key(tmp_path):
    raw_dir = tmp_path / "baseline" / "raw"
    current_root = tmp_path / "current" / "function_call"
    baseline_root = tmp_path / "baseline_logs" / "function_call"
    _write_artifact_manifest(raw_dir)
    _write_representative_logs(current_root)
    _write_representative_logs(baseline_root)
    prose_reason = [
        make_unknown_reason(
            UnknownReasonId.RETURN_COVERAGE_GAP,
            stage="S_PAIRWISE",
            detail="function2:return_coverage_gap",
            evidence_refs=("function2:return_coverage_gap",),
            object_target_key=(
                "return_coverage",
                "function2",
                ("function_ref", ("function", 2, 0x1000)),
                "return_coverage_gap",
                ("return_storage", "return_value", 32, False, "int"),
                (
                    "return_partition",
                    (
                        (
                            "return_case",
                            0,
                            "function2:return_coverage_gap",
                            None,
                            None,
                            None,
                            ("expression", "function2:return_coverage_gap"),
                            (
                                (
                                    "return_guard",
                                    False,
                                    ("condition", "function2:return_coverage_gap"),
                                    ("expression", "function2:return_coverage_gap"),
                                ),
                            ),
                        ),
                    ),
                ),
                (
                    "guard_disjunction",
                    (
                        (
                            0,
                            (
                                (
                                    "return_guard",
                                    False,
                                    ("condition", "function2:return_coverage_gap"),
                                    ("expression", "function2:return_coverage_gap"),
                                ),
                            ),
                        ),
                    ),
                ),
            ),
            recovery_action="return_coverage_proof_required",
            action_status=UnknownRecoveryActionStatus.PENDING_PROOF,
        )
    ]
    _write_log(current_root, "fc_recursive_sum", "B11", "B15", prose_reason)
    _write_log(baseline_root, "fc_recursive_sum", "B11", "B15", prose_reason)

    path = build_phase3_return_coverage_lane1_manifest(
        baseline_raw_dir=raw_dir,
        output_dir=tmp_path / "phase3",
        current_log_roots={"function_call": current_root},
        baseline_log_roots={"function_call": baseline_root},
    )

    manifest = json.loads(path.read_text())
    assert manifest["phase3_lane1_ready"] is False
    failures = manifest["readiness"]["failure_kinds"]
    assert "current_expected_reason_object_target_mismatch:gap-reason-record" in failures


def test_return_coverage_object_key_specificity_requires_function_entry_and_pcode_location():
    weak_key = (
        "return_coverage",
        "function2",
        ("function_ref", ("function", None, None)),
        "return_coverage_gap",
        ("return_storage", "return_value", 32, False, "int"),
        (
            "return_partition",
            (
                (
                    "return_case",
                    0,
                    "0x1000",
                    ("pcode_op", None, None, None, None, "RETURN"),
                    None,
                    None,
                    ("expression", ("constant", 1, 4)),
                    (
                        (
                            "return_guard",
                            False,
                            ("condition", ("INT_EQUAL", "x", 0)),
                            ("expression", ("parameter", "x", 0, 4)),
                        ),
                    ),
                ),
            ),
        ),
        (
            "guard_disjunction",
            (
                (
                    0,
                    (
                        (
                            "return_guard",
                            False,
                            ("condition", ("INT_EQUAL", "x", 0)),
                            ("expression", ("parameter", "x", 0, 4)),
                        ),
                    ),
                ),
            ),
        ),
    )
    good_key = (
        "return_coverage",
        "function2",
        ("function_ref", ("function", None, 0x1000)),
        "return_coverage_gap",
        ("return_storage", "return_value", 32, False, "int"),
        (
            "return_partition",
            (
                (
                    "return_case",
                    0,
                    "0x1000",
                    ("pcode_op", 0x1010, 0x1010, 3, 1, "RETURN"),
                    None,
                    None,
                    ("expression", ("constant", 1, 4)),
                    (
                        (
                            "return_guard",
                            False,
                            ("condition", ("INT_EQUAL", "x", 0)),
                            ("expression", ("parameter", "x", 0, 4)),
                        ),
                    ),
                ),
            ),
        ),
        (
            "guard_disjunction",
            (
                (
                    0,
                    (
                        (
                            "return_guard",
                            False,
                            ("condition", ("INT_EQUAL", "x", 0)),
                            ("expression", ("parameter", "x", 0, 4)),
                        ),
                    ),
                ),
            ),
        ),
    )

    assert _object_target_key_is_specific(weak_key) is False
    assert _object_target_key_is_specific(good_key) is True


def test_return_coverage_object_key_specificity_rejects_address_only_return_case():
    address_only_key = (
        "return_coverage",
        "function2",
        ("function_ref", ("function", None, 0x1000)),
        "return_coverage_gap",
        ("return_storage", "return_value", 32, False, "int"),
        (
            "return_partition",
            (
                (
                    "return_case",
                    0,
                    "0x1000",
                    None,
                    None,
                    None,
                    ("expression", ("constant", 1, 4)),
                    (
                        (
                            "return_guard",
                            False,
                            ("condition", ("INT_EQUAL", "x", 0)),
                            ("expression", ("parameter", "x", 0, 4)),
                        ),
                    ),
                ),
            ),
        ),
        (
            "guard_disjunction",
            (
                (
                    0,
                    (
                        (
                            "return_guard",
                            False,
                            ("condition", ("INT_EQUAL", "x", 0)),
                            ("expression", ("parameter", "x", 0, 4)),
                        ),
                    ),
                ),
            ),
        ),
    )
    structured_identity_key = (
        "return_coverage",
        "function2",
        ("function_ref", ("function", None, 0x1000)),
        "return_coverage_gap",
        ("return_storage", "return_value", 32, False, "int"),
        (
            "return_partition",
            (
                (
                    "return_case",
                    0,
                    "0x1000",
                    None,
                    ("pcode_op", 0x1010, 0x1010, 3, 1, "RETURN"),
                    None,
                    ("expression", ("constant", 1, 4)),
                    (
                        (
                            "return_guard",
                            False,
                            ("condition", ("INT_EQUAL", "x", 0)),
                            ("expression", ("parameter", "x", 0, 4)),
                        ),
                    ),
                ),
            ),
        ),
        (
            "guard_disjunction",
            (
                (
                    0,
                    (
                        (
                            "return_guard",
                            False,
                            ("condition", ("INT_EQUAL", "x", 0)),
                            ("expression", ("parameter", "x", 0, 4)),
                        ),
                    ),
                ),
            ),
        ),
    )

    assert _object_target_key_is_specific(address_only_key) is False
    assert _object_target_key_is_specific(structured_identity_key) is True


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
        retired_transitions=(),
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
        retired_transitions=(),
    )

    manifest = json.loads(path.read_text())
    assert manifest["phase3_lane1_ready"] is False
    failures = manifest["readiness"]["failure_kinds"]
    assert "current_observed_payload_direction_mismatch" in failures
    assert "baseline_observed_payload_direction_mismatch" in failures


def test_return_coverage_object_key_requires_object_derived_pcode_ref():
    strategy = _NoopStrategy(None, None)
    legacy_ret = ReturnInfo(
        address="ram:00401000",
        value=Expression.constant(0, 4),
        conditions=[],
        pcode_identity="ram:00401000:t23:o1",
        pcode_order=1,
        pcode_time=23,
    )
    object_ret = ReturnInfo(
        address="ram:00401000",
        value=Expression.constant(0, 4),
        conditions=[],
        pcode_identity="ram:00401000:t23:o1",
        pcode_order=1,
        pcode_time=23,
        pcode_op_ref=PcodeOpRef(
            address_offset=0x401000,
            seq_time=23,
            seq_order=1,
            block_index=4,
            mnemonic="RETURN",
        ),
    )

    legacy_key = strategy._return_case_object_key(0, legacy_ret)
    object_key = strategy._return_case_object_key(0, object_ret)

    assert legacy_key[3] is None
    assert object_key[3] == ("pcode_op", 0x401000, 23, 1, 4, "RETURN")
