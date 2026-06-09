# -*- coding: utf-8 -*-

import hashlib
import json
from pathlib import Path

import pytest

import scripts.function_tracer_pcode.validation.phase3_return_coverage_lane1 as lane1_module
from scripts.function_tracer_pcode.equivalence.strategies.base import CheckStrategy
from scripts.function_tracer_pcode.equivalence.unknown_reason import (
    UnknownRecoveryActionStatus,
    UnknownReasonId,
    build_proof_obligation_id,
    build_unknown_recovery_actions,
    make_unknown_reason,
)
from scripts.function_tracer_pcode.model import Expression, ReturnInfo
from scripts.function_tracer_pcode.model.runtime_refs import PcodeOpRef
from scripts.function_tracer_pcode.validation.phase3_return_coverage_lane1 import (
    DEFAULT_REPRESENTATIVES,
    FUNCTION_CALL_BINARY_NAMES,
    _object_target_key_is_specific,
    _validation_records_for_entries,
    build_phase3_return_coverage_lane1_manifest,
    build_phase3_return_coverage_lane1_post_fix_gate,
    main as phase3_return_coverage_lane1_main,
    validate_phase3_return_coverage_lane1_manifest,
    validate_phase3_return_coverage_lane1_post_fix_gate,
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
        "unknown_recovery_actions": [
            action.to_dict() for action in build_unknown_recovery_actions(reasons)
        ],
    }


def _payload_binary_name(binary_id: str) -> str:
    return FUNCTION_CALL_BINARY_NAMES.get(binary_id, binary_id)


def _reason_from_ref(ref: str):
    reason_id = ref.split(":", 1)[1]
    side = ref.split(":", 1)[0]
    binary_id = "B11" if side == "function1" else "B15"
    return make_unknown_reason(
        reason_id,
        stage="S_PAIRWISE",
        detail=ref,
        evidence_refs=(ref,),
        object_target_key=(
            "return_coverage",
            side,
            ("function_ref", ("function", binary_id, 0x1000)),
            reason_id,
            ("return_storage", "return_value", 32, False, "int"),
            (
                "return_partition",
                (
                    (
                        "return_case",
                        0,
                        "0x1000",
                        (
                            "pcode_op",
                            binary_id,
                            ("function_entry", "ram", 0x1000),
                            ("seq_target", "ram", 0x1004),
                            23,
                            0,
                            10,
                            0,
                        ),
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
    _write_payload_log(
        path,
        _payload(
            function,
            _payload_binary_name(left),
            _payload_binary_name(right),
            reasons,
        )
    )


def _write_payload_log(path: Path, payload):
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(
        "\n".join(
            [
                "Result: UNKNOWN",
                RESULT_JSON_BEGIN,
                json.dumps(payload),
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


def _write_completed_eq_log(root: Path, frozen_entry, evidence_updates=None):
    function = frozen_entry["function"]
    left = frozen_entry["expected_observed_left_binary_id"]
    right = frozen_entry["expected_observed_right_binary_id"]
    path = root / function / f"{function}_{left}_{right}.log"
    payload = _payload(
        function,
        frozen_entry["expected_observed_binary1_name"],
        frozen_entry["expected_observed_binary2_name"],
        [],
    )
    payload["is_equivalent"] = True
    payload["decision_gated_by_pending_proof"] = False
    payload["debug_trace"]["final_result"] = True
    payload["debug_trace"]["attempts"][0]["result"] = True
    payload["debug_trace"]["attempts"][0]["unknown_reasons"] = []
    payload["unknown_reasons"] = []
    payload["unknown_recovery_actions"] = []
    evidence_records = []
    for action in frozen_entry["current_observation"]["proof_actions"]:
        if action["reason_id"] != "return_coverage_gap":
            continue
        evidence = {
            "object_derived": True,
            "status": "complete",
            "reason_id": action["reason_id"],
            "recovery_proof_kind": action["proof_kind"],
            "proof_stage": action["proof_stage"],
            "evidence_kind": action["evidence_kind"],
            "object_target_key": action["object_target_key"],
            "proof_obligation_id": action["proof_obligation_id"],
        }
        if evidence_updates:
            evidence.update(evidence_updates)
        evidence_records.append(
            {
                "side": action["object_target_key"][1],
                "function_name": function,
                "binary_name": frozen_entry["expected_observed_binary2_name"],
                "binary_id": action["object_target_key"][2][1][1],
                "evidence": evidence,
            }
        )
    payload["completed_recovery_proof_evidence"] = evidence_records
    _write_payload_log(path, payload)


def _write_completed_unknown_log(root: Path, frozen_entry, reasons, *, numeric_function_identity=False):
    function = frozen_entry["function"]
    left = frozen_entry["expected_observed_left_binary_id"]
    right = frozen_entry["expected_observed_right_binary_id"]
    path = root / function / f"{function}_{left}_{right}.log"
    payload = _payload(
        function,
        frozen_entry["expected_observed_binary1_name"],
        frozen_entry["expected_observed_binary2_name"],
        reasons,
    )
    payload["decision_gated_by_pending_proof"] = False
    evidence_records = []
    for action in frozen_entry["current_observation"]["proof_actions"]:
        if action["reason_id"] != "return_coverage_gap":
            continue
        object_target_key = json.loads(json.dumps(action["object_target_key"]))
        if numeric_function_identity:
            object_target_key[2][1][1] = 3734179612044370016
        evidence_records.append(
            {
                "side": object_target_key[1],
                "function_name": function,
                "binary_name": frozen_entry["expected_observed_binary2_name"],
                "binary_id": object_target_key[2][1][1],
                "evidence": {
                    "object_derived": True,
                    "status": "complete",
                    "reason_id": action["reason_id"],
                    "recovery_proof_kind": action["proof_kind"],
                    "proof_stage": action["proof_stage"],
                    "evidence_kind": action["evidence_kind"],
                    "coverage_status": "covered",
                    "object_target_key": object_target_key,
                    "proof_obligation_id": action["proof_obligation_id"],
                },
            }
        )
    payload["completed_recovery_proof_evidence"] = evidence_records
    _write_payload_log(path, payload)


def _write_completed_eq_log_with_current_return_coverage_targets(
    root: Path,
    frozen_entry,
    *,
    retarget_binary_id: str | None = None,
):
    function = frozen_entry["function"]
    left = frozen_entry["expected_observed_left_binary_id"]
    right = frozen_entry["expected_observed_right_binary_id"]
    path = root / function / f"{function}_{left}_{right}.log"
    payload = _payload(
        function,
        frozen_entry["expected_observed_binary1_name"],
        frozen_entry["expected_observed_binary2_name"],
        [],
    )
    payload["is_equivalent"] = True
    payload["decision_gated_by_pending_proof"] = False
    payload["debug_trace"]["final_result"] = True
    payload["debug_trace"]["attempts"][0]["result"] = True
    payload["debug_trace"]["attempts"][0]["unknown_reasons"] = []
    payload["unknown_reasons"] = []
    payload["unknown_recovery_actions"] = []
    evidence_records = []
    for action in frozen_entry["current_observation"]["proof_actions"]:
        if action["reason_id"] != "return_coverage_gap":
            continue
        current_target = json.loads(json.dumps(action["object_target_key"]))
        if retarget_binary_id is not None:
            current_target = _replace_nested_value(current_target, "B15", retarget_binary_id)
        else:
            current_target[5][1].append(current_target[5][1][-1])
            current_target[6][1].append(current_target[6][1][-1])
        proof_id = build_proof_obligation_id(
            action["reason_id"],
            action["proof_stage"],
            action["proof_kind"],
            action["evidence_kind"],
            current_target,
        )
        evidence_records.append(
            {
                "side": current_target[1],
                "function_name": function,
                "binary_name": frozen_entry["expected_observed_binary2_name"],
                "binary_id": current_target[2][1][1],
                "evidence": {
                    "coverage_status": "covered",
                    "object_derived": True,
                    "status": "complete",
                    "reason_id": action["reason_id"],
                    "recovery_proof_kind": action["proof_kind"],
                    "proof_stage": action["proof_stage"],
                    "evidence_kind": action["evidence_kind"],
                    "object_target_key": current_target,
                    "proof_obligation_id": proof_id,
                },
            }
        )
    payload["completed_recovery_proof_evidence"] = evidence_records
    _write_payload_log(path, payload)


def _replace_nested_value(value, old, new):
    if isinstance(value, list):
        return [_replace_nested_value(item, old, new) for item in value]
    if isinstance(value, tuple):
        return tuple(_replace_nested_value(item, old, new) for item in value)
    if isinstance(value, dict):
        return {
            key: _replace_nested_value(item, old, new)
            for key, item in value.items()
        }
    if value == old:
        return new
    return value


def _sha256_path(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _retarget_frozen_return_coverage_evidence(entry, old_binary_id, new_binary_id):
    observation = entry["current_observation"]
    for record in observation["reason_records"]:
        if record.get("reason_id") == "return_coverage_gap":
            record["object_target_key"] = _replace_nested_value(
                record["object_target_key"],
                old_binary_id,
                new_binary_id,
            )
    for action in observation["proof_actions"]:
        if action.get("reason_id") == "return_coverage_gap":
            action["object_target_key"] = _replace_nested_value(
                action["object_target_key"],
                old_binary_id,
                new_binary_id,
            )
            action["proof_obligation_id"] = _replace_nested_value(
                action["proof_obligation_id"],
                old_binary_id,
                new_binary_id,
            )


def _retarget_implementation_return_coverage_evidence(
    manifest,
    entry_id,
    old_binary_id,
    new_binary_id,
):
    implementation = manifest["implementation_manifest"]
    implementation_entry = next(
        entry
        for entry in implementation["expected_movement_entries"]
        if entry["id"] == entry_id
    )
    for field_name in ("expected_return_coverage_targets", "required_completion_actions"):
        implementation_entry[field_name] = _replace_nested_value(
            implementation_entry[field_name],
            old_binary_id,
            new_binary_id,
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
    recursive_implementation = next(
        entry
        for entry in implementation["expected_movement_entries"]
        if entry["function"] == "fc_recursive_sum"
    )
    assert recursive_implementation["expected_return_coverage_targets"]
    assert recursive_implementation["required_completion_actions"]
    assert {
        action["proof_stage"]
        for action in recursive_implementation["required_completion_actions"]
    } == {"return_partition_extraction", "return_guard_coverage"}
    pre_fix_gate = manifest["pre_fix_regression_gate"]
    assert pre_fix_gate["ready"] is True
    assert pre_fix_gate["summary"]["failed_kinds"] == []
    assert "current_logs_exact_match" in pre_fix_gate["summary"]["locked_gates"]
    assert "return_coverage_gap_object_evidence_proof_id" in {
        check["kind"] for check in pre_fix_gate["checks"]
    }
    validate_phase3_return_coverage_lane1_manifest(manifest)
    tampered_readiness = json.loads(json.dumps(manifest))
    tampered_readiness["readiness"]["failure_kinds"] = ["hidden_lane1_failure"]
    with pytest.raises(ValueError, match="hidden_lane1_failure"):
        validate_phase3_return_coverage_lane1_manifest(tampered_readiness)
    tampered_pre_fix = json.loads(json.dumps(manifest))
    tampered_pre_fix["pre_fix_regression_gate"]["summary"]["failed_kinds"] = [
        "hidden_lane1_pre_fix_failure"
    ]
    with pytest.raises(ValueError, match="hidden_lane1_pre_fix_failure"):
        validate_phase3_return_coverage_lane1_manifest(tampered_pre_fix)


def test_phase3_return_coverage_post_fix_gate_accepts_completed_eq_with_frozen_proof_ids(tmp_path):
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
    pre_fix_path = build_phase3_return_coverage_lane1_manifest(
        baseline_raw_dir=raw_dir,
        output_dir=tmp_path / "phase3-pre",
        current_log_roots={"function_call": current_root},
        baseline_log_roots={"function_call": baseline_root},
        phase1_dir=phase1_dir,
    )
    pre_fix_manifest = json.loads(pre_fix_path.read_text())
    frozen_recursive = next(
        entry
        for entry in pre_fix_manifest["entries"]
        if entry["function"] == "fc_recursive_sum"
    )
    _write_completed_eq_log(current_root, frozen_recursive)

    path = build_phase3_return_coverage_lane1_post_fix_gate(
        baseline_raw_dir=raw_dir,
        output_dir=tmp_path / "phase3-post",
        current_log_roots={"function_call": current_root},
        baseline_log_roots={"function_call": baseline_root},
        phase1_dir=phase1_dir,
        phase3_manifest_path=pre_fix_path,
        phase3_manifest_sha256=_sha256_path(pre_fix_path),
    )

    manifest = json.loads(path.read_text())
    assert manifest["phase3_lane1_post_fix_ready"] is True
    assert manifest["post_fix_regression_gate"]["summary"]["failed_kinds"] == []
    statuses = {entry["function"]: entry["post_fix_status"] for entry in manifest["entries"]}
    assert statuses == {
        "fc_recursive_sum": "completed_recovery",
        "fc_is_even": "pending_proof",
    }
    pending = next(entry for entry in manifest["entries"] if entry["function"] == "fc_is_even")
    required_actions = pending["required_completion_actions"]
    assert len(required_actions) == 4
    assert {
        json.dumps(action["proof_obligation_id"], sort_keys=True)
        for action in required_actions
    } == {
        json.dumps(obligation["proof_obligation_id"], sort_keys=True)
        for obligation in pending["pending_proof_obligations"]
    }
    pending_obligations = pending["pending_proof_obligations"]
    assert len(pending_obligations) == 4
    assert {obligation["proof_stage"] for obligation in pending_obligations} == {
        "return_partition_extraction",
        "return_guard_coverage",
    }
    required_by_stage = {
        obligation["proof_stage"]: obligation["required_evidence"]
        for obligation in pending_obligations
    }
    assert required_by_stage == {
        "return_partition_extraction": [
            "missing_return_guard",
            "tail_or_default_return_value",
            "return_storage",
        ],
        "return_guard_coverage": [
            "case_guard_disjunction",
            "path_feasibility",
            "function_precondition",
        ],
    }
    assert all(
        obligation["reason_id"] == "return_coverage_gap"
        and obligation["completed_evidence_present"] is False
        and obligation["status"] == "pending_evidence"
        and obligation["proof_obligation_id"]
        for obligation in pending_obligations
    )
    recursive = next(entry for entry in manifest["entries"] if entry["function"] == "fc_recursive_sum")
    completed = recursive["current_observation"]["completed_recovery_proof_evidence"]
    assert {item["proof_stage"] for item in completed} == {
        "return_partition_extraction",
        "return_guard_coverage",
    }
    assert {
        json.dumps(item["proof_obligation_id"], sort_keys=True)
        for item in completed
    } == {
        json.dumps(action["proof_obligation_id"], sort_keys=True)
        for action in frozen_recursive["current_observation"]["proof_actions"]
    }
    validate_phase3_return_coverage_lane1_post_fix_gate(manifest)
    tampered_post_fix = json.loads(json.dumps(manifest))
    tampered_post_fix["post_fix_regression_gate"]["summary"]["failed_kinds"] = [
        "hidden_lane1_post_fix_failure"
    ]
    with pytest.raises(ValueError, match="hidden_lane1_post_fix_failure"):
        validate_phase3_return_coverage_lane1_post_fix_gate(tampered_post_fix)
    tampered_pre_fix = json.loads(pre_fix_path.read_text())
    tampered_pre_fix["readiness"]["failure_kinds"] = [
        "hidden_lane1_pre_fix_manifest_failure"
    ]
    tampered_pre_fix_path = pre_fix_path.with_name(
        "tampered_return_coverage_lane1_representatives.json"
    )
    tampered_pre_fix_path.write_text(json.dumps(tampered_pre_fix))
    tampered_pre_fix_gate_path = build_phase3_return_coverage_lane1_post_fix_gate(
        baseline_raw_dir=raw_dir,
        output_dir=tmp_path / "phase3-post-tampered-pre-fix",
        current_log_roots={"function_call": current_root},
        baseline_log_roots={"function_call": baseline_root},
        phase1_dir=phase1_dir,
        phase3_manifest_path=tampered_pre_fix_path,
        phase3_manifest_sha256=_sha256_path(tampered_pre_fix_path),
    )
    tampered_pre_fix_gate = json.loads(tampered_pre_fix_gate_path.read_text())
    assert tampered_pre_fix_gate["phase3_lane1_post_fix_ready"] is False
    assert (
        "phase3_pre_fix_manifest_ready"
        in tampered_pre_fix_gate["post_fix_regression_gate"]["summary"]["failed_kinds"]
    )
    ready_check = next(
        check
        for check in tampered_pre_fix_gate["post_fix_regression_gate"]["checks"]
        if check["kind"] == "phase3_pre_fix_manifest_ready"
    )
    assert ready_check["status"] == "failed"
    assert "hidden_lane1_pre_fix_manifest_failure" in ready_check["error"]
    with pytest.raises(ValueError, match="phase3_pre_fix_manifest_ready"):
        validate_phase3_return_coverage_lane1_post_fix_gate(tampered_pre_fix_gate)


def test_phase3_return_coverage_post_fix_gate_accepts_completed_proof_with_operational_unknown(
    tmp_path,
):
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
    pre_fix_path = build_phase3_return_coverage_lane1_manifest(
        baseline_raw_dir=raw_dir,
        output_dir=tmp_path / "phase3-pre",
        current_log_roots={"function_call": current_root},
        baseline_log_roots={"function_call": baseline_root},
        phase1_dir=phase1_dir,
    )
    pre_fix_manifest = json.loads(pre_fix_path.read_text())
    frozen_recursive = next(
        entry
        for entry in pre_fix_manifest["entries"]
        if entry["function"] == "fc_recursive_sum"
    )
    frozen_even = next(
        entry
        for entry in pre_fix_manifest["entries"]
        if entry["function"] == "fc_is_even"
    )
    _write_completed_eq_log(current_root, frozen_recursive)
    _write_completed_unknown_log(
        current_root,
        frozen_even,
        [
            make_unknown_reason(
                UnknownReasonId.UNRESOLVED_EXPRESSION,
                stage="S_PAIRWISE",
                detail="unrelated expression backlog",
            )
        ],
        numeric_function_identity=True,
    )

    path = build_phase3_return_coverage_lane1_post_fix_gate(
        baseline_raw_dir=raw_dir,
        output_dir=tmp_path / "phase3-post",
        current_log_roots={"function_call": current_root},
        baseline_log_roots={"function_call": baseline_root},
        phase1_dir=phase1_dir,
        phase3_manifest_path=pre_fix_path,
        phase3_manifest_sha256=_sha256_path(pre_fix_path),
    )

    manifest = json.loads(path.read_text())
    assert manifest["phase3_lane1_post_fix_ready"] is True
    even = next(entry for entry in manifest["entries"] if entry["function"] == "fc_is_even")
    assert even["post_fix_status"] == "completed_recovery_with_operational_unknown"
    assert even["current_observation"]["final_result"] == "UNKNOWN"
    assert even["current_observation"]["observed_reason_ids"] == ["unresolved_expression"]
    assert even["post_fix_failures"] == []
    validate_phase3_return_coverage_lane1_post_fix_gate(manifest)


def test_phase3_return_coverage_post_fix_gate_accepts_negative_reason_reclassified_after_fix(
    tmp_path,
):
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
    pre_fix_path = build_phase3_return_coverage_lane1_manifest(
        baseline_raw_dir=raw_dir,
        output_dir=tmp_path / "phase3-pre",
        current_log_roots={"function_call": current_root},
        baseline_log_roots={"function_call": baseline_root},
        phase1_dir=phase1_dir,
    )
    pre_fix_manifest = json.loads(pre_fix_path.read_text())
    frozen_recursive = next(
        entry
        for entry in pre_fix_manifest["entries"]
        if entry["function"] == "fc_recursive_sum"
    )
    _write_completed_eq_log(current_root, frozen_recursive)
    _write_log(
        current_root,
        "fc_negative_fixture",
        "B11",
        "B12",
        [
            make_unknown_reason(
                UnknownReasonId.UNRESOLVED_EXPRESSION,
                stage="S_PAIRWISE",
                detail="post-fix reason moved off return coverage",
            )
        ],
    )
    (phase1_dir / "negative_manifest.json").write_text(
        json.dumps(
            {
                "entries": [
                    {
                        "id": "negative-return-coverage-reclassified",
                        "category": "function_call",
                        "function": "fc_negative_fixture",
                        "binary_pair": "B11_B12",
                        "expected_result": "UNKNOWN",
                        "must_not_be_equivalent": True,
                        "required_reason_ids": ["return_coverage_gap"],
                    }
                ]
            }
        )
    )

    path = build_phase3_return_coverage_lane1_post_fix_gate(
        baseline_raw_dir=raw_dir,
        output_dir=tmp_path / "phase3-post",
        current_log_roots={"function_call": current_root},
        baseline_log_roots={"function_call": baseline_root},
        phase1_dir=phase1_dir,
        phase3_manifest_path=pre_fix_path,
        phase3_manifest_sha256=_sha256_path(pre_fix_path),
    )

    manifest = json.loads(path.read_text())
    assert manifest["phase3_lane1_post_fix_ready"] is True
    negative_check = next(
        check
        for check in manifest["post_fix_regression_gate"]["checks"]
        if check.get("entry_id") == "negative-return-coverage-reclassified"
    )
    assert negative_check["status"] == "ok"
    assert negative_check["reason_policy"] == "post_fix_no_false_eq"
    assert negative_check["observed_reason_ids"] == ["unresolved_expression"]
    validate_phase3_return_coverage_lane1_post_fix_gate(manifest)


def test_phase3_return_coverage_post_fix_gate_accepts_retired_transition_one_sided_gap(
    tmp_path,
):
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
    pre_fix_path = build_phase3_return_coverage_lane1_manifest(
        baseline_raw_dir=raw_dir,
        output_dir=tmp_path / "phase3-pre",
        current_log_roots={"function_call": current_root},
        baseline_log_roots={"function_call": baseline_root},
        phase1_dir=phase1_dir,
    )
    pre_fix_manifest = json.loads(pre_fix_path.read_text())
    frozen_recursive = next(
        entry
        for entry in pre_fix_manifest["entries"]
        if entry["function"] == "fc_recursive_sum"
    )
    _write_completed_eq_log(current_root, frozen_recursive)
    _write_log(
        current_root,
        "fc_is_odd",
        "B11",
        "B16",
        [_reason_from_ref("function2:return_coverage_gap")],
    )

    path = build_phase3_return_coverage_lane1_post_fix_gate(
        baseline_raw_dir=raw_dir,
        output_dir=tmp_path / "phase3-post",
        current_log_roots={"function_call": current_root},
        baseline_log_roots={"function_call": baseline_root},
        phase1_dir=phase1_dir,
        phase3_manifest_path=pre_fix_path,
        phase3_manifest_sha256=_sha256_path(pre_fix_path),
    )

    manifest = json.loads(path.read_text())
    assert manifest["phase3_lane1_post_fix_ready"] is True
    transition = next(
        entry
        for entry in manifest["retired_transitions"]
        if entry["binary_pair"] == "B11_B16"
    )
    assert transition["selection_status"] == "retired_by_reclassification"
    assert transition["selection_failures"] == []
    assert transition["final_result_invariant"]["final_result_unchanged_unknown"] is True
    validate_phase3_return_coverage_lane1_post_fix_gate(manifest)


def test_phase3_return_coverage_post_fix_gate_accepts_completed_eq_with_current_completed_partition(
    tmp_path,
):
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
    pre_fix_path = build_phase3_return_coverage_lane1_manifest(
        baseline_raw_dir=raw_dir,
        output_dir=tmp_path / "phase3-pre",
        current_log_roots={"function_call": current_root},
        baseline_log_roots={"function_call": baseline_root},
        phase1_dir=phase1_dir,
    )
    pre_fix_manifest = json.loads(pre_fix_path.read_text())
    frozen_recursive = next(
        entry
        for entry in pre_fix_manifest["entries"]
        if entry["function"] == "fc_recursive_sum"
    )
    _write_completed_eq_log_with_current_return_coverage_targets(
        current_root,
        frozen_recursive,
    )

    path = build_phase3_return_coverage_lane1_post_fix_gate(
        baseline_raw_dir=raw_dir,
        output_dir=tmp_path / "phase3-post",
        current_log_roots={"function_call": current_root},
        baseline_log_roots={"function_call": baseline_root},
        phase1_dir=phase1_dir,
        phase3_manifest_path=pre_fix_path,
        phase3_manifest_sha256=_sha256_path(pre_fix_path),
    )

    manifest = json.loads(path.read_text())
    assert manifest["phase3_lane1_post_fix_ready"] is True
    recursive = next(entry for entry in manifest["entries"] if entry["function"] == "fc_recursive_sum")
    assert recursive["post_fix_status"] == "completed_recovery"
    validate_phase3_return_coverage_lane1_post_fix_gate(manifest)


def test_phase3_return_coverage_post_fix_gate_rejects_completed_eq_with_wrong_current_binary(
    tmp_path,
):
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
    pre_fix_path = build_phase3_return_coverage_lane1_manifest(
        baseline_raw_dir=raw_dir,
        output_dir=tmp_path / "phase3-pre",
        current_log_roots={"function_call": current_root},
        baseline_log_roots={"function_call": baseline_root},
        phase1_dir=phase1_dir,
    )
    pre_fix_manifest = json.loads(pre_fix_path.read_text())
    frozen_recursive = next(
        entry
        for entry in pre_fix_manifest["entries"]
        if entry["function"] == "fc_recursive_sum"
    )
    _write_completed_eq_log_with_current_return_coverage_targets(
        current_root,
        frozen_recursive,
        retarget_binary_id="B16",
    )

    path = build_phase3_return_coverage_lane1_post_fix_gate(
        baseline_raw_dir=raw_dir,
        output_dir=tmp_path / "phase3-post",
        current_log_roots={"function_call": current_root},
        baseline_log_roots={"function_call": baseline_root},
        phase1_dir=phase1_dir,
        phase3_manifest_path=pre_fix_path,
        phase3_manifest_sha256=_sha256_path(pre_fix_path),
    )

    manifest = json.loads(path.read_text())
    assert manifest["phase3_lane1_post_fix_ready"] is False
    recursive = next(entry for entry in manifest["entries"] if entry["function"] == "fc_recursive_sum")
    assert recursive["post_fix_status"] == "failed"
    assert {
        failure.split(":", 1)[0]
        for failure in recursive["post_fix_failures"]
    } == {"return_coverage_completed_proof_required"}
    with pytest.raises(ValueError, match="return_coverage_post_fix_expected_movement"):
        validate_phase3_return_coverage_lane1_post_fix_gate(manifest)


def test_phase3_return_coverage_post_fix_gate_rejects_eq_without_completed_proof(tmp_path):
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
    pre_fix_path = build_phase3_return_coverage_lane1_manifest(
        baseline_raw_dir=raw_dir,
        output_dir=tmp_path / "phase3-pre",
        current_log_roots={"function_call": current_root},
        baseline_log_roots={"function_call": baseline_root},
        phase1_dir=phase1_dir,
    )
    _write_eq_log(current_root, "fc_recursive_sum", "B11", "B15")

    path = build_phase3_return_coverage_lane1_post_fix_gate(
        baseline_raw_dir=raw_dir,
        output_dir=tmp_path / "phase3-post",
        current_log_roots={"function_call": current_root},
        baseline_log_roots={"function_call": baseline_root},
        phase1_dir=phase1_dir,
        phase3_manifest_path=pre_fix_path,
        phase3_manifest_sha256=_sha256_path(pre_fix_path),
    )

    manifest = json.loads(path.read_text())
    assert manifest["phase3_lane1_post_fix_ready"] is False
    recursive = next(entry for entry in manifest["entries"] if entry["function"] == "fc_recursive_sum")
    assert recursive["post_fix_status"] == "failed"
    assert "return_coverage_completed_proof_required" in recursive["post_fix_failures"]
    assert manifest["post_fix_regression_gate"]["summary"]["failed_kinds"] == [
        "return_coverage_post_fix_expected_movement"
    ]
    with pytest.raises(ValueError, match="return_coverage_post_fix_expected_movement"):
        validate_phase3_return_coverage_lane1_post_fix_gate(manifest)


@pytest.mark.parametrize("blocker_field", ["active_coverage_gaps", "active_unsupported_effects"])
def test_phase3_return_coverage_post_fix_gate_rejects_completed_eq_with_active_blockers(
    tmp_path, blocker_field
):
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
    pre_fix_path = build_phase3_return_coverage_lane1_manifest(
        baseline_raw_dir=raw_dir,
        output_dir=tmp_path / "phase3-pre",
        current_log_roots={"function_call": current_root},
        baseline_log_roots={"function_call": baseline_root},
        phase1_dir=phase1_dir,
    )
    pre_fix_manifest = json.loads(pre_fix_path.read_text())
    frozen_recursive = next(
        entry
        for entry in pre_fix_manifest["entries"]
        if entry["function"] == "fc_recursive_sum"
    )
    _write_completed_eq_log(
        current_root,
        frozen_recursive,
        evidence_updates={blocker_field: [{"status": "active"}]},
    )

    path = build_phase3_return_coverage_lane1_post_fix_gate(
        baseline_raw_dir=raw_dir,
        output_dir=tmp_path / "phase3-post",
        current_log_roots={"function_call": current_root},
        baseline_log_roots={"function_call": baseline_root},
        phase1_dir=phase1_dir,
        phase3_manifest_path=pre_fix_path,
        phase3_manifest_sha256=_sha256_path(pre_fix_path),
    )

    manifest = json.loads(path.read_text())
    assert manifest["phase3_lane1_post_fix_ready"] is False
    recursive = next(entry for entry in manifest["entries"] if entry["function"] == "fc_recursive_sum")
    assert recursive["post_fix_status"] == "failed"
    assert {
        failure.split(":", 1)[0]
        for failure in recursive["post_fix_failures"]
    } == {"return_coverage_completed_proof_required"}
    assert all(
        item["evidence"][blocker_field] == [{"status": "active"}]
        for item in recursive["current_observation"]["completed_recovery_proof_evidence"]
    )
    assert manifest["post_fix_regression_gate"]["summary"]["failed_kinds"] == [
        "return_coverage_post_fix_expected_movement"
    ]
    with pytest.raises(ValueError, match="return_coverage_post_fix_expected_movement"):
        validate_phase3_return_coverage_lane1_post_fix_gate(manifest)


def test_phase3_return_coverage_post_fix_gate_rejects_empty_pre_fix_manifest(tmp_path):
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
    empty_pre_fix_path = tmp_path / "empty_phase3_pre_fix.json"
    empty_pre_fix_path.write_text(json.dumps({"entries": [], "retired_transitions": []}))

    path = build_phase3_return_coverage_lane1_post_fix_gate(
        baseline_raw_dir=raw_dir,
        output_dir=tmp_path / "phase3-post",
        current_log_roots={"function_call": current_root},
        baseline_log_roots={"function_call": baseline_root},
        phase1_dir=phase1_dir,
        phase3_manifest_path=empty_pre_fix_path,
        phase3_manifest_sha256=_sha256_path(empty_pre_fix_path),
    )

    manifest = json.loads(path.read_text())
    assert manifest["phase3_lane1_post_fix_ready"] is False
    assert manifest["entries"] == []
    assert manifest["retired_transitions"] == []
    failed_kinds = set(manifest["post_fix_regression_gate"]["summary"]["failed_kinds"])
    assert {
        "phase3_pre_fix_entries_non_empty",
        "phase3_pre_fix_entries_exact_set",
        "phase3_pre_fix_implementation_manifest_available",
        "phase3_pre_fix_manifest_kind",
        "phase3_pre_fix_manifest_ready",
        "phase3_pre_fix_retired_transitions_non_empty",
        "phase3_pre_fix_retired_transitions_exact_set",
    }.issubset(failed_kinds)
    with pytest.raises(ValueError, match="phase3_pre_fix_entries_non_empty"):
        validate_phase3_return_coverage_lane1_post_fix_gate(manifest)


def test_phase3_return_coverage_post_fix_gate_rejects_phase3_manifest_sha_mismatch(
    tmp_path,
):
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
    pre_fix_path = build_phase3_return_coverage_lane1_manifest(
        baseline_raw_dir=raw_dir,
        output_dir=tmp_path / "phase3-pre",
        current_log_roots={"function_call": current_root},
        baseline_log_roots={"function_call": baseline_root},
        phase1_dir=phase1_dir,
    )

    path = build_phase3_return_coverage_lane1_post_fix_gate(
        baseline_raw_dir=raw_dir,
        output_dir=tmp_path / "phase3-post",
        current_log_roots={"function_call": current_root},
        baseline_log_roots={"function_call": baseline_root},
        phase1_dir=phase1_dir,
        phase3_manifest_path=pre_fix_path,
        phase3_manifest_sha256="definitely-not-the-frozen-manifest-sha256",
    )

    manifest = json.loads(path.read_text())
    assert manifest["phase3_lane1_post_fix_ready"] is False
    failed_kinds = manifest["post_fix_regression_gate"]["summary"]["failed_kinds"]
    assert "phase3_pre_fix_manifest_sha256" in failed_kinds
    with pytest.raises(ValueError, match="phase3_pre_fix_manifest_sha256"):
        validate_phase3_return_coverage_lane1_post_fix_gate(manifest)


def test_phase3_return_coverage_post_fix_cli_requires_phase3_manifest_sha256(capsys):
    with pytest.raises(SystemExit) as exc:
        phase3_return_coverage_lane1_main(
            [
                "--gate-stage",
                "post-fix",
                "--baseline-raw-dir",
                "/tmp/nonexistent-baseline/raw",
                "--output-dir",
                "/tmp/nonexistent-output",
            ]
        )

    assert exc.value.code == 2
    assert "--phase3-manifest-sha256 is required" in capsys.readouterr().err


@pytest.mark.parametrize(
    "mutation, expected_failure",
    [
        (
            "empty_proof_actions",
            "phase3_pre_fix_entry_has_proof_actions",
        ),
        (
            "missing_proof_ids",
            "phase3_pre_fix_entry_has_return_coverage_completion_proof_ids",
        ),
    ],
)
def test_phase3_return_coverage_post_fix_gate_rejects_pre_fix_manifest_without_frozen_proofs(
    tmp_path, mutation, expected_failure
):
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
    pre_fix_path = build_phase3_return_coverage_lane1_manifest(
        baseline_raw_dir=raw_dir,
        output_dir=tmp_path / "phase3-pre",
        current_log_roots={"function_call": current_root},
        baseline_log_roots={"function_call": baseline_root},
        phase1_dir=phase1_dir,
    )
    pre_fix_manifest = json.loads(pre_fix_path.read_text())
    frozen_actions = pre_fix_manifest["entries"][0]["current_observation"]["proof_actions"]
    if mutation == "empty_proof_actions":
        pre_fix_manifest["entries"][0]["current_observation"]["proof_actions"] = []
    else:
        for action in frozen_actions:
            action.pop("proof_obligation_id", None)
            action["raw_proof_obligation_id_present"] = False
    invalid_pre_fix_path = tmp_path / f"invalid_phase3_pre_fix_{mutation}.json"
    invalid_pre_fix_path.write_text(json.dumps(pre_fix_manifest))

    path = build_phase3_return_coverage_lane1_post_fix_gate(
        baseline_raw_dir=raw_dir,
        output_dir=tmp_path / "phase3-post",
        current_log_roots={"function_call": current_root},
        baseline_log_roots={"function_call": baseline_root},
        phase1_dir=phase1_dir,
        phase3_manifest_path=invalid_pre_fix_path,
        phase3_manifest_sha256=_sha256_path(invalid_pre_fix_path),
    )

    manifest = json.loads(path.read_text())
    assert manifest["phase3_lane1_post_fix_ready"] is False
    assert expected_failure in manifest["post_fix_regression_gate"]["summary"]["failed_kinds"]
    with pytest.raises(ValueError, match=expected_failure):
        validate_phase3_return_coverage_lane1_post_fix_gate(manifest)


def test_phase3_return_coverage_post_fix_gate_rejects_partial_frozen_completion_stage_set(
    tmp_path,
):
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
    pre_fix_path = build_phase3_return_coverage_lane1_manifest(
        baseline_raw_dir=raw_dir,
        output_dir=tmp_path / "phase3-pre",
        current_log_roots={"function_call": current_root},
        baseline_log_roots={"function_call": baseline_root},
        phase1_dir=phase1_dir,
    )
    pre_fix_manifest = json.loads(pre_fix_path.read_text())
    frozen_recursive = next(
        entry
        for entry in pre_fix_manifest["entries"]
        if entry["function"] == "fc_recursive_sum"
    )
    frozen_recursive["current_observation"]["proof_actions"] = [
        action
        for action in frozen_recursive["current_observation"]["proof_actions"]
        if action["proof_stage"] == "return_partition_extraction"
    ]
    invalid_pre_fix_path = tmp_path / "partial_stage_phase3_pre_fix.json"
    invalid_pre_fix_path.write_text(json.dumps(pre_fix_manifest))
    _write_completed_eq_log(current_root, frozen_recursive)

    path = build_phase3_return_coverage_lane1_post_fix_gate(
        baseline_raw_dir=raw_dir,
        output_dir=tmp_path / "phase3-post",
        current_log_roots={"function_call": current_root},
        baseline_log_roots={"function_call": baseline_root},
        phase1_dir=phase1_dir,
        phase3_manifest_path=invalid_pre_fix_path,
        phase3_manifest_sha256=_sha256_path(invalid_pre_fix_path),
    )

    manifest = json.loads(path.read_text())
    assert manifest["phase3_lane1_post_fix_ready"] is False
    failed_kinds = manifest["post_fix_regression_gate"]["summary"]["failed_kinds"]
    assert "phase3_pre_fix_entry_has_complete_return_coverage_completion_proof_ids" in failed_kinds
    assert "return_coverage_post_fix_expected_movement" in failed_kinds
    recursive = next(entry for entry in manifest["entries"] if entry["function"] == "fc_recursive_sum")
    assert recursive["post_fix_status"] == "failed"
    assert (
        "return_coverage_completed_proof_required:"
        "return_guard_coverage:case_guard_disjunction"
    ) in recursive["post_fix_failures"]
    completed = recursive["current_observation"]["completed_recovery_proof_evidence"]
    assert {item["proof_stage"] for item in completed} == {"return_partition_extraction"}
    with pytest.raises(
        ValueError,
        match="phase3_pre_fix_entry_has_complete_return_coverage_completion_proof_ids",
    ):
        validate_phase3_return_coverage_lane1_post_fix_gate(manifest)


def test_phase3_return_coverage_post_fix_gate_rejects_missing_expected_target_ref(
    tmp_path,
):
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
    pre_fix_path = build_phase3_return_coverage_lane1_manifest(
        baseline_raw_dir=raw_dir,
        output_dir=tmp_path / "phase3-pre",
        current_log_roots={"function_call": current_root},
        baseline_log_roots={"function_call": baseline_root},
        phase1_dir=phase1_dir,
    )
    pre_fix_manifest = json.loads(pre_fix_path.read_text())
    frozen_even = next(
        entry
        for entry in pre_fix_manifest["entries"]
        if entry["function"] == "fc_is_even"
    )
    frozen_even["current_observation"]["reason_records"] = [
        record
        for record in frozen_even["current_observation"]["reason_records"]
        if record["evidence_refs"] != ["function2:return_coverage_gap"]
    ]
    frozen_even["current_observation"]["proof_actions"] = [
        action
        for action in frozen_even["current_observation"]["proof_actions"]
        if action["evidence_refs"] != ["function2:return_coverage_gap"]
    ]
    invalid_pre_fix_path = tmp_path / "missing_expected_target_phase3_pre_fix.json"
    invalid_pre_fix_path.write_text(json.dumps(pre_fix_manifest))

    path = build_phase3_return_coverage_lane1_post_fix_gate(
        baseline_raw_dir=raw_dir,
        output_dir=tmp_path / "phase3-post",
        current_log_roots={"function_call": current_root},
        baseline_log_roots={"function_call": baseline_root},
        phase1_dir=phase1_dir,
        phase3_manifest_path=invalid_pre_fix_path,
        phase3_manifest_sha256=_sha256_path(invalid_pre_fix_path),
    )

    manifest = json.loads(path.read_text())
    assert manifest["phase3_lane1_post_fix_ready"] is False
    failed_kinds = manifest["post_fix_regression_gate"]["summary"]["failed_kinds"]
    assert "phase3_pre_fix_entry_expected_return_coverage_targets_resolved" in failed_kinds
    failed_checks = [
        check
        for check in manifest["post_fix_regression_gate"]["checks"]
        if check["kind"] == "phase3_pre_fix_entry_expected_return_coverage_targets_resolved"
        and check["status"] == "failed"
    ]
    assert failed_checks[0]["missing_evidence_refs"] == [["function2:return_coverage_gap"]]
    with pytest.raises(
        ValueError,
        match="phase3_pre_fix_entry_expected_return_coverage_targets_resolved",
    ):
        validate_phase3_return_coverage_lane1_post_fix_gate(manifest)


@pytest.mark.parametrize("mutation", ["missing", "changed_required_evidence"])
def test_phase3_return_coverage_post_fix_gate_rejects_mutated_expected_movements_on_eq_path(
    tmp_path,
    mutation,
):
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
    pre_fix_path = build_phase3_return_coverage_lane1_manifest(
        baseline_raw_dir=raw_dir,
        output_dir=tmp_path / "phase3-pre",
        current_log_roots={"function_call": current_root},
        baseline_log_roots={"function_call": baseline_root},
        phase1_dir=phase1_dir,
    )
    pre_fix_manifest = json.loads(pre_fix_path.read_text())
    frozen_recursive = next(
        entry
        for entry in pre_fix_manifest["entries"]
        if entry["function"] == "fc_recursive_sum"
    )
    if mutation == "missing":
        frozen_recursive["expected_movements"] = []
    else:
        movements = [dict(item) for item in frozen_recursive["expected_movements"]]
        movements[1]["required_evidence"] = [
            "wrong_evidence",
            "tail_or_default_return_value",
            "return_storage",
        ]
        frozen_recursive["expected_movements"] = movements
    invalid_pre_fix_path = tmp_path / f"mutated_expected_movements_{mutation}.json"
    invalid_pre_fix_path.write_text(json.dumps(pre_fix_manifest))
    _write_completed_eq_log(current_root, frozen_recursive)

    path = build_phase3_return_coverage_lane1_post_fix_gate(
        baseline_raw_dir=raw_dir,
        output_dir=tmp_path / "phase3-post",
        current_log_roots={"function_call": current_root},
        baseline_log_roots={"function_call": baseline_root},
        phase1_dir=phase1_dir,
        phase3_manifest_path=invalid_pre_fix_path,
        phase3_manifest_sha256=_sha256_path(invalid_pre_fix_path),
    )

    manifest = json.loads(path.read_text())
    assert manifest["phase3_lane1_post_fix_ready"] is False
    failed_kinds = manifest["post_fix_regression_gate"]["summary"]["failed_kinds"]
    assert "phase3_pre_fix_entry_expected_movements_match_definition" in failed_kinds
    assert "phase3_pre_fix_entry_expected_movements_match_implementation" in failed_kinds
    recursive = next(entry for entry in manifest["entries"] if entry["function"] == "fc_recursive_sum")
    assert recursive["post_fix_status"] == "completed_recovery"
    movement_check = next(
        check
        for check in manifest["post_fix_regression_gate"]["checks"]
        if check["kind"] == "phase3_pre_fix_entry_expected_movements_match_definition"
        and check["entry"]["function"] == "fc_recursive_sum"
    )
    assert movement_check["status"] == "failed"
    if mutation == "missing":
        assert movement_check["actual_count"] == 0
    else:
        assert movement_check["actual_movements"][1]["required_evidence"] == [
            "wrong_evidence",
            "tail_or_default_return_value",
            "return_storage",
        ]
    with pytest.raises(ValueError, match="phase3_pre_fix_entry_expected_movements_match_definition"):
        validate_phase3_return_coverage_lane1_post_fix_gate(manifest)


@pytest.mark.parametrize("mutation", ["missing", "changed_required_evidence"])
def test_phase3_return_coverage_post_fix_gate_rejects_mutated_expected_movements_without_implementation_manifest(
    tmp_path,
    mutation,
):
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
    pre_fix_path = build_phase3_return_coverage_lane1_manifest(
        baseline_raw_dir=raw_dir,
        output_dir=tmp_path / "phase3-pre",
        current_log_roots={"function_call": current_root},
        baseline_log_roots={"function_call": baseline_root},
        phase1_dir=phase1_dir,
    )
    pre_fix_manifest = json.loads(pre_fix_path.read_text())
    pre_fix_manifest.pop("implementation_manifest")
    frozen_recursive = next(
        entry
        for entry in pre_fix_manifest["entries"]
        if entry["function"] == "fc_recursive_sum"
    )
    if mutation == "missing":
        frozen_recursive["expected_movements"] = []
    else:
        movements = [dict(item) for item in frozen_recursive["expected_movements"]]
        movements[1]["required_evidence"] = [
            "wrong_evidence",
            "tail_or_default_return_value",
            "return_storage",
        ]
        frozen_recursive["expected_movements"] = movements
    invalid_pre_fix_path = (
        tmp_path / f"missing_implementation_mutated_expected_movements_{mutation}.json"
    )
    invalid_pre_fix_path.write_text(json.dumps(pre_fix_manifest))
    _write_completed_eq_log(current_root, frozen_recursive)

    path = build_phase3_return_coverage_lane1_post_fix_gate(
        baseline_raw_dir=raw_dir,
        output_dir=tmp_path / "phase3-post",
        current_log_roots={"function_call": current_root},
        baseline_log_roots={"function_call": baseline_root},
        phase1_dir=phase1_dir,
        phase3_manifest_path=invalid_pre_fix_path,
        phase3_manifest_sha256=_sha256_path(invalid_pre_fix_path),
    )

    manifest = json.loads(path.read_text())
    assert manifest["phase3_lane1_post_fix_ready"] is False
    summary = manifest["post_fix_regression_gate"]["summary"]
    assert summary["not_evaluated"] == 0
    failed_kinds = summary["failed_kinds"]
    assert "phase3_pre_fix_implementation_manifest_available" in failed_kinds
    assert "phase3_pre_fix_entry_expected_movements_match_definition" in failed_kinds
    assert "phase3_pre_fix_implementation_expected_movements_match_definition" in failed_kinds
    recursive = next(entry for entry in manifest["entries"] if entry["function"] == "fc_recursive_sum")
    assert recursive["post_fix_status"] == "completed_recovery"
    with pytest.raises(ValueError, match="phase3_pre_fix_implementation_manifest_available"):
        validate_phase3_return_coverage_lane1_post_fix_gate(manifest)


def test_phase3_return_coverage_post_fix_gate_rejects_self_consistent_target_tampering(
    tmp_path,
):
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
    pre_fix_path = build_phase3_return_coverage_lane1_manifest(
        baseline_raw_dir=raw_dir,
        output_dir=tmp_path / "phase3-pre",
        current_log_roots={"function_call": current_root},
        baseline_log_roots={"function_call": baseline_root},
        phase1_dir=phase1_dir,
    )
    pre_fix_manifest = json.loads(pre_fix_path.read_text())
    frozen_recursive = next(
        entry
        for entry in pre_fix_manifest["entries"]
        if entry["function"] == "fc_recursive_sum"
    )
    _retarget_frozen_return_coverage_evidence(frozen_recursive, "B15", "B16")
    invalid_pre_fix_path = tmp_path / "retargeted_concrete_evidence_phase3_pre_fix.json"
    invalid_pre_fix_path.write_text(json.dumps(pre_fix_manifest))
    _write_completed_eq_log(current_root, frozen_recursive)

    path = build_phase3_return_coverage_lane1_post_fix_gate(
        baseline_raw_dir=raw_dir,
        output_dir=tmp_path / "phase3-post",
        current_log_roots={"function_call": current_root},
        baseline_log_roots={"function_call": baseline_root},
        phase1_dir=phase1_dir,
        phase3_manifest_path=invalid_pre_fix_path,
        phase3_manifest_sha256=_sha256_path(invalid_pre_fix_path),
    )

    manifest = json.loads(path.read_text())
    assert manifest["phase3_lane1_post_fix_ready"] is False
    failed_kinds = manifest["post_fix_regression_gate"]["summary"]["failed_kinds"]
    assert "phase3_pre_fix_entry_return_coverage_targets_match_implementation" in failed_kinds
    assert "phase3_pre_fix_entry_required_completion_actions_match_implementation" in failed_kinds
    recursive = next(entry for entry in manifest["entries"] if entry["function"] == "fc_recursive_sum")
    assert recursive["post_fix_status"] == "completed_recovery"
    target_check = next(
        check
        for check in manifest["post_fix_regression_gate"]["checks"]
        if check["kind"] == "phase3_pre_fix_entry_return_coverage_targets_match_implementation"
        and check["entry"]["function"] == "fc_recursive_sum"
    )
    assert target_check["status"] == "failed"
    assert "B15" in json.dumps(target_check["expected_targets"])
    assert "B16" in json.dumps(target_check["actual_targets"])
    with pytest.raises(
        ValueError,
        match="phase3_pre_fix_entry_required_completion_actions_match_implementation",
    ):
        validate_phase3_return_coverage_lane1_post_fix_gate(manifest)


def test_phase3_return_coverage_post_fix_gate_requires_sha_for_self_consistent_manifest_tampering(
    tmp_path,
):
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
    pre_fix_path = build_phase3_return_coverage_lane1_manifest(
        baseline_raw_dir=raw_dir,
        output_dir=tmp_path / "phase3-pre",
        current_log_roots={"function_call": current_root},
        baseline_log_roots={"function_call": baseline_root},
        phase1_dir=phase1_dir,
    )
    pre_fix_manifest = json.loads(pre_fix_path.read_text())
    frozen_recursive = next(
        entry
        for entry in pre_fix_manifest["entries"]
        if entry["function"] == "fc_recursive_sum"
    )
    _retarget_frozen_return_coverage_evidence(frozen_recursive, "B15", "B16")
    _retarget_implementation_return_coverage_evidence(
        pre_fix_manifest,
        frozen_recursive["id"],
        "B15",
        "B16",
    )
    invalid_pre_fix_path = (
        tmp_path / "self_consistent_retargeted_concrete_evidence_phase3_pre_fix.json"
    )
    invalid_pre_fix_path.write_text(json.dumps(pre_fix_manifest))
    _write_completed_eq_log(current_root, frozen_recursive)

    path = build_phase3_return_coverage_lane1_post_fix_gate(
        baseline_raw_dir=raw_dir,
        output_dir=tmp_path / "phase3-post",
        current_log_roots={"function_call": current_root},
        baseline_log_roots={"function_call": baseline_root},
        phase1_dir=phase1_dir,
        phase3_manifest_path=invalid_pre_fix_path,
    )

    manifest = json.loads(path.read_text())
    assert manifest["phase3_lane1_post_fix_ready"] is False
    failed_kinds = manifest["post_fix_regression_gate"]["summary"]["failed_kinds"]
    assert "phase3_pre_fix_manifest_sha256_required" in failed_kinds
    assert "phase3_pre_fix_entry_return_coverage_targets_match_implementation" not in failed_kinds
    assert "phase3_pre_fix_entry_required_completion_actions_match_implementation" not in failed_kinds
    recursive = next(entry for entry in manifest["entries"] if entry["function"] == "fc_recursive_sum")
    assert recursive["post_fix_status"] == "completed_recovery"
    with pytest.raises(ValueError, match="phase3_pre_fix_manifest_sha256_required"):
        validate_phase3_return_coverage_lane1_post_fix_gate(manifest)


def test_phase3_return_coverage_post_fix_gate_rejects_missing_representative_entry(
    tmp_path,
):
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
    pre_fix_path = build_phase3_return_coverage_lane1_manifest(
        baseline_raw_dir=raw_dir,
        output_dir=tmp_path / "phase3-pre",
        current_log_roots={"function_call": current_root},
        baseline_log_roots={"function_call": baseline_root},
        phase1_dir=phase1_dir,
    )
    pre_fix_manifest = json.loads(pre_fix_path.read_text())
    frozen_recursive = next(
        entry
        for entry in pre_fix_manifest["entries"]
        if entry["function"] == "fc_recursive_sum"
    )
    pre_fix_manifest["entries"] = [
        entry
        for entry in pre_fix_manifest["entries"]
        if entry["function"] != "fc_is_even"
    ]
    invalid_pre_fix_path = tmp_path / "missing_representative_phase3_pre_fix.json"
    invalid_pre_fix_path.write_text(json.dumps(pre_fix_manifest))
    _write_completed_eq_log(current_root, frozen_recursive)

    path = build_phase3_return_coverage_lane1_post_fix_gate(
        baseline_raw_dir=raw_dir,
        output_dir=tmp_path / "phase3-post",
        current_log_roots={"function_call": current_root},
        baseline_log_roots={"function_call": baseline_root},
        phase1_dir=phase1_dir,
        phase3_manifest_path=invalid_pre_fix_path,
        phase3_manifest_sha256=_sha256_path(invalid_pre_fix_path),
    )

    manifest = json.loads(path.read_text())
    assert manifest["phase3_lane1_post_fix_ready"] is False
    failed_kinds = manifest["post_fix_regression_gate"]["summary"]["failed_kinds"]
    assert "phase3_pre_fix_entries_exact_set" in failed_kinds
    assert "phase3_pre_fix_implementation_entries_consistent" in failed_kinds
    exact_check = next(
        check
        for check in manifest["post_fix_regression_gate"]["checks"]
        if check["kind"] == "phase3_pre_fix_entries_exact_set"
    )
    assert exact_check["missing"] == [
        {
            "id": "representative-return-coverage-gap-even-both-sides",
            "function": "fc_is_even",
            "binary_pair": "B11_B12",
        }
    ]
    assert [
        (entry["id"], entry["post_fix_status"])
        for entry in manifest["entries"]
    ] == [("representative-return-coverage-gap-recursive-simple", "completed_recovery")]
    with pytest.raises(ValueError, match="phase3_pre_fix_entries_exact_set"):
        validate_phase3_return_coverage_lane1_post_fix_gate(manifest)


def test_phase3_return_coverage_post_fix_gate_rejects_missing_retired_transition(
    tmp_path,
):
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
    pre_fix_path = build_phase3_return_coverage_lane1_manifest(
        baseline_raw_dir=raw_dir,
        output_dir=tmp_path / "phase3-pre",
        current_log_roots={"function_call": current_root},
        baseline_log_roots={"function_call": baseline_root},
        phase1_dir=phase1_dir,
    )
    pre_fix_manifest = json.loads(pre_fix_path.read_text())
    pre_fix_manifest["retired_transitions"] = pre_fix_manifest["retired_transitions"][:1]
    invalid_pre_fix_path = tmp_path / "missing_retired_transition_phase3_pre_fix.json"
    invalid_pre_fix_path.write_text(json.dumps(pre_fix_manifest))

    path = build_phase3_return_coverage_lane1_post_fix_gate(
        baseline_raw_dir=raw_dir,
        output_dir=tmp_path / "phase3-post",
        current_log_roots={"function_call": current_root},
        baseline_log_roots={"function_call": baseline_root},
        phase1_dir=phase1_dir,
        phase3_manifest_path=invalid_pre_fix_path,
        phase3_manifest_sha256=_sha256_path(invalid_pre_fix_path),
    )

    manifest = json.loads(path.read_text())
    assert manifest["phase3_lane1_post_fix_ready"] is False
    failed_kinds = manifest["post_fix_regression_gate"]["summary"]["failed_kinds"]
    assert "phase3_pre_fix_retired_transitions_exact_set" in failed_kinds
    assert "phase3_pre_fix_implementation_retired_transitions_consistent" in failed_kinds
    exact_check = next(
        check
        for check in manifest["post_fix_regression_gate"]["checks"]
        if check["kind"] == "phase3_pre_fix_retired_transitions_exact_set"
    )
    assert exact_check["missing"] == [
        {
            "id": "retired-inconclusive-reclassified-to-gap-odd-B11-B16",
            "function": "fc_is_odd",
            "binary_pair": "B11_B16",
        },
        {
            "id": "retired-inconclusive-reclassified-to-gap-odd-B12-B16",
            "function": "fc_is_odd",
            "binary_pair": "B12_B16",
        },
    ]
    assert len(manifest["retired_transitions"]) == 1
    with pytest.raises(ValueError, match="phase3_pre_fix_retired_transitions_exact_set"):
        validate_phase3_return_coverage_lane1_post_fix_gate(manifest)


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


def test_phase3_phase1_checks_read_only_manifest_entry_logs(tmp_path, monkeypatch):
    current_root = tmp_path / "current" / "function_call"
    _write_eq_log(current_root, "fc_positive_fixture", "B11", "B12")
    unrelated = current_root / "fc_unrelated" / "fc_unrelated_B1_B2.log"
    unrelated.parent.mkdir(parents=True)
    unrelated.write_text("Result: UNKNOWN\n")
    entries = [
        {
            "id": "positive-fixture-eq",
            "category": "function_call",
            "function": "fc_positive_fixture",
            "binary_pair": "B11_B12",
        }
    ]
    read_paths = []
    original_read = lane1_module.read_validation_log_record

    def _tracking_read(path):
        read_paths.append(Path(path))
        return original_read(path)

    monkeypatch.setattr(lane1_module, "read_validation_log_record", _tracking_read)

    records = _validation_records_for_entries({"function_call": current_root}, entries)

    assert records[("function_call", "fc_positive_fixture", "B11_B12")]["status"] == "EQ"
    assert read_paths == [
        current_root / "fc_positive_fixture" / "fc_positive_fixture_B11_B12.log"
    ]


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


def test_phase3_return_coverage_retired_inventory_is_scoped_to_selected_transitions(tmp_path):
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
    _write_log(
        baseline_root,
        "fc_is_odd_extra",
        "B11",
        "B16",
        [_legacy_reason_from_ref("function2:return_coverage_inconclusive")],
    )

    path = build_phase3_return_coverage_lane1_manifest(
        baseline_raw_dir=raw_dir,
        output_dir=tmp_path / "phase3",
        current_log_roots={"function_call": current_root},
        baseline_log_roots={"function_call": baseline_root},
        phase1_dir=phase1_dir,
    )

    manifest = json.loads(path.read_text())
    assert manifest["phase3_lane1_ready"] is True
    inventory = manifest["retired_reason_inventory"]["return_coverage_inconclusive"]
    assert inventory["inventory_scope"] == "selected_retired_transitions"
    assert inventory["reason_record"]["baseline_tuple_counts"][0]["count"] == 3
    validate_phase3_return_coverage_lane1_manifest(manifest)


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


def test_phase3_return_coverage_manifest_rejects_raw_action_without_proof_obligation_id(tmp_path):
    raw_dir = tmp_path / "baseline" / "raw"
    current_root = tmp_path / "current" / "function_call"
    baseline_root = tmp_path / "baseline_logs" / "function_call"
    _write_artifact_manifest(raw_dir)
    _write_representative_logs(current_root)
    _write_representative_logs(baseline_root)
    payload = _payload(
        "fc_recursive_sum",
        _payload_binary_name("B11"),
        _payload_binary_name("B15"),
        [_reason_from_ref("function2:return_coverage_gap")],
    )
    payload["unknown_recovery_actions"][0].pop("proof_obligation_id")
    _write_payload_log(
        current_root / "fc_recursive_sum" / "fc_recursive_sum_B11_B15.log",
        payload,
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
    assert "current_expected_proof_action_id_mismatch:gap-return-partition-extraction" in failures
    action = manifest["entries"][0]["current_observation"]["proof_actions"][0]
    assert action["proof_obligation_id"] is None
    assert action["raw_proof_obligation_id_present"] is False


def test_phase3_return_coverage_manifest_rejects_raw_action_with_null_proof_obligation_id(tmp_path):
    raw_dir = tmp_path / "baseline" / "raw"
    current_root = tmp_path / "current" / "function_call"
    baseline_root = tmp_path / "baseline_logs" / "function_call"
    _write_artifact_manifest(raw_dir)
    _write_representative_logs(current_root)
    _write_representative_logs(baseline_root)
    payload = _payload(
        "fc_recursive_sum",
        _payload_binary_name("B11"),
        _payload_binary_name("B15"),
        [_reason_from_ref("function2:return_coverage_gap")],
    )
    payload["unknown_recovery_actions"][0]["proof_obligation_id"] = None
    _write_payload_log(
        current_root / "fc_recursive_sum" / "fc_recursive_sum_B11_B15.log",
        payload,
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
    assert "current_expected_proof_action_id_mismatch:gap-return-partition-extraction" in failures
    assert manifest["entries"][0]["current_observation"]["proof_actions"][0][
        "raw_proof_obligation_id_present"
    ] is False


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
    legacy_key = (
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
    good_key = (
        "return_coverage",
        "function2",
        ("function_ref", ("function", "B11", 0x1000)),
        "return_coverage_gap",
        ("return_storage", "return_value", 32, False, "int"),
        (
            "return_partition",
            (
                (
                    "return_case",
                    0,
                    "0x1000",
                    (
                        "pcode_op",
                        "B11",
                        ("function_entry", "ram", 0x1000),
                        ("seq_target", "ram", 0x1010),
                        3,
                        1,
                        10,
                        0,
                    ),
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
    assert _object_target_key_is_specific(legacy_key) is False
    assert _object_target_key_is_specific(good_key) is True


def test_return_coverage_object_key_specificity_requires_canonical_function_binary_id():
    good_key = _reason_from_ref("function2:return_coverage_gap").object_target_key
    missing_binary_key = (
        good_key[0],
        good_key[1],
        ("function_ref", ("function", None, 0x1000)),
        *good_key[3:],
    )
    program_uid_key = (
        good_key[0],
        good_key[1],
        ("function_ref", ("function", 2, 0x1000)),
        *good_key[3:],
    )
    code_address_program_uid_key = (
        good_key[0],
        good_key[1],
        ("function_ref", ("code_address", 2, 0x1000)),
        *good_key[3:],
    )
    code_address_binary_key = (
        good_key[0],
        good_key[1],
        ("function_ref", ("code_address", "B15", 0x1000)),
        *good_key[3:],
    )

    assert _object_target_key_is_specific(missing_binary_key) is False
    assert _object_target_key_is_specific(program_uid_key) is False
    assert _object_target_key_is_specific(code_address_program_uid_key) is False
    assert _object_target_key_is_specific(good_key) is True
    assert _object_target_key_is_specific(code_address_binary_key) is True


def test_return_coverage_object_key_specificity_rejects_address_only_or_legacy_return_case():
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
    legacy_identity_key = (
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
    full_identity_key = (
        "return_coverage",
        "function2",
        ("function_ref", ("function", "B11", 0x1000)),
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
                    (
                        "pcode_op",
                        "B11",
                        ("function_entry", "ram", 0x1000),
                        ("seq_target", "ram", 0x1010),
                        3,
                        1,
                        10,
                        0,
                    ),
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
    assert _object_target_key_is_specific(legacy_identity_key) is False
    assert _object_target_key_is_specific(full_identity_key) is True


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


def test_return_coverage_object_key_carries_full_pcode_ref_context():
    strategy = _NoopStrategy(None, None)
    full_ref = PcodeOpRef(
        address_offset=0x401000,
        seq_time=23,
        seq_order=1,
        block_index=4,
        mnemonic="RETURN",
        binary_id="B11",
        function_entry_space="ram",
        function_entry_offset=0x400000,
        target_space="ram",
        target_offset=0x401000,
        opcode=62,
        local_op_ordinal=3,
    )
    ret = ReturnInfo(
        address="ram:00401000",
        value=Expression.constant(0, 4),
        conditions=[],
        pcode_op_ref=full_ref,
    )

    key = strategy._return_case_object_key(0, ret)

    assert key[3] == (
        "pcode_op",
        "B11",
        ("function_entry", "ram", 0x400000),
        ("seq_target", "ram", 0x401000),
        23,
        1,
        62,
        3,
    )
