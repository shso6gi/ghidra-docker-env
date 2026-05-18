# -*- coding: utf-8 -*-

import json
from pathlib import Path

import pytest

from scripts.function_tracer_pcode.equivalence.unknown_reason import (
    UnknownRecoveryActionStatus,
    UnknownRecoveryProofKind,
    UnknownReasonId,
    build_proof_obligation_id,
    make_unknown_reason,
)
from scripts.function_tracer_pcode.validation.phase2_equivalence_blocking_unsafety import (
    build_phase2_equivalence_blocking_unsafety_movement,
    validate_phase2_equivalence_blocking_unsafety_movement,
)
from scripts.function_tracer_pcode.validation.unknown_reason_summary import (
    RESULT_JSON_BEGIN,
    RESULT_JSON_END,
)

REPRESENTATIVES = (
    (
        "representative-equivalence-blocking-unsafety-apply",
        "fc_apply_indirect",
        "B10_B11",
        "B10",
        "B11",
    ),
    (
        "representative-equivalence-blocking-unsafety-dispatch",
        "fc_dispatch_indirect",
        "B10_B11",
        "B10",
        "B11",
    ),
    (
        "representative-equivalence-blocking-unsafety-recursive-stress",
        "fc_recursive_sum",
        "B10_B14",
        "B10",
        "B14",
    ),
)


def _write_log(root: Path, function: str, left: str, right: str, payload):
    function_dir = root / function
    function_dir.mkdir(parents=True, exist_ok=True)
    if payload["is_equivalent"] is True:
        result = "EQUIVALENT"
    elif payload["is_equivalent"] is False:
        result = "NOT EQUIVALENT"
    else:
        result = "UNKNOWN"
    path = function_dir / f"{function}_{left}_{right}.log"
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


def _representative_manifest(phase1_dir: Path):
    phase1_dir.mkdir(parents=True)
    (phase1_dir / "phase1_manifest_index.json").write_text(
        json.dumps(
            {
                "manifest_kind": "phase1_concrete_manifest_index",
                "manifest_version": 1,
                "baseline_id": "observed-v0@0a53352",
                "baseline_git_head": "0a53352cf3c9528abfb654906ed7b963474bedc5",
                "phase1_ready": True,
            }
        )
    )
    (phase1_dir / "representative_manifest.json").write_text(
        json.dumps(
            {
                "manifest_kind": "representative_concrete_pairs",
                "entries": [
                    _representative_entry(entry_id, function, binary_pair, left, right)
                    for entry_id, function, binary_pair, left, right in REPRESENTATIVES
                ],
            }
        )
    )


def _representative_entry(entry_id: str, function: str, binary_pair: str, left: str, right: str):
    return {
        "id": entry_id,
        "category": "function_call",
        "function": function,
        "binary_pair": binary_pair,
        "left_binary_id": left,
        "right_binary_id": right,
        "current_result": "UNKNOWN",
        "required_reason_ids": ["equivalence_blocking_unsafety"],
        "expected_movement": {
            "reason_id": "equivalence_blocking_unsafety",
            "decision_effect": "blocks_equivalence",
            "reason_scope": "function",
            "recovery_proof_kind": "call_effect_summary_proof",
            "proof_stage": "object_evidence_collected",
            "action_status": "pending_proof",
            "evidence_kind": [
                "call_effect_summary",
                "runtime_ref",
                "callsite_storage",
            ],
        },
    }


def _payload(function: str, left_binary: str, right_binary: str, is_equivalent, reasons):
    return {
        "function1_name": function,
        "function2_name": function,
        "binary1_name": left_binary,
        "binary2_name": right_binary,
        "is_equivalent": is_equivalent,
        "is_timeout": False,
        "error_message": None,
        "unknown_reasons": [reason.to_dict() for reason in reasons],
    }


def _pending_reason(*, object_target_key=None, proof_obligation_id=None):
    target = object_target_key or (
        "unsupported_call_effect",
        "function1",
        ("function_ref", ("function", 10, 0x401000)),
        ("pcode_op", "ram", 0x401020, "ram", 0x401020, 7, "CALLIND", 0),
        None,
        ("typed_target_expression", ("storage", ("register", "a0", 8))),
        7,
        "target_identity_unavailable",
    )
    return make_unknown_reason(
        UnknownReasonId.EQUIVALENCE_BLOCKING_UNSAFETY,
        decision_effect="blocks_equivalence",
        reason_scope="function",
        recovery_proof_kind=UnknownRecoveryProofKind.CALL_EFFECT_SUMMARY_PROOF,
        proof_stage="object_evidence_collected",
        evidence_kind="call_effect_summary",
        object_target_key=target,
        proof_obligation_id=proof_obligation_id,
        recovery_action="call_effect_summary_proof_required",
        action_status=UnknownRecoveryActionStatus.PENDING_PROOF,
    )


def _old_blocking_reason():
    return make_unknown_reason(
        UnknownReasonId.EQUIVALENCE_BLOCKING_UNSAFETY,
        decision_effect="blocks_equivalence",
        reason_scope="function",
    )


def _write_all_representative_logs(root: Path, payload_by_function=None):
    payload_by_function = payload_by_function or {}
    for _entry_id, function, _binary_pair, left, right in REPRESENTATIVES:
        payload = payload_by_function.get(function) or _payload(function, left, right, None, [_pending_reason()])
        _write_log(root, function, left, right, payload)


def _write_all_baseline_representative_logs(root: Path, payload_by_function=None):
    payload_by_function = payload_by_function or {}
    for _entry_id, function, _binary_pair, left, right in REPRESENTATIVES:
        payload = payload_by_function.get(function) or _payload(function, left, right, None, [_old_blocking_reason()])
        _write_log(root, function, left, right, payload)


def test_phase2_accepts_expected_pending_proof_movement_for_representative(tmp_path):
    phase1_dir = tmp_path / "phase1"
    baseline_root = tmp_path / "baseline" / "function_call"
    current_root = tmp_path / "logs" / "function_call"
    output_dir = tmp_path / "phase2"
    _representative_manifest(phase1_dir)
    _write_all_baseline_representative_logs(baseline_root)
    _write_all_representative_logs(current_root)

    path = build_phase2_equivalence_blocking_unsafety_movement(
        phase1_dir=phase1_dir,
        output_dir=output_dir,
        current_log_roots={"function_call": current_root},
        baseline_log_roots={"function_call": baseline_root},
    )

    manifest = json.loads(path.read_text())
    assert manifest["baseline_id"] == "observed-v0@0a53352"
    assert manifest["baseline_git_head"] == "0a53352cf3c9528abfb654906ed7b963474bedc5"
    assert manifest["phase1_manifest_index_ref"]["sha256"] != "__missing__"
    assert manifest["phase2_ready"] is True
    assert manifest["movement_summary"]["failed"] == 0
    assert manifest["movement_summary"]["passed"] == 3
    assert manifest["overall_baseline_comparison_gate"]["passed"] is True
    assert {entry["movement_status"] for entry in manifest["entries"]} == {"expected_movement"}
    validate_phase2_equivalence_blocking_unsafety_movement(manifest)


def test_phase2_rejects_false_eq_while_proof_is_pending(tmp_path):
    phase1_dir = tmp_path / "phase1"
    baseline_root = tmp_path / "baseline" / "function_call"
    current_root = tmp_path / "logs" / "function_call"
    output_dir = tmp_path / "phase2"
    _representative_manifest(phase1_dir)
    _write_all_baseline_representative_logs(baseline_root)
    _write_all_representative_logs(
        current_root,
        {
            "fc_apply_indirect": _payload("fc_apply_indirect", "B10", "B11", True, [_pending_reason()]),
        },
    )

    path = build_phase2_equivalence_blocking_unsafety_movement(
        phase1_dir=phase1_dir,
        output_dir=output_dir,
        current_log_roots={"function_call": current_root},
        baseline_log_roots={"function_call": baseline_root},
    )

    manifest = json.loads(path.read_text())
    assert manifest["phase2_ready"] is False
    assert "pending_proof_allowed_equivalent" in manifest["movement_summary"]["failed_kinds"]
    with pytest.raises(ValueError, match="pending_proof_allowed_equivalent"):
        validate_phase2_equivalence_blocking_unsafety_movement(manifest)


def test_phase2_rejects_missing_object_target_key_and_non_full_proof_id(tmp_path):
    phase1_dir = tmp_path / "phase1"
    baseline_root = tmp_path / "baseline" / "function_call"
    current_root = tmp_path / "logs" / "function_call"
    output_dir = tmp_path / "phase2"
    _representative_manifest(phase1_dir)
    _write_all_baseline_representative_logs(baseline_root)
    malformed_id = build_proof_obligation_id(
        UnknownReasonId.EQUIVALENCE_BLOCKING_UNSAFETY,
        "object_evidence_collected",
        UnknownRecoveryProofKind.CALL_EFFECT_SUMMARY_PROOF,
        "runtime_ref",
        ("runtime_ref", "B10"),
    )
    _write_all_representative_logs(
        current_root,
        {
            "fc_apply_indirect": _payload(
                "fc_apply_indirect",
                "B10",
                "B11",
                None,
                [
                    _pending_reason(
                        object_target_key=("runtime_ref", "B10"),
                        proof_obligation_id=malformed_id,
                    ),
                ],
            ),
        },
    )

    path = build_phase2_equivalence_blocking_unsafety_movement(
        phase1_dir=phase1_dir,
        output_dir=output_dir,
        current_log_roots={"function_call": current_root},
        baseline_log_roots={"function_call": baseline_root},
    )

    manifest = json.loads(path.read_text())
    assert manifest["phase2_ready"] is False
    assert "proof_obligation_id_mismatch" in manifest["movement_summary"]["failed_kinds"]
    assert "object_target_key_missing_or_not_specific" in manifest["movement_summary"]["failed_kinds"]


def test_phase2_rejects_aggregate_call_effect_blocker_key_with_log_prose(tmp_path):
    phase1_dir = tmp_path / "phase1"
    baseline_root = tmp_path / "baseline" / "function_call"
    current_root = tmp_path / "logs" / "function_call"
    output_dir = tmp_path / "phase2"
    _representative_manifest(phase1_dir)
    _write_all_baseline_representative_logs(baseline_root)
    aggregate_key = (
        "call_effect_blocker",
        "function1",
        ("function_ref", ("function", 10, 0x401000)),
        "unsupported_call_effect_summary",
        "function1:unsupported_call_effect_summary: rendered diagnostic detail",
        (),
        (),
        (),
    )
    _write_all_representative_logs(
        current_root,
        {
            "fc_apply_indirect": _payload(
                "fc_apply_indirect",
                "B10",
                "B11",
                None,
                [_pending_reason(object_target_key=aggregate_key)],
            ),
        },
    )

    path = build_phase2_equivalence_blocking_unsafety_movement(
        phase1_dir=phase1_dir,
        output_dir=output_dir,
        current_log_roots={"function_call": current_root},
        baseline_log_roots={"function_call": baseline_root},
    )

    manifest = json.loads(path.read_text())
    assert manifest["phase2_ready"] is False
    assert "object_target_key_missing_or_not_specific" in manifest["movement_summary"]["failed_kinds"]


def test_phase2_accepts_unknown_reason_reclassification_after_bool_lowering_fix(tmp_path):
    phase1_dir = tmp_path / "phase1"
    baseline_root = tmp_path / "baseline" / "function_call"
    current_root = tmp_path / "logs" / "function_call"
    output_dir = tmp_path / "phase2"
    _representative_manifest(phase1_dir)
    _write_all_baseline_representative_logs(baseline_root)
    _write_all_representative_logs(current_root)
    _write_log(
        baseline_root,
        "fc_is_odd",
        "B6",
        "B7",
        _payload(
            "fc_is_odd",
            "function_call_test-arm64-gcc-O1",
            "function_call_test-arm64-gcc-O2",
            None,
            [make_unknown_reason(UnknownReasonId.UNRESOLVED_EXPRESSION)],
        ),
    )
    _write_log(
        current_root,
        "fc_is_odd",
        "B6",
        "B7",
        _payload(
            "fc_is_odd",
            "function_call_test-arm64-gcc-O1",
            "function_call_test-arm64-gcc-O2",
            None,
            [make_unknown_reason(UnknownReasonId.SAT_UNSAFETY)],
        ),
    )

    path = build_phase2_equivalence_blocking_unsafety_movement(
        phase1_dir=phase1_dir,
        output_dir=output_dir,
        current_log_roots={"function_call": current_root},
        baseline_log_roots={"function_call": baseline_root},
    )

    manifest = json.loads(path.read_text())
    assert manifest["phase2_ready"] is True
    assert manifest["overall_baseline_comparison_gate"]["passed"] is True
    assert manifest["overall_baseline_comparison_gate"]["unexpected_deltas"] == {
        "final_result_counts_delta": {},
        "pair_result_multiset_delta": {},
        "proof_action_multiset_delta": {},
        "reason_record_multiset_delta": {},
        "timeout_class_multiset_delta": {},
        "validation_unknown_unit_multiset_delta": {},
    }
    validate_phase2_equivalence_blocking_unsafety_movement(manifest)


def test_phase2_accepts_return_coverage_inconclusive_to_gap_reclassification(tmp_path):
    phase1_dir = tmp_path / "phase1"
    baseline_root = tmp_path / "baseline" / "function_call"
    current_root = tmp_path / "logs" / "function_call"
    output_dir = tmp_path / "phase2"
    _representative_manifest(phase1_dir)
    _write_all_baseline_representative_logs(baseline_root)
    _write_all_representative_logs(current_root)
    _write_log(
        baseline_root,
        "fc_return_partition",
        "B14",
        "B16",
        _payload(
            "fc_return_partition",
            "function_call_test-mips64-gcc-O1",
            "function_call_test-mips64-gcc-O3",
            None,
            [make_unknown_reason(UnknownReasonId.RETURN_COVERAGE_INCONCLUSIVE)],
        ),
    )
    _write_log(
        current_root,
        "fc_return_partition",
        "B14",
        "B16",
        _payload(
            "fc_return_partition",
            "function_call_test-mips64-gcc-O1",
            "function_call_test-mips64-gcc-O3",
            None,
            [make_unknown_reason(UnknownReasonId.RETURN_COVERAGE_GAP)],
        ),
    )

    path = build_phase2_equivalence_blocking_unsafety_movement(
        phase1_dir=phase1_dir,
        output_dir=output_dir,
        current_log_roots={"function_call": current_root},
        baseline_log_roots={"function_call": baseline_root},
    )

    manifest = json.loads(path.read_text())
    assert manifest["phase2_ready"] is True
    assert manifest["overall_baseline_comparison_gate"]["passed"] is True
    assert manifest["overall_baseline_comparison_gate"]["unexpected_deltas"] == {
        "final_result_counts_delta": {},
        "pair_result_multiset_delta": {},
        "proof_action_multiset_delta": {},
        "reason_record_multiset_delta": {},
        "timeout_class_multiset_delta": {},
        "validation_unknown_unit_multiset_delta": {},
    }
    validate_phase2_equivalence_blocking_unsafety_movement(manifest)


def test_phase2_accepts_exposed_reason_addition_when_same_pair_broad_records_drop(tmp_path):
    phase1_dir = tmp_path / "phase1"
    baseline_root = tmp_path / "baseline" / "function_call"
    current_root = tmp_path / "logs" / "function_call"
    output_dir = tmp_path / "phase2"
    _representative_manifest(phase1_dir)
    _write_all_baseline_representative_logs(baseline_root)
    _write_all_representative_logs(current_root)
    _write_log(
        baseline_root,
        "fc_bool_lowering",
        "B6",
        "B7",
        _payload(
            "fc_bool_lowering",
            "function_call_test-arm64-gcc-O1",
            "function_call_test-arm64-gcc-O2",
            None,
            [
                make_unknown_reason(UnknownReasonId.UNRESOLVED_EXPRESSION),
                make_unknown_reason(UnknownReasonId.UNRESOLVED_EXPRESSION),
            ],
        ),
    )
    _write_log(
        current_root,
        "fc_bool_lowering",
        "B6",
        "B7",
        _payload(
            "fc_bool_lowering",
            "function_call_test-arm64-gcc-O1",
            "function_call_test-arm64-gcc-O2",
            None,
            [
                make_unknown_reason(UnknownReasonId.UNRESOLVED_EXPRESSION),
                make_unknown_reason(UnknownReasonId.SAT_UNSAFETY),
            ],
        ),
    )

    path = build_phase2_equivalence_blocking_unsafety_movement(
        phase1_dir=phase1_dir,
        output_dir=output_dir,
        current_log_roots={"function_call": current_root},
        baseline_log_roots={"function_call": baseline_root},
    )

    manifest = json.loads(path.read_text())
    assert manifest["phase2_ready"] is True
    assert manifest["overall_baseline_comparison_gate"]["passed"] is True
    assert manifest["overall_baseline_comparison_gate"]["unexpected_deltas"] == {
        "final_result_counts_delta": {},
        "pair_result_multiset_delta": {},
        "proof_action_multiset_delta": {},
        "reason_record_multiset_delta": {},
        "timeout_class_multiset_delta": {},
        "validation_unknown_unit_multiset_delta": {},
    }
    validate_phase2_equivalence_blocking_unsafety_movement(manifest)


def test_phase2_accepts_inconclusive_removal_when_gap_remains_for_same_pair(tmp_path):
    phase1_dir = tmp_path / "phase1"
    baseline_root = tmp_path / "baseline" / "function_call"
    current_root = tmp_path / "logs" / "function_call"
    output_dir = tmp_path / "phase2"
    _representative_manifest(phase1_dir)
    _write_all_baseline_representative_logs(baseline_root)
    _write_all_representative_logs(current_root)
    _write_log(
        baseline_root,
        "fc_return_partition",
        "B14",
        "B16",
        _payload(
            "fc_return_partition",
            "function_call_test-mips64-gcc-O1",
            "function_call_test-mips64-gcc-O3",
            None,
            [
                make_unknown_reason(UnknownReasonId.RETURN_COVERAGE_GAP),
                make_unknown_reason(UnknownReasonId.RETURN_COVERAGE_INCONCLUSIVE),
            ],
        ),
    )
    _write_log(
        current_root,
        "fc_return_partition",
        "B14",
        "B16",
        _payload(
            "fc_return_partition",
            "function_call_test-mips64-gcc-O1",
            "function_call_test-mips64-gcc-O3",
            None,
            [make_unknown_reason(UnknownReasonId.RETURN_COVERAGE_GAP)],
        ),
    )

    path = build_phase2_equivalence_blocking_unsafety_movement(
        phase1_dir=phase1_dir,
        output_dir=output_dir,
        current_log_roots={"function_call": current_root},
        baseline_log_roots={"function_call": baseline_root},
    )

    manifest = json.loads(path.read_text())
    assert manifest["phase2_ready"] is True
    assert manifest["overall_baseline_comparison_gate"]["passed"] is True
    assert manifest["overall_baseline_comparison_gate"]["unexpected_deltas"] == {
        "final_result_counts_delta": {},
        "pair_result_multiset_delta": {},
        "proof_action_multiset_delta": {},
        "reason_record_multiset_delta": {},
        "timeout_class_multiset_delta": {},
        "validation_unknown_unit_multiset_delta": {},
    }
    validate_phase2_equivalence_blocking_unsafety_movement(manifest)


def test_phase2_rejects_unrelated_exposed_reason_record_addition(tmp_path):
    phase1_dir = tmp_path / "phase1"
    baseline_root = tmp_path / "baseline" / "function_call"
    current_root = tmp_path / "logs" / "function_call"
    output_dir = tmp_path / "phase2"
    _representative_manifest(phase1_dir)
    _write_all_baseline_representative_logs(baseline_root)
    _write_all_representative_logs(current_root)
    _write_log(
        baseline_root,
        "fc_valid_reclassification",
        "B6",
        "B7",
        _payload(
            "fc_valid_reclassification",
            "function_call_test-arm64-gcc-O1",
            "function_call_test-arm64-gcc-O2",
            None,
            [
                make_unknown_reason(UnknownReasonId.UNRESOLVED_EXPRESSION),
                make_unknown_reason(UnknownReasonId.UNRESOLVED_EXPRESSION),
            ],
        ),
    )
    _write_log(
        current_root,
        "fc_valid_reclassification",
        "B6",
        "B7",
        _payload(
            "fc_valid_reclassification",
            "function_call_test-arm64-gcc-O1",
            "function_call_test-arm64-gcc-O2",
            None,
            [
                make_unknown_reason(UnknownReasonId.UNRESOLVED_EXPRESSION),
                make_unknown_reason(UnknownReasonId.SAT_UNSAFETY),
            ],
        ),
    )
    _write_log(
        baseline_root,
        "fc_unrelated_reason_addition",
        "B6",
        "B8",
        _payload(
            "fc_unrelated_reason_addition",
            "function_call_test-arm64-gcc-O1",
            "function_call_test-arm64-gcc-O3",
            None,
            [
                make_unknown_reason(UnknownReasonId.UNRESOLVED_EXPRESSION),
                make_unknown_reason(UnknownReasonId.SAT_UNSAFETY),
            ],
        ),
    )
    _write_log(
        current_root,
        "fc_unrelated_reason_addition",
        "B6",
        "B8",
        _payload(
            "fc_unrelated_reason_addition",
            "function_call_test-arm64-gcc-O1",
            "function_call_test-arm64-gcc-O3",
            None,
            [
                make_unknown_reason(UnknownReasonId.UNRESOLVED_EXPRESSION),
                make_unknown_reason(UnknownReasonId.SAT_UNSAFETY),
                make_unknown_reason(UnknownReasonId.SAT_UNSAFETY),
            ],
        ),
    )

    path = build_phase2_equivalence_blocking_unsafety_movement(
        phase1_dir=phase1_dir,
        output_dir=output_dir,
        current_log_roots={"function_call": current_root},
        baseline_log_roots={"function_call": baseline_root},
    )

    manifest = json.loads(path.read_text())
    assert manifest["phase2_ready"] is False
    assert "unexpected_reason_record_delta" in manifest["movement_summary"]["failed_kinds"]
    unexpected = manifest["overall_baseline_comparison_gate"]["unexpected_deltas"]
    assert unexpected["pair_result_multiset_delta"] == {}
    assert any(
        "reason_record | sat_unsafety" in key
        for key in unexpected["reason_record_multiset_delta"]
    )


def test_phase2_rejects_reason_addition_without_broad_reason_reduction(tmp_path):
    phase1_dir = tmp_path / "phase1"
    baseline_root = tmp_path / "baseline" / "function_call"
    current_root = tmp_path / "logs" / "function_call"
    output_dir = tmp_path / "phase2"
    _representative_manifest(phase1_dir)
    _write_all_baseline_representative_logs(baseline_root)
    _write_all_representative_logs(current_root)
    _write_log(
        baseline_root,
        "fc_valid_reclassification",
        "B6",
        "B7",
        _payload(
            "fc_valid_reclassification",
            "function_call_test-arm64-gcc-O1",
            "function_call_test-arm64-gcc-O2",
            None,
            [make_unknown_reason(UnknownReasonId.UNRESOLVED_EXPRESSION)],
        ),
    )
    _write_log(
        current_root,
        "fc_valid_reclassification",
        "B6",
        "B7",
        _payload(
            "fc_valid_reclassification",
            "function_call_test-arm64-gcc-O1",
            "function_call_test-arm64-gcc-O2",
            None,
            [make_unknown_reason(UnknownReasonId.SAT_UNSAFETY)],
        ),
    )
    _write_log(
        baseline_root,
        "fc_invalid_reason_addition",
        "B6",
        "B8",
        _payload(
            "fc_invalid_reason_addition",
            "function_call_test-arm64-gcc-O1",
            "function_call_test-arm64-gcc-O3",
            None,
            [make_unknown_reason(UnknownReasonId.UNRESOLVED_EXPRESSION)],
        ),
    )
    _write_log(
        current_root,
        "fc_invalid_reason_addition",
        "B6",
        "B8",
        _payload(
            "fc_invalid_reason_addition",
            "function_call_test-arm64-gcc-O1",
            "function_call_test-arm64-gcc-O3",
            None,
            [
                make_unknown_reason(UnknownReasonId.UNRESOLVED_EXPRESSION),
                make_unknown_reason(UnknownReasonId.SAT_UNSAFETY),
            ],
        ),
    )

    path = build_phase2_equivalence_blocking_unsafety_movement(
        phase1_dir=phase1_dir,
        output_dir=output_dir,
        current_log_roots={"function_call": current_root},
        baseline_log_roots={"function_call": baseline_root},
    )

    manifest = json.loads(path.read_text())
    assert manifest["phase2_ready"] is False
    assert "pair_result_tuple_delta" in manifest["movement_summary"]["failed_kinds"]
    unexpected = manifest["overall_baseline_comparison_gate"]["unexpected_deltas"]
    assert any(
        "fc_invalid_reason_addition" in key
        and "sat_unsafety,unresolved_expression" in key
        for key in unexpected["pair_result_multiset_delta"]
    )


def test_phase2_rejects_non_target_baseline_tuple_delta(tmp_path):
    phase1_dir = tmp_path / "phase1"
    baseline_root = tmp_path / "baseline" / "function_call"
    current_root = tmp_path / "logs" / "function_call"
    output_dir = tmp_path / "phase2"
    _representative_manifest(phase1_dir)
    _write_all_baseline_representative_logs(baseline_root)
    _write_all_representative_logs(current_root)
    _write_log(
        baseline_root,
        "fc_extra",
        "B1",
        "B2",
        _payload(
            "fc_extra",
            "B1",
            "B2",
            None,
            [make_unknown_reason(UnknownReasonId.RETURN_WIDTH_BRIDGE_MISSING)],
        ),
    )
    _write_log(
        current_root,
        "fc_extra",
        "B1",
        "B2",
        _payload(
            "fc_extra",
            "B1",
            "B2",
            None,
            [make_unknown_reason(UnknownReasonId.RETURN_COVERAGE_GAP)],
        ),
    )

    path = build_phase2_equivalence_blocking_unsafety_movement(
        phase1_dir=phase1_dir,
        output_dir=output_dir,
        current_log_roots={"function_call": current_root},
        baseline_log_roots={"function_call": baseline_root},
    )

    manifest = json.loads(path.read_text())
    assert manifest["phase2_ready"] is False
    assert "unexpected_validation_unknown_unit_delta" in manifest["movement_summary"]["failed_kinds"]
    assert "unexpected_reason_record_delta" in manifest["movement_summary"]["failed_kinds"]
    assert manifest["overall_baseline_comparison_gate"]["passed"] is False
